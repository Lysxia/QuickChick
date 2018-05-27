Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import Omega.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrnat ssrbool eqtype div.

Require Import SimpleIO.IOMonad.
Require Import SimpleIO.CoqPervasives.

From QuickChick Require Import
     RoseTrees
     RandomQC
     GenLow
     GenHigh
     SemChecker
     Show
     Checker
     State
     Classes
     Term
     Utils.

Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import List.

Require Import Recdef.

Require Import Arith.EqNat.

Import GenLow GenHigh.

Import IONotations.

Definition gte n m := Nat.leb m n.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Record Args := MkArgs {
  replay     : option (RandomSeed * nat);
  maxSuccess : nat;
  maxDiscard : nat;
  maxShrinks : nat;
  maxSize    : nat;
  chatty     : bool
}.

Definition updMaxSize (a : Args) (x : nat) : Args := 
  let '(MkArgs r msc md msh msz c) := a in 
  MkArgs r msc md msh x c.

Definition updMaxSuccess (a : Args) (x : nat) : Args := 
  let '(MkArgs r msc md msh msz c) := a in 
  MkArgs r x md msh msz c.

Inductive Result :=
  | Success : nat -> nat -> list (string * nat) -> string -> Result
  | GaveUp  : nat -> list (string * nat) -> string -> Result
  | Failure : nat -> nat -> nat -> RandomSeed -> nat -> string ->
              list (string * nat) -> string -> Result
  | NoExpectedFailure : nat -> list (string * nat) -> string -> Result.

Definition isSuccess (r : Result) : bool :=
  match r with
    | Success _ _ _ _ => true
    | _         => false
  end.

(* Representing large constants in Coq is not a good idea... :) *)
Axiom defNumTests    : nat.
Extract Constant defNumTests    => "10000".
Axiom defNumDiscards : nat.
Extract Constant defNumDiscards => "(2 * defNumTests)".
Axiom defNumShrinks  : nat.
Extract Constant defNumShrinks  => "1000".
Axiom defSize        : nat.
Extract Constant defSize        => "7".

Definition stdArgs := MkArgs None defNumTests defNumDiscards
                             defNumShrinks defSize true.

Definition roundTo n m := mult (Nat.div n m) m.

Definition computeSize' (a : Args) (n : nat) (d : nat) : nat :=
  if (roundTo n (maxSize a) <= maxSuccess a) || (n >= maxSuccess a)
     || (maxSuccess a %| (maxSize a))
  then
    minn (n %% (maxSize a) + d %/ 10) (maxSize a)
  else
    minn ((n %% (maxSize a)) * maxSize a %/
      ((maxSuccess a) %% (maxSize a) + d %/ 10)) (maxSize a).

 Definition at0 (f : nat -> nat -> nat) (s : nat) (n d : nat) :=
  if andb (beq_nat n 0) (beq_nat d 0) then s
  else f n d.

Fixpoint prependToAll {A : Type} (sep : A) (ls : list A) : list A :=
  match ls with
    | nil => nil
    | h :: t => sep :: h :: prependToAll sep t
  end.

Definition intersperse {A : Type} (sep : A) (ls : list A) : list A :=
  match ls with
    | nil => nil
    | h :: t => h :: prependToAll sep t
  end.

Definition notNull (ls : list string) : bool :=
  match ls with
    | nil => false
    | _ => true
  end.

Fixpoint insertBy A (compare : A -> A -> bool) (x : A) (l : list A) : list A :=
  match l with
    | nil => x :: nil
    | h :: t => if compare x h then x :: l else h :: insertBy compare x t
  end.

Fixpoint insSortBy A (compare : A -> A -> bool) (l : list A) : list A :=
  match l with
    | nil => nil
    | h :: t => insertBy compare h (insSortBy compare t)
  end.

Local Open Scope string.
Fixpoint concatStr (l : list string) : string :=
  match l with
    | nil => ""
    | (h :: t) => h ++ concatStr t
  end.

Definition summary (st : State) : list (string * nat) :=
  let res := Map.fold (fun key elem acc => (key,elem) :: acc) (labels st) nil
  in insSortBy (fun x y => snd y <= snd x) res .

Definition doneTesting (st : State) (f : nat -> RandomSeed -> QProp) :
  IO Result :=
  let n_success := numSuccessTests st in
  let n_discard := numDiscardedTests st in
  if expectedFailure st then
    let msg :=
        "+++ Passed " ++ show n_success ++
        " tests" ++
        match n_discard with
        | O => ""
        | S _ => " (" ++ show n_discard ++ " discards)"
        end in
    (clear_output_term (terminal st) msg;;
     IOMonad.ret
       (Success (n_success + 1) n_discard (summary st) msg))%io
  else
    let msg :=
        "*** Failed! Passed " ++ show n_success ++
        " tests (expected failure)" in
    (clear_output_term (terminal st) msg;;
     IOMonad.ret
       (NoExpectedFailure n_success (summary st) msg))%io.
  (* TODO: success st - labels *)

Definition giveUp (st : State) (_ : nat -> RandomSeed -> QProp) :
  IO Result :=
  let n_success := numSuccessTests st in
  let n_discard := numDiscardedTests st in
  let msg :=
      "*** Gave up! Passed only " ++ show n_success ++ " tests, " ++
      "discarded  " ++ show n_discard in
  (clear_output_term (terminal st) msg;;
   IOMonad.ret (GaveUp n_success (summary st) msg)).

Definition callbackPostTest
           (st : State) (res : Checker.Result) : IO unit :=
  match res with
  | MkResult o e r i s c t =>
    let res := MkSmallResult o e r i s t in
    traverse_io_ (fun callback =>
      match callback with
      | PostTest _ call => call st res
      | _ => IOMonad.ret tt
      end) c
  end.

Definition callbackPostFinalFailure
           (st : State) (res : Checker.Result) : IO unit :=
  match res with
  | MkResult o e r i s c t =>
    let res := MkSmallResult o e r i s t in
    traverse_io_ (fun callback =>
      match callback with
      | PostFinalFailure _ call => call st res
      | _ => IOMonad.ret tt
      end) c
  end.

Fixpoint localMin (st : State) (r_ : Rose_ Checker.Result)
         {struct r_} : IO (nat * Checker.Result) :=
  match r_ with
  | MkRose res ts =>
    let fix localMin' st ts {struct ts} :=
        match ts with
        | nil =>
          callbackPostFinalFailure st res;;
          IOMonad.ret (numSuccessShrinks st, res)
        | cons r' ts' =>
          pluckRose_ r' (fun '((MkRose res' _) as r_') =>
          callbackPostTest st res;;
          let tryNext :=
              localMin' (updTryShrinks st (fun x => x + 1)) ts' in
          match ok res' with
          | Some false =>
            let consistent_tags :=
                match result_tag res, result_tag res' with
                | Some t1, Some t2 => is_left (string_dec t1 t2)
                | None, None => true
                | _, _ => false
                end in
            if consistent_tags then
              localMin (updSuccessShrinks st (fun x => x + 1))
                       r_'
            else
              tryNext
          | _ => tryNext
          end)
        end in
    localMin' st (force ts)
  end.

Fixpoint runATest (st : State) (f : nat -> RandomSeed -> QProp)
         (maxSteps : nat) : IO Result :=
  if maxSteps is maxSteps'.+1 then
    let n_success := numSuccessTests st in
    let n_discard := numDiscardedTests st in
    update_term (terminal st) (show n_success);;
    let size := (computeSize st) n_success n_discard in
    let (rnd1, rnd2) := randomSplit (randomSeed st) in
    let test (st : State) :=
        if (gte (numSuccessTests st) (maxSuccessTests st)) then
          doneTesting st f
        else if (gte (numDiscardedTests st) (maxDiscardedTests st)) then
               giveUp st f
             else runATest st f maxSteps'
    in
    match st with
    | MkState tm mst mdt ms cs nst ndt ls e r nss nts =>
      match f size rnd1 with
      | MkProp r0 =>
        pluckRose_ r0 (fun '(MkRose res ts) =>
        (* TODO: CallbackPostTest *)
        callbackPostTest st res;;
        match res with
        | MkResult (Some x) e reas _ s _ t =>
          if x then (* Success *)
            let ls' := 
                match s with 
                | nil => ls 
                | _ => 
                  let s_to_add := 
                      ShowFunctions.string_concat 
                        (ShowFunctions.intersperse " , "%string s) in
                  match Map.find s_to_add ls with 
                    | None   => Map.add s_to_add 1 ls
                    | Some k => Map.add s_to_add (k+1) ls
                  end 
                end in
(*                  
            let ls' := fold_left (fun stamps stamp =>
                                    let oldBind := Map.find stamp stamps in
                                    match oldBind with
                                    | None   => Map.add stamp 1 stamps
                                    | Some k => Map.add stamp (k+1) stamps
                                    end
                                 ) s ls in*)
            test (MkState tm mst mdt ms cs (nst + 1) ndt ls' e rnd2 nss nts)
          else (* Failure *)
            let tag_text := 
                match t with 
                | Some s => "Tag: " ++ s ++ nl
                | _ => "" 
                end in 
            let pre : string := (if expect res then "*** Failed "
                                 else "+++ Failed (as expected) ")%string in
            n_shrinks_res <- localMin st (MkRose res ts);;
            let (numShrinks, res') := n_shrinks_res in
            let suf := ("after " ++ (show (S nst)) ++ " tests and "
                                 ++ (show numShrinks) ++ " shrinks. ("
                                 ++ (show ndt) ++ " discards)")%string in
            (* TODO: Output *)
            if (negb (expect res)) then
              IOMonad.ret
                (Success (nst + 1) ndt (summary st)
                         (tag_text ++ pre ++ suf))
            else
              IOMonad.ret
                (Failure (nst + 1) numShrinks ndt r size
                         (tag_text ++ pre ++ suf)
                         (summary st) reas)
        | MkResult None e reas _ s _ t =>
          (* Ignore labels of discarded tests? *)
          test (MkState tm mst mdt ms cs nst ndt.+1 ls e rnd2 nss nts)
        end)%io
      end
    end
  else giveUp st f.

Definition test (st : State) (f : nat -> RandomSeed -> QProp) :
  IO Result :=
  if (gte (numSuccessTests st) (maxSuccessTests st)) then
    doneTesting st f
  else if (gte (numDiscardedTests st) (maxDiscardedTests st)) then
         giveUp st f
  else
    let maxSteps := maxSuccessTests st + maxDiscardedTests st in
    runATest st f maxSteps.

Require Import ZArith.

(* ZP: This was quickCheckResult before but since we always return result
       return result there is no reason for such distinction *)
Definition quickCheckResult {prop : Type} {_ : Checkable prop}
           (a : Args) (p : prop) : IO Result :=
  (* ignore terminal - always use trace :D *)
  let (rnd, computeFun) :=
      match replay a with
        | Some (rnd, s) => (rnd, at0 (computeSize' a) s)
        | None          => (newRandomSeed, computeSize' a)
        (* make it more random...? need IO action *)
      end in
  withStdTerminal (fun tm =>
  test (MkState tm
                (maxSuccess a)  (* maxSuccessTests   *)
                (maxDiscard a)  (* maxDiscardTests   *)
                (maxShrinks a)  (* maxShrinks        *)
                computeFun      (* computeSize       *)
                0               (* numSuccessTests   *)
                0               (* numDiscardTests   *)
                (Map.empty nat) (* labels            *)
                false           (* expectedFailure   *)
                rnd             (* randomSeed        *)
                0               (* numSuccessShrinks *)
                0               (* numTryShrinks     *)
       ) (run (checker p))).

Fixpoint showCollectStatistics (l : list (string * nat)) :=
  match l with
    | nil => ""
    | cons (s,n) l' =>
      show n ++ " : " ++ s ++ newline ++ showCollectStatistics l'
  end.

Instance showResult : Show Result := Build_Show _ (fun r =>
  match r with
  | Success _ _ l s => showCollectStatistics l ++ s
  | GaveUp _ l s => showCollectStatistics l ++ s
  | Failure _ _ _ _ _ s l _ => showCollectStatistics l ++ s
  | NoExpectedFailure _ l s => showCollectStatistics l ++ s
  end ++ newline).

Definition quickCheckWith {prop : Type} {_ : Checkable prop}
           (a : Args) (p : prop) : IO unit :=
  IOMonad.bind (quickCheckResult a p) (fun _ => IOMonad.ret tt).

Definition quickCheck {prop : Type} {_ : Checkable prop}
           (p : prop) : IO unit :=
  quickCheckWith stdArgs p.

Require Import QuickChick.
Require Import SimpleIO.IOMonad.
Require Import SimpleIO.CoqPervasives.

Class Mutateable (A : Type) : Type :=
{
  mutate : A -> list A
}.

Require Import Utils.
Require Import List.
Import ListNotations.
Import IONotations.
Open Scope io_scope.

(* Default mutateable instance for lists *)
(* Priority 1, in case someone overrides the default to further mutate
   when the A's are mutateable *)
Instance MutateableList (A : Type) : Mutateable (list A) | 1 :=
{|
  mutate l :=
    let fix f l :=
        match l with
          | [] => []
          | x::xs => xs :: map (fun xs' => x :: xs') (f xs)
        end
    in f l
|}.

Example mutate_example : mutate [1;2;3] = [[2;3];[1;3];[1;2]].
Proof. reflexivity. Qed.

Require Import Coq.Strings.String. Open Scope string_scope.

Definition force {X} (x : X) := x.

Definition found_bug r :=
  match r with
  | Failure _ _ _ _ _ _ _ _ => true
  | _ => false
  end.

Definition message (kill : bool) (n1 n2 : nat) :=
  (if kill then "Killed" else "Missed") ++
  " mutant " ++ (if kill then "" else "[") ++ show n2
             ++ (if kill then "" else "]")
  ++ " (" ++ show n1 ++ " frags)" ++ nl.

Open Scope nat.

Definition mutateCheckManyWith {A P : Type} {_: Checker.Checkable P}
           {mutA: Mutateable A} (args : Args)
           (a : A) (ps : A -> list P)
  : IO (nat * nat) :=
  let mutants := mutate a in
  print_endline ("Fighting " ++ show (List.length mutants) ++ " mutants");;
  (fold_io
     (fun n m => match n with (n1,n2) =>
        kill <- existsb_io (fun c =>
                  map_io found_bug (quickCheckResult args c)) (ps m);;
        let n1' := n1 + (if kill then 1 else 0) in
        let msg := message kill n1' n2 in
        ret (Checker.trace msg (n1', n2 + 1))
      end)
     mutants (0, 0)).

Definition mutateCheckMany {A P : Type} {_: Checkable P}
           `{mutA: Mutateable A}
           (a : A) (ps : A -> list P) :=
  mutateCheckManyWith stdArgs a ps.

Definition mutateCheckWith {A P: Type}
           {_: Checkable P} {mutA: Mutateable A} (args : Args)
           (a : A) (p : A -> P):=
  mutateCheckManyWith args a (fun a => cons (p a) nil).

Definition mutateCheck {A P: Type}
           {_: Checkable P} {mutA: Mutateable A}
           (a : A) (p : A -> P):=
  mutateCheckManyWith stdArgs a (fun a => cons (p a) nil).

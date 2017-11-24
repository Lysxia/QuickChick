(* Port of https://github.com/jmid/qcheck-fun/blob/master/fun.ml (OCaml) *)

Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import String. Open Scope string.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From QuickChick Require Import QuickChick Tactics CoArbitrary GenLow Checker.
Import QcNotation.
Import QcDoNotation.
Open Scope qc_scope.

Require Import List.
Import ListNotations.

(** Setting up **)

(* Give high priority to function instance. *)
Instance genFun (A : Type) (B : Type) (CA : CoArbitrary A) (GB : Gen B) : Gen (A -> B) | 1 := QuickChick.CoArbitrary.genFun.

(** Obviously true properties. **)

(* Note that we could not actually write a generator of functions
   with mutable and unsplittable seeds. *)
Definition prop_extensional_refl
           (f : bool -> bool) (b : bool) : bool :=
  f b = f b ?.

(* QuickChick prop_extensional_refl. *)

(** Obviously false properties. **)

Definition prop_false_bool (f : bool -> bool) (b : bool) : bool :=
  f (f b) = b ?.

(* QuickChick prop_false_bool. *)

(**  https://github.com/jsverify/jsverify   c.f. README **)
Definition prop_thrice_bool (f : bool -> bool) (b : bool) : bool :=
  f (f (f b)) = b ?.

(* QuickChick prop_thrice_bool. *)

(* This doesn't look too good without shrinking. *)
Definition prop_false_nat (f : nat -> nat) (n : nat) : bool :=
  f (f n) <= n + 3 ?.

(* QuickChick prop_false_nat. *)

(** Claessen, Haskell'12 **)

Definition prop_map_filter
           (f : nat -> nat) (p : nat -> bool) (xs : list nat)
  : bool :=
  map f (filter p xs) = filter p (map f xs) ?.

(* QuickChick prop_map_filter. *)

Definition prop_foldl_foldr
           (f : nat -> nat -> nat) (x : nat) (xs : list nat) : bool :=
  foldl f x xs = foldr f x xs ?.

(* QuickChick prop_foldl_foldr. *)

Definition prop_pred_list (f : list nat -> bool) : Checker :=
  f [1; 2; 3; 4; 5; 6; 7; 8; 9] ==> f [1; 2; 3; 4; 0; 6; 7; 8; 9].

(* QuickChick prop_pred_list. *)

Definition prop_member
           (f : nat -> nat) (x : nat) (xs : list nat) : Checker :=
  In x (map f (map f xs)) ? ==> (In x xs ?). (* TODO Fix precedence? *)

(* QuickChick prop_member. *)

(** Nim game **)

Inductive move : Set := take_2 | take_3.

Search G.

Instance gen_move : Gen move :=
  {| arbitrary := liftGen (fun b => if b then take_2 else take_3) arbitrary |}.

Instance shrink_move : Shrink move :=
  {| shrink m :=
       match m with
       | take_2 => []
       | take_3 => [take_2]
       end
  |}.


Instance arbitrary_move : Arbitrary move.

Instance show_move : Show move :=
  {| show m :=
       match m with
       | take_2 => "take_2"
       | take_3 => "take_3"
       end
  |}.

Definition name : Set := nat.
Definition player : Set := name * (nat -> move).

Definition play_move (p : player) (n : nat) : move :=
  let '(_, strat) := p in strat n.

Definition player_name (p : player) : name :=
  let '(nm, _) := p in nm.

Fixpoint play (n : nat) (player1 player2 : player) : name :=
  match play_move player1 n, n with
  | take_2, n'.+2 => play n' player2 player1
  | take_3, n'.+3 => play n' player2 player1
  | _, _ => player_name player2 (* Player 1 loses. *)
  end.

(* The checker
     (prop_winning n strat1) : (nat -> move) -> bool
   checks whether strat1 is a winning strategy for Player 1.
*)
Definition prop_winning
           (n : nat)
           (strat1 : nat -> move)
           (strat2 : nat -> move) :=
  1 = play n (1, strat1) (2, strat2) ?.

(* QuickChick (prop_winning 19 (fun _ => take_2)). *)

Definition winning_strat (n : nat) : move :=
  match div.modn n 5 with
  | 3 => take_2
  | 4 => take_3
  | _ => take_2
  end.

QuickChick (prop_winning 19 winning_strat).

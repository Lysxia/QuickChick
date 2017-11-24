(* Port of https://github.com/jmid/qcheck-fun/blob/master/fun.ml (OCaml) *)

Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import String. Open Scope string.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From QuickChick Require Import QuickChick Tactics CoArbitrary GenLow.
Import QcDefaultNotation.
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

QuickChick prop_extensional_refl.

(** Obviously false properties. **)

Definition prop_false_bool (f : bool -> bool) (b : bool) : bool :=
  f (f b) = b ?.

QuickChick prop_false_bool.

(* This doesn't look too good without shrinking. *)
Definition prop_false_nat (f : nat -> nat) (n : nat) : bool :=
  f (f n) <= n + 3 ?.

QuickChick prop_false_nat.


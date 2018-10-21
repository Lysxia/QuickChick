Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool ssrnat eqtype.
Require Import ZArith.

(* Splittable randomness. *)
Class Splittable (seed : Type) : Type := {
  (* Split into two independent seeds. *)
  randomSplit : seed -> seed * seed;
  (* Random number less than or equal to bound. *)
  randomN : seed -> N -> N;
  (* Random boolean. *)
  randomBool : seed -> bool;

  (* Specification of [randomN]. *)
  randomN_correct : forall s bound, randomN s bound <= bound;
}.

Module Generator.

(* A random generator is a function that produces a
   value given a seed, only via that interface. *)
Definition G (A : Type) : Type :=
  forall seed `(Splittable seed), seed -> A.

Definition run {seed : Type} `{Splittable seed} {A : Type}
           (g : G A) (s : seed) : A := g _ _ s.

Definition bind {A B : Type} (g : G A) (k : A -> G B) : G B :=
  fun _ _ s =>
    let '(s1, s2) := randomSplit s in
    k (g _ _ s1) _ _ s2.

Definition ret {A : Type} (a : A) : G A :=
  fun _ _ _ => a.

End Generator.

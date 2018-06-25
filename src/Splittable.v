Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool ssrnat eqtype.
Require Import ZArith.

Require SplitMix.

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

End Generator.

(* Concrete implementation of a splittable PRNG. *)
Definition RandomSeed := SplitMix.State.

Lemma State_randomN_correct : forall (s : SplitMix.State) bound,
    SplitMix.random_N s bound <= bound.
Proof.
Admitted.

Instance Splittable_State : Splittable SplitMix.State :=
  { randomSplit := SplitMix.split;
    randomN := SplitMix.random_N;
    randomBool := SplitMix.random_bool;
    randomN_correct := State_randomN_correct;
  }.

(* TODO: better ways to get an initial seed. *)
Definition newRandomSeed : SplitMix.State := SplitMix.of_seed 33.

(* This is a fast implementation, but its state is finite
   and difficult to reason about. It is not suitable to
   describe the set of values that a generator can produce.
   We must consider better-behaved types of seeds. *)

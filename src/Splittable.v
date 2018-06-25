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

(* "Surjective" splittable randomness.
   We can use this to define the set of values generated
   by a QuickChick generator. *)
Class CoSplittable (seed : Type) `{Splittable seed} : Type := {
  corandomSplit : seed * seed -> seed;
  corandomN : N -> N -> seed;
  corandomBool : bool -> seed;

  randomSplit_complete :
    forall ss, randomSplit (corandomSplit ss) = ss;
  randomN_complete :
    forall (bound n : N),
      n <= bound -> randomN (corandomN bound n) bound = n;
  randomBool_complete : forall b, randomBool (corandomBool b) = b;
}.

(* This lemma is useful to handle constant generators. *)
Lemma inhabitedCoSplittable (seed : Type) `{CoSplittable seed} :
  inhabited seed.
Proof. by constructor; exact (corandomBool false). Qed.

(* A simple model of splittable randomness. *)
(* Just a theoretical observation for the moment. *)
Module Infinite.
  (* [Splittable] instances are coalgebras.
     [Tree] is the final [Splittable] coalgebra. *)
  CoInductive Tree : Type :=
  | Node : Tree * Tree ->
           forall (f : N -> N),
           (forall bound : N, f bound <= bound) ->
           bool -> Tree.

  (* An arbitrary placeholder tree. *)
  CoFixpoint def : Tree :=
    Node (def, def) (fun _ => 0%N) leq0n false.

  Global Instance Splittable_Tree : Splittable Tree := {|
    randomSplit := fun '(Node ss _ _ _) => ss;
    randomN := fun '(Node _ f _ _) bound => f bound;
    randomBool := fun '(Node _ _ _ b) => b;
    randomN_correct := fun t bound =>
      let '(Node _ _ g _) := t in g bound;
  |}.

  (* [seedToTree] is the anamorphism from any [Splittable]
     coalgebra to [Tree]: it summarizes all the observations
     we can make of a seed via [Splittable]. *)
  CoFixpoint seedToTree {seed} `{Splittable seed} (s : seed) :=
      let ss := randomSplit s in
      Node (seedToTree (fst ss), seedToTree (snd ss))
           (randomN s)
           (randomN_correct s)
           (randomBool s).

  Definition corandomSplit (ts : Tree * Tree) : Tree :=
    Node ts (fun _ => 0%N) leq0n true.

  Definition corandomBool (b : bool) : Tree :=
    Node (def, def) (fun _ => 0%N) leq0n b.

  (* [randomN_complete]. *)
  Definition step_fun (x : N) : N -> N :=
    fun bound => if x <= bound then x else 0%N.

  Lemma step_fun_correct (x bound : N) :
    step_fun x bound <= bound.
  Proof.
    unfold step_fun. by destruct (x <= bound) eqn:e.
  Qed.

  Definition corandomN (x : N) : Tree :=
    Node (def, def) _ (step_fun_correct x) false.

  Lemma randomN_complete (bound x : N) :
    x <= bound -> randomN (corandomN x) bound = x.
  Proof.
    move => H /=.
    unfold step_fun.
      by rewrite H.
  Qed.

  Global Instance CoSplittable_Tree : CoSplittable Tree :=
    { corandomSplit := corandomSplit;
      corandomN := fun _ => corandomN;
      corandomBool := corandomBool;

      randomSplit_complete := fun '(_, _) => erefl;
      randomN_complete := randomN_complete;
      randomBool_complete := fun _ => erefl;
    }.

End Infinite.

(* Another model of splittable randomness that more closely
   reflects the observations we want to allow. In particular,
   observations are finite and a seed should not be reused
   with different [Splittable] methods. *)
Module Finite.
  Unset Elimination Schemes.

  Inductive Tree : Type :=
  | CoRandomSplit : Tree * Tree -> Tree
  | CoRandomN : N -> N -> Tree
  | CoRandomBool : bool -> Tree.

  Definition Tree_ind (P : Tree -> Type)
           (coSplit : forall (ts : Tree * Tree),
               P ts.1 -> P ts.2 -> P (CoRandomSplit ts))
           (coN : forall bound n, P (CoRandomN bound n))
           (coBool : forall b, P (CoRandomBool b)) :
    forall t, P t :=
    fix cata t :=
      match t with
      | CoRandomSplit ts => coSplit ts (cata ts.1) (cata ts.2)
      | CoRandomN bound n => coN bound n
      | CoRandomBool b => coBool b
      end.

  Definition def : Tree := CoRandomBool true.

  Global Instance Splittable_Tree : Splittable Tree := {
    randomSplit := fun t =>
      if t is CoRandomSplit ss then ss else (def, def);
    randomN := fun t =>
      if t is CoRandomN _ n then
        Infinite.step_fun n
      else fun _ => 0%N;
    randomBool := fun t =>
      if t is CoRandomBool b then b else true;
  }.
  Proof.
    move => [_ | n | _] bound; try reflexivity.
    intros; apply Infinite.step_fun_correct.
  Defined.

  Global Instance CoSplittable_Tree : CoSplittable Tree := {
    corandomSplit := CoRandomSplit;
    corandomN := CoRandomN;
    corandomBool := CoRandomBool;

    randomSplit_complete := fun ss => erefl;
    randomN_complete := Infinite.randomN_complete;
    randomBool_complete := fun b => erefl;
  }.

  (* This finite [Tree] is initial in some sense... *)
  (* We can use it to reconstruct cosplittable seeds. *)
  Fixpoint treeToSeed {seed : Type}
           `{CoSplittable seed} (t : Tree) : seed :=
    match t with
    | CoRandomSplit ts =>
      corandomSplit (treeToSeed ts.1, treeToSeed ts.2)
    | CoRandomN bound x => corandomN bound x
    | CoRandomBool b => corandomBool b
    end.

  (* And we can assert that a seed matches the observations
     described by a tree. *)
  Fixpoint observeSeed {seed : Type}
           `{Splittable seed} (t : Tree) (s : seed) : bool :=
    match t with
    | CoRandomSplit ts =>
      let ss := randomSplit s in
      observeSeed ts.1 ss.1 && observeSeed ts.2 ss.2
    | CoRandomN bound x => randomN s bound == x
    | CoRandomBool b => randomBool s == b
    end.

  (* We need to check as a precondition that the [CoRandomN]
     leaves have bounds greater than the observed value. *)
  Fixpoint wfTree (t : Tree) : bool :=
    match t with
    | CoRandomSplit ts => wfTree ts.1 && wfTree ts.2
    | CoRandomN bound x => x <= bound
    | CoRandomBool b => true
    end.

  (* Any tree can be "cosplit" into a seed with matching
     observations. *)
  Lemma observeTreeToSeed {seed : Type} `{CoSplittable seed}
        (t : Tree) : wfTree t -> observeSeed t (treeToSeed t : seed).
  Proof.
    induction t as [ts IHt1 IHt2 | bound x | b]; move=> /= wf.
    - move: wf => /andP [/IHt1 Ht1 /IHt2 Ht2].
        by apply (introT andP); rewrite randomSplit_complete.
    - by rewrite randomN_complete.
    - by rewrite randomBool_complete.
  Qed.

  Lemma treeToSeed_self (t : Tree) : wfTree t -> treeToSeed t = t.
  Proof.
    induction t as [[ts1 ts2] IHt1 IHt2 | bound x | b]; move=> //= wf.
    - move: wf => /andP [/IHt1 Ht1 /IHt2 Ht2].
      rewrite Ht1 Ht2. done.
  Qed.

  Lemma observeSeed_self (t : Tree) : wfTree t -> observeSeed t t.
  Proof.
    intro wf.
    rewrite <- treeToSeed_self at 2; auto.
    apply observeTreeToSeed; auto.
  Qed.

  Lemma observeSeed_wf {seed} `{Splittable seed} (t : Tree) :
    forall (s : seed), observeSeed t s -> wfTree t.
  Proof.
    induction t as [[ts1 ts2] IHt1 IHt2 | bound x | b];
      move=> //= s os.
    - move: os => /andP [/IHt1 Ht1 /IHt2 Ht2].
        by rewrite Ht1 Ht2.
    - move: os => /eqP os. subst. apply randomN_correct.
  Qed.
End Finite.

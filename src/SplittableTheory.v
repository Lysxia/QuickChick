Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

From Coq Require Import
     ZArith List.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool ssrnat eqtype.
Require Import Numbers.BinNums.
Require Import Classes.RelationClasses.

From QuickChick Require Import Sets Splittable.

Set Bullet Behavior "Strict Subproofs".

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

  (* We make some default values opaque, so proofs can't rely
     on them. *)
  Module Type TreeParamSig.
    Parameter def : Tree.
    Parameter split_def : Tree * Tree.
    Parameter N_def : N -> N.
    Parameter N_def_correct : forall n, N_def n <= n.
    Parameter bool_def : bool.
  End TreeParamSig.

  Module Import TreeParam : TreeParamSig.
    Definition def : Tree := CoRandomBool true.
    Definition split_def : Tree * Tree := (def, def).
    Definition N_def : N -> N := fun _ => N0.
    Lemma N_def_correct n : N_def n <= n.
    Proof. reflexivity. Qed.
    Definition bool_def : bool := true.
  End TreeParam.

  Lemma inhabited_Tree : inhabited Tree.
  Proof. constructor; exact def. Qed.

  Global Instance Splittable_Tree : Splittable Tree := {
    randomSplit := fun t =>
      if t is CoRandomSplit ss then ss else split_def;
    randomN := fun t =>
      if t is CoRandomN _ n then
        Infinite.step_fun n
      else N_def;
    randomBool := fun t =>
      if t is CoRandomBool b then b else bool_def;
  }.
  Proof.
    move => [_ | n | _] bound;
      try reflexivity;
      try apply N_def_correct.
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

Module Semantics.
Import Generator.

(* Naive semantics: set of values that can be generated
   (for a fixed [seed] type). *)
Definition generable (seed : Type) `{Splittable seed}
           {A : Type} (g : G A) : set A :=
  fun a => exists s, run g s = a.

Arguments generable seed {_ A} g.

(* Parametricity/universal property of the final coalgebra:
   seeds are generalized by infinite trees. *)
Axiom parametricity_G :
  forall {seed : Type} `{Splittable seed} {A} (g : G A) (s : seed),
    run g (Infinite.seedToTree s) = run g s.

(* Thus the model of infinite trees gives a superset of all
   generable values. *)
Lemma general_generable (seed : Type) `{Splittable seed}
      {A : Type} (g : G A) :
  generable seed g \subset generable Infinite.Tree g.
Proof.
  move=> a [s Hs].
  rewrite <- parametricity_G in Hs.
  eexists.
  eassumption.
Qed.

(* Thus we may consider specializing [generable] to that model. *)
Notation generable' := (generable Infinite.Tree).

(* However, we would like to consider only generators which
   apply at most one [Splittable] method to each seed. *)
(* Without linear types, we need to be more creative with
   parametricity. A tree [t] is a [fingerprint] of a value [a]
   with respect to a generator [g] if running the generator with
   any seed [s] compatible with [t] (this includes [t] itself)
   produces the value [a]. *)
Definition fingerprint {A : Type}
           (g : G A) (t : Finite.Tree) (a : A) : Prop :=
  forall seed `(Splittable seed) (s : seed),
    Finite.observeSeed t s -> run g s = a.

(* The set of fingerprinted values that can be generated by [g]. *)
Definition fgenerable {A : Type} (g : G A) : set A :=
  fun a =>
    exists (t : Finite.Tree),
      Finite.wfTree t /\ fingerprint g t a.

(* A [linear] generator is one whose every execution can be
   explained by a fingerprint compatible with the original seed. *)
Definition linear {A : Type} (g : G A) : Prop :=
  forall seed `(Splittable seed) (s : seed),
    exists (t : Finite.Tree),
      Finite.observeSeed t s /\ fingerprint g t (run g s).

(* For linear generators, [generable'] and [fgenerable] coincide. *)
Theorem linear_generable {A : Type} (g : G A) :
  linear g -> generable' g <--> fgenerable g.
Proof.
  intros Hg a; split=> Hgble.
  - case: Hgble => [t Ht].
    destruct (Hg _ _ t) as [t' [Ht' Hft']].
    rewrite Ht in Hft'.
    apply Finite.observeSeed_wf in Ht'.
    eexists; split; eassumption.
  - case: Hgble => [t' Ht'].
    exists (Infinite.seedToTree t').
    rewrite parametricity_G.
    apply Ht', Finite.observeSeed_self, Ht'.
Qed.

End Semantics.

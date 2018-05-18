Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool ssrnat eqtype.
Require Import ZArith.
Require Peano.

(* We axiomatize a random number generator
   (currently written in OCaml only) *)
Axiom RandomSeed : Type.
Axiom randomSeed_inhabited : inhabited RandomSeed.

Axiom mkRandomSeed   : Z          -> RandomSeed.
Axiom newRandomSeed  : RandomSeed.

(* begin randomSplitAssumption *)
Axiom randomSplit : RandomSeed -> RandomSeed * RandomSeed.
Axiom randomSplitAssumption :
  forall s1 s2 : RandomSeed, exists s, randomSplit s = (s1,s2).
(* end randomSplitAssumption *)

CoInductive RandomSeedTree :=
| RstNode : RandomSeed -> RandomSeedTree -> RandomSeedTree -> RandomSeedTree.

Definition root_rst (rst : RandomSeedTree) : RandomSeed :=
  match rst with
  | RstNode root _ _ => root
  end.

Definition left_rst (rst : RandomSeedTree) : RandomSeedTree :=
  match rst with
  | RstNode _ t1 _ => t1
  end.

Definition right_rst (rst : RandomSeedTree) : RandomSeedTree :=
  match rst with
  | RstNode _ _ t2 => t2
  end.

Lemma rst_eta : forall rst : RandomSeedTree,
  rst = RstNode (root_rst rst) (left_rst rst) (right_rst rst).
Proof. destruct rst. reflexivity. Qed.

CoFixpoint mkSeedTree (s : RandomSeed) : RandomSeedTree :=
  let (s1, s2) := randomSplit s in
  RstNode s (mkSeedTree s1) (mkSeedTree s2).

Lemma mkSeedTreeHelper r :
  mkSeedTree r = RstNode r (mkSeedTree (randomSplit r).1) (mkSeedTree (randomSplit r).2).
Proof. by rewrite [mkSeedTree _]rst_eta /=; case: (randomSplit r). Qed.

Inductive SplitDirection := Left | Right.

Definition SplitPath := list SplitDirection.

Require Import List. Import ListNotations.
Fixpoint varySeedAux (p : SplitPath) (rst : RandomSeedTree) : RandomSeed :=
  let '(RstNode s t1 t2) := rst in
  match p with 
    | [] => s 
    | Left  :: p' => varySeedAux p' t1
    | Right :: p' => varySeedAux p' t2
  end.

Definition varySeed (p : SplitPath) (s : RandomSeed) : RandomSeed :=
  varySeedAux p (mkSeedTree s).

(* Primitive generator combinators and some basic soundness
   assumptions about them *)

Set Bullet Behavior "Strict Subproofs".

Section RangeGens.
Import Peano.

Axiom randomBool : RandomSeed -> bool.
Axiom randomBoolCorrect :
  forall b, exists seed, randomBool seed = b.

(* Generate a number in [\[0, n)]. *)
Axiom randomNat : RandomSeed -> nat -> nat.
Axiom randomNatSound : forall s n, 0 < n -> randomNat s n < n.
Axiom randomNatComplete :
  forall n m, n < m -> exists s, randomNat s m = n.

Axiom randomInt : RandomSeed -> Z -> Z.
Axiom randomIntSound : forall s n, (0 < n -> 0 <= randomInt s n < n)%Z.
Axiom randomIntComplete :
  forall n m, (0 <= n < m)%Z -> exists s, randomInt s m = n.

Definition randomRNat '(m, n) s := m + randomNat s (n-m+1).
Definition randomRInt '(m, n) s := (m + randomInt s (n-m+1))%Z.

Lemma randomRNatCorrect:
  forall n n1 n2, n1 <= n2 ->
    (n1 <= n <= n2 <->
    exists seed, (randomRNat (n1, n2) seed) = n).
Proof.
  intros n n1 n2 H0.
  split.
  - intros [H1 H2].
    pose proof (randomNatComplete (n-n1) (n2-n1+1)) as complete.
    apply (fun f x => f (complete x));
      [intros [s Hs]; exists s; simpl |]; intuition.
  - simpl; intros [s H1].
    pose proof (randomNatSound s (n2 - n1 + 1)).
    intuition.
Qed.

Lemma randomRIntCorrect:
  forall z z1 z2, (z1 <= z2 ->
    (z1 <= z <= z2 <->
    exists seed, randomRInt (z1, z2) seed = z))%Z.
Proof.
  intros n n1 n2 H0.
  split.
  - intros [H1 H2].
    pose proof (randomIntComplete (n-n1) (n2-n1+1)) as complete.
    apply (fun f x => f (complete x));
      [intros [s Hs]; exists s; simpl |]; intuition.
  - simpl; intros [s H1].
    pose proof (randomIntSound s (n2 - n1 + 1)).
    intuition.
Qed.

End RangeGens.

Lemma randomRNatCorrect_ :
  forall n n1 n2, n1 <= n2 ->
    (n1 <= n <= n2 <->
     exists seed, randomRNat (n1, n2) seed = n).
Proof.
  intros.
  transitivity (n1 <= n /\ n <= n2)%coq_nat.
  - split.
    + intros Hn0.
      apply andb_prop in Hn0 as [Hn1 Hn2].
      split;
        apply (Bool.reflect_iff _ _ leP); auto.
    + intros [Hn1 Hn2].
      apply andb_true_intro.
      split;
        apply (Bool.reflect_iff _ _ leP); auto.
  - apply randomRNatCorrect; auto.
    apply (Bool.reflect_iff _ _ leP); auto.
Qed.

Lemma randomRIntCorrect_ :
  forall n n1 n2, (n1 <=? n2 ->
    (andb (n1 <=? n) (n <=? n2) = true <->
     exists seed, randomRInt (n1, n2) seed = n))%Z.
Proof.
  intros.
  pose proof Z.leb_spec0 as ZP.
  transitivity (n1 <= n /\ n <= n2)%Z.
  - split.
    + intros Hn0.
      apply andb_prop in Hn0 as [Hn1 Hn2].
      split;
        apply (Bool.reflect_iff _ _ (ZP _ _)); auto.
    + intros [Hn1 Hn2].
      apply andb_true_intro.
      split;
        apply (Bool.reflect_iff _ _ (ZP _ _)); auto.
  - apply randomRIntCorrect; auto.
    apply (Bool.reflect_iff _ _ (ZP _ _)); auto.
Qed.

(* A small experiment showing that infinite random trees
   are a potential model of the randomSplitAssumption *)

Module InfiniteTrees.
  CoInductive RandomSeed : Type :=
  | Node : bool -> RandomSeed -> RandomSeed -> RandomSeed.

  Definition randomSplit (s : RandomSeed) :=
    match s with
    | Node b s1 s2 => (s1,s2)
    end.

  Lemma randomSplitAssumption :
    forall s1 s2 : RandomSeed, exists s, randomSplit s = (s1,s2).
  Proof.
    move => s1 s2. by exists (Node true s1 s2).
  Qed.
End InfiniteTrees.


(* Type class machinery for generating things in intervals *)

Class OrdType (A: Type) :=
  {
    leq     : A -> A -> bool;
    refl    : reflexive leq;
    trans   : transitive leq;
    antisym : antisymmetric leq
  }.

Program Instance OrdBool : OrdType bool :=
  {
    leq b1 b2 := implb b1 b2
  }.
Next Obligation.
  by case.
Qed.
Next Obligation.
  by do 3! case.
Qed.
Next Obligation.
  by do 2! case.
Qed.

Program Instance OrdNat : OrdType nat :=
  {
    leq := ssrnat.leq;
    refl := leqnn;
    trans := leq_trans;
    antisym := anti_leq
  }.

Program Instance OrdZ : OrdType Z :=
  {
    leq := Z.leb;
    refl := Z.leb_refl
  }.
Next Obligation.
move=> x y z le_yx le_xz.
exact: (Zle_bool_trans y x z).
Qed.
Next Obligation.
move=> x y /andP[].
exact: Zle_bool_antisym.
Qed.

Class ChoosableFromInterval (A : Type)  :=
  {
    super :> OrdType A;
    randomR : A * A -> RandomSeed -> A;
    randomRCorrect :
      forall (a a1 a2 : A), leq a1 a2 ->
      (leq a1 a && leq a a2 <->
       exists seed, randomR (a1, a2) seed = a)
  }.

Instance ChooseNat : ChoosableFromInterval nat :=
  {
    randomR := randomRNat;
    randomRCorrect := randomRNatCorrect_
  }.

Instance ChooseZ : ChoosableFromInterval Z :=
  {
    randomR := randomRInt;
    randomRCorrect := randomRIntCorrect_
  }.

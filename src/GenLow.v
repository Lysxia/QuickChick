Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import ZArith List.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool ssrnat.
Require Import Numbers.BinNums.
Require Import Classes.RelationClasses.

From ExtLib.Structures Require Export
     Monads.
From ExtLib.Structures Require Import
     Functor Applicative.
Import MonadNotation.
Open Scope monad_scope.

From QuickChick Require Import
     Splittable SplittableTheory GenLowInterface RoseTrees Sets Tactics.

From QuickChick Require RandomQC.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Import ListNotations.

(* Low-level Generators *)

Open Scope fun_scope.
Open Scope set_scope.

Module Raw.

  Definition G (A : Type) : Type :=
    forall seed `{Splittable seed}, nat -> seed -> A.

  Definition extensional {A : Type} (g : G A) : Prop :=
    forall seed `{Splittable seed} n,
      codom (g seed _ n) \subset
      codom (g Finite.Tree _ n).

  Definition semGenSize {A : Type} (g : G A) (n : nat) : set A :=
    codom (g Finite.Tree _ n).

  Definition semGen {A : Type} (g : G A) : set A :=
    \bigcup_s semGenSize g s.

  Lemma semGenWithSize {A : Type} (g : G A) (n : nat) (x : A) :
    x \in semGenSize g n -> x \in semGen g.
  Proof.
    exists n; split; [constructor | auto].
  Qed.

  Definition ret {A : Type} (x : A) : G A :=
    fun _ _ _ _ => x.

  Lemma extensionalRet {A : Type} {x : A} : extensional (ret x).
  Proof.
    intros seed Sseed n a [? Hseed].
    destruct Finite.inhabited_Tree as [t].
    exists t; auto.
  Qed.

  Definition bind {A B : Type} (g : G A) (k : A -> G B) : G B :=
    fun _ _ n s =>
      let '(s1, s2) := randomSplit s in
      k (g _ _ n s1) _ _ n s2.

  Lemma extensionalBind {A B : Type} {g : G A} {k : A -> G B} :
    extensional g ->
    (forall a, (a \in semGen g) -> extensional (k a)) ->
    extensional (bind g k).
  Proof.
    intros ext_g ext_k seed Sseed n b [s Hs].
    unfold bind in *.
    destruct (randomSplit s) as [s1 s2].
    specialize (ext_g _ _ n (g _ _ n s1) codom_apply).
    destruct (ext_k _ (semGenWithSize ext_g) _ _ n
                    (k (g _ _ n s1) _ _ n s2) codom_apply)
      as [t2 Ht2].
    destruct ext_g as [t1 Ht1].
    exists (Finite.CoRandomSplit (t1, t2)); simpl.
    rewrite Ht1 Ht2. auto.
  Qed.

  Definition fmap {A B : Type} (f : A -> B) (g : G A) : G B :=
    (fun _ _ n s => f (g _ _ n s)).

  Lemma extensionalFmap {A B : Type} {f : A -> B} {g : G A} :
    extensional g ->
    extensional (fmap f g).
  Proof.
    intros ext_g seed Sseed n b [s Hseed].
    destruct (ext_g _ _ n (g _ _ n s) codom_apply) as [t Ht].
    exists t; unfold fmap in *; rewrite Ht; auto.
  Qed.

  Definition sized {A : Type} (f : nat -> G A) : G A :=
    (fun _ _ n s => f n _ _ n s).

  Definition resize {A : Type} (n : nat) (g : G A) : G A :=
    (fun _ _ _ => g _ _ n).

  Lemma extensionalSized {A : Type} {f : nat -> G A} :
    (forall n, extensional (f n)) ->
    extensional (sized f).
  Proof.
    intros ext_f seed Sseed n b [s Hseed].
    destruct (ext_f n _ _ n (f n _ _ n s) codom_apply) as [t Ht].
    exists t; unfold sized in *; rewrite Ht; auto.
  Qed.

  Lemma extensionalResize {A : Type} {n : nat} {g : G A} :
    extensional g ->
    extensional (resize n g).
  Proof.
    intros ext_g seed Sseed n' b [s Hseed].
    destruct (ext_g _ _ n (g _ _ n s) codom_apply) as [t Ht].
    exists t; unfold resize in *; rewrite Ht; auto.
  Qed.

  Definition promote {A : Type} (m : Rose (G A)) : G (Rose A) :=
    fun _ _ n s => fmapRose (fun g => g _ _ n s) m.

  (* More things *)
  Definition bind_aux' {A seed : Type} `{Splittable seed}
             {g : G A} (ext_g : extensional g)
             {n : nat} {s : seed} : semGen g (g _ _ n s).
  Proof.
    exists n; split; [ constructor | ].
    eapply ext_g.
    apply codom_apply.
  Qed.

  Definition bind' {A B : Type} (g : G A) (ext_g : extensional g)
             (k : forall (a : A), (a \in semGen g) -> G B)
    : G B :=
    fun _ _ n s =>
      let '(s1, s2) := randomSplit s in
      k (g _ _ n s1) (bind_aux' ext_g) _ _ n s2.

  Lemma extensionalBind' {A B : Type} {g : G A}
        {k : forall a : A, a \in semGen g -> G B}
        (ext_g : extensional g) :
    (forall a (H : a \in semGen g), extensional (k a H)) ->
    extensional (bind' ext_g k).
  Proof.
    (* Unprovable, needs at least UIP *)
  Admitted.
(*
    intros ext_k seed Sseed n b [s Hs].
    unfold bind' in *.
    destruct (randomSplit s) as [s1 s2].
    pose proof (ext_g _ _ n (g _ _ n s1) codom_apply) as ext_g'.
    destruct (ext_k _ (semGenWithSize ext_g') _ _ n
                    (k (g _ _ n s1) _ _ _ n s2) codom_apply)
      as [t2 Ht2].
    destruct ext_g' as [t1 Ht1].
    exists (Finite.CoRandomSplit (t1, t2)); simpl.
    rewrite Ht1 Ht2. auto.
  Qed.
*)

End Raw.

Module GenLow : GenLowInterface.Sig.

  (** * Type of generators *)

  (* begin GenType *)
  Record GenType (A : Type) : Type := MkGen {
    runGen : Raw.G A;
    extGen : Raw.extensional runGen;
  }.
  (* end GenType *)

  Arguments extGen {A g}.
  
  Definition G := GenType.

  (** * Primitive generator combinators *)

  (* begin run *)
  Definition run {A seed : Type} `{Splittable seed} (g : G A) :
    nat -> seed -> A := runGen g _.
  (* end run *)

  Definition returnGen {A : Type} (x : A) : G A := {|
    runGen := Raw.ret x;
    extGen := Raw.extensionalRet;
  |}.

  Definition bindGen {A B : Type} (g : G A) (k : A -> G B) : G B := {|
    runGen := Raw.bind (runGen g) (fun x => runGen (k x));
    extGen := Raw.extensionalBind extGen (fun _ _ => extGen);
  |}.

  Definition bindGenOpt {A B} (g : G (option A)) (f : A -> G (option B)) : G (option B) :=
    bindGen g (fun ma =>
                 match ma with
                   | None => returnGen None
                   | Some a => f a
                 end).

  Definition fmap {A B : Type} (f : A -> B) (g : G A) : G B := {|
    runGen := Raw.fmap f (runGen g);
    extGen := Raw.extensionalFmap extGen;
  |}.

  Definition apGen {A B} (gf : G (A -> B)) (gg : G A) : G B :=
    bindGen gf (fun f => fmap f gg).

  Definition sized {A : Type} (f : nat -> G A) : G A := {|
    runGen := Raw.sized (fun n => runGen (f n));
    extGen := Raw.extensionalSized (fun n => extGen);
  |}.

  Definition resize {A : Type} (n : nat) (g : G A) : G A := {|
    runGen := Raw.resize n (runGen g);
    extGen := Raw.extensionalResize extGen;
  |}.

(*
  Definition promote {A : Type} (m : Rose (G A)) : G (Rose A) :=
    MkGen (fun _ _ n r => fmapRose (fun g => run g n r) m).
*)

  Fixpoint rnds {seed} `{Splittable seed}
           (s : seed) (n' : nat) : list seed :=
    match n' with
      | O => nil
      | S n'' =>
        let (s1, s2) := randomSplit s in
        cons s1 (rnds s2 n'')
    end.
  
  Fixpoint createRange (n : nat) (acc : list nat) : list nat :=
    match n with
      | O => List.rev (cons O acc)
      | S n' => createRange n' (cons n acc)
    end.

  Definition choose {A : Type} `{RandomQC.ChoosableFromInterval A} (range : A * A) : G A.
  Admitted. (*
    MkGen (fun _ r => fst (randomR range r)). *)

(*
  Definition sample (A : Type) (g : G A) : list A :=
    match g with
      | MkGen m =>
        let rnd := newRandomSeed in
        let l := List.combine (rnds rnd 20) (createRange 10 nil) in
        List.map (fun (p : RandomSeed * nat) => let (r,n) := p in m n r) l
    end.
  
  (* LL : Things that need to be in GenLow because of MkGen *)
  
  Definition variant {A : Type} (p : SplitPath) (g : G A) : G A := 
    match g with 
      | MkGen f => MkGen (fun n r => f n (varySeed p r))
    end.
  
  Definition reallyUnsafeDelay {A : Type} : G (G A -> A) :=
    MkGen (fun r n g => (match g with MkGen f => f r n end)).
  
  Definition reallyUnsafePromote {r A : Type} (m : r -> G A) : G (r -> A) :=
    (bindGen reallyUnsafeDelay (fun eval => 
                                  returnGen (fun r => eval (m r)))).
*)

  (* End Things *)

  (** * Semantics of generators *)

  (* Set of outcomes semantics definitions (repeated above) *)
  (* begin semGen *)
  Definition semGenSize {A : Type} (g : G A) (s : nat) : set A :=
    codom (@run _ Finite.Tree _ g s).
  Definition semGen {A : Type} (g : G A) : set A := \bigcup_s semGenSize g s.

  Definition semGenSizeOpt {A : Type} (g : G (option A)) (s : nat) : set A :=
    somes (semGenSize g s).

  Definition semGenOpt {A : Type} (g : G (option A)) : set A :=
    somes (semGen g).
  (* end semGen *)

  Lemma semGenOpt_equiv {A} (g : G (option A)) :
    semGenOpt g <--> \bigcup_s semGenSizeOpt g s.
  Proof.
    split; intros [n [Hn [t H]]];
      (exists n; split; [constructor | exists t; auto]).
  Qed.

  Definition bindGen' {A B : Type} (g : G A) (k : forall (a : A), (a \in semGen g) -> G B) : G B := {|
    runGen := Raw.bind' extGen (fun a H => runGen (k a H));
    extGen :=  Raw.extensionalBind' (fun _ _ => extGen);
  |}.

  (** * Semantic properties of generators *)

  Class Unsized {A} (g : G A) :=
    unsized : forall s1 s2, semGenSize g s1 <--> semGenSize g s2.
  
  Class SizedMonotonic {A} (g : nat -> G A) :=
    (* TODO remove prime when GenSizedSizeMotonic is modified *)
    sizeMonotonic : forall s s1 s2,
      s1 <= s2 ->
      semGenSize (g s1) s \subset semGenSize (g s2) s.

  (** Sized generators of option type monotonic in the size parameter *)
  Class SizedMonotonicOpt {A} (g : nat -> G (option A)) :=
    sizeMonotonicOpt : forall s s1 s2,
      s1 <= s2 ->
      semGenSizeOpt (g s1) s \subset semGenSizeOpt (g s2) s.
  
  (** Generators monotonic in the runtime size parameter *)
  Class SizeMonotonic {A} (g : G A) :=
    monotonic : forall s1 s2,
      s1 <= s2 -> semGenSize g s1 \subset semGenSize g s2.

  (** Generators monotonic in the runtime size parameter *)
  Class SizeMonotonicOpt {A} (g : G (option A)) :=
    monotonicOpt : forall s1 s2,
      s1 <= s2 ->
      semGenSizeOpt g s1 \subset semGenSizeOpt g s2.

  Class SizeAntiMonotonicNone {A} (g : G (option A)) :=
    monotonicNone : forall s1 s2,
      s1 <= s2 ->
      isNone :&: semGenSize g s2 \subset isNone :&: semGenSize g s1.

  (* Unsizedness trivially implies size-monotonicity *)
  Lemma unsizedMonotonic {A} (g : G A) : Unsized g -> SizeMonotonic g. 
  Proof.
    intros s1 s2 Hleq.
    rewrite /unsized /monotonic => a H12.
      by apply unsized.
  Qed.
  
  Lemma unsized_alt_def :
    forall A (g : G A) `{Unsized _ g},
    forall s, semGenSize g s <--> semGen g.
  Proof.
    move => A f H s a. split.
    move => H'. exists s. split; auto => //.
    move => [s' [_ H']]. eapply unsized; eauto.
  Qed.

  (** * Semantics of combinators *)

  (* begin semReturn *)
  Lemma semReturn {A} (x : A) : semGen (returnGen x) <--> [set x].
  (* end semReturn *)
  Proof.
    rewrite /semGen /semGenSize /=. unfold Raw.ret.
    rewrite bigcup_const; [|do 2 constructor].
    rewrite codom_const; [| exact Finite.inhabited_Tree].
    reflexivity.
  Qed.
  
  (* begin semReturnSize *)
  Lemma semReturnSize A (x : A) (s : nat) :
  semGenSize (returnGen x) s <--> [set x].
  (* end semReturnSize *)
  Proof.
    unfold semGenSize.
    rewrite codom_const;
      [ reflexivity | apply Finite.inhabited_Tree ].
  Qed.
  
  Instance unsizedReturn {A} (x : A) : Unsized (returnGen x).
  Proof. firstorder. Qed.
  
  Instance returnGenSizeMonotonic {A} (x : A) : SizeMonotonic (returnGen x).
  Proof. firstorder. Qed.

  Instance returnGenSizeMonotonicOpt {A} (x : option A) : SizeMonotonicOpt (returnGen x).
  Proof. firstorder. Qed.
  
  (* begin semBindSize *)
  Lemma semBindSize A B (g : G A) (f : A -> G B) (s : nat) :
    semGenSize (bindGen g f) s <-->
    \bigcup_(a in semGenSize g s) semGenSize (f a) s.
  (* end semBindSize *)
  Proof.
    rewrite /semGenSize /bindGen /= bigcup_codom -curry_codom2l.
      by rewrite -[codom (prod_curry _)]imsetT -randomSplit_codom -codom_comp.
  Qed.
  
  Lemma semBindSize_subset_compat {A B : Type} (g g' : G A) (f f' : A -> G B) :
    (forall s, semGenSize g s \subset semGenSize g' s) ->
    (forall x s, semGenSize (f x) s \subset semGenSize (f' x) s) ->
    (forall s, semGenSize (bindGen g f) s \subset semGenSize (bindGen g' f') s).
  Proof.
    intros H1 H2 s. rewrite !semBindSize.
    eapply subset_trans.
    eapply incl_bigcupl. eapply H1.
    eapply incl_bigcupr. intros; eapply H2.
  Qed.
  
  Lemma semBindSizeOpt_subset_compat {A B : Type} (g g' : G A) (f f' : A -> G (option B)) :
    (forall s, semGenSize g s \subset semGenSize g' s) ->
    (forall x s, isSome :&: semGenSize (f x) s \subset isSome :&: semGenSize (f' x) s) ->
    (forall s, isSome :&: semGenSize (bindGen g f) s \subset isSome :&: semGenSize (bindGen g' f') s).
  Proof.
    intros H1 H2 s. rewrite !semBindSize.
    eapply subset_trans.
    eapply setI_subset_compat. eapply subset_refl.
    eapply incl_bigcupl. eapply H1.
    rewrite !setI_bigcup_assoc. 
    eapply incl_bigcupr. intros. eapply H2.
  Qed.
  
  Lemma monad_leftid A B (a : A) (f : A -> G B) :
    semGen (bindGen (returnGen a) f) <--> semGen (f a).
  Proof.
      by apply: eq_bigcupr => size; rewrite semBindSize semReturnSize bigcup_set1.
  Qed.
  
  Lemma monad_rightid A (g : G A) : semGen (bindGen g returnGen) <--> semGen g.
  Proof.
    apply: eq_bigcupr => size; rewrite semBindSize.
      by rewrite (eq_bigcupr _ (fun x => semReturnSize x size))
                 /semGenSize bigcup_codom codomE.
  Qed.
  
  Lemma monad_assoc A B C (ga : G A) (fb : A -> G B) (fc : B -> G C) :
    semGen (bindGen (bindGen ga fb) fc) <--> 
    semGen (bindGen ga (fun a => bindGen (fb a) fc)).
  Proof.
    apply eq_bigcupr => ?; rewrite !semBindSize ?bigcup_flatten.
    by apply eq_bigcupr => ?; rewrite !semBindSize ?bigcup_flatten.
  Qed.

  Instance bindUnsized
          {A B} (g : G A) (f : A -> G B) `{Unsized _ g} `{forall x, Unsized (f x)} : 
    Unsized (bindGen g f).
  Proof.
    intros s1 s2.
    rewrite !semBindSize !unsized_alt_def. move => b. 
    split; move => [a [H1 H2]]; exists a; split => //; by eapply unsized; eauto.
  Qed.
  
  Instance bindMonotonic
          {A B} (g : G A) (f : A -> G B) `{SizeMonotonic _ g} `{forall x, SizeMonotonic (f x)} : 
    SizeMonotonic (bindGen g f).
  Proof.
    intros s1 s2 Hs.
    rewrite !semBindSize. move => b.
    move => [a [H3 H4]]; exists a; split => //; eapply monotonic; eauto.
  Qed.

  Instance bindMonotonicOpt
          {A B} (g : G A) (f : A -> G (option B))
          `{SizeMonotonic _ g} `{forall x, SizeMonotonicOpt (f x)} : 
    SizeMonotonicOpt (bindGen g f).
  Proof.
    intros s1 s2 Hs.
    unfold semGenSizeOpt.
    rewrite !semBindSize. move => b.
    move => [a [Hsome [H4 H5]]].
    eexists a; split => //. eapply monotonic; eauto.
    eapply monotonicOpt; eauto; eexists; eauto.
  Qed.

  Instance bindMonotonicStrong
          {A B} (g : G A) (f : A -> G B) `{SizeMonotonic _ g}
          `{forall x, semGen g x -> SizeMonotonic (f x)} :
    SizeMonotonic (bindGen g f).
  Proof.
    intros s1 s2 Hleq.
    rewrite !semBindSize. move => b.
    move => [a [H3 H4]]; exists a; split => //.
    now eapply monotonic; eauto.
    eapply H0.
    eexists. split; eauto. now constructor.
    eassumption.
    eassumption.
  Qed.
  
  Instance bindMonotonicOptStrong
          {A B} (g : G A) (f : A -> G (option B)) `{SizeMonotonic _ g}
          `{forall x, semGen g x -> SizeMonotonicOpt (f x)} :
    SizeMonotonicOpt (bindGen g f).
  Proof.
    intros s1 s2 Hleq.
    unfold semGenSizeOpt.
    rewrite !semBindSize. move => b.
    move => [a [Hsome [H4 H5]]].
    exists a; split => //.
    - eapply monotonic; eauto.
    - eapply H0; eauto. exists s1; split; auto. constructor.
      eexists; eauto.
  Qed.

  Instance bindOptMonotonic
           {A B} (g : G (option A)) (f : A -> G (option B))
           `{SizeMonotonic _ g} `{forall x, SizeMonotonic (f x)} :
    SizeMonotonic (bindGenOpt g f).
  Proof.
    intros s1 s2 Hleq.
    intros x Hx. eapply semBindSize in Hx.
    destruct Hx as [a [Hg Hf]].
    destruct a as [a | ].
    - eapply H in Hg; try eassumption.
      eapply H0 in Hf; try eassumption.
      eapply semBindSize.
      eexists; split; eauto.
    - eapply H in Hg; try eassumption.
      eapply semReturnSize in Hf. inv Hf.
      eapply semBindSize.
      eexists; split; eauto. simpl.
      eapply semReturnSize.
      reflexivity.
  Qed.
  
  (* begin semBindUnsized1 *)
  Lemma semBindUnsized1 {A B} (g : G A) (f : A -> G B) `{H : Unsized _ g}:
    semGen (bindGen g f) <--> \bigcup_(a in semGen g) semGen (f a).
  (* end semBindUnsized1 *)
  Proof.
    rewrite /semGen. setoid_rewrite semBindSize.
    setoid_rewrite (@unsized_alt_def A g H). move => b. split.
    - intros [s [_ [a [H1 H2]]]].
      exists a. split; exists s; split; by [].
    - intros [a [[s1 [_ H1]] [s2 [_ H2]]]]. 
      exists s2. split; first by [].
      exists a. split; by [].
  Qed.
  
  Lemma semBindUnsized2 :
    forall A B (g : G A) (f : A -> G B),
      (forall a, Unsized (f a)) ->
      semGen (bindGen g f) <--> \bigcup_(a in semGen g) semGen (f a).
  Proof.
    move=> A B g f H.
    rewrite /semGen. setoid_rewrite semBindSize.
    intro b. split.
    - intros [s [_ [a [H1 H2]]]].
      exists a. split; exists s; split => //. 
    - intros [a [[s1 [_ H1]] [s2 [_  H2]]]].
      exists s1. split; first by []. exists a. 
      split; first by []; apply unsized_alt_def; eauto.
        by eapply unsized_alt_def; eauto.
  Qed.

  (* begin semBindSizeMonotonic *)
  Lemma semBindSizeMonotonic {A B} (g : G A) (f : A -> G B)
        `{Hg : SizeMonotonic _ g} `{Hf : forall a, SizeMonotonic (f a)} :
    semGen (bindGen g f) <--> \bigcup_(a in semGen g) semGen (f a).
  (* end semBindSizeMonotonic *)
  Proof.
    rewrite /semGen. setoid_rewrite semBindSize.
    intro b. split.
    - intros [s [_ [a [H1 H2]]]].
      exists a. split; exists s; (split; first (compute; by []); first by[]).
    - intros [a [[s1 [_ H1]] [s2 [_ H2]]]]. exists (max s1 s2).
      split; first (compute; by []).
      exists a. split.
      eapply Hg; last eassumption. by apply/leP; apply Max.le_max_l.
      eapply Hf; last eassumption. by apply/leP; apply Max.le_max_r.
  Qed.
  
  Lemma semFmapSize A B (f : A -> B) (g : G A) (size : nat) :
    semGenSize (fmap f g) size <--> f @: semGenSize g size.  Proof.
      by rewrite /fmap /semGenSize /= codom_comp.
  Qed.
  
  Lemma semFmap A B (f : A -> B) (g : G A) :
    semGen (fmap f g) <--> f @: semGen g.
  Proof.
      by rewrite imset_bigcup /semGen (eq_bigcupr _ (semFmapSize _ _)).
  Qed.
  
  Instance fmapUnsized {A B} (f : A -> B) (g : G A) `{Unsized _ g} :
    Unsized (fmap f g).
  Proof.
    intros s1 s2.
    rewrite !semFmapSize. move => b.
      by split; move => [a [H1 <-]]; eexists; split; eauto => //; eapply unsized; eauto.
  Qed.
  
  Instance fmapMonotonic
          {A B} (f : A -> B) (g : G A) `{SizeMonotonic _ g} : 
    SizeMonotonic (fmap f g).
  Proof.
    intros s1 s2 Hs.
    rewrite !semFmapSize. move => b.
    move => [a [H1 <-]]; eexists; split; eauto => //; eapply monotonic; eauto.
  Qed.

  Lemma semChooseSize A `{RandomQC.ChoosableFromInterval A} (a1 a2 : A) :
    RandomQC.leq a1 a2 ->
    forall size, semGenSize (choose (a1,a2)) size <-->
                       [set a | RandomQC.leq a1 a && RandomQC.leq a a2].
  Proof.
  Admitted. (* by move=> /= le_a1a2 m n; rewrite (randomRCorrect n a1 a2). Qed. *)
  
  Instance chooseUnsized {A} `{RandomQC.ChoosableFromInterval A} (a1 a2 : A) :
    Unsized (choose (a1, a2)).
  Admitted. (* by []. Qed. *)
  
  Lemma semChoose A `{RandomQC.ChoosableFromInterval A} (a1 a2 : A) :
    RandomQC.leq a1 a2 ->
    (semGen (choose (a1,a2)) <--> [set a | RandomQC.leq a1 a && RandomQC.leq a a2]).
  Proof.
  Admitted. (*
    move=> /= le_a1a2. rewrite <- (unsized_alt_def 1).
    move => m /=. rewrite (randomRCorrect m a1 a2) //.
  Qed.

  Lemma promoteVariant :
    forall {A B : Type} (a : A) (f : A -> SplitPath) (g : G B) size
      (r r1 r2 : RandomSeed),
      randomSplit r = (r1, r2) ->
      run (reallyUnsafePromote (fun a => variant (f a) g)) size r a =
      run g size (varySeed (f a) r1).
  Proof.
    move => A B a p g size r r1 r2 H.
    rewrite /reallyUnsafePromote /variant.
    destruct g. rewrite /= H. by [].
  Qed.

  Lemma semPromote A (m : Rose (G A)) :
    semGen (promote m) <-->
    codom2 (fun size seed => fmapRose (fun g => run g size seed) m).
  Proof. by rewrite /codom2 curry_codom2l. Qed.

  Lemma semPromoteSize (A : Type) (m : Rose (G A)) n :
    semGenSize (promote m) n <-->
               codom (fun seed => fmapRose (fun g => run g n seed) m).
  Proof. by []. Qed.

  Lemma runPromote A (m : Rose (G A)) seed size :
    run (promote m) seed size = fmapRose (fun (g : G A) => run g seed size) m.
  Proof. by []. Qed.
*)

  Lemma runFmap (A B : Type) (f : A -> B) (g : G A) seed size :
    run (fmap f g) seed size = f (run g seed size).
  Proof. by []. Qed.

  Lemma semFmapBind :
    forall A B C (g : G A) (f1 : B -> C) (f2 : A -> G B),
      semGen (fmap f1 (bindGen g f2)) <-->
      semGen (bindGen g (fun x => fmap f1 (f2 x))).
  Proof.
    intros. rewrite /semGen. setoid_rewrite semFmapSize.
    setoid_rewrite semBindSize.
    apply eq_bigcupr => s. setoid_rewrite semFmapSize.
    rewrite imset_bigcup. reflexivity.
  Qed.

  Lemma semSized A (f : nat -> G A) :
    semGen (sized f) <--> \bigcup_n semGenSize (f n) n.
  Proof. by []. Qed.

  Lemma semSizedSize A(f:nat->G A)s : semGenSize (sized f) s <--> semGenSize (f s) s.
  Proof. by []. Qed.

  Lemma semSized_opt A (f : nat -> G (option A)) (H : forall n, SizeMonotonicOpt (f n)) (H' : SizedMonotonicOpt f) :
    isSome :&: semGen (sized f) <--> isSome :&: \bigcup_n (semGen (f n)).
  Proof.
    rewrite semSized. rewrite !setI_bigcup_assoc.
    move => x; split.
    - move => [n [HT [Hs1 Hs2]]].
      eexists. split; eauto. split; eauto. eexists; eauto.
    - move => [n [HT [Hs1 [m [HT' Hs2]]]]].
      eexists (m + n).
      split. now constructor. 
      split; [ eassumption | ].
      destruct x as [ x | ].
      + eapply monotonicOpt with (s2 := m + n) in Hs2; [| now ssromega ].
        eapply sizeMonotonicOpt with (s1 := n) (s2 := m + n); [now ssromega |].
        auto.
      + inv Hs1.
  Qed.

  Lemma semSized_alt A (f : nat -> G A) (H : forall n, SizeMonotonic (f n))
        (H' : forall n m s,  n <= m -> semGenSize (f n) s \subset semGenSize (f m) s) :
    semGen (sized f) <--> \bigcup_n (semGen (f n)).
  Proof.
    rewrite semSized.
    move => x; split.
    - move => [n [HT Hs]].
      eexists. split; eauto. eexists; eauto.
    - move => [n [HT [m [_ Hs]]]].
      eapply semSized. eexists (m + n).
      split. constructor. 
      eapply (H' n). ssromega.
      eapply (H n); try eassumption. ssromega.
  Qed.

  Instance sizedSizeMonotonic
           A (gen : nat -> G A) `{forall n, SizeMonotonic (gen n)} `{SizedMonotonic A gen} :
    SizeMonotonic (sized gen).
  Proof.
    move => s1 s2 Hleq a /semSizedSize H1.
    eapply semSizedSize.
    eapply H. eassumption.
    eapply H0; eassumption.
  Qed.

  Instance sizedSizeMonotonicOpt
          A (gen : nat -> G (option A)) `{forall n, SizeMonotonic (gen n)} `{SizedMonotonicOpt A gen} :
    SizeMonotonicOpt (sized gen).
  Proof.
    move => s1 s2 Hleq a H1.
    eapply semSizedSize.
    eapply H. eassumption.
    unfold semGenSizeOpt in H1.
    unfold somes in H1.
    eapply @sizeMonotonicOpt; eauto.
  Qed.
  
  Lemma semResize A n (g : G A) : semGen (resize n g) <--> semGenSize g n .
  Proof. firstorder. Qed.

  Lemma semSizeResize A (s n : nat) (g : G A) :
    semGenSize (resize n g) s <--> semGenSize g n.
  Proof. firstorder. Qed.
  
  Instance unsizedResize {A} (g : G A) n :
    Unsized (resize n g).
  Proof. firstorder. Qed.


  Lemma semGenSizeInhabited {A} (g : G A) s :
    exists x, semGenSize g s x.
  Proof.
    destruct Finite.inhabited_Tree as [r].
    eexists (run g s r ). unfold semGenSize, codom.
    exists r. reflexivity.
  Qed.

(*
  Lemma promoteVariant :
    forall {A B : Type} (a : A) (f : A -> SplitPath) (g : G B) size
      (r r1 r2 : RandomSeed),
      randomSplit r = (r1, r2) ->
      run (reallyUnsafePromote (fun a => variant (f a) g)) size r a =
      run g size (varySeed (f a) r1).
  Proof.
    move => A B a p g size r r1 r2 H.
    rewrite /reallyUnsafePromote /variant.
    destruct g. rewrite /= H. by [].
  Qed.

  Lemma semPromote A (m : Rose (G A)) :
    semGen (promote m) <-->
    codom2 (fun size seed => fmapRose (fun g => run g size seed) m).
  Proof. by rewrite /codom2 curry_codom2l. Qed.

  Lemma semPromoteSize (A : Type) (m : Rose (G A)) n :
    semGenSize (promote m) n <-->
               codom (fun seed => fmapRose (fun g => run g n seed) m).
  Proof. by []. Qed.

  Lemma runPromote A (m : Rose (G A)) seed size :
    run (promote m) seed size = fmapRose (fun (g : G A) => run g seed size) m.
  Proof. by []. Qed.
*)

  Instance Functor_G : Functor G := {
    fmap A B := fmap;
  }.

  Instance Applicative_G : Applicative G := {
    pure A := returnGen;
    ap A B := apGen;
  }.

  Instance Monad_G : Monad G := {
    ret A := returnGen;
    bind A B := bindGen;
  }.

  Definition thunkGen {A} (f : unit -> G A) : G A := {|
    runGen := fun _ _ n r => runGen (f tt) _ n r;
    extGen := extGen;
  |}.

  Lemma semThunkGenSize {A} (f : unit -> G A) s :
    semGenSize (thunkGen f) s <--> semGenSize (f tt) s.
  Proof.
    split; intros [r Hr]; exists r; simpl in *; assumption.
  Qed.

  Lemma semThunkGen {A} (f : unit -> G A) :
    semGen (thunkGen f) <--> semGen (f tt).
  Proof.
    split; intros [r Hr]; exists r; simpl in *; assumption.
  Qed.

  Instance thunkGenUnsized {A} (f : unit -> G A)
          `{Unsized _ (f tt)} : Unsized (thunkGen f).
  Proof.
    intros s1 s2.
    do 2 rewrite semThunkGenSize.
    apply unsized.
  Qed.

  Instance thunkGenSizeMonotonic {A} (f : unit -> G A)
          `{SizeMonotonic _ (f tt)} : SizeMonotonic (thunkGen f).
  Proof.
    intros s1 s2 Hs.
    do 2 rewrite semThunkGenSize.
    by apply monotonic.
  Qed.

  Instance thunkGenSizeMonotonicOpt {A} (f : unit -> G (option A))
          `{SizeMonotonicOpt _ (f tt)} : SizeMonotonicOpt (thunkGen f).
  Proof.
    intros s1 s2 Hs. unfold semGenSizeOpt.
    do 2 rewrite semThunkGenSize.
    by apply monotonicOpt.
  Qed.

  Instance thunkGenSizeAntiMonotonicNone {A} (f : unit -> G (option A))
          `{SizeAntiMonotonicNone _ (f tt)} : SizeAntiMonotonicNone (thunkGen f).
  Proof.
    intros s1 s2 Hs.
    do 2 rewrite semThunkGenSize.
    by apply monotonicNone.
  Qed.

End GenLow.

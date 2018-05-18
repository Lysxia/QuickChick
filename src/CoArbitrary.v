Require Import PArith List.
From mathcomp Require Import ssrfun.

Require Import Classes RandomQC GenLow Sets.

Import ListNotations.

Set Bullet Behavior "Strict Subproofs".

Class Splittable (S : Type) : Type :=
  { split : S -> (S * S) }.

Instance Splittable_RandomSeed : Splittable RandomSeed :=
  { split := randomSplit }.

Class CoArbitrary (A : Type) : Type :=
  { coarbitrary :
      forall (S : Type) `{Splittable S}, A -> S -> S;
  }.

Arguments coarbitrary {A _ S _}.

Definition perturb_seed {A} `{CoArbitrary A} :
  A -> RandomSeed -> RandomSeed :=
  coarbitrary.

(* For every finite assignment of values of A to seeds, there
   is a seed that coincides with that assignment. Defining the
   assignment as the restriction of a function [f] to a finite
   support [xs] avoids issues with duplicate elements in the
   list, at least when stating this property.
*)
Class CoArbitraryCorrect (A : Type) `{CoArbitrary A} : Prop :=
  { coarbitrary_correct :
      forall (xs : list A) (f : A -> RandomSeed),
        exists (s : RandomSeed),
          Forall (fun x => f x = coarbitrary x s) xs;
  }.

(* A good CoArbitrary instance implicitly defines a
   tree of values, and making it explicit allows us to
   deduce a proof of correctness. *)
Module Import TreeCorrectness.

(* 50% shorter name. *)
Definition path := SplitPath.

Definition dir {A} d (f g : A) :=
  match d with
  | Left => f
  | Right => g
  end.

(* Splitting extends the path in either direction. *)
Definition split_path (x : path) : path * path :=
  (x ++ [Left], x ++ [Right]).

Instance Splittable_path : Splittable path :=
  { split := split_path }.

(* Using parametricity in [CoArbitrary], we can compute
   the path taken to perturb the seed for a given value. *)
Definition path_coarbitrary {A} `{CoArbitrary A} : A -> path :=
  fun a => coarbitrary a [].

(* The free theorem for [coarbitrary'], maybe not provable
   generally, (parametricity is not internal to Coq?)
   but provable for each [CoArbitrary A] individually.
*)
Class CoArbitraryParametric (A : Type) `{CoArbitrary A} : Prop :=
  { free_theorem_coarbitrary :
      forall (S T : Type) `{Splittable S, Splittable T}
             (R : S -> T -> Prop),
        (forall s0 t0,
            R s0 t0 ->
            R (fst (split s0)) (fst (split t0)) /\
            R (snd (split s0)) (snd (split t0))) ->
        forall a s t,
          (R s t) ->
          R (coarbitrary a s) (coarbitrary a t);
  }.

(* The following holds by parametricity. *)
Lemma path_coarb_app A `{CoArbitraryParametric A} :
  forall a p,
    coarbitrary a p = p ++ path_coarbitrary a.
Proof.
  intros a p.
  apply free_theorem_coarbitrary with
    (R := fun p0 q0 => p0 = p ++ q0).
  - intros s0 t0 Hs0.
    simpl.
    rewrite Hs0.
    repeat rewrite <- app_assoc.
    auto.
  - rewrite app_nil_r; reflexivity.
Qed.

(* Given a path, we can perturb a seed. *)
Fixpoint coarbitrary_path {S} `{Splittable S} (p : path) (s : S) :=
  match p with
  | [] => s
  | b :: p' =>
    let s' := dir b fst snd (split s) in
    coarbitrary_path p' s'
  end.

(* When [S = path], that function is [app] flipped. *)
Lemma coarbitrary_path_app :
  forall p q, coarbitrary_path p q = q ++ p.
Proof.
  induction p; intro q.
  - rewrite app_nil_r; reflexivity.
  - destruct a; simpl; rewrite IHp; rewrite <- app_assoc; reflexivity.
Qed.

Lemma coarbitrary_path_comm (A S : Type)
      `{CoArbitraryParametric A} `{Splittable S} :
  forall a (s : S) p,
    coarbitrary a (coarbitrary_path p s) =
    coarbitrary_path (coarbitrary a p) s.
Proof.
  intros a s p.
  apply free_theorem_coarbitrary with
    (R := fun s0 p0 => s0 = coarbitrary_path p0 s).
  - intros s0 t0. generalize dependent s. induction t0; intros; subst.
    + auto.
    + apply IHt0.
      reflexivity.
  - reflexivity.
Qed.

Lemma coarbitrary_path_comm_nil (A S : Type)
      `{CoArbitraryParametric A} `{Splittable S} :
  forall a s,
    coarbitrary a s =
    coarbitrary_path (path_coarbitrary a) s.
Proof.
  intros.
  apply coarbitrary_path_comm with (p := []).
  assumption.
Qed.

(* Paths are locations in trees.
   Note that trees may be infinite. *)
CoInductive tree (A : Type) : Type :=
| Split : tree A -> tree A -> tree A
| Leaf : A -> tree A
| Empty : tree A.

Arguments Split {A}.
Arguments Leaf {A}.
Arguments Empty {A}.

(* Useful to rewrite cofixpoints in proofs. *)
Lemma match_tree {A} (t : tree A) : t = match t with
                                        | Split t1 t2 => Split t1 t2
                                        | Leaf a => Leaf a
                                        | Empty => Empty
                                        end.
Proof. destruct t; auto. Qed.

Definition map_tree {A B} (f : A -> B) :=
  cofix map t :=
    match t with
    | Split t1 t2 => Split (map t1) (map t2)
    | Leaf a => Leaf (f a)
    | Empty => Empty
    end.

(* The monadic interface is useful for composite types
   (pairs, sums, etc.) *)
Definition bind_tree {A B} (t : tree A) (k : A -> tree B) : tree B :=
  (cofix sub t :=
     match t with
     | Split t1 t2 => Split (sub t1) (sub t2)
     | Leaf a => k a
     | Empty => Empty
     end) t.

(* A path [p] points to a value [a] in a tree [t]. *)
Fixpoint In_tree {A} (t : tree A) (a : A) (p : path) :=
  match p, t with
  | [], Leaf a' => a' = a
  | b :: p', Split t1 t2 =>
    In_tree (dir b t1 t2) a p'
  | _, _ => False
  end.

Lemma In_tree_map {A B}
      (f : A -> B) (t : tree A) (a : A) (p : path) :
  In_tree t a p -> In_tree (map_tree f t) (f a) p.
Proof.
  generalize dependent t.
  induction p as [ | [] p' ];
    intros [] Ht;
    try destruct Ht;
    try reflexivity;
    simpl; auto.
Qed.

Lemma In_tree_bind {A B}
      (t : tree A) (k : A -> tree B)
      (a : A) (pa : path) (b : B) (pb : path) :
  In_tree t a pa -> In_tree (k a) b pb ->
  In_tree (bind_tree t k) b (pa ++ pb).
Proof.
  generalize dependent t.
  induction pa as [ | [] pa' ]; intros [] Ht Hk;
    try destruct Ht;
    rewrite (match_tree (bind_tree _ _)); simpl;
    (rewrite <- match_tree; auto) +
    (apply IHpa'; auto).
Qed.

(* A path to [a] in tree [t], with constructors
   [Left], [Right], [Here]. *)
Definition tree_path {A} (t : tree A) (a : A) : Type :=
  sigT (In_tree t a).

Definition GoLeft {A} {a : A} {t1 t2} (p_ : tree_path t1 a) :
  tree_path (Split t1 t2) a :=
  existT _ (Left :: projT1 p_) (projT2 p_).

Definition GoRight {A} {a : A} {t1 t2} (p_ : tree_path t2 a) :
  tree_path (Split t1 t2) a :=
  existT _ (Right :: projT1 p_) (projT2 p_).

Definition GoHere {A} {a : A} : tree_path (Leaf a) a :=
  existT _ [] eq_refl.

(* Finite trees, meant to represent finite approximations of
   infinite trees. *)
Inductive pretree : Type :=
| Split_ : pretree -> pretree -> pretree
| Leaf_ : pretree
| Any_ : pretree.

(* This relation can be seen as a form of unifiability. *)
Fixpoint prefix_of {A} (t : tree A) (q : pretree) : Prop :=
  match q, t with
  | Split_ q1 q2, Split t1 t2 =>
    prefix_of t1 q1 /\ prefix_of t2 q2
  | Leaf_, Leaf _ => True
  | Any_, _ => True
  | _, _ => False
  end.

(* Universal quantification over values of a tree [t]
   covered by the prefix [q]. *)
(* TODO make it an inductive type. *)
Fixpoint ForallPT {A} (t : tree A) (q : pretree) :
  (forall a, tree_path t a -> Prop) -> Prop :=
  match q, t return (forall a, tree_path t a -> _) -> _ with
  | Split_ q1 q2, Split t1 t2 => fun P =>
    ForallPT t1 q1 (fun a p => P a (GoLeft p)) /\
    ForallPT t2 q2 (fun a p => P a (GoRight p))
  | Leaf_, Leaf a => fun P => P a GoHere
  | Any_, _ => fun _ => True
  | _, _ => fun _ => False
  end.

(* The correctness criterion of [CoArbitrary] expressed using
   trees. *)
Lemma tree_coarbitrary_seed A :
  forall (t : tree A)
         (q : pretree)
         (f : A -> RandomSeed),
    prefix_of t q ->
    exists s,
      ForallPT t q (fun x p_ => f x = coarbitrary_path (projT1 p_) s).
Proof.
  intros t q.
  generalize dependent t.
  induction q; intros t f Hq.
  - destruct t; try solve [destruct Hq].
    destruct Hq as [Hq1 Hq2].
    destruct (IHq1 t1 f Hq1) as [ s1 Hs1 ].
    destruct (IHq2 t2 f Hq2) as [ s2 Hs2 ].
    destruct (randomSplitAssumption s1 s2) as [ s0 Hs0 ].
    exists s0.
    simpl.
    rewrite Hs0.
    auto.
  - destruct t; destruct Hq.
    exists (f a); simpl; auto.
  - destruct randomSeed_inhabited as [s'].
    exists s'; simpl; auto.
Qed.

(* We now need to transport that lemma to the original
   property using lists. *)

(* The main assumption is that there is a tree which coincides
   with the [CoArbitrary] instance, such that for any value
   [a], the [path] generated by [coarbitrary] leads to
   [a]'s own leaf in the tree. *)
Class TreeCoArbitrary A `{CoArbitrary A} : Type :=
  { tree_coarbitrary : tree A;
    tree_complete :
      forall a, In_tree tree_coarbitrary a (path_coarbitrary a);
  }.

Lemma tree_complete_coyoneda A `{CoArbitrary A}
      (t : (A -> A) -> tree A) :
  (forall a k,
      In_tree (t k) (k a) (path_coarbitrary a)) ->
  forall a,
    In_tree (t id) a (path_coarbitrary a).
Proof.
  intros Ht a.
  apply Ht with (k := id).
Qed.

Lemma prefix_union {A} :
  forall (t : tree A)
         (q1 : pretree)
         (q2 : pretree),
    prefix_of t q1 ->
    prefix_of t q2 ->
    exists (q3 : pretree),
      prefix_of t q3 /\
      forall (P : forall a, tree_path t a -> Prop),
        ForallPT t q3 P -> ForallPT t q1 P /\ ForallPT t q2 P.
Proof.
  fix prefix_union 2.
  intros t q1 q2 Hq1 Hq2.
  destruct q1 as [q1l q1r | | ] eqn:e1.
  - destruct t as [tl tr | | ].
    + destruct q2 as [q2l q2r | | ] eqn:e2.
      * destruct Hq1 as [Hq1l Hq1r].
        destruct Hq2 as [Hq2l Hq2r].
        destruct
          (prefix_union tl q1l q2l Hq1l Hq2l)
          as [q3l Hq3l].
        destruct
          (prefix_union tr q1r q2r Hq1r Hq2r)
          as [q3r Hq3r].
        exists (Split_ q3l q3r).
        split.
        { split; [apply Hq3l | apply Hq3r]. }
        intros P H.
        repeat (split + eauto + apply Hq3l + apply Hq3r + apply H).
      * inversion Hq2.
      * eexists (Split_ q1l q1r).
        split; eauto.
    + inversion Hq1.
    + inversion Hq1.
  - exists Leaf_.
    destruct t; destruct q2;
      try solve [inversion Hq1 | inversion Hq2]; auto.
  - exists q2.
    auto.
Qed.

Lemma path_to_tree {A} :
  forall (t : tree A)
         (x : A)
         (p_ : tree_path t x),
    exists q,
      prefix_of t q /\
      forall (P : forall (a : A), tree_path t a -> Prop),
        ForallPT t q P -> P x p_.
Proof.
  intros t x [p Hp].
  generalize dependent t.
  generalize dependent p.
  fix path_to_tree 1.
  intros [ | [] p ]; [ clear path_to_tree | |];
    intros [t1 t2 | | ] Hp; try destruct Hp.
  - exists Leaf_; simpl; auto.
  - destruct (path_to_tree p t1 Hp) as [q' [Htq' Hq']].
    exists (Split_ q' Any_).
    split.
    { simpl; auto. }
    intros P H.
    apply Hq' with (P := fun a p => P a (GoLeft p)), H.
  - destruct (path_to_tree p t2 Hp) as [q' [Htq' Hq']].
    exists (Split_ Any_ q').
    split.
    { simpl; auto. }
    intros P H.
    apply Hq' with (P := fun a p => P a (GoRight p)), H.
Qed.

Lemma list_to_tree {A} :
  forall (t : tree A)
         (xs : list { x : A & tree_path t x }),
    exists q,
      prefix_of t q /\
      forall (P : forall a, tree_path t a -> Prop),
        ForallPT t q P ->
        Forall (fun x_ => P (projT1 x_) (projT2 x_)) xs.
Proof.
  fix list_to_tree 2.
  intros t [ | [x p] xs ].
  - exists Any_. split; simpl; auto.
  - destruct (path_to_tree t x p) as [qx [Htqx Hqx]].
    destruct (list_to_tree t xs) as [qxs [Htqxs Hqxs]].
    destruct (prefix_union t qx qxs Htqx Htqxs) as [q' [Htq' Hq']].
    exists q'.
    split; auto.
    intros P H.
    constructor.
    + apply Hqx, Hq'. auto.
    + apply Hqxs, Hq'. auto.
Qed.

Lemma tree_coarbitrary_seed' {A} :
  forall (t : tree A)
         (xs : list { x : A & tree_path t x })
         (f : A -> RandomSeed),
  exists s,
    Forall
      (fun x_ =>
         f (projT1 x_) = coarbitrary_path (projT1 (projT2 x_)) s)
      xs.
Proof.
  intros t xs f.
  destruct (list_to_tree t xs) as [q [Htq Hq]].
  apply tree_coarbitrary_seed with (f := f) in Htq.
  destruct Htq as [s' Hs'].
  exists s'.
  apply Hq with
    (P := fun a p => f a = coarbitrary_path (projT1 p) s').
  apply Hs'.
Qed.

Lemma Forall_map {A B} :
  forall xs (f : A -> B) P,
    Forall P (map f xs) -> Forall (fun x => P (f x)) xs.
Proof.
  induction xs; intros f P H; auto.
  inversion H; auto.
Qed.

(* A quick shortcut to avoid the diamond inheritance problem. *)
Class TreeCoArbitraryCorrect A
      {CA : CoArbitrary A}
      `{@CoArbitraryParametric A CA}
      `{@TreeCoArbitrary A CA} : Prop := {}.
Instance TreeCoArbitraryCorrect_default A
         `{CoArbitrary A}
         `{@CoArbitraryParametric A _}
         `{@TreeCoArbitrary A _} :
  TreeCoArbitraryCorrect A := {}.

Lemma tree_coarbitrary_correct {A}
      `{TreeCoArbitraryCorrect A} :
  forall xs f,
    exists s : RandomSeed,
      Forall (fun x => f x = coarbitrary x s) xs.
Proof.
  intros xs f.
  destruct
    (let g x := existT _ x (existT _ (path_coarbitrary x)
                                   (tree_complete x)) in
     tree_coarbitrary_seed' tree_coarbitrary (map g xs) f)
    as [s' Hs'].
  exists s'.
  apply Forall_map in Hs'.
  induction xs; auto.
  inversion Hs'.
  simpl in *.
  constructor; [rewrite coarbitrary_path_comm_nil | ]; auto.
Qed.

End TreeCorrectness.

(* [CoArbitrary] instances can be defined by providing
   an embedding. *)
Module Import EmbeddingCorrectness.

Section Embedding.

Context {A B : Type}.
Context {CA : CoArbitrary A}
        `{@CoArbitraryParametric A CA}
        `{@TreeCoArbitrary A CA}
        `{@CoArbitraryCorrect A CA}.
Variable embed : B -> A.
Variable project : A -> B.
Variable embedding : forall b, project (embed b) = b.

Local Instance EmbedCoArbitrary : CoArbitrary B :=
  { coarbitrary _ _ b := coarbitrary (embed b) }.

Local Instance EmbedCoArbitraryParametric :
  CoArbitraryParametric B := {}.
Proof.
  intros S T ? ? R HR b s t ?.
  simpl.
  apply free_theorem_coarbitrary; auto.
Qed.

Local Instance EmbedTreeCoArbitrary :
  TreeCoArbitrary B :=
  { tree_coarbitrary := map_tree project tree_coarbitrary }.
Proof.
  intro b.
  rewrite <- embedding at 1.
  apply In_tree_map.
  simpl.
  apply tree_complete.
Qed.

(* We deduce correctnes directly from another [CoArbitraryCorrect]
   instance. It's a bit more work but makes it more generally
   applicable.
*)
Local Instance EmbedCoArbitraryCorrect :
  CoArbitraryCorrect B := {}.
Proof.
  intros xs0 f0.
  destruct coarbitrary_correct with
    (xs := map embed xs0) (f := fun a => f0 (project a))
    as [s' Hs'].
  exists s'.
  apply Forall_map in Hs'.
  apply (fun X => Forall_impl _ X Hs').
  intros a Ha.
  rewrite embedding in Ha.
  exact Ha.
Qed.

End Embedding.

End EmbeddingCorrectness.

(**********************************************************)

(* [bool] *)

Instance CoArbitrary_bool : CoArbitrary bool :=
  {| coarbitrary _ _ (b : bool) s :=
       (if b then fst else snd) (split s);
  |}.

Instance CoArbitraryParametric_bool :
  CoArbitraryParametric bool := {}.
Proof.
  intros S T ? ? R H [] s t ?; apply H; auto.
Qed.

Instance TreeCoArbitrary_bool : TreeCoArbitrary bool :=
  { tree_coarbitrary :=
      Split (Leaf true) (Leaf false) }.
Proof.
  intros []; simpl; auto.
Qed.

Instance CoArbitraryCorrect_bool : CoArbitraryCorrect bool := {}.
Proof. apply tree_coarbitrary_correct. Qed.

(* [positive] *)

Definition coarbitrary_positive {S} `{Splittable S} :=
  fix coarb (x : positive) s :=
    let s' := split s in
    match x with
    | xI x' => coarb x' (fst (split (fst s')))
    | xO x' => coarb x' (snd (split (fst s')))
    | xH => snd s'
    end.

Instance CoArbitrary_positive : CoArbitrary positive :=
  {| coarbitrary := @coarbitrary_positive |}.

Instance CoArbitraryParametric_positive :
  CoArbitraryParametric positive := {}.
Proof.
  induction a; intros; try apply IHa; repeat apply H; auto.
Qed.

Instance TreeCoArbitrary_positive : TreeCoArbitrary positive :=
  { tree_coarbitrary :=
      (cofix tree_ca k :=
         Split
           (Split
              (tree_ca (comp k xI))
              (tree_ca (comp k xO)))
           (Leaf (k xH))
      ) (fun x => x) }.
Proof.
  pose (e := path_coarb_app positive); clearbody e.
  apply tree_complete_coyoneda.
  induction a; intro k;
    reflexivity +
    (simpl; rewrite e;
     apply IHa with (k := comp k _)).
Qed.

Instance CoArbitraryCorrect_positive : CoArbitraryCorrect positive :=
  {}.
Proof. apply tree_coarbitrary_correct. Qed.

(* [nat] *)

Instance CoArbitrary_nat : CoArbitrary nat :=
  EmbedCoArbitrary Pos.of_succ_nat.

Instance CoArbitraryParametric_nat : CoArbitraryParametric nat :=
  EmbedCoArbitraryParametric _.

Instance TreeCoArbitrary_nat : TreeCoArbitrary nat :=
  EmbedTreeCoArbitrary _ (comp _ _) SuccNat2Pos.pred_id.

Instance CoArbitraryCorrect_nat : CoArbitraryCorrect nat :=
  EmbedCoArbitraryCorrect _ (comp _ _) SuccNat2Pos.pred_id.

(* [prod] *)

Instance CoArbitrary_prod {A B} `{CoArbitrary A} `{CoArbitrary B} :
  CoArbitrary (A * B) :=
  { coarbitrary _ _ xy s :=
      let '(x, y) := xy in
      coarbitrary y (coarbitrary x s)
  }.

Instance CoArbitraryParametric_prod {A B}
         `{CoArbitraryParametric A}
         `{CoArbitraryParametric B} :
  CoArbitraryParametric (A * B) := {}.
Proof.
  intros S T ? ? R HR [a b] s t ?.
  simpl.
  do 2 (apply free_theorem_coarbitrary; auto).
Qed.

Instance TreeCoArbitrary_prod {A B}
         {CB : CoArbitrary B}
         `{TreeCoArbitrary A}
         `{@CoArbitraryParametric B CB}
         `{@TreeCoArbitrary B CB} :
  TreeCoArbitrary (A * B) :=
  { tree_coarbitrary :=
      bind_tree tree_coarbitrary (fun a =>
      bind_tree tree_coarbitrary (fun b =>
      Leaf (a, b)));
  }.
Proof.
  intros [a0 b0].
  simpl.
  rewrite path_coarb_app.
  apply In_tree_bind with (a := a0).
  { apply tree_complete. }
  { rewrite <- app_nil_r.
    apply In_tree_bind with (a := b0).
    { apply tree_complete. }
    { simpl; auto. } }
  { auto. }
Qed.

Instance CoArbitraryCorrect_prod {A B}
         `{TreeCoArbitraryCorrect A}
         `{TreeCoArbitraryCorrect B} :
  CoArbitraryCorrect (A * B) := {}.
Proof.
  eapply (@tree_coarbitrary_correct); typeclasses eauto.
Qed.

(* This one is surprisingly hard, the definition of
   [CoArbitraryCorrect] using a function [f] is not too
   convenient here. *)
Instance CoArbitraryCorrect_prod' {A B}
         {CA : CoArbitrary A}
         `{@CoArbitraryParametric A CA}
         `{@CoArbitraryCorrect A CA}
         `{CoArbitraryCorrect B} :
  CoArbitraryCorrect (A * B) := {}.
Abort.

(* [list] *)

Instance CoArbitrary_list {A} `{CoArbitrary A} :
  CoArbitrary (list A) :=
  { coarbitrary _ _ :=
      fix coarb xs s :=
        match xs with
        | [] => fst (split s)
        | x :: xs' => coarb xs' (coarbitrary x (snd (split s)))
        end
  }.

Instance CoArbitraryParametric_list {A}
         `{CoArbitraryParametric A} :
  CoArbitraryParametric (list A) := {}.
Proof.
  intros S T ? ? R HR xs.
  induction xs; simpl in *; intros.
  - apply HR; auto.
  - apply IHxs.
    apply free_theorem_coarbitrary; auto.
    apply HR; auto.
Qed.

(* The guardedness condition forces us to shift and duplicate bits. *)
Instance TreeCoArbitrary_list {A} `{TreeCoArbitraryCorrect A} :
  TreeCoArbitrary (list A) :=
  { tree_coarbitrary :=
      Split
        (Leaf [])
        ((cofix tree_ca k :=
           bind_tree tree_coarbitrary (fun x =>
           Split
             (Leaf (k [x]))
             (tree_ca (comp k (cons x))))
         ) (fun x => x))
  }.
Proof.
  intro xs.
  destruct xs as [ | x xs' ]; simpl; auto.
  rewrite path_coarb_app; [ | typeclasses eauto ].
  remember id as k eqn:e.
  replace (x :: xs') with (k (x :: xs')); [ | rewrite e; reflexivity ].
  clear e.
  generalize dependent k.
  generalize dependent x.
  induction xs' as [ | x' xs'' ]; intros x k; simpl.
  - match goal with
    | [ |- In_tree (?t ?k) _ _ ] =>
      replace (t k) with
        (bind_tree tree_coarbitrary (fun x =>
         Split (Leaf (k [x])) (t (comp k (cons x)))))
    end.
    { apply In_tree_bind with (a := x).
      + apply tree_complete.
      + reflexivity. }
    { match goal with
      | [ |- ?u = ?v ] =>
        rewrite (match_tree u);
        rewrite (match_tree v)
      end; reflexivity. }
  - rewrite path_coarb_app; auto.
    pose (pca := @path_coarb_app (list A) _ _); clearbody pca.
    rewrite pca.
    repeat (rewrite <- app_assoc; simpl).
    match goal with
    | [ |- In_tree (?t ?k) _ _ ] =>
      replace (t k) with
        (bind_tree tree_coarbitrary (fun x =>
         Split (Leaf (k [x])) (t (comp k (cons x)))))
    end.
    { apply In_tree_bind with (a := x).
      + apply tree_complete.
      + specialize IHxs'' with (x := x').
        rewrite pca in IHxs''.
        apply IHxs''. }
    { match goal with
      | [ |- ?u = ?v ] =>
        rewrite (match_tree u);
        rewrite (match_tree v)
      end; reflexivity. }
Qed.

Instance CoArbitraryCorrect_list {A}
         `{TreeCoArbitraryCorrect A} :
  CoArbitraryCorrect A := {}.
Proof. apply tree_coarbitrary_correct. Qed.

(*
Local Open Scope positive.
Fixpoint posToPathAux (p : positive) : SplitPath := 
  match p with 
    | xH => []
    | xI p' => posToPathAux p' ++ [Left; Right]
    | xO p' => posToPathAux p' ++ [Left; Left ]
  end.

Section PathLemmas.

Set Implicit Arguments.
Unset Strict Implicit.

Definition posToPath (p : positive) : SplitPath := posToPathAux p ++ [Right].

Fixpoint pathToPosAux (p : SplitPath) (f : positive -> positive) 
: option positive :=
match p with 
  | [Right] => Some (f xH)
  | Left :: Right :: p' => pathToPosAux p' (fun p => xI (f p))
  | Left :: Left  :: p' => pathToPosAux p' (fun p => xO (f p))     
  | _ => None
end.

Definition pathToPos p := pathToPosAux p (fun x => x).

(*
Eval compute in (pathToPos (posToPath 1)).
Eval compute in (pathToPos (posToPath 2)).
Eval compute in (pathToPos (posToPath 3)).
Eval compute in (pathToPos (posToPath 4)).
Eval compute in (pathToPos (posToPath 5)).
Eval compute in (pathToPos (posToPath 6)).
Eval compute in (pathToPos (posToPath 7)).
Eval compute in (pathToPos (posToPath 8)).
Eval compute in (pathToPos (posToPath 9)).
*)

Definition list_ind' (A : Type) (P : list A -> Prop) : 
                    P [] -> (forall (a : A), P [a]) -> 
                    (forall (a b : A) (l : list A), P l -> P (a :: b :: l)) ->
                    forall (l : list A), P l :=
  fun H0 H1 H2 => 
    fix aux (l : list A) : P l := 
      match l with 
        | []  => H0
        | [x] => H1 x
        | a :: b :: l' => H2 a b l' (aux l')
      end.

Lemma aux1 : forall l p f, pathToPosAux (l ++ [Right]) f = Some p ->
               exists f', forall l', pathToPosAux (l ++ l') f =
                                    pathToPosAux l' f' /\ f' xH = p.
induction l using list_ind'; intros.
+ simpl in *; inversion H; subst.
  exists f; intros.
  split; auto.
+ simpl in H; destruct a; inversion H.
+ pose proof IHl p; clear IHl.
  destruct a; destruct b; simpl in *.
  -  pose proof (H0 (fun p0 => xO (f p0))); clear H0.
     apply H1 in H; clear H1.
     assumption.
  -  pose proof (H0 (fun p0 => xI (f p0))); clear H0.
     apply H1 in H; clear H1.
     assumption.
  - inversion H.
  - inversion H.
Qed.

Lemma posPathInj : forall p, pathToPos (posToPath p) = Some p.
induction p; unfold posToPath, pathToPos in *; simpl in *.
- apply aux1 in IHp. 
  inversion IHp as [f' Hyp]; clear IHp.
  rewrite <- app_assoc; simpl.
  pose proof Hyp [Left; Right; Right] as H; clear Hyp.
  inversion H as [H0 H1]; clear H.
  rewrite H0; clear H0.
  simpl; subst; auto.
- apply aux1 in IHp. 
  inversion IHp as [f' Hyp]; clear IHp.
  rewrite <- app_assoc; simpl.
  pose proof Hyp [Left; Left; Right] as H; clear Hyp.
  inversion H as [H0 H1]; clear H.
  rewrite H0; clear H0.
  simpl; subst; auto.
- auto.
Qed.

Fixpoint lengthSplit {A : Type} (l l' : list A) : option (list A * list A) :=
  match l, l' with
    | [], x => Some ([], x)
    | _::xs, y::ys => 
      option_map (fun (p : list A * list A) => 
                    let (l1,l2) := p in (y::l1, l2)) (lengthSplit xs ys)
    | _, _ => None
  end.

Lemma lengthSplit1 : forall {A : Type} (l l' : list A), 
                       le (length l) (length l') -> 
                       exists p, lengthSplit l l' = Some p.
induction l as [ | x xs IHxs].
+ intros; exists ([], l'); auto.
+ intros l' LE; destruct l' as [ | b bs] eqn:LEq.
  - inversion LE.
  - pose proof IHxs bs as IH; clear IHxs.
    assert (LE' : le (length xs) (length bs))
           by (simpl in *; omega). (* Overkill? :) *)
    clear LE.
    apply IH in LE'; clear IH.
    inversion LE' as [pair Split]; clear LE'.
    destruct pair as [l1 l2] eqn:Pair.
    simpl.
    rewrite Split.
    exists (b :: l1, l2).
    simpl.
    auto.
Qed.

Lemma lengthSplit2 : forall {A : Type} (l l' l1 l2 : list A), 
                       lengthSplit l l' = Some (l1, l2) -> l1 ++ l2 = l'.
induction l.
+ intros l' l1 l2 Hyp; simpl in Hyp; inversion_clear Hyp; auto.
+ intros l' l1 l2 Hyp. 
  simpl in Hyp.
  destruct l' as [ | y ys] eqn:L'.
  - inversion Hyp.
  - destruct l1 eqn:L1.
    * destruct (lengthSplit l ys); simpl in *.
      + destruct p; congruence.
      + congruence.
    * pose proof IHl ys l0 l2; clear IHl.
      destruct (lengthSplit l ys) eqn:LenSplit; simpl in *.
      + inversion Hyp. destruct p. inversion H1. subst.
        rewrite H; auto.
      + inversion Hyp.
Qed.      

Lemma lengthSplit3 : forall {A : Type} (l l' l1 l2 : list A), 
                       lengthSplit l l' = Some (l1, l2) -> length l1 = length l.
induction l as [ | x xs IHxs].
+ intros; simpl in H; inversion H; auto.
+ intros l' l1 l2 Split.
  simpl in Split.
  destruct l'.
  - inversion Split.
  - destruct l1.
    * destruct (lengthSplit xs l').
      + simpl in *. destruct p. inversion Split.
      + simpl in *. inversion Split.
    * simpl in *. 
      destruct (lengthSplit xs l') eqn:LenSplit.
      + simpl in *. destruct p. inversion Split; subst; clear Split.
        pose proof (IHxs l' l1 l2 LenSplit) as Hyp; clear IHxs.
        auto.
      + simpl in *. inversion Split.
Qed.        

Lemma lengthPathEven : forall p, exists n, length (posToPathAux p) = (2 * n)%nat.
induction p.
+ inversion IHp as [n Hyp]; clear IHp.
  simpl.
  exists (S n).
  rewrite app_length. 
  rewrite Hyp.
  simpl.
  omega.
+ inversion IHp as [n Hyp]; clear IHp.
  simpl.
  exists (S n).
  rewrite app_length. 
  rewrite Hyp.
  simpl.
  omega.
+ exists (O).
  simpl.
  auto.
Qed.

Lemma evenPathAux : forall l l' l'' lApp f n p, length l = (2 * n)%nat -> 
                      pathToPosAux (l ++ l' ++ l'') f = Some p ->
                      exists f', pathToPosAux (l ++ l') f = pathToPosAux l' f'
                                 /\ pathToPosAux (l ++ l' ++ lApp) f = 
                                    pathToPosAux (l' ++ lApp) f'.
induction l using list_ind'.
+ intros. exists f. auto.
+ intros. simpl in *. omega.
+ intros l' l'' lApp f n p Len Valid.
  destruct n.
  - simpl in Len. congruence.
  - simpl in Len; assert (length l = (2 * n)%nat) by omega.
    destruct a eqn:A; destruct b eqn:B; simpl in *.
    * unfold pathToPos in Valid. simpl in Valid.
      pose proof (IHl l' l'' lApp (fun p => xO (f p)) n p H Valid) as Hyp; clear IHl H.
      inversion Hyp as [f' HF]; clear Hyp.
      exists f'.
      auto.
    * unfold pathToPos in Valid. simpl in Valid.
      pose proof (IHl l' l'' lApp (fun p => xI (f p)) n p H Valid) as Hyp; clear IHl H.
      inversion Hyp as [f' HF]; clear Hyp.
      exists f'.
      auto.
    * inversion Valid.
    * inversion Valid.
Qed.

Lemma pathBeginsLeft : forall l1 l2 f x, l1 <> [] -> l2 <> [] -> 
                                     pathToPosAux (l1 ++ l2) f = Some x ->
                                     head l1 = Some Left.
destruct l1.
+ intros. exfalso; apply H; auto.
+ intros. 
  destruct s.
  - auto.
  - simpl in H1. 
    destruct (l1 ++ l2) eqn:Contra.
    * destruct l1; destruct l2; try solve [unfold not; exfalso; auto]; 
      simpl in *; congruence.
    * congruence.
Qed.

Lemma listAppNeq : forall (A : Type) (l1 l2 l3 l4 : list A), 
                     (forall (x y : A), {x = y} + {x <> y}) ->
                     length l1 = length l2 -> 
                     l1 <> l2 ->
                     l1 ++ l3 <> l2 ++ l4.
induction l1.
+ intros.
  destruct l2.
  - unfold not in H0. exfalso; apply H0; auto.
  - simpl in H; inversion H.
+ intros l2 l3 l4 EqDec Len Neq.
  destruct l2 as [ | b l2 ].
  - simpl in Len. congruence.
  - destruct (EqDec a b).
    * subst. simpl in Len. 
      inversion Len as [ Len']; clear Len.
      simpl.
      pose proof (IHl1 l2 l3 l4 EqDec Len') as Contra; clear IHl1.
      assert (l1 <> l2) by (unfold not; intros; congruence).
      apply Contra in H.
      unfold not in *.
      intros.
      apply H.
      inversion H0.
      auto.
    * unfold not; intros.
      inversion H.
      congruence.
Qed.

Lemma PosToPathPrefixFreeAux : forall (x y : positive), (x <> y) -> 
                                 le (length (posToPathAux y)) (length(posToPathAux x)) ->
                              PrefixFree [posToPath x;
                                          posToPath y].
intros x y H Leq.
apply FreeCons; [ apply FreeCons ; [ constructor | intros p Contra; inversion Contra] | ].
intros.
inversion H0; subst; clear H0; [ | inversion H2].
unfold posToPath in *; simpl in *; repeat rewrite <- app_assoc in *.

pose proof (lengthSplit1 Leq) as Hyp.
inversion Hyp as [pair Split]; clear Hyp.
destruct pair as [l0 l1].
pose proof (lengthSplit2 Split) as AppHyp.
pose proof (lengthSplit3 Split) as LenHyp.
pose proof (lengthPathEven y) as Hyp; inversion Hyp as [n LenN]; subst; clear Hyp.
assert (XHyp : pathToPosAux (l0 ++ l1 ++ [Right]) (fun x => x) = Some x); 
  [ rewrite app_assoc; rewrite AppHyp; apply posPathInj | ].

rewrite <- LenHyp in LenN.

pose proof (evenPathAux [Right] LenN XHyp) as Even.
inversion Even as [f' HF]; clear Even.
inversion HF as [HF1 HF2]; clear HF.
rewrite <- AppHyp in H1.
rewrite <- app_assoc in H1.

destruct (list_eq_dec Direction_eq_dec (posToPathAux y) l0).
- subst. apply app_inv_head in H1.
  destruct l1.
  *  simpl in AppHyp; rewrite app_nil_r in AppHyp.
      assert (posToPathAux y ++ [Right] = posToPathAux x ++ [Right]) 
        by (rewrite AppHyp; auto).
      assert (posToPath y = posToPath x) by (unfold posToPath; auto).
      assert (pathToPos (posToPath y) = pathToPos (posToPath x)) by (rewrite H2; auto).
      repeat rewrite posPathInj in H3.
      congruence.
  * assert (Contra : hd_error (s :: l1) = Some Left).
    eapply pathBeginsLeft.
    + unfold not; intros; congruence.
    + instantiate (1 := [Right]); unfold not; intros; congruence.
    + instantiate (1:= x); instantiate (1:=f').
      rewrite <- HF2.
      apply XHyp.
    simpl in Contra. inversion Contra; subst. simpl in H1. congruence.
- eapply listAppNeq.
  * apply Direction_eq_dec.
  * instantiate (1 := l0). instantiate (1 := posToPathAux y). eauto.
  * eassumption.
  * eapply H1.
Qed.

Lemma prefixFreeCommutative : forall l1 l2, PrefixFree [l1;l2] -> PrefixFree [l2;l1].
intros.
inversion H.
apply FreeCons.
+ apply FreeCons.
  - constructor.
  - intros. inversion H4.
+ intros.
  subst.
  eapply H3.
  - instantiate (1 := l2); left; auto.
  - inversion H4.
    * subst. inversion H4. subst. instantiate (1:= p1); instantiate (1 := p2).
      auto.
    * inversion H0.
  - inversion H0.
Qed.

Lemma PosToPathPrefixFree : forall (x y : positive), (x <> y) -> 
                              PrefixFree [posToPath x;
                                          posToPath y].
intros. 
destruct (Compare_dec.le_ge_dec (length (posToPathAux y)) 
                                (length (posToPathAux x))).
+ apply (PosToPathPrefixFreeAux H l).
+ apply prefixFreeCommutative.
  apply (@PosToPathPrefixFreeAux y x).
  - unfold not in *; intros; exfalso; auto.
  - auto.
Qed.

Function rangeNat (p : nat) : list nat :=
  match p with 
    | O => []
    | S n' => p :: (rangeNat n')
  end.

Definition rangePos (p : positive) : list positive := 
  map Pos.of_nat (rangeNat (Pos.to_nat p)).

Lemma ltInRange : forall m n, le n m -> n <> O -> In n (rangeNat m).
  induction m; intros.
  + inversion H. simpl. auto.
  + simpl. inversion H.
    - left; auto.
    - right; subst. apply IHm; auto.
Qed.

Lemma posLtInRange : forall max pos, Pos.le pos max -> In pos (rangePos max).
  intros.
  apply in_map_iff.
  exists (Pos.to_nat pos).
  split.
  - apply Pos2Nat.id.
  - apply ltInRange.
    + apply Pos2Nat.inj_le; auto.
    + pose proof (Pos2Nat.is_succ pos) as Contra; inversion_clear Contra; congruence.
Qed.

Lemma rangeNatLt : forall n m, In m (rangeNat n) -> lt m (S n) /\ m <> O.
  induction n; intros.
  + simpl in H. inversion H. 
  + inversion H.
    - split. 
      * subst. unfold lt. apply le_n.
      * congruence.
    - apply IHn in H0; inversion H0; clear H0; split.
      * unfold lt in *.
        apply le_S.
        auto.
      * auto.
Qed.    

Lemma rangePosPrefixFree : forall p, PrefixFree (map posToPath (rangePos p)).
  intros.
  unfold rangePos.
  induction (Pos.to_nat p) as [ | n IHn].
  + constructor.
  + simpl. apply FreeCons; auto.
    intros p' InP' p1 p2 App.
    apply in_map_iff in InP'.
    clear IHn.
    inversion InP' as [x xHyp]; clear InP'.
    inversion xHyp as [Pos2Path InX]; clear xHyp.
    subst.
    apply in_map_iff in InX.
    inversion InX as [y yHyp]; clear InX.
    inversion yHyp as [Pos2PathY InY]; clear yHyp.
    apply rangeNatLt in InY.
    inversion InY as [LtYSn YNotO]; clear InY.
    remember (match n with | O => 1 | S _ => Pos.succ (Pos.of_nat n) end) as m.
    assert (Neq : x <> m).
      unfold not; intros; subst.
      destruct y.
      - congruence.
      - destruct n.
        * omega.
        * assert (Pos.to_nat (Pos.of_nat (S y)) = Pos.to_nat (Pos.succ (Pos.of_nat (S n))))
            by (rewrite H; auto).
          rewrite Pos2Nat.inj_succ in H0.
          
          rewrite Nat2Pos.id in H0.
          rewrite Nat2Pos.id in H0.
          + subst; omega.
          + congruence.
          + congruence.
    pose proof (@PosToPathPrefixFree x m) as Hyp.
    apply Hyp in Neq; clear Hyp.
    inversion Neq.
    eapply H2.
    + left; auto.
    + eauto.
Qed.    

Definition posFunToPathFun (f : positive -> RandomSeed) (p : SplitPath) 
: RandomSeed :=
  match pathToPos p with 
    | Some a => f a
    | None   => newRandomSeed
  end.

Theorem coarbComplete' : forall (max : positive) (f : positive -> RandomSeed) ,
                          exists seed, forall p, p <= max -> 
                            varySeed (posToPath p) seed = f p.
intros.
pose proof (SplitPathCompleteness (map posToPath (rangePos max)) 
                                (posFunToPathFun f) (rangePosPrefixFree max)).
inversion H; clear H.
exists x.
intros.
pose proof H0 (posToPath p).
rewrite H1.
+ unfold posFunToPathFun.
  rewrite posPathInj.
  reflexivity.
+ apply in_map_iff.
  exists p.
  split; auto.
  apply posLtInRange.
  auto.
Qed.

Definition funToPosFun {A : Type} `{_ : CoArbitraryCorrect A}
           (f : A -> RandomSeed) (p : positive)
  : RandomSeed :=
  match coarbReverse p with 
    | Some a => f a
    | None   => newRandomSeed
  end.

Definition coarbLe {A : Type} `{_ : CoArbitrary A} (x y : A) : Prop :=
  Pos.le (coarbitrary x) (coarbitrary y).

Lemma coarbLePreservesLe : forall {A : Type} `{_ : CoArbitrary A} (x y : A),
  coarbLe x y -> Pos.le (coarbitrary x) (coarbitrary y).
by [].
Qed.

Theorem coarbComplete :
  forall {A : Type} `{CoArbitraryCorrect A} (max : A)
         (f : A -> RandomSeed),
  exists seed, forall a,
      coarbLe a max ->
      varySeed (posToPath (coarbitrary a)) seed = f a.
intros.
pose proof (coarbComplete' (coarbitrary max) (funToPosFun f)) as Hyp.
inversion Hyp as [seed HSeed]; clear Hyp.
exists seed.
intros a HLe.
pose proof (HSeed (coarbitrary a)) as HCo; clear HSeed.
apply coarbLePreservesLe in HLe.
apply HCo in HLe; clear HCo.
rewrite HLe; clear HLe.
unfold funToPosFun.
rewrite coarbCorrect.
reflexivity.
Qed.

End PathLemmas.

Instance genFun {A B : Type} `{_ : CoArbitrary A} `{_ : Gen B} : Gen (A -> B) :=
  {|
    arbitrary := 
      reallyUnsafePromote (fun a => variant (posToPath (coarbitrary a)) arbitrary);
  |}.

Instance shrinkFunNil {A B : Type} : Shrink (A -> B) :=
  {| shrink x := nil |}.

Section arbFun_completeness.

Variables A B : Type.
Hypothesis choice : FunctionalChoice_on A RandomSeed.

(* begin arbFunCorrect *)
Theorem arbFunComplete `{CoArbitraryCorrect A, Arbitrary B} (max:A) (f:A-> B) (s:nat) :
  s = Pos.to_nat (coarbitrary max) -> (semGenSize arbitrary s <--> setT) ->
  exists seed, forall a, coarbLe a max -> run arbitrary s seed a = f a.
(* end arbFunCorrect *)
Proof.
move=> eqsize semB.
have/choice [fseed fseedP]: forall a, exists seed : RandomSeed, run arbitrary s seed = f a.
  by move => a; case: (semB (f a))=> _ /(_ I) [seed ?]; exists seed.
case: (coarbComplete max fseed) => seed Hseed.
pose proof (randomSplitAssumption seed seed) as Hyp.
move : Hyp => [seed' Hsplit].
exists seed' => a le_a; rewrite -fseedP -Hseed //=.
apply (@promoteVariant A B a (fun a => posToPath (coarbitrary a)) arbitrary 
                       s seed' seed seed Hsplit).
Qed.

End arbFun_completeness.

Require Import Program.
Require Import FunInd.

Section CoArbitraryList.

Fixpoint merge_pos (a : positive) (b : positive) : positive :=
  match a with
  | xH => xO b
  | xO ta => xI (xO (merge_pos ta b))
  | xI ta => xI (xI (merge_pos ta b))
  end.

Function split_pos (c : positive) : option (positive * positive) :=
  (* let append f ab :=
      match ab with
      | Some (a, b) => Some (f a, b)
      | None => None
      end
  in
  *)
  match c with
  | xO b => Some (xH, b)
  | xI (xO tc) =>
    match split_pos tc with
    | Some (a, b) => Some (xO a, b)
    | None => None
    end
    (* append xO (split_pos tc) *)
  | xI (xI tc) =>
    match split_pos tc with
    | Some (a, b) => Some (xI a, b)
    | None => None
    end
    (* append xI (split_pos tc) *)
  | _ => None
  end.

Ltac split_induction c :=
  functional induction (split_pos c); intros a0 b0 H;
  try (inversion H; auto).

Lemma split_merge : forall (a b c : positive),
    merge_pos a b = c <-> Some (a, b) = split_pos c.
Proof.
  intros a b c.
  split.
  - generalize dependent c.
    generalize dependent b.
    induction a; intros b c; intro H; rewrite <- H; simpl;
      [ erewrite <- IHa | erewrite <- IHa | ]; reflexivity.
  - generalize dependent b.
    generalize dependent a.
    split_induction c;
      try (simpl; erewrite IHo; auto).
Qed.

Lemma size_nat_pos : forall (c : positive),
    (0 < Pos.size_nat c)%nat.
Proof.
  destruct c; apply Lt.le_lt_n_Sm; apply PeanoNat.Nat.le_0_l.
Qed.

Lemma split_decr_1 : forall (a b c : positive),
    Some (a, b) = split_pos c ->
    (Pos.size_nat a < Pos.size_nat c)%nat.
Proof.
  intros a b c.
  generalize dependent b.
  generalize dependent a.
  split_induction c;
    simpl; simpl; apply Lt.lt_n_S;
      [ apply size_nat_pos | | ];
      destruct a; symmetry in e0; apply IHo in e0;
      apply (PeanoNat.Nat.lt_trans _ _ _ e0); auto.
Qed.

Lemma split_decr_2 : forall (a b c : positive),
    Some (a, b) = split_pos c ->
    (Pos.size_nat b < Pos.size_nat c)%nat.
Proof.
  intros a b c.
  generalize dependent b.
  generalize dependent a.
  split_induction c;
    try (symmetry in e0; apply IHo in e0;
         apply (PeanoNat.Nat.lt_trans _ _ _ e0);
         intuition).
Qed.

Definition semCogen (A : Type)
           (coa : A -> positive)
           (coaR : positive -> option A)
  := forall (a : A) (c : positive),
    coa a = c <-> Some a = coaR c.

Definition pairCoa (A B : Type)
           (coA : A -> positive)
           (coB : B -> positive)
  : A * B -> positive :=
  fun '(a, b) => merge_pos (coA a) (coB b).

Definition pairCoaR (A B : Type)
           (coAR : positive -> option A)
           (coBR : positive -> option B)
  : positive -> option (A * B) :=
  fun c =>
    match split_pos c with
    | None => None
    | Some (a', b') =>
      match coAR a', coBR b' with
      | Some a, Some b => Some (a, b)
      | _, _ => None
      end
    end.

Lemma semCogen_pair :
  forall (A B : Type)
         (coA : A -> positive)
         (coAR : positive -> option A)
         (coB : B -> positive)
         (coBR : positive -> option B),
    semCogen coA coAR ->
    semCogen coB coBR ->
    semCogen (pairCoa coA coB) (pairCoaR coAR coBR).
Proof.
  intros A B coA coAR coB coBR HA HB [a b] c.
  unfold pairCoaR.
  remember (split_pos c) as ab'.
  eapply iff_trans.
  apply split_merge.
  rewrite <- Heqab'.
  destruct ab' as [[a' b']| ]; split; intro H;
    try (discriminate H).
  - injection H as H1 H2.
    apply HA in H1. rewrite <- H1.
    apply HB in H2. rewrite <- H2.
    reflexivity.
  - remember (coAR a') as a0 eqn:Ha0.
    remember (coBR b') as b0 eqn:Hb0.
    destruct a0, b0; try (discriminate H).
    apply HA in Ha0.
    apply HB in Hb0.
    subst.
    inversion H.
    reflexivity.
Qed.

Definition slt (d c : positive) : Prop :=
  (Pos.size_nat d < Pos.size_nat c)%nat.

(* Explicit decreasingness. *)
Program Definition pairCoaR' (A B : Type)
           (coAR : positive -> option A)
           (c : positive)
           (coBR : forall (d : positive), slt d c -> option B)
  : option (A * B) :=
  match split_pos c with
  | None => None
  | Some (a', b') =>
    match coAR a', coBR b' _ with
    | Some a, Some b => Some (a, b)
    | _, _ => None
    end
  end.

Next Obligation.
  eapply split_decr_2.
  apply Heq_anonymous.
Qed.

Fixpoint coarbitrary_list
         (A : Type) (CA : CoArbitrary A) (xs : list A) : positive :=
  match xs with
  | nil => xH
  | x :: xs =>
    xI (pairCoa coarbitrary (coarbitrary_list CA) (x, xs))
  end.

Program Fixpoint coarbReverse_list
         (A : Type) `{CA : CoArbitraryCorrect A} (c : positive)
         {measure (Pos.size_nat c)} :
  option (list A) :=
  match c with
  | xH => Some nil
  | xI c0 =>
    let n := @pairCoaR'
               _ _
               coarbReverse
               c0
               (fun d p => coarbReverse_list d)
    in
    match n with
    | None => None
    | Some (x, xs) => Some (x :: xs)
    end
  | xO _ => None
  end.

Next Obligation.
  eapply PeanoNat.Nat.lt_trans.
  apply p.
  auto.
Qed.

Global Instance coArbList
         (A : Type) `{CoArbitrary A} : CoArbitrary (list A) :=
  {|
    coarbitrary := coarbitrary_list _;
  |}.

Global Instance coArbListCorrect A `{CoArbitraryCorrect A}
  : CoArbitraryCorrect (list A) :=
  {
    coarbReverse p := coarbReverse_list p;
  }.
Proof.
Admitted.

End CoArbitraryList.
*)

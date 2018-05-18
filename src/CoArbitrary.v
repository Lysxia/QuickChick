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

(* The main motivation for [CoArbitrary]: to generate functions. *)
Instance Gen_fun {A B : Type}
         `{CoArbitrary A} `{Gen B} : Gen (A -> B) :=
  {| arbitrary := GenLow.reallyUnsafePromote
       (fun a => GenLow.vary (coarbitrary a) arbitrary);
  |}.

Instance ShrinkNil_fun {A : Type} {F : A -> Type} :
  Shrink (forall a, F a) :=
  {| shrink x := nil |}.

(* Interestingly, this seems to work with dependent functions. *)
(* TODO: is this safe and does it entirely supersed Gen_fun?
   Type inference issues. *)
Instance Gen_forall {A : Type} {F : A -> Type}
       `{CoArbitrary A} `{forall a, Gen (F a)} :
  Gen (forall a, F a) :=
  {| arbitrary :=
      GenLow.reallyUnsafePromote'
        (fun a => GenLow.vary (coarbitrary a) arbitrary);
  |}.

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


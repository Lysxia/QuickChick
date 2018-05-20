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

Definition dir {A} d (f g : A) : A :=
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
| Leaf : A -> tree A
| Unguard : tree' A -> tree A

(* Subtype of "guarded trees". *)
with tree' (A : Type) : Type :=
| Empty' : tree' A
| Fork' : (SplitDirection -> tree A) -> tree' A.

Arguments Leaf {A} _.
Arguments Unguard {A} _.
Arguments Empty' {A}.
Arguments Fork' {A} _.

Definition Empty {A : Type} : tree A := Unguard Empty'.

Definition Split' {A : Type} (t1 t2 : tree A) : tree' A :=
  Fork' (fun d => dir d t1 t2).

Definition Split {A : Type} (t1 t2 : tree A) : tree A :=
  Unguard (Split' t1 t2).

Definition bind_tree {A B}
           (t : tree A) (k : A -> tree B) : tree B :=
  let cofix sub t :=
    match t with
    | Leaf a => k a
    | Unguard t' => Unguard
      match t' with
      | Empty' => Empty'
      | Fork' s => Fork' (fun d => sub (s d))
      end
    end in
  sub t.

Definition bind_tree_guarded {A B}
           (t : tree A) (k : A -> tree' B) : tree B :=
  bind_tree t (fun a => Unguard (k a)).

Definition map_tree {A B} (f : A -> B) (t : tree A) :=
  bind_tree t (fun a => Leaf (f a)).

(* A path [p] points to a value [a] in a tree [t]. *)
Fixpoint In_tree {A}
         (a : A) (t : tree A) (p : path) : Prop :=
  match p, t return Prop with
  | [], Leaf a' => a' = a
  | d :: p', Unguard (Fork' s) =>
    In_tree a (s d) p'
  | _, _ => False
  end.

Lemma In_tree_bind {A B}
      (t : tree A) (k : A -> tree B)
      (a : A) (pa : path) (b : B) (pb : path) :
  In_tree a t pa -> In_tree b (k a) pb ->
  In_tree b (bind_tree t k) (pa ++ pb).
Proof.
  generalize dependent t.
  induction pa as [ | d pa' ]; intros [ | [ | s ] ] Ht Hk;
    try destruct Ht;
    simpl in *.
  - destruct pb; apply Hk.
  - apply IHpa'; auto.
Qed.

Lemma In_tree_map {A B}
      (f : A -> B) (t : tree A) (a : A) (p : path) :
  In_tree a t p -> In_tree (f a) (map_tree f t) p.
Proof.
  intros.
  rewrite <- app_nil_r.
  eapply In_tree_bind; [ eauto | constructor ].
Qed.

(* A path to [a] in tree [t], with constructors
   [Left], [Right], [Here]. *)
Definition tree_path {A} (a : A) (t : tree A) : Type :=
  sigT (In_tree a t).

Definition GoDir {A} {a : A} {s}
           (d : SplitDirection) (p_ : tree_path a (s d)) :
  tree_path a (Unguard (Fork' s)) :=
  existT _ (d :: projT1 p_) (projT2 p_).

Definition GoLeft {A} {a : A} {t1 t2} :
  tree_path a t1 -> tree_path a (Split t1 t2) :=
  GoDir Left.

Definition GoRight {A} {a : A} {t1 t2} :
  tree_path a t2 -> tree_path a (Split t1 t2) :=
  GoDir Right.

Definition GoHere {A} {a : A} : tree_path a (Leaf a) :=
  existT _ [] eq_refl.

(* Finite trees, meant to represent finite approximations of
   infinite trees. *)
Inductive pretree : Type :=
| Any_ : pretree
| Leaf_ : pretree
| Fork_ : (SplitDirection -> pretree) -> pretree.

(* This relation can be seen as a form of unifiability. *)
Fixpoint prefix_of {A} (t : tree A) (q : pretree) : Prop :=
  match q, t with
  | Any_, _ => True
  | Leaf_, Leaf _ => True
  | Fork_ r, Unguard (Fork' s) =>
    forall d, prefix_of (s d) (r d)
  | _, _ => False
  end.

(* Universal quantification over values of a tree [t]
   covered by the prefix [q]. *)
Fixpoint ForallPT {A} (t : tree A) (q : pretree) :
  (forall a, tree_path a t -> Prop) -> Prop :=
  match q, t return (forall a, tree_path a t -> _) -> _ with
  | Any_, _ => fun _ => True
  | Leaf_, Leaf a => fun P => P a GoHere
  | Fork_ r, Unguard (Fork' s) => fun P =>
    forall d,
      ForallPT (s d) (r d) (fun a p => P a (GoDir d p))
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
  intros t q f.
  generalize dependent t.
  induction q as [ | | r Hr ]; intros t Hq.
  - destruct randomSeed_inhabited as [s'].
    exists s'; simpl; auto.
  - destruct t; destruct Hq.
    exists (f a); simpl; auto.
  - destruct t as [ | [ | s ] ]; try contradiction Hq.
    pose (Hs := fun d => Hr d (s d) (Hq d)); clearbody Hs.
    destruct (Hs Left) as [ s1 Hs1 ].
    destruct (Hs Right) as [ s2 Hs2 ].
    destruct (randomSplitAssumption s1 s2) as [ s0 Hs0 ].
    exists s0.
    simpl.
    rewrite Hs0.
    intros []; auto.
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
      forall a, In_tree a tree_coarbitrary (path_coarbitrary a);
  }.

Lemma tree_complete_coyoneda A `{CoArbitrary A}
      (t : (A -> A) -> tree A) :
  (forall a k,
      In_tree (k a) (t k) (path_coarbitrary a)) ->
  forall a,
    In_tree a (t id) (path_coarbitrary a).
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
      forall (P : forall a, tree_path a t -> Prop),
        ForallPT t q3 P -> ForallPT t q1 P /\ ForallPT t q2 P.
Proof.
  fix prefix_union 2.
  intros t q1 q2 Hq1 Hq2.
  destruct t as [ | [ | s ] ];
    (destruct q1 as [ | | r1 ] eqn:e1;
     [ exists q2; clear prefix_union; auto | | ]);
    try contradiction Hq1;
    (destruct q2 as [ | | r2 ] eqn:e2;
     [ exists q1; clear prefix_union; rewrite e1; auto | | ]);
    try contradiction Hq2.
  - exists Leaf_; clear prefix_union; auto.
  - simpl in *.
    pose (H3 :=
      fun d => prefix_union (s d) (r1 d) (r2 d) (Hq1 d) (Hq2 d));
      clearbody H3.
    destruct (H3 Left) as [q3l [ Hq3l Hq3l' ]].
    destruct (H3 Right) as [q3r [ Hq3r Hq3r' ]].
    exists (Fork_ (fun d => dir d q3l q3r)).
    split.
    { intros []; [apply Hq3l | apply Hq3r]. }
    intros P H.
    split; (intros []; [apply Hq3l' | apply Hq3r']); apply H.
Qed.

Lemma path_to_tree {A} :
  forall (t : tree A)
         (x : A)
         (p_ : tree_path x t),
    exists q,
      prefix_of t q /\
      forall (P : forall (a : A), tree_path a t -> Prop),
        ForallPT t q P -> P x p_.
Proof.
  intros t x [p Hp].
  generalize dependent t.
  induction p as [ | d p' IHp' ]; intros t Hp;
    destruct t as [ | [ | s ]]; try destruct Hp.
  - exists Leaf_; split; simpl; auto.
  - simpl in *.
    destruct (IHp' _ Hp) as [ q' [ Hq' Hq'' ] ].
    exists (Fork_ (fun d' => dir d' (dir d q' Any_) (dir d Any_ q'))).
    split.
    { destruct d; intros []; simpl; auto. }
    intros P H.
    apply Hq'' with (P := fun a p => P a (GoDir d p)).
    destruct d; apply H.
Qed.

Lemma list_to_tree {A} :
  forall (t : tree A)
         (xs : list { x : A & tree_path x t }),
    exists q,
      prefix_of t q /\
      forall (P : forall a, tree_path a t -> Prop),
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
         (xs : list { x : A & tree_path x t })
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
  intros []; do 2 constructor.
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
  induction a; intro k; simpl;
    [ | | auto ];
    rewrite e;
    apply IHa with (k := comp k _).
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
      Unguard
        ((cofix tree_ca k :=
            Split'
              (Leaf (k []))
              (bind_tree_guarded tree_coarbitrary (fun x =>
                 tree_ca (comp k (cons x))))
         ) (fun x => x))
  }.
Proof.
  intro xs.
  remember id as k eqn:e.
  cut (xs = k xs);
    [ intro Hkxs; rewrite Hkxs at 1; clear Hkxs
    | rewrite e; reflexivity ].
  clear e.
  generalize dependent k.
  induction xs as [ | x xs' ]; intros k.
  - simpl; auto.
  - simpl.
    rewrite path_coarb_app; [ | typeclasses eauto ].
    pose (pca := @path_coarb_app (list A) _ _); clearbody pca.
    rewrite pca.
    rewrite <- app_assoc.
    simpl.
    eapply In_tree_bind.
    + apply tree_complete.
    + apply IHxs' with (k := comp k (cons x)).
Qed.

Instance CoArbitraryCorrect_list {A}
         `{TreeCoArbitraryCorrect A} :
  CoArbitraryCorrect A := {}.
Proof. apply tree_coarbitrary_correct. Qed.


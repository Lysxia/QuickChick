Require Import PArith List ChoiceFacts Omega.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool.

Require Import Classes RandomQC GenLow Sets.
Import GenLow.

Import ListNotations.

Unset Printing Implicit Defensive.

(* LL: TODO: Add proof obligation that the result paths be prefix free? *)
Class CoArbitrary (A : Type) : Type :=
  {
    coarbitrary : A -> positive;
  }.

Class CoArbitraryCorrect (A : Type) `{CoArbitrary A} : Type :=
  {
    coarbReverse : positive -> option A;
    coarbCorrect : forall a, coarbReverse (coarbitrary a) = Some a
  }.

Instance coArbPos : CoArbitrary positive := 
  {|
    coarbitrary x := x;
  |}.

Instance coArbPosCorrect : CoArbitraryCorrect positive :=
  {
    coarbReverse x := Some x
  }.
Proof. auto. Qed.

Instance coArbNat : CoArbitrary nat :=
  {|
    coarbitrary x := Pos.of_succ_nat x;
  |}.

Instance coArbNatCorrect : CoArbitraryCorrect nat :=
  {
    coarbReverse p := Some (Coq.Init.Peano.pred (Pos.to_nat p))
  }.
Proof.
  intros; simpl. f_equal.
  apply SuccNat2Pos.pred_id.
Qed.

Instance coArbBool : CoArbitrary bool :=
  {|
    coarbitrary x := if x then 1%positive else 2%positive;
  |}.

Instance coArbBoolCorrect : CoArbitraryCorrect bool :=
  {
    coarbReverse x :=
      match x with
      | 2%positive => Some false
      | 1%positive => Some true
      | _ => None
      end
  }.
Proof. intros []; auto. Qed.

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

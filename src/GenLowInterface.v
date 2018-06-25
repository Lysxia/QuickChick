Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import ZArith List.
From mathcomp Require Import ssrbool ssrfun ssrnat.

From QuickChick Require Import
     Sets Splittable SplittableTheory RoseTrees.

Require Export ExtLib.Structures.Monads.
Import MonadNotation.
Open Scope monad_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition isNone {T : Type} (u : option T) :=
  match u with
    | Some _ => false
    | None => true
  end.

(* We hide the implementation of generators behind this interface. The
   rest of the framework and user code are agnostic to the internal
   representation of generators. The proof organization/abstraction
   tries to follow this code organization/abstraction. We need to
   expose quite a bit on the proof side for this to work though. *)
Module Type GenLowInterface.
  (** * Type of generators *)

  Parameter G : Type -> Type.

  (** * Primitive generator combinators *)

  Parameter returnGen : forall {A : Type}, A -> G A.
  (* TODO: Add dependent combinator *)
  Parameter bindGen : forall {A B : Type},
      G A -> (A -> G B) -> G B.
  Parameter bindGenOpt : forall {A B : Type},
      G (option A) -> (A -> G (option B)) -> G (option B).
  Parameter run  : forall {seed} `{Splittable seed} {A : Type},
      G A -> nat -> seed -> A.
  Parameter fmap : forall {A B : Type}, (A -> B) -> G A -> G B.
  Parameter sized : forall {A: Type}, (nat -> G A) -> G A.
  Parameter resize : forall {A: Type}, nat -> G A -> G A.
  Parameter promote : forall {A : Type}, Rose (G A) -> G (Rose A).
  Parameter suchThatMaybe : forall {A : Type},
      G A -> (A -> bool) -> G (option A).
  Parameter suchThatMaybeOpt : forall {A : Type},
      G (option A) -> (A -> bool) -> G (option A).
  Parameter genN : N -> G N.
  Parameter genBool : G bool.
  (* Parameter sample : forall {A : Type}, G A -> list A. *)

  (* LL: The abstraction barrier is annoying :D *)
(*
  Parameter variant : forall `{Splittable seed} {A : Type}, SplitPath -> G A -> G A.
*)
  Parameter reallyUnsafePromote : forall {r A:Type}, (r -> G A) -> G (r -> A).

  (** * Semantics of generators *)

  (* Set of outcomes semantics definitions (repeated below) *)
  Definition semGenSize {A : Type} (g : G A) (size : nat) : set A :=
    codom (run g size : Infinite.Tree -> _).
  Definition semGen {A : Type} (g : G A) : set A :=
    \bigcup_size semGenSize g size.

  Parameter semGenUnsize : forall {A} (g : G A) (S : set A),
      (forall s, semGenSize g s <--> S) -> (semGen g <--> S).

  Parameter bindGen' : forall {A B : Type} (g : G A), 
      (forall (a : A), (a \in semGen g) -> G B) -> G B.

  Arguments bindGen' [A] [B] _ _.

  (** * Properties of generators *)

  (** A generator is [Unsized] if its semantics does not depend on the runtime size *)
  (* begin Unsized *)
  Class Unsized {A} (g : G A) :=
    {
      unsized : forall s1 s2, semGenSize g s1 <--> semGenSize g s2
    }.
  (* end Unsized *)

  (** Sized generators monotonic in the size parameter *)
  Class SizedMonotonic {A} (g : nat -> G A) :=
    {
      sizeMonotonic :
        forall s s1 s2,
          s1 <= s2 ->
          semGenSize (g s1) s \subset semGenSize (g s2) s
    }.

  (** Sized generators of option type monotonic in the size parameter *)
  Class SizedMonotonicOpt {A} (g : nat -> G (option A)) :=
    {
      sizeMonotonicOpt :
        forall s s1 s2,
          s1 <= s2 ->
          isSome :&: semGenSize (g s1) s \subset isSome :&: semGenSize (g s2) s
    }.
  
  (** Generators monotonic in the runtime size parameter *)
  Class SizeMonotonic {A} (g : G A) :=
    {
      monotonic :
        forall s1 s2, s1 <= s2 -> semGenSize g s1 \subset semGenSize g s2
    }.

  (** Generators monotonic in the runtime size parameter *)
  Class SizeMonotonicOpt {A} (g : G (option A)) :=
    {
      monotonic_opt :
        forall s1 s2, s1 <= s2 -> isSome :&: semGenSize g s1 \subset isSome :&: semGenSize g s2
    }.
  
  (** Generators monotonic in the runtime size parameter *)
  Class SizeAntiMonotonicNone {A} (g : G (option A)) :=
    {
      monotonic_none :
        forall s1 s2, s1 <= s2 -> isNone :&: semGenSize g s2 \subset isNone :&: semGenSize g s1
    }.

  (* CH: Why does Unsized need a _ when A is marked as implict! *)
  Parameter unsized_alt_def :
    forall A (g : G A) `{Unsized _ g},
    forall s, semGenSize g s <--> semGen g.

  (* begin unsizedMonotonic *)
  Declare Instance unsizedMonotonic : forall {A} (g : G A), Unsized g -> SizeMonotonic g.
  (* end unsizedMonotonic *)
  

  (** *  Semantics of combinators *)

  Parameter semReturn :
    forall A (x : A), semGen (returnGen x) <--> [set x].
  Parameter semReturnSize :
    forall A (x : A) size, semGenSize (returnGen x) size <--> [set x].
  
  Declare Instance unsizedReturn {A} (x : A) : Unsized (returnGen x).
  Declare Instance returnGenSizeMonotonic {A} (x : A) : SizeMonotonic (returnGen x).
  Declare Instance returnGenSizeMonotonicOpt {A} (x : option A) : SizeMonotonicOpt (returnGen x).

  Parameter semBindSize :
    forall A B (g : G A) (f : A -> G B) (size : nat),
      semGenSize (bindGen g f) size <-->
                 \bigcup_(a in semGenSize g size) semGenSize (f a) size.

  Parameter semBindSize_subset_compat :
    forall {A B : Type} (g g' : G A) (f f' : A -> G B),
      (forall s, semGenSize g s \subset semGenSize g' s) ->
      (forall x s, semGenSize (f x) s \subset semGenSize (f' x) s) ->
      (forall s, semGenSize (bindGen g f) s \subset semGenSize (bindGen g' f') s).

  Parameter semBindSizeOpt_subset_compat :
    forall {A B : Type} (g g' : G A) (f f' : A -> G (option B)),
      (forall s, semGenSize g s \subset semGenSize g' s) ->
      (forall x s, isSome :&: semGenSize (f x) s \subset isSome :&: semGenSize (f' x) s) ->
      (forall s, isSome :&: semGenSize (bindGen g f) s \subset isSome :&: semGenSize (bindGen g' f') s) .

  Parameter monad_leftid : 
    forall {A B : Type} (a: A) (f : A -> G B),
      semGen (bindGen (returnGen a) f) <--> semGen (f a).
  Parameter monad_rightid : 
    forall {A : Type} (g : G A),
      semGen (bindGen g returnGen) <--> semGen g.
  Parameter monad_assoc: 
    forall {A B C : Type} (ga : G A) (fb : A -> G B) (fc : B -> G C),
      semGen (bindGen (bindGen ga fb) fc) <--> 
             semGen (bindGen ga (fun a => bindGen (fb a) fc)).
  
  (* I'm not sure how this universal quantifier will behave *)
  (* begin bindUnsized *)
  Declare Instance bindUnsized {A B} (g : G A) (f : A -> G B)
          `{Unsized _ g} `{forall x, Unsized (f x)} : Unsized (bindGen g f).
  (* end bindUnsized *)

  (* XXX these will always succeed and they have the same priority *)
  Declare Instance bindMonotonic
          {A B} (g : G A) (f : A -> G B)
          `{SizeMonotonic _ g} `{forall x, SizeMonotonic (f x)} : 
    SizeMonotonic (bindGen g f).

  Declare Instance bindMonotonicOpt
          {A B} (g : G A) (f : A -> G (option B))
          `{SizeMonotonic _ g} `{forall x, SizeMonotonicOpt (f x)} : 
    SizeMonotonicOpt (bindGen g f).

  Declare Instance bindMonotonicStrong
          {A B} (g : G A) (f : A -> G B)
          `{SizeMonotonic _ g} `{forall x, semGen g x -> SizeMonotonic (f x)} : 
    SizeMonotonic (bindGen g f).

  Declare Instance bindMonotonicOptStrong
          {A B} (g : G A) (f : A -> G (option B)) `{SizeMonotonic _ g}
          `{forall x, semGen g x -> SizeMonotonicOpt (f x)} :
    SizeMonotonicOpt (bindGen g f).

  Declare Instance bindOptMonotonic
          {A B} (g : G (option A)) (f : A -> G (option B))
          `{SizeMonotonic _ g} `{forall x, SizeMonotonic (f x)} : 
    SizeMonotonic (bindGenOpt g f).

  Declare Instance bindOptMonotonicOpt
          {A B} (g : G (option A)) (f : A -> G (option B))
          `{SizeMonotonicOpt _ g} `{forall x, SizeMonotonicOpt (f x)} : 
    SizeMonotonicOpt (bindGenOpt g f).
  
  Parameter semBindUnsized1 :
    forall A B (g : G A) (f : A -> G B) `{Unsized _ g},
      semGen (bindGen g f) <--> \bigcup_(a in semGen g) semGen (f a).
  
  Parameter semBindUnsized2 :
    forall A B (g : G A) (f : A -> G B) `{forall a, Unsized (f a)},
      semGen (bindGen g f) <--> \bigcup_(a in semGen g) semGen (f a).
  
  Parameter semBindSizeMonotonic :
  forall {A B} (g : G A) (f : A -> G B)
         `{SizeMonotonic _ g} `{forall a, SizeMonotonic (f a)},
    semGen (bindGen g f) <--> \bigcup_(a in semGen g) semGen (f a).

  Parameter semBindOptSizeMonotonicIncl_r :
    forall {A B} (g : G (option A)) (f : A -> G (option B)) (s1 : set A) (s2 : A -> set B),
      semGen g \subset (Some @: s1) :|: [set None] ->
      (forall x, semGen (f x) \subset Some @: (s2 x) :|: [set None]) -> 
      semGen (bindGenOpt g f) \subset Some @: (\bigcup_(a in s1) s2 a) :|: [set None].

  Parameter semBindSizeMonotonicIncl_r :
    forall {A B} (g : G A) (f : A -> G (option B)) (s1 : set A) (s2 : A -> set B),
      semGen g \subset s1 ->
      (forall x, semGen (f x) \subset Some @: (s2 x) :|: [set None]) -> 
      semGen (bindGen g f) \subset Some @: (\bigcup_(a in s1) s2 a)  :|: [set None].

  Parameter semBindOptSizeMonotonicIncl_l :
    forall {A B} (g : G (option A)) (f : A -> G (option B)) (s1 : set A)  (fs : A -> set B) 
      `{Hg : SizeMonotonicOpt _ g} {Hf : forall a, SizeMonotonicOpt (f a)},
      Some @: s1 \subset semGen g ->
      (forall x, Some @: (fs x) \subset semGen (f x)) ->
      (Some @: \bigcup_(a in s1) (fs a)) \subset semGen (bindGenOpt g f).

  Parameter semBindOptSizeOpt_subset_compat :
    forall {A B : Type} (g g' : G (option A)) (f f' : A -> G (option B)),
      (forall s, isSome :&: semGenSize g s \subset isSome :&: semGenSize g' s) ->
      (forall x s, isSome :&: semGenSize (f x) s \subset isSome :&: semGenSize (f' x) s) ->
      (forall s, isSome :&: semGenSize (bindGenOpt g f) s \subset isSome :&: semGenSize (bindGenOpt g' f') s).

  Parameter semBindSizeMonotonicIncl_l :
    forall {A B} (g : G A) (f : A -> G (option B)) (s1 : set A) (fs : A -> set B) 
      `{Hg : SizeMonotonic _ g}
      `{Hf : forall a, SizeMonotonicOpt (f a)},
    s1 \subset semGen g ->
    (forall x, Some @: (fs x) \subset semGen (f x)) ->
    (Some @: \bigcup_(a in s1) (fs a)) \subset semGen (bindGen g f).

  Parameter semFmap :
    forall A B (f : A -> B) (g : G A),
      semGen (fmap f g) <--> f @: semGen g.

  Parameter semFmapSize :
    forall A B (f : A -> B) (g : G A) (size : nat),
      semGenSize (fmap f g) size <--> f @: semGenSize g size.

  Declare Instance fmapUnsized {A B} (f : A -> B) (g : G A) `{Unsized _ g} : 
    Unsized (fmap f g).

  Declare Instance fmapMonotonic
          {A B} (f : A -> B) (g : G A) `{SizeMonotonic _ g} : 
    SizeMonotonic (fmap f g).

(*
  Parameter semChoose :
    forall A `{ChoosableFromInterval A} (a1 a2 : A),
      RandomQC.leq a1 a2 ->
      (semGen (choose (a1,a2)) <--> [set a | RandomQC.leq a1 a && RandomQC.leq a a2]).

  Parameter semChooseSize :
    forall A `{ChoosableFromInterval A} (a1 a2 : A),
      RandomQC.leq a1 a2 ->
      forall size, (semGenSize (choose (a1,a2)) size <-->
              [set a | RandomQC.leq a1 a && RandomQC.leq a a2]).

  Declare Instance chooseUnsized A `{ChoosableFromInterval A} (a1 a2 : A) : 
    Unsized (choose (a1, a2)).
*)

  Parameter semGenN :
    forall bound, semGen (genN bound) <--> [set m | m <= bound].

  Parameter semGenNSize : forall bound size,
      semGenSize (genN bound) size <--> [set m | m <= bound].

  Parameter semGenBool : semGen genBool <--> setT.
  Parameter semGenBoolSize : forall size,
      semGenSize genBool size <--> setT.

  Declare Instance genNSizeMonotonic (bound : N) :
    SizeMonotonic (genN bound).

  Declare Instance genBoolSizeMonotonic : SizeMonotonic genBool.

  Parameter semSized :
    forall A (f : nat -> G A),
      semGen (sized f) <--> \bigcup_s semGenSize (f s) s.

  Parameter semSizedSize :
    forall A (f : nat -> G A) s,
      semGenSize (sized f) s <--> semGenSize (f s) s.

  (* TODO change name *)

  Parameter semSized_alt :
    forall A (f : nat -> G A) `{forall n, SizeMonotonic (f n)},
      (forall n m s,  n <= m -> semGenSize (f n) s \subset semGenSize (f m) s) ->
      semGen (sized f) <--> \bigcup_n (semGen (f n)).

  Parameter semSized_opt :
    forall A (f : nat -> G (option A)) (H : forall n, SizeMonotonicOpt (f n)) (H' : SizedMonotonicOpt f),
      isSome :&: semGen (sized f) <--> isSome :&: \bigcup_n (semGen (f n)).

  Declare Instance sizedSizeMonotonic
          A (gen : nat -> G A) `{forall n, SizeMonotonic (gen n)} `{SizedMonotonic A gen} :
    SizeMonotonic (sized gen).

  Declare Instance sizedSizeMonotonicOpt
          A (gen : nat -> G (option A)) `{forall n, SizeMonotonic (gen n)} `{SizedMonotonicOpt A gen} :
    SizeMonotonicOpt (sized gen).
  
  Parameter semResize :
    forall A (n : nat) (g : G A),
      semGen (resize n g) <--> semGenSize g n.

  Parameter semSizeResize :
    forall A (s n : nat) (g : G A),
      semGenSize (resize n g) s <--> semGenSize g n.

  Declare Instance unsizedResize {A} (g : G A) n : 
    Unsized (resize n g).


  Parameter semSuchThatMaybe_sound':
    forall A (g : G A) (f : A -> bool),
      semGen (suchThatMaybe g f) \subset None |: some @: (semGen g :&: f).

  (* Declare Instance suchThatMaybeMonotonic *)
  (*        {A : Type} (g : G A) (f : A -> bool) `{SizeMonotonic _ g} :  *)
  (*   SizeMonotonic (suchThatMaybe g f). *)

  (* Declare Instance suchThatMaybeOptMonotonic *)
  (*         {A : Type} (g : G (option A)) (f : A -> bool) `{SizeMonotonic _ g} :  *)
  (*   SizeMonotonic (suchThatMaybeOpt g f). *)

  Declare Instance suchThatMaybeMonotonicOpt
           {A : Type} (g : G A) (f : A -> bool) `{SizeMonotonic _ g} : 
    SizeMonotonicOpt (suchThatMaybe g f).
  
  Declare Instance suchThatMaybeOptMonotonicOpt
           {A : Type} (g : G (option A)) (f : A -> bool) `{SizeMonotonicOpt _ g} : 
    SizeMonotonicOpt (suchThatMaybeOpt g f).

  Parameter semSuchThatMaybe_complete:
    forall (A : Type) (g : G A) (f : A -> bool) (s : set A),
      SizeMonotonic g ->
      s \subset semGen g ->
      (Some @: (s :&: (fun x : A => f x))) \subset
                                        semGen (suchThatMaybe g f).

  Parameter semSuchThatMaybeOpt_complete:
    forall (A : Type) (g : G (option A)) (f : A -> bool) (s : set A),
      SizeMonotonicOpt g ->
      (Some @: s) \subset semGen g ->
      (Some @: (s :&: (fun x : A => f x))) \subset
                                        semGen (suchThatMaybeOpt g f).

  Parameter semSuchThatMaybe_sound:
    forall (A : Type) (g : G A) (f : A -> bool) (s : set A),
      semGen g \subset s ->
      semGen (suchThatMaybe g f) \subset ((Some @: (s :&: (fun x : A => f x))) :|: [set None]).

  Parameter semSuchThatMaybeOpt_sound:
    forall (A : Type) (g : G (option A)) (f : A -> bool) (s : set A),
      semGen g \subset ((Some @: s) :|: [set None]) ->
      semGen (suchThatMaybeOpt g f) \subset (Some @: (s :&: (fun x : A => f x)) :|: [set None]).

  Parameter suchThatMaybe_subset_compat :
    forall {A : Type} (p : A -> bool) (g1 g2 : G A),
      (forall s, (semGenSize g1 s) \subset (semGenSize g2 s)) ->
      (forall s, isSome :&: (semGenSize (suchThatMaybe g1 p) s) \subset
            isSome :&: (semGenSize (suchThatMaybe g2 p) s)).

  Parameter suchThatMaybeOpt_subset_compat :
    forall {A : Type} (p : A -> bool) (g1 g2 : G (option A)),
      (forall s, isSome :&: (semGenSize g1 s) \subset isSome :&: (semGenSize g2 s)) ->
      (forall s, isSome :&: (semGenSize (suchThatMaybeOpt g1 p) s) \subset
            isSome :&: (semGenSize (suchThatMaybeOpt g2 p) s)).

  (* This (very concrete) spec is needed to prove shrinking *)
  Parameter semPromote :
    forall A (m : Rose (G A)),
      semGen (promote m) <-->
      codom2 (fun size (seed : Infinite.Tree) =>
                fmapRose (fun g => run g size seed) m).

  Parameter semPromoteSize :
    forall (A : Type) (m : Rose (G A)) n,
      semGenSize (promote m) n <-->
      (fun t : Rose A =>
         exists (s : Infinite.Tree),
           fmapRose (fun g : G A => run g n s) m = t).

  (* Those are too concrete, but I need them to prove shrinking.
   Does this reveal a weakness in our framework?
   Should we try to get rid of this?
   This is expected since the spec of promote is too concrete. *)

  Parameter runFmap :
    forall (A B : Type) (f : A -> B) (g : G A) size
           (seed : Infinite.Tree),
      run (fmap f g) size seed = f (run g size seed).
  
  Parameter runPromote :
    forall A (m : Rose (G A)) size (seed : Infinite.Tree),
      run (promote m) size seed =
      fmapRose (fun (g : G A) => run g size seed) m.
  
  Parameter semFmapBind :
    forall A B C (g : G A) (f1 : B -> C) (f2 : A -> G B),
      semGen (fmap f1 (bindGen g f2)) <-->
      semGen (bindGen g (fun x => fmap f1 (f2 x))).

  Global Instance GMonad : Monad G :=
  {
    ret T x := returnGen x ;
    bind T U m f := bindGen m f 
  }.

  Definition GOpt A := G (option A).

  Global Instance GOptMonad : `{Monad GOpt} :=
  {
    ret A x := returnGen (Some x);
    bind A B m k := bindGenOpt m k
  }.

(*
  Parameter promoteVariant :
    forall `{Splittable seed} {A B : Type} (a : A) (f : A -> SplitPath) (g : G B) size
           (r r1 r2 : seed),
      split r = (r1,r2) ->
      run (reallyUnsafePromote (fun a => variant (f a) g)) size r a =
      run g size (varySeed (f a) r1). *)

End GenLowInterface.

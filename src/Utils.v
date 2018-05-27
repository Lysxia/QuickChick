Require Import List.
Require Import SimpleIO.IOMonad.

Import ListNotations.

Fixpoint fold_io {A B} (f : A -> B -> IO A) (xs : list B) (a : A) :
  IO A :=
  match xs with
  | [] => ret a
  | x :: xs' => bind (f a x) (fun a' => fold_io f xs' a')
  end.

Fixpoint existsb_io {A} (f : A -> IO bool) (xs : list A) : IO bool :=
  match xs with
  | [] => ret true
  | x :: xs' =>
    bind (f x) (fun b => if b then ret true else existsb_io f xs')
  end.

Fixpoint traverse_io_ {A} (f : A -> IO unit) (xs : list A) :
  IO unit :=
  match xs with
  | [] => ret tt
  | x :: xs' => bind (f x) (fun _ => traverse_io_ f xs')
  end.

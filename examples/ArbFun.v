(* Port of https://github.com/jmid/qcheck-fun/blob/master/fun.ml (OCaml) *)

Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import String. Open Scope string.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From QuickChick Require Import QuickChick Tactics CoArbitrary GenLow.
Import QcDefaultNotation.
Import QcDoNotation.
Open Scope qc_scope.

Require Import List.
Import ListNotations.

Definition prop_false_bool (f : bool -> bool) (b : bool) : bool :=
  f (f b) = b ?.

Definition g := @genFun bool bool coArbBool (@GenOfGenSized bool (@genBoolSized)).

(*
Print g.
Compute g.
Sample (@arbitrary _ g).
*)

Check forAll.

QuickChick (forAll (@arbitrary _ g) prop_false_bool).

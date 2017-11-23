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

(* WIP *)

Check @genFun bool bool coArbBool.

Check @sample (bool -> bool) (@genFun bool bool coArbBool arbitrary).

Check (@sample _ (genFun : G (bool -> bool))).

QuickChick (forAll  (fun b => (prop_false_bool (fun _ => b)))).
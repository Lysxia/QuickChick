Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

From Coq Require Import
     Ascii String NArith.

From QuickChick Require Import
     Splittable.

Module Import Internal.

(* Binary numbers. Most operations assume little-endianness,
   but this can also be used as a big-endian representation.
   This will be extracted to [Int64.t]. *)
Inductive binary : Type :=
| b0 : binary -> binary
| b1 : binary -> binary
| b_ : binary (* End *)
.

(* Hidden by efficient extraction. *)
Module InternalPrimitives.

Fixpoint zeroes (d : nat) : binary :=
  match d with
  | O => b_
  | S d => b0 (zeroes d)
  end.

Fixpoint rev' (y z : binary) : binary :=
  match z with
  | b0 z => rev' (b0 y) z
  | b1 z => rev' (b1 y) z
  | b_ => y
  end.

(* big-endian <-> little-endian *)
(* Eta-expand because this somehow ends up in the extracted
   code and we need to not evaluate it. *)
Definition rev (z : binary) : binary := rev' b_ z.

Notation bit := bool.
Notation zero := false.
Notation one := true.

Definition of_bit (a : bool) : binary -> binary :=
  match a with
  | false => b0
  | true => b1
  end.

Fixpoint succ (z : binary) : binary :=
  match z with
  | b1 z => b0 (succ z)
  | _ => z
  end.

(* Add two numbers with carry. The result is truncated to the
   length of the first operand. *)
Fixpoint plus' (c : bit) (z1 z2 : binary) :=
  match z1, z2 with
  | b0 z1, b0 z2 => of_bit c (plus' zero z1 z2)
  | b1 z1, b0 z2 | b0 z1, b1 z2 =>
    match c with
    | zero => b1 (plus' zero z1 z2)
    | one => b0 (plus' one z1 z2)
    end
  | b1 z1, b1 z2 =>
    of_bit c (plus' one z1 z2)
  | _, _ => succ z1
  end.

Fixpoint hex' (acc : binary) (s : string) : binary :=
  match s with
  | EmptyString => acc
  | String x s =>
    let acc :=
        match x with
        (* Digit *)
        | Ascii a0 a1 a2 a3 _ _ false _ =>
          of_bit a0 (of_bit a1 (of_bit a2 (of_bit a3 acc)))
        | "a" => b0 (b1 (b0 (b1 acc)))
        | "b" => b1 (b1 (b0 (b1 acc)))
        | "c" => b0 (b0 (b1 (b1 acc)))
        | "d" => b1 (b0 (b1 (b1 acc)))
        | "e" => b0 (b1 (b1 (b1 acc)))
        | "f" => b1 (b1 (b1 (b1 acc)))
        | _ => b0 (b0 (b0 (b0 acc)))
        end%char in
    hex' acc s
  end.

Definition hex : string -> binary := hex' b_.

Fixpoint positive_to_binary (d : nat) (n : positive) : binary :=
  match n, d with
  | xI n, S d => b1 (positive_to_binary d n)
  | xO n, S d => b0 (positive_to_binary d n)
  | xH,   S d => b1 (zeroes d)
  | _, O => b_
  end.

Definition N_to_binary (d : nat) (n : N) : binary :=
  match n with
  | N0 => zeroes d
  | Npos n => positive_to_binary d n
  end.

Fixpoint binary_to_N (z : binary) :=
  match z with
  | b_ => 0%N
  | b1 z => N.succ_double (binary_to_N z)
  | b0 z => N.double (binary_to_N z)
  end.

End InternalPrimitives.

(* To be extracted efficiently. *)
Module Import ExternalPrimitives.
Import InternalPrimitives.

(** * Primitive operations *)

(* Bitwise xor. The second operand is
   extended/truncated to the length of the first one. *)
Fixpoint xor (z1 z2 : binary) :=
  match z1, z2 with
  | b0 z1, b0 z2 | b1 z1, b1 z2 => b0 (xor z1 z2)
  | b0 z1, b1 z2 | b1 z1, b0 z2 => b1 (xor z1 z2)
  | _, _ => z1
  end.

Fixpoint shiftr (z : binary) (n : nat) :=
  match n, z with
  | S n, (b0 z | b1 z) => shiftr z n
  | _, _ => z
  end.

Definition plus : binary -> binary -> binary := plus' zero.

Fixpoint mul (z1 z2 : binary) :=
  match z1 with
  | b0 z1 => b0 (mul z1 z2)
  | b1 z1 => plus (b0 (mul z1 z2)) z2
  | b_ => b_
  end.

(* True if less than [n] bits are set in [z]. *)
Fixpoint popcount_under (n : nat) (z : binary) : bool :=
  match z, n with
  | b1 _, O => false
  | b1 z, S n => popcount_under n z
  | b0 z, _ => popcount_under n z
  | b_, _ => true
  end.

(* Set the first bit of [z]. *)
Definition set_lsb z :=
  match z with
  | b0 z => b1 z
  | _ => z
  end.

(** * SplitMix constants *)

Definition golden_gamma : binary :=
  Eval compute in hex "9e3779b97f4a7c15".

Definition x_ff51afd7ed558ccd : binary :=
  Eval compute in hex "ff51afd7ed558ccd".
Definition x_c4ceb9fe1a85ec53 : binary :=
  Eval compute in hex "c4ceb9fe1a85ec53".

Definition x_bf58476d1ce4e5b9 : binary :=
  Eval compute in hex "bf58476d1ce4e5b9".
Definition x_94d049bb133111eb : binary :=
  Eval compute in hex "94d049bb133111eb".

Definition x_aaaaaaaaaaaaaaaa : binary :=
  Eval compute in hex "aaaaaaaaaaaaaaaa".

(** * Binary path representation. *)

Definition N64 := binary.

(** * Conversions *)

Definition positive_to_N64 := positive_to_binary 64.
Definition N_to_N64 := N_to_binary 64.
Definition N64_to_N := binary_to_N.

(* Big-endian binary. Will be extracted to a regular [int64]
   (no endianness). *)
Definition big_N64 : Type := binary.

(* Encoding of the length of a [big_N64] counter interpreted
   as a binary path.

   Extraction magic.
   In Coq: 63 - number of counter bits (remaining padding).
   In OCaml: 2^(number of counter bits). *)
Definition pad : Type := nat.

Definition empty_counter : big_N64 := b_.
Definition full_pad : pad := 63.

(* Little-endian [2 * c]. Each increment of the counter
   corresponds to the two steps in SplitMix's original [split]
   function. *)
Definition normalize_counter (c : big_N64) : N64 := b0 (rev c).

(* Extend a [big_N64] path with [0] or [1].
   If the path is full (length 63), output it as [Some]
   64bit word to hash, and produce fresh paths. *)
Definition split_path (c : big_N64) (r : pad) :
  option N64 * big_N64 * big_N64 * pad :=
  match r with
  | S r => (None, b0 c, b1 c, r)
  | O => (Some (normalize_counter c), b0 b_, b1 b_, 63)
  end.

End ExternalPrimitives.

(* SplitMix implementation. *)

(* [z ^ (z >>> n)]*)
Definition shift_xor z (n : nat) :=
  xor z (shiftr z n).

Definition mix64 z :=
  let z := mul x_ff51afd7ed558ccd (shift_xor z 33) in
  let z := mul x_c4ceb9fe1a85ec53 (shift_xor z 33) in
  shift_xor z 33.

Definition mix64variant13 z :=
  let z := mul x_bf58476d1ce4e5b9 (shift_xor z 30) in
  let z := mul x_94d049bb133111eb (shift_xor z 27) in
  shift_xor z 31.

Definition mix_gamma z :=
  let z := set_lsb (mix64 z) in
  if popcount_under 24 (shift_xor z 1) then
    xor z x_aaaaaaaaaaaaaaaa
  else
    z.

(* Palka's trick of constructing a path (stored in [counter]) that
   only gets hashed once in a while. In this case the hash function
   is [mix64variant13 (seed + g * counter)].  *)
Record State := MkState {
  seed : N64;
  gamma : N64;
  counter : big_N64;
  remaining : pad;
}.

Definition split '(MkState s0 g c r) : State * State :=
  let '(oc, c0, c1, r) := split_path c r in
  match oc with
  | None =>
    let new c := MkState s0 g c r in
    (new c0, new c1)
  | Some c' =>
    let s1 := plus s0 (mul g c') in
    let s2 := plus s1 g in
    let s' := mix64variant13 s1 in
    let g' := mix_gamma s2 in
    let new c := MkState s' g' c r in
    (new c0, new c1)
  end.

(* Probably overkill if you just need a few bits. *)
Definition to_binary '(MkState s0 g c r) : binary :=
  let s1 := plus s0 (mul g (normalize_counter c)) in
  mix64variant13 s1.

Definition of_seed (n : N) : State :=
  {| seed := N_to_N64 n;
     gamma := golden_gamma;
     counter := empty_counter;
     remaining := full_pad; |}.

Module Import InternalBinaryStreams.
Section BinaryStreams.

Variable State : Type.
Variable split : State -> State * State.
Variable to_binary : State -> binary.

Definition bstream : Type := State * binary.

Definition to_bstream (s : State) : bstream :=
  let '(s1, s2) := split s in
  (s2, to_binary s1).

Definition step (sb : bstream) : bool * bstream :=
  let '(s, b) := sb in
  match b with
  | b_ =>
    let '(s, b) := to_bstream s in
    match b with
    | b0 b => (false, (s, b))
    | b1 b => (true,  (s, b))
    | b_   => (false, (s, b)) (* Should not happen *)
    end
  | b0 b => (false, (s, b))
  | b1 b => (true,  (s, b))
  end.

End BinaryStreams.
End InternalBinaryStreams.

Export ExternalPrimitives.
Import InternalPrimitives.
Import InternalBinaryStreams.

(* Convert a little-endian [positive] to a big-endian [binary]. *)
Definition rev_pos (p : positive) : binary :=
  let fix rev_pos' p b :=
      match p with
      | xH => b1 b
      | xI p => rev_pos' p (b1 b)
      | xO p => rev_pos' p (b0 b)
      end in
  rev_pos' p b_.

Definition lsb (z : binary) : bool :=
  match z with
  | b1 _ => true
  | b0 _ | b_ => false
  end.

(* A generic algorithm to get approximately uniform distributions
   on a finite interval out of a splittable seed.
   This can be extracted to a more efficient version;
   the parametrization by [split] and [to_binary] also makes
   the dependency on these two functions explicit (via
   [random_binary]) to ensure they get extracted too. *)
Definition random_binary' {S : Type}
           (split : S -> (S * S))
           (to_binary : S -> binary)
           (s : S) (bound : binary) : binary :=
  let step := step _ split to_binary in
  let to_bstream := to_bstream _ split to_binary in
  let fix uniformly bound sb acc :=
      match bound with
      | b_ => acc
      | b0 bound | b1 bound =>
        let '(b, sb) := step sb in
        uniformly bound sb (of_bit b acc)
      end in
  let fix retry (tries : nat) sb :=
      match tries with
      | O => b_
      | S tries =>
        let fix try_once bound sb acc :=
            match bound with
            | b_ => acc
            | b0 bound =>
              let '(b, sb) := step sb in
              if b then retry tries sb
              else try_once bound sb (b0 acc)
            | b1 bound =>
              let '(b, sb) := step sb in
              if b then try_once bound sb (b1 acc)
              else uniformly bound sb (b0 acc)
            end
        in try_once bound sb b_
      end in
  retry 64 (to_bstream s).

End Internal.

(* Big-endian [bound], little-endian result! *)
Definition random_binary : State -> binary -> binary :=
  random_binary' split to_binary.

(* Random [N] between [0] and [bound], inclusive. *)
Definition random_N_0 (s : State) (bound : N) : N :=
  match bound with
  | N0 => N0
  | Npos bound => N64_to_N (random_binary s (rev_pos bound))
  end.

(* Random boolean. *)
Definition random_bool (s : State) : bool :=
  lsb (to_binary s).

Module Example.

Import NArith.

Fixpoint split_many2 (n : nat) g :=
  match n with
  | O => g
  | S n' => let (_, g) := split g in split_many2 n' g
  end.

Import List.
Import ListNotations.

Definition example_N :=
  map (fun x => random_N_0 (of_seed x) 10)
      [10;20;30;40;50;61;72;83;96;101;102;103]%N.

(* Compute example_N. *)

End Example.

Section Splittable.

Import ssrnat ssrbool.

(* Concrete implementation of a splittable PRNG. *)
Definition RandomSeed := State.

Lemma randomN_0_correct : forall (s : State) (bound : N),
    (random_N_0 s bound <= bound).
Proof.
Admitted.

Global Instance Splittable_State : Splittable State :=
  { randomSplit := split;
    randomN_0 := random_N_0;
    randomBool := random_bool;
    randomN_0_correct := randomN_0_correct;
  }.

(* TODO: better ways to get an initial seed. *)
Definition newRandomSeed : State := of_seed 33.

(* This is a fast implementation, but its state is finite
   and difficult to reason about. It is not suitable to
   describe the set of values that a generator can produce.
   We must consider better-behaved types of seeds. *)

End Splittable.

(* Sanity checks. *)
Module Properties.
Import Internal.
Import InternalPrimitives.

Example binary_from_to : (binary_to_N (N_to_binary 64 10) = 10)%N.
Proof. reflexivity. Qed.

Fixpoint length_binary (z : binary) : nat :=
  match z with
  | b0 z | b1 z => S (length_binary z)
  | b_ => O
  end.

Lemma xor_length :
  forall z1 z2, length_binary (xor z1 z2) = length_binary z1.
Proof.
  induction z1; destruct z2; simpl; try f_equal; auto.
Qed.

Example shiftr_test :
  shiftr (N_to_binary 10 30) 3 = (N_to_binary 7 3%N).
Proof. reflexivity. Qed.

Lemma shiftr_length :
  forall n z, length_binary (shiftr z n) = length_binary z - n.
Proof.
  induction n; destruct z; simpl; auto.
Qed.

Definition succ_length :
  forall z, length_binary (succ z) = length_binary z.
Proof.
  induction z; simpl; auto.
Qed.

Lemma plus'_length :
  forall z1 z2 c, length_binary (plus' c z1 z2) = length_binary z1.
Proof.
  induction z1; destruct z2; destruct c; simpl; auto using succ_length.
Qed.

Example plus_test :
  plus (N_to_binary 10 3) (N_to_binary 5 5) = N_to_binary 10 8.
Proof. reflexivity. Qed.

Lemma plus_length :
  forall z1 z2, length_binary (plus z1 z2) = length_binary z1.
Proof.
  intros; apply plus'_length.
Qed.

Example mul_test :
  mul (N_to_binary 10 3) (N_to_binary 5 5) = N_to_binary 10 15.
Proof. reflexivity. Qed.

Lemma mul_length :
  forall z1 z2, length_binary (mul z1 z2) = length_binary z1.
Proof.
  induction z1; intro z2; simpl; auto.
  rewrite plus_length; simpl; auto.
Qed.

End Properties.

(* Compute hex "123". *)

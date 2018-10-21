Require Extraction.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlZInt.

Require Import SplitMix.
Import External.

Extract Inductive binary => "Int64.t"
  [ "(fun _ -> assert false)"
    "(fun _ -> assert false)"
    "0L (* dummy *)" ]
  "(fun _ -> assert false)".

Extract Inlined Constant positive_to_N64 => "Int64.of_int".
Extract Inlined Constant N_to_N64 => "Int64.of_int".
Extract Inlined Constant N64_to_N => "Int64.to_int".

Extract Inlined Constant xor => "Int64.logxor".
Extract Inlined Constant shiftr => "Int64.shift_right_logical".
Extract Inlined Constant plus => "Int64.add".
Extract Inlined Constant mul => "Int64.mul".
Extract Inlined Constant set_lsb => "Int64.logor 1L".

Extract Constant popcount_under =>
  "(fun n z ->
    let open Int64 in
    let popcount z =
          let z = sub z (logand (shift_right_logical z 1)
                                0x5555_5555_5555_5555L) in
          let z = add (logand z 0x3333_3333_3333_3333L)
                      (logand (shift_right_logical z 2)
                              0x3333_3333_3333_3333L) in
          let z = logand (add z (shift_right_logical z 4))
                         0x0f0f_0f0f_0f0f_0f0fL in
          shift_right_logical (mul z 0x01010101_01010101L) 56
    in popcount z < 24L
  )".

Extract Inlined Constant golden_gamma => "0x9e3779b97f4a7c15L".
Extract Inlined Constant x_ff51afd7ed558ccd => "0xff51afd7ed558ccdL".
Extract Inlined Constant x_c4ceb9fe1a85ec53 => "0xc4ceb9fe1a85ec53L".
Extract Inlined Constant x_bf58476d1ce4e5b9 => "0xbf58476d1ce4e5b9L".
Extract Inlined Constant x_94d049bb133111eb => "0x94d049bb133111ebL".
Extract Inlined Constant x_aaaaaaaaaaaaaaaa => "0xaaaaaaaaaaaaaaaaL".

Extract Inlined Constant big_N64 => "Int64.t".
Extract Inlined Constant pad => "Int64.t".
Extract Inlined Constant empty_counter => "0L".
Extract Inlined Constant full_pad => "1L".

Extract Inlined Constant normalize_counter => "Int64.mul 2L".
Extract Constant split_path =>
  "(fun c r ->
    if r < 0L then
      (((Some (Int64.mul c 2L), 0L), 1L), 2L)
    else
      (((None, c), Int64.logor c r), Int64.shift_left r 1))".

Extract Inlined Constant rev_pos => "Int64.of_int".
Extract Inlined Constant lsb => "(fun x -> x < 0L)".

Extract Constant random_binary' =>
  "(fun split to_binary ->
  (* bound must be positive. *)
  let rec int64' rng bound =
    let (rng, rng0) = split rng in
    let bits = to_binary rng0 in
    (* Make it nonnegative at the cost of one bit. *)
    let r = Int64.shift_right_logical bits 1 in
    let v = Int64.rem r bound in
    if Int64.sub bits v > Int64.sub Int64.min_int bound then
      int64' rng bound
    else
      v in
  fun rng bound -> int64' rng (Int64.add bound 1L))".

(* We extract these explicitly to silence some warnings. Otherwise,
   these get extracted with the [fun _ -> assert false] from [binary]
   at the top of this file inlined, resulting in "arguments unused"
   warnings. *)
Import InternalPrimitives.

Extract Constant zeroes => "fun _ -> assert false".
Extract Constant rev' => "fun _ -> assert false".
Extract Constant rev => "fun _ -> assert false".
Extract Constant of_bit => "fun _ -> assert false".
Extract Constant succ => "fun _ -> assert false".
Extract Constant plus' => "fun _ -> assert false".
Extract Constant hex' => "fun _ -> assert false".
Extract Constant hex => "fun _ -> assert false".
Extract Constant positive_to_binary => "fun _ -> assert false".
Extract Constant N_to_binary => "fun _ -> assert false".
Extract Constant binary_to_N => "fun _ -> assert false".

Extract Constant InternalBinaryStreams.step => "fun _ -> assert false".

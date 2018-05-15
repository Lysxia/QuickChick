Set Warnings "-extraction-opaque-accessed,-extraction".
Set Warnings "-notation-overridden,-parsing".

Require Import ZArith.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import RandomQC RoseTrees Test Show Checker.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlZInt.

Extraction Blacklist String List.

Extract Constant show_nat =>
  "(fun i ->
  let s = string_of_int i in
  let rec copy acc i =
    if i < 0 then acc else copy (s.[i] :: acc) (i-1)
  in copy [] (String.length s - 1))".

Extract Constant show_int =>
  "(fun i ->
  let s = string_of_int i in
  let rec copy acc i =
    if i < 0 then acc else copy (s.[i] :: acc) (i-1)
  in copy [] (String.length s - 1))".

Extract Constant RandomSeed   => "PureSplitMix.t".
Extract Constant randomSplit  => "PureSplitMix.split".
Extract Constant mkRandomSeed =>
  "(fun x -> PureSplitMix.of_seed (Int64.of_int x))".
Extract Constant randomRBool => "(fun _ r -> PureSplitMix.bool r)".
Extract Constant randomNat => "PureSplitMix.int".
Extract Constant randomInt => "PureSplitMix.int".
Extract Constant newRandomSeed => "(PureSplitMix.auto_seed ())".

Extract Inductive Lazy => "Lazy.t" [lazy].
Extract Constant force => "Lazy.force".

(* Extract Constant Test.ltAscii => "(<=)". *)
(* Extract Constant Test.strEq   => "(=)". *)
Extract Constant Nat.div => "(/)".
Extract Constant Test.gte => "(>=)".
Extract Constant le_gt_dec => "(<=)".
Extract Constant trace => 
  "(fun l -> print_string (
   let s = Bytes.create (List.length l) in
   let rec copy i = function
    | [] -> s
    | c :: l -> s.[i] <- c; copy (i+1) l
   in Bytes.to_string (copy 0 l)); flush stdout; fun y -> y)".

Set Extraction AccessOpaque.

Extract Constant Show.nl => "['\n']".

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssreflect ssrnat ssrbool div eqtype.
Extract Constant divn => "(/)".
Extract Constant modn => "(fun x y -> x mod y)".
Extract Constant eqn => "(==)".

Axiom print_extracted_coq_string : string -> unit.
Extract Constant print_extracted_coq_string => 
 "fun l -> print_string (  
   let s = Bytes.create (List.length l) in
   let rec copy i = function
    | [] -> s
    | c :: l -> s.[i] <- c; copy (i+1) l
   in Bytes.to_string (copy 0 l))".


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
Extract Constant show_bool =>
  "(fun i ->    
  let s = string_of_bool i in
  let rec copy acc i =
    if i < 0 then acc else copy (s.[i] :: acc) (i-1)
  in copy [] (String.length s - 1))".

Extract Constant show_int =>
  "(fun i ->    
  let s = string_of_int i in
  let rec copy acc i =
    if i < 0 then acc else copy (s.[i] :: acc) (i-1)
  in copy [] (String.length s - 1))".

(* Extract Constant RandomSeed   => "Random.State.t". *)
Extract Constant RandomSeed   => "Quickchick_lib.SPRNG.t".
Extract Constant randomNext   => "Quickchick_lib.SPRNG.bits".
(* Extract Constant rndGenRange => "SR.genRange".*)
Extract Constant randomSplit  => "Quickchick_lib.SPRNG.split".
Extract Constant mkRandomSeed => "(fun x -> Quickchick_lib.SPRNG.make [|x|])".
Extract Constant randomRNat  =>
  "(fun (x,y) r -> if y < x then failwith ""choose called with unordered arguments"" else let (a, r) = Quickchick_lib.SPRNG.int (y - x + 1) r in (x+a, r))".
Extract Constant randomRBool => "(fun _ r -> Quickchick_lib.SPRNG.bool r)".
Extract Constant randomRInt  =>
  "(fun (x,y) r -> if y < x then failwith ""choose called with unordered arguments"" else let (a, r) = Quickchick_lib.SPRNG.int (y - x + 1) r in (x+a, r))".
Extract Constant newRandomSeed => "(Quickchick_lib.SPRNG.make_self_init ())".

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
   in copy 0 l); flush stdout; fun y -> y)".

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
   in copy 0 l)".


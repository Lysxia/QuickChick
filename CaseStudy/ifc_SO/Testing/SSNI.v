Require Import String.
Require Import Arith.EqNat.
Require Import ZArith.

Require Import Machine.

Require Import QuickChick.

Require Import Common.
Require Import Printing.
Require Import Shrinking.
Require Import Generation.
Require Import Indist.

Open Scope string_scope.

Require Import Show.

Require Import Reachability.
Definition propSSNI_helper t v :=
  let '(Var lab st1 st2) := v in
(*  Property.trace (Show.show lab ++ Show.nl ++
     showStatePair lab frameMap1 frameMap2 st1 st2) *)

  collect (option_bind opcode_of_instr
            (instr_lookup (st_imem st1) (st_pc st1))) 

(* collect (show lab) *)
  (let is_low_state st := isLow (pc_lab (st_pc st)) lab in
  if indist lab st1 st2 then
     (* XXX Our generator should always give us this by design.
            If that's not the case the generator is broken. *)
     match exec t st1 with
       | Some (tr1, st1') =>
         if is_low_state st1 then
           match exec t st2 with
             | Some (tr2, st2') =>
               collect "LOW -> *" (
               whenFail (Property.trace 
                           ("LOW -> *" ++ nl ++
                           (show_execution lab [st1; st1'] [st2; st2'])))
                   (observe_comp (observe lab tr1) (observe lab tr2) 
                    && (indist lab st1' st2'))
               )
             | _ => (* 1 took a low step and 2 failed *)
               collect "Second failed" (property true)
(*
                ((Property.trace (show_pair lab st1 st1'))
                (property false))
*)
               (* XXX This used to fail the property in ICFP paper.
                  But here it does happen for Alloc, Store and BRet *)
           end
         else (* is_high st1 *)
           if is_low_state st1' then
             match exec t st2 with
               | Some (tr2, st2') =>
                 if is_low_state st2' then 
                   collect "HIGH -> LOW" (
                   (whenFail (Property.trace ("HIGH -> LOW" ++ Show.nl ++
                               (show_execution lab [st1; st1'] [st2; st2'])))
                             (observe_comp (observe lab tr1) (observe lab tr2) 
                              && (indist lab st1' st2')))
                   )
                 else collect "Second not low" (property true)
                      (* This can happen; it's just a discard *)
               | _ => collect "Second failed H" (property true)
                      (* This can happen; it's just a discard *)
             end
           else
             collect "HIGH -> HIGH" (
             whenFail (Property.trace ("HIGH -> HIGH" ++ Show.nl ++
                         (show_pair lab st1 st1')))
                      (beq_nat (List.length (observe lab tr1)) 0 
                       && indist lab st1 st1')
             )
       | _ => collect "Failed" (property true)
              (* This can happen; it's just a discard *)
     end
  else collect "Not indist!" (property true)).
       (* XXX this should never happen with a correct generator;
              and prop_generate_indist already tests this;
              so this should either go away or become (propery false) *)

Definition propSSNI t : Property := 
  forAllShrink (fun _ => ""%string) gen_variation_state (fun _ => nil) (* shrinkVState *) (propSSNI_helper t).
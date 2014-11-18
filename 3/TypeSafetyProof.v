(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Defining type safety, page 67.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.

Require Export FormalSyntax.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export DynamicSemanticsTypeSubstitution.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemantics.
Require Export TypeSafety.
Require Export CpdtTactics.

Theorem Type_Safety :
(*   If ·; ·; ·; τ styp s, ret s, and ·; s → H ; s *)
 forall (s : St) (tau : Tau),
        styp [] [] [] tau s ->
        ret s ->
        exists (h' : H) (s' : St), 
           Sstar [] s h' s' -> 
           NotStuck h' s'.
Proof.
 Definition Thm (s : St) (tau : Tau) : Prop := 
   (ret s ->
     exists (h' : H) (s' : St), 
       Sstar [] s h' s' -> 
       NotStuck h' s').
  intros s tau.
  apply (Term_ind_mutual
           (fun (s : St) =>  
              forall (tau : Tau) (ts : (styp [] [] [] tau s)), 
                Thm s tau)
           (fun (e : E ) =>
              forall (tau : Tau) (ts : (styp [] [] [] tau (e_s e))),
                Thm (e_s e) tau)
           (fun (f : F) =>
              forall (ts : (styp [] [] [] tau (e_s (f_e f)))),
                Thm (e_s (f_e f)) tau));
        repeat (unfold Thm; crush).
  (* Crush gets one. *)
Admitted.


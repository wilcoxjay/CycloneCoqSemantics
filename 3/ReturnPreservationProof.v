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

Lemma A_8_Return_Preservation:
  forall (s s' : St) (h h' : H),
  ret s ->
  S h s h' s' ->
  ret s'.
Proof.
  intros s s' h h' retder.
  apply (SLR_ind_mutual 
           (fun (h : H) (s : St) (h' : H) (s' : St) (rstep: R h s h' s') =>
              ret s')
           (fun (h : H) (s : St) (h' : H) (s' : St) (sstep: S h s h' s') =>
              ret s')
           (fun (h : H) (s : St) (h' : H) (s' : St) (lstep: L h s h' s') =>
              ret s')); crush.
  (* Crush get's 1 goal. *)
Admitted.


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

(* Try a context weakening. *)
Lemma A_1_Context_Weakening_1:
  forall (d d' : Delta) (tau : Tau) (k : Kappa),
    K d tau k ->
    K (d ++ d') tau k.
Proof.
  intros d d' tau k.
  intros Kder.
  induction Kder; crush.
  (* Crush get's zero, no wonder, no inductive hypothesis. *)
Admitted.

Lemma A_1_Context_Weakening_2:
  forall (u : Upsilon) (d : Delta) (tau : Tau) 
         (x : EVar) (p : P),
    getU u x p = Some tau ->
    WFU u ->
    K d tau A.
Proof.
  intros u d t x p getUder WFUder.
  (* Losing wfu nil. *)
  induction WFUder. 
  (* crush gets zero. *)
Admitted.

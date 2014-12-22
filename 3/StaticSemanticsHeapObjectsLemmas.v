(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

   Lemmas about static semantics of heap objects. 

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
Require Export TacticNotations.
Require Export GetLemmasRelation.

Lemma gettype_weakening:
  forall (u : Upsilon) (x : EVar) (tau' tau : Tau) (p : P),
    WFU u ->
    gettype u x [] tau' p tau ->
    forall (u' : Upsilon), 
      WFU (u ++ u') ->
      gettype (u ++ u') x [] tau' p tau.
Proof.
  intros u x tau' tau p WFUder gettypeder.
  gettype_ind_cases(induction gettypeder) Case.
  Case "gettype u x p tau [] tau".
   constructor.
  Case "gettype u x p (cross t0 t1) (i_pe zero_pe :: p') tau".
   intros.
   apply IHgettypeder with (u':=u') in WFUder.
   constructor.
   assumption.
   assumption.
  Case "gettype u x p (cross t0 t1) (i_pe one_pe :: p') tau".
   intros.
   apply IHgettypeder with (u':=u') in WFUder.
   constructor.
   assumption.
   assumption.
  Case "gettype u x p (etype aliases alpha k tau') (u_pe :: p') tau)".
   intros.
   apply IHgettypeder with (u':=u') in WFUder.
   apply gettype_etype with (tau'':= tau'').
   apply getU_Some_Weakening.
   assumption.
   assumption.
   assumption.
Qed.


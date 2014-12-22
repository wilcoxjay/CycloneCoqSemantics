(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

   Lemmas about static semantics kinding.

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
Require Export ContextExtensionRelation.
Require Export ContextExtensionLemmas.

Lemma K_weakening:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      WFD d ->
      K d tau k -> 
      forall (d' : Delta),
        WFD d' ->
        ExtendedByD d d' ->
        K d' tau k.
Proof.
 intros d tau k WFDder Kder.
 K_ind_cases (induction Kder) Case.
 
 Case "K d cint B".
  intros.
  constructor.
 Case "K d (tv_t alpha) B".
  intros.
  apply getD_extension_agreement with (d:= d) (d':=d') (alpha:= alpha) (k:= B) 
    in WFDder; 
    try assumption.
  apply K_B; try assumption.
 Case "K d (ptype (tv_t alpha)) B".
  intros.
  constructor.
  apply getD_extension_agreement with (d':= d') in H; try assumption.
 Case "K d tau A".
  intros.
  apply IHKder with (d':= d') in WFDder; try assumption.
  constructor; try assumption.
 Case "K d (cross t0 t1) A".
  intros.
  pose proof WFDder as WFDder2.
  apply IHKder1 with (d':= d') in WFDder; try assumption.
  apply IHKder2 with (d':= d') in WFDder2; try assumption.
  apply K_cross; try assumption.
 Case "K d (arrow t0 t1) A".
  intros.
  pose proof WFDder as WFDder2.
  apply IHKder1 with (d':= d') in WFDder; try assumption.
  apply IHKder2 with (d':= d') in WFDder2; try assumption.
  apply K_arrow; try assumption.
 Case "K d (ptype tau) B".
  intros.
  apply IHKder with (d':= d') in WFDder; try assumption.
  constructor.
  assumption.
 Case "K d (utype alpha k tau) A".
  intros.
  assert (Z: getD d' alpha = None).
  AdmitAlphaConversion.
  apply IHKder with (d':= ([(alpha, k)] ++ d')) in H; try assumption.
  apply K_utype; try assumption.
  constructor; try  assumption.
  constructor; try assumption.
  apply ExtendedByD_preserved_under_add_alpha_k; try assumption.
 Case "K d (etype p alpha k tau) A)".
  intros.
  assert (Z: getD d' alpha = None).
  AdmitAlphaConversion.
  apply IHKder with (d':= ([(alpha, k)] ++ d')) in H; try assumption.
  apply K_etype; try assumption.
  constructor; try  assumption.
  constructor; try assumption.
  apply ExtendedByD_preserved_under_add_alpha_k; try assumption.
Qed.

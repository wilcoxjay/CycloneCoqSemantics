(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Defining type safety, page 67.

*)

(* Done modulo alpha conversion. *)
Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.
Require Import Coq.Program.Equality.

Require Export FormalSyntax.
Require Export GetLemmasRelation.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export DynamicSemanticsTypeSubstitution.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemantics.
Require Export TypeSafety.
Require Export CpdtTactics.
Require Export Case.
Require Export TacticNotations.

Require Export GetLemmasRelation.
Require Export AlphaConversion.
Require Export VarLemmas.
Require Export PathLemmas.
Require Export ContextExtensionRelation.
Require Export StaticSemanticsKindingLemmas.

Lemma A_1_Context_Weakening_1:
  forall (d : Delta) (tau : Tau) (k : Kappa),
    WFD d -> 
    K d tau k ->
    forall (d' : Delta), 
      WFD (d ++ d') -> 
      K (d ++ d') tau k.
Proof.
  intros d tau k WFDder Kder.
  K_ind_cases (induction Kder) Case.
  Case "K d cint B".
   intros.
   constructor.
  Case "K d (tv_t alpha) B".
   intros.
   apply K_B.
   apply getD_Some_Weakening.
   assumption.
   assumption.
  Case "K d (ptype (tv_t alpha)) B".
   intros.
   constructor.
   apply getD_Some_Weakening.
   assumption.
   assumption.
  Case "K d tau A".
   intros.
   constructor.
   apply IHKder.
   assumption.
   assumption.
  Case "K d (cross t0 t1) A".
   intros.
   apply K_cross.
   apply IHKder1.
   assumption.
   assumption.
   apply IHKder2.
   assumption.
   assumption.
Case "K d (arrow t0 t1) A".
   intros.
   apply K_arrow.
   apply IHKder1.
   assumption.
   assumption.
   apply IHKder2.
   assumption.
   assumption.
  Case "K d (ptype tau) B".
   intros.
   apply K_ptype.
   apply IHKder.
   assumption.
   assumption.
  Case "K d (utype alpha k tau) A".
   intros.
   apply K_utype; try assumption. 
   constructor;  try assumption.
   AdmitAlphaConversion.
   AdmitAlphaConversion.
   apply IHKder with (d':= d') in H; try assumption.
   AdmitAlphaConversion.
  Case "K d (etype p alpha k tau) A)".
   intros.
   apply K_etype; try assumption. 
   constructor;  try assumption.
   AdmitAlphaConversion.
   AdmitAlphaConversion.
   apply IHKder with (d':= d') in H; try assumption.
   AdmitAlphaConversion.
Qed.

Lemma A_1_Context_Weakening_2:
  forall (u : Upsilon),
    WFU u ->
    forall (x : EVar) (p : P) (tau : Tau), 
    getU u x p tau ->
    forall (d : Delta),
      WFD d ->
      K d tau A.
Proof.
  intros u WFUder.
  induction WFUder.
 Case "WFU []".
   intros.
   inversion H.
 Case "WFU ([(x, p, tau)] ++ u)".
  intros.
  inversion H1.
  SCase "getU_top".
   assert (Y: ExtendedByD [] d).
   constructor.
   assert (Z: WFD []).
   constructor.
   rewrite <- H9.
   apply K_weakening with (d:= []) (d':= d) (tau:= tau) (k:= A) in Z; try assumption.
  SCase "getU_next".
   apply IHWFUder with (x:= x0) (p:= p0) (tau:= tau0) (d:= d)  in H11; 
    try assumption.
Qed.

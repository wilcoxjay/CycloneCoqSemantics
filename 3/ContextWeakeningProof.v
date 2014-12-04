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
   apply K_utype. 
   constructor.
   apply alpha_conversion_punt_getD with (k:=k).
   assumption.
   assumption.
   assumption.
   apply alpha_conversion_punt_getD with (k:=k).
   assumption.
   assumption.
   apply IHKder with (d':= d') in H. 
   assumption.
   constructor.
   apply alpha_conversion_punt_getD with (k:=k).
   assumption.
   assumption.
   assumption.

  Case "K d (etype p alpha k tau) A)".
   intros.
   apply K_etype.
   constructor.
   apply alpha_conversion_punt_getD with (k:=k).
   assumption.
   assumption.
   assumption.
   apply alpha_conversion_punt_getD with (k:=k).
   assumption.
   assumption.
   apply IHKder with (d':= d') in H. 
   assumption.
   constructor.
   apply alpha_conversion_punt_getD with (k:=k).
   assumption.
   assumption.
   assumption.
Qed.

Lemma get_lemma_extension_neq:
  forall (u : Upsilon) (x x' : nat) (p p': P) (t1 t2 t3: Tau),
    getU (u ++ [(((evar x'), p'), t1)]) (evar x) p t2 ->
    x <> x' -> 
    getU u (evar x) p t3.
Proof.
Admitted.

Lemma A_1_Context_Weakening_2:
  forall (u : Upsilon),
    WFU u ->
    forall (d : Delta) (x : EVar) (p : P) (tau : Tau), 
      getU u x p tau ->
      K d tau A.
Proof.
  intros u WFUder.
  WFU_ind_cases (induction WFUder) Case.
  Case "WFU []".
   intros.
   destruct x.
   inversion H.
  Case "WFU ([(x, p, tau)] ++ u)".
   intros.
   specialize (IHWFUder d x0 p0 tau0).
   apply IHWFUder.
   destruct x0.
   destruct x.
   assert (A: n <> n0 \/ n0 = n).
   omega.
   inversion A.
   apply get_lemma_extension_neq 
    with (x':=n0) (p:=p0) (p':=p) (t1:= tau) (t2:= tau0) (t3:=tau0).
   admit.
   assumption.
   admit.
Qed.

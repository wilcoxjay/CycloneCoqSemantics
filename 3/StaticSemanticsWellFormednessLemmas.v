(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

   Lemmas about static semantics context well formedness.

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
Require Export ContextExtensionRelation.

Require Export VarLemmas.
Require Export GetLemmasRelation.

Require Export AlphaConversion.

Lemma NotInDomU_strengthening:
  forall (u u' : Upsilon) (x : EVar) (p : P),
    WFU (u ++ u') ->
    NotInDomU (u ++ u') x p ->
    NotInDomU u x p.
Proof.
  intros u u' x p.
  induction u.
  Case "u = []".
   rewrite app_nil_l.
   intros.
   constructor.
  Case "a::u".
   intros.
   destruct a.
   destruct p0.
   case_eq (beq_evar x e); case_eq (beq_path p p0).
   intros.
   inversion H.
   apply IHu in H8.
   unfold NotInDomU.
   fold NotInDomU.
   rewrite H1.
   rewrite H2.
   simpl.
   tauto.
   apply beq_evar_eq in H2.
   admit.
   intros.
   admit.
   intros.
   admit.
   admit.
Admitted.  

Lemma WFU_strengthening:
 forall (u u' : Upsilon),
   WFU (u ++ u') ->
   WFU u.
Proof.
  intros.
  induction u.
  constructor.
  destruct a.
  destruct p.
  apply WFU_A.
  inversion H.
  apply NotInDomU_strengthening with (u':= u') (x:= e) (p:= p) in H5; try assumption.
  inversion H.
  apply IHu in H5.
  assumption.
  destruct t.
  Case "K [] (tv_t t) A".
   inversion H.
   assumption.
   constructor.
  Case "K [] cint B".
   apply K_int.
  Case "K [] (cross t1 t2) A".
   apply K_cross.
   inversion H.
   inversion H6.
   inversion H7.
   assumption.
   inversion H.
   inversion H6.
   inversion H7.
   assumption.
  Case "K [] (arrow t1 t2) A".
   apply K_arrow.
   inversion H.
   inversion H6.
   inversion H7.
   assumption.
   inversion H.
   inversion H6.
   inversion H7.
   assumption.
  Case "K [] (ptype t) A".
   constructor.
   apply K_ptype.
   inversion H.
   inversion H6.
   inversion H7.
   inversion H12.
   assumption.
  Case "K [] (utype t k t0) A".
   apply K_utype.
   rewrite app_nil_r.
   constructor.
   simpl.
   destruct t.
   reflexivity.
   constructor.
   simpl.
   destruct t.
   reflexivity.
   inversion H.
   inversion H6.
   inversion H7.
   assumption.
  Case "K [] (etype p0 t k t0) A".
   apply K_etype.
   rewrite app_nil_r.
   constructor.
   simpl.
   destruct t.
   reflexivity.
   constructor.
   simpl.
   destruct t.
   reflexivity.
   inversion H.
   inversion H6.
   inversion H7.
   assumption.
Qed.

Lemma WFDG_g_strengthening:
  forall (d : Delta) (g g' : Gamma),
    WFDG d (g ++ g') ->
    WFDG d g.
Proof.
  intros.
  induction g.
  Case "g = []".
   rewrite app_nil_l in H.
   constructor.
   inversion H.
   crush.
  Case "a :: g'". 
   constructor.
   apply getG_None_Strengthening with (g':=g').
   assumption.
   assumption.
   assumption.
  Case "(alpha,k) :: d0".
   constructor.
   assumption.
   destruct a.
   constructor.
   inversion H1.
   apply getG_None_Strengthening with (g':=g').   
   assumption.
   crush.
   AdmitAlphaConversion.
   admit. (* K? *)
   crush.
   inversion H.
   admit. (* TODO *)
   admit.
Qed.

Lemma WFD_strengthening:
 forall (d d' : Delta),
   WFD (d ++ d') ->
   WFD d.
Proof.
   intros.
   induction d.
  Case "d=[]".
   constructor.
  Case "a :: d'".
   inversion H.
   apply IHd in H3.
   constructor. 
   AdmitAlphaConversion.
   assumption.
Qed.

(* used. *)
Lemma WFDG_d_strengthening:
  forall (d d' : Delta) (g  : Gamma),
    WFDG (d ++ d') g ->
    WFDG d g.
Proof.
  intros d d' g WFDGder.
  induction WFDGder.
  Case "g = []".
   constructor.
  Case "[(x,tau] ++ g".
   constructor.
   AdmitAlphaConversion.
   admit. (* induction wrong, d0 instead of d. *)
   assumption.
   admit.
Qed.

Lemma WFDG_strengthening:
  forall (d d' : Delta) (g g' : Gamma),
    WFDG (d ++ d') (g ++ g') ->
    WFDG d g.
Proof.
  intros.
  apply WFDG_d_strengthening in H.
  apply WFDG_g_strengthening in H.
  assumption.
Qed.

(* Is this really true? *)
Lemma WFC_strengthening:
  forall (d d': Delta) (u u' : Upsilon) (g g': Gamma),
    WFC (d ++ d') (u ++ u') (g ++ g') ->
    WFC d u g.
Proof.
  intros d d' u u' g g' WFCder.
  apply (WFC_ind
           (fun (d : Delta) (u : Upsilon) (g : Gamma) =>
              WFC (d ++ d') (u ++ u') (g ++ g') ->
              WFC d u g)).
  intros.
  Case "WFC d0 u0 g0".
   constructor; try assumption.
  Case "WFC d u g".
   inversion WFCder.
   crush.
   apply WFD_strengthening in H; try assumption.
   apply WFU_strengthening in H1; try assumption.
   apply WFDG_strengthening in H0; try assumption.
   constructor; try assumption.
   assumption.
Qed.

(* This one might be true. *)
Lemma WFDG_g_weakening:
  forall (d : Delta) (g: Gamma),
    WFDG d g -> 
    forall (g' : Gamma),
      WFDG d g' -> 
      WFDG d (g ++ g').
Proof.
  intros d g WFDGder.
  induction g.
  Case "g = []".
   intros.
   rewrite app_nil_l.
   assumption.
  Case "a :: g".
   intros.
   SCase "((x, tau) :: g) ++ g'".
    destruct a.
    constructor; try assumption.
    AdmitAlphaConversion.
    admit. (* K again. *)
(* 
   SCase "[(alpha, k)] ++ d0".
    destruct a.
    apply WFDG_xt; try assumption.
    AdmitAlphaConversion.
    inversion H1.
    apply K_weakening with (d:= d0); try assumption.
    admit. (* Perhaps we need WFD in WFDG ? *)
    admit.
    admit. (* Simple lemma. *)
    admit.
    apply WFDG_alphak; try assumption.
    inversion WFDGder; try assumption.
    apply IHg in H10.
*)    
Admitted.
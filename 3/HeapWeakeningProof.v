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
Require Export TacticNotations.
Require Export TermWeakeningProof.

Require Export GetLemmasRelation.
Require Export StaticSemanticsLemmas.
Require Export StaticSemanticsHeapObjectsLemmas.

Lemma WFDG_nil_strengthening_right:
  forall (g g' : Gamma),
    WFDG [] (g ++ g') ->
    WFDG [] g'.
Proof.
  intros g g' WFDGder.
  induction g.
  Case "g = nil".
   rewrite app_nil_l in WFDGder.
   assumption.
  Case "u = a :: u".
   destruct a.   
   inversion WFDGder.
   apply IHg in H5.
   assumption.
Qed.

Lemma WFDG_nil_strengthening_left:
  forall (g g' : Gamma),
    WFDG [] (g ++ g') ->
    WFDG [] g.
Proof.
  intros g g' WFDGder.
  induction g.
  Case "g = nil".
   constructor.
  Case "g = a :: g".
   destruct a.
   inversion WFDGder.
   constructor.
   apply getG_None_Strengthening with (g':=g'); try assumption.
   apply IHg in H5.
   assumption.
   apply IHg in H5.
   assumption.
Qed.

Lemma WFU_strengthening_right:
  forall (u u' : Upsilon),
    WFU (u ++ u') ->
    WFU u'.
Proof.
  intros u u' WFUder.
  induction u.
  Case "u = nil".
   rewrite app_nil_l in WFUder.
   assumption.
  Case "u = a :: u".
   destruct a.   
   destruct p.
   inversion WFUder.
   apply IHu in H4.
   assumption.
Qed.

Lemma NotInDomU_strengthening:
  forall (u u' : Upsilon) (x : EVar) (p : P),
    NotInDomU (u ++ u') x p ->
    NotInDomU u x p.
Proof.
  intros u u' x p.
  induction u.
  Case "u = []".
   intros.
   constructor.
  Case "u = a :: u".
   intros.
   destruct a.
   destruct p0.
   rewrite <- app_comm_cons in H.
   unfold NotInDomU in H.
   fold NotInDomU in H.

   unfold NotInDomU.
   fold NotInDomU.
   case_eq (beq_evar x e && beq_path p p0)%bool.
   SCase "?".
    intros.
    rewrite H0 in H.
    assumption.
   SCase "?".
    intros.
    rewrite H0 in H.
    apply IHu in H.
    assumption.
Qed.

Lemma WFU_strengthening_left:
  forall (u u' : Upsilon),
    WFU (u ++ u') ->
    WFU u.
Proof.
  intros u u' WFUder.
  induction u.
  Case "u' = nil".
   constructor.
  Case "u = a :: u".
   destruct a.
   inversion WFUder.
   constructor.
   apply NotInDomU_strengthening in H2; try assumption.
   apply IHu in H3.
   assumption.
   assumption.
Qed.

Lemma WFC_nil_strengthening_left : 
  forall u u' g g', 
    WFC ([] ++ []) (u ++ u') (g ++ g') -> 
    WFC [] u g .
Proof.
  intros u u' g g' WFCder.
  inversion WFCder.
  constructor; try assumption.
  apply WFDG_nil_strengthening_left with (g':= g'); try assumption.
  apply WFU_strengthening_left with (u':= u'); try assumption.
Qed.

Lemma WFC_nil_strengthening_right: 
  forall u u' g g',
  WFC ([] ++ []) (u ++ u') (g ++ g') -> 
  WFC [] u' g'.
Proof.
  intros u u' g g' WFCder.
  inversion WFCder.
  constructor; try assumption.
  apply WFDG_nil_strengthening_right with (g:= g); try assumption.
  apply WFU_strengthening_right with (u:= u); try assumption.
Qed.

(* This works with WFC_strengthening because \Delta is nil and 
  WFC [] (u ++ u') (g ++ g') => u/u' g/g' disjoint! *)

Lemma A_3_Heap_Weakening_1_strengthen_quantification:
  forall (u u' : Upsilon) (g g': Gamma),
    WFC [] (u ++ u') (g ++ g') ->
    forall (h : H) (g'' : Gamma), 
      htyp u g h g'' ->
      htyp (u ++ u') (g ++ g') h g''.
Proof.
  intros u u' g g' WFCder h g'' htypder.
  htyp_ind_cases (induction htypder) Case.
  Case "htyp u g [] []".
   constructor.
  Case "htyp u g h ([(x, tau)] ++ g')".
   apply htyp_xv with (h':= h') (v:= v); try assumption.
   apply IHhtypder in WFCder; try assumption.
   apply A_2_Term_Weakening_3; try assumption.
   rewrite <- append_nil_noop with (l:= []) in WFCder.
   apply WFC_nil_strengthening_left in WFCder; try assumption.
   rewrite <- append_nil_noop with (l:= []) in WFCder.
   apply WFC_nil_strengthening_right in WFCder.
   try assumption.
Qed.

(* Correct. *)

Lemma A_3_Heap_Weakening_2:
  forall (u : Upsilon) (h : H),
    refp h u ->
    forall (h' : H),
      refp (h ++ h') u.
Proof.
  intros u h refpder.
  refp_ind_cases (induction refpder) Case.
  Case  "refp h []".
   intros.
   constructor.
  Case "refp h ([(x, p, tau')] ++ u)".
   intros.
   apply refp_pack 
   with (tau:= tau) (alpha:= alpha) (k:= k) (v:= v) (v':= v'); try assumption.
   apply getH_Some_weakening; try assumption.
   apply refp_weakening; try assumption.
Qed.

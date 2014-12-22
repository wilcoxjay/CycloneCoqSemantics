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

Lemma A_3_Heap_Weakening_1:
  forall (u u' : Upsilon) (g g' g'': Gamma) (h : H),
    WFC [] (u ++ u') (g ++ g') ->
    htyp u g h g'' ->
    htyp (u ++ u') (g ++ g') h g''.
Proof.
  intros u u' g g' g'' h WFCder htypder.
  htyp_ind_cases (induction htypder) Case.
  Case "htyp u g [] []".
   constructor.
  Case "htyp u g h ([(x, tau)] ++ g')".
   apply IHhtypder in WFCder; try assumption.
   apply htyp_xv with (h':= h') (v:= v); try assumption.
   apply rtyp_weakening.
   assumption.
Qed.

Lemma refp_weakening:
  forall (h : H) (u : Upsilon),
    refp h u ->
    forall (h' : H),
      refp (h ++ h') u.
Proof.
  
Admitted.


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
   apply getH_weakening; try assumption.
   apply refp_weakening; try assumption.
Qed.

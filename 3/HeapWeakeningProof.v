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

Lemma A_3_Heap_Weakening_1:
  forall (u u' : Upsilon) (g g' g'': Gamma) (h : H),
   (WFC [] (u ++ u') (g ++ g') /\ htyp u g h g'') ->
    htyp (u ++ u') (g ++ g') h g''.
Proof.
  intros u u' g g' g'' h.
  intros WFCder.
  induction WFCder.
  (* Collision. *)
  (* Crush get's 0. *)
Admitted.

Lemma A_3_Heap_Weakening_2:
  forall (u u' : Upsilon) (h h': H),
    refp h u ->
    refp (h ++ h') u.
Proof.
  intros u u' h h'.
  intros refpder.
  induction refpder.
  (* Crush gets 0. *)
  Focus 2.
Admitted.

(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  These are lemmas required to allow the weakening of various partial
  mapping and typing judgements.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Export FormalSyntax.
Require Export DynamicSemanticsHeapObjects.
Require Export StaticSemanticsTypingHeapObjects.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemantics.
Require Export TacticNotations.
Require Export VarLemmas.
Require Export ListLemmas.
Require Export GetLemmasRelation.


(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  This gives lemmas for gettype and the typing of states.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Export FormalSyntax.
Require Export TacticNotations.
Require Export CpdtTactics.
Require Export Case.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export VarLemmas.
Require Export ListLemmas.
Require Export GetLemmasRelation.


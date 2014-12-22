(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  This defines the notions of extending contexts. 

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
Require Export ContextExtension.
Require Export TestUtilities.

Example ExtendedByD_1:
  ExtendedByD [] [] = true.
Proof.
 reflexivity.
Qed.

Example ExtendedByD_2:
  ExtendedByD [(alpha,A)] [] = false.
Proof.
  reflexivity.
Qed.

Example ExtendedByD_3:
  ExtendedByD [(alpha,A)] [(alpha,B)] = false.
Proof.
  reflexivity.
Qed.

Example ExtendedByD_4:
  ExtendedByD [(alpha,A)] [(beta,A)] = false.
Proof.
  reflexivity.
Qed.

Example ExtendedByD_5:
  ExtendedByD [(alpha,A)] [(alpha,A)] = true.
Proof.
  reflexivity.
Qed.

Example ExtendedByD_6:
  ExtendedByD [(alpha,A); (beta,A)] [(beta,A); (alpha,A)] = true.
Proof.
  reflexivity.
Qed.

Example ExtendedByD_7:
  ExtendedByD [(alpha,A); (beta,A)] [(beta,A); (alpha,B)] = false.
Proof.
  reflexivity.
Qed.

Example ExtendedByD_8:
  ExtendedByD [(alpha,A); (beta,A)] [(alpha,A)] = false.
Proof.
  reflexivity.
Qed.


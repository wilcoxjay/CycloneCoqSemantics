(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This tests the static semantics of typing in the heap, pg 64.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Export FormalSyntax.
Require Export DynamicSemanticsTypeSubstitution.
Require Export Tacticals.
Require Export TestUtilities.

Example gettype_empty_test2:
  gettype [] x [] tau [] tau.
Proof.
  eauto 20 with Chapter3.
Qed.

Definition pnil : P := [].

Example getu_for_cint:
 getU ([((x, pnil), cint)] ++ []) x pnil cint.
Proof.
  eauto 20 with Chapter3.
Qed.

Example gettype_etype_test2:
  gettype [((x, pnil), cint)] x pnil (etype aliases alpha k cint) [u_pe] cint.
Proof.
  eauto 20 with Chapter3.
Qed.

Definition t0 := cint.
Definition t1 := cint.

Example gettype_left_test2:
  gettype [] x [] (cross t0 t1) [i_pe zero_pe] cint.
Proof.   
  constructor; eauto 20 with Chapter3.
Qed.

Example gettype_right_test2:
  gettype [] x [] (cross cint cint) [i_pe one_pe] cint.
Proof.
  eauto 20 with Chapter3.
Qed.

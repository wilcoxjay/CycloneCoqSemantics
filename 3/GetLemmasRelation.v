(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Useful lemmas about get functions. 

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Import FormalSyntax.
Require Import StaticSemanticsKindingAndContextWellFormedness.

Lemma getD_Some_Weakening:
 forall (alpha : TVar) (k : Kappa) (d d' : Delta),
   WFD (d ++ d') ->
   getD d alpha = Some k ->
   getD (d ++ d') alpha = Some k.
Proof.
  intros alpha k d d' WFDder getDder.
  functional induction (getD d alpha); crush.
  inversion WFDder.
  apply IHo in H3.
  assumption.
  assumption.
Qed.

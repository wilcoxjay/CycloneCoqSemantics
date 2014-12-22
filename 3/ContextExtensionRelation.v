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

Inductive ExtendedByD : Delta -> Delta -> Prop := 
  | ExtendedByD_nil   : forall (d' : Delta),
                          ExtendedByD [] d'
  | ExtendedByD_left  : 
      forall (alpha : TVar) (k : Kappa) (dtail : Delta) (d' : Delta),
        getD d' alpha = Some k ->
        ExtendedByD dtail d' ->
        ExtendedByD ((alpha,k) :: dtail) d'.


(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  The trivial subset of the language. 
*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import CpdtTactics.

Require Export FormalSyntax.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export DynamicSemanticsTypeSubstitution.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemantics.
Require Export TypeSafetyProof.
Require Export TypeSafety.

Fixpoint EmptySubsetTau (tau : Tau) :=
  match tau with
    | _ => False
  end.

Fixpoint EmptySubsetSt (s : St) :=
  match s with
    | _ => False
  end.

Fixpoint EmptySubsetE (e : E) :=
  match e with
    | _ => False
  end.

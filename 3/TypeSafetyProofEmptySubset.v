(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  The trivial subset of the language. 

 This is an attempt to see if I can work with these proofs.
 It is teaching me a few things but most of it is just rubbish. 

 Lessons: 

 So far it has shown me that I have to make gettype a relation again,
 as we induct on the structure of its derivation.

 Also it is checking for unused quantifiers.

 And it is teaching me how to do a proof by derivation of a relation.

 And it is teaching me how to set up a simultaneous instruction.

 And it is showing me how to do a proof by inspection and the form of values.

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

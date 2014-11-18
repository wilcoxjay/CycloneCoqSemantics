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

(* The smallest trivial subset that I can think of, integer with 
 the return statement. *)
(* This may not really work without subsetting I also.
   These have to be mutually recursive. *)

Fixpoint IntSubsetTau (tau : Tau) :=
  match tau with
    | cint => True
    | _ => False
  end.
Fixpoint IntSubsetI    (i : I)        := True.
Fixpoint IntSubsetEVar (x : EVar)     := False.
Fixpoint IntSubsetTVar (alpha : TVar) := False.

Fixpoint IntSubsetF (f : E) := False.

Fixpoint IntSubsetE (e : E) :=
  match e with 
    | i_e i => IntSubsetI i
    | _ => False
  end.

Fixpoint IntSubsetSt (s : St) :=
  match s with
    | (retn e) => IntSubsetE e
    | (e_s e) => IntSubsetE e
    | _ => False
  end.


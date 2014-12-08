(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Punting alpha conversion. 

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.
Require Import Coq.Program.Equality.

Require Export FormalSyntax.
Require Export GetLemmasRelation.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export DynamicSemanticsTypeSubstitution.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemantics.
Require Export TypeSafety.
Require Export CpdtTactics.
Require Export Case.
Require Export TacticNotations.
Require Export GetLemmasRelation.


(* This is the strongest minimal use of alpha conversion that I can find
  so far. This lemma just punts it for the moment.  Although I have
  been alpha conversioning commenting every use. 
*)

Lemma alpha_conversion_punt_getD:
  forall (alpha : TVar) (k : Kappa) (d d' : Delta),
    WFD ([(alpha, k)] ++ d) ->
    WFD (d ++ d') -> 
    getD (d ++ d') alpha = None.
Proof.
Admitted.


(* This is a form of alpha conversion for Context Weakening. *)
Lemma get_lemma_extension_neq:
  forall (u : Upsilon) (x x' : nat) (p p': P) (t1 t2 t3: Tau),
    getU (u ++ [(((evar x'), p'), t1)]) (evar x) p t2 ->
    x <> x' -> 
    getU u (evar x) p t3.
Proof.
Admitted.



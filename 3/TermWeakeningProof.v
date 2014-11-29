(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Defining type safety, page 67.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.

Require Export FormalSyntax.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export DynamicSemanticsTypeSubstitution.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemantics.
Require Export TypeSafety.
Require Export CpdtTactics.

Lemma A_2_Term_Weakening_1 :
  forall (d: Delta) (u u' : Upsilon) (g g' : Gamma)
         (x : EVar) (p p' : P) (tau tau' : Tau),
    WFC d (u ++ u') (g ++ g') ->
    gettype u x p tau p' = Some tau' ->
    gettype (u ++ u') x p tau p' = Some tau'.
Proof.
  intros d u u' g g' x p p' tau tau'.
  intros WFCd.
  intros gettypederivation.
  functional induction (gettype u x p tau p'); crush.
  (* Warning: Collision between bound varibles of name x *)
  (* Crush gets 25/26 *)
  
Admitted.

Lemma A_2_Term_Weakening_2_3_4 :
  forall (d: Delta) (u u' : Upsilon) (g g' : Gamma)
         (e : E) (tau : Tau),
    WFC d (u ++ u') (g ++ g') ->
    ltyp d u g e tau ->
    ltyp d (u ++ u') (g++g') e tau.
Proof.
  intros d u u' g g' e tau WFC.
  apply (typ_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) =>
              styp d u g t s -> 
              ltyp d (u ++ u') (g++g') e tau)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (lt : ltyp d u g e t) =>
              ltyp d u g e t -> 
              ltyp d (u ++ u') (g++g') e tau)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              rtyp d u g e t ->
              ltyp d (u ++ u') (g++g') e tau)); crush.
  (* Crush get's 3/26 *)
Admitted.

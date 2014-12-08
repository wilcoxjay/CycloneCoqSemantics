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

Lemma A_14_Term_Progress_1:
  forall (g : Gamma) (u : Upsilon) (h : H) (e : E) (tau : Tau),
    htyp u g h g -> 
    refp h u ->
    ltyp [] u g e tau -> 
    (exists (x : EVar) (p : P), e = (p_e x p)) \/ 
    (exists (h' : H) (e' : E),  L h (e_s e) h' (e_s e')).
Proof.
  intros g u h e tau.
  intros htypder refpder.
  apply (typ_ind_mutual 
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              styp d u g t s ->
              (exists (x : EVar) (p : P), e = (p_e x p)) \/ 
              (exists (h' : H) (e' : E),  L h (e_s e) h' (e_s e')))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
                (lt : ltyp d u g  e tau') =>
              ltyp d u g  e tau' ->
              (exists (x : EVar) (p : P), e = (p_e x p)) \/ 
              (exists (h' : H) (e' : E),  L h (e_s e) h' (e_s e')))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              rtyp d u g e t -> 
              (exists (x : EVar) (p : P), e = (p_e x p)) \/ 
              (exists (h' : H) (e' : E),  L h (e_s e) h' (e_s e')))).
  (* crush goes up many goals here. *)
  Focus 3.
  

Admitted.

Lemma A_14_Term_Progress_2:
  forall (g : Gamma) (u : Upsilon) (h : H) (e : E) (tau : Tau),
    htyp u g h g -> 
    refp h u ->
    rtyp [] u g e tau -> 
    (Value e \/
     exists (h' : H) (e' : E),  R h (e_s e) h' (e_s e')).
Proof.
  intros g u h e tau.
  intros htypder refpder.
  apply (typ_ind_mutual 
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              styp d u g t s ->
              (Value e \/
               exists (h' : H) (e' : E),  S h (e_s e) h' (e_s e')))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
                (lt : ltyp d u g  e tau') =>
              ltyp d u g  e tau' ->
              (Value e \/
               exists (h' : H) (e' : E),  L h (e_s e) h' (e_s e')))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              rtyp d u g e t ->
              (Value e \/
               exists (h' : H) (e' : E),  R h (e_s e) h' (e_s e')))).
  
Admitted.

(* TODO can't get this formulated right due to the statement that only
    appears in s types.
   I'm just not sure that I'm proving the inductive hypotheses right
   in the L/R cases by weakening them. 
 Dan? *)

Lemma A_14_Term_Progress_3:
  forall (g : Gamma) (u : Upsilon) (h : H) (s : St) (tau : Tau),
    htyp u g h g ->
    refp h u ->
    styp [] u g tau s -> 
     (exists (v : E), Value v /\ (s = (e_s v) \/ s = retn v)) \/
     (exists (h' : H) (s' : St), S h s h' s').
Proof.
  intros g u h e tau.
  intros htypder refpder.
  apply (typ_ind_mutual 
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              styp d u g t s ->
              (exists (v : E), Value v /\ (s = (e_s v) \/ s = retn v)) \/
              (exists (h' : H) (s' : St), S h s h' s'))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
                (lt : ltyp d u g  e tau') =>
              ltyp d u g  e tau' ->
              (exists (h' : H) (s' : St), L h (e_s e) h' s'))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              rtyp d u g e t ->
              (exists (h' : H) (s' : St), R h (e_s e) h' s'))).
  (* crush goes up many goals here. *)
Admitted.

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
  
Inductive extends_Gamma : Gamma -> Gamma -> Prop := 
  | A_12_Extension_Gamma : 
      forall (g1 g2 : Gamma),
        (exists (g3 : Gamma), g2 = g1 ++ g3) ->
        extends_Gamma g2 g1.

Inductive extends_Upsilon : Upsilon -> Upsilon -> Prop := 
  | A_12_Extension_Upsilon : 
      forall (u1 u2 : Upsilon),
        (exists (g3 : Upsilon), u2 = u1 ++ g3) ->
        extends_Upsilon u2 u1.

Lemma A_13_Term_Preservation_1:
  forall (u : Upsilon) (g : Gamma) 
         (e e' : E) (tau : Tau) (h h' : H),
    htyp u g h g ->
    refp h u -> 
    ltyp [] u g e tau -> 
    L h (e_s e)  h' (e_s e') ->
     exists (g' : Gamma) (u' : Upsilon),
       (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
       htyp u' g' h' g' /\
       refp h' u' /\
       ltyp [] u' g' e' tau.
Proof.
  intros u g e e' tau h h'.
  intros htypder refpder ltypder.
  (* TODO am I proving the right theorem? e_s e not here. *)
  apply (SLR_ind_mutual
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (rstep: R h s h' s') =>
              exists (g' : Gamma) (u' : Upsilon),
                (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                htyp u' g' h' g' /\
                refp h' u' /\
                ltyp [] u' g' e' tau)
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (sstep: S h s h' s') =>
              exists (g' : Gamma) (u' : Upsilon),
                (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                htyp u' g' h' g' /\
                refp h' u' /\
                ltyp [] u' g' e' tau)
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (lstep: L h s h' s') =>
              exists (g' : Gamma) (u' : Upsilon),
                (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                htyp u' g' h' g' /\
                refp h' u' /\
                ltyp [] u' g' e' tau)); crush.
  (* crush gives 19/41. *)
Admitted.

Lemma A_13_Term_Preservation_2:
  forall (u : Upsilon) (g : Gamma) (e e' : E) (tau : Tau) (h h' : H),
    htyp u g h g ->
    refp h u -> 
    rtyp [] u g e tau ->
    R h (e_s e)  h' (e_s e') ->
    exists (g' : Gamma) (u' : Upsilon),
      (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
      htyp u' g' h' g' /\ 
      refp h' u' /\
      rtyp [] u' g' e' tau.
Proof.
  intros u g e e' tau h h'.
  intros htypder refpder ltypder.
  apply (SLR_ind_mutual
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (rstep: R h s h' s') =>
              exists (g' : Gamma) (u' : Upsilon),
                (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                htyp u' g' h' g' /\
                refp h' u' /\
                rtyp [] u' g' e' tau)
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (sstep: S h s h' s') =>
              exists (g' : Gamma) (u' : Upsilon),
                (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                htyp u' g' h' g' /\
                refp h' u' /\
                rtyp [] u' g' e' tau)
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (lstep: L h s h' s') =>
              exists (g' : Gamma) (u' : Upsilon),
                (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                htyp u' g' h' g' /\
                refp h' u' /\
                rtyp [] u' g' e' tau)); crush.
  (* crush gets 19/41. *)
Admitted.

Lemma A_13_Term_Preservation_3:
  forall (u : Upsilon) (g : Gamma) (s s': St) (tau : Tau) (h h' : H),
    htyp u g h g ->
    refp h u -> 
    styp [] u g tau s -> 
    S h s  h' s' ->
    exists (g' : Gamma) (u' : Upsilon),
      (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
      htyp u' g' h' g' /\ 
      refp h' u' /\
      styp [] u' g' tau s'.
Proof.
  intros u g e e' tau h h'.
  intros htypder refpder ltypder.
  apply (SLR_ind_mutual
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (rstep: R h s h' s') =>
              exists (g' : Gamma) (u' : Upsilon),
                (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                htyp u' g' h' g' /\
                refp h' u' /\
                styp [] u' g' tau e')
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (sstep: S h s h' s') =>
              exists (g' : Gamma) (u' : Upsilon),
                (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                htyp u' g' h' g' /\
                refp h' u' /\
                styp [] u' g' tau e')
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (lstep: L h s h' s') =>
              exists (g' : Gamma) (u' : Upsilon),
                (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                htyp u' g' h' g' /\
                refp h' u' /\
                styp [] u' g' tau e')); crush.
  (* crush gives 19/41. *)
Admitted.

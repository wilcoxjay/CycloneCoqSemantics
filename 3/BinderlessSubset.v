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
Require Export TypeSafety.

Fixpoint BinderlessSubsetTau (tau : Tau) :=
  match tau with
    | cint => True
    | cross t0 t1 => 
      BinderlessSubsetTau t0  /\
       BinderlessSubsetTau t1
    | ptype t => BinderlessSubsetTau t
    | _ => False
  end.

Fixpoint BinderlessSubsetI    (i : I)        := True.
Fixpoint BinderlessSubsetEVar (x : EVar)     := False.
Fixpoint BinderlessSubsetTVar (alpha : TVar) := False.

Fixpoint BinderlessSubsetF (f : E) := False.

Fixpoint BinderlessSubsetE (e : E) :=
  match e with 
    | p_e _ _ => False
    | call _ => False
    | inst _ _ => False 
    | pack _ _ _ => False
    | _ => True
  end.

Fixpoint BinderlessSubsetSt (s : St) :=
  match s with
    | (retn e) => BinderlessSubsetE e
    | (e_s e) => BinderlessSubsetE e
    | (seq s1 s2) => BinderlessSubsetSt s1 /\ BinderlessSubsetSt s2
    | (if_s e s1 s2) => 
      BinderlessSubsetE e /\ BinderlessSubsetSt s1 /\ BinderlessSubsetSt s2
    | (while e s) =>
      BinderlessSubsetE e /\ BinderlessSubsetSt s
    | _ => False
  end.

Theorem Type_Safety :
(*   If ·; ·; ·; τ styp s, ret s, and ·; s → H ; s *)
 forall (s : St) (tau : Tau),
   styp [] [] [] tau s ->
   BinderlessSubsetSt s ->
   BinderlessSubsetTau tau ->
   ret s ->
   exists (h' : H) (s' : St), 
     Sstar [] s h' s' -> 
     NotStuck h' s'.
Proof.
 Definition Thm (s : St) (tau : Tau) : Prop := 
   (
   BinderlessSubsetSt s ->
   BinderlessSubsetTau tau ->
   ret s ->
     exists (h' : H) (s' : St), 
       Sstar [] s h' s' -> 
       NotStuck h' s').
  intros s tau.
  apply (Term_ind_mutual
           (fun (s : St) =>  
              forall (tau : Tau) (ts : (styp [] [] [] tau s)), 
                Thm s tau)
           (fun (e : E ) =>
              forall (tau : Tau) (ts : (styp [] [] [] tau (e_s e))),
                Thm (e_s e) tau)
           (fun (f : F) =>
              forall (ts : (styp [] [] [] tau (e_s (f_e f)))),
                Thm (e_s (f_e f)) tau));
    repeat (unfold Thm; crush).
   (* Crush 8/22. *)
Admitted.

Lemma A_8_Return_Preservation:
  forall (s s' : St) (h h' : H),
  ret s ->
  S h s h' s' ->
  BinderlessSubsetSt s ->
  ret s'.
Proof.
  intros s s' h h' retder.
  apply (SLR_ind_mutual 
           (fun (h : H) (s : St) (h' : H) (s' : St) (rstep: R h s h' s') =>
              BinderlessSubsetSt s ->
              ret s')
           (fun (h : H) (s : St) (h' : H) (s' : St) (sstep: S h s h' s') =>
              BinderlessSubsetSt s ->
              ret s')
           (fun (h : H) (s : St) (h' : H) (s' : St) (lstep: L h s h' s') =>
              BinderlessSubsetSt s ->
              ret s')); crush.
  (* Crush gets 13/41 *)
Admitted.

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
    BinderlessSubsetTau tau ->
    BinderlessSubsetE e ->
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
              BinderlessSubsetTau tau ->
              BinderlessSubsetE e ->
              exists (g' : Gamma) (u' : Upsilon),
                (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                htyp u' g' h' g' /\
                refp h' u' /\
                ltyp [] u' g' e' tau)
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (sstep: S h s h' s') =>
              BinderlessSubsetTau tau ->
              BinderlessSubsetE e ->
              exists (g' : Gamma) (u' : Upsilon),
                (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                htyp u' g' h' g' /\
                refp h' u' /\
                ltyp [] u' g' e' tau)
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (lstep: L h s h' s') =>
              BinderlessSubsetTau tau ->
              BinderlessSubsetE e ->
              exists (g' : Gamma) (u' : Upsilon),
                (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                htyp u' g' h' g' /\
                refp h' u' /\
                ltyp [] u' g' e' tau)); crush.
  (* crush gives 19/41, same without filter *)
Admitted.


Lemma A_2_Term_Weakening_1 :
  forall (d: Delta) (u u' : Upsilon) (g g' : Gamma)
         (x : EVar) (p p' : P) (tau tau' : Tau),
    WFC d (u ++ u') (g ++ g') ->
    BinderlessSubsetTau tau ->
    BinderlessSubsetTau tau' ->
    gettype u x p tau p' = Some tau' ->
    gettype (u ++ u') x p tau p' = Some tau'.
Proof.
  intros d u u' g g' x p p' tau tau'.
  intros WFCd.
  intros gettypederivation.
  functional induction (gettype u x p tau p'); crush.
  (* Warning: Collision between bound varibles of name x *)
  (* Crush gets 25/26 same *)
Admitted.

Lemma A_2_Term_Weakening_2_3_4 :
  forall (d: Delta) (u u' : Upsilon) (g g' : Gamma)
         (e : E) (tau : Tau),
    WFC d (u ++ u') (g ++ g') ->
    ltyp d u g e tau ->
    BinderlessSubsetE e ->
    BinderlessSubsetTau tau ->
    ltyp d (u ++ u') (g++g') e tau.
Proof.
  intros d u u' g g' e tau WFC.
  apply (typ_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) =>
              BinderlessSubsetSt s ->
              BinderlessSubsetTau tau ->
              ltyp d (u ++ u') (g++g') e tau)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (lt : ltyp d u g e t) =>
              BinderlessSubsetE e ->
              BinderlessSubsetTau tau ->
              ltyp d (u ++ u') (g++g') e tau)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              BinderlessSubsetE e ->
              BinderlessSubsetTau tau ->
              ltyp d (u ++ u') (g++g') e tau)).
  (* Crush gets 11/26. *)
Admitted.

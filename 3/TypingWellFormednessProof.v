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
Require Export Case.
Require Export ContextWeakeningProof.
Require Export SubstitutionsProof.

Lemma A_7_Typing_Well_Formedness_1 :
  forall (d: Delta) (u : Upsilon) (x : EVar) (tau tau' : Tau) (p p' : P),
    WFU u ->
    K d tau A ->
    gettype u x p tau p' = Some tau' ->
    K d tau' A.
Proof.
  intros d u x tau tau' p p'.
  intros WFUder Kder.
  functional induction (gettype u x p tau p'); crush.   (* Wow, crush gets 23/26. *)
  inversion Kder.
  inversion H.
  crush.
  inversion Kder.
  inversion H.
  crush.
  inversion Kder.
  inversion H.
  crush' true fail.
  crush' [A_1_Context_Weakening_2] [e4].
  crush' [A_6_Substitution_1]  [e4].
  (* Down to one goal. *)
  (* Context weakening lemma 2 or substitution lemma 1. *)
  inversion Kder.
  Focus 2.
  crush.
  inversion e4.
  crush' [A_1_Context_Weakening_2] fail.
  crush' [A_6_Substitution_1]      fail.

Admitted.

Lemma A_7_Typing_Well_Formedness_2 :
  forall (d: Delta) (g : Gamma) (u : Upsilon) (tau : Tau) (e : E),
  ltyp d u g e tau ->
  (WFC d u g /\ 
   K d tau A).
Proof.
  intros d g u tau e.
  apply (typ_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              (WFC d u g /\  K d tau A))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
                (lt : ltyp d u g  e tau') =>
              (WFC d u g /\  K d tau A))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              (WFC d u g /\  K d tau A))); crush.
  (* Crush gets 21/26 subgoals. *)
(*

  Focus 4.
  destruct r.
  inversion H0.
  crush.

  Focus 1.
  inversion w.
  inversion H.
  crush.

  Focus 2.
  crush.

  Focus 1.
  apply A_7_Typing_Well_Formedness_1
        with (u:= u0) (x:=x) (tau:=tau') (p:=[]) (p':= p).
  inversion w.
  assumption.
  assumption.

  Focus 2.
  apply A_7_Typing_Well_Formedness_1
        with (u:= u0) (x:=x) (tau:=tau') (p:=[]) (p':= p).
  inversion w.
  assumption.
  assumption.

  constructor.
  Focus 2.
  assumption.

  (* goal: WFDG d0 g0 and H WFDG d0 (g0 + ...). So why an't I get wfdg d0 g0? *)
*)  

Admitted.

Lemma A_7_Typing_Well_Formedness_3 :
  forall (d: Delta) (g : Gamma) (u : Upsilon) (tau : Tau) (e : E),
    rtyp d u g e tau ->
    (WFC d u g /\ 
     K d tau A).
Proof.
  intros d g u tau e.
  apply (typ_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              (WFC d u g /\  K d tau A))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
                (lt : ltyp d u g  e tau') =>
              (WFC d u g /\  K d tau A))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              (WFC d u g /\  K d tau A))); crush.
  (* Wow crush gets 21/26. *)
Admitted.

Lemma A_7_Typing_Well_Formedness_4 :
  forall (d: Delta) (g : Gamma) (u : Upsilon) (tau : Tau) (s : St),
    styp d u g tau s ->
    WFC d u g.
Proof.
  intros d g u tau e.
  apply (typ_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              (WFC d u g /\  K d tau A))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
                (lt : ltyp d u g  e tau') =>
              (WFC d u g /\  K d tau A))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              (WFC d u g /\  K d tau A))).
  (* crush gets 21/26. *)
  (* Am I losing information in these cases with Crush? *)
  crush.
  crush.
  crush.
  crush.
  crush.
  crush.
  crush.
  crush.
  Focus 2.
  crush.
  Focus 2.
  crush.
  Focus 3.
  
Admitted.

Lemma A_7_Typing_Well_Formedness_5 :
  forall (d: Delta) (g : Gamma) (u : Upsilon) (tau : Tau) (s : St),
    styp d u g tau s ->
    ret s ->
    K d tau A.
Proof.
  intros d g u tau e.
  apply (typ_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
                  ret s ->
                  K d tau A)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
                (lt : ltyp d u g  e tau') =>
                  K d tau A)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
                  K d tau A)); crush.
  (* Crush gets 21/16 goals. *)
Admitted.

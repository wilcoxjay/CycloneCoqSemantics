(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Useful lemmas about get functions. 

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Import FormalSyntax.
Require Import StaticSemanticsKindingAndContextWellFormedness.


Inductive getU' : Upsilon -> EVar -> P -> Tau -> Prop :=
  | getU_top  : forall (u : Upsilon) (x : EVar) (p : P) (tau : Tau),
                 getU' (cons ((x,p),tau) u) x p tau
  | getU_next : forall (u : Upsilon) (x y: EVar) (p p': P) (tau tau': Tau),
                 x <> y \/ p <> p'->
                 getU' u x p tau -> 
                 getU' (cons ((y,p'),tau') u) x p tau.

Lemma getU_nil_none:
  forall  (x : EVar) (p : P) (tau : Tau),
     ~(getU' [] x p tau).
Proof.
  intros x p tau.
  compute.
  intros.
  inversion H.
Qed.

(* TODO jrw these properties don't hold on nil. *)
Lemma getU'_weakening :
  forall (u : Upsilon) (x x': EVar) (p p': P) (tau tau': Tau),
    getU' (u ++ [((x', p'),tau')]) x p tau ->
    x <> x' ->
    p <> p' ->
    getU' u x p tau.
Proof.
  intros.
  induction u.
  Case "u = []".
   assert (A: ~ getU' [] x p tau).
   apply getU_nil_none.
   compute in A.
   admit. (* How do I show this contradiction? *)
  Case "u = a :: u".
   destruct a.
   destruct p0.
   eapply getU_next.
Admitted.  

Lemma getU_partial_function:
  forall (u : Upsilon) (x : EVar) (p : P) (tau : Tau),
    WFU u ->
    getU' u x p tau ->
    forall (tau' : Tau),
      getU' u x p tau' ->
      tau = tau'.
Proof.
  intros.
  induction u.
  inversion H0.
  destruct a.
  inversion H0.
  inversion H1.
  crush.
  admit.
  admit.
Qed.

Lemma getU_function_inversion:
  forall (u : Upsilon),
    WFU u ->
    forall  (x : EVar) (p : P) (tau : Tau),
      getU' u x p tau ->
      forall (tau' : Tau),
        (getU' u x p tau' /\ tau = tau').
Proof.
  intros u WFUder.
  induction (rev u).
  intros.
  split.
  inversion H.
  inversion H.
  intros.
  inversion WFUder.
  crush.

Qed.

(* TODO not strictly true as d is a list. *)
Lemma getD_weakening_some_left:
  forall (d : Delta) (alpha : TVar) (k : Kappa),
    WFD d ->
     getD d         alpha   = Some k ->
    forall (d' : Delta),
      WFD (d ++ d') -> 
      getD (d ++ d') alpha   = Some k.
Proof.
Admitted.  

Lemma getD_weakening_some_right:
  forall (d : Delta) (alpha : TVar) (k : Kappa),
    WFD d ->
    getD d         alpha   = None ->
    forall (d' : Delta),
      WFD (d ++ d') ->
      getD d'        alpha   = Some k ->
      getD (d ++ d') alpha   = Some k.
Proof.
Admitted. 


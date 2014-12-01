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

Lemma getU_nil_none:
  forall  (x : EVar) (p : P),
    getU [] x p = None.
Proof.
  intros x p.
  compute.
  destruct x.
  reflexivity.
Qed.

Lemma getU_weakening :
  forall (u : Upsilon) (x x': EVar) (p p': P) (tau tau': Tau),
    getU (u ++ [(p_e x' p',tau')]) x p = Some tau ->
    x <> x' ->
    p <> p' ->
    getU u x p = Some tau.
Proof.
Admitted.  

Lemma getU_function:
  forall (u : Upsilon) (x : EVar) (p : P) (tau : Tau),
    getU u x p = Some tau ->
    forall (tau' : Tau),
      getU u x p = Some tau' ->
      tau = tau'.
Proof.
  intros.
  rewrite H in H0.
  inversion H0.
  reflexivity.
Qed.

(* Known true but Coq is not generating functional inversion. *)
Lemma getU_function_inversion:
  forall (u : Upsilon) (x : EVar) (p : P) (tau : Tau),
    getU u x p = Some tau ->
    forall (tau' : Tau),
      (getU u x p = Some tau' /\ tau = tau').
Proof.
  intros.
  split.
  functional induction (getU u x p); crush.
  admit.
  admit.
Admitted.

(* TODO not strictly true as d is a list. *)
Lemma getD_weakening_some_left:
(*  WFD d ->
    WFD d ++ d' -> 
*)
  forall (d : Delta) (alpha : TVar) (k : Kappa),
    getD d         alpha   = Some k ->
    forall (d' : Delta),
      getD (d ++ d') alpha   = Some k.
Proof.
Admitted.  

Lemma getD_weakening_some_right:
  forall (d : Delta) (alpha : TVar) (k : Kappa),
    getD d         alpha   = None ->
    forall (d' : Delta),
      getD d'        alpha   = Some k ->
      getD (d ++ d') alpha   = Some k.
Proof.
Admitted. 


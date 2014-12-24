(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Some useful lemmas about Vars.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Export CpdtTactics.
Require Export Case.
Require Export FormalSyntax.

Lemma beq_kappa_reflexive:
  forall (k : Kappa),
    beq_kappa k k = true.
Proof.
  destruct k.
  reflexivity.
  reflexivity.
Qed.

Lemma beq_kappa_eq:
  forall (k k': Kappa),
    beq_kappa k k' = true ->
    k = k'.
Proof.
  intros.
  destruct k; destruct k'.
  reflexivity.
  inversion H.
  inversion H.
  reflexivity.
Qed.

Lemma beq_kappa_neq:
  forall (k k': Kappa),
    beq_kappa k k' = false ->
    k <> k'.
Proof.
  intros.
  destruct k; destruct k'.
  inversion H.
  discriminate.
  discriminate.
  inversion H.
Qed.

Lemma beq_tvar_reflexive:
 forall (alpha : TVar),
   beq_tvar alpha alpha = true.
Proof.
  intros.
  destruct alpha.
  unfold beq_tvar.
  apply eq_sym.
  apply beq_nat_refl.
Qed.

Lemma beq_tvar_symmetric:
  forall (alpha beta : TVar),
    beq_tvar alpha beta = beq_tvar beta alpha.
Proof.
  intros alpha beta.
  case_eq (beq_tvar alpha beta); case_eq (beq_tvar beta alpha); intros; try reflexivity; destruct alpha; destruct beta; unfold beq_tvar in H; unfold beq_tvar in H0.
  symmetry in H0.
  apply beq_nat_eq in H0.
  apply beq_nat_false in H.
  congruence.
  symmetry in H.
  apply beq_nat_eq in H.
  apply beq_nat_false in H0.
  congruence.
Qed.

Lemma beq_tvar_eq:
  forall (alpha beta : TVar),
    beq_tvar alpha beta = true ->
    alpha = beta.
Proof.
  intros.
  case_eq (beq_tvar alpha beta).
  intros.
  destruct alpha; destruct beta.
  unfold beq_tvar in H.
  unfold beq_tvar in H0.
  symmetry in H.
  apply beq_nat_eq in H.
  rewrite H.
  reflexivity.
  intros.
  rewrite H in H0.
  inversion H0.
Qed.

Lemma beq_tvar_neq:
  forall (alpha beta : TVar),
    beq_tvar alpha beta = false ->
    alpha <> beta.
Proof.
  intros.
  case_eq (beq_tvar alpha beta).
  intros.
  destruct alpha; destruct beta.
  unfold beq_tvar in H.
  unfold beq_tvar in H0.
  apply beq_nat_false in H.
  congruence.
  intros.
  destruct alpha; destruct beta.  
  unfold beq_tvar in H.
  fold beq_tvar in H.
  apply beq_nat_false in H.
  congruence.
Qed.  

Lemma beq_evar_reflexive:
 forall (x : EVar),
   beq_evar x x = true.
Proof.
  intros.
  destruct x.
  unfold beq_evar.
  apply eq_sym.
  apply beq_nat_refl.
Qed.

Lemma beq_evar_symmetric:
  forall (x y : EVar),
    beq_evar x y = beq_evar y x.
Proof.
  intros x y.
  case_eq (beq_evar x y); case_eq (beq_evar y x); intros; try reflexivity; destruct x; destruct y; unfold beq_evar in H; unfold beq_evar in H0.
  symmetry in H0.
  apply beq_nat_eq in H0.
  apply beq_nat_false in H.
  congruence.
  symmetry in H.
  apply beq_nat_eq in H.
  apply beq_nat_false in H0.
  congruence.
Qed.

Lemma beq_evar_eq:
  forall (x y : EVar),
    beq_evar x y = true ->
    x = y.
Proof.
  intros.
  case_eq (beq_evar x y).
  intros.
  destruct x; destruct y.
  unfold beq_evar in H.
  unfold beq_evar in H0.
  symmetry in H.
  apply beq_nat_eq in H.
  rewrite H.
  reflexivity.
  intros.
  rewrite H in H0.
  inversion H0.
Qed.

Lemma beq_evar_neq:
  forall (x y : EVar),
    beq_evar x y = false ->
    x <> y.
Proof.
  intros.
  case_eq (beq_evar x y).
  intros.
  destruct x; destruct y.
  unfold beq_evar in H.
  unfold beq_evar in H0.
  apply beq_nat_false in H.
  congruence.
  intros.
  destruct x; destruct y.  
  unfold beq_evar in H.
  fold beq_evar in H.
  apply beq_nat_false in H.
  congruence.
Qed.  


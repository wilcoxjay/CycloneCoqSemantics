(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Some useful lemmas about Paths.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Export CpdtTactics.
Require Export Case.
Require Export FormalSyntax.

(* TODO finish proofs. *)

Lemma beq_path_symmetric:
  forall (p p' : P),
    beq_path p p' = beq_path p' p.
Proof.
  induction p; induction p'.
  Case "[],[]".
   reflexivity.
  Case "[], a :: p'".
   compute.
   destruct a; try destruct i; try reflexivity. 
  Case "a :: p, []".
   compute.
   destruct a; try destruct i; try reflexivity. 
  Case "a ::p, a0 :: p'".
  (* Cute reasoning by cases. *)
   destruct a; try destruct i; destruct a0; try destruct i0; unfold beq_path;
   fold   beq_path; try destruct i; try reflexivity.
   destruct p'.
   admit.
   admit.
   admit.
   admit.
Qed.   

Lemma beq_path_eq:
  forall (p p' : P),
    beq_path p p' = true ->
    p = p'.
Proof.
  intros.
  case_eq (beq_path p p').
  intros.
  destruct p; destruct p'.
  unfold beq_path in H.
  unfold beq_path in H0.
  symmetry in H.
  reflexivity.
  inversion H.
  inversion H.
  destruct p.
  destruct i.
  inversion H2.
  inversion H2.
  inversion H2.
  admit. (* Need beq_path -> equality. *)
  intros.
  rewrite H in H0.
  inversion H0.
Qed.

Lemma beq_path_neq:
  forall (p p' : P),
    beq_path p p' = false ->
    p <> p'.
Proof.
  intros.
  case_eq (beq_path p p').
  intros.
  destruct p; destruct p'.
  unfold beq_path in H.
  unfold beq_path in H0.
  inversion H.
  rewrite H in H0.
  inversion H0.
  rewrite H in H0.
  inversion H0.
  admit.
  intros.
  destruct p; destruct p'.
  inversion H.
  admit.
  admit.
  admit.
Qed.  


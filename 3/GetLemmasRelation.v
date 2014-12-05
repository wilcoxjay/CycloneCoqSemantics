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

Lemma getD_Some_Weakening:
 forall (alpha : TVar) (k : Kappa) (d d' : Delta),
   WFD (d ++ d') ->
   getD d alpha = Some k ->
   getD (d ++ d') alpha = Some k.
Proof.
  intros alpha k d d' WFDder getDder.
  functional induction (getD d alpha); crush.
  inversion WFDder.
  apply IHo in H3.
  assumption.
  assumption.
Qed.

Lemma getD_Some_None_Implies_Different_Variables:
  forall (alpha : TVar) (d : Delta) (n : nat) (k : Kappa),
      getD d (tvar n ) = Some k ->
      forall (n' : nat),
        getD d (tvar n') = None ->
        beq_nat n' n = false.
Proof.
  intros alpha d n k getDder.
  induction (cons (alpha,k) d); crush.
  (* TODO It's true but how to show it? *)
Admitted.

(* Does this need to be strengthened with WFU u ? *)
Lemma getU_Some_Weakening:
  forall (u : Upsilon) (x : EVar) (p : P) (tau : Tau),
    getU u x p tau ->
    forall (u' : Upsilon),
      getU (u ++ u') x p tau.
Proof.
  intros u x p tau getUder.
  induction u.
  Case "[]".
   inversion getUder.
  Case "a :: u".
   intros u'.
   destruct a.
   destruct p0.
   inversion getUder.
   constructor.
   constructor.
   assumption.
   crush.
Qed.
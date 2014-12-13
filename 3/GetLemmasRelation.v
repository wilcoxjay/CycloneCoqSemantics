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

Lemma getD_None_Strengthening: 
  forall (d d' : Delta) (alpha : TVar),
    getD (d ++ d') alpha = None ->
    getD d alpha = None.
Proof.
 intros.
 induction d.
 Case "d = []".
  simpl.
  destruct alpha.
  reflexivity.
 Case "a :: d".
  destruct a.
  unfold getD.
  destruct alpha.
  fold getD.
  destruct t.
  unfold getD in H.
  simpl in H.
  fold getD in H.
  destruct (beq_nat n n0).
  inversion H.
  apply IHd in H.
  admit. (* beq_tvar bug. *)
Qed.

Lemma getG_None_Strengthening: 
  forall (g g' : Gamma) (x : EVar),
    getG (g ++ g') x = None ->
    getG g x = None.
Proof.
 intros.
 induction g.
 Case "g = []".
  simpl.
  destruct x.
  reflexivity.
 Case "a :: g".
  destruct a.
  unfold getG.
  destruct x.
  fold getG.
  destruct e.
  unfold getG in H.
  simpl in H.
  fold getG in H.
  destruct (beq_nat n n0).
  inversion H.
  apply IHg in H.
  admit. (* beq_tvar bug. *)
Qed.

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

(* TODO strengthen this with WFCDG or build a WFG? *)
Lemma getG_Some_Weakening:
 forall (x: EVar) (tau : Tau) (g g' : Gamma),
   getG g x = Some tau ->
   getG (g ++ g') x = Some tau.
Proof.
  intros x tau g g' getGder.
  functional induction (getG g x); crush.
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


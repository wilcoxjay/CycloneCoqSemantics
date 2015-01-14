(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  This defines lemmas about extending contexts. 

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Export FormalSyntax.
Require Export TacticNotations.
Require Export CpdtTactics.
Require Export Case.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export ContextExtensionRelation.

Require Export VarLemmas.
Require Export ListLemmas.
Require Export GetLemmasRelation.
Require Export StaticSemanticsWellFormednessLemmas.

Lemma ExtendedByD_weakening:
 forall (d d' : Delta),
   ExtendedByD d d' -> 
   forall (alpha : TVar) (k : Kappa),
     WFD ((alpha, k) :: d') ->
     ExtendedByD d ((alpha, k) :: d').
Proof.
  intros d d' ext.
  induction ext.
  Case "[]".
   intros.
   constructor.
  Case "(alpha,k) :: dtail".
   intros.
   constructor.

   case_eq(beq_tvar alpha alpha0); case_eq(beq_kappa k k0); intros.
   SCase "alpha0 = alpha, k = k0.".
    apply beq_kappa_eq in H1.
    apply beq_tvar_eq in H2.
    rewrite H1.
    rewrite H2.
    unfold getD.
    fold getD.
    rewrite beq_tvar_reflexive.
    reflexivity.
   SCase "alpha0 = alpha, k <> k0".
    apply beq_tvar_eq in H2.
    rewrite <- H2 in H0.
    apply Duplicate_Alpha_implies_not_WFD with (k':= k0) in H.
    unfold not in H.
    apply H in H0.
    inversion H0.
   SCase "alpha <> alpha0, k = k0".
    unfold getD.     
    fold getD.
    rewrite H2.
    assumption.
   SCase "alpha <> alpha0, k <> k0".
    unfold getD.     
    fold getD.
    rewrite H2.
    assumption.
   SCase "IH".
    apply IHext.
    assumption.
Qed.

Lemma ExtendedByD_preserved_under_add_alpha_k:
  forall (d : Delta),
    WFD d ->
    forall (alpha : TVar),
      getD d alpha = None ->
      forall (d' : Delta),
        WFD d' ->
        getD d' alpha = None ->
        ExtendedByD d d' ->
        forall (k : Kappa), 
          ExtendedByD ([(alpha, k)] ++ d) ([(alpha, k)] ++ d').
Proof.
  intros d WFDder alpha getDdalphaNone d' WFDd' getDd'alphaNone ext k.
  constructor.
  rewrite <- cons_is_append_singleton.
  unfold getD.
  fold getD.
  rewrite beq_tvar_reflexive.
  reflexivity.
  apply ExtendedByD_weakening.
  assumption.
  constructor; try assumption.
Qed.

Lemma Nil_ExtendedByD_Only_Nil:
 forall (d : Delta) (alpha : TVar) (k : Kappa),
      ~ExtendedByD ((alpha,k) :: d) [].
Proof.
  intros.
  unfold not.
  intros.
  inversion H.
  inversion H4.
Qed.


Lemma ExtendedByD_reflexive:
  forall d, 
    WFD d -> 
    ExtendedByD d d.
Proof.
  intros.
  induction d.
  constructor.
  destruct a.
  constructor.
  simpl.
  rewrite beq_tvar_reflexive.
  reflexivity.
  apply ExtendedByD_weakening; try assumption.
  inversion H.
  apply IHd in H4; try assumption.
Qed.
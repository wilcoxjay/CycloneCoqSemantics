(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

   Lemmas about static semantics kinding.

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
Require Export TacticNotations.
Require Export GetLemmasRelation.
Require Export ContextExtensionRelation.
Require Export ContextExtensionLemmas.

Fixpoint no_bound_vars (t : Tau) (d : Delta) : Prop :=
  match t with
    | tv_t tv => True
    | cint => True
    | cross t1 t2 => no_bound_vars t1 d /\ no_bound_vars t2 d
    | arrow t1 t2 => no_bound_vars t1 d /\ no_bound_vars t2 d
    | ptype t' => no_bound_vars t' d
    | utype tv k t' => (forall k, ~ In (tv,k) d) /\ no_bound_vars t' ((tv,k)::d)
    | etype phi tv k t' => (forall k, ~ In (tv,k) d) /\ no_bound_vars t' ((tv,k)::d)
  end.

Lemma not_in_getD_none :
  forall d alpha,
    (forall k, ~ In (alpha,k) d) ->
    getD d alpha = None.
Proof.
  induction d; intros; simpl in *; auto.
  destruct a.
  destruct (beq_tvar alpha t) eqn:?; auto.
  - apply beq_tvar_eq in Heqb. subst. exfalso. eapply H; eauto.
  - apply beq_tvar_neq in Heqb.
    apply IHd.
    intros. intro.
    eapply H; eauto.
Qed.

Lemma K_weakening:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      WFD d ->
      K d tau k -> 
      forall (d' : Delta),
        WFD d' ->
        ExtendedByD d d' ->
        no_bound_vars tau d' ->
        K d' tau k.
Proof.
 intros d tau k WFDder Kder.
 K_ind_cases (induction Kder) Case.
 
 Case "K d cint B".
  intros.
  constructor.
 Case "K d (tv_t alpha) B".
  intros.
  apply getD_extension_agreement with (d:= d) (d':=d') (alpha:= alpha) (k:= B) 
    in WFDder; 
    try assumption.
  apply K_B; try assumption.
 Case "K d (ptype (tv_t alpha)) B".
  intros.
  constructor.
  apply getD_extension_agreement with (d':= d') in H; try assumption.
 Case "K d tau A".
  intros.
  apply IHKder with (d':= d') in WFDder; try assumption.
  constructor; try assumption.
 Case "K d (cross t0 t1) A".
  intros. simpl in H1.  destruct H1.
  pose proof WFDder as WFDder2.
  apply IHKder1 with (d':= d') in WFDder; try assumption.
  apply IHKder2 with (d':= d') in WFDder2; try assumption.
  apply K_cross; try assumption.
 Case "K d (arrow t0 t1) A".
  intros. simpl in H1. destruct H1.
  pose proof WFDder as WFDder2.
  apply IHKder1 with (d':= d') in WFDder; try assumption.
  apply IHKder2 with (d':= d') in WFDder2; try assumption.
  apply K_arrow; try assumption.
 Case "K d (ptype tau) B".
  intros. simpl in H1.
  apply IHKder with (d':= d') in WFDder; try assumption.
  constructor.
  assumption.
 Case "K d (utype alpha k tau) A".
  intros. simpl in H3. destruct H3.
  assert (Z: getD d' alpha = None) by auto using not_in_getD_none.

  apply IHKder with (d':= ([(alpha, k)] ++ d')) in H; try assumption.
  apply K_utype; try assumption.
  constructor; try  assumption.
  constructor; try assumption.
  apply ExtendedByD_preserved_under_add_alpha_k; try assumption.
 Case "K d (etype p alpha k tau) A)".
  intros. simpl in H3. destruct H3.
  assert (Z: getD d' alpha = None) by auto using not_in_getD_none.
  apply IHKder with (d':= ([(alpha, k)] ++ d')) in H; try assumption.
  apply K_etype; try assumption.
  constructor; try  assumption.
  constructor; try assumption.
  apply ExtendedByD_preserved_under_add_alpha_k; try assumption.
Qed.

Lemma AK_weakening:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      WFD d ->
      AK d tau k -> 
      forall (d' : Delta),
        WFD d' ->
        ExtendedByD d d' ->
        AK d' tau k.
Proof.
 intros d tau k WFDder AKder.
 inversion AKder.
 intros.
 constructor.
 apply K_weakening with (d:= d); try assumption.
 intros.
 rewrite <- H2 in *.
 rewrite <- H1 in *.
 assert (Z: getD d' alpha = Some A).
 apply getD_extension_agreement with (d':= d') in H; try assumption.
 apply AK_A; try assumption.
Qed.

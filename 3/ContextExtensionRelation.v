(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  This defines the notions of extending contexts. 

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
Require Export VarLemmas.
Require Export ListLemmas.
Require Export GetLemmasRelation.

Inductive ExtendedByD : Delta -> Delta -> Prop := 
  | ExtendedByD_nil   : forall (d' : Delta),
                          ExtendedByD [] d'
  | ExtendedByD_left  : 
      forall (alpha : TVar) (k : Kappa) (dtail : Delta) (d' : Delta),
        getD d' alpha = Some k ->
        ExtendedByD dtail d' ->
        ExtendedByD ((alpha,k) :: dtail) d'.

Lemma Duplicate_Alpha_implies_not_WFD:
  forall (d' : Delta) (alpha : TVar) (k k' : Kappa),
    getD d' alpha = Some k -> 
    ~ WFD ((alpha,k') :: d').
Proof.
  intros d' alpha k k' getDder.
  unfold not.
  intros WFDder.
  inversion WFDder.
  rewrite H1 in getDder.
  inversion getDder.
Qed.

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

   case_eq(beq_tvar alpha alpha0); case_eq(beq_Kappa k k0); intros.
   SCase "alpha0 = alpha, k = k0.".
    apply beq_Kappa_eq in H1.
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

Lemma getD_extension_agreement:
  forall (d : Delta) (alpha : TVar) (k : Kappa),
    getD d  alpha = Some k ->
    WFD d ->
    forall (d' : Delta),
      WFD d' ->
      ExtendedByD d d' ->
      getD d' alpha = Some k.
Proof.
  (* Laphroig 10 year. *)
  intros d alpha k.
  functional induction (getD d alpha).
  Case "Some k0 = k0".
   intros.
   apply beq_tvar_eq in e1.
   inversion H.
   rewrite <- e1 in H2.
   rewrite <- e1 in H0.
   rewrite H4 in H2.
   rewrite H4 in H0.
   inversion H2.
   assumption.
  Case "getD d' alpha = Some k".
   intros.
   inversion H0.
   inversion H2.
   apply IHo with (d'0 := d'0) in H; try assumption.
  Case "None = Some".
   intros.
   inversion H.
Qed.

Lemma getD_extension_agreement_fun:
  forall (d : Delta) (alpha : TVar) (k : Kappa),
    getD d alpha = Some k ->
  forall (d' : Delta),
    WFD d' ->
    ExtendedByD d d' ->
    getD d' alpha = Some k.
Proof.
  intros d alpha k.
  functional induction (getD d alpha).
  intros.
  Case "alpha = b".
   apply beq_tvar_eq in e1.
   inversion H1.
   rewrite <- H2 in H1.
   rewrite <- H2 in H6.
   inversion H.
   rewrite H9 in H1.
   crush.
  Case "?".
   intros.
   apply IHo with (d'0:= d'0) in H; try assumption.
   inversion H1.
   assumption.
  Case "false".
   intros.
   inversion H.
Qed.

Lemma K_weakening:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      WFD d ->
      K d tau k -> 
      forall (d' : Delta),
        WFD d' ->
        ExtendedByD d d' ->
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
  intros.
  pose proof WFDder as WFDder2.
  apply IHKder1 with (d':= d') in WFDder; try assumption.
  apply IHKder2 with (d':= d') in WFDder2; try assumption.
  apply K_cross; try assumption.
 Case "K d (arrow t0 t1) A".
  intros.
  pose proof WFDder as WFDder2.
  apply IHKder1 with (d':= d') in WFDder; try assumption.
  apply IHKder2 with (d':= d') in WFDder2; try assumption.
  apply K_arrow; try assumption.
 Case "K d (ptype tau) B".
  intros.
  apply IHKder with (d':= d') in WFDder; try assumption.
  constructor.
  assumption.
 Case "K d (utype alpha k tau) A".
  intros.
  assert (Z: getD d' alpha = None).
  AdmitAlphaConversion.
  apply IHKder with (d':= ([(alpha, k)] ++ d')) in H; try assumption.
  apply K_utype; try assumption.
  constructor; try  assumption.
  constructor; try assumption.
  apply ExtendedByD_preserved_under_add_alpha_k; try assumption.
 Case "K d (etype p alpha k tau) A)".
  intros.
  assert (Z: getD d' alpha = None).
  AdmitAlphaConversion.
  apply IHKder with (d':= ([(alpha, k)] ++ d')) in H; try assumption.
  apply K_etype; try assumption.
  constructor; try  assumption.
  constructor; try assumption.
  apply ExtendedByD_preserved_under_add_alpha_k; try assumption.
Qed.

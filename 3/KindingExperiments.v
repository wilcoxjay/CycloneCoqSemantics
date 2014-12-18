(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Playing with Kinding.

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
Require Export WeakeningLemmas.
Require Export SubstitutionsProof.

(* I don't think that this is strong enough. *)
Lemma rtype_K_A:
  forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau),
    rtyp d u g e t ->
      K d t A.
Proof.
  intros d u g e t rtypder.
  rtyp_ind_mutual_cases (
  apply (rtyp_ind_mutual 
              (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                   (st : styp d u g t s) => 
                  K d t A)
              (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                   (lt : ltyp d u g  e t) =>
                   K d t A)
              (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                   (rt : rtyp d u g e t) =>
                 K d t A)) with (u:=u) (g:=g) (e:=e)) Case.

  Case "styp_e_3_1".
   intros.
   assumption.
  Case "styp_return_3_2".
   intros.
   assumption.
  Case "styp_seq_3_3".
   intros.
   assumption.
  Case "styp_while_3_4".
   intros.
   assumption.
  Case "styp_if_3_5".
   intros.
   assumption.
  Case "styp_let_3_6".
   intros.
   assumption.
  Case "styp_open_3_7".
   intros.
   assumption.
  Case "styp_openstar_3_8".
   intros.
   assumption.
  Case "SL_3_1".
   admit.
 Case "SL_3_2".
   intros.
   assumption.
  Case "SL_3_3".
   intros.
   inversion H.
   inversion H0. (* get rid of K B. *)
   assumption.
  Case "SL_3_4".
   intros.
   inversion H.
   inversion H0. (* get rid of K B. *)
   assumption.
  Case "SR_3_1".
   intros.
   admit.
  Case "SR_3_2".
   intros.
   assumption.
  Case "SR_3_3".
   intros.
   inversion H.
   inversion H0.
   assumption.
  Case "SR_3_4".
   intros.
   inversion H.
   inversion H0.
   assumption.
  Case "SR_3_5".
   intros.
   constructor.
   apply K_int.
  Case "SR_3_6".
   intros.
   constructor.
   constructor.
   assumption.
  Case "SR_3_7".
   intros.
   apply K_cross.
   assumption.
   assumption.
  Case "SR_3_8".
   intros.
   assumption.
  Case "SR_3_9".
   intros.
   inversion H.
   inversion H1.
   assumption.
  Case "SR_3_10".
   intros.
   assumption.
  Case "SR_3_11".
   intros.
   apply A_6_Substitution_1 with (k:= A).
   inversion H.
   inversion H0.
   destruct k.
   inversion a.
   crush.
   constructor.
   constructor.
   assumption.
   assumption.
   destruct k.
   admit.
   admit.
  Case "SR_3_12".
   intros.
   assumption.
  Case "SR_3_13".
   intros.
   apply K_arrow.
   inversion s0.
   crush.
   admit. (* Very interesting that I can't get this case. *)
   assumption.
  Case "SR_3_14".
   intros.
   apply K_utype; try assumption.
   constructor; try assumption.
   inversion w; try assumption.
  Case "base".
   assumption.
Qed.

(* This may even be true now. *)
(* Definitely going to need some lemmas to reason about this here. *)
(* Perhaps disjoint kinding needs to be a judgement here. *)
Lemma disjoint_kinding_well_formed:
  forall (d' : Delta),
    WFD d' ->
      forall (d : Delta),
        DisjointKinding d' d = true ->
        WFD (d ++ d').
Proof.
  intros.
  induction d.
  Case "WFD ([] ++ d')".
   rewrite app_nil_l.
   assumption.
  Case "WFD ((a :: d) ++ d')".
   destruct a.
   unfold DisjointKinding in H0.
   simpl in H0.
   (* 
   destruct (InDomD alpha d').
   fold DisjointKinding in H0.
   constructor.
   admit.
   assert (Z: DisjointKinding d' d = true).
   admit.
   apply IHd in Z.
   assumption.
     *)
   admit.
Qed.


Lemma kinding_unkinded_tvars_is_disjoint:
  forall (d d' : Delta) (tau : Tau),
   d' = KindUnkindedTVarsAtB tau d ->
   DisjointKinding d' d = true.
Proof.
  intros.
  induction d'.
  admit.
  (* That might be provable from fold/unfolds. *)
Admitted.
                             
Lemma kinding_unions_make_well_formed_Deltas:
  forall (d0 d1 d : Delta),
    DisjointKinding d0 d = true ->
    DisjointKinding d1 d = true -> 
    WFD (KindingUnion d0 d1 ++ d).
Proof.
Admitted.

(* Not strong enough without the ~ I think. *)
(* Do I need open in d? *)
Lemma recursion_kinding: 
  forall (d : Delta) (tau : Tau),
    K (KindingUnion (KindUnkindedTVarsAtB tau d) d) tau B.
Proof.
  intros.
  Tau_ind_cases
    (apply (Tau_ind 
               (fun (tau : Tau) => 
                    K (KindingUnion (KindUnkindedTVarsAtB tau d) d) tau B))) Case.
  Case "(tv_t t)".
  (* 
   intros.
   unfold KindUnkindedTVarsAtB.
   destruct (InDomD t d).
   admit. (* Just plain false, nothing to invert, so we're not strong enough. *)
   simpl.
   destruct (InDomD t d).
   admit. (* Again false. *)
   constructor.
   destruct t.
   simpl.
   destruct (beq_nat n n).
   reflexivity.
   admit. (* False, None = Some. *)
   simpl.
   constructor.
   *)
   admit.
  Case "cint".
   intros.
   simpl.
   constructor.
  Case "(cross t t0)".
   intros.
   apply K_cross.
   unfold KindUnkindedTVarsAtB.
   fold KindUnkindedTVarsAtB.
   admit.
   admit.
  Case "(arrow t t0)".
   admit.
  Case "(ptype t)".
   intros.
   constructor.
   apply K_ptype.
   unfold KindUnkindedTVarsAtB.
   fold KindUnkindedTVarsAtB.
   assumption.
  Case "(utype t k t0)".
   admit.
  Case "(etype p t k t0)".
   admit.
Qed.

(* I think that this is what I need. *)
Lemma all_open_types_have_weakened_A_kinding:
  forall (d : Delta) (tau : Tau),
    WFD d ->
     exists (d' : Delta), 
      d' = KindUnkindedTVarsAtB tau d /\
      WFD (d' ++ d) /\
      K (d' ++ d) tau A.
Proof.
  intros.
  Tau_ind_cases
    (apply (Tau_ind 
               (fun (tau : Tau) => 
                  exists (d' : Delta), 
                    d' = KindUnkindedTVarsAtB tau d /\
                    WFD (d' ++ d) /\
                    K (d' ++ d) tau A))) Case.
  Case "(tv_t t)".
   admit.
  Case "cint".
   intros.
   apply ex_intro with (x:=[]).
   rewrite app_nil_l.
   split.
   reflexivity.
   split.
   assumption.
   constructor.
   constructor.
  Case "(cross t t0)".
   intros.
   destruct H0.
   inversion H0.
   inversion H3.
   destruct H1.
   inversion H1.
   inversion H7.
   apply ex_intro with (x:= KindingUnion x x0).
   split.
   unfold KindUnkindedTVarsAtB.
   fold KindUnkindedTVarsAtB.
   rewrite H6.
   rewrite H2.
   reflexivity.
   split.
   apply kinding_unkinded_tvars_is_disjoint in H6.
   apply kinding_unkinded_tvars_is_disjoint in H2.
   apply kinding_unions_make_well_formed_Deltas; try assumption.

  Case "(arrow t t0)".
   admit.
  Case "(ptype t)".
   admit.
  Case "(utype t k t0)".
   admit.
  Case "(etype p t k t0)".
   admit.
  Case "base".
   admit.
Qed.

(* This is not quite right, I want to make sure that tau's free variables are
  covered, not kind them all if they are in d. *)
Lemma get_a_Klue:
  forall (d : Delta) (u : Upsilon) (g: Gamma),
    WFC d u g -> 
    forall (x : EVar) (tau : Tau),
      DisjointKinding (KindTVarsAtB tau (DomD d)) d = true ->
      WFC ((KindTVarsAtB tau) ++ d) u ([(x, tau)] ++ g).
Proof.
  intros d u g WFCder.
  apply (WFC_ind
           (fun (d : Delta) (u : Upsilon) (g : Gamma) =>
              forall (x : EVar) (tau : Tau),
                DisjointKinding (KindTVarsAtB tau) d = true ->
                WFC ((KindTVarsAtB tau) ++ d) u ([(x, tau)] ++ g))).
  Case "WFD, WFDG, WFU.".
   intros.
   constructor; try assumption.
   SCase "WFDG d0 ([(x, tau)] ++ g0)".
    constructor; try assumption.
    AdmitAlphaConversion.
    Tau_ind_cases (induction tau) SSCase.
    SSCase "(tv_t t)".
     admit.
    SSCase "cint".
     constructor.
     constructor.
    SSCase "(cross t t0)".
     apply K_cross; try assumption.
    SSCase "(arrow t t0)".
     apply K_arrow; try assumption.
    SSCase "(ptype t)".
     constructor.
     apply K_ptype; try assumption.
    SSCase "(utype t k t0)".
     apply K_utype; try assumption.
     admit.
     admit.
     admit.
    SSCase "(etype p t k t0)".
     apply K_etype.
     admit.
     admit.
     admit.
  Case "WFC d u g".
   assumption.
Qed.

Lemma K_A_all_Tau:
  forall (d : Delta) (tau : Tau),
    K d tau B ->
    K d tau A.
Proof.
  intros.
  apply K_B_A.
  assumption.
Qed.
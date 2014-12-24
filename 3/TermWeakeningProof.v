(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Defining type safety, page 67.

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

Require Export StaticSemanticsWellFormednessLemmas.
Require Export StaticSemanticsHeapObjectsLemmas.

Lemma A_2_Term_Weakening_1 :
  forall (d: Delta) (u u' : Upsilon) (g g' : Gamma)
         (x : EVar) (p p' : P) (tau tau' : Tau),
    WFC d (u ++ u') (g ++ g') ->
    gettype u x p tau p' tau' ->
    gettype (u ++ u') x p tau p' tau'.
Proof.
  intros d u u' g g' x p p' tau tau'.
  intros WFCd.
  intros gettypeder.
  gettype_ind_cases (induction gettypeder) Case.
  Case "gettype u x p tau [] tau".
   constructor.
  Case "gettype u x p (cross t0 t1) (i_pe zero_pe :: p') tau".
   constructor.
   apply IHgettypeder in WFCd.
   assumption.
  Case "gettype u x p (cross t0 t1) (i_pe one_pe :: p') tau".
   constructor.
   apply IHgettypeder in WFCd.
   assumption.
  Case "gettype u x p (etype aliases alpha k tau') (u_pe :: p') tau)".
   apply IHgettypeder in WFCd.
   apply gettype_etype with (tau'':= tau'').
   apply getU_Some_Weakening. 
   assumption.
   assumption.
Qed.

(* TODO let, open, openstar and function application. *)
Lemma A_2_Term_Weakening_2:
  forall (d: Delta) (u : Upsilon) (g : Gamma)  (e : E) (tau : Tau),
    ltyp d u g e tau ->
    WFC d u g -> 
      forall (u' : Upsilon) (g' : Gamma),
        WFC d u' g' ->
        WFC d (u ++ u') (g ++ g') ->
        ltyp d (u ++ u') (g ++ g') e tau.
Proof.
  intros d u g e tau ltypder.
  apply (ltyp_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              WFC d u g -> 
              forall (u' : Upsilon) (g' : Gamma),
                WFC d u' g' ->
                WFC d (u ++ u') (g ++ g') ->
                styp d (u ++ u') (g ++ g') t s)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (lt : ltyp d u g  e t) =>
              WFC d u g -> 
              forall (u' : Upsilon) (g' : Gamma),
                WFC d u' g' ->
                WFC d (u ++ u') (g ++ g') ->
                ltyp d (u ++ u') (g ++ g') e t)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              WFC d u g -> 
              forall (u' : Upsilon) (g' : Gamma),
                WFC d u' g' ->
                WFC d (u ++ u') (g ++ g') ->
                rtyp d (u ++ u') (g ++ g') e t)).
  Case "styp_e_3_1".
   intros.
   constructor.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "styp_return_3_2".
   intros.
   constructor.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "styp_seq_3_3".
   intros.
   constructor.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "styp_while_3_4".
   intros.
   constructor.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "styp_if_3_5".
   intros.
   constructor.
   apply H with (u':= u') (g':= g') in H2; try assumption.
   apply H0 with (u':= u') (g':= g') in H2; try assumption.
   apply H1 with (u':= u') (g':= g') in H2; try assumption.

  Case "styp_let_3_6".
  (* OKay this works, modulo alpha conversion but the case is a 
      repetitive mess. *)
   intros.
   apply styp_let_3_6 with (tau':=tau'); try assumption.
   AdmitAlphaConversion.
   inversion H2; try assumption.
   assert (Z: WFC d0 u0 ([(x, tau')] ++ g0)).
   constructor; try assumption.
   constructor; try assumption.
   inversion H1; try assumption.
   inversion H3; try assumption.
   apply WFU_strengthening in H12; try assumption.
   apply H with (u':= u') (g':= g') in Z; try assumption.
   constructor; try assumption.
   apply WFDG_xt.
   AdmitAlphaConversion.
   assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
   inversion H3.
   assumption.
   inversion H3; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "styp_open_3_7".
   intros.
   inversion H1.
   inversion H2.
   crush.
   apply styp_open_3_7 with (p:= p) (k:= k) (tau':= tau'); try assumption.
   AdmitAlphaConversion.
   apply H16 in H2; try assumption.
   apply H0; try assumption.
   constructor; try assumption.
   constructor; try assumption.
   constructor; try assumption.
   admit. (* Don't know where to get this K, it's coming from the pack that is e0. *)
   constructor; try assumption.
   constructor; try assumption.
   constructor; try assumption.   
   constructor; try assumption.   
   constructor; try assumption.   
   constructor; try assumption.      
   constructor; try assumption.   
   AdmitAlphaConversion.
   admit. (* Don't know where to get this K. *)
   constructor; try assumption.
   admit. (* WFDG weakening. *)
   (* What do I have here to make a WFDG true ? *)
   inversion H3; try assumption.
  Case "styp_openstar_3_8".
   admit. (* Will have the similar problems with let. *)
  Case "SL_3_1".
   intros.
   apply SL_3_1 with (tau':=tau'); try assumption.
   apply getG_Some_Weakening; try assumption.
   apply gettype_weakening; try assumption.
   inversion H; try assumption.
   inversion H1; try assumption.
  Case "SL_3_2".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SL_3_3".
   intros.
   apply SL_3_3 with (t1:= t1); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SL_3_4".
   intros.
   apply SL_3_4 with (t0:= t0); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_1".
   intros.
   apply SR_3_1 with (tau':= tau'); try assumption.
   apply getG_Some_Weakening; try assumption.
   apply gettype_weakening; try assumption.
   inversion H; try assumption.
   inversion H1; try assumption.
  Case "SR_3_2".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_3".
   intros.
   apply SR_3_3 with (t1:= t1); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_4".
   intros.
   apply SR_3_4 with (t0:= t0); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_5".
   intros.
   constructor; try assumption.
  Case "SR_3_6".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_7".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_8".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_9".
   intros.
   apply SR_3_9 with (tau':= tau'); try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_10".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_11".
   intros.
   apply SR_3_11 with (k:=k); try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_12".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  (* TODO two cases and then I'm done without rtype weakening. *)
  Case "SR_3_13".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   AdmitAlphaConversion.
   admit.
   admit.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   admit.
   admit.
  Case "SR_3_14".
   admit.
  Case "base".
   assumption.
Qed.


Lemma A_2_Term_Weakening_3:
  forall (d: Delta) (u : Upsilon) (g : Gamma)  (e : E) (tau : Tau),
    rtyp d u g e tau ->
    WFC d u g -> 
      forall (u' : Upsilon) (g' : Gamma),
        WFC d u' g' ->
        WFC d (u ++ u') (g ++ g') ->
        rtyp d (u ++ u') (g ++ g') e tau.
Proof.
  intros d u g e tau ltypder.
  apply (rtyp_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              WFC d u g -> 
              forall (u' : Upsilon) (g' : Gamma),
                WFC d u' g' ->
                WFC d (u ++ u') (g ++ g') ->
                styp d (u ++ u') (g ++ g') t s)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (lt : ltyp d u g  e t) =>
              WFC d u g -> 
              forall (u' : Upsilon) (g' : Gamma),
                WFC d u' g' ->
                WFC d (u ++ u') (g ++ g') ->
                ltyp d (u ++ u') (g ++ g') e t)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              WFC d u g -> 
              forall (u' : Upsilon) (g' : Gamma),
                WFC d u' g' ->
                WFC d (u ++ u') (g ++ g') ->
                rtyp d (u ++ u') (g ++ g') e t)).
(*
  Case "styp_e_3_1".
   intros.
   constructor.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "styp_return_3_2".
   intros.
   constructor.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "styp_seq_3_3".
   intros.
   constructor.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "styp_while_3_4".
   intros.
   constructor.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "styp_if_3_5".
   intros.
   constructor.
   apply H with (u':= u') (g':= g') in H2; try assumption.
   apply H0 with (u':= u') (g':= g') in H2; try assumption.
   apply H1 with (u':= u') (g':= g') in H2; try assumption.
  Case "styp_let_3_6".
   intros.
   apply styp_let_3_6 with (tau':=tau'); try assumption.
   AdmitAlphaConversion.
   inversion H2; try assumption.
   assert (Z: WFC d0 u0 ([(x, tau')] ++ g0)). (* How do I get this ? *)
   constructor; try assumption.
   constructor; try assumption.
   admit.
   admit.
   admit.
   admit.
   admit.
   (* 
   apply H with (u':= u') (g':= g') in Z; try assumption.
   admit.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
   *)
  Case "styp_open_3_7".
   admit. (* Will have the similar problems with let. *)
  Case "styp_openstar_3_8".
   admit. (* Will have the similar problems with let. *)
  Case "SL_3_1".
  (* Should use the previous theorem.
   intros.
   apply SL_3_1 with (tau':= tau0); try assumption.
   apply getG_Some_Weakening; try assumption.
   apply gettype_weakening; try assumption.
   inversion H; try assumption.
   inversion H1; try assumption.
   *)
  admit.
  Case "SL_3_2".
   intros.
   admit. (* constructor; try assumption. *)
   (* apply H with (u':= u') (g':= g') in H0; try assumption. *)
  Case "SL_3_3".
   intros.
   apply SL_3_3 with (t1:= t1); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SL_3_4".
   intros.
   apply SL_3_4 with (t0:= t0); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_1".
   intros.
   apply SR_3_1 with (tau':= tau'); try assumption.
   apply getG_Some_Weakening; try assumption.
   apply gettype_weakening; try assumption.
   inversion H; try assumption.
   inversion H1; try assumption.
  Case "SR_3_2".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_3".
   intros.
   apply SR_3_3 with (t1:= t1); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_4".
   intros.
   apply SR_3_4 with (t0:= t0); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_5".
   intros.
   constructor; try assumption.
  Case "SR_3_6".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_7".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_8".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_9".
   intros.
   apply SR_3_9 with (tau':= tau'); try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_10".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_11".
   intros.
   apply SR_3_11 with (k:=k); try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_12".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_13".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   AdmitAlphaConversion.
   admit.
   admit.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   admit.
   admit.
  Case "SR_3_14".
   admit.
  Case "base".
   assumption.
Qed.

Lemma A_2_Term_Weakening_4:
  forall (d: Delta) (u : Upsilon) (g : Gamma)  (s : St) (tau : Tau),
    styp d u g tau s ->
    WFC d u g -> 
      forall (u' : Upsilon) (g' : Gamma),
        WFC d u' g' ->
        WFC d (u ++ u') (g ++ g') ->
        styp d (u ++ u') (g ++ g') tau s.
Proof.
  intros d u g e tau ltypder.
  apply (styp_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              WFC d u g -> 
              forall (u' : Upsilon) (g' : Gamma),
                WFC d u' g' ->
                WFC d (u ++ u') (g ++ g') ->
                styp d (u ++ u') (g ++ g') t s)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (lt : ltyp d u g  e t) =>
              WFC d u g -> 
              forall (u' : Upsilon) (g' : Gamma),
                WFC d u' g' ->
                WFC d (u ++ u') (g ++ g') ->
                ltyp d (u ++ u') (g ++ g') e t)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              WFC d u g -> 
              forall (u' : Upsilon) (g' : Gamma),
                WFC d u' g' ->
                WFC d (u ++ u') (g ++ g') ->
                rtyp d (u ++ u') (g ++ g') e t)).
  Case "styp_e_3_1".
   intros.
   constructor.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "styp_return_3_2".
   intros.
   constructor.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "styp_seq_3_3".
   intros.
   constructor.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "styp_while_3_4".
   intros.
   constructor.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "styp_if_3_5".
   intros.
   constructor.
   apply H with (u':= u') (g':= g') in H2; try assumption.
   apply H0 with (u':= u') (g':= g') in H2; try assumption.
   apply H1 with (u':= u') (g':= g') in H2; try assumption.
  Case "styp_let_3_6".
   intros.
   apply styp_let_3_6 with (tau':=tau'); try assumption.
   AdmitAlphaConversion.
   inversion H2; try assumption.
   assert (Z: WFC d0 u0 ([(x, tau')] ++ g0)). (* How do I get this ? *)
   constructor; try assumption.
   constructor; try assumption.
   admit.
   admit.
   admit.
   apply H with (u':= u') (g':= g') in Z; try assumption.
   admit.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "styp_open_3_7".
   admit. (* Will have the similar problems with let. *)
  Case "styp_openstar_3_8".
   admit. (* Will have the similar problems with let. *)
  Case "SL_3_1".
   intros.
   apply SL_3_1 with (tau':=tau'); try assumption.
   apply getG_Some_Weakening; try assumption.
   apply gettype_weakening; try assumption.
   inversion H; try assumption.
   inversion H1; try assumption.
  Case "SL_3_2".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SL_3_3".
   intros.
   apply SL_3_3 with (t1:= t1); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SL_3_4".
   intros.
   apply SL_3_4 with (t0:= t0); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_1".
   intros.
   apply SR_3_1 with (tau':= tau'); try assumption.
   apply getG_Some_Weakening; try assumption.
   apply gettype_weakening; try assumption.
   inversion H; try assumption.
   inversion H1; try assumption.
  Case "SR_3_2".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_3".
   intros.
   apply SR_3_3 with (t1:= t1); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_4".
   intros.
   apply SR_3_4 with (t0:= t0); try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_5".
   intros.
   constructor; try assumption.
  Case "SR_3_6".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H0; try assumption.
  Case "SR_3_7".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_8".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_9".
   intros.
   apply SR_3_9 with (tau':= tau'); try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   apply H0 with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_10".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_11".
   intros.
   apply SR_3_11 with (k:=k); try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_12".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
  Case "SR_3_13".
   intros.
   constructor; try assumption.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   AdmitAlphaConversion.
   admit.
   admit.
   apply H with (u':= u') (g':= g') in H1; try assumption.
   admit.
   admit.
  Case "SR_3_14".
   admit.
  Case "base".
   assumption.
*)
Admitted.

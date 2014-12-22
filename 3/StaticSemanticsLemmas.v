(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

   Lemmas about static semantics typing. 

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
Require Export StaticSemanticsHeapObjectsLemmas.
Require Export StaticSemanticsWellFormednessLemmas.

Require Export TermWeakeningProof.

Lemma ltyp_weakening:
  forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau : Tau),
   ltyp d u g e tau ->
   forall (u' : Upsilon) (g' : Gamma), 
     ltyp d (u ++ u') (g ++ g') e tau.
Proof.
Admitted.

Lemma styp_weakening:
  forall (d : Delta) (u : Upsilon) (g : Gamma) (tau : Tau) (s : St),
    styp d u g tau s -> 
    forall (u' : Upsilon) (g' : Gamma), 
      styp d (u ++ u') (g ++ g') tau s.
Proof.
Admitted.

Lemma rtyp_weakening:
  forall (u : Upsilon) (g : Gamma) (v : E) (tau : Tau),
    rtyp [] u g v tau -> 
    (* WFC [] u g -> *)
    forall (u' : Upsilon) (g' : Gamma),
      (* WFC [] (u ++ u') (g ++ g') ->  *)
      rtyp [] (u ++ u') (g ++ g') v tau.
Proof.
  intros u g v tau rtypder.
  rtyp_ind_cases (induction rtypder) Case.
  Case "rtyp d u g (p_e x p) tau".
   intros.
   apply SR_3_1 with (tau':= tau'); try assumption.
   apply getG_weakening; try assumption.
   apply gettype_weakening; try assumption.
   inversion H2; try assumption.
   admit. (* WFU u ++ u' *)
   admit. (* WFC d (u ++ u') (g ++ g') *)
  Case "rtyp d u g (star e) tau".
   intros.
   constructor; try assumption.
   apply IHrtypder.
  Case "rtyp d u g (dot e zero_pe) t0".
   intros.
   apply SR_3_3 with (t1:= t1) ; try assumption.
   apply IHrtypder.
  Case "rtyp d u g (dot e one_pe) t1".
   intros.
   apply SR_3_4 with (t0:= t0) ; try assumption.
   apply IHrtypder.
  Case "rtyp d u g (i_e (i_i z)) cint".
   intros.
   apply SR_3_5; try assumption.
   admit. (* WFC d (u ++ u') (g ++ g') *)
  Case "rtyp  d u g (amp e) (ptyp tau)".
   intros.
   apply SR_3_6; try assumption.
   apply ltyp_weakening; try assumption.
  Case "rtyp d u g (cpair e0 e1) (cross t0 t1)".
   intros.
   apply SR_3_7; try assumption.
   apply IHrtypder1.
   apply IHrtypder2.
  Case "rtyp d u g (assign e1 e2) tau".
   intros.
   apply SR_3_8; try assumption.
   apply ltyp_weakening; try assumption.   
   apply IHrtypder.
  Case "rtyp d u g (appl e1 e2) tau".
   intros.
   apply SR_3_9 with (tau':= tau'); try assumption.
   apply IHrtypder1; try assumption.
   apply IHrtypder2; try assumption.
  Case "rtyp d u g (call s) tau".
   intros.
   apply SR_3_10; try assumption.
   apply styp_weakening; try assumption.
  Case "rtyp d u g (inst e tau) (subst_Tau tau' tau alpha)".
   intros.
   apply SR_3_11 with (k:= k); try assumption.
   apply IHrtypder; try assumption.
  Case "rtyp  d u g (pack tau' e (etype p alpha k tau)) (etyp p alpha k tau)".
   intros.
   apply SR_3_12; try assumption.
   apply IHrtypder; try assumption.
  Case "rtyp d u g (f_e (dfun tau x tau' s)) (arrow tau tau')".
   intros.
   apply SR_3_13; try assumption.
   AdmitAlphaConversion.
   apply styp_weakening; try assumption.
   admit. (* styp d u [(x, tau)] tau' s  from styp d u ([(x, tau)] ++ g) tau' s. 
          False? *)
  Case "rtyp  d u g (f_e (ufun alpha k f12)) (utyp alpha k tau))".
   intros.
   apply SR_3_14; try assumption.
   apply WFC_weakening with (d':= []) (u':= u') (g':= g'); try assumption.
   admit. (* Think more, it's here. *)
   apply IHrtypder.
Qed.

(* Alternative broken version.
Lemma rtyp_weakening: 
  forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau : Tau),
    rtyp d u g e tau ->
    WFDG d g ->
    WFU  u -> 
    forall (u' : Upsilon) (g' : Gamma),
      WFDG d (g ++ g') ->
      WFU (u ++ u') ->
      rtyp d (u ++ u') (g ++ g') e tau.
Proof.
  (* list induction or rtypeder or a combination? *)
  intros d u g e tau rtypder.
  rtyp_ind_mutual_cases (
  apply (rtyp_ind_mutual
         (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) =>
                 WFDG d g ->
                 WFU  u -> 
                 forall (u' : Upsilon) (g' : Gamma),
                   WFDG d (g ++ g') ->
                   WFU (u ++ u') ->
                   styp d (u ++ u') (g ++ g') t s)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (lt : ltyp d u g e t) =>
                WFDG d g ->
                WFU  u -> 
                forall (u' : Upsilon) (g' : Gamma),
                  WFDG d (g ++ g') ->
                  WFU (u ++ u') ->
                  ltyp d (u ++ u') (g ++ g') e t)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              WFDG d g ->
              WFU  u -> 
              forall (u' : Upsilon) (g' : Gamma),
                WFDG d (g ++ g') ->
                WFU (u ++ u') ->
                rtyp d (u ++ u') (g ++ g') e t)))
        Case.
Proof.
   Case "styp_e_3_1".
    intros.
    apply H with (u':= u') (g':= g') in H0; try assumption.
    constructor; try assumption.
   Case "styp_return_3_2".
    intros.
    apply H with (u':= u') (g':= g') in H0; try assumption.
    constructor; try assumption.
   Case "styp_seq_3_3".
    intros.
    constructor; try assumption.
    apply H  with (u':= u') (g':= g') in H1; try assumption.
    apply H0 with (u':= u') (g':= g') in H1; try assumption.
   Case "styp_while_3_4".
    intros.
    constructor; try assumption.
    apply H  with (u':= u') (g':= g') in H1; try assumption.
    apply H0 with (u':= u') (g':= g') in H1; try assumption.
   Case "styp_if_3_5".
    intros.
    constructor; try assumption.
    apply H with (u':= u') (g':= g') in H2; try assumption.
    apply H0 with (u':= u') (g':= g') in H2; try assumption.
    apply H1 with (u':= u') (g':= g') in H2; try assumption.
   Case "styp_let_3_6".
    intros.
    apply styp_let_3_6 with (tau':= tau'); try assumption.
AdmitAlphaConversion.
    apply WFDG_xt with (d:=d0) (tau:=tau') in e1; try assumption.
    apply H with (u':= u') (g':= g') in e1; try assumption.
    inversion e1; try assumption.
    admit. (* Where ? *)
    admit. (* And this K is from inverting that. *)
    apply H0 with (u':= u') (g':= g')in H1; try assumption.
   Case "styp_open_3_7".
    intros.
    apply styp_open_3_7 with (p:= p) (k:= k) (tau':= tau'); try assumption.
AdmitAlphaConversion.
    apply H with (u':= u') (g':= g') in H1; try assumption.
    (* Construct WFDG ([(alpha, k)] ++ d0) ([(x, tau')] ++ g0)  from
              WFDG d0 g0. *)
    (* apply H0 with (u':= u') (g':= g') in H0; try assumption. *)
    admit.
   Case "styp_openstar_3_8".
    intros.
    apply styp_openstar_3_8 with (k:= k) (tau':= tau'); try assumption.
    apply H with (u':= u') (g':= g') in H1; try assumption.
    admit. (* See construction note above. *)
AdmitAlphaConversion.
   Case "SL_3_1".
    intros.
    apply SL_3_1 with (tau':= tau').
    apply getG_Some_Weakening; assumption.
    apply gettype_weakening; try assumption.
    constructor; try assumption.
    inversion w.
    assumption.
    assumption.
   Case "SL_3_2".
    intros.
    apply H with (u':= u') (g':= g') in H0; try assumption.
    constructor; try assumption.
   Case "SL_3_3".
    intros.
    apply H with (u':= u') (g':= g') in H0; try assumption.
    apply SL_3_3 with (t1:= t1).
    assumption.
   Case "SL_3_4".
    intros.
    apply H with (u':= u') (g':= g') in H0; try assumption.
    apply SL_3_4 with (t0:= t0).
    assumption.
   Case "SR_3_1".
    intros.
    apply SR_3_1 with (tau':=tau'); try assumption.
    apply getG_Some_Weakening; try assumption.
    apply gettype_weakening; try assumption.
    constructor; try assumption.
    inversion w; try assumption.
   Case "SR_3_2".
    intros.
    apply SR_3_2; try assumption.
    apply H with (u':= u') (g':= g') in H0; try assumption.
   Case "SR_3_3".
    intros.
    apply SR_3_3 with (t1:= t1) ; try assumption.
    apply H with (u':= u') (g':= g') in H0; try assumption.
   Case "SR_3_4".
    intros.
    apply SR_3_4 with (t0 := t0) ; try assumption.
    apply H with (u':= u') (g':= g') in H0; try assumption.
   Case "SR_3_5".
    intros.
    apply SR_3_5 ; try assumption.
    constructor; try assumption.
    inversion w; try assumption.
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
    apply SR_3_9 with (tau':=tau'); try assumption.
    apply H with (u':= u') (g':= g') in H1; try assumption.
    apply H0 with (u':= u') (g':= g') in H1; try assumption.
   Case "SR_3_10".
    intros.
    constructor; try assumption.
    apply H with (u':= u') (g':= g') in H1; try assumption.
   Case "SR_3_11".
    intros.
    apply SR_3_11 with (k:= k); try assumption.
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
    constructor; try assumption.
    assert (Z: WFDG d0 ([(x, tau0)] ++ g0)).
    admit.
    inversion Z; try assumption.
    admit. (* Where do I get WFDG d0 (([(x, tau0)] ++ g0) ++ g') from ?*)
    assert (Z: WFDG d0 ([(x, tau0)] ++ g0)).
    admit.
    apply H with (u':= u') (g':= g') in Z; try assumption.
    admit.
   Case "SR_3_14".
    intros.
    constructor; try assumption.
    apply H with (u':= u') (g':= g') in H1; try assumption.
    constructor; try assumption.
    inversion w; try assumption.
    assert (Z: WFDG ([(alpha, k)] ++ d0) g0).
    admit.
    assumption.
    assert (Z: WFDG ([(alpha, k)] ++ d0) (g0 ++ g')).
    admit.
    admit.
    assert (Z: WFDG ([(alpha, k)] ++ d0) (g0 ++ g')).
    admit.
    apply H with (u':= u') in Z.
    assumption.
    admit.
    assumption.
    assumption.
   Case "base".
    assumption.
Qed.

*)


Lemma htyp_weakening:
 forall (u : Upsilon) (g : Gamma),  
   htyp u  g [] [] ->
   WFC [] u g -> 
   forall (u' : Upsilon) (g' : Gamma),
    WFC [] u' g' -> 
    WFC [] (u ++ u') (g ++ g') -> 
    htyp (u ++ u') (g ++ g') [] [].
Proof.
  intros u g htypder.
  intros.
  htyp_ind_cases (induction htypder) Case.
  Case "htyp u g [] []".
   constructor.
  Case "htyp u g h ([(x, tau)] ++ g')".
   pose proof H as H'.
   apply A_2_Term_Weakening_3 with (u':= u') (g':= g') (u:= u) (g:= g) 
                                             (tau:= tau) (e:= v)
     in H; try assumption.
   apply htyp_xv with (h':= h') (v:= v); try assumption.
   apply IHhtypder in H'.
   assumption.
   assumption.
Qed.



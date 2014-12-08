(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  These are lemmas required to allow the weakening of various partial
  mapping and typing judgements.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Export FormalSyntax.
Require Export DynamicSemanticsHeapObjects.
Require Export StaticSemanticsTypingHeapObjects.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemantics.
Require Export TacticNotations.
Require Export ListLemmas.
Require Export GetLemmasRelation.

(* Used. *)
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

(* Used. *)
Lemma gettype_weakening:
  forall (u : Upsilon) (x : EVar) (tau' tau : Tau) (p : P),
    WFU u ->
    gettype u x [] tau' p tau ->
    forall (u' : Upsilon), 
      WFU (u ++ u') ->
      gettype (u ++ u') x [] tau' p tau.
Proof.
  intros u x tau' tau p WFUder gettypeder.
  gettype_ind_cases(induction gettypeder) Case.
  Case "gettype u x p tau [] tau".
   constructor.
  Case "gettype u x p (cross t0 t1) (i_pe zero_pe :: p') tau".
   intros.
   apply IHgettypeder with (u':=u') in WFUder.
   constructor.
   assumption.
   assumption.
  Case "gettype u x p (cross t0 t1) (i_pe one_pe :: p') tau".
   intros.
   apply IHgettypeder with (u':=u') in WFUder.
   constructor.
   assumption.
   assumption.
  Case "gettype u x p (etype aliases alpha k tau') (u_pe :: p') tau)".
   intros.
   apply IHgettypeder with (u':=u') in WFUder.
   apply gettype_etype with (tau'':= tau'').
   apply getU_Some_Weakening.
   assumption.
   assumption.
   assumption.
Qed.

Lemma WFU_weakening:
 forall (u u' : Upsilon),
   WFU (u ++ u') ->
   WFU u.
Proof.
  intros.
  induction u.
  constructor.
  destruct a.
  destruct p.
  apply WFU_A.
  admit. (* Alpha Conversion. *)
  inversion H.
  apply IHu in H5.
  assumption.
  (* How do I get an A kinding ? Invert on variables ?*)
  destruct t.
  Case "K [] (tv_t t) A".
   inversion H.
   assumption.
   constructor.
  Case "K [] cint B".
   apply K_int.
  Case "K [] (cross t1 t2) A".
   apply K_cross.
   inversion H.
   inversion H6.
   inversion H7.
   assumption.
   inversion H.
   inversion H6.
   inversion H7.
   assumption.
  Case "K [] (arrow t1 t2) A".
   apply K_arrow.
   inversion H.
   inversion H6.
   inversion H7.
   assumption.
   inversion H.
   inversion H6.
   inversion H7.
   assumption.
  Case "K [] (ptype t) A".
   constructor.
   apply K_ptype.
   inversion H.
   inversion H6.
   inversion H7.
   inversion H12.
   destruct alpha.
   inversion H14.
   assumption.
  Case "K [] (utype t k t0) A".
   apply K_utype.
   rewrite app_nil_r.
   constructor.
   simpl.
   destruct t.
   reflexivity.
   constructor.
   simpl.
   destruct t.
   reflexivity.
   inversion H.
   inversion H6.
   inversion H7.
   assumption.
  Case "K [] (etype p0 t k t0) A".
   apply K_etype.
   rewrite app_nil_r.
   constructor.
   simpl.
   destruct t.
   reflexivity.
   constructor.
   simpl.
   destruct t.
   reflexivity.
   inversion H.
   inversion H6.
   inversion H7.
   assumption.
Qed.

Lemma WFDG_g_weakening:
  forall (d : Delta) (g g' : Gamma),
    WFDG d (g ++ g') ->
    WFDG d g.
Proof.
  intros.
  induction g.
  Case "g = []".
   rewrite app_nil_l in H.
   constructor.
   inversion H.
   crush.
  Case "a :: g'". 
   constructor.
   apply getG_None_Strengthening with (g':=g').
   assumption.
   assumption.
   assumption.
  Case "(alpha,k) :: d0".
   constructor.
   assumption.
   destruct a.
   constructor.
   inversion H1.
   apply getG_None_Strengthening with (g':=g').   
   assumption.
   admit. (* Alpha Conversion. *)
   admit. (* K? *)
   crush.
   inversion H.
   admit. (* TODO *)
   admit.
Qed.

(* All unused after this. *)

Lemma WFD_weakening:
 forall (d d' : Delta),
   WFD (d ++ d') ->
   WFD d.
Proof.
   intros.
   induction d.
  Case "d=[]".
   constructor.
  Case "a :: d'".
   inversion H.
   apply IHd in H3.
   constructor. 
   admit. (* Alpha Conversion. *)
   assumption.
Qed.



(* jrw what is wrong here ? *)
Lemma WFDG_d_weakening:
  forall (d d' : Delta) (g  : Gamma),
    WFDG (d ++ d') g ->
    WFDG d g.
Proof.
  intros d d' g WFDGder.
  induction WFDGder.
  Case "g = []".
   constructor.
  Case "[(x,tau] ++ g".
   constructor.
   admit. (* Alpha Conversion. *)
   admit. (* induction wrong, d0 instead of d. *)
   assumption.
   admit.
Qed.

Lemma WFDG_d_weakening2:
  forall (d d' : Delta) (g  : Gamma),
    WFDG (d ++ d') g ->
    WFDG d g.
Proof.
 (*
  intros d d' g WFDGder.
  apply (WFDG_ind
           (fun (d : Delta) (g: Gamma) =>
                WFDG (d ++ d') g ->
                WFDG d g)).
  Case "g = []".
   intros.
   constructor.
  Case "[(x,tau] ++ g".
   intros.
   constructor.
   inversion H3.
   assumption.
   assumption.
   assumption.
   admit. (* TODO *)
  Case "d ++ d'".
   induction g.
   SCase "g = []".
    constructor.
    assumption.
    assumption.
   SCase "a :: g".
    inversion WFDGder.
    destruct a.
    constructor.
    assumption.
    apply IHg in H4.
    crush.
    rewrite cons_is_append_singleton in WFDGder.
    inversion WFDGder.
    apply IHg in H8.
    destruct g.
    crush.
    destruct e.
    admit. (* How do I get this to go away ? *)
    inversion WFDGder.
    admit. (* K weakening ? *)
    admit.
    (* Lemma time I think. *)
    apply IHg in H4.
    assumption.
  Case "(d ++ d') g".
   assumption.
  *)
Admitted.

Lemma WFDG_weakening:
  forall (d d' : Delta) (g g' : Gamma),
    WFDG (d ++ d') (g ++ g') ->
    WFDG d g.
Proof.
  intros.
  apply WFDG_d_weakening in H.
  apply WFDG_g_weakening in H.
  assumption.
Qed.

Lemma WFC_g_weakening:
  forall (d : Delta) (u : Upsilon) (g : Gamma)
         (x : EVar) (tau : Tau),
    WFC d u ([(x, tau)] ++ g) ->
    WFC d u g.
Proof.
  intros d u g x tau WFCder.
 (*  induction WFCder. *) (* jrw Bug, g0 not connected to g. *)
  apply (WFC_ind
           (fun (d : Delta) (u : Upsilon) (g : Gamma) =>
              WFC d u ([(x, tau)] ++ g) ->
              WFC d u g)).
  intros.
  Case "WFC d0 u0 g0".
   constructor; try assumption.
  Case "WFC d u g".
   inversion WFCder.
   inversion H0.
   admit. (* Have to break stuff down and build up the right WFC. *)
   admit.
   admit.
Qed.

Lemma WFC_weakening:
  forall (d d': Delta) (u u' : Upsilon) (g g': Gamma),
    WFC (d ++ d') (u ++ u') (g ++ g') ->
    WFC d u g.
Proof.
  intros d d' u u' g g' WFCder.
  apply (WFC_ind
           (fun (d : Delta) (u : Upsilon) (g : Gamma) =>
              WFC (d ++ d') (u ++ u') (g ++ g') ->
              WFC d u g)).
  intros.
  Case "WFC d0 u0 g0".
   constructor; try assumption.
  Case "WFC d u g".
   inversion WFCder.
   crush.
   apply WFD_weakening in H; try assumption.
   apply WFU_weakening in H1; try assumption.
   apply WFDG_weakening in H0; try assumption.
   constructor; try assumption.
   assumption.
Qed.

(* Don't actually need this. 
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
    admit. (* Alpha conversion. *)
    apply WFDG_xt with (d:=d0) (tau:=tau') in e1; try assumption.
    apply H with (u':= u') (g':= g') in e1; try assumption.
    inversion e1; try assumption.
    admit. (* Where ? *)
    admit. (* And this K is from inverting that. *)
    apply H0 with (u':= u') (g':= g')in H1; try assumption.
   Case "styp_open_3_7".
    intros.
    apply styp_open_3_7 with (p:= p) (k:= k) (tau':= tau'); try assumption.
    admit. (* Alpha Conversion. *)
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
    admit. (* Alpha Conversion. *)
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
    admit. (* Alpha Conversion. *)
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
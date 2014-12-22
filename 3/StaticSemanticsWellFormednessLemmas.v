(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

   Lemmas about static semantics context well formedness.

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
Require Export VarLemmas.
Require Export GetLemmasRelation.

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

Lemma NotInDomU_weakening:
  forall (u u' : Upsilon) (x : EVar) (p : P),
    WFU (u ++ u') ->
    NotInDomU (u ++ u') x p ->
    NotInDomU u x p.
Proof.
  intros u u' x p.
  induction u.
  Case "u = []".
   rewrite app_nil_l.
   intros.
   constructor.
  Case "a::u".
   intros.
   destruct a.
   destruct p0.
   case_eq (beq_evar x e); case_eq (beq_path p p0).
   intros.
   inversion H.
   apply IHu in H8.
   unfold NotInDomU.
   fold NotInDomU.
   rewrite H1.
   rewrite H2.
   simpl.
   tauto.
   apply beq_evar_eq in H2.
Admitted.  

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
  inversion H.
  apply NotInDomU_weakening with (u':= u') (x:= e) (p:= p) in H5; try assumption.
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
   (* 
   destruct alpha. (* beq_tvar bug. *)
   inversion H14.
   assumption.
    *) 
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
   AdmitAlphaConversion.
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
   AdmitAlphaConversion.
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
   AdmitAlphaConversion.
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

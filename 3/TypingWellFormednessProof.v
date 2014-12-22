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
Require Export GetLemmasRelation.
Require Export ListLemmas.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export DynamicSemanticsTypeSubstitution.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemantics.
Require Export TypeSafety.
Require Export CpdtTactics.
Require Export Case.
Require Export TacticNotations.

Require Export ContextWeakeningProof.
Require Export SubstitutionsProof.


Lemma A_7_Typing_Well_Formedness_1 :
  forall (u : Upsilon),
    WFU u ->
    forall (d: Delta) (tau : Tau),
      K d tau A ->
      forall (x : EVar) (tau' : Tau) (p p' : P),
        gettype u x p tau p' tau' ->
        K d tau' A.
Proof.
  intros u WFUder d tau Kder x tau' p p' gettypeder.
  gettype_ind_cases (induction gettypeder) Case.
  Case "gettype u x p tau [] tau".
   assumption.
  Case "gettype u x p (cross t0 t1) (i_pe zero_pe :: p') tau".
   inversion Kder.
   inversion H.
   apply IHgettypeder in WFUder.
   assumption.
   assumption.
  Case "gettype u x p (cross t0 t1) (i_pe one_pe :: p') tau".
   inversion Kder.
   inversion H.
   apply IHgettypeder in WFUder.
   assumption.
   assumption.
  Case "gettype u x p (etype aliases alpha k tau') (u_pe :: p') tau)".
   apply IHgettypeder in WFUder. 
   assumption.
   inversion Kder.
   inversion H0.
   apply A_1_Context_Weakening_2 with (u:= u) (x:= x) (p:= p) (d:= d) (tau:= tau'')
     in WFUder; try assumption.
   apply A_6_Substitution_1 with (k:= k) (tau:= tau''); try assumption.
   constructor.
   destruct k; try assumption.
   admit. (* K d tau'' B *)
   inversion H4.
   assumption.
Qed.

Lemma A_7_Typing_Well_Formedness_2 :
  forall (d: Delta) (u : Upsilon) (g : Gamma) (e : E) (tau : Tau),
    ltyp d u g e tau ->
    (WFC d u g /\ 
     K d tau A).
Proof.
  intros d u g e tau ltypder.
  ltyp_ind_mutual_cases
   (apply (ltyp_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (tau : Tau) (s : St)
                (st : styp d u g tau s) => 
              (WFC d u g /\  K d tau A))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau : Tau)
                (lt : ltyp d u g e tau) =>
              (WFC d u g /\  K d tau A))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau : Tau)
                (rt : rtyp d u g e tau) =>
              (WFC d u g /\  K d tau A))) with (e:=e))
  Case.
 
  (* Crush gets 21/27 subgoals. *)
  (* But let's look at some cases, these two are just induction hypothesis really.*)
  (* Let's look at the uncrushed cases and see if I can see where these unsolvable things are comging from. *)

  Ltac twf0  := intros; assumption.

  Ltac twf1 := 
    try (intros;
         try inversion H1;
         try inversion H;
         try assumption).

  Ltac twf2 :=
    try (intros;
         try constructor;
         try constructor;
         try assumption).

  Ltac twf3 :=
    try (intros;
         inversion H;
         split; try assumption;
         inversion H1;
         inversion H2;
         assumption).

  Case "styp_e_3_1".
   twf0. (* This has been done by changing the return statement to be deterministally typed. *)
  Case "styp_return_3_2".
   twf0.
  Case "styp_seq_3_3".
   twf0.
  Case "styp_while_3_4".
   twf0.
  Case "styp_if_3_5".
   twf0.
  Case "styp_let_3_6".
   crush.
  Case "styp_open_3_7".
   crush.
  Case "styp_openstar_3_8".
   crush.
  Case "SL_3_1".
   intros.
   split; try assumption.
   apply A_7_Typing_Well_Formedness_1 with
    (u:= u0) (tau:= tau') (x:= x) (p:=[]) (p':= p). 
   inversion w.
   assumption.
   assumption.
   assumption.
  Case "SL_3_2".
   intros.
   inversion H.
   split; assumption.
  Case "SL_3_3".
   twf3.
  Case "SL_3_4".
   twf3.
  Case "SR_3_1".
   intros.
   split.
   assumption.
   apply A_7_Typing_Well_Formedness_1 with
    (u:= u0) (tau:= tau') (x:= x) (p:=[]) (p':= p). 
   inversion w.
   assumption.
   assumption.
   assumption.
  Case "SR_3_2".
   intros.
   inversion H.
   split; try assumption.
  Case "SR_3_3".
   twf3.
  Case "SR_3_4".
   twf3.
  Case "SR_3_5".
   intros.
   split.
   assumption.
   constructor.
   constructor.
  Case "SR_3_6".
   intros.
   inversion H.
   split.
   assumption.
   constructor.
   constructor.
   assumption.
  Case "SR_3_7".
   intros.
   inversion H.
   split.
   assumption.
   apply K_cross.
   assumption.
   inversion H0.
   assumption.
  Case "SR_3_8".
   crush.
  Case "SR_3_9".
   intros.
   inversion H.
   split.
   assumption.
   inversion H2.
   inversion H3.
   assumption.
  Case "SR_3_10".
   twf0.
  Case "SR_3_11".
   intros.
   inversion H.
   split.
   assumption.
   apply A_6_Substitution_1 with (k:=k).
   inversion H1.
   inversion H2.
   assumption.
   assumption.
  Case "SR_3_12".
   twf3.
  Case "SR_3_13".
   intros.
   split.
   inversion H.
   rewrite <- app_nil_r with (l:= d0) in H0.
   rewrite <- app_nil_r with (l:= u0) in H0.
   (* Need a lemma saying I can rearrange the context Gamma. *)
   apply WFC_weakening with (d:= d0) (d':=[]) (u:= u0) (g':= g0)
     in H0.
   admit. (* assumption.*)
   apply K_arrow.
   inversion H.
   (* WFDG to K d0 tau0 A.*)
   inversion H0; try assumption.
   inversion H3; try assumption.
   inversion H; try assumption.
   (* WFDG d2 to K d2 tau0 A. *)
   admit.
   inversion H; try assumption.
  Case "SR_3_14".
   intros.
   split.
   assumption.
   apply K_utype.
   admit.
   assumption.
   admit.
  Case "base".
   assumption.
Qed.

Lemma A_7_Typing_Well_Formedness_3 :
  forall (d: Delta) (g : Gamma) (u : Upsilon) (tau : Tau) (e : E),
    rtyp d u g e tau ->
    (WFC d u g /\ 
     K d tau A).
Proof.
  intros d g u tau e rtypder.
  rtyp_ind_mutual_cases
   (apply (rtyp_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (tau : Tau) (s : St)
                (st : styp d u g tau s) => 
              (WFC d u g /\  K d tau A))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau : Tau)
                (lt : ltyp d u g e tau) =>
              (WFC d u g /\  K d tau A))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau : Tau)
                (rt : rtyp d u g e tau) =>
              (WFC d u g /\  K d tau A))) with (e:=e))
   Case.
  (* Wow crush gets 21/26. *)

    
Case "styp_e_3_1".
   twf0. (* This has been done by changing the return statement to be deterministally typed. *)
  Case "styp_return_3_2".
   twf0.
  Case "styp_seq_3_3".
   twf0.
  Case "styp_while_3_4".
   twf0.
  Case "styp_if_3_5".
   twf0.
  Case "styp_let_3_6".
   crush.
  Case "styp_open_3_7".
   crush.
  Case "styp_openstar_3_8".
   crush.
  Case "SL_3_1".
   intros.
   split; try assumption.
   apply A_7_Typing_Well_Formedness_1 with
    (u:= u0) (tau:= tau') (x:= x) (p:=[]) (p':= p). 
   inversion w.
   assumption.
   assumption.
   assumption.
  Case "SL_3_2".
   intros.
   inversion H.
   split; assumption.
  Case "SL_3_3".
   twf3.
  Case "SL_3_4".
   twf3.
  Case "SR_3_1".
   intros.
   split.
   assumption.
   apply A_7_Typing_Well_Formedness_1 with
    (u:= u0) (tau:= tau') (x:= x) (p:=[]) (p':= p). 
   inversion w.
   assumption.
   assumption.
   assumption.
  Case "SR_3_2".
   intros.
   inversion H.
   split; try assumption.
  Case "SR_3_3".
   twf3.
  Case "SR_3_4".
   twf3.
  Case "SR_3_5".
   intros.
   split.
   assumption.
   constructor.
   constructor.
  Case "SR_3_6".
   intros.
   inversion H.
   split.
   assumption.
   constructor.
   constructor.
   assumption.
  Case "SR_3_7".
   intros.
   inversion H.
   split.
   assumption.
   apply K_cross.
   assumption.
   inversion H0.
   assumption.
  Case "SR_3_8".
   crush.
  Case "SR_3_9".
   intros.
   inversion H.
   split.
   assumption.
   inversion H2.
   inversion H3.
   assumption.
  Case "SR_3_10".
   twf0.
  Case "SR_3_11".
   intros.
   inversion H.
   split.
   assumption.
   apply A_6_Substitution_1 with (k:=k).
   inversion H1.
   inversion H2.
   assumption.
   assumption.
  Case "SR_3_12".
   twf3.
  Case "SR_3_13".
   intros.
   split.
   inversion H.
   (* 
   apply WFC_weakening in H0.
   assumption.
   apply K_arrow.
    *)
   admit.
   admit.
  Case "SR_3_14".
   intros.
   split.
   assumption.
   apply K_utype.
   admit. (* assumption.*)
   inversion H.
   assumption.
   admit.
  Case "base".
   assumption.
Qed.

Lemma A_7_Typing_Well_Formedness_4 :
  forall (d: Delta) (g : Gamma) (u : Upsilon) (tau : Tau) (s : St),
    styp d u g tau s ->
    WFC d u g.
Proof.
  intros d g u tau s stypder.
  (styp_ind_mutual_cases
    (apply (styp_ind_mutual
              (fun (d : Delta) (u : Upsilon) (g : Gamma) (tau : Tau) (s : St)
                   (st : styp d u g tau s) => 
                 WFC d u g)
              (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau : Tau)
                   (lt : ltyp d u g e tau) =>
                 WFC d u g)
              (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau : Tau)
                   (rt : rtyp d u g e tau) =>
                 WFC d u g)) with (t:=tau) (s:=s))
    Case); crush.
  Case "SR_3_13".
   intros.
   split.
   inversion H.
   assumption.
   inversion H.
   inversion H1.
   assumption.
   admit. (* TODO come back and fix this. *)
   admit.
Qed.

Lemma A_7_Typing_Well_Formedness_5 :
  forall (d: Delta) (g : Gamma) (u : Upsilon) (tau : Tau) (s : St),
    styp d u g tau s ->
    ret s ->
    K d tau A.
Proof.
  intros d g u tau e stypder.
  (* TODO, do I need the ret in the l and r cases? *)
  apply (styp_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (tau : Tau) (s : St)
                (st : styp d u g tau s) => 
                 ret s ->
                 K d tau A)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau : Tau) 
                (lt : ltyp d u g  e tau) =>
                 K d tau A)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau : Tau) 
                (rt : rtyp d u g e tau) =>
                 K d tau A)) with (u:= u) (g:= g).

  Ltac twf4 :=
    try (intros;
         try inversion H;
         try inversion H1;
         try crush).
  Case "styp_e_3_1".
   crush.
  Case "styp_return_3_2".
   crush.
  Case "styp_seq_3_3".
   intros.
   inversion H1.
   apply H in H3.
   assumption.
   apply H0 in H3.
   assumption.
  Case "styp_while_3_4".
   intros.
   inversion H1.
  Case "styp_if_3_5".
   intros.
   inversion H2.
   apply H1 in H7.
   assumption.
  Case "styp_let_3_6".
   twf4.
  Case "styp_open_3_7".
   crush.
  Case "styp_openstar_3_8".
   crush.
  Case "SL_3_1".
   intros.
   (* Lemma *)
   admit.
  Case "SL_3_2".
   crush.
  Case "SL_3_3".
   intros.
   inversion H.
   inversion H0.
   assumption.
  Case "SL_3_4".
   intros.
   inversion H.
   inversion H0.
   assumption.
  Case "SR_3_1".
   admit.
  Case "SR_3_2".
   crush.
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
   (* Looks broken. *)
   admit.
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
   crush.
  Case "SR_3_9".
   intros.
   admit. 
  Case "SR_3_10".
   crush.
  Case "SR_3_11".
   intros.
   inversion H.
   apply A_6_Substitution_1 with (k:=k).
   admit.
   assumption.
   admit.
  Case "SR_3_12".
   crush.
  Case "SR_3_13".
   admit.
  Case "SR_3_14".
   intros.
   apply K_utype.
   admit.
   assumption.
   assumption.
  Case "base".
   crush.
Qed.

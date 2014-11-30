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
Require Export Case.
Require Export ContextWeakeningProof.
Require Export SubstitutionsProof.

Lemma A_7_Typing_Well_Formedness_1 :
  forall (u : Upsilon),
    WFU u ->
    forall (d: Delta) (tau : Tau),
      K d tau A ->
      forall (x : EVar) (tau' : Tau) (p p' : P),
        gettype u x p tau p' = Some tau' ->
        K d tau' A.
Proof.
  intros u WFUder d tau Kder x tau' p p'. 
  functional induction (gettype u x p tau p'); crush.   (* Wow, crush gets 23/26. *)
  Case "p ++ zero_pe".
   induction p'0.      (* Ask Dan, is this what you mean ? *)
   (* Wow inversion on Kder seems to be looping. *)
   inversion Kder.
   SCase "K d (cross t0 t1) B".
    inversion H.
   SCase "K d (cross t0 t1) A".
    apply IHo in H2.
    assumption.
    assumption.
    inversion Kder.
    inversion H.
    apply IHo in H2.
    assumption.
    assumption.
  Case "p ++ one_pe".
   inversion Kder.
   inversion H.
   apply IHo in H3.
   assumption.
   assumption.
  Case "etype".
   inversion Kder.
   inversion H.
   inversion e4.
   apply A_1_Context_Weakening_2 with (u:=u) (x:=x) (p:=p).
   assumption.
   apply A_6_Substitution_1 with (tau:=tau'0) in H5.
   admit.
   admit.
Qed.

Lemma A_7_Typing_Well_Formedness_2 :
  forall (d: Delta) (u : Upsilon) (g : Gamma) (e : E) (tau : Tau),
    ltyp d u g e tau ->
    (WFC d u g /\ 
     K d tau A).
Proof.
  intros d u g e tau ltypder.
  apply (ltyp_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (tau : Tau) (s : St)
                (st : styp d u g tau s) => 
              (WFC d u g /\  K d tau A))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau : Tau)
                (lt : ltyp d u g e tau) =>
              (WFC d u g /\  K d tau A))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau : Tau)
                (rt : rtyp d u g e tau) =>
              (WFC d u g /\  K d tau A))) with (e:=e).
 
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
   assumption.
   inversion H1.
   inversion H2.
   assumption.
  Case "SR_3_12".
   twf3.
  Case "SR_3_13".
   admit.
  Case "SR_3_14".
   intros.
   split.
   assumption.
   apply K_utype.
   inversion H.
   assumption.
   assumption.
  Case "?".
   assumption.
Qed.

Lemma A_7_Typing_Well_Formedness_3 :
  forall (d: Delta) (g : Gamma) (u : Upsilon) (tau : Tau) (e : E),
    rtyp d u g e tau ->
    (WFC d u g /\ 
     K d tau A).
Proof.
  intros d g u tau e rtypder.
  apply (rtyp_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (tau : Tau) (s : St)
                (st : styp d u g tau s) => 
              (WFC d u g /\  K d tau A))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau : Tau)
                (lt : ltyp d u g e tau) =>
              (WFC d u g /\  K d tau A))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau : Tau)
                (rt : rtyp d u g e tau) =>
              (WFC d u g /\  K d tau A))) with (e:=e).
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
   assumption.
   inversion H1.
   inversion H2.
   assumption.
  Case "SR_3_12".
   twf3.
  Case "SR_3_13".
   admit.
  Case "SR_3_14".
   intros.
   split.
   assumption.
   apply K_utype.
   inversion H.
   assumption.
   assumption.
  Case "?".
   assumption.
Qed.

Lemma A_7_Typing_Well_Formedness_4 :
  forall (d: Delta) (g : Gamma) (u : Upsilon) (tau : Tau) (s : St),
    styp d u g tau s ->
    WFC d u g.
Proof.
  intros d g u tau s stypder.
  apply (styp_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (tau : Tau) (s : St)
                (st : styp d u g tau s) => 
              WFC d u g)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau : Tau)
                (lt : ltyp d u g e tau) =>
              WFC d u g)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau : Tau)
                (rt : rtyp d u g e tau) =>
              WFC d u g)) with (t:=tau) (s:=s); crush.
  Case "SR_3_13".
   admit.
Qed.

Lemma A_7_Typing_Well_Formedness_5 :
  forall (d: Delta) (g : Gamma) (u : Upsilon) (tau : Tau) (s : St),
    styp d u g tau s ->
    ret s ->
    K d tau A.
Proof.
  intros d g u tau e stypder.
  (* Todo, do I need the ret in the l and r cases? *)
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
   (* Looks fucked up. *)
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
   assumption.
   inversion H0.
   admit.
  Case "SR_3_12".
   crush.
  Case "SR_3_13".
   admit.
  Case "SR_3_14".
   intros.
   apply K_utype.
   assumption.
   assumption.
  Case "?".
   crush.
Qed.

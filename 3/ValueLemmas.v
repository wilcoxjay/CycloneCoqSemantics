(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Lemmas about values. 

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

Require Export StaticSemanticsWellFormednessLemmas.

(* Interesting but do I really need it? 
   And can I constructively prove it? *)
(* I should just admit classical logic. *)
Lemma value_or_not:
  forall (e : E),
    Value e \/ ~ Value e.
Proof.
  intros.
  Ltac is_value := 
   try (
       left; 
        try constructor).
  Ltac is_not_value :=
   try (
       right; 
       compute; 
       intros;
       inversion H).

  E_ind_cases (induction e) Case.
  Case "(i_e i)".
   is_value.
  Case  "(p_e e l)".
   is_not_value.
  Case  "(f_e f1)".
   left.
   destruct f.
   constructor.
   constructor.
  Case  "(amp e)".
  (* destruct e.
   inversion IHe.
   inversion H. *)
   admit.
  Case  "(star e)".
   admit.
  Case  "(cpair e e0)".
   admit.
  Case  "(dot e i)".
   admit.
  Case  "(assign e e0)".
   admit.
  Case  "(appl e e0)".
   admit.
  Case  "(call s)".
   admit.
  Case  "(inst e t)".
   admit.
  Case  "(pack t e t0)".
   admit.
Admitted.
  
Lemma rtyp_value_d_strengthening_Value:
  forall (e : E),
    Value e ->
    forall (d : Delta) (u : Upsilon) (g : Gamma) (tau : Tau),
    rtyp d  u g e tau ->
    rtyp [] u g e tau.
Proof.
  intros e Valuee.
  Value_ind_cases (induction Valuee) Case.
  Case "(i_e i)".
   intros.
   destruct i.
   destruct tau; try inversion H.
   constructor.
   (* Stuck at WFC [] u g. *)
   admit.
  Case "(amp (p_e x p))".
   admit.
  Case "(f_e (dfun t1 x t2 s))".
   admit.
  Case "(f_e (ufun t k f2))".
   admit.
  Case "(cpair v0 v1)".
   admit.
  Case "(pack tau v tau')".
   admit.
Qed.

(* Heck might even need mutual induction. *)
(* Needs ltyp_d_strengthening, rtyp_d_strengthening, ... *)
(* Sketchy use of WFC strengthening which I don't know is true. *)
Lemma rtyp_value_d_strengthening_rtyp_ind:
  forall (e : E),
    Value e ->
    forall (d : Delta) (u : Upsilon) (g : Gamma) (tau : Tau),
    rtyp d u g e tau ->
    rtyp [] u g e tau.
Proof.
  intros e Valuee d u g tau rtypder.

  rtyp_ind_mutual_cases_2base (
      apply (rtyp_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) =>
              styp d u g t s ->
              s = (e_s e) ->
              rtyp [] u g e t)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (lt : ltyp d u g  e t) =>
              ltyp d u g  e t ->
              rtyp [] u g e t)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              rtyp d u g e t -> 
              rtyp [] u g e t)) with (d:=d)) Case.
  Case "styp_e_3_1".
   intros.
   (* Connecting now, but is it right? s = (e_s e). *)
   inversion H1.
   rewrite <- H3.
   apply H in r; try assumption.
   (* disconnected e *)
   admit.
  Case "styp_return_3_2".
   intros.
   inversion H1. (* Now is this really true that I don't care about that case? *)
  Case "styp_seq_3_3".
   intros.
   inversion H2.
  Case "styp_while_3_4".
   intros.
   inversion H2.
  Case "styp_if_3_5".
   intros.
   inversion H3.
  Case "styp_let_3_6".
   intros.
   inversion H2.
  Case "styp_open_3_7".
   intros.
   inversion H2.
  Case "styp_openstar_3_8".
   intros.
   inversion H2.
  Case "SL_3_1".
   intros.
   apply SR_3_1 with (tau':= tau'); try assumption.
   admit. (* K [] tau' A *)
   admit. (* WFC [] u0 g0 *)
  Case "SL_3_2".
   admit.
  Case "SL_3_3".
   admit.
  Case "SL_3_4".
   admit.
  Case "SR_3_1".
   admit.
  Case "SR_3_2".
   admit.
  Case "SR_3_3".
   admit.
  Case "SR_3_4".
   admit.
  Case "SR_3_5".
   admit.
  Case "SR_3_6".
   admit.
  Case "SR_3_7".
   admit.
  Case "SR_3_8".
   admit.
  Case "SR_3_9".
   admit.
  Case "SR_3_10".
   admit.
  Case "SR_3_11".
   admit.
  Case "SR_3_12".
   admit.
  Case "SR_3_13".
   admit.
  Case "SR_3_14".
   admit.
  Case "base".
   assumption.
  Case "base2".
   assumption.
Qed.

(* Induction cases, not going to work. 
  rtyp_ind_cases (induction rtypder) Case; try solve [inversion Valuee].

  Case "rtyp d u g (i_e (i_i z)) cint".
   constructor.
   apply WFC_strengthening with (d':= d) (u':= []) (g':= []).
   rewrite app_nil_l.
   rewrite app_nil_r.
   rewrite app_nil_r.
   assumption.
  Case "rtyp  d u g (amp e) (ptyp tau)".
   constructor.
  Case "rtyp d u g (cpair e0 e1) (cross t0 t1)".
   admit.
  Case "rtyp  d u g (pack tau' e (etype p alpha k tau)) (etyp p alpha k tau)".
   admit.
  Case "rtyp d u g (f_e (dfun tau x tau' s)) (arrow tau tau')".
   admit.
  Case "rtyp  d u g (f_e (ufun alpha k f12)) (utyp alpha k tau))".
   admit.
*)

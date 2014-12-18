(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Defining type safety, page 67.

*)

(* Done modulo Kappa bug in K_nil_A. *)
Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.
Require Import Coq.Program.Equality.

Require Export FormalSyntax.
Require Export GetLemmasRelation.
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
Require Export GetLemmasRelation.
Require Export AlphaConversion.
Require Export WeakeningLemmas.
Require Export VarLemmas.
Require Export PathLemmas.

Lemma A_1_Context_Weakening_1:
  forall (d : Delta) (tau : Tau) (k : Kappa),
    WFD d -> 
    K d tau k ->
    forall (d' : Delta), 
      WFD (d ++ d') -> 
      K (d ++ d') tau k.
Proof.
  intros d tau k WFDder Kder.
  K_ind_cases (induction Kder) Case.
  Case "K d cint B".
   intros.
   constructor.
  Case "K d (tv_t alpha) B".
   intros.
   apply K_B.
   apply getD_Some_Weakening.
   assumption.
   assumption.
  Case "K d (ptype (tv_t alpha)) B".
   intros.
   constructor.
   apply getD_Some_Weakening.
   assumption.
   assumption.
  Case "K d tau A".
   intros.
   constructor.
   apply IHKder.
   assumption.
   assumption.
  Case "K d (cross t0 t1) A".
   intros.
   apply K_cross.
   apply IHKder1.
   assumption.
   assumption.
   apply IHKder2.
   assumption.
   assumption.
Case "K d (arrow t0 t1) A".
   intros.
   apply K_arrow.
   apply IHKder1.
   assumption.
   assumption.
   apply IHKder2.
   assumption.
   assumption.
  Case "K d (ptype tau) B".
   intros.
   apply K_ptype.
   apply IHKder.
   assumption.
   assumption.
  Case "K d (utype alpha k tau) A".
   intros.
   apply K_utype. 
   constructor.
   apply alpha_conversion_punt_getD with (k:=k).
   assumption.
   assumption.
   assumption.
   apply alpha_conversion_punt_getD with (k:=k).
   assumption.
   assumption.
   apply IHKder with (d':= d') in H. 
   assumption.
   constructor.
   apply alpha_conversion_punt_getD with (k:=k).
   assumption.
   assumption.
   assumption.

  Case "K d (etype p alpha k tau) A)".
   intros.
   apply K_etype.
   constructor.
   apply alpha_conversion_punt_getD with (k:=k).
   assumption.
   assumption.
   assumption.
   apply alpha_conversion_punt_getD with (k:=k).
   assumption.
   assumption.
   apply IHKder with (d':= d') in H. 
   assumption.
   constructor.
   apply alpha_conversion_punt_getD with (k:=k).
   assumption.
   assumption.
   assumption.
Qed.

Lemma K_nil_A:
  forall (d : Delta) (tau : Tau),
      K [] tau A -> 
        K d tau A.
Proof.
  intros d tau.
  apply (K_ind 
           (fun (d : Delta) (t : Tau) (k : Kappa) =>
              K [] t A -> 
                K d t A))
  with (k := A) (d:= d).

  Case  "K d cint B".
   intros.
   constructor.
   constructor.
  Case  "K d (tv_t alpha) B".
   intros.
   inversion H0. 
   inversion H1.
   inversion H6.
  Case  "K d (ptype (tv_t alpha)) B".
   intros.
   inversion H0.
   inversion H1.
   inversion H6.

   inversion H6.
   inversion H7.
   inversion H12.
  Case  "K d tau A".
   intros.
   apply H0 in H1.
   assumption.
  Case  "K d (cross t0 t1) A".
   intros.
   inversion H3.
   inversion H4.
   apply H0 in H7.
   apply H2 in H8.
   apply K_cross; try assumption.
  Case  "K d (arrow t0 t1) A".
   intros.
   inversion H3.
   inversion H4.
   apply H0 in H7.
   apply H2 in H8.
   apply K_arrow; try assumption.
   (* Zig Zag, old overholt and carpano antiqua rye manhattan. *)
  Case  "K d (ptype tau) B".
   intros.
   inversion H1.
   inversion H2.
   inversion H7.

   apply H0 in H7.
   constructor.
   apply K_ptype.
   assumption.
  Case  "K d (utype alpha k tau) A".
   intros.
   apply K_utype; try assumption.
  Case  "K d (etype p alpha k tau) A)".
   intros.
   apply K_etype; try assumption.
  Case "base".
   admit. (* WTF is this case, K d tau A with no assumptions? *)
Qed.  

Check K_nil_A.

(*
Lemma K_nil_k:
  forall (d : Delta) (tau : Tau) (k : Kappa),
    K [] tau k -> 
    K d tau k.
Proof.
  intros d tau k.
  apply (K_ind 
           (fun (d : Delta) (t : Tau) (k : Kappa) =>
              K [] tau k -> 
              K d t k)).
  Focus 10.
  Case  "K d cint B".
   intros.
   constructor.
   constructor.
  Case  "K d (tv_t alpha) B".
   intros.
   inversion H0. 
   inversion H1.
   assumption.
  Case  "K d (ptype (tv_t alpha)) B".
   intros.
   inversion H0.
   inversion H1.
   admit.
   admit.
   (* 
   inversion H6.

   inversion H6.
   inversion H7.
   inversion H12.
    *)
  Case  "K d tau A".
   intros.
   apply H0 in H1.
   assumption.
  Case  "K d (cross t0 t1) A".
   intros.
   inversion H3.
   inversion H4.
   apply H0 in H7.
   apply H2 in H8.
   apply K_cross; try assumption.
  Case  "K d (arrow t0 t1) A".
   intros.
   inversion H3.
   inversion H4.
   apply H0 in H7.
   apply H2 in H8.
   apply K_arrow; try assumption.
   (* Zig Zag, old overholt and carpano antiqua rye manhattan. *)
  Case  "K d (ptype tau) B".
   intros.
   inversion H1.
   inversion H2.
   inversion H7.

   apply H0 in H7.
   constructor.
   apply K_ptype.
   assumption.
  Case  "K d (utype alpha k tau) A".
   intros.
   apply K_utype; try assumption.
  Case  "K d (etype p alpha k tau) A)".
   intros.
   apply K_etype; try assumption.
  Case "base".
   admit. (* WTF is this case, K d tau A with no assumptions? *)
Qed.  

*)

Lemma WFU_dont_extend_with_a_used_variable:
  forall (u : Upsilon),
      WFU u ->
      forall (x : EVar) (p : P) (tau: Tau),
        getU u x p tau -> 
         forall (tau' : Tau),
           ~WFU((x, p, tau') :: u).
Proof.
  (* Two choices, induction on WFU or getU. *)
  intros u WFUder.
  apply (WFU_ind 
          (fun (u : Upsilon) =>
             forall (x : EVar) (p : P) (tau: Tau),
               getU u x p tau -> 
               forall (tau' : Tau),
                 ~WFU((x, p, tau') :: u))).
  Case "WFU []".
   intros.    
   inversion H.
  Case "WFU ([(x, p, tau)] ++ u)".   
   intros.       
   case_eq(beq_evar x x0); case_eq(beq_path p p0); intros.
   SCase "x = x0, p = p0".
    pose proof H4.
    pose proof H5.
    apply beq_path_eq in H4.
    apply beq_evar_eq in H5.
    rewrite H4 in H3.
    rewrite H5 in H3.
    inversion H3.
    SSCase "get_top".
      crush. (* Nice gives me False so I have to invert it away. *)
      admit. (* TODO *)
    SSCase "get_next".
      crush.
   SCase "x = x0, p <> p0".
    pose proof H4.
    pose proof H5.
    apply beq_path_neq in H4.
    apply beq_evar_eq in H5.
    rewrite H5 in H3.
    inversion H3.
    SSCase "get_top".
     crush.
    SSCase "get_next".
     admit.
   SCase "x <> x0, p = p0".
    admit.
   SCase "x <> x0, p <> p0".
    admit.
  Case "base".
   assumption.
Qed.

(* Dan, should this really be WFD also? Probably not necessary really. *)
Lemma A_1_Context_Weakening_2:
  forall (u : Upsilon),
    WFU u ->
    forall (x : EVar) (p : P) (tau : Tau), 
    getU u x p tau ->
    forall (d : Delta),
      K d tau A.
Proof.
  intros u WFUder.
  apply (WFU_ind 
          (fun (u : Upsilon) =>
             WFU u -> 
             forall (x : EVar) (p : P) (tau : Tau), 
               getU u x p tau ->
               forall (d : Delta),
                 K d tau A)).
 Case "WFU []".
   intros.
   inversion H0.
 Case "WFU ([(x, p, tau)] ++ u)".
  intros.
  inversion H4. 
  SCase "getU_top".
   crush.
   apply K_nil_A with (d:= d) in H2.
   assumption.
   admit. (* TODO something is wrong with K_nil_A *)
  SCase "getU_next".
   case_eq (beq_evar x x0); case_eq (beq_path p p0); intros.
   SSCase "p = p0, x = x0".
    (* TODO this is really sketchy as I'm putting 
      getU ([(x, p, tau)] ++ u0) x0 p0 tau0 with x0 = x and p0 = p in this 
      context and using getU u0 x p tau. *)
   (* I should really invert this away or prove it without the induction 
       hypothesis.
    So WFU ([(x, p, tau)] ++ u0), WFU u0 and get u0 x p tau conflict. *)
    apply beq_evar_eq in H15.
    apply beq_path_eq in H14.
    rewrite H15 in H3.
    rewrite H14 in H3.
    apply WFU_dont_extend_with_a_used_variable 
          with (x:= x0) (p:= p0) (tau:= tau0) (tau':= tau)
      in H0; try assumption.
    compute in H0.
    apply H0 in H3.
    contradiction.
   SSCase "p <> p0, x = x0".
    specialize (H1 H0 x0 p0 tau0).
    apply H1 with (d:= d) in H13.
    assumption.
   SSCase "p = p0, x <> x0".
    specialize (H1 H0 x0 p0 tau0).
    apply H1 with (d:= d) in H13.
    assumption.
  SSCase "p <> p0, x <> x0".
   specialize (H1 H0 x0 p0 tau0).
   apply H1 with (d:= d) in H13.
   assumption.
 Case "base".
  assumption.
 Case "base again".  
  assumption.
Qed.

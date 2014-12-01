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
Require Import Coq.Program.Equality.

Require Export FormalSyntax.
Require Export GetLemmas.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export DynamicSemanticsTypeSubstitution.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemantics.
Require Export TypeSafety.
Require Export CpdtTactics.
Require Export Case.

(* Implementation/Thesis bug, I can't add a type variable in to a kinding context if it
 is already there. This is not checked in K_B and K_Star_A. 
 Perhaps there is prose defining this?)
 ASGN, K and AK all suffer from this.
 Also there really is no WFD judgement that should be doing that and should
  be part of any addition to a delta. So WFDG d [] should be used. 
*)

(* TODO this relies upon sketchy lemmas. *)
Lemma A_1_Context_Weakening_1:
  forall (d : Delta) (tau : Tau) (k : Kappa),
    K d tau k ->
    forall (d' : Delta), 
      K (d ++ d') tau k.
Proof.
  intros d tau k Kder.
  induction Kder.
  Case "K d cint B".
   intros.
   constructor.
  Case "K d (tv_t alpha) B".
   intros.
   apply K_B.
   apply getD_weakening_some_left.
   assumption.
  Case "K d (ptype (tv_t alpha)) B".
   intros.
   constructor.
   apply getD_weakening_some_left.
   assumption.
  Case "K d tau A".
   intros.
   constructor.
   apply IHKder.
  Case "K d (cross t0 t1) A".
   intros.
   apply K_cross.
   apply IHKder1.
   apply IHKder2.
  Case "K d (arrow t0 t1) A".
   intros.
   apply K_arrow.
   apply IHKder1.
   apply IHKder2.
  Case "K d (ptype tau) B".
   intros.
   apply K_ptype.
   apply IHKder.
  Case "K d (utype alpha k tau) A".
   intros.
   apply K_utype.
   (* Canon high west rye manhattan with carpano antiqua. *)
   (* This is really provable by the commutivity of a well formed Delta. *)
   (* But it requires that get (d ++ d') alpha = None so it needs more.*)
   admit.
   admit.
  Case "K d (etype p alpha k tau) A) =".
   intros.
   apply K_etype.
   admit.
   admit.
Qed.

(* Ask Dan Implementation bug, is there really an implicit statement
    that there are no duplicates in an Upsilon that I have missed? *)
(* TODO *)

Lemma get_lemma_extension_neq:
  forall (u : Upsilon) (x x' : nat) (p p': P) (t1 t2 t3: Tau),
    getU (u ++ [(p_e (evar x') p', t1)]) (evar x) p = Some t2 ->
    x <> x' -> 
    getU u (evar x) p = Some t3.
Proof.
Admitted.

Lemma A_1_Context_Weakening_2:
  forall (u : Upsilon),
    WFU u ->
    forall (d : Delta) (x : EVar) (p : P) (tau : Tau), 
      getU u x p = Some tau ->
      K d tau A.
Proof.
  intros u WFUder.
  induction WFUder.
  Case "u = nil".
   intros.
   destruct x.
   inversion H.
  Case "u ++ [(p_e x p, tau)]".
   intros.
   specialize (IHWFUder d x0 p0 tau0).
   apply IHWFUder.
   destruct x0.
   destruct x.
   assert (A: n <> n0 \/ n0 = n).
   omega.
   inversion A.
   apply get_lemma_extension_neq 
    with (x':=n0) (p:=p0) (p':=p) (t1:= tau) (t2:= tau0) (t3:=tau0).
   assumption.
   assumption.
   (* TODO Really should be inversion on the construction of u ++ here. *)
   admit.
Qed.

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
Lemma A_1_Context_Weakening_1:
  forall (d : Delta) (tau : Tau) (k : Kappa),
    K d tau k ->
    forall (d' : Delta), K (d ++ d') tau k.
Proof.
  intros d tau k Kder.
  induction Kder.
  (* crush gets zero. *)
(*  +Case "tau = cint". *)
  intros d'.
  apply K_int.
  (* 
  +Case "tau = (tv_t alpha)".
  (* TODO context match issue, not uniquness of alpha in d. *)
  (* apply K_B. *)
  intros d'.
*)
(*
  Focus 2.
  intros d'.
  apply K_star_A.

  specialize (IHKder d').
  apply K_B_A.
  exact IHKder.
  Focus 3.
  (* ... but I'm stuck on context match. *)
*)
Admitted.

(* TODO I'm going to have to get WFU u into the induction to keep the variable constraint
 from above. *)
Lemma A_1_Context_Weakening_2:
  forall (u : Upsilon) (d : Delta)
         (x : EVar) (p : P),
    WFU u ->
    forall (tau : Tau), 
      getU u x p = Some tau ->
      K d tau A.
Proof.
  intros u d x p WFUder tau getUder.
  induction WFUder.
  (* crush gets zero. *)
  +Case "u nil".
  compute in getUder.
  destruct x in getUder.
  inversion getUder.
  +Case "u gets a new member on the end".
   
(* Fun diversion but it's stuck because I can't show uniqueness of xp. *)
  apply getU_weakening in getUder.
  apply IHWFUder in getUder.
  exact getUder.

(* Attempt to use the previous lemma which Dan thinks works. *)
(*
  rewrite app_nil_end with (l:= d).
  apply A_1_Context_Weakening_1 with 
  (d:=d) (tau:= tv_t t0) (k:=A) (d':=nil).
*)
Admitted.

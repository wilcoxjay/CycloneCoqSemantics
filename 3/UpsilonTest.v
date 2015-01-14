(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Let's figure out the pack/Upsilon problem. Basically upsilon
  is referenced once and never filled.

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

Require Import TestUtilities.
Require Import Tacticals.

(* SL_3_1 *)

(* The mininal closed type test assignment with an empty path.
   Gettyp_nil applies. *)
Example ltyp_assign_cint:
    ltyp [] [] [(x,cint)] (p_e x []) cint.
Proof.
  intros.
  apply SL_3_1 with (tau' := cint).
  reflexivity.
  apply gettype_nil.
  eauto 20 with Chapter3.
  eauto 20 with Chapter3.
Qed.

Example ltyp_assign_a_pair:
    ltyp [] 
         [] (* Utype needs nothing as it has a nil path. *)
         [(x,(cross cint cint))] 
         (p_e x []) (cross cint cint).
Proof.
  intros.
  apply SL_3_1 with (tau' := cross cint cint).
  reflexivity.
  apply gettype_nil.
  eauto 20 with Chapter3.
  eauto 20 with Chapter3.
Qed.

(* Now follow a pair for an assignment. *)

Example ltyp_assign_into_pair:
    ltyp [] 
         [] (* Upsilon needs nothing as the only place it reads is in pack. *)
         [(x,(cross cint cint))] 
         (p_e x [i_pe zero_pe]) cint.
Proof.
  intros.
  apply SL_3_1 with (tau' := cross cint cint).
  reflexivity.
  apply gettype_pair_zero.
  apply gettype_nil.
  eauto 20 with Chapter3.
  eauto 20 with Chapter3.
Qed.

(* So an assignment of a pack goes through this ltype on the LHS. 
  There must be an Upsilon entry mapping x, p to the witness type
  for all etype alias within any path in the typing. *)

Example ltyp_read_pack:
    ltyp [] 
         [(x,[],cint)] (* Upsilon must be filled with witness. *)
         [(x, (etype aliases alpha B (tv_t alpha)))]
         (p_e x [u_pe]) cint.
Proof.
  intros.
  apply SL_3_1 with (tau' := (etype aliases alpha B (tv_t alpha))).
  reflexivity.
  apply gettype_etype with (tau'':= cint).
  constructor.
  simpl.
  apply gettype_nil.
  constructor; try eauto 20 with Chapter3.
  apply K_etype; try eauto 20 with Chapter3.
Qed.


(* SL 3 1 must map x to all its paths that have packs and know their type. 
 Not quite right, p' is not specified, should not be used. *)

(*
Inductive settype : Upsilon -> EVar -> P -> Tau -> Upsilon -> Prop :=
 | settype_cint:
     forall (u : Upsilon) (x : EVar) (p : P) (tau : Tau),
            settype u x [] cint u

 | settype_pair :
     forall (u : Upsilon) (x : EVar) (p : P) (t0 t1 : Tau) (p' : P) (u1' u2': Upsilon),
       settype u x  (p ++ [i_pe zero_pe]) t0 u1' ->
       settype u x  (p ++ [i_pe zero_pe]) t1 u2' ->
       settype u x p (cross t0 t1) (union_Upsilon u u1' u2')

 | settype_etype :
     forall (u : Upsilon) (x : EVar) (p : P) (tau' : Tau) (u': Upsilon),
       settype 
       settype u x p (etype aliases alpha k tau') [u_pe] u'.
*)

(* I need to go from a pack to a typing. *)

Example rtyp_pack_int:
  rtyp 
    []
    []
    []
    (pack cint (i_e (i_i 0)) (etype aliases alpha B (tv_t alpha)))
    (etype aliases alpha B (tv_t alpha)).
Proof.
  apply SR_3_12.
  simpl.
  constructor; eauto 20 with Chapter3.
  eauto 20 with Chapter3.
  eauto 20 with Chapter3.
Qed.

(* Okay the simplest full test is to dynamically execute this and then
   type it. *)

Definition pkt := (etype aliases alpha B (tv_t alpha)).
Definition pk := (pack cint (i_e (i_i 0)) pkt).

Definition t := 
  (seq (e_s (assign (p_e x []) pk))
       (e_s (p_e x []))).

Definition t' := (assign (p_e x []) pk).

Example eval_assign_pk:
  R
    []
    (e_s t')
    [(x, pk)]
    (e_s pk).
Proof.
  apply R_initial_assign_3_2; eauto 20 with Chapter3.
Qed.

Example type_assign_pk:
  rtyp
    []
    []
    []
    t'
    pkt.
Proof.
  apply SR_3_8.
  admit.
  admit.
Admitted.  

Example execute_pack_read:
  Sstar
    [] 
    t 
    [(x,pk)] 
    (e_s pk).
Proof.
Admitted.

(* SR_3_1 *) 
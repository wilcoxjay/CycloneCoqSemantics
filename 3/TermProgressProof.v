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
Require Export TacticNotations.

Require Export ValueLemmas.

Require Export CannonicalFormsProof.

(* I do not believe this works, not do I beieve that mutual induction is correct. 
Lemma A_14_Term_Progress_l_ind:
  forall (u : Upsilon) (g : Gamma) (e : E) (tau : Tau),
    ltyp [] u g e tau -> 
    forall (h : H),
      htyp u g h g -> 
      refp h u ->
    (exists (x : EVar) (p : P), e = (p_e x p)) \/ 
    (exists (h' : H) (e' : E),  L h (e_s e) h' (e_s e')).
Proof.
  intros u g e tau.
  intros ltypder.
  ltyp_ind_cases( induction ltypder) Case.
  Case "ltyp d u g (p_e x p) tau".
   intros.
   left.
   apply ex_intro with (x:= x).
   apply ex_intro with (x:= p).
   reflexivity.
  Case "ltyp d u g (star e) tau".
   (* This may be showing I do need my broken ltyp_mutual_ind. *)
   intros.
   E_ind_cases (induction e) SCase.
   SCase "(i_e i)".
    try solve [ inversion H].
   SCase "(p_e e l)".
    right.
    (* Can't get e' such that R .. e' *)
    admit.
   SCase "(f_e f1)".
    try solve [ inversion H].
   SCase "(amp e)".
    right.
    admit.
   SCase "(star e)".
    admit.
   SCase "(cpair e e0)".
    try solve [inversion H].
   SCase "(dot e i)".
    right.
    admit.
   SCase "(assign e e0)".
    right.
    admit.
   SCase "(appl e e0)".
    right.
    admit.
   SCase "(call s)".
    right.
    admit.
   SCase "(inst e t)".
    right.
    admit.
   SCase "(pack t e t0)".
    right.
    try solve [inversion H].
  Case "ltyp d u g (dot e zero_pe) t0".
   intros.
   right.
   admit.
 Case "ltyp d u g (dot e one_pe) t1".
  intros.
  right.
  (* Heap safety lemma 3, DR 3.1. *)
  admit.
Qed.
*)


(* Disconnected e in goal of ltyp cases, unprovable base. *)
Lemma A_14_Term_Progress_1_mutual_ind:
  forall (u : Upsilon) (g : Gamma) (e : E) (tau : Tau),
    ltyp [] u g e tau -> 
    forall (h : H),
      htyp u g h g -> 
      refp h u ->
    (exists (x : EVar) (p : P), e = (p_e x p)) \/ 
    (exists (h' : H) (e' : E),  L h (e_s e) h' (e_s e')).
Proof.
  intros u g e tau.
  ltyp_ind_mutual_cases  (
   apply (ltyp_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              styp d u g t s ->
              forall (h : H),
                htyp u g h g -> 
                refp h u ->
                (exists (x : EVar) (p : P), e = (p_e x p)) \/ 
                (exists (h' : H) (e' : E),  L h (e_s e) h' (e_s e')))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
                (lt : ltyp d u g  e tau') =>
              ltyp d u g  e tau' ->
              forall (h : H),
                htyp u g h g -> 
                refp h u ->
                (exists (x : EVar) (p : P), e = (p_e x p)) \/ 
                (exists (h' : H) (e' : E),  L h (e_s e) h' (e_s e')))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              rtyp d u g e t -> 
              forall (h : H),
                htyp u g h g -> 
                refp h u ->
                (exists (x : EVar) (p : P), e = (p_e x p)) \/ 
                (exists (h' : H) (e' : E),  L h (e_s e) h' (e_s e'))))
         ) Case.
 Case "styp_e_3_1".
  intros.
  apply H with (h:= h) in r; try assumption. (* Over generalizing e to e0. *)
  admit.
 Case "styp_return_3_2".
  intros.
  apply H with (h:= h) in r; try assumption.
  admit.
 Case "styp_seq_3_3".
  admit.
 Case "styp_while_3_4".
  admit.
 Case "styp_if_3_5".
  admit.
 Case "styp_let_3_6".
  admit.
 Case "styp_open_3_7".
  admit.
 Case "styp_openstar_3_8".
  admit.
 Case "SL_3_1".
  intros.
  left.
  apply ex_intro with (x:= x).
  apply ex_intro with (x:= p).
  reflexivity.
 Case "SL_3_2".
  intros.
  right.
  pose proof r as r'.
  apply H with (h:= h) in r; try assumption. (* Wrong h? *)
  inversion r.
  destruct H3 as [ e'].
  destruct H3 as [ p'].
  assert (Z: Value e0 \/ ~Value e0).
  apply value_or_not.
  inversion Z.
  SCase "value e0".
   pose proof H4 as H4'.
   apply A_9_Cannonical_Forms_4 with (u:= u0) (g:= g0) (t':= tau0) in H4.
   destruct H4 as [ x0 ].
   destruct H4 as [ p0 ].
   apply ex_intro with (x:= h).
   apply ex_intro with (x:= e0).
   rewrite H4.
   apply rtyp_value_d_strengthening_rtyp_ind
   with (d:= d) (u:= u0) (g:= g0) (tau:= (ptype tau0)) in H4'; try assumption.

   admit.
   (* a bit lost here. *)
   (* apply L_staramp_3_2. (* Extra amp there. *)  *)   admit. 
   admit. (* This is rtype strengthening so I'm not buying the proof case. *)
          (* I'd need a lemma saying all values have closed delta typing. *)
  SCase "~ value e0".
   
  

 Case "SL_3_3".
  admit.
 Case "SL_3_4".
  admit.
 Case "SR_3_1".
  admit.
 Case "SR_3_2".
  intros.
  (* Looks connected. *)
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
  (* Looks unsolvable. *)
  

Qed.

Lemma A_14_Term_Progress_2:
  forall (g : Gamma) (u : Upsilon) (h : H) (e : E) (tau : Tau),
    htyp u g h g -> 
    refp h u ->
    rtyp [] u g e tau -> 
    (Value e \/
     exists (h' : H) (e' : E),  R h (e_s e) h' (e_s e')).
Proof.
  intros g u h e tau.
  intros htypder refpder.
  apply (rtyp_ind_mutual 
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              styp d u g t s ->
              (Value e \/
               exists (h' : H) (e' : E),  S h (e_s e) h' (e_s e')))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
                (lt : ltyp d u g  e tau') =>
              ltyp d u g  e tau' ->
              (Value e \/
               exists (h' : H) (e' : E),  L h (e_s e) h' (e_s e')))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              rtyp d u g e t ->
              (Value e \/
               exists (h' : H) (e' : E),  R h (e_s e) h' (e_s e')))).
  
Admitted.

Lemma A_14_Term_Progress_3:
  forall (g : Gamma) (u : Upsilon) (h : H) (s : St) (tau : Tau),
    htyp u g h g ->
    refp h u ->
    styp [] u g tau s -> 
     (exists (v : E), Value v /\ (s = (e_s v) \/ s = retn v)) \/
     (exists (h' : H) (s' : St), S h s h' s').
Proof.
  intros g u h e tau.
  intros htypder refpder.
  apply (styp_ind_mutual 
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              styp d u g t s ->
              (exists (v : E), Value v /\ (s = (e_s v) \/ s = retn v)) \/
              (exists (h' : H) (s' : St), S h s h' s'))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
                (lt : ltyp d u g  e tau') =>
              ltyp d u g  e tau' ->
              (exists (h' : H) (s' : St), L h (e_s e) h' s'))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              rtyp d u g e t ->
              (exists (h' : H) (s' : St), R h (e_s e) h' s'))).
  (* crush goes up many goals here. *)
Admitted.

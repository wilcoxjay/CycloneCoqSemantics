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
  
Inductive extends_Gamma : Gamma -> Gamma -> Prop := 
  | A_12_Extension_Gamma : 
      forall (g1 g2 : Gamma),
        (exists (g3 : Gamma), g2 = g1 ++ g3) ->
        extends_Gamma g2 g1.

Inductive extends_Upsilon : Upsilon -> Upsilon -> Prop := 
  | A_12_Extension_Upsilon : 
      forall (u1 u2 : Upsilon),
        (exists (g3 : Upsilon), u2 = u1 ++ g3) ->
        extends_Upsilon u2 u1.

(* TODO fix /\ *)

Lemma A_13_Term_Preservation_1:
  forall (s s' : St) (h h' : H),
    L h s  h' s' ->
    forall (e e' : E),
      s  = (e_s e) ->
      s' = (e_s e') ->
      forall (u : Upsilon) (g : Gamma) (tau : Tau),
        htyp u g h g ->
        refp h u -> 
        ltyp [] u g e tau -> 
        exists (g' : Gamma) (u' : Upsilon),
          extends_Gamma  g g' ->
          extends_Upsilon  u u' -> 
          htyp u' g' h' g' /\
          refp h' u' /\
          ltyp [] u' g' e' tau.
Proof.
  intros s s' h h' Lder.
  apply (L_ind_mutual
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (rstep: R h s h' s') =>
                  forall (e e' : E),
                    s  = (e_s e) ->
                    s' = (e_s e') ->
                    forall (u : Upsilon) (g : Gamma) (tau : Tau),
                      htyp u g h g ->
                      refp h u -> 
                      rtyp [] u g e tau -> 
                      exists (g' : Gamma) (u' : Upsilon),
                        extends_Gamma  g g' -> 
                        extends_Upsilon  u u' -> 
                        htyp u' g' h' g' /\
                        refp h' u' /\
                        rtyp [] u' g' e' tau)

           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (sstep: S h s h' s') =>
                  forall (e e' : E),
                    s  = (e_s e) ->
                    s' = (e_s e') ->
                    forall (u : Upsilon) (g : Gamma) (tau : Tau),
                      htyp u g h g ->
                      refp h u -> 
                      styp [] u g tau s -> 
                      exists (g' : Gamma) (u' : Upsilon),
                        extends_Gamma  g g' ->
                        extends_Upsilon  u u' -> 
                        htyp u' g' h' g' /\
                        refp h' u' /\
                        styp [] u' g' tau s')

           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (lstep: L h s h' s') =>
                  forall (e e' : E),
                    s  = (e_s e) ->
                    s' = (e_s e') ->
                    forall (u : Upsilon) (g : Gamma) (tau : Tau),
                      htyp u g h g ->
                      refp h u -> 
                      ltyp [] u g e tau -> 
                      exists (g' : Gamma) (u' : Upsilon),
                        extends_Gamma  g g' ->
                        extends_Upsilon  u u' ->
                        htyp u' g' h' g' /\
                        refp h' u' /\
                        ltyp [] u' g' e' tau)).
  (* crush gives 26/42. *)
  Case "R_get_3_1".
   intros.
   apply ex_intro with (x:= g0).
   apply ex_intro with (x:= u).
   intros.
   split.
   assumption.
   split.
   assumption.
   
   crush.
   admit.
  Case "R_assign_3_2".
   admit.
  Case "R_initial_assign_3_2".
   admit.
  Case "R_star_amp_3_3".
   admit.
  Case "R_dot_3_4_0".
   admit.
  Case "R_dot_3_4_1".
   admit.
  Case "R_appl_3_5".
   admit.
  Case "R_call_3_6".
   admit.
  Case "R_inst_3_7".
   admit.
  Case "R_call_3_8".
   admit.
  Case "R_amp_3_9_1".
   admit.
  Case "R_assign_3_9_2".
   admit.
  Case "R_star_3_10_1".
   admit.
  Case "R_dot_3_10_2".
   admit.
  Case "R_assign_3_10_3".
   admit.
  Case "R_inst_3_10_4".
   admit.
  Case "R_pack_3_10_5".
   admit.
  Case "R_cpair_3_10_6".
   admit.
  Case "R_cpair_3_10_7".
   admit.
  Case "R_cpair_3_10_8".
   admit.
  Case "R_appl_3_10_9".
   admit.
  Case "R_appl_3_10_10".
   admit.
  Case "S_let_3_1".
   crush.
  Case "S_seq_3_2".
   crush.
  Case "S_return_3_3".
   crush.
  Case "S_if0_3_4".
   crush.
  Case "S_if_ne_0_3_5".
   crush.
  Case "S_while_3_6".
   crush.
  Case "S_open_3_7".
   crush.
  Case "S_openstar_3_8".
   crush.
  Case "S_exp_3_9_1".
   crush.
  Case "S_ret_3_9_2".
   crush.
  Case "S_if_3_9_3".
   crush.
  Case "S_letx_3_9_4".
   crush.
  Case "S_open_3_9_5".
   crush.
  Case "S_seq_3_10".
   crush.
  Case "S_openstar_3_11".
   crush.
  Case "L_xpi_3_1".
   admit.
  Case "L_staramp_3_2".
   admit.
  Case "L_star_3_3".
   admit.
  Case "L_ei_3_4".
   admit.
  Case "assumption, why do I get this?".
   assumption.
Qed.

(* 

  Case "R h0 (e_s (p_e x p)) h0 (e_s e')".
   apply ex_intro with (x:=g0).
   apply ex_intro with (x:=u).
   intros eG uG.
   split; try split; try assumption.
   inversion H4.
   (* need path lemma. *)
   admit.
  Case "R h0 (e_s (assign (p_e x p) e')) (setH h0 x v'') (e_s e')".
   admit.
  Case "R h0 (e_s (assign (p_e x []) e')) (setH h0 x e') (e_s e')".
   admit.
  Case "R h0 (star (amp (p_e x p))) h0 (p_e x p)".
   apply ex_intro with (x:=g).
   apply ex_intro with (x:=u).
   intros eG eU.
   split; try split; try assumption.
   (* Need that the heap does not change. Inversion on H is not doing it. *)
   inversion H4.
   inversion H1.
   assumption.
  Case "R h0 (e_s (dot (cpair e' v1) zero_pe)) h0 (e_s e')".
   apply ex_intro with (x:=g).
   apply ex_intro with (x:=u).
   intros eG eU.
   split; try split; try assumption.
   (* Need that the heap does not change. Inversion on H is not doing it. *)
   inversion H4.
   inversion H7.
   (* Need ltac to invert on an inversion. *)
  Case "R h0 (e_s (dot (cpair v0 e') one_pe)) h0 (e_s e')".
   apply ex_intro with (x:=g).
   apply ex_intro with (x:=u).
   intros eG eU.
   split; try split; try assumption.
   inversion H4.
   inversion H7.
  Case "R h0 (e_s (appl (f_e (dfun tau x tau' s0)) v)) h0
        (e_s (call (letx x v s0)))". 
   apply ex_intro with (x:=g).
   apply ex_intro with (x:=u).
   intros eG eU.
   split; try split; try assumption.
   inversion H4.
  Case "R h0 (e_s (call (retn e'))) h0 (e_s e')".
   apply ex_intro with (x:=g).
   apply ex_intro with (x:=u).
   intros eG eU.
   split; try split; try assumption.
   inversion H4.
  Case "R h0 (e_s (inst (f_e (ufun alpha k f)) tau)) h0
            (e_s (f_e (subst_F f tau alpha)))".
   apply ex_intro with (x:=g).
   apply ex_intro with (x:=u).
   intros eG eU.
   split; try split; try assumption.
   inversion H4.
  Case "R h0 (e_s (call s0)) h'0 (e_s (call s'0))".
(* generates goals. 
   apply ex_intro with (x:=g).
   apply ex_intro with (x:=u).
   intros eG eU.
   
   split; try split; try assumption.
   inversion H4.
*)
   admit.
  Case "R h0 (e_s (amp e)) h'0 (e_s (amp e'))".
   apply ex_intro with (x:=g).
   apply ex_intro with (x:=u).
   intros eG eU.
   
   split; try split; try assumption.
   inversion H4.
   admit.
   admit.
   admit.
   admit.
  Case "?L h0 (e_s e) h'0 (e_s e')".
   apply ex_intro with (x:=g).
   apply ex_intro with (x:=u).
   intros eG eU.
   
   split; try split; try assumption.
   inversion H4; try assumption.
   admit.
   admit.
   admit.
   admit.
 Case "R h0 (e_s (star e)) h'0 (e_s (star e'))".
   apply ex_intro with (x:=g).
   apply ex_intro with (x:=u).
   intros eG eU.
   
   split; try split; try assumption.
   inversion H4; try assumption.
   admit.
   admit.
   admit.

Admitted.
*)

Lemma A_13_Term_Preservation_2:
  forall (s s' : St) (h h' : H),
    R h s  h' s' ->
    forall (e e' : E),
      s  = (e_s e) -> 
      s' = (e_s e') ->
     forall (u : Upsilon) (g : Gamma) (tau : Tau),
       htyp u g h g ->
       refp h u -> 
       rtyp [] u g e tau ->
       exists (g' : Gamma) (u' : Upsilon),
         (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
         htyp u' g' h' g' /\ 
         refp h' u' /\
         rtyp [] u' g' e' tau.
Proof.
  intros s s' h h' Rder.
  apply (R_ind_mutual
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (step: R h s h' s') =>
              forall (e e' : E),
                s  = (e_s e) -> 
                s' = (e_s e') ->
                forall (u : Upsilon) (g : Gamma) (tau : Tau),
                  htyp u g h g ->
                  refp h u -> 
                  rtyp [] u g e tau ->
                  exists (g' : Gamma) (u' : Upsilon),
                    (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                    htyp u' g' h' g' /\ 
                    refp h' u' /\
                    rtyp [] u' g' e' tau)
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (step: S h s h' s') =>
              forall (e e' : E),
                s  = (e_s e) -> 
                s' = (e_s e') ->
                forall (u : Upsilon) (g : Gamma) (tau : Tau),
                  htyp u g h g ->
                  refp h u -> 
                  styp [] u g tau e ->
                  exists (g' : Gamma) (u' : Upsilon),
                    (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                    htyp u' g' h' g' /\ 
                    refp h' u' /\
                    styp [] u' g' tau' e)
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (step: L h s h' s') =>
              forall (e e' : E),
                s  = (e_s e) -> 
                s' = (e_s e') ->
                forall (u : Upsilon) (g : Gamma) (tau : Tau),
                  htyp u g h g ->
                  refp h u -> 
                  ltyp [] u g e tau ->
                  exists (g' : Gamma) (u' : Upsilon),
                    (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                    htyp u' g' h' g' /\ 
                    refp h' u' /\
                    ltyp [] u' g' e' tau)).
  (* crush leaves 27/42. *)
  Case "R_get_3_1".
   admit.
  Case "R_assign_3_2".
   admit.
  Case "R_initial_assign_3_2".
   admit.
  Case "R_star_amp_3_3".
   admit.
  Case "R_dot_3_4_0".
   admit.
  Case "R_dot_3_4_1".
   admit.
  Case "R_appl_3_5".
   admit.
  Case "R_call_3_6".
   admit.
  Case "R_inst_3_7".
   admit.
  Case "R_call_3_8".
   admit.
  Case "R_amp_3_9_1".
   admit.
  Case "R_assign_3_9_2".
   admit.
  Case "R_star_3_10_1".
   admit.
  Case "R_dot_3_10_2".
   admit.
  Case "R_assign_3_10_3".
   admit.
  Case "R_inst_3_10_4".
   admit.
  Case "R_pack_3_10_5".
   admit.
  Case "R_cpair_3_10_6".
   admit.
  Case "R_cpair_3_10_7".
   admit.
  Case "R_cpair_3_10_8".
   admit.
  Case "R_appl_3_10_9".
   admit.
  Case "R_appl_3_10_10".
   admit.
  Case "S_let_3_1".
   admit.
  Case "S_seq_3_2".
   admit.
  Case "S_return_3_3".
   admit.
  Case "S_if0_3_4".
   admit.
  Case "S_if_ne_0_3_5".
   admit.
  Case "S_while_3_6".
   admit.
  Case "S_open_3_7".
   admit.
  Case "S_openstar_3_8".
   admit.
  Case "S_exp_3_9_1".
   admit.
  Case "S_ret_3_9_2".
   admit.
  Case "S_if_3_9_3".
   admit.
  Case "S_letx_3_9_4".
   admit.
  Case "S_open_3_9_5".
   admit.
  Case "S_seq_3_10".
   admit.
  Case "S_openstar_3_11".
   admit.
  Case "L_xpi_3_1".
   admit.
  Case "L_staramp_3_2".
   admit.
  Case "L_star_3_3".
   admit.
  Case "L_ei_3_4".
   admit.
  Case "assumption, why do I get this?".
   assumption.
Qed.

Lemma A_13_Term_Preservation_3:
  forall (s s': St)  (h h' : H),
    S h s  h' s' ->
    forall (u : Upsilon) (g : Gamma) (tau : Tau),
      htyp u g h g ->
      refp h u -> 
      styp [] u g tau s -> 
      exists (g' : Gamma) (u' : Upsilon),
        (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
        htyp u' g' h' g' /\ 
        refp h' u' /\
        styp [] u' g' tau s'.
Proof.
  intros s s' h h' Sder.
  apply (S_ind_mutual
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (rstep: R h s h' s') =>
              forall (u : Upsilon) (g : Gamma) (tau : Tau),
                htyp u g h g ->
                refp h u -> 
                styp [] u g tau s -> 
                exists (g' : Gamma) (u' : Upsilon),
                  (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                  htyp u' g' h' g' /\ 
                  refp h' u' /\
                  styp [] u' g' tau s')
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (sstep: S h s h' s') =>
              forall (u : Upsilon) (g : Gamma) (tau : Tau),
                htyp u g h g ->
                refp h u -> 
                styp [] u g tau s -> 
                exists (g' : Gamma) (u' : Upsilon),
                  (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                  htyp u' g' h' g' /\ 
                  refp h' u' /\
                  styp [] u' g' tau s')
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (lstep: L h s h' s') =>
              forall (u : Upsilon) (g : Gamma) (tau : Tau),
                htyp u g h g ->
                refp h u -> 
                styp [] u g tau s -> 
                exists (g' : Gamma) (u' : Upsilon),
                  (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                  htyp u' g' h' g' /\ 
                  refp h' u' /\
                  styp [] u' g' tau s')).
  (* crush leaves 41/42. *)
  Case "R_get_3_1".
   admit.
  Case "R_assign_3_2".
   admit.
  Case "R_initial_assign_3_2".
   admit.
  Case "R_star_amp_3_3".
   admit.
  Case "R_dot_3_4_0".
   admit.
  Case "R_dot_3_4_1".
   admit.
  Case "R_appl_3_5".
   admit.
  Case "R_call_3_6".
   admit.
  Case "R_inst_3_7".
   admit.
  Case "R_call_3_8".
   admit.
  Case "R_amp_3_9_1".
   admit.
  Case "R_assign_3_9_2".
   admit.
  Case "R_star_3_10_1".
   admit.
  Case "R_dot_3_10_2".
   admit.
  Case "R_assign_3_10_3".
   admit.
  Case "R_inst_3_10_4".
   admit.
  Case "R_pack_3_10_5".
   admit.
  Case "R_cpair_3_10_6".
   admit.
  Case "R_cpair_3_10_7".
   admit.
  Case "R_cpair_3_10_8".
   admit.
  Case "R_appl_3_10_9".
   admit.
  Case "R_appl_3_10_10".
   admit.
  Case "S_let_3_1".
   admit.
  Case "S_seq_3_2".
   admit.
  Case "S_return_3_3".
   admit.
  Case "S_if0_3_4".
   admit.
  Case "S_if_ne_0_3_5".
   admit.
  Case "S_while_3_6".
   admit.
  Case "S_open_3_7".
   admit.
  Case "S_openstar_3_8".
   admit.
  Case "S_exp_3_9_1".
   admit.
  Case "S_ret_3_9_2".
   admit.
  Case "S_if_3_9_3".
   admit.
  Case "S_letx_3_9_4".
   admit.
  Case "S_open_3_9_5".
   admit.
  Case "S_seq_3_10".
   admit.
  Case "S_openstar_3_11".
   admit.
  Case "L_xpi_3_1".
   admit.
  Case "L_staramp_3_2".
   admit.
  Case "L_star_3_3".
   admit.
  Case "L_ei_3_4".
   admit.
  Case "assumption, why do I get this?".
   assumption.
Qed.

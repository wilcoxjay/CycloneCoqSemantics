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
Require Export GetLemmasRelation.

Lemma A_2_Term_Weakening_1 :
  forall (d: Delta) (u u' : Upsilon) (g g' : Gamma)
         (x : EVar) (p p' : P) (tau tau' : Tau),
    WFC d (u ++ u') (g ++ g') ->
    gettype u x p tau p' tau' ->
    gettype (u ++ u') x p tau p' tau'.
Proof.
  intros d u u' g g' x p p' tau tau'.
  intros WFCd.
  intros gettypeder.
  gettype_ind_cases (induction gettypeder) Case.
  Case "gettype u x p tau [] tau".
   constructor.
  Case "gettype u x p (cross t0 t1) (i_pe zero_pe :: p') tau".
   constructor.
   apply IHgettypeder in WFCd.
   assumption.
  Case "gettype u x p (cross t0 t1) (i_pe one_pe :: p') tau".
   constructor.
   apply IHgettypeder in WFCd.
   assumption.
  Case "gettype u x p (etype aliases alpha k tau') (u_pe :: p') tau)".
   apply IHgettypeder in WFCd.
   apply gettype_etype with (tau'':= tau'').
   apply getU_Some_Weakening. 
   assumption.
   assumption.
Qed.

Lemma A_2_Term_Weakening_2:
  forall (d: Delta) (u : Upsilon) (g : Gamma)  (e : E) (tau : Tau),
    ltyp d u g e tau ->
    WFC d u g -> 
      forall (u' : Upsilon) (g' : Gamma),
        WFC d u' g' ->
        WFC d (u ++ u') (g ++ g') ->
        ltyp d (u ++ u') (g ++ g') e tau.
Proof.
  intros d u g e tau ltypder.
  (* TODO Why is it universally generalizing everything ? Thus I get the
     wrong induction. *)
  
(apply (ltyp_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (tau : Tau) (s : St)
                (st : styp d u g tau s) =>
              WFC d u g -> 
              forall (u' : Upsilon) (g' : Gamma),
                WFC d u' g' ->
                WFC d (u ++ u') (g ++ g') ->
                ltyp d (u ++ u') (g ++ g') e tau)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau : Tau) 
                (lt : ltyp d u g e tau) =>
              WFC d u g -> 
              forall (u' : Upsilon) (g' : Gamma),
                WFC d u' g' ->
                WFC d (u ++ u') (g ++ g') ->
                ltyp d (u ++ u') (g ++ g') e tau)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau : Tau) 
                (rt : rtyp d u g e tau) =>
              WFC d u g -> 
              forall (u' : Upsilon) (g' : Gamma),
                WFC d u' g' ->
                WFC d (u ++ u') (g ++ g') ->
                ltyp d (u ++ u') (g ++ g') e tau))).

  ltyp_ind_mutual_cases 
     Case.

  Case "styp_e_3_1".
   intros.
   admit.
  Case "styp_return_3_2".
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
   admit.
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
  admit.
Qed.

Lemma A_2_Term_Weakening_3:
  forall (d: Delta) (u u' : Upsilon) (g g' : Gamma)
         (e : E) (tau : Tau),
    WFC d (u ++ u') (g ++ g') ->
    rtyp d u g e tau ->
    rtyp d (u ++ u') (g++g') e tau.
Proof.
  intros d u u' g g' e tau WFC rtypder.
  rtyp_ind_mutual_cases 
   (apply (rtyp_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) =>
              rtyp d (u ++ u') (g++g') e t)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (lt : ltyp d u g e t) =>
              rtyp d (u ++ u') (g++g') e t)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              rtyp d (u ++ u') (g++g') e t))) Case.
  Case "styp_e_3_1".
   admit.
  Case "styp_return_3_2".
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
   admit.
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
   admit.
Qed.


Lemma A_2_Term_Weakening_4:
  forall (d: Delta) (u u' : Upsilon) (g g' : Gamma)
         (s : St) (tau : Tau),
    WFC d (u ++ u') (g ++ g') ->
    styp d u g tau s ->
    styp d (u ++ u') (g++g') tau s.
Proof.
  intros d u u' g g' s tau WFC stypder.
  styp_ind_mutual_cases 
   (apply (styp_ind_mutual
         (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) =>
            styp d (u ++ u') (g++g') t s)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (lt : ltyp d u g e t) =>
            styp d (u ++ u') (g++g') t s)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
            styp d (u ++ u') (g++g') t s))) Case.
  Case "styp_e_3_1".
   admit.
  Case "styp_return_3_2".
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
   admit.
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
   admit.
Qed.

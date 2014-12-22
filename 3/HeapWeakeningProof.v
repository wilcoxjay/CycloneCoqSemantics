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
Require Export TermWeakeningProof.

(* TODO must thee be strengthened with WFDG and even WFDG d? *)
Lemma getG_weakening:
 forall (g : Gamma) (x : EVar) (tau : Tau),
   getG g x = Some tau ->
   (* WFDG [] g ->  *)
   forall (g' : Gamma),
     (* WFDG [] (g ++ g') -> *)
    getG (g ++ g') x = Some tau.
Proof.
Admitted.

Lemma ltyp_weakening:
  forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau : Tau),
   ltyp d u g e tau ->
   forall (u' : Upsilon) (g' : Gamma), 
     ltyp d (u ++ u') (g ++ g') e tau.
Proof.
Admitted.

Lemma styp_weakening:
  forall (d : Delta) (u : Upsilon) (g : Gamma) (tau : Tau) (s : St),
    styp d u g tau s -> 
    forall (u' : Upsilon) (g' : Gamma), 
      styp d (u ++ u') (g ++ g') tau s.
Proof.
Admitted.

Lemma rtyp_weakening:
  forall (u : Upsilon) (g : Gamma) (v : E) (tau : Tau),
    rtyp [] u g v tau -> 
    (* WFC [] u g -> *)
    forall (u' : Upsilon) (g' : Gamma),
      (* WFC [] (u ++ u') (g ++ g') ->  *)
      rtyp [] (u ++ u') (g ++ g') v tau.
Proof.
  intros u g v tau rtypder.
  rtyp_ind_cases (induction rtypder) Case.
  Case "rtyp d u g (p_e x p) tau".
   intros.
   apply SR_3_1 with (tau':= tau'); try assumption.
   apply getG_weakening; try assumption.
   apply gettype_weakening; try assumption.
   inversion H2; try assumption.
   admit. (* WFU u ++ u' *)
   admit. (* WFC d (u ++ u') (g ++ g') *)
  Case "rtyp d u g (star e) tau".
   intros.
   constructor; try assumption.
   apply IHrtypder.
  Case "rtyp d u g (dot e zero_pe) t0".
   intros.
   apply SR_3_3 with (t1:= t1) ; try assumption.
   apply IHrtypder.
  Case "rtyp d u g (dot e one_pe) t1".
   intros.
   apply SR_3_4 with (t0:= t0) ; try assumption.
   apply IHrtypder.
  Case "rtyp d u g (i_e (i_i z)) cint".
   intros.
   apply SR_3_5; try assumption.
   admit. (* WFC d (u ++ u') (g ++ g') *)
  Case "rtyp  d u g (amp e) (ptyp tau)".
   intros.
   apply SR_3_6; try assumption.
   apply ltyp_weakening; try assumption.
  Case "rtyp d u g (cpair e0 e1) (cross t0 t1)".
   intros.
   apply SR_3_7; try assumption.
   apply IHrtypder1.
   apply IHrtypder2.
  Case "rtyp d u g (assign e1 e2) tau".
   intros.
   apply SR_3_8; try assumption.
   apply ltyp_weakening; try assumption.   
   apply IHrtypder.
  Case "rtyp d u g (appl e1 e2) tau".
   intros.
   apply SR_3_9 with (tau':= tau'); try assumption.
   apply IHrtypder1; try assumption.
   apply IHrtypder2; try assumption.
  Case "rtyp d u g (call s) tau".
   intros.
   apply SR_3_10; try assumption.
   apply styp_weakening; try assumption.
  Case "rtyp d u g (inst e tau) (subst_Tau tau' tau alpha)".
   intros.
   apply SR_3_11 with (k:= k); try assumption.
   apply IHrtypder; try assumption.
  Case "rtyp  d u g (pack tau' e (etype p alpha k tau)) (etyp p alpha k tau)".
   intros.
   apply SR_3_12; try assumption.
   apply IHrtypder; try assumption.
  Case "rtyp d u g (f_e (dfun tau x tau' s)) (arrow tau tau')".
   intros.
   apply SR_3_13; try assumption.
   AdmitAlphaConversion.
   apply styp_weakening; try assumption.
   admit. (* styp d u [(x, tau)] tau' s  from styp d u ([(x, tau)] ++ g) tau' s. 
          False? *)
  Case "rtyp  d u g (f_e (ufun alpha k f12)) (utyp alpha k tau))".
   intros.
   apply SR_3_14; try assumption.
   apply WFC_weakening with (d':= []) (u':= u') (g':= g'); try assumption.
   admit. (* Think more, it's here. *)
   apply IHrtypder.
Qed.


Lemma htyp_weakening:
 forall (u : Upsilon) (g : Gamma),  
   htyp u  g [] [] ->
   WFC [] u g -> 
   forall (u' : Upsilon) (g' : Gamma),
    WFC [] u' g' -> 
    WFC [] (u ++ u') (g ++ g') -> 
    htyp (u ++ u') (g ++ g') [] [].
Proof.
  intros u g htypder.
  intros.
  htyp_ind_cases (induction htypder) Case.
  Case "htyp u g [] []".
   constructor.
  Case "htyp u g h ([(x, tau)] ++ g')".
   pose proof H as H'.
   apply A_2_Term_Weakening_3 with (u':= u') (g':= g') (u:= u) (g:= g) 
                                             (tau:= tau) (e:= v)
     in H; try assumption.
   apply htyp_xv with (h':= h') (v:= v); try assumption.
   apply IHhtypder in H'.
   assumption.
   assumption.
Qed.

Lemma A_3_Heap_Weakening_1:
  forall (u u' : Upsilon) (g g' g'': Gamma) (h : H),
    WFC [] (u ++ u') (g ++ g') ->
    htyp u g h g'' ->
    htyp (u ++ u') (g ++ g') h g''.
Proof.
  intros u u' g g' g'' h WFCder htypder.
  htyp_ind_cases (induction htypder) Case.
  Case "htyp u g [] []".
   constructor.
  Case "htyp u g h ([(x, tau)] ++ g')".
   apply IHhtypder in WFCder; try assumption.
   apply htyp_xv with (h':= h') (v:= v); try assumption.
   apply rtyp_weakening.
   assumption.
Qed.

Lemma refp_weakening:
  forall (h : H) (u : Upsilon),
    refp h u ->
    forall (h' : H),
      refp (h ++ h') u.
Proof.
  
Admitted.

Lemma getH_weakening:
  forall (h : H) (x : EVar) (v : E),
    getH h x = Some v -> 
    forall (h' : H),
      getH (h ++ h') x = Some v.
Proof.
Admitted.

Lemma A_3_Heap_Weakening_2:
  forall (u : Upsilon) (h : H),
    refp h u ->
    forall (h' : H),
      refp (h ++ h') u.
Proof.
  intros u h refpder.
  refp_ind_cases (induction refpder) Case.
  Case  "refp h []".
   intros.
   constructor.
  Case "refp h ([(x, p, tau')] ++ u)".
   intros.
   apply refp_pack 
   with (tau:= tau) (alpha:= alpha) (k:= k) (v:= v) (v':= v'); try assumption.
   apply getH_weakening; try assumption.
   apply refp_weakening; try assumption.
Qed.

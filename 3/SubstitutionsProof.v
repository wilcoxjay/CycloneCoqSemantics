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
Require Export TacticNotations.
Require Export GetLemmasRelation.

Lemma getD_weakening:
  forall (d : Delta) (alpha beta : TVar),
    getD d alpha = None -> 
    getD d beta = None ->
    (beq_tvar beta alpha) = false -> (* Alpha Conversion. *)
    forall (k : Kappa),
      getD ([(alpha, k)] ++ d) beta = None.
Proof.
  intros.
  induction d.
  Case "[]".
   rewrite app_nil_r.
   unfold getD.
   rewrite H1.
   reflexivity.
 Case "a :: d".
  destruct a.
  unfold getD in H.
  fold getD in H.
  unfold getD in H0.
  fold getD in H0.
  destruct (beq_tvar alpha t); destruct (beq_tvar beta t);
  try assumption; try inversion H; try inversion H0.
  rewrite H.
  apply IHd in H3; try assumption.
  simpl.
  rewrite H1.
  destruct (beq_tvar beta t).
  admit.  (* Must invert, don't have information to invert. *)
  assumption.
Qed.

Lemma getD_alpha_some_beta_none:
  forall (d : Delta) (alpha : TVar) (k : Kappa),
    getD d alpha = Some k ->
    forall (beta : TVar),
      getD d beta  = None ->
      beq_tvar alpha beta = false.
Proof.
  intros.
  induction d.
  Case "[]".
   destruct alpha.
   inversion H.
  Case "a :: d".
   destruct a. 
   unfold getD in H0.
   fold   getD in H0.
   unfold getD in H.
   fold   getD in H.
   destruct (beq_tvar alpha t); destruct (beq_tvar beta t); 
    try assumption; try inversion H0.
   admit. (* TODO Losing getd alpha = Some k. *)
   apply IHd in H; try assumption.
Qed.

Lemma substitution_with_different_type_variables:
  forall (alpha beta: TVar),
    beq_tvar beta alpha = false ->
    forall (tau : Tau),
      subst_Tau (tv_t alpha) tau beta = tv_t alpha.
Proof.
  intros alpha beta neqalphabeta tau.
  unfold subst_Tau.
  rewrite neqalphabeta.
  reflexivity.
Qed.

Lemma substitution_with_different_type_variables_ptype:
  forall (alpha beta: TVar),
    beq_tvar beta alpha = false ->
    forall (tau : Tau),
      subst_Tau (ptype (tv_t alpha)) tau beta = (ptype (tv_t alpha)).
Proof.
  intros alpha beta neqalphabeta tau.
  unfold subst_Tau.
  rewrite neqalphabeta.
  reflexivity.
Qed.

Lemma A_4_Useless_Substitutions_1:
  forall (d : Delta) (tau' : Tau) (k : Kappa),
    K d tau' k ->
    forall(alpha : TVar),
      getD d alpha = None ->
      forall (tau : Tau),
        subst_Tau tau' tau alpha = tau'.
Proof.
  intros d tau' k kder.
  K_ind_cases (induction kder) Case.

  Case  "K d cint B".
   intros alpha AlphaNotInDomd tau.
   reflexivity.
  Case  "K d (tv_t alpha) B".
    intros alpha0 AlphaNotInDomd tau.
    apply getD_alpha_some_beta_none with (beta:= alpha0) in H; try assumption.
    apply substitution_with_different_type_variables; try assumption.
    rewrite beq_tvar_symmetric; try assumption.
  Case  "K d (ptype (tv_t alpha)) B".
    intros alpha0 AlphaNotInDomd tau.
    apply getD_alpha_some_beta_none with (beta:= alpha0) in H; try assumption.
    apply substitution_with_different_type_variables_ptype.
    rewrite beq_tvar_symmetric; try assumption.
  Case  "K d tau A".
   intros alpha AlphaNotInDomd tau0.   
   apply IHkder with (tau0 := tau0) in AlphaNotInDomd.
   assumption.
  Case  "K d (cross t0 t1) A".
   crush.
  Case  "K d (arrow t0 t1) A".
   crush.
  Case  "K d (ptype tau) B".
   crush.
  Case  "K d (utype alpha k tau) A".
   intros alpha0 AlphaNotInDomd tau0.
   unfold subst_Tau.
   fold subst_Tau.
   specialize (IHkder alpha0).
   apply getD_weakening with (alpha:= alpha) (beta:= alpha0) (k:=k) in H0; 
     try assumption.
   apply IHkder with (tau0:= tau0) in H0.
   rewrite H0.
   reflexivity.
   AdmitAlphaConversion.
  Case  "K d (etype p alpha k tau) A)".
   intros alpha0 AlphaNotInDomd tau0.
   unfold subst_Tau.
   fold subst_Tau.
   specialize (IHkder alpha0).
   apply getD_weakening with (alpha:= alpha) (beta:= alpha0) (k:=k) in H0; 
     try assumption.
   apply IHkder with (tau0:= tau0) in H0.
   rewrite H0.
   reflexivity.
   AdmitAlphaConversion.
Qed.

(* use subst_Gamma_over_app *)
Lemma A_4_Useless_Substitutions_2:
  forall (d : Delta) (alpha : TVar),
    getD d alpha = None ->
    forall (g : Gamma), 
      WFDG d g ->
      forall (tau : Tau),
        subst_Gamma g tau alpha = g.
Proof.
  intros d alpha getd g WFDGder.
  Print WFDG_ind.
  WFDG_ind_cases (induction WFDGder) Case.
  Case "WFDG d []".
   intros.
   reflexivity.
  Case "WFDG d ([(x, tau)] ++ g)".
   intros.
   apply IHWFDGder with (tau:= tau0) in getd.
   (* Gonna need lemma 1. *)
   unfold subst_Gamma.
   simpl.
   fold subst_Gamma.
   rewrite getd.
   rewrite A_4_Useless_Substitutions_1 with (d:=d) (k:=A); try assumption.
   reflexivity.
   admit. (* Remember goal issue, jrw. *)
  Case "WFDG ([(alpha, k)] ++ d) g".
   intros tau.
   inversion getd.
   destruct (beq_tvar alpha alpha0).
   inversion H1.
   apply IHWFDGder with (tau:= tau) in H1.
   assumption.
Qed.  

Lemma A_4_Useless_Substitutions_3:
  forall (d : Delta) (alpha : TVar),
    getD d alpha = None ->
    forall (u: Upsilon) (x : EVar) (p : P) (tau': Tau),
        WFU u ->
        getU u x p tau' ->
        forall (tau : Tau),
          subst_Tau tau' tau alpha = tau'.
Proof.
  intros d alpha getDder u x p tau' WFUder.
  WFU_ind_cases (induction WFUder) Case.
  Case "WFU []".
   intros.
   inversion H.
  Case "WFU ([(x, p, tau)] ++ u)".
   intros.
   inversion H1.
   SCase "getU_top". 
    crush.
    apply A_4_Useless_Substitutions_1 with (alpha:= alpha) (tau:= tau0) in H0;
      try assumption.
    reflexivity.
   SCase "getU_next".
    crush. (* Just applies the inductive hypothesis. *)
Qed.

Lemma A_5_Commuting_Substitutions:
  forall (beta : TVar) (t2 : Tau),
    NotFreeInTau beta t2 = true ->
    forall (alpha : TVar) (t0 t1 : Tau),
      (subst_Tau (subst_Tau t0 t1 beta) t2 alpha) = 
      (subst_Tau (subst_Tau t0 t2 alpha)
                 (subst_Tau t1 t2 alpha)
                 beta).
Proof.
  intros beta t2 notfreeder alpha t0.
  (Tau_ind_cases (induction t0) Case).
  (* crush leaves 1/7. *)
  (* Need a working tautology on variable equality. *)
   Case "(tv_t t)".
    intros.
    (* Destruct as per Dan's notes, three ways. t = alpha, beta or other. *)
    destruct (beq_tvar t alpha); destruct (beq_tvar t beta).
    admit.
    admit.
    admit.
    admit.
   Case "cint".
    crush.
   Case "(cross t t0)".
    crush.
   Case "(arrow t t0)".
    crush.
   Case "(ptype t)".
    crush.
   Case "(utype t k t0)".
    crush.
   Case "(etype p t k t0)".
    crush.
Qed.

(* TODO Dan, are these induction on AKder or Kder?  I think the Kder. *)

Lemma A_6_Substitution_1:
  forall (d : Delta)  (tau : Tau) (k: Kappa),
    AK d tau k -> 
    forall (alpha : TVar) (tau' : Tau) (k' : Kappa),
      K ([(alpha,k)] ++ d) tau' k' ->
      K d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d tau k AKder alpha tau' k' Kder.
  K_ind_cases (induction Kder) Case.

  Case "K d cint B".
   simpl.
   constructor.
  Case "K d (tv_t alpha) B".
   admit.
  Case "K d (ptype (tv_t alpha)) B".
   admit.
  Case "K d tau A".
   constructor.
   assumption.
  Case "K d (cross t0 t1) A".
   unfold subst_Tau.
   fold subst_Tau.
   apply K_cross; try assumption.
  Case "K d (arrow t0 t1) A".
   unfold subst_Tau.
   fold subst_Tau.
   apply K_arrow; try assumption.
  Case "K d (ptype tau) B".
   unfold subst_Tau.
   fold subst_Tau.
   constructor.
   assumption.
  Case "K d (utype alpha k tau) A".
   unfold subst_Tau.
   fold subst_Tau.
   apply K_utype; try assumption.
   (* Where did d0 come from? *)
   admit.
   admit.
   admit.
  Case "K d (etype p alpha k tau) A)".
   admit.
Qed.

Lemma A_6_Substitution_2:
  forall (d : Delta)  (tau : Tau) (k : Kappa),
    AK d tau k -> 
    forall (alpha : TVar) (tau' : Tau) (k' : Kappa), 
      AK ([(alpha,k)] ++ d) tau' k' ->
      AK d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d tau k AKder alpha tau' k' AKder2.
  AK_ind_cases (induction AKder) Case. 
  Case "AK d (tv_t alpha) A".
   constructor.
   (* apply A_6_Substitution_1 
     with (alpha:= alpha) (tau':= tau') (k:= k) (k':= k) in AKder.*)
   admit. (* Where is d0 coming from? *)
  Case "AK d (subst_Tau (tv_t alpha0) alpha k) A".
   inversion AKder2.
   crush.
   apply A_6_Substitution_1 
     with (alpha:= alpha) (tau':= tau') (k:= k') (k':= k') in AKder2.
   admit.
   admit.
   crush.
   admit. (* Not liking this at all. *)
Qed.

Lemma A_6_Substitution_3:
  forall (d : Delta) (tau : Tau) (k : Kappa),
    AK d tau k -> 
    forall (alpha : TVar) (tau' : Tau),
      ASGN ([(alpha, k)] ++ d) tau' ->
      ASGN d (subst_Tau tau' tau alpha).
Proof.
  intros d tau k AKder.
  AK_ind_cases (induction AKder) Case.
  Case "AK d (tv_t alpha) A".
   intros.
   inversion H0.
   SCase "cint".
    simpl.
    constructor.
   SCase "(tv_t t)".
    admit.
   SCase "(ptype t)".
    simpl.
    constructor.
   SCase "(cross t t0)".
    admit.
   SCase "(arrow t t0)".
    admit.
   SCase "(utype t k t0)".
    admit.
   SCase "(etype p t k t0)".
    admit.
  Case "AK d (subst_Tau (tv_t alpha0) alpha k) A"  .
   admit.
Qed.

(* unbound d0 down there so is the induction right*) 
(*  intros d tau k AKder alpha tau' ASGNder.
  ASGN_ind_cases (induction ASGNder) Case.
  Case "ASGN d cint".
   simpl.
   constructor.
  Case "ASGN d (tv_t alpha)".
   admit.
  Case "ASGN d (ptype tau)".
   simpl.  
   constructor.
  Case "ASGN d (cross t0 t1)".
   simpl.
   constructor; try assumption.
  Case "ASGN d (arrow t0 t1)".
   simpl.
   constructor; try assumption.
  Case "ASGN d (utype alpha k tau)".
   simpl. (* What the heck is d0? *)
   constructor; try assumption.

  Case "ASGN d (etype nowitnesschange alpha k tau))".
   admit.
*)

(* Do I have to move the inductive definition to the top? *)
Lemma A_6_Substitution_4:
  forall (alpha : TVar) (k : Kappa) (d : Delta) (g : Gamma),
    WFDG ([(alpha,k)] ++ d) g ->
      forall (tau : Tau), 
        AK d tau k -> 
        WFDG d (subst_Gamma g tau alpha).
Proof.
  intros alpha k d g WFDGder.
  WFDG_ind_cases (induction WFDGder) Case.
  Case "WFDG d []".
   intros.
   simpl.
   constructor.
  Case "WFDG d ([(x, tau)] ++ g)".
   intros.
   simpl.
   constructor.
   admit.
   inversion H1.
   crush.
   admit.
   admit.
   admit.
  Case "WFDG ([(alpha, k)] ++ d) g".
   intros.
   admit.
Qed.

Lemma A_6_Substitution_5:
  forall (alpha : TVar) (k : Kappa) (d : Delta) (u : Upsilon)  (g : Gamma),
    WFC ( [(alpha,k)] ++ d) u g ->
    forall (tau : Tau) ,
      AK d tau k -> 
      WFC d u (subst_Gamma g tau alpha).
Proof.
  intros alpha k d u g WFCder.
  inversion WFCder.
  intros.
  constructor; try assumption.
  inversion H; try assumption.
  apply A_6_Substitution_4 with (k:=k); try assumption.
Qed.

(* Thesis Bug, no AK is required. *)
Lemma A_6_Substitution_6: 
  forall (s : St),
      ret s ->
      forall (alpha : TVar) (tau : Tau),
        ret (subst_St s tau alpha).
Proof.
  intros s retder.
  induction retder.
  (* crush gets 0. *)
  (* I can do these by hand or build an Ltac to do them. *)
  intros alpha tau.
  destruct e; 
    try (try intros alpha; try compute; constructor).
  
  Ltac foldunfold' :=
    try (intros alpha;
         unfold subst_St;
         fold subst_E;
         fold subst_St;
         constructor;
         crush).

  Case "ret (if_s e s1 s2)".
    foldunfold'.

  Case "ret (seq s s') 1".
   foldunfold'.

  Case "ret (seq s s') 2".
    intros alpha tau.
    unfold subst_St.
    fold subst_E.
    fold subst_St.
    apply ret_seq_2. (* Constructor takes the first rule, not all cases. *)
    crush.

  Case "ret (letx x e s)".
   foldunfold'.

  Case "ret (open e alpha x s)".
   intros alpha0 tau0.
   unfold subst_St.
   fold subst_E.
   fold subst_St.
   specialize (IHretder alpha0 tau0).
   constructor.
   assumption.

  Case "ret (openstar e alpha x s))".
   intros alpha0 tau0.
   unfold subst_St.
   fold subst_E.
   fold subst_St.
   specialize (IHretder alpha0 tau0).
   constructor.
   assumption.
Qed.


Lemma A_6_Substitution_7:
  forall (u : Upsilon) (x : EVar) (p p': P) (t1 t2: Tau),
    gettype u x p t1 p' t2 ->
    forall (d: Delta) (tau : Tau) (k : Kappa) (alpha : TVar),
      AK d tau k -> 
      WFU u ->
        gettype u x p (subst_Tau t1 tau alpha) p' (subst_Tau t2 tau alpha).
Proof.
  intros u x p p' t1 t2 gettypder.
  gettype_ind_cases (induction gettypder) Case.
  Case "gettype u x p tau [] tau".
   intros.
   constructor.
  Case "gettype u x p (cross t0 t1) (i_pe zero_pe :: p') tau".
   intros.
   simpl.
   constructor.
   apply IHgettypder with (alpha:= alpha) in H; try assumption.
  Case "gettype u x p (cross t0 t1) (i_pe one_pe :: p') tau".
   intros.
   simpl.
   constructor.
   apply IHgettypder with (alpha:= alpha) in H; try assumption.
  Case "gettype u x p (etype aliases alpha k tau') (u_pe :: p') tau)".
   intros.
   simpl.
   apply gettype_etype with (tau'':= tau''); try assumption.
   apply IHgettypder with 
    (d:= d) (tau0:= tau') (k:=k0) (alpha0:= alpha0) in H0; try assumption.
   (* It's failing to generalize alpha in the IH. *)
   admit.
   
Qed.

(* Dan, is that last ltyp supposed to be an styp? *)

(* Need three of these. *)
Lemma A_6_Substitution_8_1_2_3:
  forall (d : Delta) (tau : Tau) (k : Kappa),
    AK d tau k ->
    forall (alpha : TVar) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
            (d' : Delta),
      ltyp d u g e tau' ->
      d = ([(alpha,k)] ++ d') ->
      ltyp d u (subst_Gamma g tau alpha)
           (subst_E e tau alpha)
           (subst_Tau tau' tau alpha).
Proof.
  intros d tau k AKder.
  intros alpha u g e tau' d' ltypder.
  ltyp_ind_mutual_cases 
    (apply (ltyp_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              d = ([(alpha,k)] ++ d') ->
              styp d u (subst_Gamma g tau alpha)
                   (subst_Tau tau' tau alpha)
                   (subst_St s tau alpha))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
                (lt : ltyp d u g  e tau') =>
              d = ([(alpha,k)] ++ d') ->
              ltyp d u (subst_Gamma g tau alpha)
                   (subst_E e tau alpha)
                   (subst_Tau tau' tau alpha))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              d = ([(alpha,k)] ++ d') ->
              rtyp d u (subst_Gamma g tau alpha)
                   (subst_E e tau alpha)
                   (subst_Tau tau' tau alpha)))) Case; crush.
  (* crush gets one. *)
Admitted.    

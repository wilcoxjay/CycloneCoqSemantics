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

Lemma A_4_Useless_Substitutions_1:
  forall (d : Delta) (tau' : Tau) (k : Kappa),
    K d tau' k ->
    forall(alpha : TVar),
      getD d alpha = None ->
      forall (tau : Tau),
        subst_Tau tau' tau alpha = tau'.
Proof.
  intros d tau' k Kder.
  K_ind_cases(induction Kder) Case.
  Case "K d cint B".
   crush.
  Case "K d (tv_t alpha) B".
   intros alpha0 getalpha0 tau. 
   destruct alpha0.
   destruct alpha.
   destruct d.
   SCase "d=[] false".
    inversion H.
   SSCase "d has a member".
    apply getD_Some_None_Implies_Different_Variables with (n':= n) in H.
    unfold subst_Tau.
    rewrite H.
    reflexivity.
    assumption.
  Case "K d (ptype (tv_t alpha)) B".
   intros alpha0 getalpha0 tau.
   destruct alpha.
   destruct alpha0.
   destruct d.
   SCase "d=[] false".
    inversion H.
   SCase "d has a member".
    apply getD_Some_None_Implies_Different_Variables with (n':=n0) in H.
    unfold subst_Tau.
    rewrite H.
    reflexivity.
    assumption.
  Case "K d tau A".
   crush.
  Case "K d (cross t0 t1) A".
   crush.
  Case "K d (arrow t0 t1) A".
   crush.
  Case "K d (ptype tau) B".
   crush.
(* TODO Alpha conversion should fuck this up. *)
  Case "K d (utype alpha k tau) A".
   intros alpha0 getdalpha0 tau0.
   destruct alpha.
   destruct alpha0.
   unfold subst_Tau.
   fold subst_Tau.
   specialize (IHKder (tvar n0)). (* n or n0? *)
   assert (A: getD ([(tvar n, k)] ++ d) (tvar n0) = None).
   assert (AB: n <> n0).
   admit. (* Alpha binding admit. *)
   SCase "add_alpha_to_Delta_get_beta_None_still_None".
    admit.
    intros.
    admit.
   Case "K d (etype p alpha k tau) A)".
Admitted.

(* use subst_Gamma_over_app *)
Lemma A_4_Useless_Substitutions_2:
  forall (d : Delta) (alpha : TVar),
    getD d alpha = None ->
    forall (g : Gamma), 
      WFDG d g ->
      forall (tau : Tau) ,
        subst_Gamma g tau alpha = g.
Proof.
  intros d alpha getd g wfdgder.
  induction wfdgder. 
  crush. (* the base case. *)
  Case "subst_Gamma (g ++ [(x, tau)]) tau0 alpha = g ++ [(x, tau)]".
   intros tau0.
   (* Linear logic bullshit, how many do I need? *)
   inversion getd.
   inversion getd.
   apply IHwfdgder with (tau:=tau0) in getd.
   functional induction (subst_Gamma g tau0 alpha ).
(*
    SCase "g=[]".
     rewrite app_nil_l.
     apply IHwfdgder with (tau:=tau0) in H2.
     unfold subst_Gamma.
     assert (A: subst_Tau tau tau0 alpha = tau).
     apply A_4_Useless_Substitutions_1 with (d:=d) (k:=A).
     assumption.
     assumption.
     rewrite A.
     reflexivity.
    SCase "weird looking, why am I here? ".
     inversion wfdgder.
(*
     rewrite subst_Gamma_over_app with (x:= ((x0, tau') :: g')).
*)    
     admit. (* How do I inverse through the getd list ? *)
(*
     apply IHg0 in A.
     admit.
     inversion wfdgder; try assumption.
     admit.
     intros.
     crush.
     admit.
     assumption.
     assumption.
*)
*)
Admitted.

Lemma A_4_Useless_Substitutions_3:
  forall (d : Delta) (alpha : TVar),
    getD d alpha = None ->
    forall (u : Upsilon),
      WFU u ->
      forall (x : EVar) (p : P) (tau': Tau),
        getU u x p tau' ->
        forall (tau : Tau),
          subst_Tau tau' tau alpha = tau'.
Proof.
  intros d alpha getd u wfuder.
  WFU_ind_cases (induction wfuder) Case.
  (* apply A_4_Useless_Substitutions_1. *)
Admitted.

(* TODO do I have the ordering right? *)
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
  (Tau_ind_cases (induction t0) Case); crush.
  (* crush leaves 1/7. *)
  (* Need a working tautology on variable equality. *)
  Case "(tv_t t)".
  admit.
Qed.

(* TODO Dan, are these induction on AKder or Kder?  I think the If der not the
  suppose der. *)
Lemma A_6_Substitution_1:
  forall (d : Delta)  (tau : Tau) (k: Kappa),
    AK d tau k -> 
    forall (alpha : TVar) (tau' : Tau) (k' : Kappa),
      K ([(alpha,k)] ++ d) tau' k' ->
      K d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d tau k.
  intros AKder alpha tau' k' Kder.
  (* induction AKder; destruct tau'. (* TODO is this right? *) *)
  Tau_ind_cases (induction tau') Case.
  (* Crush gets 0. *)
Admitted.    

Lemma A_6_Substitution_2:
  forall (d : Delta)  (tau : Tau) (k : Kappa),
    AK d tau k -> 
    forall (alpha : TVar) (tau' : Tau) (k' : Kappa), 
      AK ([(alpha,k)] ++ d) tau' k' ->
      AK d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d alpha tau tau' k k'.
  intros AKder AKder2.
  AK_ind_cases (induction AKder2) Case.
  (* crush gets 0. *)
Admitted.    

Lemma A_6_Substitution_3:
  forall (d : Delta) (tau : Tau) (k : Kappa),
    AK d tau k -> 
    forall (alpha : TVar) (tau' : Tau),
      ASGN ([(alpha, k)] ++ d) tau' ->
      ASGN d (subst_Tau tau' tau alpha).
Proof.
  intros d tau k.
  intros AKder.
  intros alpha tau'.
  intros asgnder.
  ASGN_ind_cases (induction asgnder) Case.
  (* crush gets 0. *)
Admitted.    

Lemma A_6_Substitution_4:
  forall (d : Delta) (tau : Tau) (k : Kappa),
    AK d tau k -> 
    forall (alpha : TVar)  (g : Gamma),
      WFDG ([(alpha,k)] ++ d) g ->
      WFDG d (subst_Gamma g tau alpha).
Proof.
  intros d tau k.
  intros AKder.
  intros alpha g.
  intros WFDGder.
  WFDG_ind_cases (induction WFDGder) Case.
  (* crush gets 0. *)
Admitted.    

Lemma A_6_Substitution_5:
  forall (d : Delta) (tau : Tau) (k : Kappa),
    AK d tau k -> 
    forall (u : Upsilon) (alpha : TVar) (g : Gamma),
      WFC ( [(alpha,k)] ++ d) u g ->
      WFC d u (subst_Gamma g tau alpha).
Proof.
  intros d tau k.
  intros AKder.
  intros u alpha g.
  intros WFCder.
  (* Corrollary to the previous lemma. *)
Admitted.    

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
  forall (d: Delta) (tau : Tau) (k : Kappa), 
    AK d tau k -> 
    forall (u : Upsilon),
      WFU u ->
      forall (x : EVar) (p p': P) (t1 t2: Tau),
        gettype u x p t1 p' t2 ->
        forall (alpha : TVar),
          gettype u x p (subst_Tau t1 tau alpha) p' (subst_Tau t2 tau alpha).
Proof.
  intros d tau k AKder u WFUder x p p' t1 t2.
  intros gettypder.
  gettype_ind_cases (induction gettypder) Case.
Admitted.    

(* Dan, is that last ltyp supposed to be an styp? *)

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

  ltyp_ind_cases 
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

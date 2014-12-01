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

(* TODO how to prove these? *)
Lemma getD_Some_None_Implies_Different_Variables:
  forall (d : Delta) (n : nat) (k : Kappa),
      getD d (tvar n ) = Some k ->
      forall (n' : nat),
        getD d (tvar n') = None ->
        beq_nat n' n = false.
Proof.
  intros d n k.
  induction d.
  Case "d = []".
   discriminate.
  Case "d = a :: d".
   intros getdadnsome n'.
   intros getdadn'none.
   unfold getD in getdadnsome.
   fold getD in getdadnsome.
Admitted.

Lemma getD_None_None_Implies_Different_Variables:
  forall (d : Delta) (n n' : nat) (k : Kappa),
    (* TODO d <> nil *)
    getD d (tvar n ) = None ->
    getD (d ++ [(tvar n, k)]) (tvar n') = None ->
    beq_nat n' n = false.
Proof.
Admitted.

Lemma add_alpha_to_Delta_get_beta_None_still_None :
  forall (d : Delta) (n n0 : nat) (k : Kappa),
    n <> n0 ->
    getD d (tvar n0) = None ->
    getD (d ++ [(tvar n, k)]) (tvar n0) = None.
Proof.
Admitted.                       

Lemma A_4_Useless_Substitutions_1:
  forall (d : Delta) (tau' : Tau) (k : Kappa),
    K d tau' k ->
    forall(alpha : TVar),
      getD d alpha = None ->
      forall (tau : Tau),
        subst_Tau tau' tau alpha = tau'.
Proof.
  intros d tau' k Kder.
  induction Kder.
  Case "cint".
   crush.
  Case "alpha0".
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
  Case "ptype alpha0".
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
  Case "tau0".
   crush.
  Case "cross".
   crush.
  Case "arrow".
   crush.
  Case "ptype tau0".
   crush.
  Case "utype". (* Alpha conversion should fuck this up. *)
   intros alpha0 getdalpha0 tau0.
   destruct alpha.
   destruct alpha0.
   unfold subst_Tau.
   fold subst_Tau.
   specialize (IHKder (tvar n0)). (* n or n0? *)
   assert (A: getD (d ++ [(tvar n, k)]) (tvar n0) = None).
   assert (AB: n <> n0).
   admit. (* Alpha binding admit. *)
   SCase "add_alpha_to_Delta_get_beta_None_still_None".
    apply add_alpha_to_Delta_get_beta_None_still_None; assumption.
   apply IHKder with (tau0:= tau0) in A.
   rewrite A.
   reflexivity.
  Case "etype".
   intros alpha0 getdalpha0 tau0.
   destruct alpha.
   destruct alpha0.
   unfold subst_Tau.
   fold subst_Tau.
   specialize (IHKder (tvar n0)). (* n or n0? *)
   assert (A: getD (d ++ [(tvar n, k)]) (tvar n0) = None).
   assert (AB: n <> n0).
   admit. (* Alpha binding admit. *)
   SCase "add_alpha_to_Delta_get_beta_None_still_None".
    apply add_alpha_to_Delta_get_beta_None_still_None; assumption.
   apply IHKder with (tau0:= tau0) in A.
   rewrite A.
   reflexivity.
Qed.

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
Qed.

Lemma A_4_Useless_Substitutions_3:
  forall (d : Delta) (alpha : TVar),
    getD d alpha = None ->
    forall (u : Upsilon),
      WFU u ->
      forall (x : EVar) (p : P) (tau': Tau),
        getU u x p = Some tau' ->
        forall (tau : Tau),
          subst_Tau tau' tau alpha = tau'.
Proof.
  intros d alpha getd u wfuder.
  induction wfuder.
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
  induction t0.
  (* crush leaves 1/7. *)
  (* Need a working tautology on variable equality. *)
  Case "tv t alpha versus beta".

  admit.
  Case "Other are crushable".
  crush.
  crush.
  crush.
  crush.
  crush.
  crush.
Qed.

(* TODO are these induction on AKder or Kder?  I think the If der not the
  suppose der. *)
Lemma A_6_Substitution_1:
  forall (d : Delta)  (tau : Tau) (k: Kappa),
    AK d tau k -> 
    forall (alpha : TVar) (tau' : Tau) (k' : Kappa),
      K (d ++ [(alpha,k)]) tau' k' ->
      K d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d tau k.
  intros AKder alpha tau' k' Kder.
  (* induction AKder; destruct tau'. (* TODO is this right? *) *)
  induction tau'.
  (* Crush gets 0. *)
Admitted.    

Lemma A_6_Substitution_2:
  forall (d : Delta)  (tau : Tau) (k : Kappa),
    AK d tau k -> 
    forall (alpha : TVar) (tau' : Tau) (k' : Kappa), 
      AK (d ++ [(alpha,k)]) tau' k' ->
      AK d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d alpha tau tau' k k'.
  intros AKder AKder2.
  induction AKder2.
  (* crush gets 0. *)
Admitted.    

Lemma A_6_Substitution_3:
  forall (d : Delta) (tau : Tau) (k : Kappa),
    AK d tau k -> 
    forall (alpha : TVar) (tau' : Tau),
      ASGN (d ++ [(alpha, k)]) tau' ->
      ASGN d (subst_Tau tau' tau alpha).
Proof.
  intros d tau k.
  intros AKder.
  intros alpha tau'.
  intros asgnder.
  induction asgnder.
  (* crush gets 0. *)
Admitted.    

Lemma A_6_Substitution_4:
  forall (d : Delta) (tau : Tau) (k : Kappa),
    AK d tau k -> 
    forall (alpha : TVar)  (g : Gamma),
      WFDG (d ++ [(alpha,k)]) g ->
      WFDG d (subst_Gamma g tau alpha).
Proof.
  intros d tau k.
  intros AKder.
  intros alpha g.
  intros WFDGder.
  induction WFDGder.
  (* crush gets 0. *)
Admitted.    

Lemma A_6_Substitution_5:
  forall (d : Delta) (tau : Tau) (k : Kappa),
    AK d tau k -> 
    forall (u : Upsilon) (alpha : TVar) (g : Gamma),
      WFC (d ++ [(alpha,k)]) u g ->
      WFC d u (subst_Gamma g tau alpha).
Proof.
  intros d tau k.
  intros AKder.
  intros u alpha g.
  intros WFCder.
  induction WFCder; crush.
(* crush gets 0. *)
  (* TODO is this right? 1 goal?*)
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

  Case "if".
    foldunfold'.

  Case "seq s s' ret s.".
   foldunfold'.

  Case "seq s s' ret s'.".
    intros alpha tau.
    unfold subst_St.
    fold subst_E.
    fold subst_St.
    apply ret_seq_2. (* Constructor takes the first rule, not all cases. *)
    crush.

  Case "letx".
   foldunfold'.

  Case "open".
   intros alpha0 tau0.
   unfold subst_St.
   fold subst_E.
   fold subst_St.
   specialize (IHretder alpha0 tau0).
   constructor.
   assumption.

  Case "openstar".
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
        gettype u x p t1 p' = Some t2 ->
        forall (alpha : TVar),
          gettype u x p (subst_Tau t1 tau alpha) p' = 
          Some (subst_Tau t2 tau alpha).
Proof.
  intros d tau k AKder u WFUder x p p' t1 t2.
  functional induction (gettype u x p t1 p'); crush. (* or is it on WFUder? *)
  (* crush gets 24/26. *)
Admitted.    

(* Dan, is that last ltyp supposed to be an styp? *)

Lemma A_6_Substitution_8_1_2_3:
  forall (d : Delta) (tau : Tau) (k : Kappa),
    AK d tau k ->
    forall (alpha : TVar) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
            (d' : Delta),
      ltyp d u g e tau' ->
      d = (d' ++ [(alpha,k)]) ->
      ltyp d u (subst_Gamma g tau alpha)
           (subst_E e tau alpha)
           (subst_Tau tau' tau alpha).
Proof.
  intros d tau k AKder.
  intros alpha u g e tau' d' ltypder.

  (* TODO is this right? No variable binding issues. *)
  apply (typ_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              styp d u g t s -> 
              d = (d' ++ [(alpha,k)]) ->
              styp d u (subst_Gamma g tau alpha)
                   (subst_Tau tau' tau alpha)
                   (subst_St s tau alpha))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
                (lt : ltyp d u g  e tau') =>
              ltyp d u g  e tau' -> 
              d = (d' ++ [(alpha,k)]) ->
              ltyp d u (subst_Gamma g tau alpha)
                   (subst_E e tau alpha)
                   (subst_Tau tau' tau alpha))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              rtyp d u g e t -> 
              d = (d' ++ [(alpha,k)]) ->
              rtyp d u (subst_Gamma g tau alpha)
                   (subst_E e tau alpha)
                   (subst_Tau tau' tau alpha))).
  Focus 27.
  (* crush gets zero. *)
Admitted.    

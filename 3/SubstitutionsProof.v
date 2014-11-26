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

(* Alpha conversion is required? *)

Lemma A_4_Useless_Substitutions_1:
  forall (d : Delta) (alpha : TVar) (tau tau' : Tau) (k : Kappa),
    getD d alpha = None ->
    K d tau' k ->
    subst_Tau tau' tau alpha = tau'.
Proof.
  intros d alpha tau tau' k.
  intros gd Kder.
  induction Kder; crush.
  (* Crush gets 5/9 goals. *)
  Focus 3.
  
Admitted.    

Lemma A_4_Useless_Substitutions_2:
  forall (d : Delta) (alpha : TVar) (tau tau' : Tau) (g : Gamma),
    getD d alpha = None ->
    WFDG d g ->
    subst_Gamma g tau alpha = g.
Proof.
  intros d alpha tau tau' k.
  intros gd Kder.
  induction Kder.
  reflexivity.
  (* TODO this is just messed up with repeated hypotheses. *)
  functional induction (subst_Gamma (g ++ [(x, tau0)]) tau alpha).
  reflexivity.
  assert (gd': getD d alpha = None).
  assumption.
  apply IHg0 in gd'.
  rewrite gd'.
  (* Apply theorem and we're done. *)
  Focus 2.
  assumption.
  assert (J: subst_Tau tau'0 tau alpha = tau'0).
  apply A_4_Useless_Substitutions_1 with (d:=d) (k:=A).
  assumption.
  Focus 2.
  rewrite J.
  reflexivity.
Admitted.    


Lemma A_4_Useless_Substitutions_3:
  forall (d : Delta) (alpha : TVar) (tau tau': Tau) (u : Upsilon) (p : P)
         (x : EVar),
    getD d alpha = None ->
    WFU u ->
    getU u x p = Some tau' ->
    subst_Tau tau' tau alpha = tau'.
Proof.
  intros d alpha tau tau' u p x.
  intros getder WFUder.
  induction WFUder.
  intros false.
  destruct x; discriminate. 
  (* or destruct x; inversion false. *)
  (* apply A_4_Useless_Substitutions_1. *)
Admitted.


(* TODO do I have the ordering right? *)
Lemma A_5_Commuting_Substitutions:
  forall (alpha beta : TVar) (t0 t1 t2 : Tau),
    NotFreeInTau beta t2 = true ->
    (subst_Tau (subst_Tau t0 t1 beta) t2 alpha) = 
    (subst_Tau (subst_Tau t0 t2 alpha)
               (subst_Tau t1 t2 alpha)
               beta).
Proof.
  intros alpha beta t0 t1 t2.
  intros NF.
  induction t0.
  (* crush get's 6/7. *)
  (* So I get an uncrushed goal to work on. *)
  Focus 2.
  crush.
  Focus 2.
  crush.
  Focus 2.
  crush.
  Focus 2.
  crush.
  Focus 2.
  crush.
  Focus 2.
  crush.

  assert (A: (t = beta  /\ t <> alpha) \/
             (t = alpha \/ t <> beta) \/
             (t <> beta /\ t <> alpha) \/ 
             (t = beta /\ t = alpha)).
  Focus 2.
  destruct A.
  destruct H.
  rewrite H.
(*  reflexivity. *)
Admitted.

Lemma A_6_Substitution_1:
  forall (d : Delta) (alpha : TVar) (tau tau' : Tau) (k k': Kappa),
    AK d tau k -> 
    K (d ++ [(alpha,k)]) tau' k' ->
    K d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d alpha tau tau' k k'.
  intros AKder Kder.
  induction Kder.
  (* Crush gets 0. *)
Admitted.    

Lemma A_6_Substitution_2:
  forall (d : Delta) (alpha : TVar) (tau tau' : Tau) (k k': Kappa),
    AK d tau k -> 
    AK (d ++ [(alpha,k)]) tau' k' ->
    AK d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d alpha tau tau' k k'.
  intros AKder AKder2.
  induction AKder2.
  (* crush gets 0. *)
Admitted.    

Lemma A_6_Substitution_3:
  forall (d : Delta) (alpha : TVar) (tau tau' : Tau) (k : Kappa),
    AK d tau k -> 
    ASGN (d ++ [(alpha, k)]) tau' ->
    ASGN d (subst_Tau tau' tau alpha).
Proof.
  intros d alpha tau tau' k k'.
  intros ASGNder.
  induction ASGNder.
  (* crush gets 0. *)
Admitted.    

Lemma A_6_Substitution_4:
  forall (d : Delta) (alpha : TVar) (tau : Tau) (g : Gamma) (k : Kappa),
    AK d tau k -> 
    WFDG (d ++ [(alpha,k)]) g ->
    WFDG d (subst_Gamma g tau alpha).
Proof.
  intros d alpha tau tau' k AKder.
  intros WFDGder.
  induction WFDGder.
  (* crush gets 0. *)
Admitted.    

Lemma A_6_Substitution_5:
  forall (d : Delta) (u : Upsilon ) (alpha : TVar) (tau : Tau) 
         (g : Gamma) (k : Kappa),
    AK d tau k -> 
    WFC (d ++ [(alpha,k)]) u g ->
    WFC d u (subst_Gamma g tau alpha).
Proof.
  intros d u alpha tau g k.
  intros AKder WFCder.
  induction WFCder.
(* crush gets 0. *)
Admitted.    

Lemma A_6_Substitution_6:
  forall (d : Delta) (alpha : TVar) (tau : Tau) (s : St) (k : Kappa),
    AK d tau k -> 
    ret s ->
    ret (subst_St s tau alpha).
Proof.
  intros d alpha tau s k AKder retder.
  induction retder.
  (* crush gets 0. *)
Admitted.    

Lemma A_6_Substitution_7:
  forall (d: Delta) (u : Upsilon ) (alpha : TVar) (x : EVar) 
         (t1 t2 tau : Tau) (p p': P) (k : Kappa),
    AK d tau k -> 
    WFU u ->
    gettype u x p t1 p' = Some t2 ->
    gettype u x p (subst_Tau t1 tau alpha) p' = 
    Some (subst_Tau t2 tau alpha).
Proof.
  intros d u alpha x t1 t2 tau p p' k.
  intros AKder WFUder.
  (* jrw Warning: Collision between bound variables of name t *)
  functional induction (gettype u x p t1 p').
  (* crush gets 24/26. *)
Admitted.    

(* Dan, is that last ltyp supposed to be an styp? *)

Lemma A_6_Substitution_8_1_2_3:
  forall (d d': Delta) (alpha : TVar) (u : Upsilon) (g : Gamma) 
         (e : E) (tau tau' : Tau) (k : Kappa),
    AK d tau k ->
    ltyp (d ++ [(alpha,k)]) u g e tau' ->
    d = (d' ++ [(alpha,k)]) ->
    ltyp d u (subst_Gamma g tau alpha)
         (subst_E e tau alpha)
         (subst_Tau tau' tau alpha).
Proof.
  intros d d' alpha u g e tau tau' k.
  intros AKder D'.
  apply (typ_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              d = (d' ++ [(alpha,k)]) ->
              styp d u (subst_Gamma g tau alpha)
                   (subst_Tau tau' tau alpha)
                   (subst_St s tau alpha))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
                (lt : ltyp d u g  e tau') =>
              d = (d' ++ [(alpha,k)]) ->
              ltyp d u (subst_Gamma g tau alpha)
                   (subst_E e tau alpha)
                   (subst_Tau tau' tau alpha))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              d = (d' ++ [(alpha,k)]) ->
              rtyp d u (subst_Gamma g tau alpha)
                   (subst_E e tau alpha)
                   (subst_Tau tau' tau alpha))).
  (* crush gets zero. *)
Admitted.    

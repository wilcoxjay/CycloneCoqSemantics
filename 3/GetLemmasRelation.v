(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Useful lemmas about get functions. 

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Import FormalSyntax.
Require Import StaticSemanticsKindingAndContextWellFormedness.

Lemma getU_nil_none:
  forall  (x : EVar) (p : P) (tau : Tau),
     ~(getU [] x p tau).
Proof.
  intros x p tau.
  compute.
  intros.
  inversion H.
Qed.

(* TODO jrw these properties don't hold on nil. *)
Lemma getU_weakening :
  forall (u : Upsilon) (x x': EVar) (p p': P) (tau tau': Tau),
    getU (u ++ [((x', p'),tau')]) x p tau ->
    x <> x' ->
    p <> p' ->
    getU u x p tau.
Proof.
  intros.
  induction u.
  Case "u = []".
   assert (A: ~ getU [] x p tau).
   apply getU_nil_none.
   compute in A.
   admit. (* How do I show this contradiction? *)
  Case "u = a :: u".
   destruct a.
   destruct p0.
   eapply getU_next.
Admitted.  

Lemma getU_partial_function:
  forall (u : Upsilon) (x : EVar) (p : P) (tau : Tau),
    WFU u ->
    getU u x p tau ->
    forall (tau' : Tau),
      getU u x p tau' ->
      tau = tau'.
Proof.
  intros.
  induction u.
  Case "u = []".
   inversion H0.
  Case "a :: u".
   destruct a.
   destruct p0.
   inversion H.   
   apply IHu in H7.
   assumption.
Admitted.

Lemma getU_function_inversion:
  forall (u : Upsilon),
    WFU u ->
    forall  (x : EVar) (p : P) (tau : Tau),
      getU u x p tau ->
      forall (tau' : Tau),
        (getU u x p tau' /\ tau = tau').
Proof.
  intros u WFUder.
  induction (rev u).
  intros.
  split.
  inversion H.
  inversion H.
  intros.
  inversion WFUder.
  crush.
Admitted.

(* TODO not strictly true as d is a list. *)
Lemma getD_weakening_some_left:
  forall (d : Delta) (alpha : TVar) (k : Kappa),
    WFD d ->
     getD d         alpha   = Some k ->
    forall (d' : Delta),
      WFD (d ++ d') -> 
      getD (d ++ d') alpha   = Some k.
Proof.
Admitted.  

Lemma getD_weakening_some_right:
  forall (d : Delta) (alpha : TVar) (k : Kappa),
    WFD d ->
    getD d         alpha   = None ->
    forall (d' : Delta),
      WFD (d ++ d') ->
      getD d'        alpha   = Some k ->
      getD (d ++ d') alpha   = Some k.
Proof.
Admitted. 



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


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

Require Export ListLemmas.
Require Export GetLemmasRelation.


Lemma A_10_Path_Extension_1_A_good_get:
  forall (v v' v0 v1 : E) (p : P),
    Value v  ->
    Value v' ->
    get v p v' ->
    v' = (cpair v0 v1) ->
    (get v (p ++ [i_pe zero_pe]) v0 /\ 
     get v (p ++ [i_pe one_pe]) v1).
Proof.
  intros v v' v0 v1 p Valuev Valuev' getder.
  get_ind_cases (induction getder) Case.
  Case "v [] v".
   intros.
   split.
   SCase "zero_pe".
    rewrite app_nil_l.
    rewrite <- app_nil_r with (l:= [i_pe zero_pe]).
    rewrite H0.
    rewrite H0 in Valuev.
    inversion Valuev.
    apply get_l; try assumption.
    constructor; try assumption.
   SCase "one_pe".
    rewrite app_nil_l.
    rewrite <- app_nil_r with (l:= [i_pe one_pe]).
    rewrite H0.
    rewrite H0 in Valuev.
    inversion Valuev.
    apply get_r; try assumption.
    constructor; try assumption.
  Case "(cpair v0 v1) (i_pe zero_pe :: p) v".
   intros.
   pose proof H0 as Valuev2.
   apply IHgetder in H0; try assumption.
   inversion H0.
   rewrite H2 in Valuev'.
   inversion Valuev'.
   split.
   SCase "zero_pe".
    constructor; try assumption.
   SCase "one_pe".
    constructor; try assumption.
  Case "(cpair v0 v1) (i_pe one_pe :: p) v".
   intros.
   pose proof H1 as Valuev3.
   apply IHgetder in H1; try assumption.
   inversion H1.
   rewrite H2 in Valuev'.
   inversion Valuev'.
   split.
   SCase "zero_pe".
    constructor; try assumption.
   SCase "one_pe".
    constructor; try assumption.
  Case "(pack tau' v1 (etype aliases alpha k tau)) (u_pe :: p)v".
   intros.
   pose proof H0 as Valuev2'.
   apply IHgetder in H0; try assumption.
   inversion H0.
   rewrite H1 in Valuev'.
   inversion Valuev'.
   split.
   SCase "zero_pe".
    constructor; try assumption.
   SCase "one_pe".
    constructor; try assumption.
Qed.

Lemma A_10_Path_Extension_1_A:
  forall (v v' v0 v1 : E) (p : P),
    Value v  ->
    Value v' ->
    get v p v' ->
    v' = (cpair v0 v1) ->
    (~get v (p ++ [i_pe zero_pe]) v0 /\ ~get v (p ++ [i_pe one_pe]) v1) ->
    forall (p' : P) (v'' : E),
      ~(get v (p ++ [i_pe one_pe] ++ p') v'') /\
      ~(get v (p ++ [i_pe zero_pe] ++ p') v'').
Proof.
  intros v v' v0 v1 p Valuev Valuev' getder.
  intros.
  inversion H0.
  split.
  unfold not.
  intros.
  induction H3.
  
  admit.
  admit.
  admit.
  admit.
  admit.
Qed.

Lemma A_10_Path_Extension_1_B_good_get:
  forall (v v' v0 : E) (tau tau' : Tau) (alpha : TVar) (k : Kappa)
         (p : P),
    Value v  ->
    Value v' ->
    get v p v' ->
    v' = (pack tau' v0 (etype aliases alpha k tau)) ->
    get v (p ++ [u_pe]) v0 .
Proof.
  intros v v' v0 tau tau' alpha k p Valuev Valuev' getder.
  get_ind_cases (induction getder) Case.  
  Case "v [] v".
   intros.
   rewrite app_nil_l.
   rewrite <- app_nil_r with (l:= [u_pe]).
   rewrite H0 in Valuev.
   inversion Valuev; try assumption.
   rewrite H0.
   constructor; try assumption.
   constructor; try assumption.
  Case "(cpair v0 v1) (i_pe zero_pe :: p) v".
   intros.
   pose proof H0 as Valuev1'.
   apply IHgetder in H0; try assumption.
   constructor; try assumption.
   inversion H0; try assumption.
  Case "(cpair v0 v1) (i_pe one_pe :: p) v".
   intros.
   pose proof H1 as Valuev2'.
   apply IHgetder in H1; try assumption.
   constructor; try assumption.
   inversion H1; try assumption.
  Case "(pack tau' v1 (etype aliases alpha k tau)) (u_pe :: p)v".
   intros.
   pose proof H0 as Valuev1'.
   apply IHgetder in H0; try assumption.
   rewrite H1 in Valuev'.
   inversion Valuev'.
   constructor; try assumption.
Qed.
  
Lemma A_10_Path_Extension_1_B:
  forall (v v' v0 : E) (tau tau' : Tau) (alpha : TVar) (k : Kappa)
         (p : P),
    Value v  ->
    Value v' ->
    get v p v' ->
    v' = (pack tau' v0 (etype aliases alpha k tau)) ->
    get v (p ++ [u_pe]) v0 \/
     forall (p' : P) (v'' : E),
      ~(get v (p ++ [u_pe] ++ p') v'').
Proof.
  intros v v' v0 v1 p.
  intros valv valv' getvpv'.
  (* induction n. Not likely. *)
  (* crush gets 0. *)
Admitted.

Lemma A_10_Path_Extension_2_A:
  forall (u : Upsilon) (x : EVar) (p p' : P) (tau tau' t0 t1 : Tau)
         (n : nat),
    gettype u x p tau p' tau' ->
    tau' = (cross t0 t1) ->
    (gettype u x p tau (p' ++ [i_pe zero_pe]) t0  /\
     gettype u x p tau (p' ++ [i_pe one_pe])  t1).
Proof.
  intros u x p p' tau tau' t0 t1 n gettypeder.
  gettype_ind_cases (induction gettypeder) Case.
  Case "gettype u x p tau [] tau".
   intros.
   split.
   rewrite H.
   constructor; try assumption.
   constructor.
   rewrite H.
   constructor; try assumption.
   constructor.
  Case "gettype u x p (cross t0 t1) (i_pe zero_pe :: p') tau".
   intros.
   rewrite H in gettypeder.
   apply IHgettypeder in H.
   inversion H.
   split.
   constructor; try assumption.
   constructor; try assumption.
  Case "gettype u x p (cross t0 t1) (i_pe one_pe :: p') tau".
   intros.
   rewrite H in gettypeder.
   apply IHgettypeder in H.
   inversion H.
   split.
   constructor; try assumption.
   constructor; try assumption.
  Case "gettype u x p (etype aliases alpha k tau') (u_pe :: p') tau)".
   intros.
   rewrite H0 in gettypeder.
   apply IHgettypeder in H0; try assumption.
   inversion H0; try assumption.
   split.
   SCase "left".
    rewrite <- app_assoc.
    apply gettype_etype with (tau'':= tau''); try assumption.
   SCase "right".
    rewrite <- app_assoc.
    apply gettype_etype with (tau'':= tau''); try assumption.
Qed.  
  
Lemma A_10_Path_Extension_2_B:
  forall (u : Upsilon) (x : EVar) (p : P) (tau : Tau) (p' : P) (tau' : Tau),
    gettype u x p tau p' tau' ->
    forall (alpha : TVar) (k : Kappa) (t0: Tau), 
      tau' = (etype aliases alpha k t0) ->
      forall (tau'' : Tau), 
        getU u x p tau'' ->
        gettype u x p tau (p' ++ [u_pe]) (subst_Tau t0 tau'' alpha).
Proof.
  intros u x p tau p' tau' gettypeder.
  gettype_ind_cases (induction gettypeder) Case.
  Case "gettype u x p tau [] tau".
   intros.
   rewrite H.
   rewrite app_nil_l.
   rewrite <- app_nil_r with (l:= [u_pe]).
   apply gettype_etype with (tau'':= tau'');  try assumption.
   constructor.
  Case "gettype u x p (cross t0 t1) (i_pe zero_pe :: p') tau".
   intros.
   rewrite <- app_assoc.
   constructor; try assumption.
   apply IHgettypeder with (tau'':= tau'') in H; try assumption.
   admit. (* GetU wrong path? *)
  Case "gettype u x p (cross t0 t1) (i_pe one_pe :: p') tau".
   intros.
   rewrite <- app_assoc.
   constructor; try assumption.
   apply IHgettypeder with (tau'':= tau'') in H; try assumption.
   admit.
  Case "gettype u x p (etype aliases alpha k tau') (u_pe :: p') tau)".
   intros.
   rewrite <- app_assoc.
   apply gettype_etype with (tau'':= tau''); try assumption.
   apply IHgettypeder with (k:= k0); try assumption.
   admit. (* GetU wrong path ? *)
Qed.

(* Fix p problem in inductive cases. *)
(* Hypotheses:
    a) gettype is broken - I can't see it.
    b) theorem statement is broken.
       i) drop u_pe from p'.- no
       ii) add it in getU?
    c) induction is broken in that p is being changed. 
    d) I'm missing a way to find this even though it's contradictory.
    e) I should be able to unify the added path element, which is nonsense.
    f) The theorem is wrong for etypes. Which I doubt.
    g) The theorem statement is too weak. 
    h) The theorem is not provable on the gettype derivation.
       Must use path's or getU derivation. - not likely either
          as the other cases proved out right.
*)
Lemma A_10_Path_Extension_2_B':
  forall (u : Upsilon) (x : EVar) (p : P) (tau : Tau) (p' : P) (tau' tau'': Tau),
    gettype u x p tau p' tau' ->
    forall (alpha : TVar) (k : Kappa) (t0: Tau), 
      tau' = (etype aliases alpha k t0) ->
      getU u x p tau'' ->
      gettype u x p tau (p' ++ [u_pe]) (subst_Tau t0 tau'' alpha).
Proof.
  intros u x p tau p' tau' tau'' gettypeder.
  gettype_ind_cases (induction gettypeder) Case.
  Case "gettype u x p tau [] tau".
   intros.
   rewrite H.
   rewrite app_nil_l.
   rewrite <- app_nil_r with (l:= [u_pe]).
   apply gettype_etype with (tau'':= tau'');  try assumption.
   constructor.
  Case "gettype u x p (cross t0 t1) (i_pe zero_pe :: p') tau".
   intros.
   rewrite <- app_assoc.
   constructor; try assumption.
   apply IHgettypeder in H; try assumption.
   admit. (* GetU wrong path? *)
  Case "gettype u x p (cross t0 t1) (i_pe one_pe :: p') tau".
   intros.
   rewrite <- app_assoc.
   constructor; try assumption.
   apply IHgettypeder with (tau'':= tau'') in H; try assumption.
   admit.
  Case "gettype u x p (etype aliases alpha k tau') (u_pe :: p') tau)".
   intros.
   rewrite <- app_assoc.
   apply gettype_etype with (tau'':= tau''); try assumption.
   apply IHgettypeder with (k:= k0); try assumption.
   admit. (* GetU wrong path ? *)
Qed.
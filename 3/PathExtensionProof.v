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

(* Ask Dan if this is correct. 
   TODO Interesting that we have i here where only 0/1 really do. *)
Lemma A_10_Path_Extension_1_A:
  forall (v v' v0 v1 : E) (p : P),
    Value v  ->
    Value v' ->
    get v p v' ->
    v' = (cpair v0 v1) ->
    (get v (p ++ [i_pe zero_pe]) v0 /\ 
     get v (p ++ [i_pe one_pe]) v1) \/
    forall (p' : P) (v'' : E),
      ~(get v (p ++ [i_pe one_pe] ++ p') v'').
Proof.
  intros v v' v0 v1 p.
  intros valv valv' getvpv'.
  (* TODO induction n. not likely *)
Admitted.

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
    gettype u x p tau p' = Some tau' ->
    tau' = (cross t0 t1) ->
    n = length p' ->
    (gettype u x p tau (p' ++ [i_pe zero_pe]) = Some t0  /\
     gettype u x p tau (p' ++ [i_pe one_pe]) = Some t1).
Proof.
  intros.
  induction n.
  (* Wierd, crush gives subgoals. *)
Admitted.

Lemma A_10_Path_Extension_2_B:
  forall (u : Upsilon) (alpha : TVar) (x : EVar) (p p' : P) 
         (tau tau' t0 uxp: Tau) (k : Kappa) (n : nat),
    gettype u x p tau p' = Some tau' ->
    tau' = (etype nowitnesschange alpha k t0) ->
    getU u x p = Some uxp->
    n = length p' ->
    gettype u x p tau (p' ++ [u_pe]) = Some (subst_Tau uxp uxp alpha).
Proof.
  intros.
  induction n. 
  (* crush gets 0. *)
Admitted.


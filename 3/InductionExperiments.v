(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Why can't Brian induct?

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.
Require Import Coq.Program.Equality.

Require Export FormalSyntax.
Require Export GetLemmasRelation.
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
Require Export AlphaConversion.
Require Export WeakeningLemmas.
Require Export VarLemmas.
Require Export PathLemmas.

Lemma K_nil_A_apply_no_der_in_context :
  forall (d : Delta) (tau : Tau) (k : Kappa),
    K [] tau A -> 
    K d tau A.
Proof.
  intros d tau k KDer.
  (* TODO   intros Kder. revert d. *)
(*  intros Kder.
  revert d.
  induction Kder.
  Focus 7.
  Check (K_ind 
           (fun (d : Delta) (t : Tau) (k : Kappa) =>
              K [] t A -> 
              K d t A)).
*)

  apply (K_ind 
           (fun (d : Delta) (t : Tau) (k : Kappa) =>
              K [] t A -> 
              K d t A))
  with (k := A).
Proof.
  Focus 10.
  Case "bad induction".
   admit.
Admitted.


Lemma K_nil_A_apply_with_der_in_context :
  forall (d : Delta) (tau : Tau) (k : Kappa),
    K [] tau A -> 
    K d tau A.
Proof.
  intros d tau k Kder.
  (* TODO   intros Kder. revert d. *)
(*  intros Kder.
  revert d.
  induction Kder.
  Focus 7.
  Check (K_ind 
           (fun (d : Delta) (t : Tau) (k : Kappa) =>
              K [] t A -> 
              K d t A)).
*)

  apply (K_ind 
           (fun (d : Delta) (t : Tau) (k : Kappa) =>
              K [] t A -> 
              K d t A))
  with (k := A).
Proof.
  Focus 10.
  Case "redo induction bad".
   admit.
Admitted.

Lemma K_nil_A_induction_with_der_in_context :
  forall (d : Delta) (tau : Tau) (k : Kappa),
    K [] tau A -> 
    K d tau A.
Proof.
  intros d tau k Kder.
  induction Kder.
Proof.
  Focus 9.
  Case "K [] tau d not in context".
   admit.
Admitted.

Lemma K_nil_A_induction_with_der__generalize_d_in_context :
  forall (d : Delta) (tau : Tau) (k : Kappa),
    K [] tau A -> 
    K d tau A.
Proof.
  intros d tau k Kder.
  revert d.
  induction Kder.
Proof.
  Focus 9.
  Case "K [] tau d not in context".
   admit.
Admitted.

Lemma K_nil_A_induction_with_der_generalize_dependent_d_in_context :
  forall (d : Delta) (tau : Tau) (k : Kappa),
    K [] tau A -> 
    K d tau A.
Proof.
  intros d tau k Kder.
  generalize dependent d.
  induction Kder.
Proof.
  Focus 9.
  Case "K [] tau d not in context".
   admit.
Admitted.

(* Fail
Lemma K_nil_A_induction_with_der_generalize_dependent_nil_in_context :
  forall (d : Delta) (tau : Tau) (k : Kappa),
    K [] tau A -> 
    K d tau A.
Proof.
  intros d tau k Kder.
  generalize dependent nil.
  induction Kder.
Proof.
  Focus 9.
  Case "K [] tau d not in context".
   admit.
Admitted.

*)

(* Fail
Lemma K_nil_A_induction_with_der_generalize_dependent_tau_in_context :
  forall (d : Delta) (tau : Tau) (k : Kappa),
    K [] tau A -> 
    K d tau A.
Proof.
  intros d tau k Kder.
  generalize dependent d.
  generalize dependent tau.
  induction Kder.
Proof.
  Focus 9.
  Case "K [] tau d not in context".
   admit.
Admitted.

*)

Lemma K_nil_7:
  forall (d : Delta) (tau : Tau) (k : Kappa),
    K [] tau A -> 
    K d tau A.
Proof.
  intros d tau k Kder.
  generalize dependent d.
  elim Kder.
  Focus 2.
  Case "d vs d0".
Admitted.

Lemma K_nil_8:
  forall (d : Delta) (tau : Tau) (k : Kappa),
    K [] tau A -> 
    K d tau A.
Proof.
  intros d tau k Kder.
  dependent induction Kder.
  Focus 2.
  Case "d vs d0".
Admitted.

Lemma K_nil_9:
  forall (d : Delta) (tau : Tau) (k : Kappa),
    K [] tau A -> 
    K d tau A.
Proof.
  intros d tau k Kder.
  apply (K_ind 
           (fun (d : Delta) (t : Tau) (k : Kappa) =>
              K [] t A -> 
              K d t A))
  with (k := A).
  Focus 9.
  Case "K [] in the context.".
   admit.
  Focus 10.
  Case "Totally unprovable goal.".
Admitted.

Lemma K_nil_10:
  forall (d : Delta) (tau : Tau) (k : Kappa),
    K [] tau A -> 
    K d tau A.
Proof.
  intros d tau k.
  apply (K_ind 
           (fun (d : Delta) (t : Tau) (k : Kappa) =>
              K [] t A -> 
              K d t A))
  with (k := A).
  Focus 8.
  Case "but not unprovable goals".
   admit.
  Focus 9.
  Case "K [] not in the context.".
   admit.
Admitted.

(* K [] in the context, all d's right, bad extra case. *)
Lemma K_nil_11:
  forall (d : Delta) (tau : Tau) (k : Kappa),
    K [] tau A -> 
    K d tau A.
Proof.
  intros d tau k Kder.
  apply (K_ind 
           (fun (d : Delta) (t : Tau) (k : Kappa) =>
              K d t A))
  with (k := A).
  Focus 8.
  Case "nil in the context.".
   admit.
  Focus 9.
  Case "K [] in the context but unprovable goal.".
   admit.
Admitted.


(* K [] in the context, all d's right, k [] assumption case, weird delta case, 
 d d0 not related *)
Lemma K_nil_12:
  forall (tau : Tau),
    K [] tau A -> 
    forall (d : Delta),
      K d tau A.
Proof.
  intros tau Kder.
  apply (K_ind 
           (fun (d : Delta) (t : Tau) (k : Kappa) =>
              forall (d : Delta),
                K d t A))
  with (d:= []) (k:= A).
  Focus 3.
   intros.  
Admitted.

(* K [] in the context, all d's right, k [] assumption case, weird delta case, 
 d d0 not related *)
Lemma K_nil_13:
  forall (tau : Tau) (d : Delta),
    K [] tau A -> 
      K d tau A.
Proof.
  intros tau d Kder.
  apply (K_ind 
           (fun (d : Delta) (t : Tau) (k : Kappa) =>
              forall (d : Delta),
                K d t A))
  with (d:= []) (k:= A).
  Focus 3.

Admitted.

(* Closer .*) 
Lemma K_nil_14:
  forall (tau : Tau),
    K [] tau A -> 
    forall (d : Delta),
      K d tau A.
Proof.
  intros tau d.
  apply (K_ind 
           (fun (d : Delta) (t : Tau) (k : Kappa) =>
              forall (d : Delta),
                K d t A))
        with (d:=[]) (k:= A).
  Focus 3.
Admitted.

Lemma K_nil_15:
  forall (tau : Tau) (d' : Delta),
      K [] tau A -> 
      K d' tau A.
Proof.
  intros tau d'.
  apply (K_ind 
           (fun (d : Delta) (t : Tau) (k : Kappa) =>
              K [] tau A -> 
              K d' t A))
       with (d:=[]) (k:= A).
  Focus 10.
Admitted.

Lemma K_nil_16:
  forall (tau : Tau) (d : Delta),
      K [] tau A -> 
      forall (d' : Delta),
        K d' tau A.
Proof.
  intros tau d.
  apply (K_ind 
           (fun (d : Delta) (t : Tau) (k : Kappa) =>
              K [] tau A -> 
              forall (d' : Delta),
                K d' t A))
  with (d:=[]) (k:= A).
 Focus 10.
Admitted.


Lemma K_nil_17:
  forall (d : Delta), 
   forall (tau : Tau),
          K [] tau A -> 
          K d tau A.
Proof.
  intros d tau Kder.
  induction Kder.
  Focus 3.
Admitted.

Lemma K_nil_18:
  forall (d : Delta), 
    d = [] ->
    forall (tau : Tau),
      K d tau A -> 
      forall (d' : Delta),
        K d' tau A.
Proof.
  intros d dnil tau Kder.
  induction Kder.
  Focus 9.
Admitted.


(* Closer but no cigar. *)
Lemma K_nil_19:
  forall (d : Delta) (tau : Tau),
      K d tau A -> 
      d = [] ->
      forall (d' : Delta),
        K d' tau A.
Proof.
  intros d tau Kder.
  induction Kder.
  Focus 8.
  Case  "K d (utype alpha k tau) A".
  (* No correct binding of d in preconditions. *)
   admit.
  Case  "K d (etype p alpha k tau) A)".
   admit.
Admitted.

Lemma K_nil_20:
  forall (d : Delta) (tau : Tau),
      K d tau A -> 
      d = [] ->
      forall (d' : Delta),
        K d' tau A.
Proof.
  intros d tau.
  apply (K_ind 
           (fun (d : Delta) (t : Tau) (k : Kappa) =>
              K d t A -> 
              d = [] ->
              forall (d' : Delta),
                K d' t A))
  with (k := A).

  Case  "K d (utype alpha k tau) A".
  (* No correct binding of d in preconditions. *)
   admit.
  Case  "K d (etype p alpha k tau) A)".
   admit.
Admitted.


Lemma K_nil_21:
  forall (d : Delta) (tau : Tau),
      K d tau A -> 
      forall (d' : Delta),
        K d' tau A.
Proof.
  intros d' tau Kder.
  induction Kder.
  admit. admit.
  admit. admit.
  admit. admit. 
  Case "OK".
Admitted.

Print Kappa_rect.

Fixpoint Kappa_rect_X (P : Kappa -> Type) (f : P B) (f0 : P A) (k : Kappa) :=
match k as k0 return (P k0) with
| B => f
| A => f0
end.

Print Kappa_rect.

(*
Kappa_rect = 
fun (P : Kappa -> Type) (f : P B) (f0 : P A) (k : Kappa) =>
match k as k0 return (P k0) with
| B => f
| A => f0
end
     : forall P : Kappa -> Type, P B -> P A -> forall k : Kappa, P k

Print Kappa_rect_X.
Kappa_rect_X = 
fix Kappa_rect_X (P : Kappa -> Type) (f : P B) (f0 : P A) 
                 (k : Kappa) {struct k} : P k :=
  match k as k0 return (P k0) with
  | B => f
  | A => f0
  end
     : forall P : Kappa -> Type, P B -> P A -> forall k : Kappa, P k
*)

Definition Kappa_rect := 
fun (P : Kappa -> Type) (f : P B) (f0 : P A) (k : Kappa) =>
match k as k0 return (P k0) with
| B => f
| A => f0
end.

Definition K_ind_X := fun (P : Delta -> Tau -> Kappa -> Prop) 
  (f : forall d : Delta, P d cint B)
  (f0 : forall (d : Delta) (alpha : TVar),
        getD d alpha = Some B -> P d (tv_t alpha) B)
  (f1 : forall (d : Delta) (alpha : TVar),
        getD d alpha = Some A -> P d (ptype (tv_t alpha)) B)
  (f2 : forall (d : Delta) (tau : Tau), K d tau B -> P d tau B -> P d tau A)
  (f3 : forall (d : Delta) (t0 t1 : Tau),
        K d t0 A -> P d t0 A -> K d t1 A -> P d t1 A -> P d (cross t0 t1) A)
  (f4 : forall (d : Delta) (t0 t1 : Tau),
        K d t0 A -> P d t0 A -> K d t1 A -> P d t1 A -> P d (arrow t0 t1) A)
  (f5 : forall (d : Delta) (tau : Tau),
        K d tau A -> P d tau A -> P d (ptype tau) B)
  (f6 : forall (d : Delta) (alpha : TVar) (k : Kappa) (tau : Tau),
        WFD ([(alpha, k)] ++ d) ->
        getD d alpha = None ->
        K ([(alpha, k)] ++ d) tau A ->
        P ([(alpha, k)] ++ d) tau A -> P d (utype alpha k tau) A)
  (f7 : forall (d : Delta) (alpha : TVar) (k : Kappa) (tau : Tau) (p : Phi),
        WFD ([(alpha, k)] ++ d) ->
        getD d alpha = None ->
        K ([(alpha, k)] ++ d) tau A ->
        P ([(alpha, k)] ++ d) tau A -> P d (etype p alpha k tau) A) =>
fix F (d : Delta) (t : Tau) (k : Kappa) (k0 : K d t k) {struct k0} :
  P d t k :=
  match k0 in (K d0 t0 k1) return (P d0 t0 k1) with
  | K_int d0 => f d0
  | K_B d0 alpha e => f0 d0 alpha e
  | K_star_A d0 alpha e => f1 d0 alpha e
  | K_B_A d0 tau k1 => f2 d0 tau k1 (F d0 tau B k1)
  | K_cross d0 t0 t1 k1 k2 => f3 d0 t0 t1 k1 (F d0 t0 A k1) k2 (F d0 t1 A k2)
  | K_arrow d0 t0 t1 k1 k2 => f4 d0 t0 t1 k1 (F d0 t0 A k1) k2 (F d0 t1 A k2)
  | K_ptype d0 tau k1 => f5 d0 tau k1 (F d0 tau A k1)
  | K_utype d0 alpha k1 tau w e k2 =>
      f6 d0 alpha k1 tau w e k2 (F ([(alpha, k1)] ++ d0) tau A k2)
  | K_etype d0 alpha k1 tau p w e k2 =>
      f7 d0 alpha k1 tau p w e k2 (F ([(alpha, k1)] ++ d0) tau A k2)
  end.

Check K_ind_X.

Lemma K_nil_22:
  forall (d : Delta) (tau : Tau),
      K [] tau A -> 
      K d tau A.
Proof.
  intros d tau.
  apply (K_ind_X
           (fun (d : Delta) (t : Tau) (k : Kappa) =>
              K [] t A -> 
                K d t A))
  with (d:= d) (k := A).
  Focus 10. (* Bad base case. *)
Admitted.

(* Trying refine to learn what I'm doing. *)
Lemma K_nil_24:
  forall (d : Delta) (t : Tau) (k : Kappa),
    K d t k ->
    K d t k.
Proof.
  refine (K_ind_X
           (fun (d : Delta) (t : Tau) (k : Kappa) =>
              K d t k)
           _ _ _ _ _ _ _ _ _ ).
  admit.
  admit.
  admit.
  admit.

Admitted.

(* Trying refine to learn what I'm doing. *)
Definition P1 := fun (d : Delta) (t : Tau) (k : Kappa) =>  K d t k -> K d t k.
Definition P0 := fun (d : Delta) (t : Tau) (k : Kappa) =>  K d t k.
Lemma K_nil_25:
  forall (d : Delta) (t : Tau) (k : Kappa),
    P1 d t k.
Proof.
  refine (K_ind_X 
            P0

           _ _ _ _ _ _ _ _ _ ).

  admit.
  admit.
  unfold P0.
  admit.
  admit.

Admitted.


Require Export Coq.Program.Equality.

(* But is it strong enough ? *)
Lemma K_nil_26:
  forall (d : Delta) (tau : Tau),
      d = [] ->
      K d tau A -> 
      forall (d' : Delta),
        K d' tau A.
Proof.
  intros d tau dnil Kder.
  dependent induction Kder.
  admit.
  admit.
  admit.

Admitted.

(* Stronger but is it neccesary ? *)
Lemma K_nil_27:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      d = [] ->
      K d tau k -> 
      forall (d' : Delta),
        K d' tau A.
Proof.
  intros d tau k dnil Kder.
  dependent induction Kder.
  admit.
  admit.
  admit.
  admit.
  admit.
  
Admitted.

Lemma K_nil_28:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      d = [] ->
      K d tau k -> 
      forall (d' : Delta),
        K d' tau k.
Proof.
  intros d tau k dnil Kder.
  dependent induction Kder.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.  
  intros.
  apply IHKder with (d':= d') in dnil.
  constructor.
  assumption.
Admitted.

Lemma K_weakening:
  forall (d : Delta) (tau : Tau) (k : Kappa),
     K d tau k ->
     forall (alpha : TVar),
       getD d alpha = None -> 
       K ([(alpha, k)] ++ d) tau k.
Proof.
  intros t dau k Kder.
  K_ind_cases(dependent induction Kder) Case.
  Case "K d cint B".
   intros.
   constructor.
  Case "K d (tv_t alpha) B".
   intros.
   (* This is going to work. *)
   admit.
  Case "K d (ptype (tv_t alpha)) B".
   intros.
   constructor.
   AdmitAlphaConversion.
  Case "K d tau A".
   admit.
  Case "K d (cross t0 t1) A".
   intros.
   (* gonna work. *)
   admit.
  Case "K d (arrow t0 t1) A".
   admit.
  Case "K d (ptype tau) B".
   admit.
  Case "K d (utype alpha k tau) A".
   intros.
   (* Might work. *)
   admit.
  Case "K d (etype p alpha k tau) A)".
   admit.
Qed.


(* Better but strongly broken. Needs a free variable.
   And the induction hypothesis breaks as it rewrites d. *)
Lemma K_nil_A:
  forall (d : Delta) (tau : Tau) (k : Kappa),
      d = [] -> 
      K d tau k -> 
      forall (d' : Delta),
        WFD d' -> 
        K d' tau k.
Proof.
  intros d tau k dnil Kder.
  K_ind_cases (dependent induction Kder) Case.
  Case  "K d cint B".
   intros.
   constructor.
   constructor.
  Case  "K d (tv_t alpha) B".
   intros.
   rewrite dnil in H.
   inversion H.
  Case  "K d (ptype (tv_t alpha)) B".
   intros.
   rewrite dnil in H.
   inversion H.
  Case  "K d tau A".
   intros.
   apply IHKder with (d':= d') in dnil; try assumption.
   constructor; try assumption.
  Case  "K d (cross t0 t1) A".
   intros.
   pose proof dnil as dnil2.
   apply IHKder1 with (d':= d') in dnil; try assumption.
   apply IHKder2 with (d':= d') in dnil2; try assumption.
   apply K_cross; try assumption.
  Case  "K d (arrow t0 t1) A".
   intros.
   pose proof dnil as dnil2.
   apply IHKder1 with (d':= d') in dnil; try assumption.
   apply IHKder2 with (d':= d') in dnil2; try assumption.
   apply K_arrow; try assumption.
  Case  "K d (ptype tau) B".
   intros.
   apply IHKder with (d':= d') in dnil; try assumption.
   apply K_ptype.
   assumption.
  Case  "K d (utype alpha k tau) A".
   intros.
   rewrite dnil in H.
   rewrite dnil in H0.
   rewrite dnil in Kder.
   apply K_utype.
   constructor.
   AdmitAlphaConversion.
   assumption.
   AdmitAlphaConversion.
   
   admit.
   (* No K rule would work here, need a lemma 
     K d' tau k, getD d' alpha = None -> K ([(alpha, k)] ++ d') tau k
*)
  Case  "K d (etype p alpha k tau) A)".
   admit.
Qed.  

Check K_nil_A.



(* I'm going to simplify K and try and fix the induction schema. *)

Inductive J : Delta -> Tau -> Kappa -> Prop :=

 | J_int   : forall (d : Delta),
                  J d cint B

(*
 | J_B     : forall (d : Delta) (alpha : TVar),
               getD d alpha = Some B ->
               J d (tv_t alpha) B

 | J_star_A  : forall (d : Delta) (alpha : TVar),
                 getD d alpha = Some A -> 
                 J  d (ptype (tv_t alpha)) B

 | J_B_A     : forall (d : Delta) (tau : Tau),
                  J  d tau B ->
                  J  d tau A
*)

 | J_cross   : forall (d : Delta) (t0 t1 : Tau),
                    J d t0 A ->
                    J d t1 A ->
                    J d (cross t0 t1) A

(*
 | J_arrow   : forall (d : Delta) (t0 t1 : Tau),
                    J d t0 A ->
                    J d t1 A ->
                    J d (arrow t0 t1) A

 | J_ptype    :  forall (d : Delta) (tau : Tau),
                    J d tau A ->
                    J d (ptype tau) B

 | J_utype  : forall (d : Delta) (alpha : TVar) (k : Jappa) (tau : Tau),
                   WFD ([(alpha, k)] ++ d) ->
                   getD d alpha = None -> 
                   J ([(alpha, k)] ++ d) tau A ->
                   J d (utype alpha k tau) A

 | J_etype  : forall (d : Delta) (alpha : TVar) (k : Jappa) (tau : Tau) (p : Phi),
                   WFD ([(alpha, k)] ++ d) ->
                   getD d alpha = None -> 
                   J ([(alpha, k)] ++ d) tau A ->
                   J d (etype p alpha k tau) A.
*)
.

Print J_ind.

(* Wait on this, try dependent induction. 
Definition J_ind_2 := 
fun 
  (P : Delta -> Tau -> Kappa -> Prop)
  (f : forall d : Delta, P d cint B)
  (f0 : forall (d : Delta) (t0 t1 : Tau),
        J [] t0 A -> P d t0 A -> 
        J [] t1 A -> P d t1 A -> 
        P d (cross t0 t1) A) =>
fix F (d : Delta) (t : Tau) (k : Kappa) (j : J [] t A) {struct j} : 
P d t k :=
  match j in (J d0 t0 k0) return (P d0 t0 k0) with
  | J_int d0 => f d0
  | J_cross d0 t0 t1 j0 j1 => f0 d0 t0 t1 j0 (F d0 t0 A j0) j1 (F d0 t1 A j1)
  end.

Check J_ind_2 : 
     forall P : Delta -> Tau -> Kappa -> Prop,
       (forall d : Delta, P d cint B) ->
       (forall (d : Delta) (t0 t1 : Tau),
        J d t0 A -> P d t0 A -> J d t1 A -> P d t1 A -> P d (cross t0 t1) A) ->
       forall (d : Delta) (t : Tau) (k : Kappa), J d t k -> P d t k.

*)


(* 
Definition J_ind_1 := 
fun (P : Delta -> Tau -> Kappa -> Prop) 
    (f : forall d : Delta, P d cint B)
    (d : Delta) 
    (t : Tau) 
    (k : Kappa) 
    (j : J d t k) =>
match j in (J d0 t0 k0) return (P d0 t0 k0) with
| J_int x => f x
end.

Check J_ind_1  : forall P : Delta -> Tau -> Kappa -> Prop,
       (forall d : Delta, P d cint B) ->
       forall (d : Delta) (t : Tau) (k : Kappa), J d t k -> P d t k.

*)

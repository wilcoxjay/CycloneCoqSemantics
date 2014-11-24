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

(* Bug, Miswrote theorem. I like the forall quantified version although
   I can naturally express this with exists.  *)
(* This is not the right induction just whacking a length on it. *)
(* I need to induct on path extension, perhaps reverse paths? *)

Functional Scheme rev_ind := Induction for rev Sort Prop.

Lemma A_11_Heap_Object_Safety_1:
  forall (v1 : E),
      forall (p : P) (v2 : E) (v3 : E),
        get v1 p v2 ->
        get v1 p v3 -> 
        v2 = v3. 
Proof.
  intros v1.
  induction v1;
   try (intros p v2 v3 getv1pv2 getv1pv3;
        inversion getv1pv2;
        inversion getv1pv3;
        try reflexivity;
        crush).
  (* 1,2 should invert on getv1pv* why didn't it? *)
  specialize (IHv1_1 p0 v3 v2).
  apply IHv1_1 in H14.
  crush.
  assumption.
  
  specialize (IHv1_2 p0 v3 v2).
  apply IHv1_2 in H14.
  crush.
  assumption.

  specialize (IHv1 p0 v2 v3).
  apply IHv1 in H6.
  crush.
  assumption.
Qed.

(*

  Case "i_e i = []".

   intros v2 v3 getv1pv2 getv1pv3.
   inversion getv1pv2.
   inversion getv1pv3.
   crush.
  Case "a :: p".
  intros v2 v3.
  intros getv1pxv2 getv1pxv3.
  induction getv1pxv2; inversion getv1pxv3; try reflexivity; crush.
  Focus 3.

(* Nope, still reversed. *)
  intros v1 p v2 v3.
  intros getv1pv2 getv1pv3.
  induction getv1pv2.
  Case "p = []".
   inversion getv1pv3.
   reflexivity.
  Case "(cpair v0 v1) zero_pe".

(* Error: Cannot move getv1pv2 after P: it depends on P. 
   is my bug. *)
(* jrw *)
  Case "p = []".
   intros getv1pv2.
   intros getv1pv3.
   inversion getv1pv2; inversion getv1pv3; crush.
  Case "p ++ [x]".
  (* Try induction on the derivation here to get reverse reasoning. *)
   intros getv1pxv2.
   intros getv1pxv3.
   destruct x; try destruct i.
   induction getv1pxv2.
   (* Perhaps I should flip the induction? *)
   
   (* break out the path addition. *)

   (* The right cases, but not clear on how to solve them yet. *)
   (* So i want to phrase get v1 (p ++ [i_pe zero_pe]) v2 
       in terms of get v1 p. *)
   (* I need the get v1 p v2 and it's missing from the context. *)
   (* I think I really need induction on the derivation of the get. *)
*)
Admitted.


Lemma A_11_Heap_Object_Safety_2:
  forall (v0 v1 v2 : E) (p1 p2 : P),
    get v0 p1 v1 ->
    get v0 (p1 ++ p2) v2 ->
    get v1 p2 v2.
Proof.
  intros v0 v1 v2 p1.
  functional induction (rev p1).
  Case "p = []".
   intros p2.
   intros getv0p1v1 getv0p1p2v2.
   inversion getv0p1v1; inversion getv0p1p2v2; crush.   
  Case "p = p1 ++ [x]".
  intros p2.
  intros g1 g2.
  destruct x; destruct v0.
  (* crush gets 0. *)
Admitted.

Lemma A_11_Heap_Object_Safety_3:
  forall (h : H) (u : Upsilon) (g : Gamma) 
         (x : EVar) (vhx v1 : E) (t1 t2: Tau) 
         (p1 p2 : P),
    refp h u ->
    htyp u g h g ->
    getH h x = Some vhx ->
    get vhx p1 v1 ->
    rtyp [] u g v1 t1 ->
    gettype u x p1 t1 p2 = Some t2 ->
    (exists (v2 : E),
       get vhx (p1 ++ p2) v2 /\ 
       rtyp [] u g v2 t2) /\
    (forall (v2' : E),
       Value v2' ->
       (exists (v1' : E),
          Value v1' ->
          set v1 p2 v2' v1')).
Proof.
  intros h u g x vhx v1 t1 t2 p1 p2.
  induction p2. (* TODO is functional induction rev better? *)
  (* crush adds 2 goals. *)
  Case "p2 = []".
  intros.
  Focus 2.
  destruct a.
  crush.
Admitted.


(* Just instantiating the above at H(x) = v and p1 = nil. *)
(* Dan, is U; \Gamma supposed to be \Upsilon ; \Gamma ? *)
Lemma A_11_Heap_Object_Safety_3_Corollary :
  forall (h : H) (u : Upsilon) (g : Gamma) 
         (x : EVar) (p2 : P) (t1 t2 : Tau)
         (v1 v2 vhx : E),
    refp h u ->
    htyp u g h g ->
    getH h x = Some v1 ->
    get vhx [] v1 ->
    rtyp [] u g v1 t1 ->
    gettype u x [] t1 p2 = Some t2 ->
    (exists (v2 : E),
       get vhx ([] ++ p2) v2 /\ 
       rtyp [] u g v2 t2) /\
    (forall (v2' : E),
       Value v2' ->
       (exists (v1' : E),
          Value v1' ->
          set v1 p2 v2' v1')).
Proof.
  (* Prove using A_11_Heap_Object_Safety_3 *)
Admitted.

Lemma A_11_Heap_Object_Safety_4: 
  forall (h : H) (u : Upsilon) (g : Gamma) 
         (x : EVar) (vhx v1 : E) (t1 t2: Tau) 
         (p1 p2 : P),
    refp h u ->
    htyp u g h g ->
    getH h x = Some vhx ->
    get vhx p1 v1 ->
    rtyp [] u g v1 t1 ->
    gettype u x p1 t1 p2 = Some t2 ->
    ASGN [] t2 ->
    (exists (v2 : E),
       get vhx (p1 ++ p2) v2 /\ 
       rtyp [] u g v2 t2) /\
    (forall (v2' : E),
       Value v2' ->
       (exists (v1' : E),
          Value v1' ->
          set v1 p2 v2' v1')).
Proof.
  (* By lemmas and case analysis on t2. *)

Admitted.

(* TODO write lemma 5
Lemma A_11_Heap_Object_Safety_5.
*)
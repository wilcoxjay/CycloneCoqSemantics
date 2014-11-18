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


(* TODO are the orderings of quantifiers correct? *)
Lemma A_11_Heap_Object_Safety_1:
  forall (v1 : E) (p : P) (n : nat),
    Value v1 ->
    n = length p ->
    exists ! (v2 : E),
      Value v2 ->
      get v1 p v2.
Proof.
  intros.
  induction n.
  (* crush gets 0. *)
Admitted.

Lemma A_11_Heap_Object_Safety_2:
  forall (v0 v1 v2 : E) (p1 p2 : P) (n : nat),
    Value v0 ->
    Value v1 ->
    Value v2 ->
    n = length p1 ->
    get v0 p1 v1 ->
    get v0 (p1 ++ p2) v2 ->
    get v1 p2 v2.
Proof.
  intros.
  induction n.
  (* crush gets 0. *)
Admitted.

Lemma A_11_Heap_Object_Safety_3:
  forall (h : H) (u : Upsilon) (g : Gamma) 
         (x : EVar) (p1 p2 : P) (t1 t2 : Tau)
         (v1 v2 vhx : E) (n : nat),
    Value v1 ->
    Value v2 ->
    refp h u ->
    htyp u g h g ->
    getH h x = Some vhx ->
    get vhx p1 v1 ->
    rtyp [] u g v1 t1 ->
    gettype u x p1 t1 p2 = Some t2 ->
    n = length p2 ->
    (exists (v2 : E),
       get vhx (p1 ++ p2) v2 /\ 
       rtyp [] u g v2 t2) /\
    (forall (v2' : E),
       Value v2' ->
       (exists (v1' : E),
          Value v1' ->
          set v1 p2 v2' v1')).
Proof.
  intros.
  induction n.
  (* crush adds 2 goals. *)
Admitted.


(* Just instantiating the above at H(x) = v and p1 = nil. *)
(* Dan, is U; \Gamma supposed to be \Upsilon ; \Gamma ? *)
Lemma A_11_Heap_Object_Safety_3_Corollary :
  forall (h : H) (u : Upsilon) (g : Gamma) 
         (x : EVar) (p2 : P) (t1 t2 : Tau)
         (v1 v2 vhx : E),
    Value v1 ->
    Value v2 ->
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

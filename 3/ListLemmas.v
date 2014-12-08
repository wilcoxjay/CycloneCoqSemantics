(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  List utility proofs. 

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.

Lemma Nil_Not_App_Anything:
  forall (A : Type) (g g' : list A),
    g' <> [] ->
    [] <> g ++ g'.
Proof.    
Admitted.

Lemma app_equals:
  forall (A: Type) (g g' : list A) (x y : A),
    g ++ [x] = g' ++ [y] ->
    g = g' /\ x = y.
Proof.
Admitted.

Lemma cons_is_append_singleton:
 forall (A : Type) (x : A) (l : list A),
   x :: l = [x] ++ l.
Proof.
Admitted.
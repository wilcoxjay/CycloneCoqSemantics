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

Lemma cons_is_append_singleton:
 forall (A : Type) (x : A) (l : list A),
   x :: l = [x] ++ l.
Proof.
  intros.
  reflexivity.
Qed.

Lemma append_nil_noop:
 forall (A : Type) (l : list A),
   [] ++ l = l.
Proof.
  intros.
  compute.
  reflexivity.
Qed.


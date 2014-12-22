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




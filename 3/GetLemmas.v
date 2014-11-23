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

Lemma getU_nil_none:
  forall  (x : EVar) (p : P),
    getU [] x p = None.
Proof.
  intros x p.
  compute.
  destruct x.
  reflexivity.
Qed.

Lemma getU_weakening :
  forall (u : Upsilon) (x x': EVar) (p p': P) (tau tau': Tau),
    getU (u ++ [(p_e x' p',tau')]) x p = Some tau ->
    x <> x' ->
    p <> p' ->
    getU u x p = Some tau.
Proof.
Admitted.  
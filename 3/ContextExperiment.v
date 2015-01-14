(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Why not build a context specific partial function with the
  lemmas I'd like once and for all.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.

Set Implicit Arguments.

Variable K : Type. (* Key *)
Variable V : Type. (* Value *)

Inductive Context (K : Type) (V : Type) : Type :=
  | Context_dot    : Context K V
  | Context_extend : K -> V -> Context K V -> Context K V.

Infix "+>" := Context_extend (at level 61, right associativity). 

Definition empty_context  := Context_dot.

Fixpoint Context_add (f : Context K V) (kv : K * V) : Context K V :=
match kv with 
 | (k,v) => 
    match f with
      | nil => kv :: nil
      | (k',v') :: f' =>
        match D_eq_dec d d' with
          | left _ => kv :: f'
          | right _ => (k',k') :: Context_add f' kv
        end
    end
end.

Arguments Context_add _ [dc].

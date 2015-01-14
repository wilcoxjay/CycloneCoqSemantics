(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  I'll need to build partial functions from list sets, I would say.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.
Require Import PFunExperiment.
Require Import Coq.Lists.ListSet.
Require Import Coq.Arith.Peano_dec.

Search set.

Set Implicit Arguments.

Check empty_pfun.
Check empty_set.

Example eq_empty_pfun:
  empty_pfun = empty_pfun.
Proof.
  reflexivity.
Qed.

Example eq_empty_set:
  empty_set = empty_set.
Proof.
  reflexivity.
Qed.

Check pfun_add.
Check set_add.

(* jrw how do I % this? *)
Definition empty_nat_set : set nat := [].
Check eq_nat_dec.
Check set_add eq_nat_dec 0 empty_nat_set.
Check list_eq_dec.

Check pfun_eq_dec.
Check pfun nat nat.
Check pfun_eq_dec eq_nat_dec eq_nat_dec.

Definition empty_set_nat_nat : set (nat  * nat) := [].
Definition empty_pfun_nat_nat : pfun nat nat := [].

Check pfun_add.
Check (pfun_eq_dec eq_nat_dec eq_nat_dec).
Check pfun_add eq_nat_dec.
Check pfun_add eq_nat_dec (0,0) empty_pfun_nat_nat.

Definition pfun_nat_nat_add (x : nat) (v : nat) (f : pfun nat nat) := 
  pfun_add eq_nat_dec (x,v) f.

Definition pfun_nat_nat_get (x : nat) (f : pfun nat nat) := 
  pfun_get eq_nat_dec f x.

Unset Implicit Arguments.
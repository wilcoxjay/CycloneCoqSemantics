(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Standard proof of NoDup on all operations.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.

Require Export CpdtTactics.
Require Export Case.
Require Export TacticNotations.

Set Implicit Arguments.

Definition K    := nat.
Definition K_eq := beq_nat.
Definition T    := nat.
Definition T_eq := beq_nat.

Inductive Context (K : Type) (T : Type) : Type :=
| Ctxt_dot  : Context K T
| Ctxt      : K -> T -> Context K T -> Context K T.

Inductive In (k : K) : Context K T ->  Prop := 
| In_hd : forall k' t' c, K_eq k k' = true -> In k (Ctxt k' t' c)
| In_tl : forall k' t' c, In k c -> In k (Ctxt k' t' c).
Hint Constructors In.

Inductive  NoDup : Context K T -> Prop :=
| NoDup_dot  : NoDup (Ctxt_dot K T)
| NoDup_ctxt : forall k t c,
                 NoDup c ->
                 ~In k c ->
                 NoDup (Ctxt k t c).
Hint Constructors NoDup.

Definition empty  := Ctxt_dot K T.

Fixpoint add (f : Context K T) (k: K) (t : T)  : Context K T :=
  match f with
    | Ctxt_dot => (Ctxt k t (Ctxt_dot K T))
    | (Ctxt k' t' f') =>
      match K_eq k k' with
        | true  => (Ctxt k  t  f')
        | false => (Ctxt k' t' (add f' k t))
      end
  end.

Fixpoint map (f : Context K T) (k: K) : option T :=
  match f with
    | Ctxt_dot => None
    | (Ctxt k' t' f') =>
      match K_eq k k' with
        | true  => Some t'
        | false => (map f' k)
      end
  end.

Fixpoint ink (f : Context K T) (k: K) : bool :=
  match f with
    | Ctxt_dot => false
    | (Ctxt k' t' f') =>
      match K_eq k k' with
        | true  => true
        | false => (ink f' k)
      end
  end.

Fixpoint inkt (f : Context K T) (k: K) (t : T) : bool :=
  match f with
    | Ctxt_dot => false
    | (Ctxt k' t' f') =>
      match K_eq k k' with
        | true => match T_eq t t' with | true => true | false => (inkt f' k t) end
        | false => (inkt f' k t)
      end
  end.

Fixpoint lt (f f' : Context K T) : bool :=
  match f with
    | Ctxt_dot => true
    | (Ctxt k' t' f'') =>
      match inkt f' k' t' with
        | true => (lt f'' f')
        | false => false
      end
  end.

Fixpoint equal (f f' : Context K T) : bool :=
  andb (lt f f') (lt f' f).

Fixpoint extends (c c' : Context K T) : bool :=
  match c with 
    | Ctxt_dot => true
    | Ctxt k t c'' =>
      if inkt c' k t
      then extends c'' c' 
      else false
  end.

Theorem empty_NoDup:
  NoDup empty.
Proof.
  crush.
Qed.

Theorem add_NoDup:
  forall c,
    NoDup c ->
    forall k t, 
    NoDup (add c k t).
Proof.
  intros c NoDupder k t.
  induction c.
  Case "Ctxt_dot".
   simpl.
   constructor; try assumption.
   unfold not.
   intros.
   inversion H.
  Case "Ctxt".
   unfold add.
   fold add.
   case_eq (K_eq k k0).
   SCase "K_eq k k0 = false".
    intros.
    inversion NoDupder.
    pose proof H2 as H2'.
    apply IHc in H2.
    constructor; try assumption.
    admit. (* Need var lemmas here for beq_nat in this case, then it solves. *)
   SCase "K_eq k k0 = true".
    intros.
    inversion NoDupder.
    apply IHc in H2.
    constructor; try assumption.
    inversion H2.
    unfold not.
    intros.
    inversion H5.
Admitted.

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
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Equality.

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
Require Export SubstitutionsProof.

(* TODO Is it a thesis bug that I have to have a kinding for the open case? *)
(* TODO Do I have to split this on concrete versus abstract types? *)
Fixpoint concreteTau (tau : Tau) : Prop := 
  match tau with
    | cint => True
    | cross x y     => concreteTau x /\ concreteTau y
    | arrow x y     => concreteTau x /\ concreteTau y
    | ptype x       => concreteTau x
    | utype _ _ x   => concreteTau x
    | etype _ _ _ x => concreteTau x
    | _ => False
end.

Print Tau_ind.
Print ex_intro.

Lemma All_Types_Have_A_Kinding:
    forall (tau : Tau), 
      exists (d : Delta) (k : Kappa),
        AK d tau k.
Proof.
  (* Induction on the type is not giving me a strong enough hypothesis
     when I have a concrete predicate. *)
  intros tau.
  induction tau.
  Focus 2.
  Case "cint".
   exists nil.
   exists A.
   constructor.
   constructor.
   constructor.
  Focus 2.
  Case "cross".
    exists nil.
    exists A.
    constructor.

(*
    elim IHtau1.
    intros [].
    intros IHtau1'.
    elim IHtau1'.
    intros A.
    intros IHtau1''.

    elim IHtau2.
    intros [].
    intros IHtau2'.
    elim IHtau2'.
    intros A'.
    intros IHtau2''.

    inversion IHtau1''.
    inversion IHtau2''.
    crush.
    apply K_cross.



   inversion IHtau1 with (d:=[]).
   inversion H5.
   crush.
   apply K_cross.
   assumption.
   assumption.
  SCase "(cross _ (tv_t _))".
   crush.
  SCase "(cross (tv_t _) _)".
   crush.
*)

(*
  SCase "arrow".
   crush.
   right.
   constructor.
   constructor.
   
   left.
   constructor.
   inversion H4.
   inversion H5.
   crush.
   apply K_arrow.
   assumption.
   assumption.
  SCase "arrow _ tv_t _".
  crush.
  SCase "arrow  tv_t _ _".
  crush.
  Case "ptype".
  crush.
  constructor.
  inversion H.
  crush.
  apply K_ptype.
*)
Admitted.

Lemma All_Types_Have_A_Kinding :
  forall (tau : Tau), 
    exists (d: Delta) (k : Kappa),
      AK d tau k.
Proof.
(*
  intros tau.
  induction tau.
  Case "tv_ t t".
  Focus 3.
  Case "cross".
  exists [].
  assert (I: AK [] tau1 B).
  assert (I: AK [] tau2 B).
  constructor.
  constructor.
  (* Thesis bug? Is this a bug in the thesis? *)

  apply AK_K_AK in H.
  apply K_cross.

  
  assumption.

  Case "cint".
   exists [].
   exists A.
   constructor.
   constructor.
   constructor.
*)  
Admitted.

Lemma A_8_Return_Preservation:
  forall (s : St),
    ret s ->
    forall (h h' : H) (s' : St),
      S h s h' s' ->
      ret s'.
Proof.
  intros s retder.
  induction retder.
  (* Cases are all messed up due to quantifier changes! *)
  Case "retn e".
   intros h h' s' H.
   inversion H.
   constructor.
  Case "if".
   intros h h' s' H.
   inversion H.
   SCase "if 0".
    rewrite <- H5.
    assumption.
   SCase "if <> 0".
    rewrite <- H5.
    assumption.
   SCase "if e->e'".
    constructor.
    SSCase "ret s1".
    assumption.
    SSCase "ret s2".
    assumption.
  Case "seq s1 s2".
   intros h h' s'0 H.
   inversion H.
   SCase "seq (e_s v) s'".
   subst.
   inversion retder. (* e_s v does not return. *)
   SCase "ret (retn v)".
   constructor.
   subst.
   SCase "(seq s1 s2) (seq s1' s2)".
   constructor.
   specialize (IHretder h h' s'1).
   apply IHretder in H5.
   assumption.
   SCase "ret (seq s'1 s)".
   intros h h' s'0 H.
   inversion H.
   crush.
   constructor.
   crush.
   (* Oh this is the we don't care that s1 does not have a return, s does case.*)
   apply ret_seq_2 with (s:= s'1) (s':= s') in retder. 
   assumption.
  Case "let".
   intros h h' s' H.
   inversion H.
   SCase "let s->s'".
   rewrite H5 in retder.
   assumption.
   SCase "let e->e'".
   constructor.
   exact retder.
   Case "open".
   intros h h' s' H.
   inversion H.
   constructor.
   crush.
   (* I need a substitution lemma and its there but it needs a kinding. *)
   elim All_Types_Have_A_Kinding with (tau:= tau).
   intros d.
   intros K.
   elim K.
   intros k9.
   intros.
   eapply A_6_Substitution_6 with (tau:=tau) (d:=d) (k:=k9).
   assumption.
   assumption.
   SCase "ret (open e' alpha x s)".
   crush.
   constructor.
   assumption.

   Case "openstar".
   intros h h' s' H.
   inversion H.
   constructor.
   crush.
   (* I need a substitution lemma and its there but it needs a kinding. *)
   elim All_Types_Have_A_Kinding with (tau:= tau).
   intros d.
   intros K.
   elim K.
   intros k9.
   intros.
   eapply A_6_Substitution_6 with (tau:=tau) (d:=d) (k:=k9).
   assumption.
   assumption.
   SCase "ret (open e' alpha x s)".
   crush.
   constructor.
   assumption.
Qed.


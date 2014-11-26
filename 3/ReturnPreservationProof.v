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

Check AK_AK_K.
Check K_B.
Check getD [((tvar 0),B)] (tvar 0) = Some B.
Check eq.

Lemma eq7:
  forall (n : nat),
    n = n.
Proof.
  intros n.
  reflexivity.
Qed.

Print eq7.

Inductive getD' : Delta-> TVar -> Kappa -> Prop :=
  | getD_top  : forall (d : Delta) (alpha : TVar) (k : Kappa),
                 getD' (cons (alpha,k) d) alpha k
  | getD_next : forall (d : Delta) (alpha beta : TVar) (k k': Kappa),
                 alpha <> beta ->
                 getD' d alpha k ->
                 getD' (cons (beta,k') d) alpha k.


Lemma fred:
  forall (alpha : TVar),
    getD' [(alpha,B)] alpha B.
Proof.
  intros alpha.
  constructor.
Qed.

Set Printing All.
Print fred.

Check fred.

(*
Check 
fun alpha : TVar => 
  getD_top (@nil (prod TVar Kappa)) alpha B : forall alpha : TVar,
       getD'
         (@cons (prod TVar Kappa) (@pair TVar Kappa alpha B)
            (@nil (prod TVar Kappa))) alpha B.

Definition fredie (alpha : TVar) :=
  forall alpha: TVar, 
    @eq_refl (option Kappa) (@Some Kappa B)
    : @eq (option Kappa)
          (getD
             (@cons (prod TVar Kappa) (@pair TVar Kappa alpha B)
                    (@nil (prod TVar Kappa))) (tvar O)) 
          (@Some Kappa B).
Check fredie.
*)

(* TODO Will I need to recurse with delta.
   What happens if I get back a B in some cases that I want an A?
   Can I just build the context once with a B for all free type variables? 
  *)

Fixpoint KTau (d : Delta) (tau : Tau) : option (K d tau A).
  refine match tau with
    | cint              => Some (K_B_A d cint (K_int d))
    | cross t0 t1       =>
      match (KTau d t0), (KTau d t1) with
        | Some p0, Some p1 => Some (K_cross d t0 t1 p0 p1)
        | _, _ => None
      end
    | arrow t0 t1       =>
      match (KTau d t0), (KTau d t1) with
        | Some p0, Some p1 => Some (K_arrow d t0 t1 p0 p1)
        | _, _ => None
      end
    | ptype t0          => 
      match (KTau d t0) with
        | Some p0 => Some (K_B_A d (ptype t0) (K_ptype d t0 p0))
        | _       => None
      end
    (* Some (K_B d alpha (eq (getD d alpha) (Some B))) *)
    | tv_t alpha          => _

    (* Shit I'm not going to be able to prove getD d alpha = None. *)
    | utype alpha k tau   => 
      match (KTau (d ++ [(alpha,k)]) tau) with
        (* | Some p0 => Some (K_utype d alpha k tau p0) *)
       | _ => None
      end
    | etype phi alpha k tau  => 
      match (KTau (d ++ [(alpha,k)]) tau) with
        (* | Some p0 => Some (K_etype d alpha k tau phi p0)  *)
       | _ => None
      end
  end.
  apply Some.
  apply K_B_A.
  
  apply K_B.
  Unset Printing All.
  
Lemma KTau_lemma : 
  forall d tau,
    (* TODO: "d covers free variables in tau (and they're boxed)" -> *)
    K d tau A.
Proof.
  induction tau.

Fixpoint AKTau (tau : Tau) (d : Delta) : option (AK d tau _) := 
  match tau with
      | cint              => Some (AK_AK_K d cint A (K_B_A d cint (K_int d)))
      | cross t0 t1       => 
        match (KTau d (cross t0 t1)) with 
          | Some p0 => Some (AK_AK_K d (cross t0 t1) A p0)
          | _ => None
        end
      | arrow t0 t1       => 
        match (KTau d (arrow t0 t1)) with
            | Some p0 => Some (AK_AK_K d (arrow t0 t1) A p0)
            | _ => None
        end
      | ptype t0          => 
        match (KTau d (ptype t0)) with
          | Some p0 => Some (AK_AK_K d (ptype t0) A p0)
          | _ => None
        end
      | tv_t alpha => None
      (* Some (AK_AK_K (d ++ [(alpha,B)]) (tv_t alpha) B (K_B (d ++ [(alpha,B)]) alpha)) *)
      | _ => None
  end.

Fixpoint BoxEm (taus : list TVar) : Delta :=
  match taus with 
    | [] => nil
    | alpha :: taus' => (alpha,B) :: BoxEm taus'
  end.

Fixpoint AKTau' (tau : Tau) : option (AK _ tau _) := 
  AKTau tau (BoxEm (FreeVariablesTau tau)).

(* This is too hard to prove due to the existentials. 
   I need a function to produce the right AK'ing. *)
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
(*


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


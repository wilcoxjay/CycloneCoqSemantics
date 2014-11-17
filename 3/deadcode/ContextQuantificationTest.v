(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  How do I quantify a property over a context ? 

*)
 
Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Export FormalSyntax.

(* Just for test experiments. *)

Definition QE : Type := prod TVar Kappa.
Definition Quelta  := list QE.

Fixpoint getQ (q : Quelta) (a : TVar) : option Kappa :=
  match a, q with 
    | tvar a', (tvar b', k) :: q' =>
      if beq_nat a' b' 
      then Some k 
      else getQ q' a
    | _ , nil => None
  end.

Inductive InQuelta : TVar -> Kappa -> Quelta -> Prop :=
  | InQuelta_top : forall (a : TVar) (k : Kappa) (q': Quelta),
                     InQuelta a k ([(a,k)] ++ q')
  | InQuelta_next : forall (a beta : TVar) (k k': Kappa) (q': Quelta),
                     beta <> a \/  k <> k' ->
                     InQuelta a k q' ->
                     InQuelta a k ([(beta,k')] ++ q').

Inductive CoolQE : TVar -> Kappa -> Prop :=
  | its_all_cool: forall (a : TVar) (k : Kappa), CoolQE a k.

Inductive WFQ : Quelta -> Prop :=
  | WFQ_Iterate : forall (q : Quelta),
                    (forall (a : TVar) (k : Kappa),
                       InQuelta a k q ->
                       CoolQE a k) ->
                  WFQ q.

Require Export TestUtilities.

Hint Constructors WFQ.
Hint Constructors CoolQE.
Hint Constructors InQuelta.
Hint Extern 2 (InQuelta _ _ [?x])      => 
try rewrite <- app_nil_r with (l:=[x]).

Lemma app_first_element :
  forall (A : Type) (l l': list A) (x : A),
    l' <> nil -> 
    l = x :: l' ->
    l = [x] ++ l'.
Proof.
Admitted.

Hint Extern 2 (InQuelta _ _ ?x)      => 
try rewrite <- app_nil_r with (l:=[x]).

Hint Extern 2 (InQuelta _ _ ?x)      => 
try rewrite app_first_element with (l:=[x]).

Theorem InQuelta_nil :
  ~(exists (alpha : TVar) (k : Kappa), InQuelta alpha k nil).
Proof.
  compute.
  intros H.
  inversion H.
  inversion H0.
  inversion H1.
Qed.

Theorem InQuelta_1 :
  InQuelta alpha k [(alpha,k)].
Proof.
  (* debug eauto 10. works. *)
  apply InQuelta_top.
Qed.

Theorem InQuelta_2_1 :
  InQuelta alpha B [(alpha,B); (beta,A) ].
Proof.
  rewrite app_first_element 
  with (l:= [(alpha,B); (beta,A)])
       (l':= [(beta,A)])
       (x:= (alpha,B)).
  apply InQuelta_top.
  discriminate.
  reflexivity.
Qed.

Theorem InQuelta_2_2 :
  InQuelta beta A [(alpha,B); (beta,A)].
Proof.
  apply InQuelta_next.
  left.
  discriminate.
  apply InQuelta_top.
Qed.

Theorem NotInQuelta_2_2 :
  ~ InQuelta beta B [(alpha,B); (beta,A)].
Proof.
  compute.
  intros.
  inversion H.
  assert (H7: tvar 0 <> tvar 1 \/ B <> B).
  left.
  discriminate.
  inversion H6.
  eauto.
Admitted.

Theorem wfc_nil :
 WFQ nil.
Proof.
  (* eauto 10.  Works. *)
  apply WFQ_Iterate.
  intros a k.
  intros I.
  inversion I.
Qed.

Theorem wfc_1:
  WFQ [(alpha,B)].
Proof.
  (* eauto 10. works *)
  apply WFQ_Iterate.
  intros a k.
  intros I.
  (* Inversion is just wrong, it's stopping at the first possible goal. *)

  apply its_all_cool. (* TODO why is this two goals ? *)
  apply its_all_cool. 
Qed.

Theorem wfc_2:
  WFQ [(alpha,B) ; (beta, A)].
Proof.
  (* eauto 10. Works. *)
  apply WFQ_Iterate.
  intros a k I.
  inversion I.  
  inversion I.
  simpl in *.
  apply its_all_cool. (* TODO why is this two goals ? *)  
  simpl in *.
  apply its_all_cool. 
(* This is just wrong, not getting all the subgoals. *)
Qed.

Theorem wfc_3:
  WFQ [(alpha,B) ; (beta, A) ; (gamma, B)].
Proof.
  (* eauto 10. Works. *)
  apply WFQ_Iterate.
  intros a k.
  intros I.
  inversion I.  
  apply its_all_cool. (* TODO why is this two goals ? *)  
  apply its_all_cool. 
Qed.
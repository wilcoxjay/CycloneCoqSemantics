(* Unused. *)
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


(* Not used yet. *)
Lemma getD_Some_None_Implies_Different_Variables:
  forall (alpha : TVar) (d : Delta) (n : nat) (k : Kappa),
      getD d (tvar n ) = Some k ->
      forall (n' : nat),
        getD d (tvar n') = None ->
        beq_nat n' n = false.
Proof.
  intros alpha d n k getDder.
  induction (cons (alpha,k) d); crush.
  (* TODO It's true but how to show it? *)
Admitted.


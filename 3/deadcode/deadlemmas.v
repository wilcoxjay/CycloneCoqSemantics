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

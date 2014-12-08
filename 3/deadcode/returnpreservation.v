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


Inductive getD' : Delta-> TVar -> Kappa -> Prop :=
  | getD_top  : forall (d : Delta) (alpha : TVar) (k : Kappa),
                 getD' (cons (alpha,k) d) alpha k
  | getD_next : forall (d : Delta) (alpha beta : TVar) (k k': Kappa),
                 alpha <> beta ->
                 getD' d alpha k ->
                 getD' (cons (beta,k') d) alpha k.


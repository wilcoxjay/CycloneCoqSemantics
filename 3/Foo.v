Parameter A : Prop.
Parameter P : A -> Prop.
Axiom T : exists x:A, P x.
Parameter G : Prop.
Axiom U : forall x:A, P x -> G.
Goal G.
Proof.
(* TODO James's version. 
destruct T.
apply U with (x:=x). auto.
*)
(* TODO wtf is elim ? *)
elim T.
intro o.
apply U.
Qed.
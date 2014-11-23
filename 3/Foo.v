Parameter A : Prop.
Parameter P : A -> Prop.
Axiom T : exists x:A, P x.
Parameter G : Prop.
Axiom U : forall x:A, P x -> G.
Goal G.
Proof.
elim T.
intro o.
apply U.
Qed.
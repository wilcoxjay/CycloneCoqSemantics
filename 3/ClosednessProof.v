(* Not proven, not used. *)

(* jrw why is this overly generalizing d? *)
Lemma k_nil_implies_tau_closed:
  forall (d : Delta) (tau : Tau) (k : Kappa),
    K [] tau k ->
    FreeVariablesTau tau = [].
Proof.
  intros d tau k Kder.
  Tau_ind_cases (induction tau) Case.
  Case "(tv_t t)".
   inversion Kder.
   crush.
   inversion H.
   inversion H5.
  Case "cint".
    reflexivity.
  Case "(cross t t0)".
   admit.
  Case "(arrow t t0)".
   admit.
  Case "(ptype t)".
   admit.
  Case "(utype t k t0)".
    unfold FreeVariablesTau.
    fold FreeVariablesTau.
    inversion Kder.
    crush.
    inversion H.
    crush.
    admit.
   Case "(etype p t k t0)".
   admit.
Qed.

(*  induction kder fails, try by type.
  intros d tau k dnil kder.
  K_ind_cases (induction kder) Case.
  Case "K d cint B".
   intros.
   reflexivity.
  Case "K d (tv_t alpha) B".
   rewrite dnil in H.
   inversion H.
  Case "K d (ptype (tv_t alpha)) B".
   rewrite dnil in H.
   inversion H.
   apply IHkder in dnil.
   assumption.
  Case "K d (cross t0 t1) A".
   unfold FreeVariablesTau.
   fold FreeVariablesTau.
   assert (dnil': d = []).
   assumption.
   apply IHkder1 in dnil.
   rewrite dnil.
   apply IHkder2 in dnil'.
   rewrite dnil'.
   reflexivity.
  Case "K d (arrow t0 t1) A".
   unfold FreeVariablesTau.
   fold FreeVariablesTau.
   assert (dnil': d = []).
   assumption.
   apply IHkder1 in dnil.
   rewrite dnil.
   apply IHkder2 in dnil'.
   rewrite dnil'.
   reflexivity.
  Case "K d (ptype tau) B".
   unfold FreeVariablesTau.
   fold FreeVariablesTau.
   apply IHkder in dnil.
   assumption.
  Case "K d (utype alpha k tau) A".
  (* Again the induction hypothesis is false. *)
   unfold FreeVariablesTau.
   fold FreeVariablesTau.
   (* Could be that I'm not strong enough as I removeTVar in the subcase. *)
   rewrite dnil in *.
   rewrite app_nil_r in *.
   admit.
  Case "K d (etype p alpha k tau) A)".
   admit.
*)

Lemma subst_Tau_in_closed_term:
  forall (tau : Tau),
    FreeVariablesTau tau = [] ->
    forall (tau' : Tau) (alpha : TVar),
      subst_Tau tau tau' alpha = tau.
Proof.
  intros tau tauclosed.
  Tau_ind_cases (induction tau) Case.
  Case "(tv_t t)".
   intros.
   inversion tauclosed.
  Case "cint".
   admit.
  Case "(cross t t0)".
   admit.
  Case "(arrow t t0)".
   admit.
  Case "(ptype t)".
   admit.
  Case "(utype t k t0)".
   intros.
   unfold subst_Tau.
   fold subst_Tau.
   unfold FreeVariablesTau in tauclosed.
   fold FreeVariablesTau in tauclosed.
   admit.
  Case "(etype p t k t0)".
   admit.
Qed.
  

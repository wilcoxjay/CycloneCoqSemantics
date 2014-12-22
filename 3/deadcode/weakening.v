Lemma WFU_dont_extend_with_a_used_variable:
  forall (u : Upsilon),
      WFU u ->
      forall (x : EVar) (p : P) (tau: Tau),
        getU u x p tau -> 
         forall (tau' : Tau),
           ~WFU((x, p, tau') :: u).
Proof.
  (* Two choices, induction on WFU or getU. *)
  intros u WFUder.
  apply (WFU_ind 
          (fun (u : Upsilon) =>
             forall (x : EVar) (p : P) (tau: Tau),
               getU u x p tau -> 
               forall (tau' : Tau),
                 ~WFU((x, p, tau') :: u))).
  Case "WFU []".
   intros.    
   inversion H.
  Case "WFU ([(x, p, tau)] ++ u)".   
   intros.       
   case_eq(beq_evar x x0); case_eq(beq_path p p0); intros.
   SCase "x = x0, p = p0".
    pose proof H4.
    pose proof H5.
    apply beq_path_eq in H4.
    apply beq_evar_eq in H5.
    rewrite H4 in H3.
    rewrite H5 in H3.
    inversion H3.
    SSCase "get_top".
      crush. (* Nice gives me False so I have to invert it away. *)
      admit. (* TODO *)
    SSCase "get_next".
      crush.
   SCase "x = x0, p <> p0".
    pose proof H4.
    pose proof H5.
    apply beq_path_neq in H4.
    apply beq_evar_eq in H5.
    rewrite H5 in H3.
    inversion H3.
    SSCase "get_top".
     crush.
    SSCase "get_next".
     admit.
   SCase "x <> x0, p = p0".
    admit.
   SCase "x <> x0, p <> p0".
    admit.
  Case "base".
   assumption.
Qed.


Lemma K_nil_A:
  forall (d : Delta) (tau : Tau),
      K [] tau A -> 
        K d tau A.
Proof.
  intros d tau.
  apply (K_ind 
           (fun (d : Delta) (t : Tau) (k : Kappa) =>
              K [] t A -> 
                K d t A))
  with (k := A) (d:= d).

  Case  "K d cint B".
   intros.
   constructor.
   constructor.
  Case  "K d (tv_t alpha) B".
   intros.
   inversion H0. 
   inversion H1.
   inversion H6.
  Case  "K d (ptype (tv_t alpha)) B".
   intros.
   inversion H0.
   inversion H1.
   inversion H6.

   inversion H6.
   inversion H7.
   inversion H12.
  Case  "K d tau A".
   intros.
   apply H0 in H1.
   assumption.
  Case  "K d (cross t0 t1) A".
   intros.
   inversion H3.
   inversion H4.
   apply H0 in H7.
   apply H2 in H8.
   apply K_cross; try assumption.
  Case  "K d (arrow t0 t1) A".
   intros.
   inversion H3.
   inversion H4.
   apply H0 in H7.
   apply H2 in H8.
   apply K_arrow; try assumption.
   (* Zig Zag, old overholt and carpano antiqua rye manhattan. *)
  Case  "K d (ptype tau) B".
   intros.
   inversion H1.
   inversion H2.
   inversion H7.

   apply H0 in H7.
   constructor.
   apply K_ptype.
   assumption.
  Case  "K d (utype alpha k tau) A".
   intros.
   apply K_utype; try assumption.
  Case  "K d (etype p alpha k tau) A)".
   intros.
   apply K_etype; try assumption.
  Case "base".
   admit. (* WTF is this case, K d tau A with no assumptions? *)
Qed.  




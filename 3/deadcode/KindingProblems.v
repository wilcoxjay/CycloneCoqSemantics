(* TODO Will I need to recurse with delta.
   What happens if I get back a B in some cases that I want an A?
   Can I just build the context once with a B for all free type variables? 
  *)

(* 
Fixpoint KTau (d : Delta) (tau : Tau) : option (K d tau A) := 
  match tau with
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
*)


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


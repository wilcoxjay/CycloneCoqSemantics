
Lemma getD_weakening_None: 
  forall (d d': Delta) (alpha : TVar) (k : Kappa),
   WFD d ->
   getD d alpha = None ->
   WFD (d ++ d') /\ getD d' alpha = None -> 
   WFD ([(alpha, k)] ++ d) /\ 
   WFD (([(alpha, k)] ++ d) ++ d') /\ 
   getD (d ++ d') alpha = None /\
   getD (([(alpha, k)] ++ d) ++ d') alpha = Some k. 
Proof.
Admitted.

Lemma getD_weakening_some: 
  forall (d : Delta) (alpha : TVar) (k : Kappa),
    WFD d ->
    getD d         alpha   = Some k ->
    forall (d' : Delta),
      WFD (d ++ d') -> 
      getD d' alpha = None /\ 
      getD (d ++ d') alpha   = Some k.
Proof.
Admitted.  

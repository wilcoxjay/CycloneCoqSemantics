Definition UE'        := prod (prod EVar P) Tau.      
Definition Upsilon'   := list UE'.

(* Coq Bug : Wow this must be a coq bug in the inversion generation.
  The only difference with getD above is Upsilon have a pair of a pair and tau. *)
Function getUwe (u : Upsilon') (x : EVar) : option Tau :=
  match x, u with 
    | evar x', ((evar y', _),t) :: u' =>
      if beq_nat x' y' 
      then Some t
      else getUwe u' x
    | _ , [] => None
  end.

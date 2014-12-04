Function getU (u : Upsilon) (x: EVar) (p : P) : option Tau :=
  match x, u with 
    | (evar x'), (((evar y'), p'), v) :: u'  =>
      if andb (beq_nat x' y') (path_eq p p')
      then Some v
      else getU u' x p
    | _,  _ => None 
  end.
(* jrw why can't coqie invert? *)


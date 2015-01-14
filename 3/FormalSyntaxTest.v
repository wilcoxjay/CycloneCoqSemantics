(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This tests the formal syntax, pg. 57. 

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Import FormalSyntax.
Require Import TestUtilities.


Check A : Kappa.
Check B : Kappa.

Check (tvar 0) : TVar.

Check witnesschanges : Phi.
Check aliases         : Phi.

Check (tv_t (tvar 0)) : Tau.
Check cint : Tau.
Check cross cint cint : Tau.
Check arrow cint cint : Tau.
Check ptype cint : Tau.
Check utype (tvar 0) A cint : Tau.
Check etype aliases (tvar 0) B cint : Tau.

Check evar 0 : EVar.

Check e_s  (i_e (i_i Z0)) : St.
Check retn (i_e (i_i Z0)) : St.
Check seq (e_s  (i_e (i_i Z0))) (retn (i_e (i_i Z0))) : St.
Check if_s (i_e (i_i Z0)) (e_s  (i_e (i_i Z0))) (retn (i_e (i_i Z0))) : St.
Check while (i_e (i_i Z0)) (retn (i_e (i_i Z0))) : St.
Check letx  (evar 0) (i_e (i_i Z0)) (retn (p_e (evar 0) [])) : St.
Check open (i_e (i_i Z0)) (tvar 0) (evar 0) (retn (p_e (evar 0) [])) : St.
Check openstar (i_e (i_i Z0)) (tvar 0) (evar 0) (retn (p_e (evar 0) [])) : St.

Example NumValue : Value (i_e (i_i Z0)).
Proof.
  apply IIsAValue.
Qed.

(* Bug 1, no amp in source. *)
Example AmpValue : 
  Value (amp (p_e (evar 0) [(i_pe one_pe)])).
Proof.
  apply AmpIsAValue.
Qed.

(* 2 bugs found, extra variable in quantification. *)
Example FunctionValue : 
  Value (f_e (dfun cint (evar 0) cint (retn (p_e (evar 0) [])))). 
Proof.
  apply DfunIsAValue.
Qed.

Example PolymorphicFunctionValue : 
  Value (f_e (ufun (tvar 0) A
                   (dfun cint (evar 0) cint (retn (p_e (evar 0) []))))).
Proof.
  apply UfunIsAValue.
Qed.

Example NotInDomHnil :
  getH [] (evar 0)  = None.
Proof.
  reflexivity.
Qed.

Example NotInDomHsingle :
  getH [] (evar 0)  = None.
Proof.
  reflexivity.
Qed.

Example NotInDomHdifferent :
  getH [(x,v0)] y = None. 
Proof.
  reflexivity.
Qed.

Example NotInDomHsecond :
  getH [(x,v0) ; (z,v0)] y = None.
Proof.
  reflexivity.
Qed.

Example NotInDomDnil :
  getD [] (tvar 0) = None.
Proof.
  reflexivity.
Qed.

Example NotInDomDsingle :
  getD [(alpha,A)] alpha = Some A.
Proof.
  reflexivity.
Qed.

Example NotInDomDdifferent :
   getD [(alpha,B)] beta = None.
Proof.
  reflexivity.
Qed.

Example NotInDomDsecond :
   getD [(alpha,A) ; (gamma,B)] beta = None.
Proof.
  reflexivity.
Qed.

(* TODO test setH. *)

Example deleteH_test_nil : 
  deleteH [] x = [].
Proof.
  reflexivity.
Qed.

Example deleteH_test_x :
  deleteH [(x,(i_e (i_i 0)))] x = [].
Proof.
  reflexivity.
Qed.

Example deleteH_test_xy :
  deleteH [(y,(i_e (i_i 0))) ; (x,(i_e (i_i 0)))] x = [(y,(i_e (i_i 0)))].
Proof.
  reflexivity.
Qed.

Example delete_test_yx :
  deleteH [(y,(i_e (i_i 0))) ; (x,(i_e (i_i 0)))] y = [(x,(i_e (i_i 0)))].
Proof.
 reflexivity.
Qed.

Example delete_test_z :
  deleteH [(y,(i_e (i_i 0))) ; (x,(i_e (i_i 0)))] z = 
          [(y,(i_e (i_i 0))) ; (x,(i_e (i_i 0)))].
Proof.
 reflexivity.
Qed.

Example setD_nil :
  setD [] alpha A = [(alpha,A)].
Proof.
  reflexivity.
Qed.

Example setD_exists :
  setD [(alpha,B)] alpha A = [(alpha,A)].
Proof.
  reflexivity.
Qed.

Example setD_add_to_end :
  setD [(alpha,B)] beta A = [(alpha,B); (beta,A)].
Proof.
  reflexivity.
Qed.

Example setD_overwrite_at_end :
  setD [(alpha,B); (beta, B)] beta A = [(alpha,B); (beta,A)].
Proof.
  reflexivity.
Qed.

Example setD_overwrite_at_start :
  setD [(alpha,B); (beta, B)] alpha A = [(alpha,A); (beta,B)].
Proof.
  reflexivity.
Qed.

Example getGx : 
  getG [(x,tau)] x = Some tau.
Proof.
  reflexivity.
Qed.

Example getGyx : 
  getG [(y,tau) ; (x,tau')] x = Some tau'.
Proof.
  reflexivity.
Qed.

Example NotInDomGnil :
  getG [] (evar 0) = None.
Proof.
  reflexivity.
Qed.

Example NotInDomGsingle :
  getG [(x,tau)] x = Some tau.
Proof.
  reflexivity.
Qed.

Example NotInDomGdifferent :
   getG  [(x,tau)] y = None.
Proof.
  reflexivity.
Qed.

Example NotInDomGsecond :
  getG [(x,tau) ; (z,tau') ] y = None.
Proof.
  reflexivity.
Qed.

Example getUnil :
  forall (tau : Tau),
    ~getU [] x [] tau.
Proof.
  intros.
  compute.
  intros.
  inversion H.
Qed.

(* TODO 
Example getUxBadPath : 
  getU (((x, p0), tau) :: nil) x [] tau.
Proof.
  constructor.
Qed.
*)

Example path_eq:
  beq_path [] [] = true.
Proof.
  reflexivity.
Qed.

Example getUx : 
  getU ((( x, p0), tau) :: nil) x p0 tau.
Proof.
  compute.
  constructor.
Qed.

(* Bug 6 in defintion x <>y \/ [] = nil. *)
Example getUyx : 
  getU [((y,nil),tau) ; ((x,nil),tau')] x [] tau'.
Proof.
  constructor.
  left.
  constructor.
  constructor.
Qed.


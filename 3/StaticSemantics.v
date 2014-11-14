(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This defines the static semantics of statements and expressions, pg. 63. 

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Export FormalSyntax.
Require Export DynamicSemanticsHeapObjects.
Require Export StaticSemanticsTypingHeapObjects.
Require Export StaticSemanticsKindingAndContextWellFormedness.

Inductive ret : St -> Prop :=
| ret_ret       : forall (e : E),
                       ret (retn e)

| ret_if        : forall (e : E) (s1 s2 : St),
                       ret s1 ->
                       ret s2 ->
                       ret (if_s e s1 s2)

| ret_seq_1     : forall (s s' : St),
                       ret s ->
                       ret (seq s s')

| ret_seq_2     : forall (s s' : St),
                       ret s ->
                       ret (seq s' s)

| ret_let       : forall (x : EVar) (e : E) (s : St),
                       ret s ->
                       ret (letx x e s)

| ret_open      : forall (e : E) (alpha : TVar) (x : EVar) (s : St),
                       ret s ->
                       ret (open e alpha x s)

| ret_openstar  : forall (e : E) (alpha : TVar) (x : EVar) (s : St),
                       ret s ->
                       ret (openstar e alpha x s).

Inductive styp : C -> Tau -> St   -> Prop :=
  | styp_e_3_1    : forall (c : C) (tau tau' : Tau) (e : E),        (* This is correct, return at end of program. *)
                      rtyp c e   tau' ->
                      styp c tau (e_s e)

  | styp_return_3_2 : forall (c : C) (tau : Tau) (e : E),
                         rtyp c e tau ->
                         styp c tau (retn e)

  | styp_seq_3_3    : forall (c : C) (tau : Tau) (s1 s2 : St),
                         styp c tau s1 ->
                         styp c tau s2 ->
                         styp c tau (seq s1 s2)

  | styp_while_3_4  : forall (c : C) (tau : Tau) (e: E) (s : St),
                         rtyp c e cint ->
                         styp c tau s ->
                         styp c tau (while e s)

  | styp_if_3_5     :  forall (c : C) (tau : Tau) (e: E) (s1 s2 : St),
                          rtyp c e cint ->
                          styp c tau s1 ->
                          styp c tau s2 ->
                          styp c tau (if_s e s1 s2)
                               
  | styp_let_3_6    :  forall (d : Delta) (u : Upsilon) (g : Gamma)
                               (x : EVar)  (tau tau' : Tau) 
                               (s : St) (e : E),
                          styp (c d u (g ++ [(x,tau')]))
                                            tau' s ->
                          rtyp (c d u g) e    tau' ->
                          styp (c d u g) tau  (letx x e s)

(* Bug 33, alpha conversion of alpha here ? *)

  | styp_open_3_7   :  forall (d : Delta) (u : Upsilon) (g : Gamma)
                               (x : EVar)  (p : Phi) (alpha : TVar)
                               (k : Kappa) (tau tau' : Tau)
                               (s : St) (e : E),
                          getD d alpha = None ->
                          getG g x = None ->
                          K d tau A      ->
                          rtyp (c d u g) e (etype p alpha k tau') ->
                          styp (c (d ++ [(alpha,k)]) u (g ++ [(x,tau')]))
                               tau s ->
                          styp (c d u g) tau (open e alpha x s)

  | styp_openstar_3_8 :  forall (d : Delta) (u : Upsilon) (g : Gamma)
                               (x : EVar)  (alpha : TVar)
                               (k : Kappa) (tau tau' : Tau)
                               (s : St) (e : E),
                          rtyp (c d u g) e (etype aliases alpha k tau') -> 
                          styp (c (d ++ [(alpha,k)])
                                  u 
                                  (g ++ [(x,tau')]))
                                  tau s ->
                          getD d alpha = None ->
                          getG g x = None ->
                          K d tau A      ->
                          styp (c d u g) tau (openstar e alpha x s)

with      ltyp : C -> E   -> Tau -> Prop := 

  | SL_3_1     : forall (d : Delta) (g : Gamma) (u : Upsilon) 
                           (x : EVar) (p : P) (tau tau': Tau),
                      getG g x = Some tau' ->
                      gettype u x nil tau' p = Some tau ->
                      WFC d u g->
                      K d tau' A -> 
                      ltyp (c d u g) (p_e x p) tau

  | SL_3_2     : forall (d : Delta) (u : Upsilon) (g : Gamma)
                        (e : E) (tau : Tau) ,
                      rtyp (c d u g) e (ptype tau) ->
                      K d tau A ->
                      ltyp (c d u g) (star e) tau

  | SL_3_3     : forall (c : C) (e : E) (t0 t1 : Tau),
                      ltyp c e (cross t0 t1) ->
                      ltyp c (dot e (i_i Z0)) t0

  | SL_3_4     : forall (c : C) (e : E) (t0 t1 : Tau),
                      ltyp c e (cross t0 t1) ->
                      ltyp c (dot e (i_i 1)) t1

with      rtyp : C -> E   -> Tau -> Prop := 
  | SR_3_1  : forall (d : Delta) (g : Gamma) (u : Upsilon) 
                        (x  : EVar) (p : P) (tau tau': Tau),
                   getG g x = Some tau' -> 
                   gettype u x nil tau' p = Some tau ->
                   K d tau' A ->
                   WFC d u g ->
                   rtyp (c d u g) (p_e x p) tau

  | SR_3_2  :  forall (e : E) (tau : Tau) 
                      (d : Delta) (u : Upsilon) (g : Gamma),
                    rtyp (c d u g) e (ptype tau) ->
                    K d tau A ->
                    rtyp (c d u g) (star e) tau
                            
  | SR_3_3  :  forall (c : C) (e : E) (t0 t1 : Tau),
                        rtyp c e (cross t0 t1) ->
                        rtyp c (dot e (i_i Z0)) t0

  | SR_3_4  : forall (c : C) (e : E) (t0 t1 : Tau),
                      rtyp c e (cross t0 t1) ->
                      rtyp c (dot e (i_i 1)) t1

  | SR_3_5  : forall (d : Delta) (u : Upsilon) (g : Gamma) (z : Z),
                   WFC d u g ->
                   rtyp (c d u g) (i_e (i_i z)) cint

  | SR_3_6  : forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau : Tau),
                   ltyp (c d u g) e tau ->
                   rtyp (c d u g) (amp e) (ptype tau)

  | SR_3_7  : forall (d : Delta) (u : Upsilon) (g : Gamma) (e0 e1: E) (t0 t1 : Tau),
                   rtyp (c d u g) e0 t0 ->
                   rtyp (c d u g) e1 t1 ->
                   rtyp (c d u g) (cpair e0 e1) (cross t0 t1)

  | SR_3_8  : forall (d : Delta) (u : Upsilon) (g : Gamma) (e1 e2 : E) (tau : Tau),
                   ltyp (c d u g) e1 tau ->
                   rtyp (c d u g) e2 tau ->
                   ASGN d tau    ->
                   rtyp (c d u g) (assign e1 e2) tau

  | SR_3_9  : forall (c : C) (e1 e2 : E) (tau tau' : Tau),
                   rtyp c e1 (arrow tau' tau) ->
                   rtyp c e2 tau' ->
                   rtyp c (appl e1 e2) tau

  | SR_3_10 : forall (c : C) (tau : Tau) (s : St),
                   styp c tau s ->
                   ret s ->
                   rtyp c (call s) tau

  | SR_3_11 : forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) 
                        (tau tau': Tau) (alpha : TVar) (k : Kappa),
                   rtyp (c d u g) e (utype alpha k tau') ->
                   AK   d tau k ->
                   rtyp (c d u g) (inst e tau) (subst_Tau tau' tau alpha)

  | SR_3_12 : forall (d : Delta) (u : Upsilon) (g : Gamma) (e : E) 
                        (tau tau': Tau) (alpha : TVar) (k : Kappa) (p : Phi),
                   rtyp (c d u g) e (subst_Tau tau tau' alpha) ->
                   AK   d tau' k -> 
                   K    d (etype p alpha k tau) A ->
                   rtyp (c d u g) (pack tau' e (etype p alpha k tau)) (etype p alpha k tau)

  | SR_3_13 : forall (d : Delta) (u : Upsilon) (g : Gamma) (tau tau': Tau) (s : St) (x : EVar),
                   getG g x = None ->
                   styp (c d u (g ++ [(x,tau)])) tau' s ->
                   ret s ->
                   rtyp (c d u g) (f_e (dfun tau x tau' s)) (arrow tau tau')

  | SR_3_14 : forall (d : Delta) (u : Upsilon) (g : Gamma) (f : F)
                        (tau : Tau) (alpha : TVar) (k : Kappa),
                   getD d alpha = None ->
                   WFC  d u g ->
                   rtyp (c (d ++ [(alpha,k)]) u g) (f_e f) tau ->
                   rtyp (c d u g) (f_e (ufun alpha k f)) (utype alpha k tau).

Scheme styp_ind_mutual := Induction for styp Sort Prop
with   ltyp_ind_mutual := Induction for ltyp Sort Prop
with   rtyp_ind_mutual := Induction for rtyp Sort Prop.
Combined Scheme typ_ind_mutual from
          styp_ind_mutual, ltyp_ind_mutual, rtyp_ind_mutual.

Inductive htyp: Upsilon -> Gamma -> H -> Gamma -> Prop :=
  | htyp_empty : forall (u : Upsilon) (g: Gamma),
                      htyp u g nil nil
  | htyp_xv    : forall (u : Upsilon) (g g': Gamma) (h h': H) (x : EVar) (v : E) (tau : Tau),
                      Value v -> 
                      htyp u g (h ++ h') g' ->
                      rtyp (c nil u g) v tau ->
                      htyp u g (h ++ [(x,v)] ++ h') (g' ++ [(x, tau)]).

Inductive refp  : H -> Upsilon -> Prop :=
  | refp_empty  : forall (h : H),
                       refp h nil
  | refp_pack  : forall (h : H) (u : Upsilon) (x : EVar) (p : P) (tau tau' : Tau) (alpha : TVar) (k : Kappa) (v v' : E),
                      getH h x = Some v' -> 
                      get v' p (pack tau' v (etype aliases alpha k tau)) ->
                      refp h u ->
                      refp h (u ++ [((p_e x p),tau')]).

Inductive prog  : H -> St -> Prop := 
  | program  : forall (h : H) (u : Upsilon) (g : Gamma) (tau : Tau) (s : St),
                    htyp u g h g ->
                    refp h u     ->
                    styp (c nil u g) tau s ->
                    ret s -> 
                    prog h s.

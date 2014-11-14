(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This defines the dynamic semantics of statements and expressions, pg. 58, 59.

*)
 
Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Relation_Definitions.

Require Export FormalSyntax.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.

Inductive S : State -> State -> Prop :=

 | S_Let_3_1 : forall (x : EVar) (v : E) (H: H) (s: St),
              Value v ->
              getH H x = None -> 
              S (state H (letx x v s)) (state ((x,v) :: H) s)

 | S_Seq_3_2 : forall (v : E) (H: H) (s: St),
                  Value v ->
                  S (state H (seq (e_s v) s)) (state H s)

 | S_Return_3_3: forall (v : E) (H: H) (s: St),
                    Value v ->
                    S (state H (seq (retn v) s)) (state H (retn v))

 | S_If0_3_4: forall (H: H) (s1 s2: St),
                 S (state H (if_s (i_e (i_i 0)) s1 s2))
                   (state H s1)

 | S_If_ne_0_3_5: forall (H: H) (z : Z) (s1 s2: St),
                     z <> Z0 ->                                  
                     S (state H (if_s (i_e (i_i z)) s1 s2))
                       (state H s2)

 | S_while_3_6: forall (H: H) (e : E) (s : St),
                     S (state H (while e s))
                       (state H (if_s e (seq s (while e s)) (e_s (i_e (i_i 0)))))

| S_open_3_7:  forall (tau tau' : Tau) (v : E) (p : Phi) (k : Kappa) (alpha : TVar) (x x': EVar) (H : H) (s : St),
                  Value v ->
                  S (state H (open (pack tau' v (etype p alpha k tau)) alpha x s))
                    (state H (letx x' v (subst_St s tau alpha)))

| S_openstar_3_8: forall (tau tau' : Tau) (v v' : E) (q : Phi) (k : Kappa) (alpha : TVar) (x x': EVar) (H : H) (s : St) (p : P),
                    Value v ->
                    x <> x' ->
                    get v' p (pack tau' v (etype q alpha k tau)) ->
                    (* S is part of the context not the heap, overloading ; in DS3.8 *)
                    (* x' is right, openstar uses *x' but I am eliding it in the syntax. *)
                    getH H x = Some v' ->
                    S (state H (openstar (p_e x p) alpha x' s))
                      (state H (letx x'  (amp (p_e x (p ++ [u_pe]))) 
                                     (subst_St s tau alpha)))

| S_exp_3_9_1: forall (h h' : H) (e e' : E),
                   R (state h (e_s e)) (state h' (e_s e')) ->
                   S (state h (e_s e)) (state h' (e_s e'))

| S_ret_3_9_2: forall (h h' : H) (e e' : E),
                   R (state h (e_s e)) (state h' (e_s e')) ->
                   S (state h (retn e)) (state h' (retn e'))

| S_if_3_9_3: forall (h h' : H) (e e' : E) (s1 s2 : St),
                   R (state h (e_s e)) (state h' (e_s e')) ->
                   S (state h (if_s e s1 s2)) (state h' (if_s e' s1 s2))

| S_letx_3_9_4: forall (h h' : H) (e e' : E) (s : St) (x : EVar),
                   R (state h (e_s e)) (state h' (e_s e')) ->
                   S (state h (letx x e s)) (state h' (letx x e' s))

| S_open_3_9_5: forall (h h' : H) (e e' : E) (x : EVar) (alpha : TVar) (s : St),
                   R (state h (e_s e)) (state h' (e_s e')) ->
                   S (state h  (open e  alpha x s))
                        (state h' (open e' alpha x s))

| S_seq_3_10:  forall (h h' : H) (s s' s2: St),
                    S (state h s) (state h' s') ->
                    S (state h  (seq s  s2)) (state h' (seq s' s2))

| S_openstar_3_11: forall (h h' : H) (e e' : E) (x : EVar) (alpha : TVar) (s : St),
                        L (state h  (e_s e)) (state h' (e_s e')) ->
                        S (state h  (openstar e  alpha x s))
                             (state h' (openstar e' alpha x s))

with R : State -> State -> Prop :=

 | R_get_3_1 : forall (H : H) (x : EVar) (p : P) (v v' : E),
                    Value v ->
                    Value v' ->
                    get v' p v ->
                    getH H x = Some v' -> 
                    R (state H (e_s (p_e x p)))
                      (state H (e_s v))

 | R_read_heap_3_2:
     forall (H' H : H) (v v' v'' : E) (x : EVar) (p : P),
       Value v   ->
       Value v'  ->
       Value v'' ->
       set v' p v v'' ->
       R (state (H ++ ([(x,v')] ++ H'))  (e_s (assign (p_e x p) v)))
         (state (H ++ ([(x,v'')] ++ H')) (e_s v))

 | R_star_3_3:    forall (H : H) (x : EVar) (p : P),
                 R (state H (e_s (star (amp (p_e x p)))))
                   (state H (e_s (p_e x p)))

 (* Split on 0 or 1. *)
 | R_dot_3_4_0:  forall (H : H) (v0 v1 : E),
                    R (state H (e_s (dot (cpair v0 v1) (i_i 0))))
                      (state H (e_s v0))

 | R_dot_3_4_1:  forall (H : H) (v0 v1 : E),
                    R (state H (e_s (dot (cpair v0 v1) (i_i 1))))
                      (state H (e_s v1))

 | R_appl_3_5:   forall (H : H) (x : EVar) (tau tau' : Tau) (v : E) (s : St),
                    Value v ->
                    R (state H (e_s (appl (f_e (dfun tau x tau' s)) v)))
                      (state H (e_s (call (letx x v s))))

 | R_call_3_6:    forall (H : H) (v : E),
                    Value v ->
                    R (state H (e_s (call (retn v))))
                         (state H (e_s v))

 | R_inst_3_7:  forall (H : H) (alpha : TVar) (k : Kappa) (f : F) (tau : Tau),
                  R (state H (e_s (inst (f_e (ufun alpha k f)) tau)))
                    (state H (e_s (f_e (subst_F f tau alpha))))

 | R_call_3_8:  forall (h h': H) (s s': St), 
                  S (state h s) (state h' s') ->
                  R (state h (e_s (call s))) (state h' (e_s (call s')))
 
 | R_amp_3_9_1: forall (h h' : H) (e e' : E),
                   L (state h (e_s e))       (state h' (e_s e')) ->
                   R (state h (e_s (amp e))) (state h' (e_s (amp e')))

 | R_assign_3_9_2: forall (h h' : H) (e e' e2: E),
                   L (state h (e_s e))             (state h' (e_s e')) ->
                   R (state h (e_s (assign e e2))) (state h' (e_s (assign e' e2)))

 | R_star_3_10_1: forall (h h' : H) (e e' : E),
                    R (state h (e_s e))        (state h' (e_s e')) ->
                    R (state h (e_s (star e))) (state h' (e_s (star e')))

 | R_dot_3_10_2: forall (h h' : H) (e e' : E) (z : Z),
                    R (state h (e_s e)) (state h' (e_s e')) ->
                    R (state h  (e_s (dot e  (i_i z))))  
                      (state h' (e_s (dot e' (i_i z))))

 | R_assign_3_10_3: forall (h h' : H) (e e' : E) (x : EVar) (p : P),
                    R (state h (e_s e)) (state h' (e_s e')) ->
                    R (state h  (e_s (assign (p_e x p) e)))
                      (state h' (e_s (assign (p_e x p) e')))

 | R_inst_3_10_4:  forall (h h' : H) (e e' : E) (tau : Tau),
                 R (state h (e_s e)) (state h' (e_s e')) ->
                 R (state h  (e_s (inst e tau))) 
                   (state h' (e_s (inst e' tau)))

 | R_pack_3_10_5:  forall (h h' : H) (e e' : E) (tau tau' : Tau) (p : Phi) (k : Kappa) (alpha : TVar),
                    R (state h (e_s e))        (state h' (e_s e')) ->
                    R (state h  (e_s (pack tau' e  (etype p alpha k tau))))
                      (state h' (e_s (pack tau' e' (etype p alpha k tau))))

 | R_cpair_3_10_6:  forall (h h' : H) (e e' e2 : E),
                    R (state h (e_s e)) (state h' (e_s e')) ->
                    R (state h  (e_s (cpair e e2)))
                      (state h' (e_s (cpair e' e2)))

 | R_cpair_3_10_7:  forall (h h' : H) (e e' v : E),
                    Value v -> 
                    R (state h (e_s e)) (state h' (e_s e')) ->
                    R (state h  (e_s (cpair v e)))
                      (state h' (e_s (cpair v e')))

 | R_cpair_3_10_8:  forall (h h' : H) (e e' e2 : E),
                    R (state h (e_s e)) (state h' (e_s e')) ->
                    R (state h  (e_s (cpair e e2)))
                      (state h' (e_s (cpair e' e2)))

 | R_appl_3_10_9:  forall (h h' : H) (e e' e2 : E),
                    R (state h  (e_s e)) (state h' (e_s e')) ->
                    R (state h  (e_s (appl e e2)))
                      (state h' (e_s (appl e' e2)))

 | R_appl_3_10_10: forall (h h' : H) (v e e': E),
                     Value v ->
                     R (state h  (e_s e)) (state h' (e_s e')) ->
                     R (state h  (e_s (appl v e)))
                       (state h' (e_s (appl v e')))

with L : State -> State -> Prop :=

 | L_xpi_3_1: forall (H : H) (x : EVar) (p : P) (z : Z),
                L (state H (e_s (dot (p_e x p) (i_i z))))
                  (state H (e_s (p_e x (p ++ [(i_pe (i_i z))]))))

 | L_staramp_3_2: forall (H : H) (x : EVar) (p : P),
                    L (state H (e_s (star (amp (p_e x p)))))
                      (state H (e_s (p_e x p)))

 | L_star_3_3: forall (h h' : H) (e e': E),
                 R (state h (e_s e))        (state h' (e_s e')) ->
                 L (state h (e_s (star e))) (state h' (e_s (star e'))) 

 | L_ei_3_4: forall (h h' : H) (e e': E) (z : Z),
               L (state h (e_s e))                (state h' (e_s e')) ->
               L (state h (e_s (dot e (i_i z))))  (state h' (e_s (dot e' (i_i z)))).

Scheme R_ind_mutual := Induction for R Sort Prop
with   S_ind_mutual := Induction for S Sort Prop
with   L_ind_mutual := Induction for L Sort Prop.
Combined Scheme SLR_ind_mutual 
         from S_ind_mutual, L_ind_mutual, R_ind_mutual.

(* Transitive, reflexive closure of S. *)
(* Borrowed from Software Foundations. *)
Inductive multi {X:Type} (R: relation X) : relation X :=
  | multi_refl  : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Definition Sstar := (multi S).
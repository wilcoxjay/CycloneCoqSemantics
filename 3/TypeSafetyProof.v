(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Defining type safety, page 67.

*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.
Require Import Coq.Init.Logic.

Require Export FormalSyntax.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export DynamicSemanticsTypeSubstitution.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemantics.
Require Export TypeSafety.
Require Export CpdtTactics.

Theorem Type_Safety :
(*   If ·; ·; ·; τ styp s, ret s, and ·; s → H ; s *)
 forall (s : St) (tau : Tau),
        styp [] [] [] tau s ->
        ret s ->
        exists (h' : H) (s' : St), 
           Sstar [] s h' s' -> 
           NotStuck h' s'.
Proof.
 Definition Thm (s : St) (tau : Tau) : Prop := 
   (ret s ->
     exists (h' : H) (s' : St), 
       Sstar [] s h' s' -> 
       NotStuck h' s').
  intros s tau.
  apply (Term_ind_mutual
           (fun (s : St) =>  
              forall (tau : Tau) (ts : (styp [] [] [] tau s)), 
                Thm s tau)
           (fun (e : E ) =>
              forall (tau : Tau) (ts : (styp [] [] [] tau (e_s e))),
                Thm (e_s e) tau)
           (fun (f : F) =>
              forall (ts : (styp [] [] [] tau (e_s (f_e f)))),
                Thm (e_s (f_e f)) tau));
        repeat (unfold Thm; crush).
  (* Crush gets one. *)
Admitted.

(* Try a context weakening. *)
Lemma A_1_Context_Weakening_1:
  forall (d d' : Delta) (tau : Tau) (k : Kappa),
    K d tau k ->
    K (d ++ d') tau k.
Proof.
  intros d d' tau k.
  intros Kder.
  induction Kder; crush.
  (* Crush get's zero, no wonder, no inductive hypothesis. *)
Admitted.

Lemma A_1_Context_Weakening_2:
  forall (u : Upsilon) (d : Delta) (tau : Tau) 
         (x : EVar) (p : P),
    getU u x p = Some tau ->
    WFU u ->
    K d tau A.
Proof.
  intros u d t x p getUder WFUder.
  (* Losing wfu nil. *)
  induction WFUder. 
  (* crush gets zero. *)
Admitted.

Lemma A_2_Term_Weakening_1 :
  forall (d: Delta) (u u' : Upsilon) (g g' : Gamma)
         (x : EVar) (p p' : P) (tau tau' : Tau),
    WFC d (u ++ u') (g ++ g') ->
    gettype u x p tau p' = Some tau' ->
    gettype (u ++ u') x p tau p' = Some tau'.
Proof.
  intros d u u' g g' x p p' tau tau'.
  intros WFCd.
  intros gettypederivation.
  functional induction (gettype u x p tau p'); crush.
  (* Warning: Collision between bound varibles of name x *)
  (* Crush gets 25. *)
Admitted.

Lemma A_2_Term_Weakening_2_3_4 :
  forall (d: Delta) (u u' : Upsilon) (g g' : Gamma)
         (e : E) (tau : Tau),
    WFC d (u ++ u') (g ++ g') ->
    ltyp d u g e tau ->
    ltyp d (u ++ u') (g++g') e tau.
Proof.
  intros d u u' g g' e tau WFC.
  apply (typ_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) =>
              ltyp d (u ++ u') (g++g') e tau)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (lt : ltyp d u g e t) =>
              ltyp d (u ++ u') (g++g') e tau)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              ltyp d (u ++ u') (g++g') e tau)); crush.
  (* Crush get's 3. *)
Admitted.

Lemma A_3_Heap_Weakening_1:
  forall (u u' : Upsilon) (g g' g'': Gamma) (h : H),
   (WFC [] (u ++ u') (g ++ g') /\ htyp u g h g'') ->
    htyp (u ++ u') (g ++ g') h g''.
Proof.
  intros u u' g g' g'' h.
  intros WFCder.
  induction WFCder.
  (* Collision. *)
  (* Crush get's 0. *)
Admitted.

Lemma A_3_Heap_Weakening_2:
  forall (u u' : Upsilon) (h h': H),
    refp h u ->
    refp (h ++ h') u.
Proof.
  intros u u' h h'.
  intros refpder.
  induction refpder.
  (* Crush gets 0. *)
  Focus 2.
Admitted.

Lemma A_4_Useless_Substitutions_1:
  forall (d : Delta) (alpha : TVar) (tau tau' : Tau) (k : Kappa),
    getD d alpha = None ->
    K d tau' k ->
    subst_Tau tau' tau alpha = tau'.
Proof.
  intros d alpha tau tau' k.
  intros gd Kder.
  induction Kder; crush.
  (* Crush gets 5 goals. *)
Admitted.    

Lemma A_4_Useless_Substitutions_2:
  forall (d : Delta) (alpha : TVar) (tau tau' : Tau) (g : Gamma),
    getD d alpha = None ->
    WFDG d g ->
    subst_Gamma g tau alpha = g.
Proof.
  intros d alpha tau tau' k.
  intros gd Kder.
  (* apply A_4_Useless_Substitutions_1. *)
Admitted.    

Lemma A_4_Useless_Substitutions_3:
  forall (d : Delta) (alpha : TVar) (tau tau': Tau) (u : Upsilon) (p : P)
         (x : EVar),
    getD d alpha = None ->
    WFU u ->
    getU u x p = Some tau' ->
    subst_Tau tau' tau alpha = tau'.
Proof.
  intros d alpha tau tau' k.
  intros gd Kder.
  (* apply A_4_Useless_Substitutions_1. *)
Admitted.

(* TODO do I have the ordering right? *)
Lemma A_5_Commuting_Substitutions:
  forall (alpha beta : TVar) (t0 t1 t2 : Tau),
    NotFreeInTau beta t2 = true ->
    (subst_Tau (subst_Tau t0 t1 beta) t2 alpha) = 
    (subst_Tau (subst_Tau t0 t2 alpha)
              (subst_Tau t1 t2 alpha)
              beta).
Proof.
  intros alpha beta t0 t1 t2.
  intros NF.
  induction t0; crush.
  (* crush get's six. *)
Admitted.

Lemma A_6_Substitution_1:
  forall (d : Delta) (alpha : TVar) (tau tau' : Tau) (k k': Kappa),
    AK d tau k -> 
    K (d ++ [(alpha,k)]) tau' k' ->
    K d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d alpha tau tau' k k'.
  intros AKder Kder.
  induction Kder.
  (* Crush gets 0. *)
Admitted.    

Lemma A_6_Substitution_2:
  forall (d : Delta) (alpha : TVar) (tau tau' : Tau) (k k': Kappa),
    AK d tau k -> 
    AK (d ++ [(alpha,k)]) tau' k' ->
    AK d (subst_Tau tau' tau alpha) k'.
Proof.
  intros d alpha tau tau' k k'.
  intros AKder AKder2.
  induction AKder2.
  (* crush gets 0. *)
Admitted.    

Lemma A_6_Substitution_3:
  forall (d : Delta) (alpha : TVar) (tau tau' : Tau) (k : Kappa),
    AK d tau k -> 
    ASGN (d ++ [(alpha, k)]) tau' ->
    ASGN d (subst_Tau tau' tau alpha).
Proof.
  intros d alpha tau tau' k k'.
  intros ASGNder.
  induction ASGNder.
  (* crush gets 0. *)
Admitted.    

Lemma A_6_Substitution_4:
  forall (d : Delta) (alpha : TVar) (tau : Tau) (g : Gamma) (k : Kappa),
    AK d tau k -> 
    WFDG (d ++ [(alpha,k)]) g ->
    WFDG d (subst_Gamma g tau alpha).
Proof.
  intros d alpha tau tau' k AKder.
  intros WFDGder.
  induction WFDGder.
  (* crush gets 0. *)
Admitted.    

Lemma A_6_Substitution_5:
  forall (d : Delta) (u : Upsilon ) (alpha : TVar) (tau : Tau) 
         (g : Gamma) (k : Kappa),
    AK d tau k -> 
    WFC (d ++ [(alpha,k)]) u g ->
    WFC d u (subst_Gamma g tau alpha).
Proof.
  intros d u alpha tau g k.
  intros AKder WFCder.
  induction WFCder.
(* crush gets 0. *)
Admitted.    

Lemma A_6_Substitution_6:
  forall (d : Delta) (alpha : TVar) (tau : Tau) (s : St) (k : Kappa),
    AK d tau k -> 
    ret s ->
    ret (subst_St s tau alpha).
Proof.
  intros d alpha tau s k AKder retder.
  induction retder.
  (* crush gets 0. *)
Admitted.    

Lemma A_6_Substitution_7:
  forall (d: Delta) (u : Upsilon ) (alpha : TVar) (x : EVar) 
         (t1 t2 tau : Tau) (p p': P) (k : Kappa),
    AK d tau k -> 
    WFU u ->
    gettype u x p t1 p' = Some t2 ->
    gettype u x p (subst_Tau t1 tau alpha) p' = 
    Some (subst_Tau t2 tau alpha).
Proof.
  intros d u alpha x t1 t2 tau p p' k.
  intros AKder WFUder.
  functional induction (gettype u x p t1 p'); crush.
  (* crush gets 24/26. *)
Admitted.    

(* Dan, is that last ltyp supposed to be an styp? *)

Lemma A_6_Substitution_8_1_2_3:
  forall (d d': Delta) (alpha : TVar) (u : Upsilon) (g : Gamma) 
         (e : E) (tau tau' : Tau) (k : Kappa),
    AK d tau k ->
    ltyp (d ++ [(alpha,k)]) u g e tau' ->
    d = (d' ++ [(alpha,k)]) ->
    ltyp d u (subst_Gamma g tau alpha)
         (subst_E e tau alpha)
         (subst_Tau tau' tau alpha).
Proof.
  intros d d' alpha u g e tau tau' k.
  intros AKder D'.
  apply (typ_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              d = (d' ++ [(alpha,k)]) ->
              styp d u (subst_Gamma g tau alpha)
                   (subst_Tau tau' tau alpha)
                   (subst_St s tau alpha))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
                (lt : ltyp d u g  e tau') =>
              d = (d' ++ [(alpha,k)]) ->
              ltyp d u (subst_Gamma g tau alpha)
                   (subst_E e tau alpha)
                   (subst_Tau tau' tau alpha))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              d = (d' ++ [(alpha,k)]) ->
              rtyp d u (subst_Gamma g tau alpha)
                   (subst_E e tau alpha)
                   (subst_Tau tau' tau alpha))).
  (* crush gets zero. *)
Admitted.    

Lemma A_7_Typing_Well_Formedness_1 :
  forall (d: Delta) (u : Upsilon) (x : EVar) (tau tau' : Tau) (p p' : P),
    WFU u ->
    K d tau A ->
    gettype u x p tau p' = Some tau' ->
    K d tau' A.
Proof.
  intros d u x tau tau' p p'.
  intros WFUder Kder.
  functional induction (gettype u x p tau p'); crush.
  (* Wow, crush gets 23/26. *)
Admitted.

Lemma A_7_Typing_Well_Formedness_2 :
  forall (d: Delta) (g : Gamma) (u : Upsilon) (tau : Tau) (e : E),
  ltyp d u g e tau ->
  (WFC d u g /\ 
   K d tau A).
Proof.
  intros d g u tau e.
  apply (typ_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              (WFC d u g /\  K d tau A))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
                (lt : ltyp d u g  e tau') =>
              (WFC d u g /\  K d tau A))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              (WFC d u g /\  K d tau A))); crush.
  (* Crush gets 21 subgoals. *)
Admitted.

Lemma A_7_Typing_Well_Formedness_3 :
  forall (d: Delta) (g : Gamma) (u : Upsilon) (tau : Tau) (e : E),
    rtyp d u g e tau ->
    (WFC d u g /\ 
     K d tau A).
Proof.
  intros d g u tau e.
  apply (typ_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              (WFC d u g /\  K d tau A))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
                (lt : ltyp d u g  e tau') =>
              (WFC d u g /\  K d tau A))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              (WFC d u g /\  K d tau A))); crush.
  (* Wow crush gets 21/26. *)
Admitted.

Lemma A_7_Typing_Well_Formedness_4 :
  forall (d: Delta) (g : Gamma) (u : Upsilon) (tau : Tau) (s : St),
    styp d u g tau s ->
    WFC d u g.
Proof.
  intros d g u tau e.
  apply (typ_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              (WFC d u g /\  K d tau A))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
                (lt : ltyp d u g  e tau') =>
              (WFC d u g /\  K d tau A))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              (WFC d u g /\  K d tau A))); crush.
  (* crush gets 21/26. *)
Admitted.

Lemma A_7_Typing_Well_Formedness_5 :
  forall (d: Delta) (g : Gamma) (u : Upsilon) (tau : Tau) (s : St),
    styp d u g tau s ->
    ret s ->
    K d tau A.
Proof.
  intros d g u tau e.
  apply (typ_ind_mutual
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
                  ret s ->
                  K d tau A)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
                (lt : ltyp d u g  e tau') =>
                  K d tau A)
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
                  K d tau A)); crush.
  (* Crush gets 21/16 goals. *)
Admitted.

Lemma A_8_Return_Preservation:
  forall (s s' : St) (h h' : H),
  ret s ->
  S h s h' s' ->
  ret s'.
Proof.
  intros s s' h h' retder.
  apply (SLR_ind_mutual 
           (fun (h : H) (s : St) (h' : H) (s' : St) (rstep: R h s h' s') =>
              ret s')
           (fun (h : H) (s : St) (h' : H) (s' : St) (sstep: S h s h' s') =>
              ret s')
           (fun (h : H) (s : St) (h' : H) (s' : St) (lstep: L h s h' s') =>
              ret s')); crush.
  (* Crush get's 1 goal. *)
Admitted.

(* Wow, my first real proof! *)
Lemma A_9_Cannonical_Forms_1:
  forall (u : Upsilon) (g : Gamma) (v : E),
    Value v ->
    rtyp [] u g v cint ->
    exists z : Z, v = (i_e (i_i z)).
Proof.
  intros u g v valv.
  intros rtypder.
  destruct valv; inversion rtypder.
  exists z.
  reflexivity.
Qed.

Lemma A_9_Cannonical_Forms_2:
  forall (u : Upsilon) (g : Gamma) (v : E) (t0 t1 : Tau),
    Value v ->  
    rtyp [] u g v (cross t0 t1) ->
    exists (v0 v1 : E),
      Value v0 /\  Value v1 /\ v = (cpair v0 v1).
Proof.
  intros u g v t0 t1 valv.
  intros rtypder.
  destruct valv; inversion rtypder.
  exists v0.
  exists v1.
  eauto.
Qed.

Lemma A_9_Cannonical_Forms_3:
  forall (u : Upsilon) (g : Gamma) (v : E) (t0 t1 : Tau),
    Value v ->
    rtyp [] u g v (arrow t0 t1) ->
    exists (x : EVar) (s : St), 
      v = (f_e (dfun t0 x t1 s)).
Proof.
  intros u g v t0 t1 valv.
  intros rtypder.
  destruct valv; inversion rtypder.
  subst.
  exists x.
  exists s.
  reflexivity.
Qed.

Lemma A_9_Cannonical_Forms_4:
  forall (u : Upsilon) (g : Gamma) (v : E) (t' : Tau),
    Value v ->
    rtyp [] u g v (ptype t') ->
    exists (x : EVar) (p : P),
      v = (amp (p_e x p)).
Proof.
  intros u g v t' valv.
  intros rtypder.
  destruct valv; inversion rtypder.
  subst.
  exists x.
  exists p.
  reflexivity.
Qed.

Lemma A_9_Cannonical_Forms_5:
  forall (u : Upsilon) (g : Gamma) (v : E) (tau' : Tau) (alpha : TVar)
         (k : Kappa),
    Value v ->
    rtyp [] u g v (utype alpha k tau') ->
    exists (f : F),
      v = (f_e (ufun alpha k f)).
Proof.
  intros u g v tau' alpha kappa valv.
  intros rtypder.
  destruct valv; inversion rtypder.
  subst.
  exists f.
  reflexivity.
Qed.

Lemma A_9_Cannonical_Forms_6:
  forall (u : Upsilon) (g : Gamma) (v : E) (tau' : Tau) (alpha : TVar)
         (k : Kappa),
    Value v ->
    rtyp [] u g v (etype nowitnesschange alpha k tau') ->
    exists (tau'' : Tau) (v' : E),
      v = (pack tau'' v' (etype nowitnesschange alpha k tau')).
Proof.
  intros u g v tau' alpha kappa valv.
  intros rtypder.
  destruct valv; inversion rtypder.
  subst.
  exists tau.
  exists v.
  reflexivity.
Qed.

Lemma A_9_Cannonical_Forms_7:
  forall (u : Upsilon) (g : Gamma) (v : E) (tau' : Tau) (alpha : TVar)
         (k : Kappa),
    Value v ->
    rtyp [] u g v (etype aliases alpha k tau') ->
    exists (tau'' : Tau) (v' : E),
      v = (pack tau'' v' (etype aliases alpha k tau')).
Proof.
  intros u g v tau' alpha kappa valv.
  intros rtypder.
  destruct valv; inversion rtypder.
  subst.
  exists tau.
  exists v.
  reflexivity.
Qed.

(* Ask Dan if this is correct. 
   TODO Interesting that we have i here where only 0/1 really do. *)
Lemma A_10_Path_Extension_1_A:
  forall (v v' v0 v1 : E) (p : P) (n : nat),
    Value v  ->
    Value v' ->
    get v p v' ->
    n = length p ->
    ((v' = (cpair v0 v1) ->
      (get v (p ++ [i_pe (i_i 0)]) v0) /\ 
      (get v (p ++ [i_pe (i_i 1)]) v1)) \/
     forall (i : Z) (p' : P) (v'' : E),
      ~(get v (p ++ [i_pe (i_i i)] ++ p') v'')).
Proof.
  intros v v' v0 v1 p n.
  intros valv valv' getvpv'.
  induction n.
Admitted.

Lemma A_10_Path_Extension_1_B:
  forall (v v' v0 : E) (tau tau' : Tau) (alpha : TVar) (k : Kappa)
         (p : P) (n : nat),
    Value v  ->
    Value v' ->
    get v p v' ->
    n = length p ->
    ((v' = (pack tau' v0 (etype aliases alpha k tau)) ->
      (get v (p ++ [u_pe]) v0)) \/
     forall (p' : P) (v'' : E),
      ~(get v (p ++ [u_pe] ++ p') v'')).
Proof.
  intros v v' v0 v1 p n.
  intros valv valv' getvpv'.
  induction n.
  (* crush gets 0. *)
Admitted.

Lemma A_10_Path_Extension_2_A:
  forall (u : Upsilon) (x : EVar) (p p' : P) (tau tau' t0 t1 : Tau)
         (n : nat),
    gettype u x p tau p' = Some tau' ->
    tau' = (cross t0 t1) ->
    n = length p' ->
    (gettype u x p tau (p' ++ [i_pe (i_i 0)]) = Some t0  /\
     gettype u x p tau (p' ++ [i_pe (i_i 1)]) = Some t1).
Proof.
  intros.
  induction n.
  (* Wierd, crush gives subgoals. *)
Admitted.

Lemma A_10_Path_Extension_2_B:
  forall (u : Upsilon) (alpha : TVar) (x : EVar) (p p' : P) 
         (tau tau' t0 uxp: Tau) (k : Kappa) (n : nat),
    gettype u x p tau p' = Some tau' ->
    tau' = (etype nowitnesschange alpha k t0) ->
    getU u x p = Some uxp->
    n = length p' ->
    gettype u x p tau (p' ++ [u_pe]) = Some (subst_Tau uxp uxp alpha).
Proof.
  intros.
  induction n. 
  (* crush gets 0. *)
Admitted.

(* TODO are the orderings of quantifiers correct? *)
Lemma A_11_Heap_Object_Safety_1:
  forall (v1 : E) (p : P) (n : nat),
    Value v1 ->
    n = length p ->
    exists ! (v2 : E),
      Value v2 ->
      get v1 p v2.
Proof.
  intros.
  induction n.
  (* crush gets 0. *)
Admitted.

Lemma A_11_Heap_Object_Safety_2:
  forall (v0 v1 v2 : E) (p1 p2 : P) (n : nat),
    Value v0 ->
    Value v1 ->
    Value v2 ->
    n = length p1 ->
    get v0 p1 v1 ->
    get v0 (p1 ++ p2) v2 ->
    get v1 p2 v2.
Proof.
  intros.
  induction n.
  (* crush gets 0. *)
Admitted.

Lemma A_11_Heap_Object_Safety_3:
  forall (h : H) (u : Upsilon) (g : Gamma) 
         (x : EVar) (p1 p2 : P) (t1 t2 : Tau)
         (v1 v2 vhx : E) (n : nat),
    Value v1 ->
    Value v2 ->
    refp h u ->
    htyp u g h g ->
    getH h x = Some vhx ->
    get vhx p1 v1 ->
    rtyp [] u g v1 t1 ->
    gettype u x p1 t1 p2 = Some t2 ->
    n = length p2 ->
    (exists (v2 : E),
       get vhx (p1 ++ p2) v2 /\ 
       rtyp [] u g v2 t2) /\
    (forall (v2' : E),
       Value v2' ->
       (exists (v1' : E),
          Value v1' ->
          set v1 p2 v2' v1')).
Proof.
  intros.
  induction n.
  (* crush adds 2 goals. *)
Admitted.


(* Just instantiating the above at H(x) = v and p1 = nil. *)
(* Dan, is U; \Gamma supposed to be \Upsilon ; \Gamma ? *)
Lemma A_11_Heap_Object_Safety_3_Corollary :
  forall (h : H) (u : Upsilon) (g : Gamma) 
         (x : EVar) (p2 : P) (t1 t2 : Tau)
         (v1 v2 vhx : E),
    Value v1 ->
    Value v2 ->
    refp h u ->
    htyp u g h g ->
    getH h x = Some v1 ->
    get vhx [] v1 ->
    rtyp [] u g v1 t1 ->
    gettype u x [] t1 p2 = Some t2 ->
    (exists (v2 : E),
       get vhx ([] ++ p2) v2 /\ 
       rtyp [] u g v2 t2) /\
    (forall (v2' : E),
       Value v2' ->
       (exists (v1' : E),
          Value v1' ->
          set v1 p2 v2' v1')).
Proof.
  (* Prove using A_11_Heap_Object_Safety_3 *)
Admitted.
  
Inductive extends_Gamma : Gamma -> Gamma -> Prop := 
  | A_12_Extension_Gamma : 
      forall (g1 g2 : Gamma),
        (exists (g3 : Gamma), g2 = g1 ++ g3) ->
        extends_Gamma g2 g1.

Inductive extends_Upsilon : Upsilon -> Upsilon -> Prop := 
  | A_12_Extension_Upsilon : 
      forall (u1 u2 : Upsilon),
        (exists (g3 : Upsilon), u2 = u1 ++ g3) ->
        extends_Upsilon u2 u1.

Lemma A_13_Term_Preservation_1:
  forall (u : Upsilon) (g : Gamma) 
         (e e' : E) (tau : Tau) (h h' : H),
    htyp u g h g ->
    refp h u -> 
    ltyp [] u g e tau -> 
    L h (e_s e)  h' (e_s e') ->
     exists (g' : Gamma) (u' : Upsilon),
       (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
       htyp u' g' h' g' /\
       refp h' u' /\
       ltyp [] u' g' e' tau.
Proof.
  intros u g e e' tau h h'.
  intros htypder refpder ltypder.
  (* TODO am I proving the right theorem? e_s e not here. *)
  apply (SLR_ind_mutual
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (rstep: R h s h' s') =>
              exists (g' : Gamma) (u' : Upsilon),
                (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                htyp u' g' h' g' /\
                refp h' u' /\
                ltyp [] u' g' e' tau)
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (sstep: S h s h' s') =>
              exists (g' : Gamma) (u' : Upsilon),
                (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                htyp u' g' h' g' /\
                refp h' u' /\
                ltyp [] u' g' e' tau)
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (lstep: L h s h' s') =>
              exists (g' : Gamma) (u' : Upsilon),
                (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                htyp u' g' h' g' /\
                refp h' u' /\
                ltyp [] u' g' e' tau)); crush.
  (* crush gives 19/41. *)
Admitted.

Lemma A_13_Term_Preservation_2:
  forall (u : Upsilon) (g : Gamma) (e e' : E) (tau : Tau) (h h' : H),
    htyp u g h g ->
    refp h u -> 
    rtyp [] u g e tau ->
    R h (e_s e)  h' (e_s e') ->
    exists (g' : Gamma) (u' : Upsilon),
      (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
      htyp u' g' h' g' /\ 
      refp h' u' /\
      rtyp [] u' g' e' tau.
Proof.
  intros u g e e' tau h h'.
  intros htypder refpder ltypder.
  apply (SLR_ind_mutual
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (rstep: R h s h' s') =>
              exists (g' : Gamma) (u' : Upsilon),
                (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                htyp u' g' h' g' /\
                refp h' u' /\
                rtyp [] u' g' e' tau)
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (sstep: S h s h' s') =>
              exists (g' : Gamma) (u' : Upsilon),
                (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                htyp u' g' h' g' /\
                refp h' u' /\
                rtyp [] u' g' e' tau)
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (lstep: L h s h' s') =>
              exists (g' : Gamma) (u' : Upsilon),
                (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                htyp u' g' h' g' /\
                refp h' u' /\
                rtyp [] u' g' e' tau)); crush.
  (* crush gets 19/41. *)
Admitted.

Lemma A_13_Term_Preservation_3:
  forall (u : Upsilon) (g : Gamma) (s s': St) (tau : Tau) (h h' : H),
    htyp u g h g ->
    refp h u -> 
    styp [] u g tau s -> 
    S h s  h' s' ->
    exists (g' : Gamma) (u' : Upsilon),
      (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
      htyp u' g' h' g' /\ 
      refp h' u' /\
      styp [] u' g' tau s'.
Proof.
  intros u g e e' tau h h'.
  intros htypder refpder ltypder.
  apply (SLR_ind_mutual
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (rstep: R h s h' s') =>
              exists (g' : Gamma) (u' : Upsilon),
                (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                htyp u' g' h' g' /\
                refp h' u' /\
                styp [] u' g' tau e')
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (sstep: S h s h' s') =>
              exists (g' : Gamma) (u' : Upsilon),
                (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                htyp u' g' h' g' /\
                refp h' u' /\
                styp [] u' g' tau e')
           (fun (h : H) (s : St) (h' : H) (s' : St) 
                (lstep: L h s h' s') =>
              exists (g' : Gamma) (u' : Upsilon),
                (extends_Gamma  g g' /\ extends_Upsilon  u u') -> 
                htyp u' g' h' g' /\
                refp h' u' /\
                styp [] u' g' tau e')); crush.
  (* crush gives 19/41. *)
Admitted.

Lemma A_14_Term_Progress_1:
  forall (g : Gamma) (u : Upsilon) (h : H) (e : E) (tau : Tau),
    htyp u g h g -> 
    refp h u ->
    ltyp [] u g e tau -> 
    (exists (x : EVar) (p : P), e = (p_e x p)) \/ 
    (exists (h' : H) (e' : E),  L h (e_s e) h' (e_s e')).

Proof.
  intros g u h e tau.
  intros htypder refpder.
  apply (typ_ind_mutual 
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              (exists (x : EVar) (p : P), e = (p_e x p)) \/ 
              (exists (h' : H) (e' : E),  L h (e_s e) h' (e_s e')))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
                (lt : ltyp d u g  e tau') =>
              (exists (x : EVar) (p : P), e = (p_e x p)) \/ 
              (exists (h' : H) (e' : E),  L h (e_s e) h' (e_s e')))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              (exists (x : EVar) (p : P), e = (p_e x p)) \/ 
              (exists (h' : H) (e' : E),  L h (e_s e) h' (e_s e')))).
  (* crush goes up many goals here. *)
Admitted.

Lemma A_14_Term_Progress_2:
  forall (g : Gamma) (u : Upsilon) (h : H) (e : E) (tau : Tau),
    htyp u g h g -> 
    refp h u ->
    rtyp [] u g e tau -> 
    (Value e \/
     exists (h' : H) (e' : E),  R h (e_s e) h' (e_s e')).
Proof.
  intros g u h e tau.
  intros htypder refpder.
  apply (typ_ind_mutual 
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              (Value e \/
               exists (h' : H) (e' : E),  R h (e_s e) h' (e_s e')))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
                (lt : ltyp d u g  e tau') =>
              (Value e \/
               exists (h' : H) (e' : E),  R h (e_s e) h' (e_s e')))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              (Value e \/
               exists (h' : H) (e' : E),  R h (e_s e) h' (e_s e')))).
  (* crush goes up many goals here. *)
Admitted.

(* TODO can't get this formulated right due to the statement that only
    appears in s types.
   I'm just not sure that I'm proving the inductive hypotheses right
   in the L/R cases by weakening them. 
 Dan? *)

Lemma A_14_Term_Progress_3:
  forall (g : Gamma) (u : Upsilon) (h : H) (s : St) (tau : Tau),
    htyp u g h g ->
    refp h u ->
    styp [] u g tau s -> 
     (exists (v : E), Value v /\ (s = (e_s v) \/ s = retn v)) \/
     (exists (h' : H) (s' : St), S h s h' s').
Proof.
  intros g u h e tau.
  intros htypder refpder.
  apply (typ_ind_mutual 
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (t : Tau) (s : St)
                (st : styp d u g t s) => 
              (exists (v : E), Value v /\ (s = (e_s v) \/ s = retn v)) \/
              (exists (h' : H) (s' : St), S h s h' s'))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (tau' : Tau) 
                (lt : ltyp d u g  e tau') =>
              (exists (h' : H) (s' : St), S h (e_s e) h' s'))
           (fun (d : Delta) (u : Upsilon) (g : Gamma) (e : E) (t : Tau) 
                (rt : rtyp d u g e t) =>
              (exists (h' : H) (s' : St), S h (e_s e) h' s'))).
  (* crush goes up many goals here. *)
Admitted.

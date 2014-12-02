(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  This defines case auxiliary checks so if I change any definitions then
 if their cases get changed, I'll get notifications.

*)

Require Export Case.


Tactic Notation "ltyp_ind_mutual_cases" tactic(first) ident(c) :=
  first;
[
  Case_aux c "styp_e_3_1"
 | Case_aux c "styp_return_3_2"
 | Case_aux c "styp_seq_3_3"
 | Case_aux c "styp_while_3_4"
 | Case_aux c "styp_if_3_5"
 | Case_aux c "styp_let_3_6"
 | Case_aux c "styp_open_3_7"
 | Case_aux c "styp_openstar_3_8"
 | Case_aux c "SL_3_1"
 | Case_aux c "SL_3_2"
 | Case_aux c "SL_3_3"
 | Case_aux c "SL_3_4"
 | Case_aux c "SR_3_1"
 | Case_aux c "SR_3_2"
 | Case_aux c "SR_3_3"
 | Case_aux c "SR_3_4"
 | Case_aux c "SR_3_5"
 | Case_aux c "SR_3_6"
 | Case_aux c "SR_3_7"
 | Case_aux c "SR_3_8"
 | Case_aux c "SR_3_9"
 | Case_aux c "SR_3_10"
 | Case_aux c "SR_3_11"
 | Case_aux c "SR_3_12"
 | Case_aux c "SR_3_13"
 | Case_aux c "SR_3_14"
 | Case_aux c "?"].
 

Tactic Notation "rtyp_ind_mutual_cases" tactic(first) ident(c) :=
  first;
[  Case_aux c "styp_e_3_1"
 | Case_aux c "styp_return_3_2"
 | Case_aux c "styp_seq_3_3"
 | Case_aux c "styp_while_3_4"
 | Case_aux c "styp_if_3_5"
 | Case_aux c "styp_let_3_6"
 | Case_aux c "styp_open_3_7"
 | Case_aux c "styp_openstar_3_8"
 | Case_aux c "SL_3_1"
 | Case_aux c "SL_3_2"
 | Case_aux c "SL_3_3"
 | Case_aux c "SL_3_4"
 | Case_aux c "SR_3_1"
 | Case_aux c "SR_3_2"
 | Case_aux c "SR_3_3"
 | Case_aux c "SR_3_4"
 | Case_aux c "SR_3_5"
 | Case_aux c "SR_3_6"
 | Case_aux c "SR_3_7"
 | Case_aux c "SR_3_8"
 | Case_aux c "SR_3_9"
 | Case_aux c "SR_3_10"
 | Case_aux c "SR_3_11"
 | Case_aux c "SR_3_12"
 | Case_aux c "SR_3_13"
 | Case_aux c "SR_3_14"
 | Case_aux c "?" ].

Tactic Notation "styp_ind_mutual_cases" tactic(first) ident(c) :=
  first;
[ 
  Case_aux c "styp_e_3_1"
 | Case_aux c "styp_return_3_2"
 | Case_aux c "styp_seq_3_3"
 | Case_aux c "styp_while_3_4"
 | Case_aux c "styp_if_3_5"
 | Case_aux c "styp_let_3_6"
 | Case_aux c "styp_open_3_7"
 | Case_aux c "styp_openstar_3_8"
 | Case_aux c "SL_3_1"
 | Case_aux c "SL_3_2"
 | Case_aux c "SL_3_3"
 | Case_aux c "SL_3_4"
 | Case_aux c "SR_3_1"
 | Case_aux c "SR_3_2"
 | Case_aux c "SR_3_3"
 | Case_aux c "SR_3_4"
 | Case_aux c "SR_3_5"
 | Case_aux c "SR_3_6"
 | Case_aux c "SR_3_7"
 | Case_aux c "SR_3_8"
 | Case_aux c "SR_3_9"
 | Case_aux c "SR_3_10"
 | Case_aux c "SR_3_11"
 | Case_aux c "SR_3_12"
 | Case_aux c "SR_3_13"
 | Case_aux c "SR_3_14"
 | Case_aux c "?" ].
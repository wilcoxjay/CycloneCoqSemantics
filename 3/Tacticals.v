(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

 This defines some early attempts at tacticals for the dynamic
  semantics. 

*)
 
Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Require Export FormalSyntax.
Require Export DynamicSemanticsTypeSubstitution.
Require Export DynamicSemanticsHeapObjects.
Require Export DynamicSemantics.
Require Export StaticSemanticsKindingAndContextWellFormedness.
Require Export StaticSemantics.

Create HintDb Chapter3.
Hint Constructors Value     : Chapter3.
Hint Constructors S         : Chapter3.
Hint Constructors R         : Chapter3.
Hint Constructors L         : Chapter3.
Hint Constructors get       : Chapter3.
Hint Constructors set       : Chapter3.
(* Hint Constructors gettype   : Chapter3. *)
Hint Constructors ret       : Chapter3.
Hint Constructors styp      : Chapter3.
Hint Constructors ltyp      : Chapter3.
Hint Constructors rtyp      : Chapter3.
Hint Constructors htyp      : Chapter3.
Hint Constructors refp      : Chapter3.
Hint Constructors prog      : Chapter3.
Hint Constructors K         : Chapter3.
Hint Constructors AK        : Chapter3.
Hint Constructors ASGN      : Chapter3.
Hint Constructors WFDG      : Chapter3.
Hint Constructors WFU       : Chapter3.
Hint Constructors WFC       : Chapter3.
Hint Extern 4 => discriminate : Chapter3. (* For ifs. *)

(* Getting eauto to evaluate functions requires some of this. *)
Hint Extern 0 (gettype _ _ _ _ _ = Some _) => try reflexivity : Chapter3.
Hint Extern 0 ((getH _ _) = Some _) => try reflexivity : Chapter3.
Hint Extern 0 ((setH _ _) = _) => try reflexivity : Chapter3.
Hint Extern 0 ((deleteH _ _) = _) => try reflexivity : Chapter3.

Hint Extern 0 ((getD _ _) = Some _) => try reflexivity : Chapter3.
Hint Extern 0 ((getG _ _) = Some _) => try reflexivity : Chapter3. 
Hint Extern 0 ((getU _ _) = Some _) => try reflexivity : Chapter3.

(* A lot of the judgements just iterate through their contexts,
 popping off elements on the right. To make eauto work in these
 cases we break a single element off the right of the list. *)

Ltac right_list_recurse_gamma m :=
  rewrite app_removelast_last with (l:= m) (d:=(evar(1000),cint));
  try simpl removelast;
  try simpl last;
  try discriminate.

Ltac right_list_recurse_delta m :=
  rewrite app_removelast_last with (l:= m) (d:=(tvar(1000),A));
  try simpl removelast;
  try simpl last;
  try discriminate.
 
Ltac right_list_recurse_upsilon m :=
  rewrite app_removelast_last with (l:= m) (d:=((p_e (evar 1000) []),cint));
  try simpl removelast;
  try simpl last;
  try discriminate.

Ltac right_list_matcher :=
   match goal with
     | [ |- htyp _ _ _ (?x ++ ?l) ] => try eapply htyp_xv with (g':=x)
     | [ |- htyp _ _ _ ?l ]         => try right_list_recurse_gamma l

     | [ |- ASGN (?x ++ ?y) _ ]   => try constructor
     | [ |- ASGN ?x         _ ]   
       => try (right_list_recurse_delta x; constructor)

     | [ |- WFU (?x ++ ?y)      ]   => try constructor
     | [ |- WFU ?x              ]   
       => try (right_list_recurse_upsilon x; constructor)

     | [ |- WFDG _ (?x ++ ?y)   ]   => try constructor
     | [ |- WFDG _ ?x           ]   
       => try (right_list_recurse_gamma x; constructor)

     | [ |- K (?x ++ ?y) _ _ _   ]   => try constructor
     | [ |- K ?x _ _ _           ]   
       => try (right_list_recurse_gamma x; constructor)

     | [ |- refp _ (?x ++ ?y)   ]   => try constructor
     | [ |- refp _ ?x           ]   
       => try (right_list_recurse_upsilon x; constructor)
   end.

Hint Extern 3 (htyp _ _ _ _)   => right_list_matcher.
Hint Extern 3 (ASGN _  _)      => right_list_matcher.
Hint Extern 3 (WFU  _   )      => right_list_matcher.
Hint Extern 3 (WFDG _ _)       => right_list_matcher.
Hint Extern 3 (refp _ _)       => right_list_matcher.

Hint Extern 5 ([] ++ _ = _) => try reflexivity.
Hint Extern 5 (_ = [] + _)  => try reflexivity.

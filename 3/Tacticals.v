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
Require Export ContextExtensionRelation.

Create HintDb Chapter3.
Hint Constructors Value     : Chapter3.
Hint Constructors S         : Chapter3.
Hint Constructors R         : Chapter3.
Hint Constructors L         : Chapter3.
Hint Constructors get       : Chapter3.
Hint Constructors set       : Chapter3.
Hint Constructors getU      : Chapter3.
Hint Constructors gettype   : Chapter3.
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
Hint Constructors WFD       : Chapter3.
Hint Constructors ExtendedByD   : Chapter3.

Hint Extern 4 => discriminate : Chapter3. (* For ifs. *)

(* Getting eauto to evaluate functions requires some of this. *)
Hint Extern 0 ((getH _ _) = Some _) => try reflexivity : Chapter3.
Hint Extern 0 ((setH _ _) = _) => try reflexivity : Chapter3.
Hint Extern 0 ((deleteH _ _) = _) => try reflexivity : Chapter3.

Hint Extern 0 ((getD _ _) = Some _) => try reflexivity : Chapter3.
Hint Extern 0 ((getG _ _) = Some _) => try reflexivity : Chapter3. 
Hint Extern 0 (NotInDomU _ _ _) => try reflexivity : Chapter3.

(* Now the judgements work by popping of the left most element of their lists. *)

Lemma app_removefirst_first :
  forall (A : Type) (d : A) (l : list A),
    l <> nil -> l = [hd d l] ++ (tail l).
Proof.
Admitted.

Ltac left_list_recurse_gamma m :=
  rewrite app_removefirst_first with (l:= m) (d:=(evar(1000),cint));
  try simpl hd;
  try simpl tail;
  try discriminate.

Ltac left_list_recurse_delta m :=
  rewrite app_removefirst_first with (l:= m) (d:=(tvar(1000),A));
  try simpl hd;
  try simpl tail;
  try discriminate.
 
Ltac left_list_recurse_upsilon m :=
  rewrite app_removefirst_first with (l:= m) (d:= ( ((evar 1000), []), cint));
  try simpl hd;
  try simpl tail;
  try discriminate.

Ltac list_splitter :=
   match goal with
     | [ |- htyp _ _ _ (?x ++ ?l) ] => try eapply htyp_xv with (g':=x)
     | [ |- htyp _ _ _ ?l ]         => try left_list_recurse_gamma l

     | [ |- ASGN (?x ++ ?y) _ ]   => try constructor
     | [ |- ASGN ?x         _ ]   
       => try (left_list_recurse_delta x; constructor)

     | [ |- WFU (?x ++ ?y)      ]   => try constructor
     | [ |- WFU ?x              ]   
       => try (left_list_recurse_upsilon x; constructor)

     | [ |- WFDG _ (?x ++ ?y)   ]   => try constructor
     | [ |- WFDG _ ?x           ]   
       => try (left_list_recurse_gamma x; constructor)

     | [ |- WFD (?x ++ ?y)   ]   => try constructor
     | [ |- WFD ?x           ]   
       => try (left_list_recurse_delta x; constructor)

     | [ |- K (?x ++ ?y) _ _ _   ]   => try constructor
     | [ |- K ?x _ _ _           ]   
       => try (left_list_recurse_gamma x; constructor)

     | [ |- refp _ (?x ++ ?y)   ]   => try constructor
     | [ |- refp _ ?x           ]   
       => try (left_list_recurse_upsilon x; constructor)

     | [ |- getU (?x ++ ?y) _ _ _ ]   => try constructor
     | [ |- getU ?x _ _ _         ]   
       => try (left_list_recurse_upsilon x; constructor)

   end.

Hint Extern 3 (htyp _ _ _ _)   => list_splitter.
Hint Extern 3 (ASGN _  _)      => list_splitter.
Hint Extern 3 (WFU  _   )      => list_splitter.
Hint Extern 3 (WFDG _ _)       => list_splitter.
Hint Extern 3 (refp _ _)       => list_splitter.
Hint Extern 3 (getU _ _ _ _)   => list_splitter.

Hint Extern 5 ([] ++ _ = _) => try reflexivity.
Hint Extern 5 (_ = [] + _)  => try reflexivity.

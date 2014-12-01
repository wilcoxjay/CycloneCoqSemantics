(* 
 This is the definition of formal syntax for Dan Grossman's Thesis, 
  "SAFE PROGRAMMING AT THE C LEVEL OF ABSTRACTION". 

  Let's define partial functions as lists. 
  We have just too many unique domain constraints.
*)

Require Import List.
Export ListNotations.
Require Import ZArith.
Require Import Init.Datatypes.

Definition pfun (A : Type) (B : Type) := list (A * B).

(* TODO I could make this a relation and then check at each add that I am
  not overwriting the domain. *)
Function plusl (A : Type) (B : Type) (x : A*B) (p : pfun A B) : pfun A B := 
  x :: p.
Function plusr (A : Type) (B : Type) (p : pfun A B) (x : A * B) : pfun A B := 
  p ++ [x].
Function union (A : Type) (B : Type) 
         (p1 : pfun A B) (p2 : pfun A B) : pfun A B := 
  p1 ++ p2.

Notation "x |+ y" := (plusl x y)  
                       (at level 60, right associativity).
Notation "[ x |; .. |; y ]" := (cons x .. (cons y []) ..).
Notation "|[ ]" := [].
Notation "x |++ y" := (union x y)  
                       (at level 60, right associativity).
(* TODO Map or ? *)

Function Dom (A : Type) (B : Type) (p : pfun A B) : list A :=
  match p with
   | (a,b) :: p' => a :: Dom A B p'
   | |[] => |[]                      
  end.

Function notindom (A : Type) (B : Type) (a : A) (p : pfun A B) : Prop := 
  match a, p with
   | b, (b',_) :: p' => b = b'
   | _ , |[] => True
  end.

Inductive WFpfun : Type -> Type -> pfun Type Type  -> Prop :=
  | WFpfun_nil   : WFpfun _ _ |[]
  | WFpfun_plus : forall  (A : Type) (B : Type) (a : A * B) (p : pfun A B),
                    WFpfun (a |+ p).
  




(* How do I put an invarient in here? I don't think I can. *)


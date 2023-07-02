(* A Tutorial on Typeclasses in Coq *)
(* https://softwarefoundations.cis.upenn.edu/qc-current/Typeclasses.html *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From Coq.Strings Require Export String.

Local Open Scope string_scope.

(* ==== show ============================================ *)

Class Show A : Type := {
  show : A -> string
}.

#[export] Instance showBool : Show bool := {
  show := fun b: bool => if b then "true" else "false"
}.

Compute (show true).

Inductive primary := Red | Green | Blue.
#[export] Instance showPrimary : Show primary :=
  {
    show :=
      fun c:primary =>
        match c with
        | Red   => "Red"
        | Green => "Green"
        | Blue  => "Blue"
        end
  }.

Compute (show Green).

Definition showTwo {A B : Type}
           `{Show A} `{Show B} (a : A) (b : B) : string :=
  "First is " ++ show a ++ " and second is " ++ show b.
Compute (showTwo true 42).
Compute (showTwo Red Green).

#[export] Instance showPair {A B : Type} `{Show A} `{Show B} : Show (A * B) := {
  show p :=
    let (a,b) := p in
      "(" ++ show a ++ "," ++ show b ++ ")"
}.

Compute (show (true,false)).

(* we can also define typeclasses with Definition *)
Definition foo : Show := {
  show: 
}

(* ==== equality ======================================== *)

Class Eq A := {
  eqb : A -> A -> bool;
}.

Notation "x =? y" := (eqb x y) (at level 70).

#[export] Instance eqBool : Eq bool :=
  {
    eqb := fun (b c : bool) =>
       match b, c with
         | true, true => true
         | true, false => false
         | false, true => false
         | false, false => true
       end
  }.

#[export] Instance eqNat : Eq nat :=
  {
    eqb := Nat.eqb
  }.


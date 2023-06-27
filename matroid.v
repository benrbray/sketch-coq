(*
  Matroids and Greedy Algorithms
  Benjamin R. Bray (benrbray@gmail.com)
  2021-07-19
*)

Set Printing Parentheses.
From Coq Require Import Strings.String.  (* for manual grading *)
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
From Coq Require Export Reals.Reals.
From Coq Require Export Logic.Eqdep.
Export ListNotations.
From Coq Require Export Permutation.

(* ====================================================== *)
(* ====================================================== *)
Module Matroid.

(* ground set *)
Parameter U : Set.

Record Matroid : Type := mkMatroid
  { ground    : Set
  ; indep     : (ground -> Prop) -> Prop
  ; empty     : (ground -> Prop)
  ; subset    : (ground -> Prop) -> (ground -> Prop) -> Prop 
  ; M_0_indep : indep empty
  ; M_subset_indep : forall A B, indep A -> subset B A -> indep B
  }.

Record exrec : Type := mkRec
  { a : nat ; b : nat }.

(* ====================================================== *)
(* ====================================================== *)
Module Vect.

(*
  Adapted from Magaud 2014,
  "Programming with Dependent Types in Coq:
     A Study of Square Matrices"
  https://hal.inria.fr/hal-00955444/document
*)

(* length-indexed vector *)
Inductive vect (A : Set) : nat -> Set :=
  | vnil : vect A 0
  | vcons : forall n : nat, A -> vect A n -> vect A (S n).

Arguments vect {A}.

Check existT.

Check eq_dep.

Theorem vect_len_0_nil : forall A (v : @vect A 0),
  v = vnil A.
Proof.
  intros A v. injection. 


End Vect.
(* ====================================================== *)
(* ====================================================== *)
Module VectMat.



Definition vec : Type := 

Definition VectorMatroid : exrec := {| a:= 6; b:= 10 |}.

Print VectorMatroid.

End VectMat.
(* ====================================================== *)
(* ====================================================== *)




(* subsets are functions *)
Definition subset : U -> Prop.

End Matroid.
(* ====================================================== *)
(* ====================================================== *)
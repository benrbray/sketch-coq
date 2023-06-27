(* Moggi 1991, "Notions of Computation and Monads" *)
(* https://www.cs.cmu.edu/~crary/819-f09/Moggi91.pdf *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.

From Coq.Strings Require Export String.
From Coq.Lists Require Export List.
From Coq.Arith Require Export Peano_dec.

(* ====================================================== *)
(* ====================================================== *)
Module MultiSortedMonadic.


(* ---- parameters to the equational theory ------------- *)

Parameter A       : Type.       (* base types             *)
Parameter FnSym   : Type.       (* function symbols       *)
Parameter FnArgTy : FnSym -> A. (* function argument type *)
Parameter FnResTy : FnSym -> A. (* function result type   *)

(* ---- syntax ------------------------------------------ *)

Definition var := string.        (* variables         *)
Definition var_eq := string_dec. (* variable equality *)

(* unary function symbols *)
Inductive func : Type :=
  | func_unary : A -> A -> func.

(* the only types are base types *)
Inductive typ : Type :=
  | typ_base : A -> typ.

(* monadic context (x : A) |- ... contains exactly one variable*)
Definition ctx : Type := var * typ.

(* terms in the metalanguage *)
Inductive tm : Type :=
  | tm_var : var -> tm         (* variable             *)
  | tm_fap : FnSym -> tm -> tm (* function application *)
  | tm_eqn : forall (A : typ), (* equation             *)
      tm -> tm -> typ -> tm.

(* ---- function signatures ----------------------------- *)

(* function f has signature A1 -> A2 *)
Reserved Notation "f : A1 --> A2" (no associativity, at level 90).

Inductive has_sig : FnSym -> typ -> typ -> Prop :=
  | Fsig : forall (f : FnSym),
      f : (typ_base (FnArgTy f)) --> (typ_base (FnResTy f))
  where "f : A1 --> A2" := (has_sig f A1 A2).

(* ---- type judgements --------------------------------- *)

(* term e has type t in single-variable context (x:A) *)
Reserved Notation "x : t1 |- e : t2" (no associativity, at level 90, e at next level).

(* term has type in a (single-variable) context *)
Inductive has_type : ctx -> tm -> typ -> Prop :=
  | TVar : forall (x : var) (A : typ),
    x : A |- (tm_var x) : A
  | TFap : forall (x : var) (e : tm) (A1 A2 : typ) (f : FnSym),
    (f : A1 --> A2) ->
    (x : A1 |- (tm_fap f (tm_var x)) : A2)
  where "x : t1 |- e : t2" := (has_type (x,t1) e t2).

(* ---- type equality ----------------------------------- *)

(* term e has type t in single-variable context (x:A) *)
Reserved Notation "x : t1 |- e1 =[ t2 ]= e2" (no associativity, at level 90, e1 at next level, e2 at next level).

(* describes when an equality term is well-typed *)
Inductive eq_well_typed : ctx -> typ ->tm -> tm -> Prop :=
  | EqTm : forall (x: var) (e1 e2 : tm) (A1 A2 : typ),
    (x : A1 |- e1 : A2) ->
    (x : A1 |- e2 : A2) ->
    (x : A1 |- e1 =[ A2 ]= e2)
  where "x : t1 |- e1 =[ t2 ]= e2" := (eq_tm (x,t1) t2 e1 e2).

(* ====================================================== *)

End MultiSortedMonadic.
(* ====================================================== *)
(* ====================================================== *)
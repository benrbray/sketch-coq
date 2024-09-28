Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.

From HindleyMilner Require Import Maps.

(* ====================================================== *)
Module Unify.

Parameter K : Type. (* group generators *)

(* variable sorts *)
Notation var_gr := string. (* group variable *)
Notation var_tm := string. (* term variable  *)
Notation var_ty := string. (* type variable  *)

Inductive stmt : Type :=
  | stmt_valid : stmt
  | stmt_and   : stmt -> stmt -> stmt
  | stmt_eq    : stmt.

(* group expression *)
Inductive expr : Type :=
  | expr_var   : var_gr -> expr
  | expr_const : K -> expr
  | expr_zero  : expr
  | expr_plus  : expr -> expr -> expr
  | expr_neg   : expr -> expr.

Inductive eq_expr : expr -> expr -> Prop :=
  | eq_expr_symm  : forall a b, eq_expr a b -> eq_expr b a
  | eq_expr_trans : forall a b c, eq_expr a b -> eq_expr b c -> eq_expr a c
  | eq_expr_gr    : forall a b c 
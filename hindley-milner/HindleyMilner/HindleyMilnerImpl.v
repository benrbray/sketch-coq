Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.

From HindleyMilner Require Import Maps.

(* ====================================================== *)

Inductive tp : Type :=
  | tp_mvar : nat -> tp  (* metavariable *)
  | tp_tvar : nat -> tp  (* type variable -- bound by forall *)
  | tp_arrow : tp -> tp. (* function type *)

(* "type scheme" -- locally nameless representation where *)
(* bound variables have de bruijn indices, while free     *)
(* variables (those bound in the context) have names      *) 
Inductive scheme : Type :=
  | sch_tp     : tp -> scheme
  | sch_forall : scheme -> scheme.


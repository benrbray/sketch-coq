Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.

From HindleyMilner Require Import Maps.

(* ====================================================== *)

(* terms *)
Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_abs : string -> tm -> tm
  | tm_app : tm -> tm -> tm
  | tm_let : string -> tm -> tm -> tm.

(* types *)
Inductive tp : Type :=
  | tp_var   : string -> tp
  | tp_arrow : tp -> tp -> tp.

(* type schemes *)
Inductive scheme : Type :=
  | sc_type   : tp -> scheme
  | sc_forall : string -> scheme.


(* ====================================================== *)

Declare Custom Entry hindley_milner.
Notation "<{ e }>" := e (e custom hindley_milner at level 99).
Notation "( x )" := x (in custom hindley_milner, x at level 99).
Notation "x" := x (in custom hindley_milner at level 0, x constr at level 0).
Notation "S -> T" := (tp_arrow S T) (in custom hindley_milner at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom hindley_milner at level 1, left associativity).
Notation "\ x , y" :=
  (tm_abs x y) (in custom hindley_milner at level 90,
                x at level 99,
                y custom hindley_milner at level 99,
                left associativity).
Coercion tm_var : string >-> tm.
Notation "'let' x ':=' s 'in' t" :=
  (tm_let x s t) (in custom hindley_milner at level 89,
                  x custom hindley_milner at level 99,
                  s custom hindley_milner at level 99,
                  t custom hindley_milner at level 99,
                  left associativity).

(* shorthand for variables *)
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

(* term t has type scheme s under assumptions A *)
Example term_example_1 :=
  <{ let x := \y, y in x x }>.

(* ====================================================== *)

Inductive ctx : Type :=
  | ctx_empty         : ctx
  | ctx_metavar_intro : ctx -> string -> ctx            (* C, a:*      *)
  | ctx_metavar_dfn   : ctx -> string -> tp -> ctx      (* C, a := t:* *)
  | ctx_var_annotate  : ctx -> string -> scheme -> ctx  (* C, x:s      *)
  | ctx_locality      : ctx -> ctx.                     (* C ;         *)

(* a context C is valid provided that
     > each variable is distinct
     > each property is well-formed for the preceeding context *)
(* Inductive ctx_valid : ctx -> Prop :=
  |   *)
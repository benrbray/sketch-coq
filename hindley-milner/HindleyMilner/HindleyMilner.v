Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.

From HindleyMilner Require Import Maps.

(* ====================================================== *)

(* term vars    x,y                                       *)
(* type vars    α,β                                       *)
(* terms        t,s ::= x | λx.t | s t | let x = s in t   *)
(* types        τ,υ ::= α | τ → υ                         *)
(* scheme       σ ::= τ | ∀α. σ                           *)

Notation var_tm := string.
Notation var_tp := string.

(* term *)
Inductive tm : Type :=
  | tm_var : var_tm -> tm
  | tm_abs : var_tm -> tm -> tm
  | tm_app : tm -> tm -> tm
  | tm_let : var_tm -> tm -> tm -> tm.

(* type *)
Inductive tp : Type :=
  | tp_var   : var_tp -> tp
  | tp_arrow : tp -> tp -> tp.

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

(* ====================================================== *)

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

(* "ordinal n" represents an integer 0 <= x < n *)
Record ordinal n := {
  val :> nat;
  _ : val < n;
}.

(* a TYPE SCHEME is a type wrapped in one *)
(* or more universally-quantified variables *)
Inductive scheme : Type :=
  | sch_metavar : nat -> scheme            (* mention metavariable *)
  | sch_type    : tp  -> scheme            (* type *)
  | sch_forall  : nat -> scheme -> scheme. (* universal quantification *)

(* ctx m n = context with        *)
(*   m metavariables and         *)
(*   n term variables            *)
Inductive ctx : nat -> nat -> Type :=
  | ctx_empty :
      ctx 0 0
  | ctx_metavar_intro {m n : nat} :
      (* extend ctx with additional metavar *)
      ctx m n -> ctx (m+1) n
  | ctx_metavar_dfn {m n : nat} :
      (* extend ctx with metavar, defined equal to some type *)
      ctx m n -> tp -> ctx (m+1) n
  | ctx_var_annotate {m n : nat}:
      (* extend ctx with term-level var *)
      ctx m n -> scheme -> ctx m (n+1).

Definition metavar {m n : nat} (G: ctx m n) := ordinal m.

(* ==== valid scheme ==================================== *)

(* valid_scheme notation *)
Reserved Notation "G ⊢s t" (no associativity, at level 90, t at next level).

Inductive valid_scheme {m n : nat} (G : ctx m n): scheme -> Prop :=
  | valid_sch_metavar {x : metavar G} :
      G ⊢s (sch_metavar x)
  | valid_sch_arrow : forall (a b : tp),
      G ⊢s (sch_type a) ->
      G ⊢s (sch_type b) ->
      G ⊢s (sch_type (tp_arrow a b))
  | valid_sch_forall : forall (x : scheme),
      (ctx_metavar_intro G) ⊢s x ->
      G ⊢s (sch_forall m x)
  where "G ⊢s x" := (valid_scheme G x).

(*Inductive ctx : Type :=
  | ctx_empty         : ctx
  | ctx_metavar_intro : ctx -> string -> ctx            (* C, a:*      *)
  | ctx_metavar_dfn   : ctx -> string -> tp -> ctx      (* C, a := t:* *)
  | ctx_var_annotate  : ctx -> string -> scheme -> ctx  (* C, x:s      *)
  | ctx_locality      : ctx -> ctx.                     (* C ;         *) *)

(* a context C is valid provided that
     > each variable is distinct
     > each property is well-formed for the preceeding context *)

(* ==== statements in context =========================== *)

(* STATEMENT: an assertion which can be judged in context.*)
(* Gundry's "sanity conditions" are passed as evidence to *)
(* each constructor, and can be recovered by inversion.   *)

Inductive stmt : Type :=
  | stmt_ctx_wf    : stmt                       (* well-formed context *)
  | stmt_scheme_wf : scheme -> stmt             (* well-formed type scheme *)
  | stmt_tp_eq     : tp -> tp -> stmt           (* type equivalence *)
  | stmt_tm_wt     : tm -> tp -> stmt           (* well-typed term *)
  | stmt_scheme_inst : scheme -> scheme -> stmt (* generic instantiation of type schemes *)
  | stmt_conj      : stmt -> stmt -> stmt.      (* conjunction of statements *)

Inductive ctx_wf : ctx -> Prop :=
  | ctx_wf_empty : ctx_wf ctx_empty
  | .
(* Moggi 1991, "Notions of Computation and Monads" *)
(* https://www.cs.cmu.edu/~crary/819-f09/Moggi91.pdf *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.

From Coq.Strings Require Export String.
From Coq.Lists Require Export List.
From Coq.Arith Require Export Peano_dec.

Require Import Category.Theory.
Require Import Category.Lib.

(* ====================================================== *)
(* ====================================================== *)
Module MultiSortedMonadic.

(* ---- parameters to the equational theory ------------- *)

Parameter A       : Type.       (* base types             *)
Parameter FnSym   : Type.       (* function symbols       *)
Parameter FnArgTy : FnSym -> A. (* function argument type *)
Parameter FnResTy : FnSym -> A. (* function result type   *)


(* ---- syntax ------------------------------------------ *)

Definition var : Type := Coq.Init.Datatypes.unit. (* variable (no names!) *)
Definition var_eq := string_dec.                  (* variable equality    *)

(* the only types are base types *)
Inductive typ : Type :=
  | typ_base : A -> typ.

(* function f has signature A1 -> A2 *)
Inductive has_sig : FnSym -> typ -> typ -> Prop :=
  | Fsig : forall (f : FnSym),
      has_sig f (typ_base (FnArgTy f)) (typ_base (FnResTy f)).

(* monadic context (x : A) |- ... contains exactly one variable*)
Definition ctx : Type := var * typ.

(* terms in the metalanguage *)
Inductive tm : Type :=
  | tm_var : tm                                 (* unnamed variable     *)
  | tm_fap : forall {A1 A2 : typ} {f : FnSym}, (* function application *)
      (has_sig f A1 A2) -> tm -> tm.

(* TODO: should equations really be part of the term language? *)

(* ---- type judgements --------------------------------- *)

(* term e has type t2 in single-variable context (x : t1) *)
Reserved Notation "x : t1 |- e : t2" (no associativity, at level 90, e at next level).

(* term has type in a (single-variable) context *)
Inductive has_type : ctx -> tm -> typ -> Prop :=
  | TVar : forall (x : var) (A : typ),
    x : A |- tm_var : A
  | TFap : forall {A0 A1 A2 : typ} {f : FnSym} (fsig : has_sig f A1 A2) (x : var) (e : tm),
    (x : A0 |- e : A1) ->
    (x : A0 |- (tm_fap fsig e) : A2)
  where "x : t1 |- e : t2" := (has_type (x,t1) e t2).

(* ---- substitution ------------------------------------ *)

(* replace the free variable in e2 with e1 *)
Fixpoint subst (e1 e2 : tm) :=
  match e2 with
  | tm_var => e1
  | tm_fap f e => tm_fap f (subst e1 e)
  (* | tm_eqn t e2a e2b => tm_eqn t (subst e1 e2a) (subst e1 e2b) *)
  end.

Theorem subst_has_type:
  forall (x : var) (t0 t1 t2 : typ) (e1 e2 : tm),
    (x : t0 |- e1 : t1) /\
    (x : t1 |- e2 : t2) ->
    (x : t0 |- (subst e1 e2) : t2).
Proof.
  intros.
  generalize dependent t2.
  induction e2.
  - (* tm_var *)
    simpl. intros t2 H.
    inversion H. inversion H1.
    rewrite H2 in H0.
    assumption.
  - (* tm_fap *)
    intros t2 H.
    simpl.
    inversion H. 
    inversion H1. subst.
    specialize (IHe2 A1).
    apply TFap.
    apply IHe2.
    split; assumption.
Qed.

(* ---- type equality ----------------------------------- *)

(* terms e1 and e2 of type t2 are equivalent *)
(* in single-variable context (x : t1)       *)
Reserved Notation "x : t1 |- e1 =[ t2 ]= e2" (no associativity, at level 90, e1 at next level, e2 at next level).

(* describes when an equality term is well-typed *)
(* Inductive eq_term_well_typed : ctx -> typ ->tm -> tm -> Prop :=
  | EqTm : forall (x: var) (e1 e2 : tm) (A1 A2 : typ),
    (x : A1 |- e1 : A2) ->
    (x : A1 |- e2 : A2) ->
    (x : A1 |- e1 =[ A2 ]= e2)
  where "x : t1 |- e1 =[ t2 ]= e2" := (eq_well_typed (x,t1) t2 e1 e2). *)

(* equivalence relation on terms *)
Inductive eq_term : ctx -> typ -> tm -> tm -> Prop :=
  | EqTm_Refl : forall (x : var) (e : tm) (A1 A2 : typ),
      (x : A1 |- e : A2) ->
      (x : A1 |- e =[ A2 ]= e)
  | EqTm_Symm : forall (x : var) (e1 e2 : tm) (A1 A2 : typ),
      (x : A1 |- e1 =[ A2 ]= e2) ->
      (x : A1 |- e2 =[ A2 ]= e1)
  | EqTm_Trans : forall (x : var) (e1 e2 e3 : tm) (A1 A2 : typ),
      (x : A1 |- e1 =[ A2 ]= e2) ->
      (x : A1 |- e2 =[ A2 ]= e3) ->
      (x : A1 |- e1 =[ A2 ]= e3)
  | EqTm_Congr : forall (x : var) (e1 e2 e3 : tm) (A1 A2 A3 : typ) (f : FnSym)
      (fsig : has_sig f A2 A3),
      (x : A1 |-              e1  =[ A2 ]=           e2) ->
      (x : A1 |- (tm_fap fsig e1) =[ A3 ]= (tm_fap fsig e2))
  where "x : t1 |- e1 =[ t2 ]= e2" := (eq_term (x,t1) t2 e1 e2).

(* TODO: passing around fsig is cumbersome, is there a better term representation? *)

(* ====================================================== *)

(* a term, along with a proof of a typing judgement *)
(* x : A1 |- *)
Inductive typed_tm : typ -> typ -> Type :=
  | TypedTm : forall {A1 A2 : typ} (e : tm), (tt : A1 |- e : A2) -> typed_tm A1 A2.

Check Reflexive.

(* setoid for terms, based on eq_term *)
#[refine] #[export]
Instance tm_setoid {A1 A2} : Setoid (typed_tm A1 A2) := {
  equiv :=
    (fun t1 t2 => 
      match (t1, t2) with
      | (TypedTm e1 _, TypedTm e2 _) => eq_term (tt, A1) A2 e1 e2
      end);
}.
Proof.
  constructor.
  - (* Reflexive *) unfold Reflexive. simpl.
  - (* Symmetric *)
  - (* Transitive *)

Next Obligation.

(* ====================================================== *)



Program Definition Interp : Category := {|
  obj := typ ;
  hom (A B : typ) := tm ;
|}.
Next Obligation.

End MultiSortedMonadic.
(* ====================================================== *)
(* ====================================================== *)
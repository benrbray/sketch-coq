(* Adam Chlipala,
   "Certified Programming with Dependent Types"
   http://adam.chlipala.net/cpdt/html/Firstorder.html *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".

From Coq.Strings Require Export String.
From Coq.Lists Require Export List.
From Coq.Arith Require Export Peano_dec.

Require Import Cpdt.CpdtTactics.
(* ====================================================== *)
Module Concrete.

Definition var := string.
Definition var_eq := string_dec.

Inductive exp : Set :=
| Const : bool -> exp
| Var : var -> exp
| App : exp -> exp -> exp
| Abs : var -> exp -> exp.

Inductive type : Set :=
| Bool : type
| Arrow : type -> type -> type.

Infix "-->" := Arrow (right associativity, at level 60).

Definition ctx := list (var * type).

Reserved Notation "G |-v x : t" (no associativity, at level 90, x at next level).

Inductive lookup : ctx -> var -> type -> Prop :=
| First : forall x t G,
  (x, t) :: G |-v x : t
| Next : forall x t x' t' G,
  x <> x'
  -> G |-v x : t
  -> (x', t') :: G |-v x : t
  where "G |-v x : t" := (lookup G x t).

#[local] Hint Constructors lookup : core.

Reserved Notation "G |-e e : t" (no associativity, at level 90, e at next level).

Inductive hasType : ctx -> exp -> type -> Prop :=
| TConst : forall G b,
  G |-e Const b : Bool
| TVar : forall G v t,
  G |-v v : t
  -> G |-e Var v : t
| TApp : forall G e1 e2 dom ran,
  G |-e e1 : dom --> ran
  -> G |-e e2 : dom
  -> G |-e App e1 e2 : ran
| TAbs : forall G x e' dom ran,
  (x, dom) :: G |-e e' : ran
  -> G |-e Abs x e' : dom --> ran

  where "G |-e e : t" := (hasType G e t).

#[local] Hint Constructors hasType : core.

Lemma weaken_lookup : forall x t G' G1,
           G1 |-v x : t
  -> G1 ++ G' |-v x : t.
  induction G1 as [ | [? ?] ? ]; crush;
    match goal with
      | [ H : _ |-v _ : _ |- _ ] => inversion H; crush
    end.
Qed.

#[local] Hint Resolve weaken_lookup : core.

Theorem weaken_hasType' : forall G' G e t,
  G |-e e : t
  -> G ++ G' |-e e : t.
  induction 1; crush; eauto.
Qed.

Theorem weaken_hasType : forall e t,
  nil |-e e : t
  -> forall G', G' |-e e : t.
  intros; change G' with (nil ++ G');
    eapply weaken_hasType'; eauto.
Qed.

#[local] Hint Resolve weaken_hasType : core.

Section subst.
  Variable x : var.
  Variable e1 : exp.

  Fixpoint subst (e2 : exp) : exp :=
    match e2 with
      | Const _ => e2
      | Var x' => if var_eq x' x then e1 else e2
      | App e1 e2 => App (subst e1) (subst e2)
      | Abs x' e' => Abs x' (if var_eq x' x then e' else subst e')
    end.
  
  Variable xt : type.
  Hypothesis Ht' : nil |-e e1 : xt.

  Notation "x # G" := (forall t' : type, In (x, t') G -> False) (no associativity, at level 90).

  Lemma subst_lookup' : forall x' t,
    x <> x'
    -> forall G1, G1 ++ (x, xt) :: nil |-v x' : t
      -> G1 |-v x' : t.
    induction G1 as [ | [? ?] ? ]; crush;
      match goal with
        | [ H : _ |-v _ : _ |- _ ] => inversion H
      end; crush.
  Qed.

  #[local] Hint Resolve subst_lookup' : core.

  Lemma subst_lookup : forall x' t G1,
    x' # G1
    -> G1 ++ (x, xt) :: nil |-v x' : t
    -> t = xt.
    induction G1 as [ | [? ?] ? ]; crush; eauto;
      match goal with
        | [ H : _ |-v _ : _ |- _ ] => inversion H
      end; crush; (elimtype False; eauto;
        match goal with
          | [ H : nil |-v _ : _ |- _ ] => inversion H
        end)
      || match goal with
            | [ H : _ |- _ ] => apply H; crush; eauto
          end.
  Qed.

  Arguments subst_lookup [x' t G1].

  Lemma shadow_lookup : forall v t t' G1,
    G1 |-v x : t'
    -> G1 ++ (x, xt) :: nil |-v v : t
    -> G1 |-v v : t.
    induction G1 as [ | [? ?] ? ]; crush;
      match goal with
        | [ H : nil |-v _ : _ |- _ ] => inversion H
        | [ H1 : _ |-v _ : _, H2 : _ |-v _ : _ |- _ ] =>
          inversion H1; crush; inversion H2; crush
      end.
  Qed.

  Lemma shadow_hasType' : forall G e t,
    G |-e e : t
    -> forall G1, G = G1 ++ (x, xt) :: nil
      -> forall t'', G1 |-v x : t''
        -> G1 |-e e : t.
    #[local] Hint Resolve shadow_lookup : core.

    induction 1; crush; eauto;
      match goal with
        | [ H : (?x0, _) :: _ ++ (?x, _) :: _ |-e _ : _ |- _ ] =>
          destruct (var_eq x0 x); subst; eauto
      end.
  Qed.

  Lemma shadow_hasType : forall G1 e t t'',
    G1 ++ (x, xt) :: nil |-e e : t
    -> G1 |-v x : t''
    -> G1 |-e e : t.
    intros; eapply shadow_hasType'; eauto.
  Qed.

  #[local] Hint Resolve shadow_hasType : core.

    Lemma disjoint_cons : forall x x' t (G : ctx),
      x # G
      -> x' <> x
      -> x # (x', t) :: G.
      firstorder;
        match goal with
          | [ H : (_, _) = (_, _) |- _ ] => injection H
        end; crush.
    Qed.

    #[local] Hint Resolve disjoint_cons : core.

  Theorem subst_hasType : forall G e2 t,
    G |-e e2 : t
      -> forall G1, G = G1 ++ (x, xt) :: nil
        -> x # G1
        -> G1 |-e subst e2 : t.
    induction 1; crush;
      try match goal with
            | [ |- context[if ?E then _ else _] ] => destruct E
          end; crush; eauto 6;
      match goal with
        | [ H1 : x # _, H2 : _ |-v x : _ |- _ ] =>
          rewrite (subst_lookup H1 H2)
      end; crush.
  Qed.

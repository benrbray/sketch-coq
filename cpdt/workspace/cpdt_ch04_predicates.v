(*
  Adam Chlipala,
  "Certified Programming with Dependent Types"
  Chapter 4: Inductive Predicates
  http://adam.chlipala.net/cpdt/html/Cpdt.Predicates.html
*)

(* coq library *)
Set Printing Parentheses.
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
From Coq Require Export Reals.Reals.
Export ListNotations.

(* cpdt *)
Require Import Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Theorem or_comm : forall P Q,
  P \/ Q -> Q \/ P.
Proof.
  (* tauto is a decision procedure for constructive propositional logic *)
  tauto.
Qed.

Theorem arith_comm : forall ls1 ls2 : list nat,
  length ls1 = length ls2 \/ length ls1 + length ls2 = 6
  -> length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
Proof.
  (* intution extends tauto to simplify any remaining goals as much as
     possible using facts about propositional logic *)
  intuition.
  rewrite app_length.
  tauto.
Qed.

Inductive eq_alt (A : Type) (x : A) : A -> Prop :=
  | eq_refl : eq_alt x x.

Inductive isZero : nat -> Prop :=
  | IsZero : isZero 0.

Theorem isZero_contra:
  isZero 1 -> False.
Proof. inversion 1. Qed.

(* ====================================================== *)

Inductive even : nat -> Prop :=
  | Even0  : even 0
  | EvenSS : forall n, even n -> even (S (S n)).

Theorem even_0:
  even 0.
Proof. constructor. Qed.

SearchRewrite (_ + S _).

Theorem even_contra : forall n,
  even (S (n + n)) -> False.
Proof.
  induction 1.
  Abort.

Lemma even_contra_lemma:  forall n0,
  even n0 ->
  forall n,
    n0 = S (n + n) -> False.
Proof.
  (* manual proof *)
  induction 1; crush.
  destruct n; destruct n0; crush.
  apply IHeven with n0.
  rewrite <- plus_n_Sm in H0.
  assumption.
  (* automated proof*)
  Restart.
  #[local] Hint Rewrite <- plus_n_Sm.
  induction 1; crush;
    match goal with
    | [ H : S ?N = ?N0 + ?N0 |- _] => destruct N; destruct N0
    end; crush.
Qed.

Theorem even_contra : forall n,
  even (S (n + n)) -> False.
Proof.
  intros; eapply even_contra_lemma; eauto.
Qed.

Lemma even_contra_alt : forall n0 n,
  even n0 -> n0 = S (n + n) -> False.
Proof.
  induction 1; crush;
    match goal with
    | [ H : S ?N = ?N0 + ?N0 |- _] => destruct N; destruct N0
    end; crush.
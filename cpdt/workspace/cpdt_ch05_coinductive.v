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

(* ====================================================== *)

Section stream.
  Variable A : Type.
  CoInductive stream : Type :=
    | Cons : A -> stream -> stream.
End stream.

CoFixpoint zeroes : stream nat := Cons 0 zeroes.

CoFixpoint trues_falses : stream bool := Cons true false_trues
  with false_trues : stream bool := Cons false trues_falses.

Fixpoint approx A (s : stream A) (n : nat) : list A :=
  match n with
  | O    => nil
  | S n0 =>
    match s with
    | Cons h t => h :: approx t n0
    end
  end.

Eval simpl in approx zeroes 10.
Eval simpl in approx trues_falses 10.

Fail CoFixpoint looper : stream nat := looper.

Section interleave.
  Variable A : Type.

  CoFixpoint interleave (s1 s2 : stream A) : stream A :=
    match s1, s2 with
    | Cons h1 t1, Cons h2 t2 => Cons h1 (Cons h2 (interleave t1 t2))
    end.
End interleave.

Check interleave.

Section weird_map.
  Variables A B : Type.
  Variable f : A -> B.

  Fail CoFixpoint weird_map (s : stream A) : stream B :=
    match s with
    | Cons h t => interleave (Cons (f h) (weird_map t)) (Cons (f h) (weird_map t))
    end.
End weird_map.

(* ====================================================== *)

Section map.
  Variables A B : Type.
  Variable f : A -> B.

  CoFixpoint map (s : stream A) : stream B :=
    match s with
      | Cons h t => Cons (f h) (map t)
    end.
End map.

CoFixpoint ones : stream nat := Cons 1 ones.
Definition ones_alt : stream nat := map S zeroes.

Section stream_eq.
  Variable A : Type.

  (* we must define a coinductive notion of equality for our streams *)
  CoInductive stream_eq : stream A -> stream A -> Prop :=
    | Stream_eq : forall h t1 t2,
        stream_eq t1 t2 -> stream_eq (Cons h t1) (Cons h t2).
End stream_eq.

Theorem ones_eq:
  stream_eq ones ones_alt.
Proof.
  cofix ones_eq.
  assumption.
  Abort.

Definition frob A (s : stream A) : stream A :=
  match s with
  | Cons h t => Cons h t
  end.

Theorem frob_eq : forall A (s : stream A),
  s = frob s.
Proof. destruct s ; reflexivity. Qed.

Theorem ones_eq : stream_eq ones ones_alt.
Proof.
  cofix ones_eq.
  rewrite (frob_eq ones).
  rewrite (frob_eq ones_alt).
  simpl.
  constructor.
  assumption.
Qed.
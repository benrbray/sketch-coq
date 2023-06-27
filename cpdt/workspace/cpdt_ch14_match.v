(*
  Adam Chlipala,
  "Certified Programming with Dependent Types"
  Chapter 14: Match
  http://adam.chlipala.net/cpdt/html/Cpdt.Match.html
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
Require Import Cpdt.Coinductive.
Set Implicit Arguments.
Set Asymmetric Patterns.

(* extraction *)
Require Coq.extraction.Extraction.
Extraction Language Haskell.

(* ====================================================== *)

Ltac find_if :=
  match goal with
  | [ |- if ?X then _ else _ ] => destruct X
  end.

Theorem example_1: forall (a b c : bool),
  if a
    then if b
      then True
      else True
    else if c
      then True
      else True.
Proof.
  intros ; repeat find_if ; constructor.
Qed.

Ltac find_if_inside :=
  match goal with
  | [ |- context[if ?X then _ else _] ] => destruct X
  end.

Theorem example_2: forall (a b c : bool),
  if a
    then if b
      then True
      else True
    else if c
      then True
      else True.
Proof.
  intros; repeat find_if_inside; constructor.
Qed.

Theorem example_3: forall (a b : bool),
  (if a then 42 else 42) = (if b then 42 else 42).
Proof.
  intros;
  repeat find_if_inside;
  constructor.
Qed.

Ltac my_tauto :=
  repeat match goal with
  | [ H : ?P |- ?P ] => exact H
  
  | [ |- True   ] => constructor
  | [ |- _ /\ _ ] => constructor
  | [ |- _ -> _ ] => intro
  
  | [ H : False  |- _ ] => destruct H
  | [ H : _ /\ _ |- _ ] => destruct H
  | [ H : _ \/ _ |- _ ] => destruct H
  
  | [ H1 : ?P -> ?Q, H2 : ?P |- _ ] => specialize (H1 H2)
  end.

Section propositional.
  Variables P Q R : Prop.

  Theorem propositional : (P \/ Q \/ False) /\ (P -> Q) -> True /\ Q.
  Proof.
    my_tauto.
  Qed.
End propositional.

(* the body of the first case fails, but matching continues *)
Theorem m1 : True.
  match goal with
    | [ |- _ ] => intro
    | [ |- True ] => constructor
  end.
Qed.

(* failure can trigger a different way of matching the same pattern *)
Theorem m2 : forall P Q R : Prop,
  P -> Q -> R -> Q.
Proof.
  intros;
  (* prints matched H to "Info" panel *)
  match goal with
    | [ H : _ |- _ ] => idtac H
  end.
  (* repeatedly tries using the matched hypothesis to solve the goal *)
  match goal with
    | [ H : _ |- _ ] => idtac H; exact H
  end.
Qed.

(* checks that a proposition is not among our hypotheses *)
Ltac notHyp P :=
  match goal with
  | [ _ : P |- _ ] => fail 1
  | _ =>
    match P with
    | ?P1 /\ ?P2 => first [ notHyp P1 | notHyp P2 | fail 2 ]
    | _ => idtac
    end
  end.

Ltac extend pf :=
  let t := type of pf in
    notHyp t; generalize pf; intro.

Ltac completer :=
  repeat match goal with
    | [ |- _ /\ _ ] => constructor
    | [ H : _ /\ _ |- _ ] => destruct H
    | [ H : ?P -> ?Q, H' : ?P |- _ ] => specialize (H H')
    | [ |- forall x, _ ] => intro
    | [ H : forall x, ?P x -> _, H' : ?P ?X |- _ ] => extend (H X H')
  end.

Section firstorder.
  Variable A : Set.
  Variables P Q R S : A -> Prop.

  Hypothesis H1 : forall x, P x -> Q x /\ R x.
  Hypothesis H2 : forall x, R x -> S x.

  Theorem fo : forall (y x : A), P x -> S x.
    completer.
    assumption.
  Qed.
End firstorder.

Ltac completer_bad :=
  repeat match goal with
    | [ |- _ /\ _ ] => constructor
    | [ H : ?P /\ ?Q |- _ ] => destruct H;
      repeat match goal with
              | [ H' : P /\ Q |- _ ] => clear H'
            end
    (* below, replaced ?Q with _ *)
    | [ H : ?P -> _, H' : ?P |- _ ] => specialize (H H')
    | [ |- forall x, _ ] => intro

    | [ H : forall x, ?P x -> _, H' : ?P ?X |- _ ] => extend (H X H')
  end.

Section firstorder_bad.
  Variable A : Set.
  Variables P Q R S : A -> Prop.

  Hypothesis H1 : forall x, P x -> Q x /\ R x.
  Hypothesis H2 : forall x, R x -> S x.

  Theorem fo' : forall (y x : A), P x -> S x.
    completer_bad.
  Abort.
End firstorder_bad.

Theorem t1 : forall x : nat,
  x = x.
Proof.
  match goal with
  | [ |- forall x, _ ] => trivial
  end.
Qed.

Theorem t1_bad: forall x : nat,
  x = x.
Proof.
  match goal with
    | [ |- forall x, ?P ] => trivial
  end.
Qed.

Ltac length ls :=
  match ls with
    | nil => O
    | _ :: ?ls' => constr:(S (length ls'))
  end.

Goal False.
  let n := length (1 :: 2 :: 3 :: nil) in
    pose n.
Abort.

Reset length.

(* try all proofs of depth n *)
Ltac inster n :=
  intuition;
  match n with
  | S ?n0 =>
    (* if the recursive call to inster fails,
       coq backtracks and tries another match to the same case *)
    match goal with
    | [ H : forall x : ?T, _, y : ?T |- _ ] => generalize (H y); inster n0
    end
  end.


Section test_inster.
  Variable A : Set.
  Variables P Q : A -> Prop.
  Variable f : A -> A.
  Variable g : A -> A -> A.

  Hypothesis H1 : forall x y, P (g x y) -> Q (f x).

  Theorem test_inster : forall x, P (g x x) -> Q (f x).
    inster 2.
  Qed.

  Hypothesis H3 : forall u v, P u /\ P v /\ u <> v -> P (g u v).
  Hypothesis H4 : forall u, Q (f u) -> P u /\ P (f u).

  Theorem test_inster2 : forall x y, x <> y -> P x -> Q (f y) -> Q (f x).
    inster 3.
  Qed.
End test_inster.

Definition imp (P1 P2 : Prop) := P1 -> P2.
Infix "-->" := imp (no associativity, at level 95).
Ltac imp := unfold imp; firstorder.

Theorem and_True_prem : forall P Q,
  (P /\ True --> Q)
  -> (P --> Q).
  imp.
Qed.

Theorem and_True_conc : forall P Q,
  (P --> Q /\ True)
  -> (P --> Q).
  imp.
Qed.

Theorem pick_prem1 : forall P Q R S,
  (P /\ (Q /\ R) --> S)
  -> ((P /\ Q) /\ R --> S).
  imp.
Qed.

Theorem pick_prem2 : forall P Q R S,
  (Q /\ (P /\ R) --> S)
  -> ((P /\ Q) /\ R --> S).
  imp.
Qed.

Theorem comm_prem : forall P Q R,
  (P /\ Q --> R)
  -> (Q /\ P --> R).
  imp.
Qed.

Theorem pick_conc1 : forall P Q R S,
  (S --> P /\ (Q /\ R))
  -> (S --> (P /\ Q) /\ R).
  imp.
Qed.

Theorem pick_conc2 : forall P Q R S,
  (S --> Q /\ (P /\ R))
  -> (S --> (P /\ Q) /\ R).
  imp.
Qed.

Theorem comm_conc : forall P Q R,
  (R --> P /\ Q)
  -> (R --> Q /\ P).
  imp.
Qed.

Ltac search_prem tac :=
  let rec search P :=
    tac
    || (apply and_True_prem; tac)
    || match P with
         | ?P1 /\ ?P2 =>
           (apply pick_prem1; search P1)
           || (apply pick_prem2; search P2)
       end
  in match goal with
       | [ |- ?P /\ _ --> _ ] => search P
       | [ |- _ /\ ?P --> _ ] => apply comm_prem; search P
       | [ |- _ --> _ ] => progress (tac || (apply and_True_prem; tac))
     end.

Theorem t5:
  (forall x : nat, S x > x) ->
  2 > 1.
Proof.
  intros.
  evar (y : nat).
  let y0 := eval unfold y in y in
    clear y; specialize (H y0).
  apply H.
Qed.

Ltac insterU H :=
  repeat match type of H with
  | forall x : ?T, _ =>
    let x := fresh "x" in
      evar (x : T);
      let x0 := eval unfold x in x in
        clear x; specialize (H x0)
  end.

Theorem t5_2 : (forall x : nat, S x > x) -> 2 > 1.
  intro H. insterU H. apply H.
Qed.

Ltac insterKeep H :=
  let H' := fresh "H'" in
    generalize H; intro H'; insterU H'.

Section t6.
  Variables A B : Type.
  Variable P : A -> B -> Prop.
  Variable f : A -> A -> A.
  Variable g : B -> B -> B.

  Hypothesis H1 : forall v, exists u, P v u.
  Hypothesis H2 : forall v1 u1 v2 u2,
    P v1 u1
    -> P v2 u2
    -> P (f v1 v2) (g u1 u2).

  Theorem t6 : forall v1 v2, exists u1, exists u2, P (f v1 v2) (g u1 u2).
    intros.
    do 2 insterKeep H1.
    repeat match goal with
      | [ H : ex _ |- _ ] => destruct H
    end.
    eauto.
(*
  Brun, Duford, & Magaud 2010,
  "Designing and Proving Correct a Convex Hull
    Algorithm with Hypermaps in Coq"
  https://hal.inria.fr/hal-00955400/document
*)

Set Printing Parentheses.
From Coq Require Import Strings.String.  (* for manual grading *)
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
From Coq Require Export Reals.Reals.
Export ListNotations.
From Coq Require Export Permutation.

(* ====================================================== *)
(* ====================================================== *)

(* dimensional indices 0 and 1 of a hypermap *)
Inductive dim : Set :=
  | zero : dim
  | one  : dim.

(* decidability of equality for dim *)
Lemma eq_dim_dec : forall (i:dim) (j:dim),
  {i=j} + {~i=j}.
Proof.
  intros i j. induction i; induction j.
  - left. reflexivity.
  - right. discriminate.
  - right. discriminate.
  - left. reflexivity.
Qed.

(* dart is a half-edge *)
Definition dart := nat.
Definition eq_dart_dec := eq_nat_dec.
Definition nil := 0.

(* -- Points -------------------------------------------- *)

Inductive point :=
  | pt (x: R) (y: R).

(* -- Free Maps ----------------------------------------- *)

(* build larger maps from smaller ones *)
Inductive fmap : Set :=
  | V : fmap
  | I : fmap -> dart -> point -> fmap
  | L : fmap -> dim -> dart -> dart -> fmap.

(* these aren't correct *)
Definition p1  := pt 0 1.
Definition p2  := pt 1 2.
Definition p3  := pt 1 2.
Definition p9  := pt 1 2.
Definition p10 := pt 1 2.

Example paper_figure_2 :=
  (L (L (L (I (I (I (I V 3 p3) 2 p2) 10 p10) 9 p9) zero 3 2)
one 10 2) zero 10 9).

(* property that dart d exists in map m *)
Fixpoint exd (m:fmap) (d:dart) : Prop :=
  

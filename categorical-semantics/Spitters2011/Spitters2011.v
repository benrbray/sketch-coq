(* Spitters & van der Weegen 2011, "Type Classes for Mathematics in Type Theory" *)
(* https://arxiv.org/pdf/1102.1323.pdf *)

Global Generalizable All Variables.

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.

From Coq.Strings Require Export String.
From Coq.Lists Require Export List.
From Coq.Arith Require Export Peano_dec.

From Coq.Relations Require Export Relations.
From Coq.Classes Require Export Equivalence.
From Coq.Classes Require Export Morphisms.

(* ====================================================== *)

Class Equiv A := equiv: relation A.

Infix "=" := equiv: type_scope.

Class Associative `{Equiv A} (f : A -> A -> A) := {
  associativity : forall x y z, f x (f y z) = f (f x y) z
}.

(* ====================================================== *)
Module SemiGroup_Record.

Record SemiGroup (G : Type) (H: Equiv G) (e : relation G) (op : G -> G -> G) : Prop :=
  { sg_setoid : Equivalence e
  ; sg_assoc  : Associative op
  ; sg_proper : Proper (e ==> e ==> e) op }.

End SemiGroup_Record.
(* ====================================================== *)
(* ====================================================== *)
Module SemiGroup_TypeClass.

Class SemiGroup (G : Type) `{Equiv G} (e : relation G) (op : G -> G -> G) : Prop :=
  { sg_setoid : Equivalence e
  ; sg_assoc  : Associative op
  ; sg_proper : Proper (e ==> e ==> e) op }.

(* example theorem, "vanilla" approach *)
Theorem example_theorem `{SemiGroup G e op}:
  forall x y z,
    e (op (op x y) z) (op (op z y) x).
Admitted.

End SemiGroup_TypeClass.
(* ====================================================== *)
(* ====================================================== *)
Module SemiGroup_OperationalTypeClass.

(* an "operational type class" *)
Class SemiGroupOp A := sg_op : A -> A -> A.
Infix "&" := sg_op (at level 50, left associativity).

Record SemiGroup (G : Type) (eq : Equiv G) (op : SemiGroupOp G) : Prop :=
  { sg_setoid : Equivalence equiv
  ; sg_assoc  : Associative op
  ; sg_proper : Proper (equiv ==> equiv ==> equiv) op }.

(* example theorem, "operational type class" approach *)
Theorem example01 G eq op `{SemiGroup G eq op}:
  forall x y z,
    x & y & z = z & y & x.
Admitted.

End SemiGroup_OperationalTypeClass.
(* ====================================================== *)
(* ====================================================== *)
Module S4_1_ImplicitSyntaxDirectedAlgorithmComposition.

Class Decision (P : Prop) : Type := decide : sumbool P (not P).

#[export]
Instance decide_conj `{Decision P} `{Decision Q}: Decision (P /\ Q).
Proof.
  destruct H as [HP|HnotP]; destruct H0 as [HQ|HnotQ];
    try (left ; tauto);
    try (right; tauto).
Qed.

End S4_1_ImplicitSyntaxDirectedAlgorithmComposition.


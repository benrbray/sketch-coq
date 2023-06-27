(*
  Adam Chlipala,
  "Certified Programming with Dependent Types"
  Chapter 6: Subset Types and Variations
  http://adam.chlipala.net/cpdt/html/Cpdt.Subset.html
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

(* extraction *)
Require Coq.extraction.Extraction.
Extraction Language Haskell.

(* ====================================================== *)
(* ====================================================== *)

(* pred : nat -> nat must be total, so returns 0 for 0 *)
Print Nat.pred.
(*
  fun n : nat => match n with
               | 0 => n
               | S u => u
               end
      : nat -> nat
*)

(* the generated Haskell function does the same *)
Extraction pred.

(* we can use dependent types to strengthen the specification *)
Lemma zgtz : 0 > 0 -> False.
Proof. crush. Qed.

(* this predecessor function demands a proof
 * that (n > 0) before returning a value *)
Definition pred_strong1 (n : nat) : n > 0 -> nat :=
  match n with
  | 0 => fun pf : 0 > 0 => match zgtz pf with end
  | S n0 => fun _ => n0
  end.

Extraction pred_strong1.

Theorem two_gt0 : 2 > 0.
  crush.
Qed.

Eval compute in pred_strong1 two_gt0.

(* ====================================================== *)
(* ====================================================== *)

Locate "{ _ : _ | _ }".

Print sig.
(* 
Inductive sig (A : Type) (P : A -> Prop) : Type :=
	exist : forall x : A, (P x) -> {x : A | P x}
*)

(* the only way to construct a "sig" is to provide
       an object (x : A) and
       a proof that x satisfies property P *)

Definition pred_strong2 (s : {n : nat | n > 0}) : nat :=
  match s with
  | exist 0 pf     => match zgtz pf with end
  | exist (S n0) _ => n0
  end.

Eval compute in pred_strong2 (exist _ 2 two_gt0).

Extraction pred_strong2.

Print proj1_sig.
Print proj2_sig.

(* given n and a proof that n > 0,
 * produces m and a proof that n = S m *)
Definition pred_strong3 (s : {n : nat | n > 0}) : {m : nat | proj1_sig s = S m} :=
  match s return {m : nat | proj1_sig s = S m} with
    | exist 0 pf      => match zgtz pf with end
    | exist (S n0) pf => exist _ n0 (eq_refl _)
  end.

Eval compute in pred_strong3 (exist _ 2 two_gt0).

(* same as before! *)
Extraction pred_strong3.

Check exist.

Definition pred_strong4 : forall n : nat,
  n > 0 -> {m : nat | n = S m}.
Proof.
  refine (fun n =>
    match n with
      | O => fun _ => False_rec _ _
      | S n0 => fun _ => exist _ n0 _
    end) ; abstract crush.
Defined.

Print pred_strong4.

Notation "!" := (False_rec _ _).
Notation "[ e ]" := (exist _ e _).

Definition pred_strong5 : forall n : nat, n > 0 -> {m : nat | n = S m}.
  refine (fun n =>
    match n with
      | O => fun _ => !
      | S n' => fun _ => [n']
    end); crush.
Defined.

Eval compute in pred_strong5 two_gt0.

(* ====================================================== *)

Inductive exp : Set :=
  | Nat : nat -> exp
  | Plus : exp -> exp -> exp
  | Bool : bool -> exp
  | And : exp -> exp -> exp.

Inductive type : Set := TNat | TBool.

Inductive has_type : exp -> type -> Prop :=
  | HtHat : forall n, has_type (Nat n) TNat
  | HtPlus : forall e1 e2,
      has_type e1 TNat ->
      has_type e2 TNat ->
      has_type (Plus e1 e2) TNat
  | HtBool : forall b, has_type (Bool b) TBool
  | HtAnd : forall e1 e2,
      has_type e1 TBool ->
      has_type e2 TBool ->
      has_type (And e1 e2) TBool.

Definition eq_type_dec : forall t1 t2 : type,
  { t1 = t2 } + { t1 <> t2 }.
Proof. decide equality. Defined.

Print eq_type_dec.
Extraction eq_type_dec.
Print type_rec.

Print sumor.
Notation "!!" := (inright _ _).
Notation "[|| x ||]" := (inleft _ [x]).

Inductive maybe (A : Set) (P : A -> Prop) : Set :=
| Unknown : maybe P
| Found : forall x : A, P x -> maybe P.

Notation "{{ x | P }}" := (maybe (fun x => P)).
Notation "??" := (Unknown _).
Notation "[| x |]" := (Found _ x _).

Notation "x <- e1 ; e2" := (match e1 with
                             | Unknown => ??
                             | Found x _ => e2
                           end)
(right associativity, at level 60).

Notation "e1 ;; e2" := (if e1 then e2 else ??)
  (right associativity, at level 60).

Definition typeCheck : forall e : exp, {{t | has_type e t}}.
  #[local] Hint Constructors has_type : core.

  refine (fix F (e : exp) : {{t | has_type e t}} :=
    match e return {{t | has_type e t}} with
      | Nat _ => [|TNat|]
      | Plus e1 e2 =>
        t1 <- F e1;
        t2 <- F e2;
        eq_type_dec t1 TNat;;
        eq_type_dec t2 TNat;;
        [|TNat|]
      | Bool _ => [|TBool|]
      | And e1 e2 =>
        t1 <- F e1;
        t2 <- F e2;
        eq_type_dec t1 TBool;;
        eq_type_dec t2 TBool;;
        [|TBool|]
    end); crush.
Defined.

Eval simpl in typeCheck (Plus (Nat 1) (Nat 5)).

Extraction typeCheck.
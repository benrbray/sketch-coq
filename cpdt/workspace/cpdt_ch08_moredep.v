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
Require Import Cpdt.Coinductive.
Set Implicit Arguments.
Set Asymmetric Patterns.

(* extraction *)
Require Coq.extraction.Extraction.
Extraction Language Haskell.

(* ====================================================== *)

Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil : ilist 0
  | Cons : forall n, A -> ilist n -> ilist (S n).

  Fixpoint app n1 (ls1 : ilist n1) n2 (ls2 : ilist n2) : ilist (n1 + n2) :=
    match ls1 with
    | Nil         => ls2
    | Cons _ x t1 => Cons x (app t1 ls2)
    end.
  
  Fixpoint inject (ls : list A) : ilist (length ls) :=
    match ls with
    | nil    => Nil
    | h :: t => Cons h (inject t)
    end.

  Fixpoint forget {n} (ls : ilist n) : list A :=
    match ls with
    | Nil => nil
    | Cons _ h t => h :: forget t
    end.
  
  Theorem inject_inverse: forall ls,
    forget (inject ls) = ls.
  Proof.
    induction ls.
    - simpl. reflexivity.
    - simpl. apply f_equal. apply IHls.
  Qed.

  Definition hd_helper {n} (ls : ilist n) :=
    match ls in (ilist n) return (match n with 0 => unit | S _ => A end) with
    | Nil        => tt
    | Cons _ h _ => h
    end.

  Definition hd {n} (ls : ilist (S n)) : A := hd_helper ls.

End ilist.
(* ====================================================== *)
Section tagless.

Inductive type : Set :=
  | Nat : type
  | Bool : type
  | Prod : type -> type -> type.

Inductive exp : type -> Set :=
  | NConst : nat -> exp Nat
  | Plus   : exp Nat -> exp Nat -> exp Nat
  | Eq     : exp Nat -> exp Nat -> exp Bool
  | BConst : bool -> exp Bool
  | And    : exp Bool -> exp Bool -> exp Bool
  | If     : forall t, exp Bool -> exp t -> exp t -> exp t
  | Pair   : forall t1 t2, exp t1 -> exp t2 -> exp (Prod t1 t2)
  | Fst    : forall t1 t2, exp (Prod t1 t2) -> exp t1
  | Snd    : forall t1 t2, exp (Prod t1 t2) -> exp t2.

Fixpoint type_denote (t : type) : Set :=
  match t with
  | Nat => nat
  | Bool => bool
  | Prod t1 t2 => type_denote t1 * type_denote t2
  end%type.

Fixpoint exp_denote {t} (e : exp t) : type_denote t :=
  match e with
  | NConst n       => n
  | Plus e1 e2     => exp_denote e1 + exp_denote e2
  | Eq e1 e2       => if eq_nat_dec (exp_denote e1) (exp_denote e2) then true else false
  | BConst b       => b
  | And b1 b2      => (exp_denote b1) && (exp_denote b2)
  | If _ e0 e1 e2  => if (exp_denote e0) then (exp_denote e1) else (exp_denote e2)
  | Pair _ _ e1 e2 => (exp_denote e1, exp_denote e2)
  | Fst _ _ e      => fst (exp_denote e)
  | Snd _ _ e      => snd (exp_denote e)
  end.

Definition pair_out_type (t : type) :=
  option (match t with
    | Prod t1 t2 => exp t1 * exp t2
    | _ => unit
  end).

(* helper function which extracts components of a pair *)
Definition pair_out {t} (e : exp t) :=
  match e in (exp t) return (pair_out_type t) with
  | Pair _ _ e1 e2 => Some (e1, e2)
  | _              => None
  end.

Fixpoint constant_fold {t} (e : exp t) : exp t :=
  match e with
  | NConst n => NConst n
  | BConst b => BConst b
  | Plus e1 e2 =>
      let e1 := constant_fold e1 in
      let e2 := constant_fold e2 in
      match e1, e2 return (exp Nat) with
      | NConst n1, NConst n2 => NConst (n1 + n2)
      | _, _ => Plus e1 e2
      end
  | Eq e1 e2 =>
      let e1 := constant_fold e1 in
      let e2 := constant_fold e2 in
      match e1, e2 return (exp Bool) with
      | NConst n1, NConst n2 => BConst (n1 =? n2)
      | _, _ => Eq e1 e2
      end
  | And e1 e2 =>
      let e1 := constant_fold e1 in
      let e2 := constant_fold e2 in
      match e1, e2 return (exp Bool) with
      | BConst b1, BConst b2 => BConst (b1 && b2)
      | _, _ => And e1 e2
      end
  | If _ e et ef =>
      let e  := constant_fold e in
      let et := constant_fold et in
      let ef := constant_fold ef in
      match e with
      | BConst b => if b then et else ef
      | _        => If e et ef
      end
  | Pair _ _ e1 e2 => Pair (constant_fold e1) (constant_fold e2)
  | Fst _ _ e =>
      let e := constant_fold e in
      match pair_out e with
        | Some p => fst p
        | None => Fst e
      end
    | Snd _ _ e =>
      let e := constant_fold e in
      match pair_out e with
        | Some p => snd p
        | None => Snd e
      end
  end.
  
  Theorem constant_fold_correct: forall {t} (e : exp t),
    exp_denote e = exp_denote (constant_fold e).
  Proof.
    induction e ; crush.
    dep_destruct (constant_fold e1).
    Restart.
    induction e; crush;
    repeat (match goal with
              | [ |- context[match constant_fold ?E with NConst _ => _ | _ => _ end] ] =>
                dep_destruct (cfold E)
              | [ |- context[match pair_out (constant_fold ?E) with Some _ => _
                               | None => _ end] ] =>
                dep_destruct (constant_fold E)
              | [ |- (if ?E then _ else _) = _ ] => destruct E
            end; crush).
    Abort.


End tagless.
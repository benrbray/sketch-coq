(*
  Adam Chlipala,
  "Certified Programming with Dependent Types"
  Chapter 9: Dependent Data Structures
  http://adam.chlipala.net/cpdt/html/Cpdt.DataStruct.html
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

  (* (fin n) is isomorphic to {m : nat | m < n} *)
  Inductive fin : nat -> Set :=
  | First : forall n, fin (S n)
  | Next : forall n, fin n -> fin (S n).

  (* (fin 0) has no inhabitants *)

  (* (fin 1) has one inhabitant *)
  Check First 0 : fin 1.

  (* (fin 2) has two inhabitants *)
  Check First 1        : fin 2.
  Check Next (First 0) : fin 2.

  (* (fin 3) has three inhabitants *)
  Check First 2               : fin 3. (* select idx = 2 of 3 *)
  Check Next (First 1)        : fin 3. (* select idx = 1 of 3 *)
  Check Next (Next (First 0)) : fin 3. (* select idx = 0 0f 3 *)

  (* get element at specific index *)
  Fixpoint get n (ls : ilist n) : fin n -> A :=
    match ls in ilist n return fin n -> A with
    | Nil        => fun idx =>
      (* this case should be a contradiction *)
      match idx in fin n0 return (match n0 with 
                                  | 0 => A
                                  | S _ => unit
                                  end) with
      | First _ => tt
      | Next _ _ => tt
      end
    | Cons _ h t => fun idx =>
      (match idx in fin n return ilist (pred n) -> A with
      | First _     => fun _   => h
      | Next _ idx0 => fun ls0 => get ls0 idx0
      end) t
    end.
End ilist.

Arguments Nil {A}.
Arguments First {n}.

Check Cons 0 (Cons 1 (Cons 2 Nil)).

Eval simpl in get (Cons 0 (Cons 1 (Cons 2 Nil))) First.
Eval simpl in get (Cons 0 (Cons 1 (Cons 2 Nil))) (Next (First)).

Section ilist_map.
  Variables A B : Set.
  Variable f : A -> B.

  Fixpoint imap n (ls : ilist A n) : ilist B n :=
    match ls with
      | Nil => Nil
      | Cons _ x ls' => Cons (f x) (imap ls')
    end.

  Theorem get_imap : forall n (idx : fin n) (ls : ilist A n),
    get (imap ls) idx = f (get ls idx).
    induction ls; dep_destruct idx; crush.
  Qed.
End ilist_map.

(* ====================================================== *)

Section hlist.
  Variable A : Type.
  Variable B : A -> Type.

  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall (x : A) (ls : list A),
      B x -> hlist ls -> hlist (x :: ls).
  
  Variable elm : A.

  Inductive member : list A -> Type :=
  | HFirst : forall ls, member (elm :: ls)
  | HNext : forall x ls, member ls -> member (x :: ls).

  Fixpoint hget ls (mls : hlist ls) : member ls -> B elm :=
    match mls with
    | HNil => fun mem =>
        match mem in member ls' return (match ls' with
                                          | nil => B elm
                                          | _ :: _ => unit
                                        end) with
          | HFirst _ => tt
          | HNext _ _ _ => tt
        end
    | HCons _ _ x mls' => fun mem =>
        match mem in member ls' return (match ls' with
                                          | nil => Empty_set
                                          | x' :: ls'' =>
                                            B x' -> (member ls'' -> B elm)
                                            -> B elm
                                        end) with
          | HFirst _ => fun x _ => x
          | HNext _ _ mem' => fun _ get_mls' => get_mls' mem'
        end x (hget mls')
    end.
End hlist.


Arguments HNil {A B}.
Arguments HCons {A B x ls} _ _.

Arguments HFirst {A elm ls}.
Arguments HNext {A elm x ls} _.

Definition someTypes : list Set := nat :: nat :: bool :: nil.
Example someValues : hlist (fun T : Set => T) someTypes :=
  HCons 10 (HCons 5 (HCons true HNil)).

Eval simpl in hget someValues HFirst.
Eval simpl in hget someValues (HNext HFirst).

Check hlist.

Example somePairs : hlist (fun T : Set => T * T)%type someTypes :=
  HCons (2,3) (HCons (1, 2) (HCons (true, false) HNil)).

(* ====================================================== *)

Inductive type : Set :=
| Unit : type
| Arrow : type -> type -> type.

Inductive exp : list type -> type -> Type :=
| Const : forall ts, exp ts Unit
(* variables are represented as member values, which are
   like a constructive proof that a particular type is found
   in the type environment *)
| Var : forall ts t, member t ts -> exp ts t
| App : forall ts dom ran, exp ts (Arrow dom ran) -> exp ts dom -> exp ts ran
| Abs : forall ts dom ran, exp (dom :: ts) ran -> exp ts (Arrow dom ran).

Arguments Const {ts}.

Fixpoint typeDenote (t : type) : Set :=
  match t with
    | Unit => unit
    | Arrow t1 t2 => typeDenote t1 -> typeDenote t2
  end.

Fixpoint expDenote ts t (e : exp ts t) : hlist typeDenote ts -> typeDenote t :=
  match e with
    | Const _         => fun _ => tt
    | Var _ _ mem     => fun s => hget s mem
    | App _ _ _ e1 e2 => fun s => (expDenote e1 s) (expDenote e2 s)
    | Abs _ _ _ e'    => fun s => fun x => expDenote e' (HCons x s)
  end.

Check Abs.
Check expDenote.

Eval simpl in expDenote Const HNil.
Eval simpl in expDenote (Abs (dom := Unit) (Var HFirst)) HNil.
Eval simpl in expDenote (Abs (dom := Unit) (Abs (dom := Unit) (Var HFirst))) HNil.
Eval simpl in expDenote (Abs (dom := Unit) (Abs (dom := Unit) (Var (HNext HFirst)))) HNil.
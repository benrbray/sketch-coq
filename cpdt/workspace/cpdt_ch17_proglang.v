(*
  Adam Chlipala,
  "Certified Programming with Dependent Types"
  Chapter 17: Programming Language Syntax
  http://adam.chlipala.net/cpdt/html/Cpdt.ProgLang.html
*)

(* coq library *)
Set Printing Parentheses.
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
From Coq Require Export Reals.Reals.
Require Import FunctionalExtensionality List.
Export ListNotations.

(* cpdt *)
Require Import Cpdt.CpdtTactics.
Require Import Cpdt.Coinductive.
Require Import Cpdt.DepList.
Set Implicit Arguments.
Set Asymmetric Patterns.

(* extraction *)
Require Coq.extraction.Extraction.
Extraction Language Haskell.

(* ====================================================== *)

Ltac ext := let x := fresh "x" in extensionality x.
Ltac pl :=
  crush;
  repeat (match goal with
    | [ |- (fun x => _) = (fun y => _) ] => ext
    | [ |- _ _ _ ?E _ = _ _ _ ?E _ ] => f_equal
    | [ |- ?E ::: _ = ?E ::: _ ] => f_equal
    | [ |- hmap _ ?E = hmap _ ?E ] => f_equal
  end; crush).

Section hmap.
  Variable A : Type.
  Variables B1 B2 B3 : A -> Type.

  Variable f1 : forall x, B1 x -> B2 x.
  Variable f2 : forall x, B2 x -> B3 x.

  Theorem hmap_hmap : forall ls (hl : hlist B1 ls), 
    hmap f2 (hmap f1 hl) = hmap (fun i (x : B1 i) => f2 (f1 x)) hl.
  Proof.
    induction hl; crush.
  Qed.
End hmap.

Section Forall.
  Variable A : Type.
  Variable P : A -> Prop.

  Theorem Forall_In : forall ls,
    Forall P ls -> forall x, In x ls -> P x.
  Proof.
    induction 1; crush.
  Qed.

  Theorem Forall_In' : forall ls,
    (forall x, In x ls -> P x) -> Forall P ls.
  Proof.
    induction ls; crush.
  Qed.

  Variable P' : A -> Prop.

  Theorem Forall_weaken : forall ls,
    Forall P ls
    -> (forall x, P x -> P' x)
    -> Forall P' ls.
  Proof.
    induction 1; crush.
  Qed.
End Forall.

(* ====================================================== *)

Inductive type : Type :=
| Nat : type
| Func : type -> type -> type.

Fixpoint typeDenote (t : type) : Type :=
  match t with
    | Nat => nat
    | Func t1 t2 => typeDenote t1 -> typeDenote t2
  end.

(* ====================================================== *)
Module FirstOrder.

  Inductive term : list type -> type -> Type :=
  | Var : forall G t, member t G -> term G t
  | Const : forall {G}, nat -> term G Nat
  | Plus : forall G, term G Nat -> term G Nat -> term G Nat
  | Abs : forall G dom ran, term (dom :: G) ran -> term G (Func dom ran)
  | App : forall G dom ran, term G (Func dom ran) -> term G dom -> term G ran
  | Let : forall G t1 t2, term G t1 -> term (t1 :: G) t2 -> term G t2.

  Example add : term nil (Func Nat (Func Nat Nat)) :=
    Abs (Abs (Plus (Var (HNext HFirst)) (Var HFirst))).

  Example three_the_hard_way : term nil Nat :=
    App (App add (Const 1)) (Const 2).

  Fixpoint termDenote G t (e : term G t) : hlist typeDenote G -> typeDenote t :=
  match e with
    | Var _ _ x => fun s => hget s x
    | Const _ n => fun _ => n
    | Plus _ e1 e2 => fun s => termDenote e1 s + termDenote e2 s
    | Abs _ _ _ e1 => fun s => fun x => termDenote e1 (x ::: s)
    | App _ _ _ e1 e2 => fun s => (termDenote e1 s) (termDenote e2 s)
    | Let _ _ _ e1 e2 => fun s => termDenote e2 (termDenote e1 s ::: s)
  end.

  Fixpoint ident G t (e : term G t) : term G t :=
    match e with
      | Var _ _ x => Var x
      | Const _ n => Const n
      | Plus _ e1 e2 => Plus (ident e1) (ident e2)
      | Abs _ _ _ e1 => Abs (ident e1)
      | App _ _ _ e1 e2 => App (ident e1) (ident e2)
      | Let _ _ _ e1 e2 => Let (ident e1) (ident e2)
    end.

  Theorem identSound : forall G t (e : term G t) s,
    termDenote (ident e) s = termDenote e s.
    induction e; pl.
  Qed.

  Fixpoint cfold G t (e : term G t) : term G t :=
    match e with
      | Plus G e1 e2 =>
        let e1' := cfold e1 in
        let e2' := cfold e2 in
        let maybeOpt := match e1' return _ with
                          | Const _ n1 =>
                            match e2' return _ with
                              | Const _ n2 => Some (Const (n1 + n2))
                              | _ => None
                            end
                          | _ => None
                        end in
        match maybeOpt with
          | None => Plus e1' e2'
          | Some e' => e'
        end
      | Abs _ _ _ e1 => Abs (cfold e1)
      | App _ _ _ e1 e2 => App (cfold e1) (cfold e2)
      | Let _ _ _ e1 e2 => Let (cfold e1) (cfold e2)
      | e => e
    end.

  Theorem cfoldSound : forall G t (e : term G t) s,
    termDenote (cfold e) s = termDenote e s.
    induction e; pl;
      repeat (match goal with
                | [ |- context[match ?E with Var _ _ _ => _ | _ => _ end] ] =>
                  dep_destruct E
              end; pl).
  Qed.

  (* Fixpoint insertAt (x : nat) (ls: list nat) (pos : nat) : list nat :=
    match pos with
    | O      => x :: ls
    | S pos0 =>
      match ls with
      | nil     => x :: ls
      | y :: ys => y :: (insertAt x ys pos0)
      end
    end.

  Compute (insertAt 10 (0 :: 1 :: 2 :: 3 :: 4 :: nil) 2).
  Compute (insertAt 10 nil 0).

  Theorem insertAt_0: forall x ls,
    insertAt x ls 0 = x :: ls.
  Proof.
    intros. induction ls ; reflexivity.
  Qed. *)

  Fixpoint insertAt (t : type) (G : list type) (n : nat) {struct n} : list type :=
    match n with
      | O => t :: G
      | S n0 => match G with
                  | nil => t :: G
                  | t0 :: ts => t0 :: insertAt t ts n0
                end
    end.
  
  (* insert variable x anywhere in a typing context G *)
  Fixpoint liftVar {t} {G} (x : member t G) t0 n : member t (insertAt t0 G n).
    destruct x, n ; simpl; repeat constructor.
    - assumption.
    - apply liftVar. assumption.
  Defined.

  Fixpoint lift {G} t0 n {t} (e : term G t) : term (insertAt t0 G n) t :=
    match e with
    | Const _ n       => Const n
    | Var _ _ x       => Var  (liftVar x t0 n)
    | Abs _ _ _ e1    => Abs  (lift t0 (S n) e1)
    | Plus _ e1 e2    => Plus (lift t0 n     e1) (lift t0 n     e2)
    | App _ _ _ e1 e2 => App  (lift t0 n     e1) (lift t0 n     e2)
    | Let _ _ _ e1 e2 => Let  (lift t0 n     e1) (lift t0 (S n) e2)
    end.

  (* insert t0 at the head of the typing context *)
  Definition lift_front G t0 t (e : term G t) : term (t0 :: G) t :=
    lift t0 O e.

  (* let-removal transformation *)
  Fixpoint unlet {G1} {t} (e : term G1 t) G2 : hlist (term G2) G1 -> term G2 t :=
    match e with
      | Var _ _ x        => fun s => hget s x
      | Const _ n        => fun _ => Const n
      | Plus _ e1 e2     => fun s => Plus (unlet e1 s) (unlet e2 s)
      | Abs _ _ _ e1     => fun s => Abs (unlet e1 (Var HFirst ::: hmap (lift_front _) s))
      | App _ _ _ e1 e2  => fun s => App (unlet e1 s) (unlet e2 s)
      | Let _ t1 _ e1 e2 => fun s => unlet e2 (unlet e1 s ::: s)
    end.

End FirstOrder.

(* ====================================================== *)
Module HigherOrder.

Section var.
  Variable var : type -> Type.

  Inductive term : type -> Type :=
  | Const : nat -> term Nat
  | Var   : forall t,       var t -> term t
  | Plus  :                 term Nat -> term Nat -> term Nat
  | Abs   : forall dom ran, (var dom -> term ran) -> term (Func dom ran)
  | App   : forall dom ran, term (Func dom ran) -> term dom -> term ran
  | Let   : forall t1 t2,   term t1 -> (var t1 -> term t2) -> term t2.
End var.

Arguments Var {var t}.
Arguments Const {var}.
Arguments Abs {var dom ran}.

Definition Term t := forall var, term var t.

(* a term is a polymorphic function over variable representations,
  that is, the syntax tree has "holes" which can be freely filled
  with a specific variable representation of choice *)

Example add : Term (Func Nat (Func Nat Nat)) := fun _ =>
  Abs (fun x => Abs (fun y => Plus (Var x) (Var y))).

Example three_hard : Term Nat := fun _ =>
  App (App (add _) (Const 1)) (Const 2).

(* when working with pHOAS terms, treat the `var` parameter
   as an unconstrained choice of which data should be annotated
   on each variable. *)

(* countVars requires no annotations on variables, so we use unit *)
Fixpoint countVars t (e : term (fun _ => unit) t) : nat :=
  match e with
    | Const _       => 0
    | Var _ _       => 1
    | Plus e1 e2    => countVars e1 + countVars e2
    | Abs _ _ e1    => countVars (e1 tt)
    | App _ _ e1 e2 => countVars e1 + countVars e2
    | Let _ _ e1 e2 => countVars e1 + countVars (e2 tt)
  end.

Definition CountVars t (E : Term t) := countVars (E (fun _ => unit)).

Eval compute in CountVars add.
Eval compute in CountVars three_hard.

Require Import String.
Open Scope string_scope.

Fixpoint pretty t (e : term (fun _ => string) t) (x : string) : string :=
  match e with
    | Var _ s => s

    | Const _ => "#"
    | Plus e1 e2 => "(" ++ pretty e1 x ++ " + " ++ pretty e2 x ++ ")"

    | Abs _ _ e1 => "(fun " ++ x ++ " => " ++ pretty (e1 x) (x ++ "'") ++ ")"
    | App _ _ e1 e2 => "(" ++ pretty e1 x ++ " " ++ pretty e2 x ++ ")"

    | Let _ _ e1 e2 => "(let " ++ x ++ " = " ++ pretty e1 x ++ " in "
      ++ pretty (e2 x) (x ++ "'") ++ ")"
  end.

Definition Pretty t (E : Term t) := pretty (E (fun _ => string)) "x".

Eval compute in Pretty three_hard.

Fixpoint squash var t (e : term (term var) t) : term var t :=
  match e with
    | Const n       => Const n
    | Var _ e1      => e1
    | Plus e1 e2    => Plus (squash e1) (squash e2)
    | Abs _ _ e1    => Abs (fun x => squash (e1 (Var x)))
    | App _ _ e1 e2 => App (squash e1) (squash e2)
    | Let _ _ e1 e2 => Let (squash e1) (fun x => squash (e2 (Var x)))
  end.

(* a term with a single free variable *)
Definition Term1 (t1 t2 : type) := forall var, var t1 -> term var t2.

Definition Subst (t1 t2 : type) (E : Term1 t1 t2) (E0 : Term t1) : Term t2 :=
  fun var => squash (E (term var) (E0 var)).

Fixpoint termDenote t (e : term typeDenote t) : typeDenote t :=
  match e with
    | Var _ v => v
    | Const n => n
    | Plus e1 e2 => termDenote e1 + termDenote e2
    | Abs _ _ e1 => fun x => termDenote (e1 x)
    | App _ _ e1 e2 => (termDenote e1) (termDenote e2)
    | Let _ _ e1 e2 => termDenote (e2 (termDenote e1))
  end.

Check typeDenote.

Definition TermDenote t (E : Term t) : typeDenote t :=
  termDenote (E typeDenote).

Eval compute in TermDenote three_hard.

  Fixpoint ident var t (e : term var t) : term var t :=
    match e with
      | Var _ x => Var x

      | Const n => Const n
      | Plus e1 e2 => Plus (ident e1) (ident e2)

      | Abs _ _ e1 => Abs (fun x => ident (e1 x))
      | App _ _ e1 e2 => App (ident e1) (ident e2)

      | Let _ _ e1 e2 => Let (ident e1) (fun x => ident (e2 x))
    end.

  Definition Ident t (E : Term t) : Term t := fun var =>
    ident (E var).

  Lemma identSound : forall t (e : term typeDenote t),
    termDenote (ident e) = termDenote e.
    induction e; pl.
  Qed.

  Theorem IdentSound : forall t (E : Term t),
    TermDenote (Ident E) = TermDenote E.
    intros; apply identSound.
  Qed.

End HigherOrder.

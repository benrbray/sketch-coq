(*
  Adam Chlipala,
  "Certified Programming with Dependent Types"
  Chapter 2: Stack Machine
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

(* binary operation *)
Inductive binop : Set := Plus | Times.

(* expression *)
Inductive exp : Set :=
  | Const : nat   -> exp
  | Binop : binop -> exp -> exp -> exp.

Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
  | Plus => plus
  | Times => mult
  end.

Fixpoint expDenote (e : exp) : nat :=
  match e with
  | Const n => n
  | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
  end.

(* examples *)
Eval simpl in expDenote (Const 42).
Eval simpl in expDenote (Binop Plus (Const 2) (Const 2)).

(* ---- TARGET LANGUAGE --------------------------------- *)

Inductive instr : Set :=
  | iConst : nat   -> instr  (* push a constant onto the stack *)
  | iBinop : binop -> instr. (* pop two args and apply a binop *)

Definition prog  := list instr.
Definition stack := list nat.

(* interprets the instruction in the context of the current stack *)
Definition instrDenote (i : instr) (s1 : stack) : option stack :=
  match i with
  | iConst n => Some (n :: s1)
  | iBinop b =>
      match s1 with
      | arg1 :: arg2 :: s2 => Some ((binopDenote b) arg1 arg2 :: s2)
      | _                  => None
      end
  end.

(* execute a sequence of instructions *)
Fixpoint progDenote (p : prog) (s1 : stack) : option stack :=
  match p with
  | nil         => Some s1
  | i :: prest  =>
      match instrDenote i s1 with
      | Some s2 => progDenote prest s2
      | None    => None
      end
  end.

(* converts an expression into a list of instructions *)
(* note the evaluation order of binop! *)
Fixpoint compile (e : exp) : prog :=
  match e with
  | Const n => iConst n :: nil
  | Binop b e1 e2 => compile e2 ++ compile e1 ++ iBinop b :: nil
  end.

Eval simpl in compile (Const 42).
Eval simpl in compile (Binop Plus (Const 2) (Const 2)).
Eval simpl in compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).

Eval simpl in progDenote (compile (Const 42)) nil.
Eval simpl in progDenote (compile (Binop Plus (Const 2) (Const 2))) nil.
Eval simpl in progDenote (compile (Binop Times (Binop Plus (Const 2) (Const 2))
  (Const 7))) nil.

(* ====================================================== *)
(* ====================================================== *)

(* whenever the top of the instruction stack represents
 * a compiled expression, executing the program will
 * give the same result as evaluating the AST *) 
Lemma compile_correct_aux : forall e p s,
  progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).
Proof.
  intros e. induction e.
  - (* e = Const n *)
    simpl. reflexivity.
  - (* Binop b e0_1 e0_2 *)
    intros p s. simpl.
    rewrite <- app_assoc. rewrite IHe2.
    rewrite <- app_assoc. rewrite IHe1.
    reflexivity.
Qed.

Theorem compile_correct : forall e,
  progDenote (compile e) nil = Some (expDenote e :: nil).
Proof.
  intros e. rewrite (app_nil_end (compile e)).
  rewrite compile_correct_aux.
  reflexivity.
Qed. 

(* ====================================================== *)
(* ====================================================== *)

Inductive type : Set := Nat | Bool.

(* indexed (inductive) type family *)
Inductive tbinop : type -> type -> type -> Set :=
  | TPlus  : tbinop Nat Nat Nat
  | TTimes : tbinop Nat Nat Nat
  | TEq    : forall t, tbinop t t Bool
  | TLt    : tbinop Nat Nat Bool.

Inductive texp : type -> Set :=
  | TNConst : nat -> texp Nat
  | TBConst : bool -> texp Bool
  | TBinop : forall t1 t2 t,
      tbinop t1 t2 t -> texp t1 -> texp t2 -> texp t.

(* denotational semantics -- map types of object lang into coq *)
Definition typeDenote (t: type) : Set :=
  match t with
  | Nat => nat
  | Bool => bool
  end.

Check type.
Check Nat.

(* denotational semantics -- map types of object lang into coq *)
Definition tbinopDenote arg1 arg2 res (b : tbinop arg1 arg2 res)
  : typeDenote arg1 -> typeDenote arg2 -> typeDenote res :=
  match b with
  | TPlus    => plus
  | TTimes   => mult
  | TEq Nat  => beq_nat
  | TEq Bool => eqb
  | TLt      => leb
  end.

Fixpoint texpDenote t (e : texp t) : typeDenote t :=
  match e with
  | TNConst n => n
  | TBConst b => b
  | TBinop _ _ _ b e1 e2 => (tbinopDenote b) (texpDenote e1) (texpDenote e2)
  end.

Eval simpl in texpDenote (TNConst 42).
Eval simpl in texpDenote (TBConst true).
Eval simpl in texpDenote (TBinop TTimes (TBinop TPlus (TNConst 2) (TNConst 2))
  (TNConst 7)).

(* ---- TARGET LANGUAGE --------------------------------- *)

(* stack type classifies sets of possible stacks *)
(* - any matching stack must have same #elts *)
(* - and types of corresponding stack elts must mach *)
Definition tstack := list type.

(* example [Nat,Nat,Bool,Nat,Nat,Nat,Bool] *)

(* every instruction's type tell us
 * - the initial stack type it expects
 * - the final stack type it produces *)
Inductive tinstr : tstack -> tstack -> Set :=
  (* a numeric constant takes any stack 
     and produces a stack whose head is a Nat *)
  | TiNConst : forall s,   nat  -> tinstr s (Nat  :: s)
  (* a boolean constant takes any stack 
     and produces a stack whose head is a Bool *)
  | TiBConst : forall s,   bool -> tinstr s (Bool :: s)
  (* a binary op with signature (arg1, arg2) -> res
     takes any stack whose top is (arg1, arg2)
     and returns a stack whose top is the result type (res) *)
  | TiBinop  : forall arg1 arg2 res s,
      tbinop arg1 arg2 res -> tinstr (arg1 :: arg2 :: s) (res :: s).

(* a well-typed program also specifies the
 * type of input stack it expects, along with the
 * type of output stack it produces *)
Inductive tprog : tstack -> tstack -> Set :=
  (* the empty program produces a stack of the same type *)
  | TNil : forall s, tprog s s
  (* compose a program s1->s2
        with a program s2->s3
      to get a program s1->s3 *)
  | TCons : forall s1 s2 s3,
    tinstr s1 s2
    -> tprog s2 s3
    -> tprog s1 s3.

(* given a stack type like [Nat,Nat,Bool,Nat] for our object lang
 * we choose corresponding coq types (nat, (nat, (bool, (nat,())))
 * where the list is converted to nested pairs *)
Fixpoint vstack (stack : tstack) : Set :=
  match stack with
  | nil     => unit
  | t :: ts => typeDenote t * (vstack ts) (* product type *)
  end%type.
  (* ^^^^^ indicates type scope, so * is interpreted as a product type*)

(* explains how to use an instruction to update the runtime repr *)
Definition tinstrDenote ts ts' (i : tinstr ts ts') : vstack ts -> vstack ts' :=
  match i with
    | TiNConst _ n => fun s => (n, s)
    | TiBConst _ b => fun s => (b, s)
    | TiBinop _ _ _ _ b => fun s =>
      (* we need this let due to limitations of coq's match *)
      let '(arg1, (arg2, s')) := s in
        ((tbinopDenote b) arg1 arg2, s')
  end.

(* explains how to interpret a program one instruction at a time,
 * modifying the stack as needed *)
Fixpoint tprogDenote ts ts' (p : tprog ts ts') : vstack ts -> vstack ts' :=
  match p with
    | TNil _ => fun s => s
    | TCons _ _ _ i p' => fun s => tprogDenote p' (tinstrDenote i s)
  end.

(* concatenate two stack machine programs *)
Fixpoint tconcat ts1 ts2 ts3 (p1 : tprog ts1 ts2)
  : tprog ts2 ts3 -> tprog ts1 ts3 :=
  match p1 with
  | TNil _           => fun p2 => p2
  | TCons _ _ _ i p1 => fun p2 => TCons i (tconcat p1 p2)
  end.

Fixpoint tcompile t (e : texp t) (ts : tstack) : tprog ts (t :: ts) :=
  match e with
  | TNConst n => TCons (TiNConst _ n) (TNil _)
  | TBConst b => TCons (TiBConst _ b) (TNil _)
  | TBinop _ _ _ b e1 e2 =>
      tconcat (tcompile e2 _) (tconcat (tcompile e1 _) (TCons (TiBinop _ b) (TNil _)))
  end.


Eval simpl in tprogDenote (tcompile (TNConst 42) nil) tt.
Eval simpl in tprogDenote (tcompile (TBConst true) nil) tt.
Eval simpl in tprogDenote (tcompile (TBinop TTimes (TBinop TPlus (TNConst 2)
  (TNConst 2)) (TNConst 7)) nil) tt.

Lemma tconcat_correct : forall ts ts' ts'' (p : tprog ts ts') (p' : tprog ts' ts'')
  (s : vstack ts),
  tprogDenote (tconcat p p') s
  = tprogDenote p' (tprogDenote p s).
  induction p; crush.
Qed.

Hint Rewrite tconcat_correct.

Lemma tcompile_correct' : forall t (e : texp t) ts (s : vstack ts),
  tprogDenote (tcompile e ts) s = (texpDenote e, s).
  induction e; crush.
Qed.

Hint Rewrite tcompile_correct'.

Theorem tcompile_correct : forall t (e : texp t),
  tprogDenote (tcompile e nil) tt = (texpDenote e, tt).
  crush.
Qed.

Extraction tcompile.


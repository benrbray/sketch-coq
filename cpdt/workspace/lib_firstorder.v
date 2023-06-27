(* Adam Chlipala,
   "Certified Programming with Dependent Types"
   http://adam.chlipala.net/cpdt/html/Firstorder.html *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".

From Coq.Strings Require Export String.
From Coq.Lists Require Export List.
From Coq.Arith Require Export Peano_dec.

Require Import Cpdt.CpdtTactics.

(* ==== CONCRETE BINDING ================================ *)
Module Concrete.

Definition var := string.
Definition var_eq := string_dec.

(* simply-typed lambda calculus *)
Inductive exp : Set :=
  | Const : bool -> exp
  | Var : var -> exp
  | App : exp -> exp -> exp
  | Abs : var -> exp -> exp.

(* types *)
Inductive type : Set :=
  | Bool : type
  | Arrow : type -> type -> type.

Infix "-->" := Arrow (right associativity, at level 60).

(* a typing context is a list of assignments of types to variable names *)
Definition ctx := list (var * type).

Reserved Notation "G |-v x : t" (no associativity, at level 90, x at next level).
Reserved Notation "G |-e x : t" (no associativity, at level 90, x at next level).

(* an inhabitant of "G |-v x : t" is a proof that *)
(* variable x has type t in context G             *)
Inductive var_has_type : ctx -> var -> type -> Prop :=
  | First : forall x t G,
    (x, t) :: G |-v x : t
  | Next : forall x t x0 t0 G,
    x <> x0
    ->             G |-v x : t
    -> (x0, t0) :: G |-v x : t
    where "G |-v x : t" := (var_has_type G x t).

#[local] Hint Constructors var_has_type : core.

(* an inhabitant of "G |-e x : t" is a proof that *)
(* expression x has type t in context G           *)
Inductive has_type : ctx -> exp -> type -> Prop :=
| TConst : forall G b,   G |-e (Const b) : Bool
| TVar   : forall G x t, (G |-v x : t) -> (G |-e (Var x) : t)
| TApp   : forall G e1 e2 t1 t2,
    G |-e e1          : (Arrow t1 t2) ->
    G |-e e2          : t1            ->
    G |-e (App e1 e2) : t2
| TAbs   : forall G x t1 e t2,
    (x, t1) :: G |-e e         : t2 ->
               G |-e (Abs x e) : (Arrow t1 t2)
where "G |-e x : t" := (has_type G x t).

#[local] Hint Constructors has_type : core.

(* typing judgements can be extended with extra bindings *)
Lemma weaken_var_has_type : forall x t G1 G0,
  G0       |-v x : t ->
  G0 ++ G1 |-v x : t.
Proof.
  (* manual proof *)
  intros. induction G0.
  - (* G0 = [] *) inversion H.
  - (* G0 = a :: G0 *)
    inversion H; subst.
    + constructor.
    + simpl. apply Next.
      * assumption.
      * apply IHG0. assumption.
  Restart.
  (* automated proof *)
  intros. induction G0 as [ | [? ?] ?]; crush;
    match goal with
    | [ H : _ |-v _ :_ |- _ ] => inversion H; crush
    end.
Qed.

#[local] Hint Resolve weaken_var_has_type : core.

(* typing judgements can be extended with extra bindings *)
Lemma weaken_has_type : forall G1 G0 e t,
  G0       |-e e : t ->
  G0 ++ G1 |-e e : t.
Proof.
  (* manual proof *)
  intros. generalize dependent t. generalize dependent G0.
  induction e; intros G0 t H.
  - (* Const*) inversion H; subst. apply TConst.
  - (* Var *)  inversion H; subst. apply TVar. apply weaken_var_has_type. assumption.
  - (* App*)
    inversion H; subst.
    apply IHe1 in H3. apply IHe2 in H5.
    apply TApp with (t1 := t1); assumption.
  - (* Abs *)
    inversion H; subst.
    apply TAbs. apply IHe in H4.
    assumption.
  (* automated proof *)
  Restart.
  induction 1; crush; eauto.
Qed.

#[local] Hint Resolve weaken_has_type : core.

Lemma weaken_has_type_empty : forall e t,
            nil |-e e : t ->
  forall G, G   |-e e : t.
Proof.
  intros. change G with (nil ++ G).
  apply weaken_has_type. assumption.
Qed.

#[local] Hint Resolve weaken_has_type_empty : core.

(* capture-avoiding substitution *)
Section subst.

  Variable x : var.
  Variable e1 : exp.

  (* substitute the closed expression e1 for every free occurrence of x in e2 *)
  Fixpoint subst (e2 : exp) : exp :=
    match e2 with
    | Const _   => e2
    | Var y     => if var_eq y x then e1 else e2
    | App e1 e2 => App (subst e1) (subst e2)
    | Abs y e   => Abs y (if var_eq y x then e else (subst e))
    end.

  (* e1 is a closed expression with type xt *)
  Variable xt : type.
  Hypothesis Ht : nil |-e e1 : xt.

  (* "x#G" means "x" is fresh in context "G" *)
  Notation "x # G" := (forall t' : type, In (x, t') G -> False) (no associativity, at level 90).

  Lemma subst_var_has_type : forall y t,
    x <> y                        ->
    forall G,
      G ++ (x,xt) :: nil |-v y : t ->
                       G |-v y : t.
  Proof.
    intros.
    induction G as [ | [? ?] ?].
    - (* G = [] *)
      inversion H0; subst.
      + contradiction.
      + assumption.
    - (* G = (v,t0) :: G *)
      inversion H0; subst.
      + (* First *) apply First.
      + (* Next  *) apply Next.
        * assumption.
        * apply IHG. assumption.
  Qed.

  #[local] Hint Resolve subst_var_has_type : core.

  Lemma subst_fresh_var_has_type : forall {y t G},
    y # G ->
    G ++ (x, xt) :: nil |-v y : t ->
    t = xt.
  Proof.
    (* manual proof *)
    intros.
    induction G as [ | [? ?] ? ]; simpl.
    - (* G = [] *)
      inversion H0; subst.
      + (* First *) reflexivity.
      + (* Next *) inversion H7.
    - (* G = (v,t0) :: G *)
      inversion H0; subst.
      + (* First *)
        exfalso.
        assert (Hin : In (y,t) ((y,t) :: G)).
          { simpl. left. reflexivity. }
        apply H in Hin.
        contradiction.
      + (* Next *)
        apply IHG.
        * (* y # G *)
          intros t1 Ht1.
          specialize (H t1).
          simpl in H.
          apply H.
          right.
          assumption.
        * assumption.
    (* automated proof *)
    Restart.
    induction G as [ | [? ?] ? ]; crush; eauto;
      match goal with
        | [ H : _ |-v _ : _ |- _ ] => inversion H
      end; crush;
        (elimtype False; eauto;
          match goal with
            | [ H : nil |-v _ : _ |- _ ] => inversion H
          end)
      || match goal with
            | [ H : _ |- _ ] => apply H; crush; eauto
          end.
  Qed.

  Lemma shadow_lookup : forall y t2 t1 G,
    G                  |-v x : t1 ->
    G ++ (x,xt) :: nil |-v y : t2 ->
    G                  |-v y : t2.
  Proof.
    induction G as [ | [? ?] ? ]; crush;
      match goal with
        | [ H : nil |-v _ : _ |- _ ] => inversion H
        | [ H1 : _ |-v _ : _, H2 : _ |-v _ : _ |- _ ] =>
          inversion H1; crush; inversion H2; crush
      end.
  Qed.

  (* allows for removing provably unused variables from ends of typing contexts *)
  Lemma shadow_var_has_type : forall y t2 t1 G,
    G                  |-v x : t1 ->
    G ++ (x,xt) :: nil |-v y : t2 ->
    G                  |-v y : t2.
  Proof.
    (* manual proof -- gave up! *)
    (* automated proof *)
    induction G as [ | [? ?] ? ]; crush;
      match goal with
        | [ H : nil |-v _ : _ |- _ ] => inversion H
        | [ H1 : _ |-v _ : _, H2 : _ |-v _ : _ |- _ ] =>
          inversion H1; crush; inversion H2; crush
      end.
  Qed.

  #[local] Hint Resolve shadow_var_has_type : core.

  (* allows for removing provably unused variables from ends of typing contexts *)
  Lemma shadow_has_type_helper : forall G e t,
    G |-e e : t ->
    forall G1,
      G = G1 ++ (x,xt) :: nil ->
      forall t2, 
        G1 |-v x : t2 ->     (* (x,t2) shadows (x,xt) *)
        G1 |-e e : t.
  Proof.
    #[local] Hint Resolve shadow_var_has_type : core.
    induction 1; crush; eauto.
    destruct (var_eq x0 x); subst; eauto.
  Qed.

  Lemma shadow_has_type : forall G e t1 t2,
    G ++ (x,xt) :: nil |-e e : t1 ->
    G                  |-v x : t2 ->
    G                  |-e e : t1.
  Proof.
    intros. eapply shadow_has_type_helper; eauto.
  Qed.

  #[local] Hint Resolve shadow_has_type : core.

  (* disjointness facts may be extended to larger contexts *)
  Lemma disjoint_cons : forall x1 x2 t (G : ctx),
    x1 # G   ->
    x1 <> x2 ->
    x1 # (x2, t) :: G.
  Proof.
    (* manual proof *)
    firstorder.
    injection H1.
    intros Hxt.
    intros Hx.
    symmetry in Hx.
    contradiction.
    (* automated proof *)
    Restart.
    firstorder;
      match goal with
      | [ H : (_, _) = (_, _) |- _ ] => injection H
      end; crush.
  Qed.

  #[local] Hint Resolve disjoint_cons : core.

  Theorem subst_hasType : forall G e2 t,
    G |-e e2 : t
      -> forall G1, G = G1 ++ (x, xt) :: nil
        -> x # G1
        -> G1 |-e subst e2 : t.
    induction 1; crush;
      try match goal with
            | [ |- context[if ?E then _ else _] ] => destruct E
          end; crush; eauto 6;
      match goal with
        | [ H1 : x # _, H2 : _ |-v x : _ |- _ ] =>
          rewrite (subst_fresh_var_has_type H1 H2)
      end; crush.
  Qed.

  Theorem subst_has_type_closed : forall e2 t,
      (x, xt) :: nil |-e e2 : t
      -> nil |-e subst e2 : t.
      intros; eapply subst_hasType; eauto.
    Qed.
End subst.

#[local] Hint Resolve subst_has_type_closed : core.

Notation "[ x ~> e1 ] e2" := (subst x e1 e2) (no associativity, at level 80).

End Concrete.
(* ====================================================== *)

(* ==== DE BRUIJN INDICES =============================== *)
Module DeBruijn.

Definition var := nat.
Definition var_eq := eq_nat_dec.

(* Abstractions do not take a named variable argument.  Instead,
   variables in the body of the abstraction use integers n to
   refer to the "nth enclosing bound variable" *)
Inductive exp : Set :=
  | Const : bool -> exp
  | Var : var -> exp
  | App : exp -> exp -> exp
  | Abs : exp -> exp.

Inductive type : Set :=
  | Bool : type
  | Arrow : type -> type -> type.

Infix "-->" := Arrow (right associativity, at level 60).

(* since variables are numbers, contexts can be simple lists of types *)
Definition ctx := list type.

(* lookup *)
Reserved Notation "G '⊢v' x : t" (no associativity, at level 90, x at next level).
Inductive var_has_type : ctx -> var -> type -> Prop :=
  | VFirst : forall t G,
      t :: G  ⊢v O : t
  | VNext : forall n t0 t1 G,
      G       ⊢v n : t0 ->
      t1 :: G ⊢v (S n) : t0
  where "G '⊢v' x : t" := (var_has_type G x t).

Hint Constructors var_has_type : core.

(* has_type *)
Reserved Notation "G '⊢e' x : t" (no associativity, at level 90, x at next level).
Inductive has_type : ctx -> exp -> type -> Prop :=
  | T_Const : forall G b,
      G ⊢e Const b : Bool
  | T_Var: forall G v t,
      G ⊢v v     : t ->
      G ⊢e Var v : t
  | T_App: forall G e1 e2 dom ran,
      G ⊢e e1 : dom --> ran ->
      G ⊢e e2 : dom         ->
      G ⊢e App e1 e2 : ran
  | T_Abs : forall G e t1 t2,
      t1 :: G ⊢e e     : t2          ->
            G ⊢e Abs e : Arrow t1 t2
  where "G '⊢e' x : t" := (has_type G x t).

Hint Constructors has_type : core.

(* ------------------------------------------------------ *)

Lemma weaken_var_has_type : forall G2 v t G1,
  G1       ⊢v v : t ->
  G1 ++ G2 ⊢v v : t.
Proof. 
  (* manual proof *)
  intros.
  generalize dependent v.
  induction G1; intros v H ; inversion H ; subst.
  - apply VFirst.
  - simpl. apply VNext. apply IHG1. apply H4.
  (* automated proof *)
  Restart.
  induction 1; crush.
Qed.

Hint Resolve weaken_var_has_type : core.

Theorem weaken_has_type : forall G2 G1 e t,
  G1       ⊢e e : t ->
  G1 ++ G2 ⊢e e : t.
Proof. induction 1; crush; eauto. Qed.

Hint Resolve weaken_var_has_type : core.

Theorem weaken_has_type_empty : forall e t,
  nil ⊢e e : t ->
  forall G,
    G ⊢e e : t.
Proof.
  intros; change G with (nil ++ G).
  apply weaken_has_type. assumption.
Qed.

Hint Resolve weaken_has_type_empty : core.

(* ------------------------------------------------------ *)

(* replace free occurrences of x in e2 with e1 *)
Fixpoint subst (x : var) (e1 e2 : exp) : exp :=
  match e2 with
  | Const _   => e2
  | Var y     => if var_eq x y then e1 else e2
  | App f1 f2 => App (subst x e1 f1) (subst x e1 f2)
  | Abs e     => Abs (subst (S x) e1 e)
  end.

Lemma subst_eq : forall t1 t2 G,
  G ++ t1 :: nil ⊢v length G : t2
  ->
  t1 = t2.
Proof.
  intros.
  induction G as [ | t0 G0 ].
  - (* nil *) inversion H. reflexivity.
  - (* t0 :: G0 *) inversion H; subst. firstorder.
Qed.

Hint Resolve subst_eq : core.

Lemma subst_neq_var : forall t1 t2 G x,
  G ++ t1 :: nil ⊢v x : t2 ->
  x <> length G            ->
  G              ⊢v x : t2.
Proof.
  (* manual proof *)
  intros.
  generalize dependent x.
  induction G as [ | t0 G0]; intros x H Hlen.
  - (* [] *) inversion H; subst.
    + exfalso. apply Hlen. reflexivity.
    + inversion H4.
  - (* t0 :: G0 *)
    inversion H; subst.
    + apply VFirst.
    + apply VNext. apply IHG0.
      * assumption.
      * intros Hcontra.
        apply Hlen. simpl.
        apply f_equal.
        assumption.
  (* automated proof *)
  Restart.
  induction G; inversion 1; crush;
  match goal with
    | [ H : nil ⊢v _ : _ |-  _ ] => inversion H
  end.
Qed.

#[local] Hint Resolve subst_neq_var : core.

Lemma subst_neq : forall x t1 t2 G,
  G ++ t1 :: nil ⊢v x : t2 ->
  x <> length G            ->
  G              ⊢e Var x : t2.
Proof.
  intros.
  apply T_Var.
  apply subst_neq_var with t1; assumption.
Qed.

#[local] Hint Resolve subst_neq : core.

(* helper for eauto, which will not apply computational equivalences automatically *)
Lemma has_type_push : forall t1 t2 G e1 e2,
  t1 :: G ⊢e subst (length (t1 :: G)) e1 e2 : t2 ->
  t1 :: G ⊢e subst (S (length G))     e1 e2 : t2.
Proof. trivial. Qed.

#[local] Hint Resolve has_type_push : core.

Definition closed_term e := exists t, nil ⊢e e : t.

Theorem subst_has_type: forall G e1 e2 t1 t2,
  nil ⊢e e1 : t1 ->
  G   ⊢e e2 : t2 ->
  forall G1,
    G = G1 ++ t1 :: nil ->
    G1 ⊢e (subst (length G1) e1 e2) : t2.
Proof.
  (* attempt 1, by induction on e2 *)
  intros G e1 e2.
  induction e2; intros t1 t2 He1 He2; inversion He2; subst.
  - (* Const *) intros G1 HG. apply T_Const.
  - (* Var *) intros G1 HG. simpl.
    destruct (var_eq (length G1) v).
    + (* v = length G1 *)
      subst. apply subst_eq in H1. subst.
      apply weaken_has_type_empty. assumption.
    + (* v <> length G1 *)
      apply not_eq_sym in n. subst.
      apply subst_neq with t1; assumption.
  - (* App *) intros G1 HG; subst.
    simpl. apply T_App with dom.
    * specialize (IHe2_1 t1 (dom --> t2) He1 H2 G1).
      apply IHe2_1. reflexivity.
    * specialize (IHe2_2 t1 dom He1 H4 G1).
      apply IHe2_2. reflexivity.
  - (* Abs *)
  Restart.
  (* attempt 2, by induction on e1 *)
  induction 2; crush;
    try match goal with
          | [ |- context[if ?E then _ else _] ] => destruct E
        end; crush; eauto 6;
    try match goal with
          | [ H : _ ⊢v _ : _ |- _ ] =>
            rewrite (subst_eq H)
        end; crush.
  apply subst_eq in H0. subst.
  apply weaken_has_type_empty.
  assumption.
Qed.

Theorem subst_has_type_closed : forall t1 t2 e1 e2,
        nil ⊢e e1 : t1 ->
  t1 :: nil ⊢e e2 : t2 ->
        nil ⊢e subst O e1 e2 : t2.
Proof.
  intros; change O with (length (@nil type)).
  apply subst_has_type with (t1 :: nil) t1; trivial.
Qed.

Hint Resolve subst_has_type_closed : core.

Notation "[ x ~> e1 ] e2" := (subst x e1 e2) (no associativity, at level 80).

(* values include constants and closed lambda expressions *)
Inductive val : exp -> Prop :=
| VConst : forall b, val (Const b)
| VAbs   : forall e, val (Abs e).

Hint Constructors val : core.

Reserved Notation "e1 ==> e2" (no associativity, at level 90).

Inductive step : exp -> exp -> Prop :=
| Beta : forall e1 e2,
    val e2 ->
      App (Abs e1) e2 ==> [O ~> e2] e1
| Cong1 : forall e1a e2 e1b,
    e1a ==> e1b ->
      App e1a e2 ==> App e1b e2
| Cong2 : forall e1 e2a e2b,
    val e1 ->
    e2a ==> e2b ->
      App e1 e2a ==> App e1 e2b
where "e1 ==> e2" := (step e1 e2).

Hint Constructors step : core.

(* every well-typed closed expression is either a value, or is reducible *)
Theorem progress: forall e0 t,
  nil ⊢e e0 : t ->
  val e0 \/ exists e1, e0 ==> e1.
Proof.
  intros e0. induction e0; intros t H.
  - (* Const *) left. apply VConst.
  - (* Var *) inversion H; subst; inversion H2.
  - (* App *)
    inversion H; subst.
    apply IHe0_1 in H3.
    apply IHe0_2 in H5.
    destruct H3, H5.
    + (* val, val *) 
      inversion H; subst.
      inversion H0; subst.
      * (* e0_1 is a constant *) inversion H5.
      * (* e0_1 is an abs *) right. eexists. apply Beta. assumption.
    + (* val, red *)
      right. inversion H1. eexists. eapply Cong2; eauto.
    + (* red, val *)
      right. inversion H0. eexists. eapply Cong1; eauto.
    + (* red, red *)
     right. inversion H0. eexists. eapply Cong1; eauto.
  - (* Abs *) left. apply VAbs.
Qed.

(* reducing a well-typed expression yields a result of the same type *)
Theorem preservation: forall e0 t,
  nil ⊢e e0 : t ->
  forall e1,
    e0 ==> e1 ->
    nil ⊢e e1 : t.
Proof.
  intros e0. induction e0; intros t H e1 Hred.
  - (* Const irreducible *) inversion Hred.
  - (* Var   irreducible *) inversion Hred.
  - (* App *)
    inversion Hred; subst.
    + (* Beta *)
      inversion H; subst.
      inversion H4; subst.
      apply subst_has_type_closed with dom; assumption.
    + (* Cong1 *)
      inversion H; subst.
      apply T_App with dom.
      * apply (IHe0_1 (dom --> t)); assumption.
      * assumption. 
    + (* Cong2 *)
      inversion H; subst.
      apply T_App with dom.
      * assumption.
      * apply (IHe0_2 dom); assumption.
  - (* Abs irreducible  *) inversion Hred.
Qed.

(* ==== locally nameless ================================ *)
Module LocallyNameless.

Require Import Coq.Arith.Compare_dec.

Definition free_var := string.
Definition bound_var := nat.

(* free variables are represented as strings, like with concrete syntax *)
(* bound variables are represented as integers, the same as de bruijn *)
Inductive exp : Set :=
  | Const : bool -> exp
  | FreeVar : free_var -> exp
  | BoundVar : bound_var -> exp
  | App : exp -> exp -> exp
  | Abs : exp -> exp.

Inductive type : Set :=
  | Bool : type
  | Arrow : type -> type -> type.

Infix "-->" := Arrow (right associativity, at level 60).

(* since typing only depends on types of free variables,
   contexts are the same as in the concrete binding example *)
Definition ctx := list (free_var * type).

Reserved Notation "G |-v x : t" (no associativity, at level 90, x at next level).

Inductive var_has_type : ctx -> free_var -> type -> Prop :=
| First : forall x tx G,
    (x,tx) :: G ⊢v x : tx
| Next  : forall x tx y ty G,
                   x <> y ->
              G ⊢v x : tx ->
    (y,ty) :: G ⊢v x : tx
  where "G ⊢v x : t" := (var_has_type G x t).

Hint Constructors var_has_type : core.

(* "opening" replaces a bound variable with a free variable *)
Fixpoint open_rec (x : free_var) (n : bound_var) (e : exp) : exp :=
  match e with
  | Const _    => e
  | FreeVar _  => e
  | BoundVar m =>
      if eq_nat_dec m n
      then FreeVar x
      else if le_lt_dec m n
        then (* m <= n, index corresponds to  *) e
        else (* m  > n, term is open *) BoundVar (pred m)
  | App e1 e2  => App (open_rec x n e1) (open_rec x n e2)
  | Abs e1     => Abs (open_rec x (S n) e1)
  end.

(* "open" a locally-nameless term, replacing the outer    *)
(* most bound variable with the free variable x           *)
Definition open (x : free_var) (e : exp) : exp := open_rec x 0 e.

Definition X : string := "x".

Eval simpl in if (eq_nat_dec 0 0) then 1 else 2.

Example open_example_1:
  open_rec X 0 (Abs (BoundVar 1))
  =
  Abs (FreeVar X).
Proof. reflexivity. Qed.

Example open_example_2:
  open_rec X 0 (Abs (BoundVar 2))
  =
  Abs (BoundVar 1).
Proof. reflexivity. Qed.

Example open_example_3:
  open_rec X 1 (Abs (BoundVar 2))
  =
  Abs (FreeVar X).
Proof. reflexivity. Qed.

(* find the free variables in an expression *)
Fixpoint free_vars (e : exp): list free_var :=
  match e with
  | Const _    => nil
  | FreeVar x  => x :: nil
  | BoundVar _ => nil
  | App e1 e2  => free_vars e1 ++ free_vars e2
  | Abs e1     => free_vars e1
  end.

(* an expression is "locally closed" up to index "n" if   *)
(* it mentions no de bruijn indices higher than "pred n"  *)
Inductive lclosed : nat -> exp -> Prop :=
| lc_const     : forall n b, lclosed n (Const b)
| lc_free_var  : forall n x, lclosed n (FreeVar x)
| lc_bound_var : forall n v, v < n -> lclosed n (BoundVar v)
| lc_app       : forall n e1 e2, lclosed n e1 -> lclosed n e2 -> lclosed n (App e1 e2)
| lc_abs       : forall n e,    lclosed (S n) e -> lclosed n (Abs e).

Hint Constructors lclosed : core.

Reserved Notation "G ⊢e e : t" (no associativity, at level 90, e at next level).

Inductive has_type : ctx -> exp -> type -> Prop :=
| tp_const : forall G b,
    G ⊢e Const b : Bool
| tp_free_var : forall G f t,
    G ⊢v         f : t -> 
    G ⊢e FreeVar f : t
| tp_app : forall G e1 e2 t1 t2,
    G ⊢e e1        : (t1 --> t2) ->
    G ⊢e e2        : t1          ->
    G ⊢e App e1 e2 : t2
| tp_abs : forall G e t1 t2 L,
    (forall x, ~ In x L -> 
      (x,t1) :: G ⊢e open x e : t2) ->
    G ⊢e Abs e : t1 --> t2
where "G ⊢e e : t" := (has_type G e t).

Hint Constructors has_type : core.

Definition extends_ctx (G1 G2 : ctx) :=
  forall x t,
    G1 ⊢v x : t ->
    G2 ⊢v x : t.

Hint Unfold extends_ctx : core.

Lemma var_has_type_push: forall G1 G2 x tx y ty,
  extends_ctx G1 G2       ->
  (x, tx) :: G1 ⊢v y : ty ->
  (x, tx) :: G2 ⊢v y : ty.
Proof.
  inversion 2; eauto.
Qed.

#[local] Hint Resolve var_has_type_push : core.

Theorem weaken_has_type : forall G1 e t,
  G1 ⊢e e : t ->
  forall G2, 
    extends_ctx G1 G2 ->
    G2 ⊢e e : t.
Proof.
  induction 1; eauto.
Qed.

Hint Resolve weaken_has_type : core.

Ltac ln := crush;
  repeat (match goal with
  | [ |- context[if ?E then _ else _] ] => destruct E
  | [ _ : context[if ?E then _ else _] |- _ ] => destruct E
  end; crush); eauto.

Lemma lclosed_S : forall x e n,
  lclosed n     (open_rec x n e) ->
  lclosed (S n) e.
Proof.
  induction e; inversion 1; ln.
Qed.

#[local] Hint Resolve lclosed_S : core.

Require Import Lia.

Lemma lclosed_weaken : forall n e,
  lclosed n e
  -> forall n', n' >= n
    -> lclosed n' e.
  induction 1; crush.
  constructor. lia.
Qed.

#[local] Hint Resolve lclosed_weaken : core.
Hint Extern 1 (_ >= _) => lia : core.

(* ---- fresh variables --------------------------------- *)
Open Scope string_scope.

(* returns a variable name "x" with "n" prime marks *)
Fixpoint primes (n : nat) : string :=
  match n with
  | O    => "x"
  | S n0 => primes n0 ++ "'"
  end.

Example primes_ex:
  primes 4 = "x''''".
Proof. reflexivity. Qed.

Fixpoint sum_lengths (L : list free_var) : nat :=
  match L with
  | nil     => O
  | x :: L0 => String.length x + sum_lengths L0
  end.

Definition fresh (L : list free_var) := primes (sum_lengths L).

Theorem fresh_ok_helper: forall x L,
  String.length x > sum_lengths L ->
  ~ In x L.
Proof.
  induction L.
  - (* L = [] *) auto.
  - (* L = x0 :: L0 *)
    simpl.
    intros H Hcontra.
    inversion Hcontra.
    + (* a = x *) subst. lia.
    + (* In x L *) apply IHL. lia. assumption.
Qed.

Lemma length_app : forall s2 s1,
  String.length (s1 ++ s2) = String.length s1 + String.length s2.
  induction s1; crush.
Qed.

#[local] Hint Rewrite length_app : cpdt.

Lemma length_primes : forall n,
  String.length (primes n) = S n.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite length_app. rewrite IHn. simpl. lia.
Qed.

#[local] Hint Rewrite length_primes : cpdt.

(* the exact implementation of fresh name generation does *)
(* not matter, as long as it satisfies this theorem.      *)
Theorem fresh_ok: forall L,
  ~ In (fresh L) L.
Proof.
  intros. apply fresh_ok_helper. unfold fresh.
  rewrite length_primes. lia.
Qed.

Hint Resolve fresh_ok : core.

(* ------------------------------------------------------ *)

(* every well-typed term is locally closed *)
Lemma has_type_lclosed : forall G e t,
  G ⊢e e : t -> lclosed 0 e.
Proof. induction 1; eauto. Qed.

Lemma lclosed_open : forall n e,
  lclosed n e -> forall x, open_rec x n e = e.
Proof. induction 1; ln. Qed.

Hint Resolve lclosed_open has_type_lclosed : core.

Open Scope list_scope.

(* ---- lists as sets ----------------------------------- *)

Lemma In_cons1 : forall T (x x' : T) ls,
  x = x'
  -> In x (x' :: ls).
  crush.
Qed.

Lemma In_cons2 : forall T (x x' : T) ls,
  In x ls
  -> In x (x' :: ls).
  crush.
Qed.

Lemma In_app1 : forall T (x : T) ls2 ls1,
  In x ls1
  -> In x (ls1 ++ ls2).
  induction ls1; crush.
Qed.

Lemma In_app2 : forall T (x : T) ls2 ls1,
  In x ls2
  -> In x (ls1 ++ ls2).
  induction ls1; crush.
Qed.

Lemma fresh_ok_app1 : forall L1 L2,
  ~ In (fresh (L1 ++ L2)) L1.
  intros; generalize (fresh_ok (L1 ++ L2)); crush.
Qed.

Lemma fresh_ok_app2 : forall L1 L2,
  ~ In (fresh (L1 ++ L2)) L2.
  intros; generalize (fresh_ok (L1 ++ L2)); crush.
Qed.

Hint Resolve In_cons1 In_cons2 In_app1 In_app2 : core.

(* ---- substitution ------------------------------------ *)

Hint Resolve fresh_ok_app1 fresh_ok_app2 : core.

(* replace all occurrences of "x" in "e2" with "e1" *)
Fixpoint subst (x : free_var) (e1 e2 : exp) :=
  match e2 with
  | Const _     => e2
  | FreeVar y   => if string_dec x y then e1 else e2
  | BoundVar _  => e2
  | App e2a e2b => App (subst x e1 e2a) (subst x e1 e2b)
  | Abs e       => Abs (subst x e1 e)
  end.

(* variable "x" is fresh in context "G" *)
Definition disj x (G : ctx) := In x (map (@fst _ _) G) -> False.
Infix "#" := disj (no associativity, at level 90).

Ltac disj := crush;
  match goal with
    | [ _ : _ :: _ = ?G0 ++ _ |- _ ] => destruct G0
  end; crush; eauto.

Lemma lookup_disj' : forall x xt t G1,
  G1 ⊢v x : t
  -> forall G, x # G
    -> G1 = G ++ (x, xt) :: nil
    -> t = xt.
  unfold disj; induction 1; disj.
Qed.

Lemma lookup_disj : forall x xt t G,
  x # G
  -> G ++ (x, xt) :: nil ⊢v x : t
  -> t = xt.
  intros; eapply lookup_disj'; eauto.
Qed.

Lemma lookup_ne' : forall x xt G1 v t,
  G1 ⊢v v : t
  -> forall G, G1 = G ++ (x, xt) :: nil
    -> v <> x
    -> G ⊢v v : t.
  induction 1; disj.
Qed.

Lemma lookup_ne : forall x xt G v t,
  G ++ (x, xt) :: nil ⊢v v : t
  -> v <> x
  -> G ⊢v v : t.
  intros; eapply lookup_ne'; eauto.
Qed.

Hint Extern 1 (_ ⊢e _ : _) =>
  match goal with
    | [ H1 : _, H2 : _ |- _ ] => rewrite (lookup_disj H1 H2)
  end : core.
Hint Resolve lookup_ne : core.

Hint Extern 1 (@eq exp _ _) => f_equal : core.

(* ====================================================== *)

Lemma open_subst : forall x1 e1 x2 e2 n,
  lclosed n e1
  -> x1 <> x2
  -> open_rec x2 n (subst x1 e1 e2) = subst x1 e1 (open_rec x2 n e2).
  induction e2; ln.
Qed.

Lemma has_type_open_subst : forall G x1 e1 x2 e2 t,
  G ⊢e subst x1 e1 (open_rec x2 0 e2) : t
  -> x1 <> x2
  -> lclosed 0 e1
  -> G ⊢e open_rec x2 0 (subst x1 e1 e2) : t.
  intros; rewrite open_subst; eauto.
Qed.

Hint Resolve has_type_open_subst : core.

Lemma disj_push : forall x1 x2 (t : type) G,
  x1 # G
  -> x1 <> x2
  -> x1 # (x2, t) :: G.
  unfold disj; crush.
Qed.

Hint Resolve disj_push : core.

Lemma lookup_cons : forall x0 dom G x1 t,
  G ⊢v x1 : t
  -> ~ In x0 (map (@fst _ _) G)
  -> (x0, dom) :: G ⊢v x1 : t.
  induction 1; crush;
    match goal with
      | [ H : _ ⊢v _ : _ |- _ ] => inversion H
    end; crush.
Qed.

Hint Resolve lookup_cons : core.
Hint Unfold disj : core.


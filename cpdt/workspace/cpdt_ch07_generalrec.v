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

Section merge_sort.
  Variable A  : Type.
  Variable le : A -> A -> bool.

  (* inserts an element into a sorted list *)
  Fixpoint insert (x : A) (ls : list A) : list A :=
    match ls with
    | nil    => x :: nil
    | h :: t =>
        if le x h then x :: t
                  else h :: insert x t
    end.
  
  (* merge two sorted lists *)
  Fixpoint merge (ls1 ls2 : list A) : list A :=
    match ls1 with
    | nil      => ls2
    | h1 :: t1 => insert h1 (merge t1 ls2)
    end.
  
  (* split a list into two halves *)
  Fixpoint split (ls : list A) : list A * list A :=
    match ls with
    | nil           => (nil, nil)
    | h :: nil      => (h :: nil, nil)
    | h1 :: h2 :: t =>
        let (ls1, ls2) := split t in
          (h1 :: ls1, h2 :: ls2)
    end.

  (* Recursive call to merge_sort has principal argument equal to 
     "snd lss" instead of a subterm of "ls". *)
  Fail Fixpoint merge_sort (ls : list A) : list A :=
    if leb (length ls) 1
      then ls
      else let lss := split ls in
        merge (merge_sort (fst lss)) (merge_sort (snd lss)).

  Print well_founded.
  (* well_founded = fun (A : Type) (R : A -> A -> Prop) =>
       forall a : A, Acc R a
         : forall A : Type, (A -> A -> Prop) -> Prop
  *)
  Print Acc.
  (* Inductive Acc (A0 : Type) (R : A0 -> A0 -> Prop) (x : A0) : Prop :=
     | Acc_intro : (forall y : A0, (R y x) -> Acc R y) -> Acc R x.
  *)

  (* An element "x" is accessible for a relation "R" if every element
     less than "x" according to "R" is also accessible. *)

  CoInductive infinite_decreasing_chain A (R : A -> A -> Prop) : stream A -> Prop :=
    | ChainCons : forall x y s,
        infinite_decreasing_chain R (Cons y s) ->
        R y x ->
        infinite_decreasing_chain R (Cons x (Cons y s)).
  
  Example acc_nat_0:
    Acc Nat.lt 0.
  Proof.
    constructor.
    intros y Hy.
    inversion Hy.
  Qed.

  Example acc_nat:
    forall n, Acc lt n.
  Proof.
    (* manual proof *)
    intros n. induction n.
    - apply acc_nat_0.
    - constructor.
      Search (?a < (S ?n) -> ?a <= ?n).
      intros y Hy.
      apply Arith_prebase.lt_n_Sm_le in Hy.
      inversion Hy.
      + assumption.
      + subst. inversion IHn.
        Search (?a <= ?m -> ?a < (S ?m)).
        apply Arith_prebase.le_lt_n_Sm in H.
        apply H0 in H.
        apply H.
    (* automated *)
    Restart.
    intros n. induction n ; crush.
  Qed.

  CoFixpoint nat_stream (n : nat) :=
    Cons n (nat_stream (S n)).

  Example nat_stream_infinite_increase : forall n,
    infinite_decreasing_chain gt (nat_stream n).
  Proof.
    cofix nat_stream_infinite_increase.
    intros n.
    rewrite (frob_eq (nat_stream n)).
    simpl.
    rewrite (frob_eq (nat_stream (S n))).
    simpl.
    constructor.
  Abort.
  
  (* accessible element cannot be the beginning of any infinite decreasing chain *)
  Lemma no_bad_chains_lemma : forall A (R : A -> A -> Prop) x,
    Acc R x ->
    forall s, ~ infinite_decreasing_chain R (Cons x s).
  Proof.
    induction 1; crush;
    match goal with
      | [ H : infinite_decreasing_chain _ _ |- _ ] =>
        inversion H; eauto
    end.
  Qed.

  Theorem no_bad_chains : forall A (R : A -> A -> Prop),
    well_founded R ->
    forall s, ~ infinite_decreasing_chain R s.
  Proof.
    destruct s. 
    apply no_bad_chains_lemma.
    unfold well_founded in H. apply H.
  Qed.

  Print lt.
  (* Fix
   : forall (A : Type) (R : A -> A -> Prop),
       (well_founded R) ->
       forall P : A -> Type,
       (forall x : A, (forall y : A, (R y x) -> P y) -> P x) ->
       forall x : A, P x *)

  Definition length_order (ls1 ls2 : list A) :=
    length ls1 < length ls2.

  #[local] Hint Constructors Acc : core.

  Lemma length_order_wf' : forall len, forall ls, length ls <= len -> Acc length_order ls.
    unfold length_order; induction len; crush.
  Defined.

  Theorem length_order_wf : well_founded length_order.
    red; intro; eapply length_order_wf'; eauto.
  Defined.

  Lemma split_wf : forall len ls, 2 <= length ls <= len
    -> let (ls1, ls2) := split ls in
      length_order ls1 ls /\ length_order ls2 ls.
    unfold length_order; induction len; crush; do 2 (destruct ls; crush);
      destruct (le_lt_dec 2 (length ls));
        repeat (match goal with
                  | [ _ : length ?E < 2 |- _ ] => destruct E
                  | [ _ : S (length ?E) < 2 |- _ ] => destruct E
                  | [ IH : _ |- context[split ?L] ] =>
                    specialize (IH L); destruct (split L); destruct IH
                end; crush).
  Defined.

  Ltac split_wf := intros ls ?; intros; generalize (@split_wf (length ls) ls);
    destruct (split ls); destruct 1; crush.

  Lemma split_wf1 : forall ls, 2 <= length ls
    -> length_order (fst (split ls)) ls.
    split_wf.
  Defined.

  Lemma split_wf2 : forall ls, 2 <= length ls
    -> length_order (snd (split ls)) ls.
    split_wf.
  Defined.

  Hint Resolve split_wf1 split_wf2 : core.

  Definition merge_sort : list A -> list A.
    refine (Fix length_order_wf (fun _ => list A)
      (fun (ls : list A)
        (merge_sort : forall ls' : list A, length_order ls' ls -> list A) =>
        if le_lt_dec 2 (length ls)
          then let lss := split ls in
            merge (merge_sort (fst lss) _) (merge_sort (snd lss) _)
          else ls)); subst lss; eauto.
  Defined.
End merge_sort.

Eval compute in merge_sort leb (1 :: 2 :: 36 :: 8 :: 19 :: nil).

(* ====================================================== *)
Section computation.
  Variable A : Type.

  Definition computation :=
    { f : nat -> option A
      | forall (n : nat) (v : A),
          f n = Some v ->
          forall (n0 : nat), n0 >= n ->
          f n0 = Some v }.
  
  Print sig.

  
  Definition runTo (m : computation) (n : nat) (v : A) :=
    proj1_sig m n = Some v.
  
  Definition run (m : computation) (v : A) :=
    exists n, runTo m n v.
  
End computation.
(* ====================================================== *)

Hint Unfold runTo.

Ltac run' := unfold run, runTo in *; try red; crush;
  repeat (match goal with
            | [ _ : proj1_sig ?E _ = _ |- _ ] =>
              match goal with
                | [ x : _ |- _ ] =>
                  match x with
                    | E => destruct E
                  end
              end
            | [ |- context[match ?M with exist _ _ => _ end] ] => let Heq := fresh "Heq" in
              case_eq M; intros ? ? Heq; try rewrite Heq in *; try subst
            | [ _ : context[match ?M with exist _ _ => _ end] |- _ ] => let Heq := fresh "Heq" in
              case_eq M; intros ? ? Heq; try rewrite Heq in *; subst
            | [ H : forall n v, ?E n = Some v -> _,
                _ : context[match ?E ?N with Some _ => _ | None => _ end] |- _ ] =>
              specialize (H N); destruct (E N); try rewrite (H _ (eq_refl _)) by auto; try discriminate
            | [ H : forall n v, ?E n = Some v -> _, H' : ?E _ = Some _ |- _ ] => rewrite (H _ _ H') by auto
          end; simpl in *); eauto 7.

Ltac run := run'; repeat (match goal with
                            | [ H : forall n v, ?E n = Some v -> _
                                |- context[match ?E ?N with Some _ => _ | None => _ end] ] =>
                              specialize (H N); destruct (E N); try rewrite (H _ (eq_refl _)) by auto; try discriminate
                          end; run').

Lemma ex_irrelevant : forall P : Prop, P -> exists n : nat, P.
  exists 0; auto.
Qed.

Hint Resolve ex_irrelevant.

Require Import Max.

Theorem max_spec_le : forall n m, n <= m /\ max n m = m \/ m <= n /\ max n m = n.
  induction n; destruct m; simpl; intuition;
    specialize (IHn m); intuition.
Qed.

Ltac max := intros n m; generalize (max_spec_le n m); crush.

Lemma max_1 : forall n m, max n m >= n.
  max.
Qed.

Lemma max_2 : forall n m, max n m >= m.
  max.
Qed.

Hint Resolve max_1 max_2.

Lemma ge_refl : forall n, n >= n.
  crush.
Qed.

Hint Resolve ge_refl.

Hint Extern 1 => match goal with
                   | [ H : _ = exist _ _ _ |- _ ] => rewrite H
                 end.

(* ====================================================== *)
Section Bottom.
  Variable A : Type.

  Definition Bottom : computation A.
    exists (fun _ : nat => @None A); abstract run.
  Defined.

  Theorem run_Bottom : forall v, ~run Bottom v.
    run.
  Qed.
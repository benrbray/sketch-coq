(*
  Adam Chlipala,
  "Certified Programming with Dependent Types"
  Chapter 3: Inductive Types
  http://adam.chlipala.net/cpdt/html/Cpdt.InductiveTypes.html
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

(* ==== MUTUALLY INDUCTIVE TYPES ======================== *)

Inductive even_list : Set :=
  | ENil : even_list
  | ECons : nat -> odd_list -> even_list
with odd_list : Set :=
  | OCons : nat -> even_list -> odd_list.

Fixpoint elength (el : even_list) : nat :=
  match el with
  | ENil => O
  | ECons _ ol => S (olength ol)
  end
with olength (ol : odd_list) : nat :=
  match ol with
  | OCons _ el => S (elength el)
  end.

Fixpoint eapp (el1 el2 : even_list) : even_list :=
  match el1 with
  | ENil => el2
  | ECons n ol => ECons n (oapp ol el2)
  end
with oapp (ol : odd_list) (el : even_list) : odd_list :=
  match ol with
  | OCons n el' => OCons n (eapp el' el)
  end.

(* coq only generates non-mutual induction hypotheses by default *)
Check even_list_ind.
(* even_list_ind
	 : forall P : even_list -> Prop,
       (P ENil) ->
       (forall (n : nat) (o : odd_list), P (ECons n o)) ->
       forall e : even_list, P e *)

Theorem elength_eapp : forall el1 el2 : even_list,
  elength (eapp el1 el2) = plus (elength el1) (elength el2).
Proof.
  induction el1 ; crush.
Abort.

(* we can create mutual induction principles manually *)
Scheme even_list_mut := Induction for even_list Sort Prop
with   odd_list_mut  := Induction for odd_list Sort Prop.

Check even_list_mut.
Check odd_list_mut.

Theorem elength_eapp : forall el1 el2 : even_list,
  elength (eapp el1 el2) = plus (elength el1) (elength el2).
Proof.
  apply (even_list_mut
    (fun el1: even_list => forall el2: even_list,
      elength(eapp el1 el2) = plus (elength el1) (elength el2))
    (fun ol1: odd_list => forall el2: even_list,
      olength(oapp ol1 el2) = plus (olength ol1) (elength el2))
  ) ; crush.
Qed.

(* ==== REFLEXIVE TYPES ================================= *)

Inductive pformula : Set :=
  | Truth : pformula
  | Falsehood : pformula
  | Conjunction : pformula -> pformula -> pformula.

Fixpoint pformulaDenote (f : pformula) : Prop :=
  match f with
    | Truth             => True
    | Falsehood         => False
    | Conjunction f1 f2 => pformulaDenote f1 /\ pformulaDenote f2
  end.

(* first-order logic *)
Inductive formula : Set :=
  | Eq : nat -> nat -> formula
  | And : formula -> formula -> formula
  | ForAll : (nat -> formula) -> formula.

(* we can avoid needing to include a notion of variables in our syntax
   by using coq functions to encode the syntax of quantification *)

(* encoding of "forall x : nat, x = x" *)
Example forall_refl : formula :=
  ForAll (fun x => Eq x x).

Fixpoint formulaDenote (f : formula) : Prop :=
  match f with
  | Eq n1 n2 => n1 = n2
  | And f1 f2 => formulaDenote f1 /\ formulaDenote f2
  | ForAll f2 => forall n : nat, formulaDenote (f2 n)
  end.

(* swap the order of equality and conjunction *)
Fixpoint swapper (f : formula) : formula :=
  match f with
  | Eq n1 n2 => Eq n2 n1
  | And f1 f2 => And (swapper f2) (swapper f1)
  | ForAll f2 => ForAll (fun n => swapper (f2 n))
  end.

Theorem swapper_preserves_truth : forall f,
  formulaDenote f -> formulaDenote (swapper f).
Proof. induction f ; crush. Qed.

Check formula_ind.

(* ====================================================== *)

Print nat_rect.

Fixpoint nat_rect' (P : nat -> Type)
  (HO : P O)
  (HS : forall n, P n -> P (S n)) (n : nat) :=
  match n return P n with
    | O => HO
    | S n' => HS n' (nat_rect' P HO HS n')
  end.

(* ====================================================== *)

(* nested inductive definition, since both list and nat_tree are inductive *)
Inductive nat_tree : Set :=
  | NNode : nat -> list nat_tree -> nat_tree.

(* helper predicate *)
Section All.
  Variable T : Set.
  Variable P : T -> Prop.

  Fixpoint All (ls : list T) : Prop :=
    match ls with
    | nil      => True
    | cons h t => P h /\ All t
    end.
End All.

Section nat_tree_ind_nest.
  Variable P : nat_tree -> Prop.

  Hypothesis NNode_case:
    forall (n : nat) (ls : list nat_tree),
      All P ls -> P (NNode n ls).

  Fixpoint nat_tree_ind_nest (tr : nat_tree) : P tr :=
    match tr with
    | NNode n ls => NNode_case n ls
        ((fix list_nat_tree_ind (ls : list nat_tree) : All P ls :=
            match ls with
            | nil      => I
            | cons h t => conj (nat_tree_ind_nest h) (list_nat_tree_ind t)
            end) ls)
    end.
End nat_tree_ind_nest.

Section map.
  Variables T1 T2 : Set.
  Variable F : T1 -> T2.

  Fixpoint map (ls : list T1) : list T2 :=
    match ls with
    | nil => nil
    | cons h t => cons (F h) (map t)
    end.
End map.

Fixpoint sum (ls : list nat) : nat :=
  match ls with
  | nil => O
  | cons h t => plus h (sum t)
  end.

Fixpoint ntsize (tr : nat_tree) : nat :=
  match tr with
  | NNode _ trs => S (sum (map ntsize trs))
  end.

Fixpoint ntsplice (tr1 tr2 : nat_tree) : nat_tree :=
  match tr1 with
  | NNode n nil           => NNode n (cons tr2 nil)
  | NNode n (cons tr trs) => NNode n (cons (ntsplice tr tr2) trs)
  end.

Lemma plus_S : forall n1 n2 : nat,
  plus n1 (S n2) = S (plus n1 n2).
Proof. induction n1 ; crush. Qed.

#[local] Hint Rewrite plus_S : core.

Theorem ntsize_ntsplice : forall tr1 tr2 : nat_tree,
  ntsize (ntsplice tr1 tr2) = plus (ntsize tr1) (ntsize tr2).
Proof.
  induction tr1 using nat_tree_ind_nest ; crush.
  destruct ls ; crush.
Qed.

(* ==== MANUAL PROOFS ABOUT CONSTRUCTORS ================ *)

Theorem true_neq_false:
  true <> false.
Proof.
  (* discriminate is used to prove two constructors are not equal *)
  discriminate.
  (* ...but how does it work? *)
  Undo.
  red.     (* perform one step of reduction, unfolding <> *)
  intro H. (* introduce a hypothesis which we will prove to be a contradiction *)
  
  Definition toProp (b : bool) : Prop := if b then True else False.
  
  (* change lets us replace the goal with
     a computationally-equivalent term *)
  change (toProp false).

  rewrite <- H.
  simpl.
  trivial.
Qed.

Theorem S_inj : forall n m : nat,
  S n = S m -> n = m.
Proof.
  intros n m H.
  change (pred (S n) = pred (S m)).
  rewrite H.
  reflexivity.
Qed.




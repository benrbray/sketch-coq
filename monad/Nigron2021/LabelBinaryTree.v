(* Nigron & Dagand 2021, "Reaching for the Star: Tale of a Monad in Coq"          *)
(* https://drops.dagstuhl.de/opus/volltexte/2021/13924/pdf/LIPIcs-ITP-2021-29.pdf *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.

(* ====================================================== *)

Inductive Tree : Type -> Type :=
| Leaf : forall {X : Type}, X -> Tree X
| Node : forall {X : Type}, Tree X -> Tree X -> Tree X.

(* Q: how to implement this function, which labels *)
(* every node in the tree with a fresh integer label? *)
Definition challenge {X : Type} : Tree X -> Tree nat.
Admitted.

Example example_tree := Node (Leaf 5) (Node (Leaf 1) (Leaf 2)).

(* ====================================================== *)
Module FirstAttempt.

(* "Fresh X" is similar to "State nat x" in Haskell.  The state is a counter  *)
(* representing the next fresh variable.  Values of type `Fresh X` represent  *)
(* actions which produce a result of type "X", potentially with the effect of *)
(* incrementing the counter                                                   *) 
Definition Fresh X := nat -> X * nat.

(* The pure action simply produces a result of type "X", with no effect. *)
Definition pure {X : Type} (x : X): Fresh X :=
  fun n => (x, n).

(* The bind action sequences two effects, where the *)
(* second may depend on the result of the first.    *)
Definition bind {X Y : Type} (m : Fresh X) (f : X -> Fresh Y): Fresh Y :=
  fun n0 => let (x, n1) := m n0 in f x n1.

(* note: coq does not support nullary functions, hence the trivial input type *)
Definition fresh_nat : Fresh nat :=
  fun n => (n, 1+n).

Notation "'do' x '<-' e1 ';' e2" := (bind e1 (fun x => e2)) (at level 90).

Check Leaf.

Fixpoint label {X : Type} (t : Tree X): Fresh (Tree nat) :=
  match t with
  | Leaf _ =>
      do n <- fresh_nat ;
      pure (Leaf n)
  | Node l r =>
      do l <- label l ;
      do r <- label r ;
      pure (Node l r)
  end.

Lemma label_unique {X} : forall (t: Tree X) n0 ft n1,
  label t n0 = (ft, n1) ->
  n0 < n1.
Admitted.

End FirstAttempt.
(* ====================================================== *)
(* ====================================================== *)
Module SecondAttempt.

Inductive FreeFresh (X : Type) : Type :=
| Pure : X -> FreeFresh X
| OpFresh : unit -> (nat -> FreeFresh X) -> FreeFresh X.

Arguments Pure {X}.
Arguments OpFresh {X}.

Fixpoint bind {X Y : Type} (m : FreeFresh X) (f : X -> FreeFresh Y): FreeFresh Y :=
  match m with
  | Pure v      => f v 
  | OpFresh _ k => OpFresh tt (fun n => bind (k n) f)
  end.

Definition fresh_nat (tt : unit): FreeFresh nat := OpFresh tt Pure.

(* interpret a value of type "FreeFresh X" as an action which *)
(* uses an initial state to produce a final state as well as  *)
(* a result of type "X"                                       *)
Fixpoint eval {X : Type} (m : FreeFresh X): nat -> X * nat :=
  match m with
  | Pure v      => fun n => (v, n)
  | OpFresh _ k => fun n => eval (k n) (1 + n)
  end.

End SecondAttempt.
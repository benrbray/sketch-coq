Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".

From Coq Require Extraction.
From Coq Require Import Strings.String.
Require Import Coq.Arith.PeanoNat.

(* ====================================================== *)

Fixpoint isEven (n : nat) : bool :=
  match n with
  | 0 => true
  | 1 => false
  | S (S p0) => isEven p0
  end.

Compute (isEven 220).

(* ==== extraction ====================================== *)

Extraction Language Haskell.

(* use Haskell basic types *)
Require Import ExtrHaskellBasic.

(* use Haskell Nats *)
(* Require Import ExtrHaskellNatNum.
Extract Inductive Datatypes.nat => "Prelude.Integer" ["0" "succ"].
"(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))". *)

(* extract to file *)
Extraction "./Haskell/Extract.hs" isEven.
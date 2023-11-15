Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
Set Default Goal Selector "!".

Inductive tree : Set :=
  | Nil
  | Node (t1 : tree) (t2 : tree).

Fixpoint size  (t : tree) : nat :=
  match t with
  | Nil => 0
  | Node t1 t2 => 1 + size (t1) + size (t2)
  end.

Definition one_tree : tree := Node Nil Nil.

Definition three_tree : tree :=   Node one_tree one_tree.

Eval compute in size one_tree.

Eval compute in size three_tree.

Search max.
Fixpoint depth (t : tree) : nat :=
  match t with
  | Nil => 0
  | Node t1 t2 =>
      1 + max (depth t1) (depth t2)
  end.

Eval compute in depth one_tree.

Eval compute in depth three_tree.

Lemma leq_depth_size : forall (t : tree), depth t <= size t.
Proof.
 intros.
 induction t0.
 - reflexivity.
 - simpl. Search Peano.le.
   apply Peano.le_n_S. Search max.
   remember (le_max_l (depth t0_1)(depth t0_2)).
   inversion l.
  +
   Admitted.

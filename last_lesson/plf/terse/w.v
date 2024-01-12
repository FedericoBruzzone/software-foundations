(*
  In order to run this file you have to move it to the `vol-2` (PLF) directory.
 *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.

From PLF Require Import Equiv.

(** 1. Prove the following equivalence:*)

Theorem swap_if_branches : forall b c1 c2,
    cequiv
    <{ if b then c1 else c2 end }>
    <{ if ~ b then c2 else c1 end }>.
Proof.
  intros.
  unfold cequiv.
  intros.
  split.
  - intros.
    inversion H; subst.
    + apply E_IfFalse.
      -- simpl.
         rewrite H5.
         reflexivity.
      -- assumption.
    + apply E_IfTrue.
      -- simpl.
         rewrite H5.
         reflexivity.
      -- assumption.
  - intros.
    inversion H; subst.
    + apply E_IfFalse.
      -- simpl in H5.
         apply negb_true_iff in H5.
         assumption.
      -- assumption.
    + apply E_IfTrue.
      -- simpl in H5.
         apply negb_false_iff in H5.
         assumption.
      -- assumption.
Qed.

(** 2. Now, go back to Imp.v and the following definition*)

Print plus2.

(** and the theorem [ plus2_spec ] stating its correctness *)

Theorem plus2_spec : forall st n st',
  st X = n ->
  st =[ plus2 ]=> st' ->
  st' X = n + 2.
Proof.
  intros.
  inversion H0; subst.
  apply Maps.t_update_eq.
  Restart.
  intros.
  inversion H0; subst.
  (* info_auto. *)
  (* Show Proof. *)
  simple apply eq_refl.
Qed.
(* Print eq_refl. *)


(** What you have to do is state and prove a very similar result for
the program [subtract_slowly_body] *)

Print subtract_slowly_body.

Theorem subtract_slowly_body_spec : forall st st' n m,
  st X = n ->
  st Z = m ->
  st =[ subtract_slowly_body ]=> st' ->
  st' X = n - 1 /\ st' Z = m - 1.
Proof.
  intros.
  inversion H1; subst.
  inversion H4; subst.
  inversion H7; subst.
  split.
  - apply eq_refl.
  - apply eq_refl.
  (* info_auto. *)
Qed.


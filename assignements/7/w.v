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
Admitted.

(** 2. Now, go back to Imp.v and the following definition*)

Print plus2.

(** and the  theorem [ plus2_spec ] stating its correctness *)

Theorem plus2_spec : forall st n st',
  st X = n ->
  st =[ plus2 ]=> st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  inversion Heval. subst. clear Heval. simpl.
  apply Maps.t_update_eq.  Qed.


(** What you have to do is state and prove a very similar result for
the program [subtract_slowly_body] *)

Print subtract_slowly_body.



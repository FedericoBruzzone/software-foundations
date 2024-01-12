Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Arith.Arith.
From PLF Require Import SmallstepAM.
From PLF Require Import TypesAM.
From Hammer Require Import Tactics.
Import TM.

(** In this exercise, we explore different ways to talk about the
arithmetic language seen in Types. You can use [sauto], but you *must* pass it
the right arguments (ctrs/inv/use)*)

(**
Part 1.1: define a relational big step semantics for evaluating  [tm].
*)

Inductive eval : tm -> tm -> Prop :=
  | E_true: eval tru tru
  | E_false: eval fls fls
  | E_zero: eval zro zro
  | E_iszero_true: forall n, eval n zro -> eval (iszro n) tru
  | E_iszero_false: forall n p, eval n (scc p) -> eval (iszro n) fls
  | E_succ: forall n m, nvalue n -> eval n m -> eval (scc n) (scc m)
  | E_pred_zero: eval (prd zro) zro
  | E_pred_succ: forall n m, nvalue n -> eval n m -> eval (prd (scc n)) m
  (*ite constructor -> if then else*)
  | E_if_tru: forall b x y r, eval b tru -> eval x r -> eval (ite b x y) r
  | E_if_false: forall b x y r, eval b fls -> eval y r -> eval (ite b x y) r.

(** Part 1.2. now prove the value soundness theorem: *)

Inductive value: tm -> Prop :=
  | vb_tru: value tru
  | vb_fls: value fls
  | vn_zro: value zro
  | vn_succ: forall n, value n -> value (scc n).

Theorem vs: forall t v, eval t v -> value v.
Proof.
  intros.
  induction H; auto; constructor.
  - apply IHeval.
Qed.

(** If you have problems, perhaps
you need a different notion of [value]*)

(** 1.3. Show that [eval] is a [partial ] function*)

(* Locate deterministic. *)
Theorem eval_det: deterministic eval.
Admitted.

(** 1.4. Prove preservation: *)

Theorem preservationB : forall (t  : tm) T,
  has_type t T -> forall t',
  eval t t' ->
  has_type t T.
  Admitted.

 (** Part 2: write a ( functional) type checker. You will need to define
a _boolean_ test for [ty] equality. To make the code more concise, we suggest
 to use the let monadic notation used in the ImpCevalFun chapter. *)

 Fixpoint  typeof
     (t : tm) :  option ty.
 Admitted.

 (** 2.1 Prove that the relational version entails the functional one. *)

 Theorem rel2f: forall t T, has_type t T -> typeof t = Some T.
 Admitted.

 (** Extra credit: prove the other direction*)




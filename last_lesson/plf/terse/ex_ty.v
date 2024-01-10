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
  | E_true : eval tru tru
  | E_false : eval fls fls
  | E_zero : eval zro zro
  | E_Iszero0 : forall n, eval n zro -> eval (iszro n) tru
  | E_IszeroSucc : forall n m, eval n (scc m) -> eval (iszro n) fls
  | E_Succ : forall n m, eval n m -> eval (scc n) (scc m)
  | E_Pred0 : eval (prd zro) zro
  | E_PredSucc : forall n m, eval n m -> eval (prd (scc n)) m
  | E_IfTrue : forall b tb fb v, eval b tru -> eval tb v -> eval (ite b tb fb) v
  | E_IfFalse : forall b tb fb v, eval b fls -> eval fb v -> eval (ite b tb fb) v
  .

(** Part 1.2. now prove the value soundness theorem: *)
Theorem vs: forall t v, eval t v -> value v.
Proof.
  intros.
  induction H; subst.
  - unfold value. left. constructor.
  - unfold value. left. constructor.
  - unfold value. right. constructor.
  - unfold value. left. constructor.
  - unfold value. left. constructor.
  - unfold value. left.
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




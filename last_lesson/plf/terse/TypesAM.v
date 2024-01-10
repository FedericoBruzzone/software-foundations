(** * Types: Type Systems *)

(** New topic: _type systems_

      - This chapter: a toy type system for a toy language
           - typing relation
           - _progress_ and _preservation_ theorems

      - Next chapter: _simply typed lambda-calculus_
*)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Arith.Arith.
From PLF Require Import Maps.
From PLF Require Import SmallstepAM.
From Hammer Require Import Hammer.
Unset Hammer Vampire.
Hint Constructors multi : core.

(* ################################################################# *)
(** * Typed Arithmetic Expressions *)

(**
      - A simple toy language where expressions may fail with dynamic
        type errors
           - numbers (and arithmetic)
           - booleans (and conditionals)
      - Unlike Imp, we use a single syntactic category for both
        booleans and numbers
      - This means we can write _stuck_ terms like [5 + true] and [if
        42 then 0 else 1].
*)

(* ================================================================= *)
(** ** Syntax *)

(** Here is the syntax, informally:

    t ::= true
        | false
        | if t then t else t
        | 0
        | succ t
        | pred t
        | ? t
*)
(** And here it is formally: *)
Module TM.

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | ite : tm -> tm -> tm -> tm
  | zro : tm
  | scc : tm -> tm
  | prd : tm -> tm
  | iszro : tm -> tm.

Declare Custom Entry tm.
Declare Scope tm_scope.
Notation "'true'"  := true (at level 1): tm_scope.
Notation "'true'" := (tru) (in custom tm at level 0): tm_scope.
Notation "'false'"  := false (at level 1): tm_scope.
Notation "'false'" := (fls) (in custom tm at level 0): tm_scope.
Notation "<{ e }>" := e (e custom tm at level 99): tm_scope.
Notation "( x )" := x (in custom tm, x at level 99): tm_scope.
Notation "x" := x (in custom tm at level 0, x constr at level 0): tm_scope.
Notation "'0'" := (zro) (in custom tm at level 0): tm_scope.
Notation "'0'"  := 0 (at level 1): tm_scope.
Notation "'succ' x" := (scc x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'pred' x" := (prd x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'iszero' x" := (iszro x) (in custom tm at level 80, x custom tm at level 70): tm_scope.
Notation "'if' c 'then' t 'else' e" := (ite c t e)
                 (in custom tm at level 90, c custom tm at level 80,
                  t custom tm at level 80, e custom tm at level 80): tm_scope.
Local Open Scope tm_scope.

(** _Values_ are [<{true}>], [<{false}>], and numeric values... *)
Variant bvalue : tm -> Prop :=
  | bv_True : bvalue <{ true }>
  | bv_false : bvalue <{ false }>.

Inductive nvalue : tm -> Prop :=
  | nv_0 : nvalue <{ 0 }>
  | nv_succ : forall t, nvalue t -> nvalue <{ succ t }>.

Definition value (t : tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue : core.
Hint Unfold value : core.

(* ================================================================= *)
(** ** Operational Semantics *)

(**

                   -------------------------------                   (ST_IfTrue)
                   if true then t1 else t2 --> t1

                   -------------------------------                  (ST_IfFalse)
                   if false then t1 else t2 --> t2

                               t1 --> t1'
            ------------------------------------------------             (ST_If)
            if t1 then t2 else t3 --> if t1' then t2 else t3

                             t1 --> t1'
                         --------------------                          (ST_Succ)
                         succ t1 --> succ t1'

                           ------------                               (ST_Pred0)
                           pred 0 --> 0

                         numeric value v
                        -------------------                        (ST_PredSucc)
                        pred (succ v) --> v

                              t1 --> t1'
                         --------------------                          (ST_Pred)
                         pred t1 --> pred t1'

                          -----------------                         (ST_IsZero0)
                          iszero 0 --> true

                         numeric value v
                      -------------------------                  (ST_IszeroSucc)
                      iszero (succ v) --> false

                            t1 --> t1'
                       ------------------------                      (ST_Iszero)
                       iszero t1 --> iszero t1'
*)

(** ... and then formally: *)

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      <{ if true then t1 else t2 }> --> t1
  | ST_IfFalse : forall t1 t2,
      <{ if false then t1 else t2 }> --> t2
  | ST_If : forall c c' t2 t3,
      c --> c' ->
      <{ if c then t2 else t3 }> --> <{ if c' then t2 else t3 }>
  | ST_Succ : forall t1 t1',
      t1 --> t1' ->
      <{ succ t1 }> --> <{ succ t1' }>
  | ST_Pred0 :
      <{ pred 0 }> --> <{ 0 }>
  | ST_PredSucc : forall v,
      nvalue v ->
      <{ pred (succ v) }> --> v
  | ST_Pred : forall t1 t1',
      t1 --> t1' ->
      <{ pred t1 }> --> <{ pred t1' }>
  | ST_Iszero0 :
      <{ iszero 0 }> --> <{ true }>
  | ST_IszeroSucc : forall v,
       nvalue v ->
      <{ iszero (succ v) }> --> <{ false }>
  | ST_Iszero : forall t1 t1',
      t1 --> t1' ->
      <{ iszero t1 }> --> <{ iszero t1' }>

where "t '-->' t'" := (step t t').

Hint Constructors step : core.


(* ================================================================= *)
(** ** Normal Forms and Values *)

(** The first interesting thing to notice about this [step] relation
    is that the strong progress theorem from the [Smallstep]
    chapter fails here.  That is, there are terms that are normal
    forms (they can't take a step) but not values (they are not
    included in our definition of possible "results of reduction").
    Such terms are said to be _stuck_. *)

Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck : core.

(** However, although values and normal forms are _not_ the same in
    this language, the set of values is a subset of the set of normal
    forms.  This is important because it shows we did not accidentally
    define things so that some value could still take a step. *)

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  (* FILL IN HERE *) Admitted.

(* ================================================================= *)
(** ** Typing *)

(** _Types_ describe the possible shapes of values: *)

Inductive ty : Type :=
  | Bool : ty
  | Nat : ty.

(* ================================================================= *)
(** ** Typing Relations *)

(** The _typing relation_ [|- t \in T] relates terms to the types
    of their results:


                           ---------------                     (T_True)
                           |- true \in Bool

                          ---------------                      (T_False)
                          |- false \in Bool

             |- t1 \in Bool    |- t2 \in T    |- t3 \in T
             --------------------------------------------     (T_If)
                    |- if t1 then t2 else t3 \in T

                             --------------                    (T_0)
                             |- 0 \in Nat

                            |- t1 \in Nat
                          -----------------                    (T_Succ)
                          |- succ t1 \in Nat

                            |- t1 \in Nat
                          -----------------                    (T_Pred)
                          |- pred t1 \in Nat

                            |- t1 \in Nat
                        --------------------                 (T_Iszero)
                          |-  iszero t1 \in Bool
*)

Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_True :
       |- <{ true }> \in Bool
  | T_False :
       |- <{ false }> \in Bool
  | T_If : forall t1 t2 t3 T,
       |- t1 \in Bool ->
       |- t2 \in T ->
       |- t3 \in T ->
       |- <{ if t1 then t2 else t3 }> \in T
  | T_0 :
       |- <{ 0 }> \in Nat
  | T_Succ : forall t1,
       |- t1 \in Nat ->
       |- <{ succ t1 }> \in Nat
  | T_Pred : forall t1,
       |- t1 \in Nat ->
       |- <{ pred t1 }> \in Nat
  | T_Iszero : forall t1,
       |- t1 \in Nat ->
       |- <{ iszero t1 }> \in Bool

where "'|-' t '\in' T" := (has_type t T).

Hint Constructors has_type : core.

Example has_type_1 :
  |- <{ if false then 0 else (succ 0) }> \in Nat.
Proof.
  apply T_If.
  - apply T_False.
  - apply T_0.
  - apply T_Succ. apply T_0.
    (* Since we've included all the constructors of the typing relation
    in the hint database, the [auto] tactic can actually find this
    proof automatically. *)
    Restart.
    auto.
Qed.

(** Typing is a _conservative_ (_static_) approximation to
    behavior.

    In particular, a term can be ill typed even though it steps to
    something well typed. *)

Example has_type_not :
  ~ ( |- <{ if false then 0 else true}> \in Bool ).
Proof.
  sauto inv: has_type.  Qed.

(* ----------------------------------------------------------------- *)
(** *** Canonical forms *)

(** The following two lemmas capture the fundamental property that the
    definitions of boolean and numeric values agree with the typing
    relation. *)

Lemma bool_canonical : forall t,
  |- t \in Bool -> value t -> bvalue t.
Proof.
  intros t HT [Hb | Hn].
  - assumption.
  - destruct Hn as [ | Hs].
    + inversion HT.
    + inversion HT.
Qed.

Lemma nat_canonical : forall t,
  |- t \in Nat -> value t -> nvalue t.
Proof.
  intros t HT [Hb | Hn].
  - inversion Hb; subst; inversion HT.
  - assumption.
Qed.

(** All these proofs can be done with [sauto]*)

(* ================================================================= *)
(** ** Progress *)

(** The typing relation enjoys two critical properties.  The first is
    that well-typed normal forms are not stuck -- or conversely, if a
    term is well typed, then either it is a value or it can take at
    least one step.  We call this _progress_. *)

Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t --> t'.

Proof.
  intros t T HT.
  induction HT; auto.
  (* The cases that were obviously values, like T_True and
     T_False, are eliminated immediately by auto *)
  - (* T_If *)
    right. destruct IHHT1.
    + (* t1 is a value *)
    apply (bool_canonical t1 HT1) in H.
    destruct H.
      * exists t2. auto.
      * exists t3. auto.
    + (* t1 can take a step *)
      destruct H as [t1' H1].
      exists (<{ if t1' then t2 else t3 }>). auto.
  (* FILL IN HERE *) Admitted.
(** For the record, the theorem can be automatized via
[    intros t T HT;  induction HT;  sauto depth: 1 use:nat_canonical]

but it takes around 6 secs
 *)

(* ================================================================= *)
(** ** Type Preservation *)

(** The second critical property of typing is that, when a well-typed
    term takes a step, the result is a well-typed term (of the same type). *)

Theorem preservation : forall t  T,
  |- t \in T -> forall t',
  t --> t' ->
  |- t' \in T.

Proof.
  intros t  T HT.
  induction HT;
         (* every case needs to introduce a couple of things *)
         intros t' HE;
         (* and we can deal with several impossible
            cases all at once *)
         try solve_by_invert.
    - (* T_If *) inversion HE; subst; clear HE.
      + (* ST_IFTrue *) assumption.
      + (* ST_IfFalse *) assumption.
      + (* ST_If *) apply T_If; try assumption.
        apply IHHT1; assumption.
    (* FILL IN HERE *) Admitted.

(** There is a neat, one line proof with [sauto]. *)


(* ================================================================= *)
(** ** Type Soundness *)

(** Putting progress and preservation together, we see that a
    well-typed term can never reach a stuck state.  *)

Definition multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Corollary type_soundness : forall t t' T,
  |- t \in T ->
  t -->* t' ->
  |- t' \in T.
Proof.
  intros t t' T HT P. induction P; eauto using preservation.
  Qed.

Corollary soundness : forall t t' T,
  |- t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
  intros t t' T HT P.
  apply (type_soundness _ t' T) in HT; try assumption.
  unfold stuck. intros [R S].
  apply progress in HT. destruct HT; auto.
Qed.

End TM.

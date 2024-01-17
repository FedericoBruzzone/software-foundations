(** * Smallstep: Small-step Operational Semantics *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From PLF Require Import Maps.
From PLF Require Import Imp.
From Hammer Require Import Hammer.
Unset Hammer Vampire.
Definition FILL_IN_HERE := <{True}>.

(* ================================================================= *)
(** ** Big-step Evaluation

    Our semantics for Imp is written in the so-called
    "big-step" style...

    Evaluation rules take an expression (or command) to a final answer
    "all in one step":

      2 + 2 + 3 * 4 ==> 16

  Similarly, Hoare logic uses big-step semantics to talk about the
  relationship between the starting and final state (if any) of a
  program.

  But big-step semantics makes it hard to talk about what
  happens _along the way_...
*)

(* ================================================================= *)
(** ** Small-step Evaluation

    _Small-step_ style: Alternatively, we can show how to "reduce"
    an expression to a simpler form by performing a single step
    of computation:

      2 + 2 + 3 * 4
      --> 2 + 2 + 12
      --> 4 + 12
      --> 16

    Advantages of the small-step style include:

        - Finer-grained "abstract machine", closer to real
          implementations

        - Extends smoothly to concurrent languages and languages
          with other sorts of _computational effects_.

        - Separates _divergence_ (nontermination) from
          _stuckness_ (run-time error)

*)

(* ################################################################# *)
(** * A Toy Language *)

(** A minimal fragment: *)

Inductive tm : Type :=
  | C : nat -> tm         (* Constant *)
  | P : tm -> tm -> tm.   (* Plus *)

(** Big-step evaluation as a function *)

Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P t1 t2 => evalF t1 + evalF t2
  end.

(* ----------------------------------------------------------------- *)
(** *** Big-step evaluation as a relation

                               ---------                               (E_Const)
                               C n ==> n

                               t1 ==> v1
                               t2 ==> v2
                           -------------------                         (E_Plus)
                           P t1 t2 ==> v1 + v2
*)

Reserved Notation " t '==>' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_Const : forall n,
      C n ==> n
  | E_Plus : forall t1 t2 v1 v2,
      t1 ==> v1 ->
      t2 ==> v2 ->
      P t1 t2 ==> (v1 + v2)

where " t '==>' n " := (eval t n).

Module SimpleArith1.

(* ----------------------------------------------------------------- *)
(** *** Small-step evaluation relation

    
                     -------------------------------        (ST_PlusConstConst)
                     P (C v1) (C v2) --> C (v1 + v2)

                              t1 --> t1'
                         --------------------                        (ST_Plus1)
                         P t1 t2 --> P t1' t2

                              t2 --> t2'
                      ----------------------------                   (ST_Plus2)
                      P (C v1) t2 --> P (C v1) t2'
*)
(** Notice:

       - each step reduces the _leftmost_ [P] node that is ready to go

             - first rule tells how to rewrite this node

             - second and third rules tell where to find it

       - constants are not related to anything (i.e., they do not step
         to anything)
*)
(* ----------------------------------------------------------------- *)
(** *** Small-step evaluation in Coq *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall v1 v2,
      P (C v1) (C v2) --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
      t2 --> t2' ->
      P (C v1) t2 --> P (C v1) t2'

  where " t '-->' t' " := (step t t').

(* ----------------------------------------------------------------- *)
(** *** Examples *)

(** If [t1] can take a step to [t1'], then [P t1 t2] steps
    to [P t1' t2]: *)

Example test_step_1 :
      P
        (P (C 1) (C 3))
        (P (C 2) (C 4))
      -->
      P
        (C 4)
        (P (C 2) (C 4)).
Proof.
  apply ST_Plus1. apply ST_PlusConstConst.  Qed.

End SimpleArith1.

(* ################################################################# *)
(** * Relations *)

(** A _binary relation_ on a set [X] is a family of propositions
    parameterized by two elements of [X] -- i.e., a proposition about
    pairs of elements of [X].  *)

Definition relation (X : Type) := X -> X -> Prop.

(** The step relation [-->] is an example of a relation on [tm]. *)

(* ----------------------------------------------------------------- *)
(** *** Determinism *)

(** One simple property of the [-->] relation is that, like the
    big-step evaluation relation for Imp, it is _deterministic_.

    _Theorem_: For each [t], there is at most one [t'] such that [t]
    steps to [t'] ([t --> t'] is provable). *)

(** Formally: *)

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1  : X, R x y1 -> forall y2, R x y2 -> y1 = y2.

Module SimpleArith2.
Import SimpleArith1.

Theorem step_deterministic:
  deterministic step.
Proof.
  unfold deterministic. intros x y1  Hy1.
  induction Hy1; intros y2 Hy2.
    - (* ST_PlusConstConst *) inversion Hy2; subst.
    + (* ST_PlusConstConst *) reflexivity.
    + (* ST_Plus1 *) inversion H2.
    + (* ST_Plus2 *) inversion H2.
  - (* ST_Plus1 *) inversion Hy2; subst.
    + (* ST_PlusConstConst *)
      inversion Hy1.
    + (* ST_Plus1 *)
      apply IHHy1 in H2. rewrite H2. reflexivity.
    + (* ST_Plus2 *)
      inversion Hy1.
  - (* ST_Plus2 *) inversion Hy2; subst.
    + (* ST_PlusConstConst *)
      inversion Hy1.
    + (* ST_Plus1 *) inversion H2.
    + (* ST_Plus2 *)
      apply IHHy1 in H2. rewrite H2. reflexivity.
Qed.

End SimpleArith2.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.

(** The proof of the previous theorem can now be simplified if we use [sauto] *)

Module SimpleArith3.
Import SimpleArith1.

Theorem step_deterministic_alt: deterministic step.
Proof.
  intros x y1  Hy1.
  induction Hy1; sauto.
Qed.

End SimpleArith3.

(* ================================================================= *)
(** ** Values *)

(** It can be useful to think of the [-->] relation as defining an
    _abstract machine_:

      - At any moment, the _state_ of the machine is a term.

      - A _step_ of the machine is an atomic unit of computation --
        here, a single "add" operation.

      - The _halting states_ of the machine are ones where there is no
        more computation to be done.

    We can then _execute_ a term [t] as follows:

      - Take [t] as the starting state of the machine.

      - Repeatedly use the [-->] relation to find a sequence of
        machine states, starting with [t], where each state steps to
        the next.

      - When no more reduction is possible, "read out" the final state
        of the machine as the result of execution. *)

(** Final states of the machine are terms of the form
    [C n] for some [n].  We call such terms _values_. *)

Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).

(** This gives a more elegant way of writing the [ST_Plus2] rule:

    
                     -------------------------------        (ST_PlusConstConst)
                     P (C v1) (C v2) --> C (v1 + v2)

                              t1 --> t1'
                         --------------------                        (ST_Plus1)
                         P t1 t2 --> P t1' t2

                               value v1
                              t2 --> t2'
                         --------------------                        (ST_Plus2)
                         P v1 t2 --> P v1 t2'
*)

(** Again, variable names carry important information:
       - [v1] ranges only over values
       - [t1] and [t2] range over arbitrary terms

    So the [value] hypothesis in the last rule is actually redundant
    in the informal presentation: The naming convention tells us where
    to add it when translating the informal rule to Coq.  We'll keep
    it for now, but in later chapters we'll elide it. *)

(**  Here are the formal rules: *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall v1 v2,
          P (C v1) (C v2)
      --> C (v1 + v2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 --> t1' ->
        P t1 t2 --> P t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        value v1 ->                     (* <--- n.b. *)
        t2 --> t2' ->
        P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

(* ================================================================= *)
(** ** Strong Progress and Normal Forms *)

(** _Theorem_ (_Strong Progress_): If [t] is a term, then either [t]
    is a value or else there exists a term [t'] such that [t --> t']. *)

(**  _Proof_: By induction on [t].

    - Suppose [t = C n]. Then [t] is a value.

    - Suppose [t = P t1 t2], where (by the IH) [t1] either is a value
      or can step to some [t1'], and where [t2] is either a value or
      can step to some [t2']. We must show [P t1 t2] is either a value
      or steps to some [t'].

      - If [t1] and [t2] are both values, then [t] can take a step, by
        [ST_PlusConstConst].

      - If [t1] is a value and [t2] can take a step, then so can [t],
        by [ST_Plus2].

      - If [t1] can take a step, then so can [t], by [ST_Plus1].  []

   Or, formally: *)

Theorem strong_progress : forall t,
  value t \/ (exists t', t --> t').
Proof.
  induction t.
  - (* C *) left. apply v_const.
  - (* P *) right. destruct IHt1 as [IHt1 | [t1' Ht1] ].
    + (* l *) destruct IHt2 as [IHt2 | [t2' Ht2] ].
      * (* l *) inversion IHt1. inversion IHt2.
        exists (C (n + n0)).
        apply ST_PlusConstConst.
      * (* r *)
        exists (P t1 t2').
        apply ST_Plus2. apply IHt1. apply Ht2.
    + (* r *)
      exists (P t1' t2).
      apply ST_Plus1. apply Ht1.
      Restart.
      induction t; sauto.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Normal forms *)

(** The idea of "making progress" can be extended to tell us something
    interesting about values: they are exactly the terms that _cannot_
    make progress in this sense.

    To state this observation formally, let's begin by giving a name
    to "terms that cannot make progress", for an _arbitrary_ relation
    [R].  We'll call them _normal forms_.  *)

Definition normal_form {X : Type}
              (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

(* ----------------------------------------------------------------- *)
(** *** Values vs. normal forms

    (In this language, though not generally) normal forms and
    values coincide: *)

Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Proof.
  unfold normal_form. intros v H. destruct H.
  intros contra. destruct contra. inversion H.
Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof. (* a corollary of [strong_progress]... *)
  unfold normal_form. intros t H.
  destruct (strong_progress t) as [G | G].
  - (* l *) apply G.
  - (* r *) contradiction.
    Restart.
    sfirstorder use: strong_progress unfold: normal_form.
Qed.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
  split. apply nf_is_value. apply value_is_nf.
Qed.

(** Why is this interesting?

    Because [value] is a syntactic concept -- it is defined by looking
    at the way a term is written -- while [normal_form] is a semantic
    one -- it is defined by looking at how the term steps.

    It is not obvious that these concepts should characterize the same
    set of terms!  *)

(* ################################################################# *)
(** * Multi-Step Reduction *)

(** We can now use the single-step relation and the concept of value
    to formalize an entire _execution_ of the abstract machine.

    First, we define a _multi-step reduction relation_ [-->*] to
    capture the intermediate results of a computation. *)

(** Since we'll want to reuse the idea of multi-step reduction many
    times, let's pause and define it generically.

    Given a relation [R] (e.g., the step relation [-->]), we define a
    relation [multi R], called the _multi-step closure of [R]_ as
    follows. 

---------------- multi_refl
multi R x x 

R x y            multi R y z 
---------------------------------- multi_step
multi R x z



*)

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

(** The effect of this definition is that [multi R] relates two
    elements [x] and [y] if

       - [x = y], or
       - [R x y], or
       - there is some nonempty sequence [z1], [z2], ..., [zn] such that

           R x z1
           R z1 z2
           ...
           R zn y.

    Intuitively, if [R] describes a single-step of computation, then
    [z1] ... [zn] are the intermediate steps of computation that get
    us from [x] to [y]. *)

(** We write [-->*] for the [multi step] relation on terms. *)

Notation " t '-->*' t' " := (multi step t t') (at level 40).

(** The relation [multi R] has several crucial properties.

    First, it is obviously _reflexive_ (that is, [forall x, multi R x
    x]).  In the case of the [-->*] (i.e., [multi step]) relation, the
    intuition is that a term can execute to itself by taking zero
    steps of execution. *)

(** Second, it contains [R] -- that is, single-step executions are a
    particular case of multi-step executions.  (It is this fact that
    justifies the word "closure" in the term "multi-step closure of
    [R].") *)

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y. apply H. apply multi_refl.
Qed.

(** Third, [multi R] is _transitive_. *)

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - (* multi_refl *) assumption.
    - (* multi_step *)
      apply multi_step with y. assumption.
      apply IHG. assumption.
Qed.

(** In particular, for the [multi step] relation on terms, if
    [t1 -->* t2] and [t2 -->* t3], then [t1 -->* t3]. *)

(* ================================================================= *)
(** ** Examples *)

(** Here's a specific instance of the [multi step] relation: *)

Lemma test_multistep_1:
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
   -->*
      C 9.
Proof.
  eapply multi_step. { apply ST_Plus1. apply ST_PlusConstConst. }
  eapply multi_step. { apply ST_Plus2. apply v_const.
                       apply ST_PlusConstConst. }
  eapply multi_step. { apply ST_PlusConstConst. }
  apply multi_refl.
  Restart.
  sauto.
Qed.

(* ================================================================= *)
(** ** Normal Forms Again *)

(** If [t] reduces to [t'] in zero or more steps and [t'] is a
    normal form, we say that "[t'] is a normal form of [t]." *)

Definition step_normal_form := normal_form step.

Definition normal_form_of (t t' : tm) :=
  (t -->* t' /\ step_normal_form t').

(** Notice:

      - single-step reduction is deterministic;

      - so, if [t] can reach a normal form, then this normal form is unique;

      - so we can pronounce [normal_form t t'] as "[t'] is _the_
        normal form of [t]." *)

(** Indeed, something stronger is true (for this language):

       - the reduction of _any_ term [t] will eventually reach a
         normal form

    We say the [step] relation is _normalizing_. *)

Definition normalizing {X : Type} (R : relation X) :=
  forall t, exists t',
    (multi R) t t' /\ normal_form R t'.

(** we can indeed prove that our definition of [step] admits
one normalizing sequence:

[Theorem step_normalizing : normalizing step.]

The not too difficult proof can be found in the full version of the book.
*)

(* ================================================================= *)
(** ** Equivalence of Big-Step and Small-Step *)

(** Having defined the operational semantics of our tiny programming
    language in two different ways (big-step and small-step), it makes
    sense to ask whether these definitions actually define the same
    thing! *)

Theorem eval__multistep : forall t n,
  t ==> n -> t -->* C n.

(** The key ideas in the proof can be seen in the following picture:

       P t1 t2 -->            (by ST_Plus1)
       P t1' t2 -->           (by ST_Plus1)
       P t1'' t2 -->          (by ST_Plus1)
       ...
       P (C v1) t2 -->        (by ST_Plus2)
       P (C v1) t2' -->       (by ST_Plus2)
       P (C v1) t2'' -->      (by ST_Plus2)
       ...
       P (C v1) (C v2) -->    (by ST_PlusConstConst)
       C (v1 + v2)
*)

(** That is, the multistep reduction of a term of the form [P t1 t2]
    proceeds in three phases:
       - First, we use [ST_Plus1] some number of times to reduce [t1]
         to a normal form, which must (by [nf_same_as_value]) be a
         term of the form [C v1] for some [v1].
       - Next, we use [ST_Plus2] some number of times to reduce [t2]
         to a normal form, which must again be a term of the form [C
         v2] for some [v2].
       - Finally, we use [ST_PlusConstConst] one time to reduce [P (C
         v1) (C v2)] to [C (v1 + v2)]. 

To formalize this intuition, you'll need  some congruence
    lemmas  plus some basic
    properties of [-->*]: that it is reflexive, transitive, and
    includes [-->].*)

Proof.
  (* FILL IN HERE *) Admitted.

(** For the other direction, we need one lemma, which establishes a
    relation between single-step reduction and big-step evaluation. *)

Lemma step__eval : forall t t' n,
     t --> t' ->
     t' ==> n ->
     t  ==> n.
Proof.
  intros t t' n Hs. generalize dependent n.
  (* FILL IN HERE *) Admitted.

(** The fact that small-step reduction implies big-step evaluation is now
    straightforward to prove.

    The proof proceeds by induction on the multi-step reduction
    sequence that is buried in the hypothesis [normal_form_of t t']. *)

Theorem multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t ==> n.
Proof.
  (* FILL IN HERE *) Admitted.

(* ################################################################# *)
(** * Small-Step Imp *)

(** Now for a more serious example: a small-step version of the Imp
    operational semantics. *)

(**  We start with an inductive definition of arithmetic values -- we do not need
the same for booleans

Then we introduce relational definitions for small-step reduction relations for arithmetic and
    boolean expressions are straightforward extensions of the tiny
    language we've been working up to now.   *)

Inductive aval : aexp -> Prop :=
| av_num : forall n, aval (ANum n).


(* ----------------------------------------------------------------- *)
(** *** Small-step evaluation relation for arithmetic expressions *)
(**[[[
                             -----------------                          (AS_Id)
                             i / st --> (st i)

                              a1 / st --> a1'
                         -------------------------                   (AS_Plus1)
                         a1 + a2 / st --> a1' + a2

                        aval v1       a2 / st --> a2'
                    -------------------------------------            (AS_Plus2)
                          v1 + a2 / st --> v1 + a2'

                        --------------------------                    (AS_Plus)
                        v1 + v2 / st --> (v1 + v2)

                              a1 / st --> a1'
                          -------------------------                 (AS_Minus1)
                          a1 - a2 / st --> a1' - a2

                        aval v1       a2 / st --> a2'
                        ----------------------------                (AS_Minus2)
                           v1 - a2 / st --> v1 - a2'

                        --------------------------                   (AS_Minus)
                        v1 - v2 / st --> (v1 - v2)

                              a1 / st --> a1'
                          -------------------------                  (AS_Mult1)
                          a1 * a2 / st --> a1' * a2

                        aval v1       a2 / st --> a2'
                        ----------------------------                 (AS_Mult2)
                           v1 * a2 / st --> v1 * a2'

                        --------------------------                    (AS_Mult)
                        v1 * v2 / st --> (v1 * v2)
*)

Reserved Notation " a '/' st '-->a' a' "
                  (at level 40, st at level 39).

Inductive astep (st : state) : aexp -> aexp -> Prop :=
  | AS_Id : forall (i : string),
      i / st -->a (st i)
  | AS_Plus1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 + a2 }> / st -->a <{ a1' + a2 }>
  | AS_Plus2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 + a2 }>  / st -->a <{ v1 + a2' }>
  | AS_Plus : forall (v1 v2 : nat),
      <{ v1 + v2 }> / st -->a (v1 + v2)
  | AS_Minus1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 - a2 }> / st -->a <{ a1' - a2 }>
  | AS_Minus2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 - a2 }>  / st -->a <{ v1 - a2' }>
  | AS_Minus : forall (v1 v2 : nat),
      <{ v1 - v2 }> / st -->a (v1 - v2)
  | AS_Mult1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 * a2 }> / st -->a <{ a1' * a2 }>
  | AS_Mult2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 * a2 }>  / st -->a <{ v1 * a2' }>
  | AS_Mult : forall (v1 v2 : nat),
      <{ v1 * v2 }> / st -->a (v1 * v2)

    where " a '/' st '-->a' a' " := (astep st a a').

(* ----------------------------------------------------------------- *)
(** *** Small-step evaluation relation for boolean expressions *)
(**[[[
                          a1 / st --> a1'
                     -------------------------                     (BS_Eq1)
                     a1 = a2 / st --> a1' = a2

                    aval v1       a2 / st --> a2'
                    -----------------------------                  (BS_Eq2)
                      v1 = a2 / st --> v1 = a2'

      -----------------------------------------------------        (BS_Eq)
      v1 = v2 / st --> (if (v1 =? v2) then true else false)

                            a1 / st --> a1'
                      ---------------------------                  (BS_LtEq1)
                      a1 <= a2 / st --> a1' <= a2

                    aval v1       a2 / st --> a2'
                   ------------------------------                  (BS_LtEq2)
                    v1 <= a2 / st --> v1 <= a2'

      -------------------------------------------------------      (BS_LtEq)
      v1 <= v2 / st --> (if (v1 <=? v2) then true else false)

                           b1 / st --> b1'
                          -----------------                        (BS_NotStep)
                          ~b1 / st --> ~b1'

                        ---------------------                      (BS_NotTrue)
                        ~ true / st --> false

                        ---------------------                      (BS_NotFalse)
                        ~ false / st --> true

                            b1 / st --> b1'
                      ---------------------------                  (BS_AndStep)
                      b1 && b2 / st --> b1' && b2

                           b2 / st --> b2'
                    -------------------------------                (BS_AndTrueStep)
                    true && b2 / st --> true && b2'

                      --------------------------                   (BS_AndFalse)
                      false && b2 / st --> false

                      --------------------------                   (BS_AndTrueTrue)
                      true && true / st --> true

                     ----------------------------                  (BS_AndTrueFalse)
                     true && false / st --> false
*)
Reserved Notation " b '/' st '-->b' b' "
                  (at level 40, st at level 39).

Inductive bstep (st : state) : bexp -> bexp -> Prop :=
| BS_Eq1 : forall a1 a1' a2,
    a1 / st -->a a1' ->
    <{ a1 = a2 }> / st -->b <{ a1' = a2 }>
| BS_Eq2 : forall v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    <{ v1 = a2 }> / st -->b <{ v1 = a2' }>
| BS_Eq : forall (v1 v2 : nat),
    <{ v1 = v2 }> / st -->b
    (if (v1 =? v2) then <{ true }> else <{ false }>)
| BS_LtEq1 : forall a1 a1' a2,
    a1 / st -->a a1' ->
    <{ a1 <= a2 }> / st -->b <{ a1' <= a2 }>
| BS_LtEq2 : forall v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    <{ v1 <= a2 }> / st -->b <{ v1 <= a2' }>
| BS_LtEq : forall (v1 v2 : nat),
    <{ v1 <= v2 }> / st -->b
    (if (v1 <=? v2) then <{ true }> else <{ false }>)
| BS_NotStep : forall b1 b1',
    b1 / st -->b b1' ->
    <{ ~ b1 }> / st -->b <{ ~ b1' }>
| BS_NotTrue  : <{ ~ true }> / st  -->b <{ false }>
| BS_NotFalse : <{ ~ false }> / st -->b <{ true }>
| BS_AndStep : forall b1 b1' b2,
    b1 / st -->b b1' ->
    <{ b1 && b2 }> / st -->b <{ b1' && b2 }>
| BS_AndTrueStep : forall b2 b2',
    b2 / st -->b b2' ->
    <{ true && b2 }> / st -->b <{ true && b2' }>
| BS_AndFalse : forall b2,
    <{ false && b2 }> / st -->b <{ false }>
| BS_AndTrueTrue  : <{ true && true  }> / st -->b <{ true }>
| BS_AndTrueFalse : <{ true && false }> / st -->b <{ false }>

where " b '/' st '-->b' b' " := (bstep st b b').

(** The semantics of commands is the interesting part.  We need two
    small tricks to make it work:

       - We use [skip] as a "command value" -- i.e., a command that
         has reached a normal form.

            - An assignment command reduces to [skip] (and an updated
              state).

            - The sequencing command waits until its left-hand
              subcommand has reduced to [skip], then throws it away so
              that reduction can continue with the right-hand
              subcommand.

       - We reduce a [while] command by transforming it into a
         conditional followed by the same [while].

     - We could have given a similar presentation using _big_ step for
arithmetic and boolean expressions.

  - It is possible to show that big and the reflexive and transitive
  closure of small step presentations of Imp semantics, coincide but
  it's lengthy.  

*)

(* ----------------------------------------------------------------- *)
(** *** Small-step evaluation relation for commands *)
(**[[[
                              a1 / st --> a1'
                     ------------------------------                           (CS_AsgnStep)
                     i := a1 / st --> i := a1' / st

                   --------------------------------------                     (CS_Asgn)
                   i := n / st --> skip / (i !-> n ; st)

                           c1 / st --> c1' / st'
                     -------------------------------                          (CS_SeqStep)
                     c1 ; c2 / st --> c1' ; c2 / st'

                        --------------------------                            (CS_SeqFinish)
                        skip ; c2 / st --> c2 / st

                              b1 / st --> b1'
               ---------------------------------------------------            (CS_IfStep)
               if b1 then c1 else c2 end / st -->
                                   if b1' then c1 else c2 end / st

              ---------------------------------------------                   (CS_IfTrue)
              if true then c1 else c2 end / st --> c1 / st

              ----------------------------------------------                  (CS_IfFalse)
              if false then c1 else c2 end / st --> c2 / st

              -----------------------------------------------------------------    (CS_While)
              while b1 do c1 end / st -->
                         if b1 then (c1; while b1 do c1 end) else skip end / st
*)

(** We can distinguish different outcomes of the computation

- when it terminates

- when it diverges

- when it "goes wrong", if it cannot reduce and is not a final
  configuration, that is, c' <> SKIP.

We can show that this relation is

- deterministic (easy)

- coincides with big step evalution (long) *)

Reserved Notation " t '/' st '-->' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AsgnStep : forall st i a1 a1',
      a1 / st -->a a1' ->
      <{ i := a1 }> / st --> <{ i := a1' }> / st
  | CS_Asgn : forall st i (n : nat),
      <{ i := n }> / st --> <{ skip }> / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
  | CS_SeqFinish : forall st c2,
      <{ skip ; c2 }> / st --> c2 / st
  | CS_IfStep : forall st b1 b1' c1 c2,
      b1 / st -->b b1' ->
      <{ if b1 then c1 else c2 end }> / st
      -->
      <{ if b1' then c1 else c2 end }> / st
  | CS_IfTrue : forall st c1 c2,
      <{ if true then c1 else c2 end }> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      <{ if false then c1 else c2 end }> / st --> c2 / st
  | CS_While : forall st b1 c1,
      <{ while b1 do c1 end }> / st
      -->
      <{ if b1 then c1; while b1 do c1 end else skip end }> / st

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

(* ################################################################# *)
(** * Concurrent Imp *)

(** Finally, let's define a _concurrent_ extension of Imp, to
    show off the power of our new tools... *)

Module CImp.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CPar : com -> com -> com.         (* <--- NEW *)

Notation "x || y" :=
         (CPar x y)
           (in custom com at level 90, right associativity).
Notation "'skip'"  :=
         CSkip (in custom com at level 0).
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).

(* ----------------------------------------------------------------- *)
(** *** New small-step evaluation relation for commands *)
(**[[[

                           c1 / st --> c1' / st'
                     ---------------------------------                       (CS_Par1)
                     c1 || c2 / st --> c1' || c2 / st'

                           c2 / st --> c2' / st'
                     ---------------------------------                       (CS_Par2)
                     c1 || c2 / st --> c1 || c2' / st'

                     --------------------------------                        (CS_ParDone)
                     skip || skip / st --> skip / st
*)
Inductive cstep : (com * state)  -> (com * state) -> Prop :=
    (* Old part: *)
  | CS_AsgnStep : forall st i a1 a1',
      a1 / st -->a a1' ->
      <{ i := a1 }> / st --> <{ i := a1' }> / st
  | CS_Asgn : forall st i (n : nat),
      <{ i := n }> / st --> <{ skip }> / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
  | CS_SeqFinish : forall st c2,
      <{ skip ; c2 }> / st --> c2 / st
  | CS_IfStep : forall st b1 b1' c1 c2,
      b1 / st -->b b1' ->
      <{ if b1 then c1 else c2 end }> / st
      -->
      <{ if b1' then c1 else c2 end }> / st
  | CS_IfTrue : forall st c1 c2,
      <{ if true then c1 else c2 end }> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      <{ if false then c1 else c2 end }> / st --> c2 / st
  | CS_While : forall st b1 c1,
      <{ while b1 do c1 end }> / st
      -->
      <{ if b1 then c1; while b1 do c1 end else skip end }> / st
    (* New part: *)
  | CS_Par1 : forall st c1 c1' c2 st',
      c1 / st --> c1' / st' ->
      <{ c1 || c2 }> / st --> <{ c1' || c2 }> / st'
  | CS_Par2 : forall st c1 c2 c2' st',
      c2 / st --> c2' / st' ->
      <{ c1 || c2 }> / st --> <{ c1 || c2' }> / st'
  | CS_ParDone : forall st,
      <{ skip || skip }> / st --> <{ skip }> / st

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

Definition cmultistep := multi cstep.

Notation " t '/' st '-->*' t' '/' st' " :=
   (multi cstep  (t,st) (t',st'))
   (at level 40, st at level 39, t' at level 39).

(* QUIZ

    Which state _cannot_ be obtained as a result of executing the
    following program (from some starting state)?

       (Y := 1 || Y := 2);
       X := Y

    (1) [Y=0] and [X=0]

    (2) [Y=1] and [X=1]

    (3) [Y=2] and [X=2]

    (4) None of the above

*)
(* QUIZ

    Which state(s) _cannot_ be obtained as a result of executing the
    following program (from some starting state)?

       (Y := 1 || Y := Y + 1);
       X := Y

    (1) [Y=1] and [X=1]

    (2) [Y=0] and [X=1]

    (3) [Y=2] and [X=2]

    (4) [Y=n] and [X=n] for any [n >= 3]

    (5) 2 and 4 above

    (6) None of the above

*)
(* QUIZ

    How about this one?

      ( Y := 0; X := Y + 1 )
   ||
      ( Y := Y + 1; X := 1 )

    (1) [Y=0] and [X=1]

    (2) [Y=1] and [X=1]

    (3) [Y=0] and [X=0]

    (4) [Y=4] and [X=1]

    (5) None of the above

*)
(* /QUIZ

    Among the many interesting properties of this language is the fact
    that the following program can terminate with the variable [X] set
    to any value. *)

Definition par_loop : com :=
  <{
      Y := 1
    ||
      while (Y = 0) do X := X + 1 end
   }>.

End CImp.


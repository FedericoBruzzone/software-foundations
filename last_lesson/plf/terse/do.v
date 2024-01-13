From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Import Imp.


(** Consider a version of Imp, where the assignment and skip command
are _replaced_ with a new command [Do f], where [f : state -> state]
is an arbitrary state transformation.

For example [skip] is defined by [Do (fun s => s)].

1.1 Redefine the syntax of Imp so that [Do f] is a primitive command
and skip and assigments are derived. Redefining notations is optional.

1.2 Give _definitions_ for [skip] and assigment in terms of [Do f]

1.3 Redefine the operational semantics of Imp

1.4 Show that the rules for skip and assigments in the previous
definition of the op sem are now _derivable_ as theorems.

1.5 Give a Hoare rule for [Do f]: this means finding [P] and [Q] such
that

[  {{P}} (Do f) {{Q}} ]

is valid. You need to redefine [dhoare_triple] to use the new operational
semantics

1.6 Prove that the following example is valid wrt the *new* definition
of assigment via [Do].

[{{True}} X := 1 {{X = 1}}]
*)

Print state.

Inductive com2 : Type :=
  | CDo (f : (state -> state))
  (* | CSkip *)
  (* | CAsgn (x : string) (a : aexp) *)
  | CSeq (c1 c2 : com2)
  | CIf (b : bexp) (c1 c2 : com2)
  | CWhile (b : bexp) (c : com2).

Definition skip2 := CDo (fun st => st).
Definition assgn2 (s: string) (a: aexp) := CDo (fun st => s !-> (aeval st a) ; st).

Reserved Notation
  "st '==[' c ']=>' st'"
  (at level 40, c custom com at level 99,
  st constr, st' constr at next level).

Inductive ceval2 : com2 -> state -> state -> Prop :=
  (* | E_Skip : forall st, *)
  (*     st =[ skip ]=> st *)
  (* | E_Asgn  : forall st a n x, *)
  (*     aeval st a = n -> *)
  (*     st =[ x := a ]=> (x !-> n ; st) *)
  | E_CDo : forall f st st',
      st' = f st ->
      st ==[ CDo f ]=> st'
  | E_Seq : forall c1 c2 st st' st'',
      st  ==[ c1 ]=> st'  ->
      st' ==[ c2 ]=> st'' ->
      st  ==[ CSeq c1 c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st ==[ c1 ]=> st' ->
      st ==[ CIf b c1 c2 ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st ==[ c2 ]=> st' ->
      st ==[ CIf b c1 c2 ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st ==[ CWhile b c ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  ==[ c ]=> st' ->
      st' ==[ CWhile b c ]=> st'' ->
      st  ==[ CWhile b c ]=> st''
    where "st ==[ c ]=> st'" := (ceval2 c st st').

Theorem der_skip: forall st,
  st ==[ skip2 ]=> st. (* = st =[ skip]=> st. *)
Proof.
  intros.
  apply E_CDo.
  trivial.
Qed.

Theorem der_assign: forall st s a,
  st ==[ assgn2 s a ]=> (s !-> (aeval st a) ; st).
Proof.
  intros.
  apply E_CDo.
  trivial.
Qed.

Definition Assertion := state -> Prop.
Definition valid_hoare_triple
           (P : Assertion) (c : com2) (Q : Assertion) : Prop :=
  forall st st',
     st ==[ c ]=> st' ->
     P st  ->
     Q st'.

Notation "{{ P }} c {{ Q }}" := (valid_hoare_triple P c Q) (at level 90, c custom com at level 99).
Check ({{fun st => True}} skip2  {{fun st => True}}).

Theorem hoare_do : forall Q f (st : state),
     {{ fun st => Q (f(st)) }} CDo f {{ Q }}.
Proof.
  intros.
  unfold valid_hoare_triple.
  intros.
  inversion H; subst.
  trivial.
Qed.

Example assertion_true_x1 :
  {{fun st => True}} assgn2 X 2 {{fun st => (st X) = 2}}.
Proof.
  unfold valid_hoare_triple.
  intros.
  inversion H; subst.
  trivial.
Qed.


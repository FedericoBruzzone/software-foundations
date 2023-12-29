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

Inductive com :=
    CDo : (state -> state) -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Definition skip := CDo (fun st => st).

Definition assgn (var: string) (expr: aexp) :=
  CDo (fun st => var !-> (aeval st expr); st).

Print ceval.

Inductive ceval: state -> state -> com -> Prop :=
    E_Do: forall st f, ceval st (f st) (CDo f)
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
            ceval st st' c1 -> ceval st' st'' c2 -> ceval st st'' (CSeq c1 c2)
  | E_IfTrue : forall (st st' : state) (b : bexp) (c1 c2 : com),
               beval st b = true ->
               ceval st st' c1 -> ceval st st' (CIf b c1 c2)
  | E_IfFalse : forall (st st' : state) (b : bexp) (c1 c2 : com),
                beval st b = false ->
                ceval st st' c2 -> ceval st st' (CIf b c1 c2)
  | E_WhileFalse : forall (b : bexp) (st : state) (c : com),
                   beval st b = false -> ceval st st (CWhile b c)
  | E_WhileTrue : forall (st st' st'' : state) (b : bexp) (c : com),
                  beval st b = true ->
                  ceval st st' c ->
                  ceval st' st'' (CWhile b c) ->
                  ceval st  st'' (CWhile b c).


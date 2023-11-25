(*
  In order to run this file you have to move it to the `vol-1` (LF) directory.
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

From LF Require Import Imp.


(*

Let's go back to the IMP language described in Imp.v

Consider the REPEAT construct, whose operational semantics is
described by the following rules


  st =[ c ]=>  st'       beval st' b = true
------------------------------------------------ (E_Re_End)
    st =[ REPEAT c UNTIL b END ] => st'


   st =[ c ]=>  st'   beval st' b = false  st' =[ REPEAT c UNTIL b END ] => st''
--------------------------------------------------------------------------------- (E_Re_Loop)
                st =[ REPEAT c UNTIL b END ] => st''


In fact, REPEAT does *not* need to be taken as primitive, but it can be
*defined* in terms of the constructors of com.

1.1. ***Define*** it in terms of the original language of com, using the
While construct. Fill in the following definition:
 *)

 Module RepeatDefined.


Definition REP  (c : com) (b : bexp) : com :=
<{
  c;
  while (BNot b) do
    c
  end
}>.

 (*

 1.2. Introduce an appropriate Notation.

 1.3. Prove the above rules E_Re_End and E_Re_Loop are *derived*
 rules. That is, they do not need to be defined inductively but just
 stated and proven as Theorems, with respect to the original ceval
 relation.

 Again, do NOT redefine ceval.

 1.4 State and prove the inversion principle for the construct, that
 is a Theorem like:

 forall b c st st', st =[(REPEAT c UNTIL b END) => st' implies that
 either b is true in st and st=[ c] => st' or there exists a st'' such
 that ....

 This theorem makes explicit the reasoning behind the inversion tactic
   and corresponds to reading the two above rules from the bottom
   up. It can be proven directly via inversion w/o any auxiliary
   lemmas.  *)


 Definition FOR (c : com) (n : nat) := <{
     while (X <= n) do
       c;
       X := X + 1
     end
   }>.

 Notation "'FOR' n 'DO' c 'END'" := (FOR c n)
                                      (in custom com at level 0) : com_scope.


End RepeatDefined.



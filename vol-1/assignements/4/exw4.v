Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.

(* 1. Going back to the given inductive definitions, prove the other side of the inclusion.
You will need a lemma first. *)

Inductive beautiful : nat -> Prop :=
|  b_0   : beautiful 0
| b_3   : beautiful 3
| b_5   : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

Theorem beautiful_gorgeous : forall n, beautiful n -> gorgeous n.
  Admitted.

(** Write a txt file with the mathematical proof: I'll get you started with
the more involved case:

Theorem beautiful_gorgeous : forall n, beautiful n -> gorgeous n.

Proof: by induction on the derivation H : beautiful n:

Case H =   H1: beautiful n  H2: beautiful m
                -------------------------------------------
                              beautiful n + m

gorgeous n                    By IH applied to H1
gorgeous m                   By IH applied to H2
gorgeous n + m            By lemma ...
                                     QED

Complete the other cases specifying which rules you are applying as above
*)

(** 2. In this exercise we study some properties of the less-or-equal relation. Some
of them are not completely trivial and require previous lemmas, so think before you start writing tactics*)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Admitted.


Theorem O_le_n : forall n,
    0 <= n.
Admitted.

Theorem n_le_m__Sn_le_Sm : forall n m,
    n <= m -> S n <= S m.
Admitted.


Theorem Sn_le_Sm__n_le_m : forall n m,
    S n <= S m -> n <= m.
Admitted.

(** Most of the results above are needed in the following, where I'll start the proof, since
it requires the IH to be general enough.  Remember that < is defined in terms of <=
*)

Print Peano.lt.

Theorem lt_ge_cases : forall  m n,
  n < m \/ n >= m.
Proof.
  (* ADMITTED *)
  intros m.
  induction m.
Admitted.

(**  Prove the following equivalence between boolean and
propositional less-or-equal. You will need some of the above lemmas *)

Lemma leb_le : forall n m, (n <=? m) = true <-> n <= m.
  Proof.
  intro n.
  induction n .
Admitted.



From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.

(*  Remember the definition of arithmetic and Boolean expression and their interpreters:*)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2  => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end
.
Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
   | BEq a1 a2   => (aeval a1) =? (aeval a2)
  | BLe a1 a2   => (aeval a1) <=? (aeval a2)
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.

(* This is the optimizer for arith expressions *)


Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | APlus (ANum 0) e2 =>
      optimize_0plus e2  (* <-- here ! *)
  | APlus e1 e2 =>
      APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 =>
      AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 =>
      AMult (optimize_0plus e1) (optimize_0plus e2)
  end.



(* 1 Define a similar optimization on Boolean expression:

Fixpoint opt_b (b : bexp) : bexp :=
...

such that

  - on arithmetic sub-expressions, it applies the above optimization optimize_0plus
  - further, it performs the following optimization:

        - (true and b) is optimized to to b
        - (false and b) is optimized  to false *)

Fixpoint opt_b (b : bexp) : bexp :=
  match b with
  | BTrue       => BTrue
  | BFalse      => BFalse
  | BEq a1 a2   => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2   => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BNot b1     => BNot b1
  | BAnd b1 b2  =>
      match b1 with
      | BTrue => opt_b b2
      | BFalse => BFalse
      | _ => BAnd (opt_b b1) (opt_b b2)
      end
  end.

(* 2 Prove that the transformation over Booleans is sound.
   Use the tacticals we've seen so far to make the proof as
   short and modular as possible. *)
Theorem opt_0plus_sound: forall a,
    aeval (optimize_0plus a) = aeval a.
Proof. Admitted.

Theorem opt_b_sound : forall b : bexp, beval b = beval(opt_b b).
Proof.
  induction b; try reflexivity;
  try (simpl; destruct a;
    try (
    rewrite (opt_0plus_sound a0);
    rewrite opt_0plus_sound;
    reflexivity)
  );
  try(simpl; rewrite IHb; reflexivity);
  try (destruct b1;
    try(simpl; assumption);
    try(simpl; repeat rewrite opt_0plus_sound; rewrite IHb2; reflexivity);
    try(simpl; simpl in IHb1; rewrite IHb1; rewrite IHb2; reflexivity)).
Qed.


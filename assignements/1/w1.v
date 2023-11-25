(* To be handed in by Oct 09, 2300 hour on upload.di.unimi.it

i. This file, filled

ii. For the paper proof(s), a txt file or a scan/jpg of handwritten
notes will suffice. Latex, markdown also welcomed, but not required

These exercises will *NOT* be evaluated strictly, but you'll get
"points" for partecipation, which  will be helful in rounding up
your final vote.

Do not use generative AI.
 *)

From Coq Require Import Arith.
From Coq Require Import Lists.List.
Import ListNotations.

Definition admit {T: Type} : T.  Admitted.

(* LOGIC NOTATION *)
(* premesse & procedimento *)
(* ----- *)
(* goal *)

(*
1.1. Write an enumerated type for the month of the year
*)
Inductive month : Type :=
  | January
  | February
  | March
  | April
  | May
  | June
  | July
  | August
  | September
  | October
  | November
  | December.

(*
1.2 Write a function month_len that assigns to each month its length in days
keeping in mind that it could be a leap year, that is, month_len takes
a month and a boolean flag as arguments and returns a nat.
 *)
Definition month_len (m : month) (leap_year : bool) : nat :=
  match m with
  | January | March | May | July | August | October | December => 31
  | February => if leap_year then 29 else 28
  | April | June | September | November => 30
  end.

(*
1.3 State and prove a theorem for which the result of month_len is
greater or equal to 28. You can use "leb", which is already defined in the library.
*)
(* Using (leb 28 (month_len m leap_year)) = true. in the theorem saves me from writing all: apply leb_complete. *)
(* Using (28 <=? month_len m leap_year) = true. in the theorem saves me from writing all: apply leb_complete. *)
Theorem month_len_geq28 : forall (m : month) (leap_year : bool), 28 <= month_len m leap_year.
Proof.
  intros m leap_year.
  destruct m. (* as [n1 | n2 | n3 | n4 | n5 | n6 | n7 | n8 | n9 | n10 | n11 | n12 ] eqn:Em.*)
  all: destruct leap_year.
  (* all: simpl. *)
  all: apply leb_complete. (* Search leb. *)
  all: reflexivity.
  (* Restart.
     intros []; try reflexivity.
     intros []; reflexivity. *)
Qed.


(* 2.1. Prove the following theorem. You're going to need some
lemma(s). You can either prove them directly (they are very easy), or
try to find them in the Coq library. In the latter case, the "Search
<id>" command is very useful.

Example:   Search Nat.add.*)
Lemma Nat_add_n_0 : forall n : nat, n + 0 = n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - (* simpl. *) reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Lemma Nat_add_succ_n : forall n m : nat, n + S m = S (n + m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Lemma Nat_add_comm : forall n m : nat, n + m = m + n.
Proof.
  intros m n.
  induction n as [| n' IHn'].
  - simpl. rewrite -> Nat_add_n_0. reflexivity.
  - simpl. rewrite <- IHn'. rewrite -> Nat_add_succ_n. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,  n + m = m + n. (* apply Nat.add_comm. *)
Proof.
  intros m n.
  apply Nat_add_comm.
Qed.

(* 2.2 Write on paper the above proof, skipping the proofs of the
intermendiate lemmas, but detailing their use, as well as the use of
simplication, IH etc. Do *not* just verbalize the proof script, try to
write a math proof as in the notes.*)

(* 3.1 Complete the definition of nonzeros, a function that removes
O's from a list of nats*)

Fixpoint nonzeros (l:list nat) : list nat :=
  match l with
  | [] => []
  | h :: t =>
      match h with
      | 0 => nonzeros t
      | x => x :: nonzeros t
      end
  end.

(* 3.2 State and prove a lemma that says that nonzeros distributes
over the concatenaton (append) of two lists. Remember that a nested match in
the function definition corresponds to a destruct in the proof script. *)
Lemma nonzeros_app : forall l1 l2 : list nat, nonzeros (l1 ++ l2) = nonzeros l1 ++ nonzeros l2.
Proof.
  intros l1 l2.
  induction l1 as [| h t IHt].
  - (*simpl. *) reflexivity.
  - simpl. destruct h.
    + rewrite -> IHt. reflexivity.
    + rewrite -> IHt. reflexivity.
Qed.


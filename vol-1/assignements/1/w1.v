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


(*

1.1. Write an enumerated type for the month of the year

1.2 Write a function month_len that assigns to each month its length in days
keeping in mind that it could be a leap year, that is, month_len takes
a month and a boolean flag as arguments and returns a nat.

1.3 State and prove a theorem for which the result of month_len is
greater or equal to 28. You can use "leb", which is already defined in the library.

*)
LOGIC NOTATION
premesse & procedimento
-----
goal

Inductive month : Type :=
  | Gen
  | Feb.

Definition month_len (m:month) : nat :=
  | Gen => 31.


(* 2.1. Prove the following theorem. You're going to need some
lemma(s). You can either prove them directly (they are very easy), or
try to find them in the Coq library. In the latter case, the "Search
<id>" command is very useful.

Example:   Search Nat.add.*)

Theorem plus_comm : forall n m : nat,  n + m = m + n.
Proof.
  (* FILL IN HERE *)
Admitted.

(* 2.2 Write on paper the above proof, skipping the proofs of the
intermendiate lemmas, but detailing their use, as well as the use of
simplication, IH etc. Do *not* just verbalize the proof script, try to
write a math proof as in the notes.*)

(* 3.1 Complete the definition of nonzeros, a function that removes
O's from a list of nats*)

Fixpoint nonzeros (l:list nat) : list nat :=
admit.

(* 3.2 State and prove a lemma that says that nonzeros distributes
over the concatenaton (append) of two lists. Remember that a nested match in
the function definition corresponds to a destruct in the proof script. *)

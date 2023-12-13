
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export Imp.
From PLF Require Export Hoare.
From PLF Require Export Vcg.

Ltac verify_assn :=
  repeat split;
  simpl; unfold assert_implies;
  unfold ap in *; unfold ap2 in *;
  unfold bassertion in *; unfold beval in *; unfold aeval in *;
  unfold assertion_sub; intros;
  repeat (simpl in *;
          rewrite t_update_eq ||
          (try rewrite t_update_neq; [| (intro X; inversion X; fail)]));
  simpl in *;
  repeat match goal with [H : _ /\ _ |- _] => destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite eqb_eq in *;
  repeat rewrite eqb_neq in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  simpl in *;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
        | [H : st _ = _ |- _] => rewrite -> H in *; clear H
        | [H : _ = st _ |- _] => rewrite <- H in *; clear H
        end
    end;
  try eauto; try lia.

(** A. Prove that the following structural rule is derivable:*)
Theorem spec_conj: forall P1 P2 Q1 Q2 C, 
{{P1}}  C {{Q1}} ->
{{P2}}  C {{Q2}} -> {{P1 /\ P2}}  C {{Q1 /\ Q2}}.
  unfold valid_hoare_triple.
  intros.
  split.
  - apply (H st st').
    + trivial.
    + apply H2.
  - apply (H0 st st').
    + trivial.
    + apply H2.
Qed.

(** B. Write a program that stores in a variable the max
of two vars and prove it correct. You can use the library
function _max_ for the spec. Either you write the post-condition
with an explicit [fun st => ...] or you can use the below lifted version. *) 
Definition MAX :=
  ap2 max X Y.


(** Replace the bogus spec and skip with your own code*)
Lemma max_correct: 
{{True}}
<{ if X > Y then Z := X else Z := Y end}>
{{ (fun st => st Z = max (st X) (st Y)) }} .
Proof.
  apply hoare_if.
  - apply hoare_asg_conseq.
    verify_assn.
  - apply hoare_asg_conseq.
    verify_assn.
Qed.

(** C.  The following program computes the substraction [p - n]. 
Show that the triple is valid by _finding_ the right invariant. 
We suggest you first do this on paper.*)

Lemma subtract_slowly_correct: forall (m p : nat),
  {{ X = m /\ Z = p }}
  <{ while (X <> 0)  do  
     Z := Z - 1 ;
     X := X - 1
     end }>
    {{ Z = p - m }}.
Proof.
  intros.
  apply hoare_consequence_pre with (P':= fun st => st Z - st X = p - m);
  try verify_assn.
  - apply hoare_while_conseq.
    + eapply hoare_seq.
      * apply hoare_asgn.
      * apply hoare_asg_conseq. verify_assn.
    + verify_assn.
Qed.

(** D. Rewrite the program as an annotated program [acom]. Use the
[vc] verification function to generate the verification condition and re-prove it.  Hint: print
the previous program as a [com] _without_ notations and use it as a skeleton *)
Print acom.
Print AMinus.

Definition annotated_sub_slowly_correct (p m: nat) :=
  (CWhile (Z - X = p - m) (BNeq X 0)
    (CSeq (CAsgn Z (AMinus (AId Z) (ANum 1))) 
          (CAsgn X (AMinus (AId X) (ANum 1))))).

Theorem annotated_sub_slow_sound : forall p m, 
 vc (annotated_sub_slowly_correct p m) (fun st => st Z = p - m).
Proof.
  unfold annotated_sub_slowly_correct.
  verify_assn.
Qed.
 
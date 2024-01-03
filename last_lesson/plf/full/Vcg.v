
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export   Imp.
From PLF Require Export Hoare.
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

(** We can _derive_ an assigment rule modulo consequence that is
easier to use since the precondition is any propitions that entails the required
substitution:*)
Theorem hoare_asg_conseq':   forall P Q X a,
  P ->> Q [X |-> a] -> {{P}} X := a {{Q}}.
Proof.
  intros .
  apply hoare_consequence_pre with (Q [X |-> a]).
  - apply hoare_asgn.
  - assumption.
Qed.

(** A derived rule for [while] modulo weakening the postcondition:*) 

Theorem hoare_while_conseq' : forall P Q(b:bexp) c,
  {{P /\ b}} c {{P}} -> (fun st => P st /\ ~ (bassertion b st)) ->> Q ->
  {{P}} while b do c end {{Q}}.
  Proof.
  intros P Q b C H Himp.
  eapply hoare_consequence_post; try apply hoare_while; assumption.
  Qed. 

Theorem hoare_skip_conseq : forall P Q,
    P ->> Q -> {{P}} skip {{Q}}.
Proof.
  intros P Q HPQ.
  unfold valid_hoare_triple.
  unfold "->>" in *.
   intros st st' H HP. inversion H; subst. auto.
Qed.

(* ################################################################# *)
(** * Verification Condition Generation *)

(** Consider this set of rules for Hoare Logic:

                P ->> Q[X |-> a]
             --------------------------- (hoare_asg_conseq)
             {{P}} X:=a {{Q}}

               P ->> Q
             --------------------  (hoare_skip_conseq)
             {{ P }} skip {{ Q }}

               {{ P }} c1 {{ Q }}
               {{ Q }} c2 {{ R }}
              ----------------------  (hoare_seq)
              {{ P }} c1;c2 {{ R }}

              {{P /\  b}} c1 {{Q}}
              {{P /\ ~b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} if b then c1 else c2 end {{Q}}

               {{P /\ b}} c {{P}} (P /\ ~b) ->> Q
        -----------------------------------------------------  (hoare_while_conseq)
        {{P}} while b do c end {{Q}}

*)

(**

- We have a _syntax_ directed proof system and each backward rule
application creates new subgoals for the subcommands.  The
construction of the skeleton of this proof tree is completely
automatic.

- The consequence rule is built into the derived rules and is not
required anymore. This is crucial: the consequence rule destroys
syntax directedness because it can be applied at any point.

- When applying the sequence rule for [c1 ; c2 ] backwards we need to
provide the intermediate assertion that occurs in the premises but not
the conclusion. It turns out that we can compute it by pulling the
final assertion back through [c2].

There are two aspects that cannot be fully automated (or program
verification would be completely automatic, which is impossible):
_loop_ invariants _must_ be supplied explicitly, and the implications between
assertions in the premises of the derived rules must be proved
somehow.

In a nutshell, proving triples in Hoare logic amounts to _finding
invariants_ and _proving assertions_.

*)

(**  We aim to reduce provability in Hoare logic to provability in the
assertion language, i.e. Coq in our case. Given a triple [{P} c {Q}]
that we want to prove, we show how to compute an assertion [A] from it
such that [{P } c {Q}] is provable iff [A] is provable.

We call [A] a _verification condition_ and the function that computes [A]
a verification condition generator or _VCG_. The advantage of working
with a VCG is that no knowledge of Hoare logic is required.

Summary:

- _annotate_ the program with assertions meant to hold at certain
  program points

  ==> This needs understanding ("eureka") of how the program works

- _generate_ a set of logical conditions (VCs) from annotated program

  ==> This is automatic

- _prove_ the VCs.

  ==> This is a matter of theorem proving (undecidable in general).  *)

(* ================================================================= *)
(** ** Annotated commands *)
 
 (**
 
An annotated command is a command with _assertions_ embedded within
it.  This may vary from _full_ decoration (every command has pre and
post conditions), to more economical ones.
 
 We choose the least invasive: we only annotate [while] loops with
 their invariants.

Where do we get those invariants? Here, we take the easy way out: the
_user_ will provide them. In general, we can appeal to techniques such
as _abstract interpretation, symbolic execution_ and _machine
learning_ to get suggestions.

We introduce a type [acom] of annotated commands with the same syntax
as that of type [com], except that WHILE is annotated with an
assertion [asn]. We gloss over notations for now.*)

Inductive acom : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : acom)
  | CIf (b : bexp) (c1 c2 : acom)
  | CWhile (inv : Assertion)(b : bexp) (c : acom).

(** We can [strip] invariants from [acom] and recover our usual [com]mmands:*)
Fixpoint  strip (acm : acom)  : com  :=
  match acm with
  |CSkip =>  Imp.CSkip
  |CAsgn x e =>  Imp.CAsgn x e
  |CSeq c1 c2 =>  Imp.CSeq (strip c1) (strip c2) 
  |CIf b c1 c2 =>  Imp.CIf b (strip c1) (strip c2)
  |CWhile _ b c =>  Imp.CWhile b (strip c)
  end.

(* ----------------------------------------------------------------- *)
(** *** Weakest Preconditions *)

(**

The weakest precondition of a command [c] with postcondition [Q] is an
assertion [wpre c Q] s.t:

- it is a _precondition_: p{ wpre c Q } c { Q }] ;
-  it is the weakest: if [{ P } c { Q }] then [P ->> wpre c Q].

Think of [wpre c Q] as the assertion described by set of states [st]
 such that for all [st'], if [st =[ c ]=> st'], then [Q st'] holds.

[wpre c Q] are the necessary hypotheses for program [c] to compute a result
that satisfies the postcondition [Q].  Original intuition (Dijkstra,
1975): synthesizing the program c by refinement from its postcondition
[Q]. Examples of possible preconditions:

- A useless (though valid) Hoare triple:

[ {{ False }} X := Y + 1 {{ X <= 5 }} ]

- A better precondition:

[ {{ Y <= 4 /\ Z = 0 }} X := Y + 1 {{ X <= 5 }} ]

- The _best_  (weakest) precondition:

[ {{ Y <= 4 }} X := Y + 1 {{ X <= 5 }} ]

 *)

Fixpoint  wpre (acm : acom) (Q: Assertion) : Assertion  :=
  match acm with
  | CSkip => Q
  | CAsgn x e => fun st => Q [x |-> e] st 
  | CSeq c1 c2 => wpre c1 (wpre c2 Q)
  | CIf b c1 c2 => fun st => if beval  st b then wpre c1 Q st else wpre c2 Q st 
  | CWhile inv _ _ => inv
  end.

(** In the case of [while], computing [wpre] would not terminate. This is
why we have annotated programs and we just return the invariant. *)

(**  *** Some examples *)

(** [wpre X := 1{{X <= 10}}] yields [{{1 <= 10}}] *)
Compute (wpre (CAsgn X 1) (fun st : state => st X  <= 10 )).

(** [wpre (Z:= X; X:=Y;Y :=Z) {{X <=Y}}] yields [{{Y <= Z}}]  *)

Compute  (wpre           (CSeq (CAsgn Z X)
                       (CSeq (CAsgn X Y)
                             (CAsgn Y Z)))
                 (fun st => st X <= st Y)).

(* ----------------------------------------------------------------- *)
(** *** VC

    The function [vc] is the actual VCG and returns a [Prop], _not_ an assertion
and it is therefore independent of the state, using [wpre] in the process.

It  generates for non-while constructs only trivial verification conditions (skip, assigment)
or the conjunction of the results of subcomputations (seq, if).
 *)
Fixpoint  vc (acm : acom) (Q: Assertion) : Prop  :=
  match acm with
  | CSkip => True
  | CAsgn x e => True
  | CSeq c1 c2 => (vc c1 (wpre c2 Q) /\ vc c2 Q)
  | CIf _ c1 c2 => vc c1 Q  /\  vc c2 Q 
  | CWhile inv b c => (forall s, (inv s /\ (beval s b = true) -> wpre c inv s) /\
                                  (inv s /\ beval s b = false -> Q s))  /\ 
                                   vc c inv  end.

(**
For each [{inv} while b do c] the function [vc] builds 3 proof obligations:

- [inv] and [b] together imply the precondition of the body of the loop, i.e. [inv] is an invariant.

- At the end of the loop the postcondition holds.

- [vc c inv]: recursively applies to any other [while] in [c].

 *)

(* ----------------------------------------------------------------- *)
(** *** Examples *)

(**  Consider this "reduce to zero" program:

{{True}
while {{True}} X <> 0 do
  X := X - 1
{{X = 0}}
*)
   
Definition reduce_to_zero : acom :=
  CWhile (fun s => True)
         (BNeq X O)
         (CAsgn X (AMinus X 1)).

(** The post condition: *)
Definition reduce_to_zero_post := fun st => st X = 0.

Eval simpl in (vc 
                 (CWhile (fun s => True)
                         (BNeq X O)
                         (CAsgn X (AMinus X (S O))))
                 (fun st => st X = 0)).

(* (forall s : state,
        (True /\ negb (s X =? 0) = true ->
         ((fun _ : state => True) [X |-> X - 1]) s) /\
        (True /\ negb (s X =? 0) = false -> s X = 0)) /\ True*)

(** ... which is true.*)
Lemma reduce_to_zero_correct_vgc:
  vc reduce_to_zero reduce_to_zero_post.
Proof.
  unfold reduce_to_zero, reduce_to_zero_post.
  simpl.
  verify_assn.
Qed.

(* ================================================================= *)
(** ** Soundness *)

(** Our VCG is _sound_ w.r.t. Hoare logic.
This reduces the question " does [{{P }} c {{Q}}] hold?"  to the question "is
the verification condition true ?".

We can prove, by induction on [c], that if [vc c Q] holds, then
the Hoare triple where the precondition has been _computed_ by [wpre] is indeed valid.

In other terms, [vc] is _sufficient_ for validity
 *)

Lemma vc_sound:forall c Q, vc c Q -> {{wpre c Q}} (strip c) {{Q}}.
Proof.
induction c; intros;simpl; simpl in H; try destruct H.
- apply hoare_skip.
- apply hoare_asgn.
- eapply hoare_seq; eauto.
(* if *)
- apply IHc1 in H.  apply IHc2 in H0. clear IHc1. clear IHc2.
apply hoare_if; unfold bassertion. 
 + eapply hoare_consequence_pre. eassumption. 
 unfold "->>". intros.
  destruct (beval st b); destruct H1; auto; try congruence.
 + eapply hoare_consequence_pre. eassumption. 
 unfold "->>". intros.
  destruct (beval st b); destruct H1; auto; try congruence.
(* while *) 
- apply IHc in H0.  eapply hoare_while_conseq;  unfold bassertion.
 eapply hoare_consequence_pre. eassumption.
 + unfold "->>". intros.
  destruct (H st).  auto.
 +  unfold "->>". intros.
 destruct (H st).
 apply H3. verify_assn. Qed.

Definition vcgen (P: Assertion) (a: acom) (Q: Assertion) : Prop :=
   P ->> (wpre a Q) /\ vc a Q.

Corollary vcg_s: forall c P Q, 
  vcgen P c Q -> {{P}} (strip c) {{Q}}.
Proof.
unfold vcgen.  intros c P Q [H1 H2]. 
eapply hoare_consequence_pre; try apply vc_sound; auto.
Qed.

(** How about completeness? Is [vc] a necessarily condition?

Certainly not: if [c] is badly annotated, [{wpre c Q} strip c {Q}] may
be provable but not [vc c Q]. *)

Definition loopq (Q: Assertion) := (CWhile Q BTrue (CAsgn X (ANum 0))) .
Definition l := (Imp.CWhile  BTrue (Imp.CAsgn X (ANum 0))).

(** This triple is valid *)
Goal  valid_hoare_triple (fun s => s X = 1) l (fun _ => False).
Proof.
 eapply hoare_consequence_pre.
 assert (valid_hoare_triple (fun s => True) l (fun _ => False)) as lp.
 - unfold l.
 apply hoare_while_conseq.
  -- apply hoare_asg_conseq. verify_assn.
  -- verify_assn.
 - apply lp.
 - verify_assn.
 Qed. 

(** However, if we annotate it with a wrong loop invariant, it generates
an unprovable verification condition: *)
Goal (vc (loopq (fun s => s X = 1)) (fun _ => False)).
  unfold loop. simpl. verify_assn.
  (* false*)
Admitted.

(** We could prove that there is always an annotation that make
completeness work. We won't.  *)



(** *** Some additional examples of using the VGC*)

(** For programs w/o loops, verifying the [vc] is trivial. *)
Definition swap_program : acom   :=
  CSeq (CAsgn Z X)
       (CSeq (CAsgn X Y)
             (CAsgn Y Z)).

Lemma swap_corr_v0 :
  vc
  swap_program
  (fun st => st Y <= st X).
Proof.
  unfold swap_program.
  simpl.
  tauto.
  Qed.

Lemma swap_corr_v : forall (x y : nat), 
  vc
  swap_program
  (fun st => st X = y /\ st Y = x).
 Proof.
 intros.  unfold swap_program. simpl. tauto.
  Qed.


(** *** Division*)
Definition R : string := "R".
Definition Q : string := "Q".

Definition div_inv : Assertion :=
  fun st => st X = st R + (st Y * st Q).  

Definition div : acom :=
 CSeq (CAsgn R X)
  (CSeq (CAsgn Q O)
     (CWhile div_inv (BLe Y R)
        (CSeq
           (CAsgn R (AMinus R Y))
           (CAsgn Q (APlus Q (S O)))))).  
    
Definition div_post :=
fun st => st R < st Y /\ div_inv st.    

Lemma div_correct_vcg: (vc div div_post).
unfold div, div_post,div_inv. simpl. verify_assn.
Qed.



(* 2023-12-19 17:48 *)

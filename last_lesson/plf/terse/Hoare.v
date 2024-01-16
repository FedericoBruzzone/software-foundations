(** * Hoare: Hoare Logic, Part I *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export Imp.
Set Default Goal Selector "!".


(** Our goal in this chapter is to carry out some simple examples of
    _program verification_ -- i.e., to use the precise definition of
    Imp to prove formally that particular programs satisfy particular
    specifications of their behavior.

    We'll develop a reasoning system called _Floyd-Hoare Logic_ --
    often shortened to just _Hoare Logic_ -- in which each of the
    syntactic constructs of Imp is equipped with a generic "proof
    rule" that can be used to reason compositionally about the
    correctness of programs involving this construct. *)

(** Hoare Logic combines two beautiful ideas: a natural way of writing
    down _specifications_ of programs, and a _structured proof
    technique_ for proving that programs are correct with respect to
    such specifications -- where by "structured" we mean that the
    structure of proofs directly mirrors the structure of the programs
    that they are about. *)

(* ################################################################# *)
(** * Assertions *)

(** An _assertion_ is a logical claim about the state of a program's
    memory -- formally, a property of [state]s. *)

Definition Assertion := state -> Prop.

(** For example,

    - [fun st => st X = 3] holds for states [st] in which value of [X]
      is [3],

    - [fun st => True] hold for all states, and

    - [fun st => False] holds for no states. *)

(** We'll use Coq's notation features to make assertions
    look as much like informal math as possible.

    For example, instead of writing

      fun st => st X = m

    we'll usually write just

      X = m
*)

(** Given two assertions [P] and [Q], we say that [P] _implies_ [Q],
    written [P ->> Q], if, whenever [P] holds in some state [st], [Q]
    also holds. *)

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Declare Scope hoare_spec_scope.
Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

(** We'll also want the "iff" variant of implication between
    assertions: *)

Notation "P <<->> Q" := (P ->> Q /\ Q ->> P)
                          (at level 80) : hoare_spec_scope.

(* ================================================================= *)
(** ** Notations for Assertions *)

(** The convention described above can be implemented in Coq with a
    little syntax magic, using coercions and annotation scopes, much
    as we did with [%imp] in [Imp], to automatically lift
    [aexp]s, numbers, and [Prop]s into [Assertion]s when they appear
    in the [%assertion] scope or when Coq knows that the type of an
    expression is [Assertion].

    There is no need to understand the details of how these notation
    hacks work. (We barely understand some of it ourselves!) *)

Definition Aexp : Type := state -> nat.

Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.

Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.

Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp >-> Aexp.
(* Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop.
*)
Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.
(*
Add Printing Coercion Aexp_of_nat Aexp_of_aexp assert_of_Prop.
*)
Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.

Notation assert P := (P%assertion : Assertion).
Notation mkAexp a := (a%assertion : Aexp).

Notation "~ P" := (fun st => ~ assert P st) : assertion_scope.
Notation "P /\ Q" := (fun st => assert P st /\ assert Q st) : assertion_scope.
Notation "P \/ Q" := (fun st => assert P st \/ assert Q st) : assertion_scope.
Notation "P -> Q" := (fun st => assert P st ->  assert Q st) : assertion_scope.
Notation "P <-> Q" := (fun st => assert P st <->  assert Q st) : assertion_scope.
Notation "a = b" := (fun st => mkAexp a st = mkAexp b st) : assertion_scope.
Notation "a <> b" := (fun st => mkAexp a st <> mkAexp b st) : assertion_scope.
Notation "a <= b" := (fun st => mkAexp a st <= mkAexp b st) : assertion_scope.
Notation "a < b" := (fun st => mkAexp a st < mkAexp b st) : assertion_scope.
Notation "a >= b" := (fun st => mkAexp a st >= mkAexp b st) : assertion_scope.
Notation "a > b" := (fun st => mkAexp a st > mkAexp b st) : assertion_scope.
Notation "a + b" := (fun st => mkAexp a st + mkAexp b st) : assertion_scope.
Notation "a - b" := (fun st => mkAexp a st - mkAexp b st) : assertion_scope.
Notation "a * b" := (fun st => mkAexp a st * mkAexp b st) : assertion_scope.

(** Lift functions to operate on assertion expressions. *)

Definition ap {X} (f : nat -> X) (x : Aexp) :=
  fun st => f (x st).

Definition ap2 {X} (f : nat -> nat -> X) (x : Aexp) (y : Aexp) (st : state) :=
  f (x st) (y st).

Module ExamplePrettyAssertions.
Definition ex1 : Assertion := X = 3.
Definition ex2 : Assertion := True.
Definition ex3 : Assertion := False.

Definition assertion1 : Assertion := X <= Y.
Definition assertion2 : Assertion := X = 3 \/ X <= Y.
Definition assertion3 : Assertion := Z = ap2 max X Y.
Definition assertion4 : Assertion := Z * Z <= X
                            /\  ~ (((ap S Z) * (ap S Z)) <= X).
End ExamplePrettyAssertions.

(* ################################################################# *)
(** * Hoare Triples, Informally *)

(** A _Hoare triple_ is a claim about the state before and
    after executing a command:

      {{P}} c {{Q}}

    This means:

      - If command [c] begins execution in a state satisfying
        assertion [P],
      - and if [c] eventually terminates in some final state,
      - then that final state will satisfy the assertion [Q].

    Assertion [P] is called the _precondition_ of the triple, and [Q]
    is the _postcondition_.
*)
(** For example,

    - [{{X = 0}} X := X + 1 {{X = 1}}] is a valid Hoare triple,
      stating that command [X := X + 1] will transform a state in
      which [X = 0] to a state in which [X = 1].

    - [forall m, {{X = m}} X := X + 1 {{X = m + 1}}], is a
      _proposition_ stating that the Hoare triple [{{X = m}} X := X +
      m {{X = m + 1}}] is valid for any choice of [m].  Note that [m]
      in the two assertions and the command in the middle is a
      reference to the _Coq_ variable [m], which is bound outside the
      Hoare triple. *)

(* ################################################################# *)
(** * Hoare Triples, Formally *)

(** We can formalize valid Hoare triples in Coq as follows: *)

Definition valid_hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st' ->
     P st  ->
     Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (valid_hoare_triple P c Q)
    (at level 90, c custom com at level 99)
    : hoare_spec_scope.
Check ({{True}} X := 0 {{True}}).

(** **** Exercise: 1 star, standard (hoare_post_true) *)

(** Prove that if [Q] holds in every state, then any triple with [Q]
    as its postcondition is valid. *)

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (hoare_pre_false) *)

(** Prove that if [P] holds in no state, then any triple with [P] as
    its precondition is valid. *)

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~ (P st)) ->
  {{P}} c {{Q}}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Proof Rules *)

(** Here's our plan:
      - introduce one "proof rule" for each Imp syntactic form
      - plus a couple of "structural rules" that help glue proofs
        together
      - prove these rules correct in terms of the definition of
        [valid_hoare_triple]
      - prove programs correct using these proof rules, without ever
        unfolding the definition of [valid_hoare_triple] *)

(* ================================================================= *)
(** ** Skip *)

(** Since [skip] doesn't change the state, it preserves any
    assertion [P]:

      --------------------  (hoare_skip)
      {{ P }} skip {{ P }}
*)

Theorem hoare_skip : forall P,
     {{P}} skip {{P}}.
Proof.
  intros P st st' H HP. inversion H; subst. assumption.
Qed.

(* ================================================================= *)
(** ** Sequencing *)

(** If command [c1] takes any state where [P] holds to a state where
    [Q] holds, and if [c2] takes any state where [Q] holds to one
    where [R] holds, then doing [c1] followed by [c2] will take any
    state where [P] holds to one where [R] holds:

        {{ P }} c1 {{ Q }}
        {{ Q }} c2 {{ R }}
       ----------------------  (hoare_seq)
       {{ P }} c1;c2 {{ R }}
*)

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1; c2 {{R}}.
Proof.
  unfold valid_hoare_triple.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  eauto.
Qed.

(* ================================================================= *)
(** ** Assignment *)

(** How can we complete this triple?

       {{ ??? }}  X := Y  {{ X = 1 }}

    One natural possibility is:

       {{ Y = 1 }}  X := Y  {{ X = 1 }}

    The precondition is just the postcondition, but with [X] replaced
    by [Y]. *)

(** How about this one?

       {{ ??? }}  X := X + Y  {{ X = 1 }}

    Replace [X] with [X + Y]:

       {{ X + Y = 1 }}  X := X + Y  {{ X = 1 }}

    This works because "equals 1" holding of [X] is guaranteed
    by the property "equals 1" holding of whatever is being
    assigned to [X]. *)

(** In general, the postcondition could be some arbitrary assertion
    [Q], and the right-hand side of the assignment could be some
    arbitrary arithmetic expression [a]:

       {{ ??? }}  X := a  {{ Q }}

    The precondition would then be [Q], but with any occurrences of
    [X] in it replaced by [a].

    Let's introduce a notation for this idea of replacing occurrences:
    Define [Q [X |-> a]] to mean "[Q] where [a] is substituted in
    place of [X]".

    This yields the Hoare logic rule for assignment:

      {{ Q [X |-> a] }}  X := a  {{ Q }}

    One way of reading this rule is: If you want statement [X := a]
    to terminate in a state that satisfies assertion [Q], then it
    suffices to start in a state that also satisfies [Q], except
    where [a] is substituted for every occurrence of [X]. *)

(** Here are some valid instances of the assignment rule:

      {{ (X <= 5) [X |-> X + 1] }}   (that is, X + 1 <= 5)
        X := X + 1
      {{ X <= 5 }}

      {{ (X = 3) [X |-> 3] }}        (that is, 3 = 3)
        X := 3
      {{ X = 3 }}

      {{ (0 <= X /\ X <= 5) [X |-> 3]  (that is, 0 <= 3 /\ 3 <= 5)
        X := 3
      {{ 0 <= X /\ X <= 5 }}
*)

(** To formalize the rule, we must first formalize the idea of
    "substituting an expression for an Imp variable in an assertion",
    which we refer to as assertion substitution, or [assertion_sub].  That
    is, intuitively, given a proposition [P], a variable [X], and an
    arithmetic expression [a], we want to derive another proposition
    [P'] that is just the same as [P] except that [P'] should mention
    [a] wherever [P] mentions [X]. *)

(** This operation is related to the idea of substituting Imp
    expressions for Imp variables that we saw in [Equiv]
    ([subst_aexp] and friends). The difference is that, here,
    [P] is an arbitrary Coq assertion, so we can't directly
    "edit" its text. *)

(** However, we can achieve the same effect by evaluating [P] in an
    updated state: *)

Definition assertion_sub X a (P:Assertion) : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).

Notation "P [ X |-> a ]" := (assertion_sub X a P)
  (at level 10, X at next level, a custom com) : hoare_spec_scope.

(** That is, [P [X |-> a]] stands for an assertion -- let's call it
    [P'] -- that is just like [P] except that, wherever [P] looks up
    the variable [X] in the current state, [P'] instead uses the value
    of the expression [a]. *)

(** Now, using the substitution operation we've just defined, we can
    give the precise proof rule for assignment:

      ---------------------------- (hoare_asgn)
      {{Q [X |-> a]}} X := a {{Q}}
*)

(** We can prove formally that this rule is indeed valid. *)

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X := a {{Q}}.
Proof.
  unfold valid_hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assertion_sub in HQ. assumption.  Qed.

(** Here's a first formal proof using this rule. *)

Example assertion_sub_example :
  {{(X < 5) [X |-> X + 1]}}
    X := X + 1
  {{X < 5}}.
Proof.
  apply hoare_asgn.  Qed.

(** Of course, what we'd probably prefer is to prove this
    simpler triple:

      {{X < 4}} X := X + 1 {{X < 5}}

   We will see how to do so in the next section. *)

(* ================================================================= *)
(** ** Consequence *)

(** Sometimes the preconditions and postconditions we get from the
    Hoare rules won't quite be the ones we want in the particular
    situation at hand -- they may be logically equivalent but have a
    different syntactic form that fails to unify with the goal we are
    trying to prove, or they actually may be logically weaker (for
    preconditions) or stronger (for postconditions) than what we need. *)

(** For instance,

      {{(X = 3) [X |-> 3]}} X := 3 {{X = 3}},

    follows directly from the assignment rule, but

      {{True}} X := 3 {{X = 3}}

    does not.  This triple is valid, but it is not an instance of
    [hoare_asgn] because [True] and [(X = 3) [X |-> 3]] are not
    syntactically equal assertions.

    However, they are logically _equivalent_, so if one triple is
    valid, then the other must certainly be as well.  We can capture
    this observation with the following rule:

                {{P'}} c {{Q}}
                  P <<->> P'
         -----------------------------   (hoare_consequence_pre_equiv)
                {{P}} c {{Q}}
*)

(** Taking this line of thought a bit further, we can see that
    strengthening the precondition or weakening the postcondition of a
    valid triple always produces another valid triple. This
    observation is captured by two _Rules of Consequence_.

                {{P'}} c {{Q}}
                   P ->> P'
         -----------------------------   (hoare_consequence_pre)
                {{P}} c {{Q}}

                {{P}} c {{Q'}}
                  Q' ->> Q
         -----------------------------    (hoare_consequence_post)
                {{P}} c {{Q}}
*)

(** Here are the formal versions: *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold valid_hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  apply Hhoare with (st := st).
  - assumption.
  - apply Himp. assumption.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  unfold valid_hoare_triple, "->>".
  intros P Q Q' c Hhoare Himp st st' Heval Hpre.
  apply Himp.
  apply Hhoare with (st := st).
  - assumption.
  - assumption.
Qed.

(** For example, we can use the first consequence rule like this:

    {{ True }} ->>
    {{ (X = 1) [X |-> 1] }}
      X := 1
    {{ X = 1 }}

    Or, formally... *)

Example hoare_asgn_example1 :
  {{True}} X := 1 {{X = 1}}.
Proof.
  (* WORK IN CLASS *) Admitted.

(** We can also use it to prove the example mentioned earlier.

    {{ X < 4 }} ->>
    {{ (X < 5)[X |-> X + 1] }}
      X := X + 1
    {{ X < 5 }}

   Or, formally ... *)

Example assertion_sub_example2 :
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
  (* WORK IN CLASS *) Admitted.

(** Finally, here is a combined rule of consequence that allows us to
    vary both the precondition and the postcondition.

                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
*)

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Htriple Hpre Hpost.
  apply hoare_consequence_pre with (P' := P').
  - apply hoare_consequence_post with (Q' := Q').
    + assumption.
    + assumption.
  - assumption.
Qed.

(* ================================================================= *)
(** ** Automation *)

(** Many of the proofs we have done so far with Hoare triples can be
    streamlined using the automation techniques that we introduced in
    the [Auto] chapter of _Logical Foundations_.

    Recall that the [auto] tactic can be told to [unfold] definitions
    as part of its proof search.  Let's give it that hint for the
    definitions and coercions we're using: *)

Hint Unfold assert_implies assertion_sub t_update : core.
Hint Unfold valid_hoare_triple : core.
Hint Unfold assert_of_Prop Aexp_of_nat Aexp_of_aexp : core.

(** Also recall that [auto] will search for a proof involving [intros]
    and [apply].  By default, the theorems that it will apply include
    any of the local hypotheses, as well as theorems in a core
    database. *)

(** Here's a good candidate for automation: *)

Theorem hoare_consequence_pre' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold valid_hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  apply Hhoare with (st := st).
  - assumption.
  - apply Himp. assumption.
Qed.

(** Tactic [eapply] will find [st] for us. *)

Theorem hoare_consequence_pre''' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold valid_hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  eapply Hhoare.
  - eassumption.
  - apply Himp. assumption.
Qed.

(** The [eauto] tactic will use [eapply] as part of its proof search.
    So, the entire proof can actually be done in just one line. *)

Theorem hoare_consequence_pre'''' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  eauto.
Qed.

(** ...as can the proof for the postcondition consequence
    rule. *)

Theorem hoare_consequence_post' : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  eauto.
Qed.

(** We can also use [eapply] to streamline a
    proof ([hoare_asgn_example1]), that we did earlier as an example
    of using the consequence rule: *)

Example hoare_asgn_example1' :
  {{True}} X := 1 {{X = 1}}.
Proof.
  eapply hoare_consequence_pre. (* no need to state an assertion *)
  - apply hoare_asgn.
  - unfold "->>", assertion_sub, t_update.
    intros st _. simpl. reflexivity.
Qed.

(** The final bullet of that proof also looks like a candidate for
    automation. *)

Example hoare_asgn_example1'' :
  {{True}} X := 1 {{X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - auto.
Qed.

(** Now we have quite a nice proof script: it simply identifies the
    Hoare rules that need to be used and leaves the remaining
    low-level details up to Coq to figure out. *)

(** The other example of using consequence that we did earlier,
    [hoare_asgn_example2], requires a little more work to automate.
    We can streamline the first line with [eapply], but we can't just use
    [auto] for the final bullet, since it needs [lia]. *)

Example assertion_sub_example2' :
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - auto. (* no progress *)
    unfold "->>", assertion_sub, t_update.
    intros st H. simpl in *. lia.
Qed.

(** Let's introduce our own tactic to handle both that bullet and the
    bullet from example 1: *)

Ltac assertion_auto :=
  try auto;  (* as in example 1, above *)
  try (unfold "->>", assertion_sub, t_update;
       intros; simpl in *; lia). (* as in example 2 *)

Example assertion_sub_example2'' :
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assertion_auto.
Qed.

Example hoare_asgn_example1''':
  {{True}} X := 1 {{X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assertion_auto.
Qed.

(** Again, we have quite a nice proof script.  All the low-level
    details of proofs about assertions have been taken care of
    automatically. Of course, [assertion_auto] isn't able to prove
    everything we could possibly want to know about assertions --
    there's no magic here! But it's good enough so far. *)

(* ================================================================= *)
(** ** Sequencing + Assignment *)

(** Here's an example of a program involving both sequencing and
    assignment.  Note the use of [hoare_seq] in conjunction with
    [hoare_consequence_pre] and the [eapply] tactic. *)

Example hoare_asgn_example3 : forall (a:aexp) (n:nat),
  {{a = n}}
    X := a;
    skip
  {{X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  - (* right part of seq *)
    apply hoare_skip.
  - (* left part of seq *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto.
Qed.

(** Informally, a nice way of displaying a proof using the sequencing
    rule is as a "decorated program" where the intermediate assertion
    [Q] is written between [c1] and [c2]:

  {{ a = n }}
     X := a
              {{ X = n }};    <--- decoration for Q
     skip
  {{ X = n }}
*)
(** We'll come back to the idea of decorated programs in much more
    detail in the next chapter. *)

(* ================================================================= *)
(** ** Conditionals *)

(** What sort of rule do we want for reasoning about conditional
    commands?

    Certainly, if the same assertion [Q] holds after executing
    either of the branches, then it holds after the whole conditional.
    So we might be tempted to write:

              {{P}} c1 {{Q}}
              {{P}} c2 {{Q}}
      ---------------------------------
      {{P}} if b then c1 else c2 {{Q}}
*)

(** However, this is rather weak. For example, using this rule,
   we cannot show

     {{ True }}
       if X = 0
         then Y := 2
         else Y := X + 1
       end
     {{ X <= Y }}

   since the rule tells us nothing about the state in which the
   assignments take place in the "then" and "else" branches. *)

(** Better:

              {{P /\   b}} c1 {{Q}}
              {{P /\ ~ b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} if b then c1 else c2 end {{Q}}
*)

(** To make this formal, we need a way of formally "lifting"
    any bexp [b] to an assertion.

    We'll write [bassertion b] for the assertion "the boolean expression
    [b] evaluates to [true]." *)

Definition bassertion b : Assertion :=
  fun st => (beval st b = true).

Coercion bassertion : bexp >-> Assertion.

Arguments bassertion /.

(** A useful fact about [bassertion]: *)

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassertion b) st).
Proof. congruence. Qed.

Hint Resolve bexp_eval_false : core.

(** Now we can formalize the Hoare proof rule for conditionals
    and prove it correct. *)

Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  {{ P /\ b }} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.
(** That is (unwrapping the notations):

      Theorem hoare_if : forall P Q b c1 c2,
        {{fun st => P st /\ bassertion b st}} c1 {{Q}} ->
        {{fun st => P st /\ ~ (bassertion b st)}} c2 {{Q}} ->
        {{P}} if b then c1 else c2 end {{Q}}.
*)
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst; eauto.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Example *)

Example if_example :
  {{True}}
    if (X = 0)
      then Y := 2
      else Y := X + 1
    end
  {{X <= Y}}.
Proof.
  apply hoare_if.
  - (* Then *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto. (* no progress *)
      unfold "->>", assertion_sub, t_update, bassertion.
      simpl. intros st [_ H]. apply eqb_eq in H.
      rewrite H. lia.
  - (* Else *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto.
Qed.

(** As we did earlier, it would be nice to eliminate all the low-level
    proof script that isn't about the Hoare rules.  Unfortunately, the
    [assertion_auto] tactic we wrote wasn't quite up to the job.  Looking
    at the proof of [if_example], we can see why.  We had to unfold a
    definition ([bassertion]) and use a theorem ([eqb_eq]) that we didn't
    need in earlier proofs.  So, let's add those into our tactic, and
    clean it up a little in the process. *)

Ltac assertion_auto' :=
  unfold "->>", assertion_sub, t_update, bassertion;
  intros; simpl in *;
  try rewrite -> eqb_eq in *; (* for equalities *)
  auto; try lia.

(** Now the proof is quite streamlined. *)

Example if_example'' :
  {{True}}
    if X = 0
      then Y := 2
      else Y := X + 1
    end
  {{X <= Y}}.
Proof.
  apply hoare_if.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto'.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto'.
Qed.

(** We can even shorten it a little bit more. *)

Example if_example''' :
  {{True}}
    if X = 0
      then Y := 2
      else Y := X + 1
    end
  {{X <= Y}}.
Proof.
  apply hoare_if; eapply hoare_consequence_pre;
    try apply hoare_asgn; try assertion_auto'.
Qed.

(** For later proofs, it will help to extend [assertion_auto'] to handle
    inequalities, too. *)

Ltac assertion_auto'' :=
  unfold "->>", assertion_sub, t_update, bassertion;
  intros; simpl in *;
  try rewrite -> eqb_eq in *;
  try rewrite -> leb_le in *;  (* for inequalities *)
  auto; try lia.

(** [] *)

(* ================================================================= *)
(** ** While Loops *)

(** The Hoare rule for [while] loops is based on the idea of a
    _command invariant_ (or just _invariant_): an assertion whose
    truth is guaranteed after executing a command, assuming it is true
    before.

    That is, an assertion [P] is a command invariant of [c] if

      {{P}} c {{P}}

    holds.  Note that the command invariant might temporarily become
    false in the middle of executing [c], but by the end of [c] it
    must be restored. *)

(** The Hoare while rule combines the idea of a command invariant with
     information about when guard [b] does or does not hold.

            {{P /\ b}} c {{P}}
      --------------------------------- (hoare_while)
      {{P} while b do c end {{P /\ ~b}}
*)

Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{P /\ ~ b}}.
Proof.
  intros P b c Hhoare st st' Heval HP.
  (* We proceed by induction on [Heval], because, in the "keep looping" case,
     its hypotheses talk about the whole loop instead of just [c]. The
     [remember] is used to keep the original command in the hypotheses;
     otherwise, it would be lost in the [induction]. By using [inversion]
     we clear away all the cases except those involving [while]. *)
  remember <{while b do c end}> as original_command eqn:Horig.
  induction Heval;
    try (inversion Horig; subst; clear Horig);
    eauto.
Qed.

(** We call [P] a _loop invariant_ of [while b do c end] if

      {{P /\ b}} c {{P}}

    is a valid Hoare triple.

    This means that [P] will be true at the end of the loop body
    whenever the loop body executes. If [P] contradicts [b], this
    holds trivially since the precondition is false.

    For instance, [X = 0] is a loop invariant of

      while X = 2 do X := 1 end

    since the program will never enter the loop. *)


(* ----------------------------------------------------------------- *)
(** *** EXAMPLES *)

(** We can _derive_ an assigment rule modulo consequence that is
easier to use since the precondition is any propitions that entails the required
substitution:*)
Theorem hoare_asg_conseq:   forall P Q X a,
    P ->> Q [X |-> a] -> {{P}} X := a {{Q}}.
  Proof.
    intros .
    apply hoare_consequence_pre with (Q [X |-> a]).
    - apply hoare_asgn.
    - assumption.
  Qed.

  (** A derived rule for [while] modulo weakening the postcondition:*)
  Theorem hoare_while_conseq : forall P Q(b:bexp) c,
    {{P /\ b}} c {{P}} -> (fun st => P st /\ ~ (bassertion b st)) ->> Q ->
    {{P}} while b do c end {{Q}}.
    Proof.
    intros P Q b C H Himp.
    eapply hoare_consequence_post; try apply hoare_while; assumption.
    Qed.

Print     subtract_slowly_body.

Theorem  subtract_slowly_body_spec:  forall n m : nat,
    {{X = n /\  Z = m}}
      subtract_slowly_body
    {{Z = m - 1 /\ X = n - 1}}.
Proof.
  unfold subtract_slowly_body.
  intros.
  eapply hoare_seq.
  - eapply hoare_asgn.
  -  eapply hoare_asg_conseq.
     assertion_auto .
Qed.


Definition reduce_to_zero : com :=
  <{ while X <> 0 do X := X - 1 end }>.

Lemma reduce_to_zero_correct_:
  {{True}}
    reduce_to_zero
  {{X = 0}}.
Proof.
  unfold reduce_to_zero.
  eapply hoare_while_conseq.
  - eapply hoare_asg_conseq.
    assertion_auto.
  - assertion_auto''.
    destruct H.  apply eq_true_negb_classical in H0.
    apply eqb_eq. assumption.
Qed.

(* ################################################################# *)
(** * Summary *)

(** The rules of Hoare Logic are:

             --------------------------- (hoare_asgn)
             {{Q [X |-> a]}} X:=a {{Q}}

             --------------------  (hoare_skip)
             {{ P }} skip {{ P }}

               {{ P }} c1 {{ Q }}
               {{ Q }} c2 {{ R }}
              ----------------------  (hoare_seq)
              {{ P }} c1;c2 {{ R }}

              {{P /\   b}} c1 {{Q}}
              {{P /\ ~ b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} if b then c1 else c2 end {{Q}}

               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} while b do c end {{P /\ ~ b}}

                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
*)

(** Our task in this chapter has been to _define_ the rules of Hoare
    logic, and prove that the definitions are sound.  Having done so,
    we can now work _within_ Hoare logic to prove that particular
    programs satisfy particular Hoare triples.  In the next chapter,
    we'll see how Hoare logic is can be used to prove that more
    interesting programs satisfy interesting specifications of their
    behavior.

    Crucially, we will do so without ever again [unfold]ing the
    definition of Hoare triples -- i.e., we will take the rules of
    Hoare logic as a closed world for reasoning about programs. *)



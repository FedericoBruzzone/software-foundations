Require Import Coq.Lists.List.
Import ListNotations.

(* 3.1
Prove the following logical principles without automation: no auto, no tauto, no firstorder
*)

Theorem contrapositive : forall (P Q : Prop),  (P -> Q) -> (~Q -> ~P).
Proof.
  intro P.
  intro Q.
  intro H.
  intro H1.
  intro H2.
  apply H1.
  apply H.
  apply H2.
Qed.

(* 3.1 bis: write the same proof as a text file in a mathematical form using
the rules of natural deduction: I'll get you started:

P, Q
P -> Q
 .
 .
 .

  (~Q -> ~P).
--------------------------------------- (-> intro)
 (P -> Q) -> (~Q -> ~P)
---------------------------------------------------------- (forall intro)
forall (P Q : Prop),  (P -> Q) -> (~Q -> ~P).


*)
Theorem dist_exists_or : forall (A : Type) (P Q : A -> Prop),
            (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  (* Here *)
Admitted.

(* the double negation principle requires the following classical axiom *)
Axiom excluded_middle : forall P : Prop,
  P \/ ~ P.

Theorem  dnn: forall P, ~~ P  -> P.
  (* Here *)
  Admitted.

  (* 3.2 State and prove the injectivity, disjointness and occur check property
for polymorphic List, similarly to what we did in class (Logic.v) for Nats.
 To get you started, here is the statement for disjointness*)


Theorem  list_disj: forall (X :Type) (x  : X) (xs  : list X),
    ( [] <> (x :: xs)) .
    (* Here *)
    Admitted.

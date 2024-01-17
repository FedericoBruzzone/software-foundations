(** * StlcProp: Properties of STLC *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From PLF Require Import TypesAM.
From PLF Require Import Stlc.
From PLF Require Import SmallstepAM.
From Hammer Require Import Hammer.
Module STLCProp.
Import STLC.

(** In this chapter, we develop the fundamental theory of the Simply
    Typed Lambda Calculus -- in particular, the type safety
    theorem. *)

(* ################################################################# *)
(** * Canonical Forms *)

(** The first step in establishing basic properties of
    reduction and types is to identify the possible _canonical
    forms_ belonging to each type.  For
    [Bool], these are again the boolean values [true] and [false]; for
    arrow types, they are lambda-abstractions.

    Formally, we will need these lemmas only for terms that are not
    only well typed but _closed_ -- well typed in the empty
    context. *)

Lemma canonical_forms_bool : forall t,
  empty |--  t \in Bool ->
  value t ->
  (t = <{true}>) \/ (t = <{false}>).
Proof.
  intros t HT HVal.
  destruct HVal; inversion HT; auto.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty |--  t \in (T1 -> T2) ->
  value t ->
  exists x u, t = <{\x:T1, u}>.
Proof.
  intros t T1 T2 HT HVal.
  destruct HVal; inversion HT; subst.
  eauto.
Qed.

(* ################################################################# *)
(** * Progress *)

(** The _progress_ theorem tells us that closed, well-typed
    terms are not stuck. *)

Theorem progress : forall t T,
  empty |--  t \in T ->
  value t \/ exists t', t --> t'.
Proof.
  intros t T Ht.
  remember empty as Gamma.
  induction Ht; subst; auto.
  (* auto solves all three cases in which t is a value *)
  - (* T_Var *)
    (* contradictory: variables cannot be typed in an
       empty context *)
    inversion H.
  - (* T_App *)
    (* [t] = [t1 t2].  Proceed by cases on whether [t1] is a
       value or steps... *)
    right. destruct IHHt1; trivial. 
    + (* t1 is a value *)
      destruct IHHt2; trivial.
      * (* t2 is also a value *)
        eapply canonical_forms_fun in Ht1; try assumption.
        destruct Ht1 as [x [t0 H1]]. subst.
        eauto.
      * (* t2 steps *)
        destruct H0 as [t2' Hstp]. eauto . 
    + (* t1 steps *)
      destruct H as [t1' Hstp]. eauto.
  - (* T_If *)
    right. destruct IHHt1; trivial.
    + (* t1 is a value *)
      destruct (canonical_forms_bool t1); subst; eauto.
    + (* t1 also steps *)
      destruct H as [t1' Hstp]. eauto.

      Qed.

(* ################################################################# *)
(** * Preservation *)

(** For preservation, we need some technical machinery for
    reasoning about variables and substitution.

      - The _preservation theorem_ is proved by induction on a typing
        derivation, pretty much as we did in the [Types] chapter.

        Main novelty: [ST_AppAbs] uses the substitution operation.

        To see that this step preserves typing, we need to know that
        the substitution itself does.  So we prove a...

      - _substitution lemma_, stating that substituting a (closed,
        well-typed) term [s] for a variable [x] in a term [t]
        preserves the type of [t].

        The proof goes by induction on the form of [t] and requires
        looking at all the different cases in the definition of
        substitition.

        Tricky case: variables.
        In this case, we need to deduce from the fact that a term [s]
        has type S in the empty context the fact that [s] has type S
        in every context. For this we prove a...

      - _weakening_ lemma, showing that typing is preserved under
        "extensions" to the context [Gamma].
*)

(* ================================================================= *)
(** ** The Weakening Lemma *)

(** Typing is preserved under "extensions" to the context [Gamma].
    (Recall the definition of "includedin" from Maps.v.) *)

Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     Gamma  |--  t \in T  ->
     Gamma' |--  t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using includedin_update.
Qed.

(** The following simple corollary is what we actually need below. *)

Lemma weakening_empty : forall Gamma t T,
     empty |--  t \in T  ->    Gamma |--  t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.

(* ================================================================= *)
(** ** A Substitution Lemma *)

(** Now we come to the conceptual heart of the proof that reduction
    preserves types -- namely, the observation that _substitution_
    preserves types. *)

(** The _substitution lemma_ says:

    - Suppose we have a term [t] with a free variable [x], and
      suppose we've been able to assign a type [T] to [t] under the
      assumption that [x] has some type [U].

    - Also, suppose that we have some other _program_ [v] (closed term) and that we've
      shown that [v] has type [U].

    - Then we can substitute [v] for each of the occurrences of
      [x] in [t] and obtain a new term that still has type [T]. *)

Lemma substitution_preserves_typing : forall Gamma x U t v T,
  x |-> U ; Gamma |--  t \in T ->
                           empty |--  v \in U   ->
                                          Gamma |--  [x:=v]t \in T.
Proof.
  intros Gamma x U t v T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
  (* in each case, we'll want to get at the derivation of H *)
    inversion H; clear H; subst; simpl; eauto.
  - (* var *)
    rename s into y. destruct (eqb_spec x y); subst.
    + (* x=y *)
      rewrite update_eq in H2.
      inversion H2; subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      rewrite update_neq in H2; auto.
  - (* abs *)
    rename s into y, t into S.
    destruct (eqb_spec x y); subst; apply T_Abs.
    + (* x=y *)
      rewrite update_shadow in H5. assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto.
Qed.



(* ================================================================= *)
(** ** Proof of Preservation *)

(** We now have the ingredients we need to prove preservation: if a
    closed, well-typed term [t] has type [T] and takes a step to [t'],
    then [t'] is also a closed term with type [T].  In other words,
    the small-step reduction relation preserves types. *)

Theorem preservation : forall t t' T,
  empty |--  t \in T  ->
  t --> t'  ->
  empty |--  t' \in T.

Proof .
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT;
    sauto l:on use:substitution_preserves_typing.
      Restart.
      (* all cases in detail *)
       intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT;
       intros t' HE; subst.
       - inversion HE. (* var, imposs*)
       - inversion HE. (* lam, imposs*)
       - (* app *) inversion HE. subst.
       + (* beta *)  inversion_clear HT1. 
       apply substitution_preserves_typing with T2; eauto.
       + (* cong 1*) subst. apply T_App with T2. apply IHHT1; auto.
       ++ assumption.
       + (* cong 2 *)
        subst. apply T_App with T2; try assumption.
        ++ apply IHHT2; auto.
        -  inversion HE. (* true, imposs*)
        - inversion HE. (* false, imposs *)
        
       - (* if *) inversion HE; subst.
       + (* true *) assumption.
       + (* false *)  assumption.
       + (* cong *)  
       constructor. 
       ++  apply IHHT1; auto.
       ++ assumption. 
       ++ assumption.  
      Qed.

(** Note that our choice of restricting substitutions to _closed_ terms forced us to the above formulation, rather than the standard:

forall t t' T Gamma,
  Gamma |--  t \in T  ->  t --> t'  ->  Gamma |--  t' \in T.
*)

(* ################################################################# *)
(** * Uniqueness of Types *)

(** Another nice property of the STLC is that types are unique: a
    given term (in a given context) has at most one type. *)

Theorem unique_types : forall Gamma e T T',
  Gamma |--  e \in T  ->
  Gamma |--  e \in T' ->
                 T = T'.
Proof.
   intros Gamma e T T' Htyp. generalize dependent T'.
   induction Htyp; sauto.
   Restart.
  intros Gamma e T T' Htyp. generalize dependent T'.
  induction Htyp; intros T' Htyp'; inversion Htyp'; subst; auto.
  - (* T_Var *)
    rewrite H in H2. congruence.
  - (* T_Abs *)
    apply IHHtyp in H4. subst. reflexivity.
  - (* T_App *)
    apply IHHtyp1 in H2. congruence.
Qed.


End STLCProp.


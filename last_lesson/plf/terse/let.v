Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
 From PLF Require Import TypesAM.
From PLF Require Import Stlc.
 From PLF Require Import SmallstepAM.
Import STLC.


(** ** PART 1: Let Bindings *)

(** When writing a complex expression, it is useful to be able
    to give names to some of its subexpressions to avoid repetition
    and increase readability.  Most languages provide one or more ways
    of doing this.  In OCaml (and Coq), for example, we can write [let
    x=t1 in t2] to mean "reduce the expression [t1] to a value and
    bind the name [x] to this value while reducing [t2]."

    Our [let]-binder follows OCaml in choosing a standard
    _call-by-value_ evaluation order, where the [let]-bound term must
    be fully reduced before reduction of the [let]-body can begin.
    The typing rule [T_Let] tells us that the type of a [let] can be
    calculated by calculating the type of the [let]-bound term,
    extending the context with a binding with this type, and in this
    enriched context calculating the type of the body (which is then
    the type of the whole [let] expression).

    It's probably easier simply to look at
    the rules defining this new feature than to wade through a lot of
    English text conveying the same information.  Here they are: *)


(** Syntax:
<<
       t ::=                                   Terms
           | ...                                 (other terms same as before)
           | let x : S = t in t             let-binding
>>
*)

(**
    Reduction:
[[[
                                 t1 --> t1'
                     ----------------------------------               (ST_Let1)
                     let x : S = t1 in t2 --> let x : S =t1' in t2

                        ----------------------------              (ST_LetValue)
                        let x  : S = v1 in t2 --> [x:=v1]t2
]]]
    Typing:
[[[
             Gamma |- t1 \in T1      x |-> T1; Gamma |- t2 \in T2
             --------------------------------------------------        (T_Let)
                        Gamma |- let x : T1 = t1 in t2 \in T2
]]]
*)

(**
However, a little thought reveals that you do _not_ need to assume
[let] as a primitive, since it can be defined in terms of abstraction and
application.  This is why we annotate the variable [x] with a type [S], which
is not needed in standard functional programming where type inference is available.

In this exercise, you will do that and prove that the above typing
and reduction rules are _derived_, i.e., that can be proven as
stand alone theorems w/o extending the static and dynamic semantics

Do NOT use [sauto], if you can
*)

(** change the RHS: defining a pretty [Notation] is up to you: *)
Definition tm_let (x : string) (S : ty) (t1 t2 : tm) : tm :=
  tm_app (tm_abs x S t2) t1.

Notation "'let' x ':' S '=' t1 'in' t2" := (tm_let x S t1 t2) (in custom stlc at level 50, right associativity).

Theorem tm_typing_reduction : forall Gamma x t1 T1 t2 T2,
  Gamma |-- t1 \in T1 ->
  x |-> T1; Gamma |-- t2 \in T2 ->
  Gamma |-- (let x : T1 = t1 in t2) \in T2.
Proof.
  intros.
  apply T_App with (T2 := T1).
  - apply T_Abs. trivial.
  - trivial.
Qed.

(** ** PART 2*)

(**
Look at terse/StlcPropAM.html and prove type_soundness  by putting progress and preservation together and showing that a well-typed term can never reach a stuck state.
*)


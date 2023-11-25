(*  To be handed in by Oct 16, 2300 hour on upload.di.unimi.it *)
Require Import Coq.Lists.List.
Import ListNotations.

Definition admit {T: Type} : T.  Admitted.


(* 1. Consider the  classical definition of the function [fold] (right) *)

Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(*1.1  As well known, many
common functions on lists can be implemented in terms of fold.

Define [fold_lenght] that redefines the length of a poly list
via [fold] *)


(**
1.2 Show that [fold_length] is equivalent to [length]
*)

(**
2. Rember the definitions of [map] and (naive[rev]) *)
Print rev.
Print map.
(**
  2.1 Show that map and rev commute. You need to prove an auxiliary lemma. Try
to  state it as general as possible
*)


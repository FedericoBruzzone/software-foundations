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

Definition fold_length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | _ :: t => fold (fun _ n => S n) t 1
  end.

Example test_fold_length0 : @fold_length nat [] = 0. Proof. reflexivity. Qed.
Example test_fold_length3 : fold_length [4;7;0] = 3. Proof. reflexivity. Qed.

(**
1.2 Show that [fold_length] is equivalent to [length]
*)
Example test_length : length [1] = 1. Proof. reflexivity. Qed.

Theorem fold_length_eq_length : forall (l : list nat), fold_length l = length l.
Proof.
  intros l.
  induction l as [| h t IH].
  - reflexivity.
  - simpl.
    rewrite <- IH.
    destruct t.
      + reflexivity.
      + reflexivity.
Qed.

(**
2. Rember the definitions of [map] and (naive[rev]) *)
Print rev.
Print map.
(**
  2.1 Show that map and rev commute. You need to prove an auxiliary lemma. Try
to  state it as general as possible
*)
Example test_map : map (fun x => x + 1) [1;2;3] = [2;3;4]. Proof. reflexivity. Qed.
Example test_rev : rev [1;2;3] = [3;2;1]. Proof. reflexivity. Qed.
Example test_map_rev : map (fun x => x + 1) (rev [1;2;3]) = rev (map (fun x => x + 1) [1;2;3]). Proof. reflexivity. Qed.

Lemma List_map_app : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X), map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros X Y f l1 l2.
  induction l1 as [| h1 t1 IHl1'].
  - reflexivity.
  - simpl.
    rewrite <- IHl1'.
    reflexivity.
Qed.

Theorem map_rev_commute : forall (X Y : Type) (f : X -> Y) (l : list X), map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l as [| h t IHl'].
  - reflexivity.
  - simpl.
    rewrite <- IHl'.
    rewrite -> List_map_app. (* rewrite -> map_app. *)
    reflexivity.
Qed.


Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m -> le n (S m).

Notation "n <= m" := (le n m) (at level 70).

Example le_3_5 : 3 <= 5.
Proof.
  apply le_S.
  apply le_S.
  apply le_n.
Qed.

Require Import List.
Import ListNotations.

Inductive AllDistinct {A : Type} : list A -> Prop :=
| Dist_nil : AllDistinct []
| Dist_cons : forall x l, 
    ~ In x l ->
    AllDistinct l -> 
    AllDistinct (x :: l).

Goal AllDistinct [1;2;3].
Proof.
  constructor.
  simpl.
  intro H.
  destruct H.
  discriminate.
  destruct H.
  discriminate.
  apply H.
  constructor.
  simpl.
  intro H.
  destruct H.
  discriminate.
  contradiction.
  constructor.
  simpl.
  intro H.
  apply H.
  constructor.
Qed.

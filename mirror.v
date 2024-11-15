Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.

Inductive btree : Type :=
| Empty : btree
| Node : Z -> btree -> btree -> btree.

Fixpoint solution (t:btree) : btree :=
    match t with
    | Empty => Empty
    | Node n l r => Node n (solution r) (solution l)
    end.

Theorem test1: forall t, solution (solution t) = t.
Proof.
    intros.
    induction t.
    simpl.
    reflexivity.
    simpl.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
    Qed.
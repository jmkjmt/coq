Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.

Inductive btree : Type :=
| Empty : btree
| Node : Z -> btree -> btree -> btree.

Fixpoint solution (n:Z) (tree:btree) : bool :=
    match tree with
    | Empty => false
    | Node m l r => if Z.eqb n m then true else (solution n l) || (solution n r)
    end.
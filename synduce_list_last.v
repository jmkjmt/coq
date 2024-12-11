Require Import Bool.

Inductive Unit : Type :=
    | Null : Unit.

Inductive Nat : Type :=
    | Zero : Nat
    | Succ : Nat -> Nat.
Inductive BTree : Type :=
    | Empty : Unit -> BTree
    | Node : Nat -> BTree -> BTree -> BTree.

Inductive Zipper : Type :=
    | Top : Unit -> Zipper
    | Left : Nat -> BTree -> Zipper -> Zipper
    | Right : Nat -> BTree -> Zipper -> Zipper.

Fixpoint plus n1 n2 : Nat :=
    match n1 with
    | Zero => n2
    | Succ n1' => Succ (plus n1' n2)
    end.

Fixpoint tf1 tree : Nat :=
    match tree with
    | Empty _ => Zero
    | Node n t1 t2 => plus n (plus (tf1 t1) (tf1 t2))
    end.

Definition sum tree : Nat :=
    tf1 tree.

Fixpoint tf3 zipper : BTree :=
    match zipper with
    | Top _ => Empty Null
    | Left n t z => Node n t (tf3 z)
    | Right n t z => Node n (tf3 z) t
    end.

Definition repr zipper : BTree :=
    tf3 zipper.

Definition main zipper : Nat :=
    sum (repr zipper).

Fixpoint tf5 zipper : Nat :=
    match zipper with
    | Top _ => Zero
    | Left n t z => plus (tf5 z) (plus n (sum t))
    | Right n t z => plus (tf5 z) (plus n (sum t))
    end.

Definition reprNew zipper : Nat :=
    tf5 zipper.

Definition mainNew zipper : Nat :=
    reprNew zipper.

Lemma l1 : forall b : BTree, plus (tf1 b) Zero = sum b.
Proof.
    assert(forall n, plus n Zero = n).
    {
        induction n.
        simpl.
        reflexivity.
        simpl.
        rewrite IHn.
        reflexivity.
    }
    intros.
    rewrite H.
    induction b.
    simpl.
    reflexivity.
    simpl.
    rewrite IHb1.
    rewrite IHb2.
    reflexivity.
Qed.

Theorem equiv : forall inp0: Zipper , main inp0 = mainNew inp0.
Proof.
    assert(forall n m b , plus n (plus (tf1 b) m) = plus m (plus n (sum b))).
    {
        induction n.
        simpl.
        induction m.
        simpl.
        apply l1.
        simpl.

    }
    unfold main.
    unfold sum.
    unfold mainNew.
    unfold repr.
    unfold reprNew.
    induction inp0.
    simpl.
    reflexivity.
    simpl.
    rewrite IHinp0.
    


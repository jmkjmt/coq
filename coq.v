Require Import Arith.
Require Import Lia.
Require Import Bool.
Require Import List.
Lemma example2 : forall a b: Prop, a /\ b ->  b /\ a.
Proof.
    intros a b H.
    split.
    destruct H as [H1 H2].
    exact H2.
    intuition.
    Qed.
Lemma example3 : forall a b : Prop, a \/ b -> b \/ a.
Proof.
    intros a b H.
    destruct H as [H1 | H1].
    right; assumption.
    left;assumption.
    Qed.

Lemma example5: forall x y, x <= 10 -> 10 <= y -> x <= y.
Proof.
    intros x y x10 y10.
    apply Nat.le_trans with (m := 10).
    assumption.
    assumption.
    Qed.

Check Nat.mul_add_distr_r.

Lemma example6: forall x y , (x+y) * (x+y) = x*x + 2*x*y+ y*y.
Proof.
    intros x y.
    rewrite Nat.mul_add_distr_l.
    rewrite Nat.mul_add_distr_r.
    rewrite Nat.mul_add_distr_r.
    Search (_+ (_+_)).
    rewrite Nat.add_assoc.
    Search (_*_ = _*_).
    rewrite <- Nat.add_assoc with (n := x * x).
    rewrite Nat.mul_comm with (n := y) (m:=x).
    Search ( _ + _ ).
    SearchRewrite ( S _ * _).
    rewrite <- (Nat.mul_1_l (x * y)) at 1.
    rewrite <- Nat.mul_succ_l.
    SearchRewrite (_*_).
    rewrite Nat.mul_assoc.
    reflexivity.
    Qed.

Print Nat.pred.
Lemma pred_S_eq : forall x y , x = S y -> Nat.pred x = y.
Proof.
    intros x y H.
    unfold Nat.pred.
    rewrite H.
    reflexivity.
    Qed.

Lemma example7: forall x y , (x+y) * (x+y) = x*x + 2*x*y+ y*y.
Proof.
    intros x y.
    lia.
    Qed.

Lemma e1: forall A B C:Prop, A /\ (B/\C) -> (A/\B)/\C.
Proof.
    intros A B C H.
    Search (_ /\  _ /\ _).
    Search and_comm.
    rewrite <- and_assoc in H.
    apply H.
    Qed.
Lemma e2: forall A B C D: Prop, (A->B)/\(C->D)/\A/\C -> B/\D.
Proof.
    intros A B C D H.
    destruct H as [H1 H2].
    destruct H2 as [H2 H3].
    destruct H3 as [H3 H4].
    split.
    apply H1.
    apply H3.
    apply H2.
    apply H4.
    Qed.
Lemma e3: forall A: Prop, ~(A/\~A).
Proof.
    intros.
    unfold not.
    intros [H1 H2].
    apply H2.
    apply H1.
    Qed.

Lemma e4 : forall A B C: Prop, A\/(B\/C) -> (A\/B)\/C.
Proof.
    intros A B C H.
    rewrite <- or_assoc in H.
    apply H.
    Qed.
Lemma e5: forall A B : Prop, (A\/B)/\~A -> B.
Proof.
    intros A B H.
    destruct H as [H1 H2].
    destruct H1.
    apply H2 in H.
    contradiction.
    apply H.
    Qed.
Lemma e6: forall A:Type, forall P Q : A -> Prop,
(forall x, P x)\/ (forall y, Q y) -> forall x, P x \/ Q x.
Proof.
    intros A P Q H.
    destruct H.
    left.
    apply H.
    right.
    apply H.
    Qed.
    
Fixpoint sum_n n:=
    match n with
    0 => 0
    | S p => p + sum_n p
    end.
Lemma sum_n_p: forall n, 2 * sum_n n+n = n*n.
Proof.
    induction n.
    simpl.
    reflexivity.
    assert (SnSn : S n * S n = n * n+ 2 * n + 1).
    ring.
    rewrite SnSn.
    rewrite <- IHn.
    simpl.
    ring.
    Qed.

Fixpoint evenb n :=
match n with
0 => true| 1 => false
| S (S p) => evenb p
end.
Lemma evenb_p : forall n, evenb n = true -> exists x, n = 2 * x.
Proof.
    assert (Main: forall n, (evenb n = true -> exists x, n = 2*x) /\ (evenb (S n) = true -> exists x, S n = 2 * x)).
    induction n.
    split.
    exists 0; ring.
    simpl.
    intros H.
    discriminate.
    split.
    destruct IHn as [_ IHn'].
    exact IHn'.
    simpl evenb.
    intros H.
    destruct IHn as [IHn' _].
    assert (H' : exists x, n = 2*x).
    apply IHn'.
    exact H.
    destruct H' as [x q].
    exists (x+1).
    rewrite q.
    ring.
    
    
    intros n ev.
    destruct (Main n) as [H _].
    apply H.
    exact ev.
    Qed.

Fixpoint add n m := match n with 0 => m | S p => add p (S m) end.

Lemma add1: forall n m, add n (S m) = S (add n m).
Proof.
    induction n.
    simpl.
    reflexivity.
    simpl.
    intros m.
    apply IHn.
    Qed.

Lemma add2: forall n m, add (S n) m = S (add n m).
Proof.
    induction n.
    simpl.
    reflexivity.
    simpl.
    intros m.
    apply IHn.
    Qed.

Lemma add3: forall n m, add n m = n + m.
Proof.
    induction n.
    simpl.
    reflexivity.
    simpl.
    intros m.
    rewrite IHn.
    ring.
    Qed.
Fixpoint sum_odd_n (n:nat) : nat :=
    match n with
    0 => 0
    | S p => 1 + 2 * p + sum_odd_n p end.

Lemma son: forall n:nat, sum_odd_n n = n*n.
Proof.
    induction n.
    simpl.
    reflexivity.
    simpl sum_odd_n.
    rewrite IHn.
    ring.
    Qed.

Definition is_zero (n:nat):=
match n with
0 => true
| S p => false
end.
Lemma not_is_zero_pred: forall x:nat , is_zero x = false -> S (Nat.pred x) = x.
Proof.
    intros x.
    unfold is_zero, Nat.pred.
    destruct x.
    discriminate.
    intros.
    reflexivity.
    Qed.

Fixpoint count n l :=
match l with
| nil => 0
| a::tl => let r := count n tl in if n =? a then 1+r else r
end.
Fixpoint insert n l :=
match l with
nil => n :: nil
| a::tl => if n <=? a then n ::l else a :: insert n tl
end.

Fixpoint sort l :=
match l with
nil => nil
| a::tl => insert a (sort tl)
end.
Lemma insert_incr : forall n l, count n (insert n l) = 1 + count n l.
Proof.
    intros n l.
    induction l.
    simpl.
    rewrite Nat.eqb_refl.
    reflexivity.
    simpl.
    case (n <=? a).
    simpl.
    rewrite Nat.eqb_refl.
    reflexivity.
    simpl.
    case (n =? a).
    rewrite IHl.
    reflexivity.
    rewrite IHl.
    reflexivity.
    Qed.

Inductive bin : Type :=
| L : bin
| N : bin -> bin -> bin.

Definition e7 (t : bin) : bool :=
match t with 
N L L => false
| _ => true end.

Fixpoint size (t: bin) : nat :=
match t with
| L => 1
| N t1 t2 => 1 + size t1 + size t2
end.

Fixpoint flatten_aux (t1 t2:bin) : bin :=
match t1 with
| L => N L t2
| N t'1 t'2 => flatten_aux t'1 (flatten_aux t'2 t2)
end.

Fixpoint flatten (t:bin) : bin :=
match t with
| L => L
| N t1 t2 => flatten_aux t1 (flatten t2)
end.
Lemma e7_size : forall t, e7 t = false -> size t = 3.
Proof.
    intros.
    destruct t.
    simpl.
    discriminate.
    destruct t1.
    destruct t2.
    simpl.
    reflexivity.
    simpl.
    discriminate.
    simpl.
    discriminate.
    Qed.

Lemma flatten_aux_size : forall t1 t2, size (flatten_aux t1 t2) = size t1 + size t2 + 1.
Proof.
    induction t1.
    intros t2.
    simpl.
    ring.
    simpl.
    intros t2.
    rewrite IHt1_1.
    rewrite IHt1_2.
    ring.
    Qed.

Lemma flatten_size : forall t, size (flatten t) = size t.
Proof.
    intros.
    induction t.
    simpl.
    reflexivity.
    simpl.
    induction t1.
    simpl.
    rewrite IHt2.
    reflexivity.
    simpl.
    rewrite flatten_aux_size.
    rewrite flatten_aux_size.
    rewrite IHt2.
    ring.
    Qed.

Lemma not_subterm_self_l : forall x y, ~x = N x y.
Proof.
    induction x.
    discriminate.
    intros y abs.
    injection abs.
    intros h1 h2.
    assert (IHx1' : x1 <> N x1 x2).
    apply IHx1.
    case IHx1'.
    exact h2.
    Qed.

Inductive even : nat -> Prop :=
even0 : even 0
|evenS : forall x:nat, even x -> even (S (S x)).

Inductive even2 : nat -> Prop :=
even02 : even2 10
|even2S : forall x: nat, even2 x -> even2 (S (S x)).


Lemma even_mult : forall x, even x -> exists y, x = 2 *y.
Proof.
    intros x H.
    induction H.
    exists 0.
    reflexivity.
    destruct IHeven as [y Heq].
    rewrite Heq.
    exists (y+1).
    ring.
    Qed.

Lemma not_even_1: ~even 1.
Proof.
    intuition.
    inversion H.
    Qed.

Lemma even_inv : forall x, even (S (S x)) -> even x.
Proof.
    intros x H.
    inversion H.
    apply H1.
    Qed.
Lemma even' : even2 12.
Proof.
    apply even2S.
    apply even02.
    Qed.
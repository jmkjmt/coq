From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Bool.
From Coq Require Import ZArith.
From Coq Require Import Lia.
From Coq Require Import Program.

Import ListNotations.

Lemma l1 : forall x : list nat, x++[] = x.
Proof.
  induction x.
  reflexivity.
  simpl.
  rewrite IHx.
  reflexivity.
Qed.
Theorem clam_11 : forall (x y : list nat) , List.rev ((List.rev x) ++ (List.rev y)) = y ++ x.
Proof.
  assert(forall (x : list nat ) (a : nat), rev (x ++ [a]) = a :: rev x).
    {
      induction x.
      reflexivity.
      simpl.
      intros.
      rewrite IHx.
      reflexivity.
    }
  assert (forall x : list nat, List.rev (List.rev x) = x).
  {
    induction x.
    reflexivity.
    simpl.
    rewrite H.
    rewrite IHx.
    reflexivity.
  }
  intros.
  generalize dependent x.
  induction y.
  simpl.
  intros.
  rewrite l1.
  rewrite H0.
  reflexivity.
  intros.
  simpl.
  rewrite app_assoc.
  rewrite H.
  rewrite IHy.
  reflexivity.
Qed.
Fixpoint insert (a : nat) (x : list nat) : list nat :=
  match x with
  | [] => [a]
  | b :: tl =>
      if a <=? b then a :: x
      else b :: insert a tl
  end.

Fixpoint sort (x : list nat) : list nat :=
  match x with
  | [] => []
  | a :: tl => insert a (sort tl)
  end.
Program Fixpoint sorted (x : list nat) {measure 0} : bool :=
  match x with
  | [] => true
  | [a] => true
  | a:: (b::tl) => (a <=? b) && sorted (b::tl) 
  end.
Next Obligation.
Admitted.

Theorem clam_14 : forall x : list nat, sorted (sort x) = true.
Proof.
  induction x.
  simpl.
  reflexivity.
  simpl.
  Abort.

Theorem clam_18 : forall x y : list nat, rev (rev x ++ y) = (rev y) ++ x.
Proof.
  induction x.
  simpl.
  assert (forall x : list nat, x ++ [] = x).
  {
    induction x.
    reflexivity.
    simpl.
    rewrite IHx.
    reflexivity.
  }
  intros.
  rewrite H.
  reflexivity.
  simpl.
  intros.
  rewrite <- app_assoc.
  assert (rev y ++ [a] = rev (a::y)).
  {
    simpl.
    reflexivity.
  }
  assert (rev y ++ a :: x = rev y ++ [a] ++ x).
  {
    simpl.
    reflexivity.
  }
  rewrite H0.
  assert (rev y ++ [a] ++ x = (rev y ++ [a]) ++ x).
  {
    rewrite <- app_assoc.
    reflexivity.
  }
  rewrite H1.
  rewrite H.
  assert ([a]++y = a::y).
  {
    simpl.
    reflexivity.
  }
  rewrite H2.
  rewrite IHx.
  reflexivity.
Qed.

Fixpoint rotate (n : nat) (x : list nat) : list nat :=
  match n with
  | 0 => x
  | S n' =>
      match x with
      | [] => []
      | a :: tl => rotate n' (tl ++ [a])
      end
  end.
Theorem clam_21 : forall x y : list nat, rotate (length x) (x ++ y) = y ++ x.
Proof.
  intros.
  generalize dependent y.
  generalize dependent x.
  induction x.
  intros.
  rewrite l1.
  simpl.
  reflexivity.
  intros.
  simpl.
  rewrite <- app_assoc.
  assert (y++a::x = (y++[a])++x).
  {
    rewrite <- app_assoc.
    simpl.
    reflexivity.
  }
  rewrite H.
  rewrite IHx.
  reflexivity.
Qed.


Inductive tree : Type :=
| Leaf : tree
| Node : tree -> nat -> tree -> tree.

Fixpoint height (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node l _ r => 1 + max (height l) (height r)
  end.

Fixpoint mirror (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l n r => Node (mirror r) n (mirror l)
  end.

Fixpoint revflat (t : tree) : list nat :=
  match t with
  | Leaf => []
  | Node l n r => revflat l ++ [n] ++ revflat r
  end.

Fixpoint qrevaflat (t: tree) (lst: list nat) : list nat :=
  match t with
  | Leaf => lst
  | Node l n r => qrevaflat l (n::qrevaflat r lst)
  end.
 

Theorem clam_28 : forall t : tree, revflat t = qrevaflat t [].
Proof.
  induction t.
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHt2.
  assert (forall t lst, revflat t ++ lst = qrevaflat t lst).
  {
    induction t.
    simpl.
    reflexivity.
    simpl.
    intros.
    rewrite IHt3.
    rewrite <- IHt4.
    assert(forall t l1 l2, qrevaflat t (l1++l2) = qrevaflat t l1 ++ l2).
    {
      induction t.
      simpl.
      reflexivity.
      intros.
      simpl.
      rewrite IHt6.
      Search (_::_ ++_).
      rewrite app_comm_cons.
      rewrite IHt5.
      reflexivity.
    }
    rewrite app_comm_cons.
    rewrite H.
    reflexivity.
  }
  rewrite H.
  reflexivity.
Qed.

Fixpoint qreva (l1 l2 : list nat) : list nat :=
  match l1 with
  | [] => l2
  | a :: tl => qreva tl (a :: l2)
  end.

Theorem clam_29 : forall x : list nat, rev (qreva x []) = x.
Proof.
  induction x.
  simpl.
  reflexivity.
  simpl.
  induction x.
  simpl.
  reflexivity.
  simpl.
  assert (forall x l1, rev (qreva x l1) = rev l1 ++ x).
  {
    induction x0.
    simpl.
    intros.
    rewrite app_nil_r.
    reflexivity.
    intros.
    simpl.
    rewrite IHx1.
    simpl.
    rewrite <- app_assoc.
    reflexivity.
  }
  rewrite H.
  simpl.
  reflexivity.
Qed.

(* clam_31: 증가하는 변수를 추적해야함! & 변수 설정의 순서 *)
Theorem clam_31 : forall x : list nat, qreva (qreva x []) [] = x.
Proof.
  induction x.
  simpl.
  reflexivity.
  assert(forall x1 x2, qreva ( qreva x2 x1) [] = (rev x1) ++ x2).
  {
    intros.
    generalize dependent x1.
    induction x2.
    simpl.
    intros.
    rewrite app_nil_r.
    induction x1.
    reflexivity.
    simpl.
    induction x1.
    reflexivity.
    simpl.
    assert(forall x1 x2, qreva x1 x2 = rev x1 ++ x2).
    {
      induction x0.
      simpl.
      reflexivity.
      simpl.
      intros.
      rewrite <- app_assoc.
      assert ([a2]++x2 = a2::x2).
      {
        simpl.
        reflexivity.
      }
      rewrite H.
      rewrite IHx2.
      reflexivity.
    }
    rewrite H.
    rewrite <- app_assoc.
    reflexivity.
    intros.
    simpl.
    rewrite IHx2.
    simpl.
    rewrite <- app_assoc.
    reflexivity.
  }
  simpl.
  rewrite H.
  simpl.
  reflexivity.
Qed.

Theorem clam_32 : forall x, rotate (length x) x = x.
Proof.
  induction x.
  simpl.
  reflexivity.
  simpl.
  (*
  induction x.
  simpl.
  reflexivity.
  simpl.
  rewrite <- app_assoc.
  simpl.
  induction x.
  simpl.
  reflexivity.
  simpl.
  rewrite <- app_assoc.
  simpl.
  clear.
*)
  assert (forall x1 x2, rotate (length x1) (x1 ++ x2) = x2 ++ x1).
  {
    intros.
    generalize dependent x2.
    induction x1.
    simpl.
    intros.
    rewrite app_nil_r.
    reflexivity.
    intros.
    simpl.
    rewrite <- app_assoc.
    assert (x2++a0::x1 = x2++[a0]++x1).
    {
      simpl.
      reflexivity.
    }
    rewrite H.
    rewrite IHx1.
    rewrite <- app_assoc.
    reflexivity.
  }
  rewrite H.
  simpl.
  reflexivity.
Qed.

Fixpoint mem n lst : bool :=
  match lst with
  | [] => false
  | a :: tl => if n =? a then true else mem n tl
  end.

(* Theorem clam_49: forall x y, mem x (sort y) = true -> mem x y = true.
Proof. *)

Fixpoint count n lst : nat :=
  match lst with
  | [] => 0
  | a :: tl => if n =? a then 1 + count n tl else count n tl
  end.
(* Theorem clam_50: forall x y, count x (sort y) = count x y.
Proof. *)
  
Theorem clam_78 : forall x y, rev (qreva x (rev y)) = y ++ x.
Proof.
  assert (forall y : list nat, rev (rev y) = y).
  {
    induction y.
    reflexivity.
    (*  
    induction y.
    simpl.
    reflexivity.
    simpl in *.
    rewrite <- app_assoc.
    simpl.
    induction y.
    simpl.
    reflexivity.
    simpl.
    rewrite <- app_assoc.
    simpl.
    *)
    assert (forall l1 l2 : list nat, rev (rev l1 ++ l2) = rev l2 ++ l1).
    {
      clear.
      induction l2.
      simpl.
      intros.
      rewrite app_nil_r.
      reflexivity.
      simpl.
      intros.
      rewrite <- app_assoc.
      simpl.
      rewrite IHl2.
      simpl.
      rewrite <- app_assoc.
      simpl.
      reflexivity.
    }
    simpl.
    rewrite H.
    simpl.
    reflexivity.
  }
  induction x.
  simpl.
  intros.
  rewrite app_nil_r.
  rewrite H.
  reflexivity.
  simpl.
  intros.
  assert (forall (y : list nat) a, a:: rev y = rev (y++[a])).
  {
    simpl.
    induction y0.
    simpl.
    reflexivity.
    simpl.
    intros.
    rewrite <- IHy0.
    simpl.
    reflexivity.
  }
  rewrite H0.
  rewrite IHx.
  rewrite <- app_assoc.
  simpl.
  reflexivity.
Qed.

Theorem calm_79: forall x y : list nat, rev ((rev x) ++ y) = (rev y) ++ x.
Proof.
  induction x.
  simpl.
  intros.
  rewrite app_nil_r.
  reflexivity.
  simpl.
  intros.
  rewrite <- app_assoc.
  rewrite IHx.
  simpl.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Theorem clam_80 : forall x y : list nat, rev ( rev x ++ rev y) = y ++ x.
Proof.
  induction x.
  simpl.
  intros.
  rewrite app_nil_r.
  assert (forall y : list nat, rev (rev y) = y).
  {
    induction y0.
    reflexivity.
    assert (forall l1 l2 : list nat, rev (l1 ++ l2) = rev l2 ++ rev l1).
    {
      induction l2.
      simpl.
      intros.
      rewrite app_nil_r.
      reflexivity.
      intros.
      simpl.
      rewrite IHl2.
      rewrite app_assoc.
      reflexivity.
    }
    simpl.
    rewrite H.
    simpl.
    rewrite IHy0.
    reflexivity.
  }
  rewrite H.
  reflexivity.
  simpl.
  intros.
  rewrite <- app_assoc.
  assert (forall a (y : list nat), [a]++ rev y = rev (y++[a])).
  {
    simpl.
    induction y0.
    simpl.
    reflexivity.
    simpl.
    rewrite <- IHy0.
    simpl.
    reflexivity.
  }
  rewrite H.
  rewrite IHx.
  rewrite <- app_assoc.
  simpl.
  reflexivity.
Qed.

Theorem clam_83 : forall x y : list nat, rotate (length x) (x ++ y) = y ++ x.
Proof.
  induction x.
  simpl.
  intros.
  rewrite app_nil_r.
  reflexivity.
  simpl.
  intros.
  rewrite <- app_assoc.
  rewrite IHx.
  rewrite <- app_assoc.
  simpl.
  reflexivity.
Qed.

Fixpoint mult n m : nat :=
  match n with
  | 0 => 0
  | S n' => m + mult n' m
  end.

Fixpoint fac n : nat :=
  match n with
  | 0 => 1
  | S n' => mult n (fac n')
  end.

Fixpoint qfac n m : nat :=
  match n with
  | 0 => m
  | S n' => qfac n' (mult m n)
  end.
Theorem clema_84 : forall x y : nat , mult (fac x) y = qfac x y.
Proof.
  induction x.
  simpl.
  intros.
  lia.
  intros.
  simpl.
  rewrite <- IHx.
  induction y.
  simpl.
  assert (forall n, mult n 0 = 0).
  {
    induction n.
    simpl.
    reflexivity.
    simpl.
    rewrite IHn.
    reflexivity.
  }
  rewrite H.
  rewrite H.
  reflexivity.
  simpl.
  assert (forall x y, mult x (S y) = x + mult x y).
  {
    induction x0.
    simpl.
    reflexivity.
    simpl.
    intros.
    rewrite IHx0.
    lia.
  }
  rewrite H.
  rewrite IHy.
  rewrite H with (y := (x + mult y (S x))).
  assert (forall x y z, mult x (y+z) = mult x y + mult x z).
  {
    induction x0.
    simpl.
    reflexivity.
    simpl.
    intros.
    rewrite IHx0.
    lia.
  }
  rewrite H0.
  rewrite Nat.add_assoc.
  assert (forall x y, mult x y = mult y x).
  {
    induction x0.
    simpl.
    induction y0.
    simpl.
    reflexivity.
    simpl.
    rewrite <- IHy0.
    reflexivity.
    simpl.
    intros.
    rewrite H.
    rewrite IHx0.
    reflexivity.
  }
  rewrite H1.
  reflexivity.
Qed.
Fixpoint exp x y : nat := 
  match y with
  | 0 => 1
  | S y' => mult (exp x y') x
  end.

Fixpoint qexp x y z : nat :=
  match y with
  | 0 => z
  | S y' => qexp x y' (mult z x)
  end.

(* Theorem clam_86 : forall x y z, mult (exp x y) z = qexp x y z.
Proof. *)

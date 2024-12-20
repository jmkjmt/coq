From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Bool.
From Coq Require Import ZArith.
From Coq Require Import Lia.
From Coq Require Import Program.

Import ListNotations.

Inductive aexp : Set :=
| Con (n : Z)
| Var (s : string)
| Pow (s : string) (n : Z)
| Sum (xs : list aexp)
| Mul (xs : list aexp).

Fixpoint rank (x : aexp) : nat :=
  match x with
  | Con _
  | Var _
  | Pow _ _ => 1
  | Sum xs
  | Mul xs  => 1 +
      (fix ranks xs :=
        match xs with
        | []        => 0
        | x' :: xs' =>
            rank x' + ranks xs'
        end
      ) xs
  end.

Program Fixpoint diff s x {measure (rank x)} : aexp :=
  match x with
  | (* D_s n := 0 *)
    Con _ => Con 0
  | (* D_s a := a <> s ? 0 : 1 *)
    Var a =>
      Con (if negb (String.eqb a s) then 0 else 1)
  | (* D_s a**n := (n >= 0) ->
        n = 0 || a <> s ? 0 : n*(a**(n-1)) *)
    Pow a n =>
      if Z.ltb n 0 then Var "ERROR"
      else if Z.eqb n 0 ||
        negb (String.eqb a s) then Con 0
      else Mul [Con n; Pow a (n - 1)]
  | (* D_s Sum_i xi :=
        D_s x0 + D_s Sum_{i>0} xi *)
    Sum xs =>
      match xs with
      | []        => Con 0
      | x' :: xs' =>
          Sum [diff s x'; diff s (Sum xs')]
      end
  | (* D_s Mul_i xi :=
        D_s x0 * Mul_{i>0} xi +
        x0 * D_s Mul_{i>0} xi *)
    Mul xs =>
      match xs with
      | [] => Con 0
      | x' :: xs' =>
          Sum [
            Mul [diff s x'; Mul xs'];
            Mul [x'; diff s (Mul xs')]
          ]
      end
  end.
Next Obligation.
  cbn; lia.
Defined.
Next Obligation.
  destruct x'.
  all: cbn; lia.
Defined.
Next Obligation.
  destruct x'.
  all: cbn; lia.
Defined.
Next Obligation.
  destruct x'.
  all: cbn; lia.
Defined.
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

Theorem clam_31 : forall x : list nat, qreva (qreva x []) [] = x.
Proof.
  induction x.
  simpl.
  reflexivity.
  simpl.
  induction x.
  simpl.
  reflexivity.
  simpl.
  assert(forall x l1 , qreva (qreva x l1) [] = qreva l1 [] ++ x).
  {
    induction x0.
    simpl.
    intros.
    rewrite l1.
    reflexivity.
    intros.
    simpl.
    assert (forall l1 l2 a x, qreva l1 (l2++[a]) ++ x = qreva l1 l2 ++ [a] ++ x).
    {
      induction l2.
      simpl.
      intros.
      assert (a2 :: x1 = [a2] ++ x1).
      {
        simpl.
        reflexivity.
      }
      rewrite H.
      rewrite <- app_assoc.
      reflexivity.
      intros.
      simpl.
      remember (a2 :: l0) as l4.
      Search ( _ :: _ ++ _).
      rewrite app_comm_cons.
      rewrite <- Heql4.
      rewrite IHl2.
      assert (a3::x1= [a3]++x1).
      {
        simpl.
        reflexivity.
      }
      rewrite H.
      reflexivity.
  }
  intros.
  simpl.
  assert (a1::x0 = [a1]++x0).
  {
    simpl.
    reflexivity.
  }
  rewrite H0.
  rewrite <- H.
  simpl.




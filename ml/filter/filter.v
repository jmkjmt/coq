Require Import ZArith.
Require Import Arith.
Require Import List.
Require Import Bool.
Import ListNotations.
Open Scope Z_scope.



Fixpoint solution (pred:Z -> bool) (lst:list Z) : list Z :=
 
    match lst with
    | [] => []
    | hd::tl => if pred hd then hd :: solution pred tl else solution pred tl
    end.

Fixpoint aux171 (pred: Z -> bool) (i: Z) (l: list Z) : list Z :=
  match l with
  | [] => []
  | hd::tl => if pred hd then hd:: aux171 pred (i+1) tl else aux171 pred (i+1) tl
  end.
Definition sol171 (pred:Z -> bool) (lst: list Z) : list Z :=
    aux171 pred (1:Z) lst.

Fixpoint loop (pred: Z -> bool) (i: list Z) (o:list Z) : list Z :=
    match i with
    | [] => o
    | hd::tl => if pred hd then loop pred tl (hd::o) else loop pred tl o
    end.

Fixpoint reverse (i: list Z) (o: list Z) : list Z :=
    match i with
    | [] => o
    | hd::tl => reverse tl (hd::o)
    end.

Definition sol121 (pred: Z -> bool) (lst: list Z) := reverse (loop pred lst []) [].



Lemma cons_injective : forall  (x : Z) (l1 l2 : list Z),
  x :: l1 = x :: l2 <-> l1 = l2.
Proof.
  
  split.
  intros.
  inversion H.
  reflexivity.
  intros.
  rewrite H.
  reflexivity.
Qed.
Fixpoint cond (pred : Z -> bool) (lst: list Z) : bool :=
match lst with
| [] => true
| hd::tl => if pred hd then cond pred tl else false
end.
Fixpoint app (lst: list Z) a :=
match lst with 
| [] => [a]
| hd::tl => hd :: app tl a
end.

Theorem lemma3: forall pred a lst1 lst2, a :: reverse (loop pred lst1 lst2) [] = reverse (loop pred lst1 (app lst2 a)) [].
Proof.
  intros.
  generalize dependent lst2.
  generalize dependent a.
  induction lst1.
  simpl.
  induction lst2.
  simpl.
  reflexivity.
  simpl.
  assert (forall a lst1 lst2, a:: reverse lst1 lst2 = reverse (app lst1 a) lst2).
  {
    intros.
    generalize dependent lst0.
    induction lst1.
    simpl.
    reflexivity.
    simpl.
    intros.
    rewrite IHlst1.
    reflexivity.
  }
  rewrite H.
  reflexivity.
  simpl.
  intros.
  case (pred a) eqn:E.
  rewrite IHlst1.
  simpl.
  reflexivity.
  rewrite IHlst1.
  reflexivity.
Qed.
Theorem eq2: forall pred lst, solution pred lst = sol121 pred lst.
Proof.
  intros.
  unfold sol121.
  induction lst.
  simpl.
  reflexivity.
  simpl.
  case (pred a) eqn:E.
  2: {
    apply IHlst.
  }
  assert ([a] = app [] a).
  simpl.
  reflexivity.
  rewrite IHlst.
  rewrite H.
  rewrite <- lemma3.
  reflexivity.
Qed.

Theorem eq : forall pred lst, solution pred lst = sol171 pred lst.
Proof.
  intros.
  unfold sol171.
  (* lemma *)
  assert (forall i pred lst, aux171 pred i lst = solution pred lst).
  {
    clear.
    intros.
    generalize i.
    induction lst.
    simpl.
    reflexivity.
    simpl.
    intros.
    case (pred a) eqn:E.
    rewrite IHlst.
    reflexivity.
    rewrite IHlst.
    reflexivity.
  }
  induction lst.
  simpl.
  reflexivity.
  simpl.
  case (pred a) eqn:E.
  rewrite H.
  reflexivity.
  rewrite H.
  reflexivity.
Qed.




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

Definition filter_sub (pred:Z -> bool) (lst: list Z) : list Z :=
    let fix aux (i:nat) (l :list Z) : list Z :=
    match l with
    | [] => []
    | hd::tl => if pred hd then hd:: aux (S i) tl else aux (S i) tl
    end in
    aux (1:nat) lst.

Fixpoint aux (pred: Z -> bool) (i:Z) (lst:list Z) : list Z :=
  match lst with
  | [] => []
  | hd::tl => if pred hd then hd :: aux pred (i + 1) tl else aux pred (i+1) tl
  end.
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
Lemma l1 : forall lst , forall pred i , solution pred lst = aux pred i lst.
Proof.
    induction lst.
    simpl.
    reflexivity.
    intros.
    simpl.
    case (pred a).
    apply cons_injective with (x := a).
    apply IHlst.
    apply IHlst.
    Qed.


Theorem eq : forall pred lst, solution pred lst = filter_sub pred lst.
Proof.
    intros.
    assert (lemma: forall lst, forall i j, 
    (fix aux (i : nat) (l : list Z) {struct l} : list Z := match l with
    | [] => []
    | hd :: tl => if pred hd then hd :: aux (S i) tl else aux (S i) tl
    end) (i:nat) lst = 
    (fix aux (i : nat) (l : list Z) {struct l} : list Z := match l with
    | [] => []
    | hd :: tl => if pred hd then hd :: aux (S i) tl else aux (S i) tl
    end) (j:nat) lst).
    induction lst0.
    reflexivity.
    case (pred a).
    intros.
    apply cons_injective.
    apply IHlst0.
    intros.
    apply IHlst0.
    induction lst.
    simpl.
    unfold filter_sub.
    reflexivity.
    simpl.
    case (pred a) eqn :H.
    unfold filter_sub.
    simpl.
    rewrite H.
    rewrite IHlst.
    unfold filter_sub.    
    apply cons_injective with (x:= a).
    apply lemma.
    unfold filter_sub.
    rewrite H.
    rewrite IHlst.
    unfold filter_sub.
    unfold filter_sub.
    apply lemma.
    Qed.
    
    
    

    
    

    

    
    
    

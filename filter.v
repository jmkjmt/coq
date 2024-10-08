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
    let fix aux (i:Z) (l :list Z) : list Z :=
    match l with
    | [] => []
    | hd::tl => if pred hd then hd:: aux (i + 1) tl else aux (i + 1) tl
    end in
    aux (1:Z) lst.


Definition filter_sub2 (pred: Z -> bool) (lst: list Z) := 
	let fix loop (i: list Z) (o: list Z) :=
		match i with
		|	[] => o
		|	h :: t => loop t (if (pred h) then(h :: o) else loop t o)
    end in
	let fix reverse (i: list Z) (o: list Z) :=
		match i with
		|	[] => o
		|	h :: t => reverse t (h :: o) end in
	reverse (loop lst []) [].



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

Theorem eq : forall pred lst, solution pred lst = filter_sub pred lst.
Proof.
    intros.
    assert (lemma: forall lst, forall i j, 
    (fix aux (i : Z) (l : list Z) {struct l} : list Z := match l with
    | [] => []
    | hd :: tl => if pred hd then hd :: aux (i + 1) tl else aux (i + 1) tl
    end) (i:Z) lst = 
    (fix aux (i : Z) (l : list Z) {struct l} : list Z := match l with
    | [] => []
    | hd :: tl => if pred hd then hd :: aux (i + 1) tl else aux (i + 1) tl
    end) (j:Z) lst).
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

Theorem eq2: forall pred lst, solution pred lst = filter_sub2 pred lst.
Proof.
  intros.
  induction lst.
  reflexivity.
  simpl.
  case (pred a) eqn: Ha.
  unfold filter_sub2.
  rewrite Ha.
  unfold filter_sub2 in IHlst.
  rewrite IHlst.
  
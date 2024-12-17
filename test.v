Require Import Program Arith ZArith Lia.


Program Fixpoint solution_1 (f: nat -> nat) (a b: nat) {measure (b - a)}: nat :=
  match b - a with
  | 0 => f a
  | _ => f a + solution_1 f (a + 1) b
  end.
Next Obligation.
Proof. 
   auto with *.
  Qed.

Program Fixpoint solution_2 (f: nat -> nat) (a b: nat) {measure (b - a)}: nat :=
  match b - a with
  | 0 => f b
  | _ => f b + solution_2 f a (b - 1)
  end.
Next Obligation.
Proof. 
   auto with *.
  Qed.

Lemma H1: forall a b, b >= a -> (S b) - a = S (b - a).
Proof.
  intros.
  pose (c := b - a).
  replace (b - a) with (c) by lia.
  replace (S c) with (c + 1) by lia.
  replace (S b) with (b + 1) by lia.
  replace c with (b - a) by lia.
  lia.
Qed.

Theorem eq: forall f a b, a <= b -> solution_1 f a b = solution_2 f a b.
Proof.
  intros.
  cbn.
  induction b.
  intros.
  destruct a.
  simpl.
  reflexivity.
  lia.
  Abort.
  
  
  (* replace (S b - a) with (S (b - a)) by (rewrite (H1 a b)). *)



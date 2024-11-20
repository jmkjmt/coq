Require Import Prelude.

Inductive natural : Type :=
 ZERO : natural
| SUCC : natural -> natural.

Fixpoint natadd n1 n2 :=
  match n1 with
   ZERO => n2
  | SUCC n => SUCC (natadd n n2)
  end.
Fixpoint natadd_ref n1 n2 :=
match n1 with
| ZERO => n2
| SUCC ZERO => SUCC n2
| SUCC n => SUCC (natadd_ref n n2)
end.
Fixpoint natadd2 n1 n2 :=
  match n1 with
   ZERO => n2
  | SUCC n =>  natadd2 n (SUCC n2)
  end.
Fixpoint natadd3 n1 n2 :=
match n2 with
| ZERO => n1
| SUCC n => SUCC (natadd3 n1 n)
end.
Theorem equal : forall arg0 arg1, natadd arg0 arg1 = natadd_ref arg0 arg1.
Proof.
  induction arg0.
  simpl.
  reflexivity.
  simpl.
  intros.
  case arg0 eqn:H.
  simpl.
  reflexivity.
  simpl in *.
  simpl in IHarg0.
  rewrite IHarg0.
  reflexivity.
  Qed.

Theorem test: forall arg0 arg1, natadd arg0 arg1 = natadd_ref arg0 arg1.
Proof.
  (induction arg0).
(simpl in *).
reflexivity.
(intros arg1).
(simpl in *).
(destruct (arg0) eqn:arg0case).
(simpl in *).
reflexivity.
(rewrite <- IHarg0 in *).
(simpl in *).
reflexivity.
Qed.



Theorem sub4:forall arg0 arg1, natadd arg0 arg1 = natadd3 arg0 arg1.
Proof.
  induction arg0.
  simpl.
  intros.
  assert (lemma1: arg1 = natadd3 ZERO arg1).
    generalize dependent arg1.
    induction arg1.
    simpl.
    reflexivity.
    simpl.
    rewrite <- IHarg1.
    reflexivity.
  rewrite <- lemma1.
  reflexivity.
  simpl.
  intros arg1.
  rewrite IHarg0.
  assert (lemma2: forall arg0 arg1, SUCC (natadd3 arg0 arg1) = natadd3 (SUCC arg0) arg1).
  {
    intros.
    generalize dependent arg2.
    induction arg3.
    simpl.
    reflexivity.
    simpl.
    intros arg2.
    rewrite IHarg3.
    reflexivity.
  }
  rewrite lemma2.
  reflexivity.
  Qed.

  Theorem test1:forall arg0 arg1, natadd arg0 arg1 = natadd3 arg0 arg1.
Proof.
(induction arg0).
(simpl in *).
(intros arg1).
(simpl in *).


Qed.


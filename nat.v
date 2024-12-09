Require Import Program.
Inductive natural : Type :=
 ZERO : natural
| SUCC : natural -> natural.

Fixpoint natadd1 n1 n2 :=
  match n1 with
   ZERO => n2
  | SUCC n => SUCC (natadd1 n n2)
  end.

Fixpoint natadd2 (n1 n2 : natural) : natural :=
  match n2 with
  | ZERO => n1
  | SUCC n => SUCC (natadd2 n1 n)
  end.

Fixpoint natadd3 (n1 n2:natural) : natural :=
  match n1 with
  | ZERO => n2
  | SUCC n => natadd3 n (SUCC n2)
  end.

Fixpoint natadd4 (n1 n2 : natural) : natural :=
  match n2 with
  | ZERO => n1
  | SUCC n => natadd4 (SUCC n1) n
  end.

Fixpoint natmul1 (n1 n2 :natural) : natural :=
  match n1 with
  | ZERO => ZERO
  | SUCC n => natadd1 n2 (natmul1 n n2)
  end.

Fixpoint natmul2 (n1 n2 :natural) : natural :=
  match n1 with
  | ZERO => ZERO
  | SUCC n => natadd1 (natmul2 n n2) n2
  end.

Fixpoint natmul3 (n1 n2 : natural) : natural :=
  match n1 with
  | ZERO => ZERO
  | SUCC n => natadd3 n2 (natmul3 n n2) 
  end.

Fixpoint natmul4 (n1 n2: natural) : natural :=
  match n1 with
  | ZERO => ZERO
  | SUCC n => natadd3 (natmul4 n n2) n2
  end.

Fixpoint natmul5 (n1 n2:natural) : natural :=
  match n2 with
  | ZERO => ZERO
  | SUCC n => natadd2 n1 (natmul5 n1 n)
  end.

Fixpoint natmul6 (n1 n2:natural) : natural :=
  match n2 with
  | ZERO => ZERO
  | SUCC n => natadd4 n1 (natmul6 n1 n)
  end.

Fixpoint natmul7 (n1 n2:natural) : natural :=
  match n2 with
  | ZERO => ZERO
  | SUCC n => natadd1 n1 (natmul7 n1 n)
  end.

Fixpoint natmul_helper (n1 n2 result: natural) : natural :=
  match n1 with
  | ZERO => result
  | SUCC n => natmul_helper n n2 (natadd1 n2 result)
  end.
Definition natmul_sub (n1 n2: natural) : natural :=
  natmul_helper n1 n2 ZERO.

Lemma l1: forall n2 : natural, ZERO = natmul6 ZERO n2.
Proof.
  induction n2.
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHn2.
  reflexivity.
Qed.
Lemma l2_1 : forall n1 n2, SUCC (natadd4 n1 n2) = natadd4 (SUCC n1) n2.
Proof.
  intros.
  generalize dependent n1.
  induction n2.
  simpl.
  reflexivity.
  simpl.
  intros.
  rewrite IHn2.
  reflexivity.
Qed.
Lemma l2: forall n1 n2 n3, SUCC (natadd1 n2 (natadd4 n1 n3)) = natadd4 (SUCC n1) (natadd1 n2 n3).
Proof.
  intros.
  generalize dependent n1.
  generalize dependent n3.
  induction n2.
  simpl.
  intros.
  apply l2_1.
  simpl.
  intros.
  rewrite IHn2.
  apply l2_1.
Qed.
  
Theorem test1: forall n1 n2, natmul1 n1 n2 = natmul6 n1 n2.
Proof.
  induction n1.
  simpl.
  apply l1.
  simpl.
  intros.
  rewrite IHn1.
  induction n2.
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHn2.
  apply l2.
Qed.
Lemma test2_1: forall n2 : natural, ZERO = natmul5 ZERO n2.
Proof.
  induction n2.
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHn2.
  reflexivity.
  Qed.
Lemma test2_2_2 : forall n1 n2, SUCC (natadd2 n1 n2) = natadd2 (SUCC n1) n2.
Proof.
  intros.
  generalize dependent n1.
  induction n2.
  simpl.
  reflexivity.
  simpl.
  intros.
  rewrite IHn2.
  reflexivity.
Qed. 
Lemma test2_2_1 : forall n1 n2 n3, SUCC (natadd1 n2 (natadd2 n1 n3)) =
natadd2 (SUCC n1) (natadd1 n2 n3).
Proof.
  intros.
  generalize dependent n1.
  generalize dependent n3.
  induction n2.
  simpl.
  intros.
  apply test2_2_2.
  intros.
  simpl.
  rewrite IHn2.
  reflexivity.
  Qed.

Lemma test2_2 : forall n1 n2 , natadd1 n2 (natmul5 n1 n2) = natmul5 (SUCC n1) n2.
Proof.
  induction n2.
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHn2.
  apply test2_2_1.
Qed.

Theorem test2: forall n1 n2, natmul1 n1 n2 = natmul5 n1 n2.
Proof.
  induction n1.
  simpl.
  apply test2_1.
  intros.
  simpl.
  rewrite IHn1.
  apply test2_2.
Qed.
Lemma test3_1_1 : forall n1, natadd1 n1 ZERO = n1.
Proof.
  induction n1.
  simpl.
  reflexivity.
  simpl.
  rewrite IHn1.
  reflexivity.
Qed.
Lemma test3_1_2 : forall n1 n2, SUCC (natadd1 n1 n2) = natadd1 n1 (SUCC n2).
Proof.
  induction n1.
  simpl.
  reflexivity.
  simpl.
  intros.
  rewrite IHn1.
  reflexivity.
Qed.
Lemma test3_1: forall n1 n2, natadd1 n1 n2 = natadd3 n2 n1.
Proof.
  intros.
  generalize dependent n1.
  induction n2.
  simpl.
  apply test3_1_1.
  simpl.
  intros.
  rewrite <- IHn2.
  simpl.
  rewrite <- test3_1_2.
  reflexivity.
Qed.


Theorem test3: forall n1 n2, natmul1 n1 n2 = natmul4 n1 n2.
Proof.
  induction n1.
  simpl.
  reflexivity.
  simpl.
  intros.
  rewrite IHn1.
  apply test3_1.
  Qed.

Theorem test4: forall n1 n2, natmul6 n1 n2 = natmul7 n1 n2.
Proof.
  intros.
  generalize dependent n1.
  induction n2.
  simpl.
  reflexivity.
  simpl.
  intros.
  rewrite IHn2.
  assert (forall n1 n2, natadd4 n1 n2 = natadd1 n1 n2).
  {
    intros.
    generalize dependent n0.
    induction n3.
    simpl.
    induction n0.
    simpl.
    reflexivity.
    simpl.
    rewrite <- IHn0.
    reflexivity.
    simpl.
    intros.
    rewrite IHn3.
    simpl.
    assert(forall n1 n2, SUCC (natadd1 n1 n2) = natadd1 n1 (SUCC n2)).
    {
      induction n4.
      simpl.
      reflexivity.
      simpl.
      intros.
      rewrite IHn4.
      reflexivity.
    }
    rewrite H.
    reflexivity.
  }
  rewrite H.
  reflexivity.
  Qed.
Lemma hard: forall n1 n2, natadd4 n1 n2 = natadd4 n2 n1.
Proof.
  induction n1.
  simpl.
  induction n2.
  simpl.
  reflexivity.
  simpl.
  assert(forall n1 n2, natadd4 (SUCC n1) n2 = SUCC (natadd4 n1 n2)).
  {
    intros.
    generalize dependent n1.
    induction n0.
    simpl.
    reflexivity.
    simpl.
    intros.
    rewrite IHn0.
    reflexivity.
  }
  rewrite H.
  rewrite IHn2.
  reflexivity.
  intros.
  simpl.
  rewrite <- IHn1.
  simpl.
  reflexivity.
  Qed.

Theorem very_hard : forall n1 n2, natmul1 n1 n2 = natmul_sub n1 n2.
Proof.
  unfold natmul_sub.
  induction n1.
  simpl.
  reflexivity.
  simpl.
  intros.
  assert (forall n1 n2 n3, natmul_helper n1 n2 (natadd1 n2 n3) = natadd1 n2 (natmul_helper n1 n2 n3)).
  {
    induction n0.
    simpl.
    reflexivity.
    simpl.
    intros.
    rewrite IHn0.
    reflexivity.
  }
  rewrite H.
  rewrite IHn1.
  reflexivity.
Qed.
  
  





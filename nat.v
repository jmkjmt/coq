Require Import Program.
Require Import Setoid.
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
  rewrite IHn1.
  assert (forall n1 n2 n3, natadd1 n3 (natmul_helper n1 n2 ZERO) = natmul_helper n1 n2 (natadd1 n3 ZERO)).
  {
    induction n4.
    simpl.
    reflexivity.
    simpl.
    rewrite IHn4.
    assert (forall n1 n2 n3, SUCC (natmul_helper n1 n2 n3) = natmul_helper n1 n2 (SUCC n3)).
    {
      induction n5.
      simpl.
      reflexivity.
      simpl.
      intros.
      rewrite IHn5.
      assert (forall n1 n2, SUCC (natadd1 n1 n2) = natadd1 n1 (SUCC n2)).
      {
        induction n8.
        simpl.
        reflexivity.
        simpl.
        intros.
        rewrite IHn8.
        reflexivity.
      }
      rewrite H.
      reflexivity.
    }
    rewrite H.
    reflexivity.
  }
  rewrite H.
  reflexivity.
  (* assert (forall n, natadd1 n ZERO = n).
  {
    induction n.
    simpl.
    reflexivity.
    simpl.
    rewrite IHn.
    reflexivity.
  } 
  rewrite H.
  
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
  reflexivity. *)
Qed.
  
Theorem test1213: forall n1, natadd4 ZERO n1 = n1.
Proof.
  induction n1.
  reflexivity.
  rewrite <- IHn1 at 2.
  (* simpl natadd4 in IHn1 at 1. *)
  (* assert ( forall n1 , natadd4 (SUCC ZERO) n1 = SUCC (natadd4 ZERO n1)).
  {
    induction n0.
    simpl.
    reflexivity.
    simpl.
    intros.
    rewrite IHn0.
    reflexivity.
   
  } *)
  assert (forall n1 n2, natadd4 (SUCC n2) n1 = SUCC (natadd4 n2 n1)).
  {
    induction n0.
    simpl.
    reflexivity.
    simpl.
    intros.
    rewrite IHn0 at 1.
    reflexivity.
  }
  rewrite <- H at 1.
  simpl.
  reflexivity.
Qed.
  
Theorem test1214: forall n1 n2, natmul1 n1 n2 = natmul5 n1 n2.
Proof.
  induction n1.
  simpl.
  assert (forall n2, natmul5 ZERO n2 = ZERO).
  {
    induction n2.
    simpl.
    reflexivity.
    simpl.
    rewrite IHn2.
    reflexivity.
  }
  intros.
  rewrite H.
  reflexivity.
  intros.
  simpl.
  rewrite IHn1.
  assert (forall n1 n2, natadd1 n2 (natmul5 n1 n2) = natmul5 (SUCC n1) n2).
  {
    intros.
    generalize dependent n0.
    induction n3.
    simpl.
    reflexivity.
    intros.
    simpl.
    rewrite <- IHn3.
    remember (natmul5 n0 n3) as n.
    assert (forall n1 n2 n3, SUCC (natadd1 n3 (natadd2 n2 n1))= natadd2 (SUCC n2) (natadd1 n3 n1)).
    {
      (* induction n4.
      simpl.
      intros.
      generalize dependent n4.
      assert(forall n1 n2, SUCC (natadd1 n1 n2) = natadd2 (SUCC n2) (natadd1 n1 ZERO)).
      {
        induction n4.
        simpl.
        reflexivity.
        intros.
        simpl.
        rewrite IHn4.
        reflexivity.
      }
      intros.
      rewrite H.
      reflexivity.
      simpl.
      intros.
      generalize dependent n5.
      induction n6.
      simpl.
      assert (forall n5 n4, SUCC (SUCC (natadd2 n5 n4)) = SUCC (natadd2 (SUCC n5) n4)).
      {
        induction n6.
        simpl.
        reflexivity.
        simpl.
        rewrite IHn6.
        reflexivity.
      }
      intros.
      rewrite H.
      reflexivity.
      simpl.
      intros.
      rewrite IHn6.
      reflexivity. 
    }
    rewrite H.
    reflexivity.
  }
  rewrite H.
  reflexivity. *)

      
      induction n6.
      (* why split on n6? *)
      simpl.
      assert (forall n1 n2, SUCC (natadd2 n1 n2) = natadd2 (SUCC n1) n2).
      {
        intros.
        generalize dependent n6.
        induction n7.
        simpl.
        reflexivity.
        simpl.
        intros.
        rewrite IHn7.
        reflexivity.
      }
      rewrite H.
      reflexivity.
      simpl.
      rewrite IHn6.
      reflexivity.
    }
    rewrite H.
    reflexivity.
  }
  rewrite H.
  reflexivity.
Qed.
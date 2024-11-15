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
  match n1, n2 with 
      | _, ZERO => result
      | ZERO, _ => result
      | SUCC v1, _ => natmul_helper v1 n2 (natadd1 result n2) end.

Definition natmul_sub (n1 n2 : natural) : natural :=
  natmul_helper n1 n2 ZERO.

Lemma in_out :forall n1 n2, SUCC (natadd1 n2 n1) = natadd1 n2 (SUCC n1).
Proof.
  induction n2.
  simpl.
  reflexivity.
  simpl.
  rewrite IHn2.
  reflexivity.
  Qed.
Lemma sym: forall n1 n2, natadd1 n1 n2 = natadd1 n2 n1.
Proof.
  intros.
  induction n1.
  simpl.
  induction n2.
  reflexivity.
  simpl.
  rewrite <- IHn2.
  reflexivity.
  simpl.
  rewrite IHn1.
  apply in_out.
  Qed.
  
Theorem natmul_eq : forall n1 n2, natmul1 n1 n2 = natmul2 n1 n2.
Proof.
  intros.
  induction n1.
  simpl.
  reflexivity.
  simpl.
  rewrite IHn1.
  apply sym.
  Qed.

Lemma l1 : forall n1, forall n2, forall result, natmul_helper n1 n2 result = natadd1 (natmul1 n1 n2) result.
Proof.
  intros n1 n2.
  induction n1.
  simpl.
  case n2.
  reflexivity.
  reflexivity.
  intros result.
  simpl.
  case n2.
  simpl.
  assert(lemma2: forall n, natmul1 n ZERO = ZERO).
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
  rewrite lemma2.
  simpl.
  reflexivity.
  simpl.
  intros n.
  Abort.
Lemma l2: forall n1 n2, natmul1 n1 n2 = natmul1 n2 n1.
Proof.
  induction n1.
  simpl.
  induction n2.
  reflexivity.
  simpl.
  rewrite <- IHn2.
  reflexivity.
  intros n2.
  simpl.
  rewrite IHn1.
  induction n2.
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHn2.
  assert( lemma:forall n1 n2, natadd1 n2 (natadd1 n1 (natmul1 n2 n1)) = natadd1 n1 (natadd1 n2 (natmul1 n2 n1))).
  induction n0.
  simpl.
  reflexivity.
  simpl.
  intros n3.


Theorem eq : forall n1, forall n2, natmul_helper n1 n2 ZERO = natmul1 n1 n2.
Proof.
  induction n1.
  intros.
  simpl.
  case n2.
  reflexivity.
  reflexivity.
  induction n2.
  simpl.
  assert (lemma1: forall n, ZERO = natmul1 n ZERO).
  induction n.
  reflexivity.
  simpl.
  rewrite <- IHn.
  reflexivity.
  apply lemma1.
  simpl.
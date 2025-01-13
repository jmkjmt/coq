Require Import Arith.
Require Import List.
Require Import Bool Program.
(* Inductive nat : Type :=
 0 : nat
| S : nat -> nat. *)

Fixpoint natadd1 n1 n2 :=
  match n1 with
   0 => n2
  | S n => S (natadd1 n n2)
  end.

Fixpoint natadd2 (n1 n2 : nat) : nat :=
  match n2 with
  | 0 => n1
  | S n => S (natadd2 n1 n)
  end.

Fixpoint natadd3 (n1 n2:nat) : nat :=
  match n1 with
  | 0 => n2
  | S n => natadd3 n (S n2)
  end.

Fixpoint natadd4 (n1 n2 : nat) : nat :=
  match n2 with
  | 0 => n1
  | S n => natadd4 (S n1) n
  end.

Fixpoint natmul1 (n1 n2 :nat) : nat :=
  match n1 with
  | 0 => 0
  | S n => natadd1 n2 (natmul1 n n2)
  end.

Fixpoint natmul2 (n1 n2 :nat) : nat :=
  match n1 with
  | 0 => 0
  | S n => natadd1 (natmul2 n n2) n2
  end.

Fixpoint natmul3 (n1 n2 : nat) : nat :=
  match n1 with
  | 0 => 0
  | S n => natadd3 n2 (natmul3 n n2) 
  end.

Fixpoint natmul4 (n1 n2: nat) : nat :=
  match n1 with
  | 0 => 0
  | S n => natadd3 (natmul4 n n2) n2
  end.

Fixpoint natmul5 (n1 n2:nat) : nat :=
  match n2 with
  | 0 => 0
  | S n => natadd2 n1 (natmul5 n1 n)
  end.

Fixpoint natmul6 (n1 n2:nat) : nat :=
  match n2 with
  | 0 => 0
  | S n => natadd4 n1 (natmul6 n1 n)
  end.

Fixpoint natmul7 (n1 n2:nat) : nat :=
  match n2 with
  | 0 => 0
  | S n => natadd1 n1 (natmul7 n1 n)
  end.


(* 
Fixpoint add_sol6 (n1 n2 :nat) : nat :=
match n1 with
|0 => n2
|S x => S (add_sol6 n2 x)
end.

Fixpoint sol6 (n1 n2 :nat) : nat :=
match n1 with
|0 => 0
|S x => add_sol6 n2 (sol6 n2 x)
end.
Theorem ta1_sol6 : forall n1 n2, natmul1 n1 n2 = sol6 n1 n2.
Proof. *)
Fixpoint innerLoop (n1 n2 maintain : nat) : nat :=
  match n1 with
  | 0 => maintain
  |S 0 => n2
  |S( sub_count ) => innerLoop sub_count (natadd1 maintain n2) maintain	
  end.
  Open Scope nat_scope.
Definition sol90 (n1 n2 : nat) : nat :=
	if orb (Nat.eqb n1 0) (Nat.eqb n2 0) then 0
	else innerLoop n1 n2 n2.

Theorem ta1_sol90 : forall n1 n2, natmul1 n1 n2 = sol90 n1 n2.
Proof.
  assert (forall n1, natmul1 n1 0 = 0).
  {
    clear.
    induction n1.
    reflexivity.
    simpl.
    apply IHn1.
  }
   assert (forall n2, natadd1 n2 0= n2).
  {
    clear.
    induction n2.
    reflexivity.
    simpl.
    rewrite IHn2. 
    reflexivity.
  }
  (* very hard... *)
  Abort.







Fixpoint natmul_helper (n1 n2 result: nat) : nat :=
  match n1 with
  | 0 => result
  | S n => natmul_helper n n2 (natadd1 n2 result)
  end.
Definition natmul_sub (n1 n2: nat) : nat :=
  natmul_helper n1 n2 0.

Lemma l1: forall n2 : nat, 0 = natmul6 0 n2.
Proof.
  induction n2.
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHn2.
  reflexivity.
Qed.
Lemma l2_1 : forall n1 n2, S (natadd4 n1 n2) = natadd4 (S n1) n2.
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
Lemma l2: forall n1 n2 n3, S (natadd1 n2 (natadd4 n1 n3)) = natadd4 (S n1) (natadd1 n2 n3).
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
Lemma test2_1: forall n2 : nat, 0 = natmul5 0 n2.
Proof.
  induction n2.
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHn2.
  reflexivity.
  Qed.
Lemma test2_2_2 : forall n1 n2, S (natadd2 n1 n2) = natadd2 (S n1) n2.
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
Lemma test2_2_1 : forall n1 n2 n3, S (natadd1 n2 (natadd2 n1 n3)) =
natadd2 (S n1) (natadd1 n2 n3).
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

Lemma test2_2 : forall n1 n2 , natadd1 n2 (natmul5 n1 n2) = natmul5 (S n1) n2.
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
Lemma test3_1_1 : forall n1, natadd1 n1 0 = n1.
Proof.
  induction n1.
  simpl.
  reflexivity.
  simpl.
  rewrite IHn1.
  reflexivity.
Qed.
Lemma test3_1_2 : forall n1 n2, S (natadd1 n1 n2) = natadd1 n1 (S n2).
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
    assert(forall n1 n2, S (natadd1 n1 n2) = natadd1 n1 (S n2)).
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
  assert(forall n1 n2, natadd4 (S n1) n2 = S (natadd4 n1 n2)).
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
  (*  
  induction n1.
  simpl.
  reflexivity.
  simpl.
  induction n1.
  simpl.
  reflexivity.
  simpl.
*)
  assert (forall n1 n2 n3, natadd1 n3 (natmul_helper n1 n2 0) = natmul_helper n1 n2 (natadd1 n3 0)).
  {
    induction n4.
    simpl.
    reflexivity.
    simpl.
    rewrite IHn4.
    assert (forall n1 n2 n3, S (natmul_helper n1 n2 n3) = natmul_helper n1 n2 (S n3)).
    {
      induction n5.
      simpl.
      reflexivity.
      simpl.
      intros.
      rewrite IHn5.
      assert (forall n1 n2, S (natadd1 n1 n2) = natadd1 n1 (S n2)).
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
  (* assert (forall n, natadd1 n 0 = n).
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
  
Theorem test1213: forall n1, natadd4 0 n1 = n1.
Proof.
  induction n1.
  reflexivity.
  rewrite <- IHn1 at 2.
  (* simpl natadd4 in IHn1 at 1. *)
  (* assert ( forall n1 , natadd4 (S 0) n1 = S (natadd4 0 n1)).
  {
    induction n0.
    simpl.
    reflexivity.
    simpl.
    intros.
    rewrite IHn0.
    reflexivity.
   
  } *)
  assert (forall n1 n2, natadd4 (S n2) n1 = S (natadd4 n2 n1)).
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
  assert (forall n2, natmul5 0 n2 = 0).
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
  assert (forall n1 n2, natadd1 n2 (natmul5 n1 n2) = natmul5 (S n1) n2).
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
    assert (forall n1 n2 n3, S (natadd1 n3 (natadd2 n2 n1))= natadd2 (S n2) (natadd1 n3 n1)).
    {
      (* induction n4.
      simpl.
      intros.
      generalize dependent n4.
      assert(forall n1 n2, S (natadd1 n1 n2) = natadd2 (S n2) (natadd1 n1 0)).
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
      assert (forall n5 n4, S (S (natadd2 n5 n4)) = S (natadd2 (S n5) n4)).
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
      assert (forall n1 n2, S (natadd2 n1 n2) = natadd2 (S n1) n2).
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
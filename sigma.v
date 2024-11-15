Require Import Program Arith ZArith Lia.
Theorem th1: forall a b :nat, forall a0 b0: nat, b0 - a0 < b - a -> 0 < b - a.
Proof.
  intros.
  lia.
  Qed.

Print Z.to_nat.
  
 Program Fixpoint solution_1 (f: Z -> Z) (a b: Z) {measure (Z.to_nat (b-a))}: Z :=
  if Z.ltb b a then 0
  else if Z.eqb a b then f a
  else f a + solution_1 f (a + 1) b.

  Next Obligation.
  intuition.
  

  

Program Fixpoint solution_2 (f: nat -> nat) (a b : nat) {measure (b-a)} : nat :=
    if (Nat.ltb b a) then 0 
    else (f b) + solution_2 f a (b-1).
  

Program Fixpoint solution_2 (f: nat -> nat) (a: nat) (b : nat) : nat :=
    if (Nat.ltb b a) then 0 
    else (f b) + solution_2 f a (b-1)
.

Program Fixpoint aux (a:nat) (b:nat) (f:nat->nat) (acc:nat) : nat :=
if (Nat.ltb b a) then acc else aux (a+1) b f (acc + (f a))
.

Fixpoint solution_3 (f: nat -> nat) (a: nat) (b : nat) : nat :=
aux a b f 0
.
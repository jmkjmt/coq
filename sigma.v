Require Import Program Arith ZArith Lia.

Print Z.
Print positive.
Print Z.add.
Print Z.ltb.
Print Z.eqb.


Fixpoint sol1 (f: int -> int) (a b : int) : int :=
  if lte b a then POS ZERO
  else if a = b then f a
  else int_plus (f a) (sol1 f (int_plus a (POS (SUCC ZERO))) b).
  
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
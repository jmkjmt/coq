Require Import ZArith.
Require Import Arith.
Require Import Program.
Require Import Lia.
Require Import Coq.Arith.Wf_nat.

Fixpoint asdfasdfadfasdfas (n: nat) (f: Z -> Z): (Z -> Z) :=
if (Nat.ltb n 0) then f
else if (Nat.eqb n 0) then fun x:Z => x
else fun (x:Z) => f ((asdfasdfadfasdfas (n-1) f) x).


Program Fixpoint solution (n: nat) (f: Z -> Z) {measure (n)}: (Z -> Z) :=
if (Nat.ltb n 0) then f
else if (Nat.eqb n 0) then fun x:Z => x
else fun (x:Z) => f ((solution (n-1) f) x).

Fixpoint solution2 (n:Z) (f:Z->Z) : Z->Z :=
if (Z.ltb n 0) then f
else if (Z.eqb n 0) then fun x:Z => x
else fun (x:Z) => f (solution2 (n-1) f x).
Require Import Arith.
Require Import Program.


(* Coq에서 BigInt는 nat로 표현 *)
Program Fixpoint solution_1 (f: nat -> nat) (a: nat) (b: nat) {measure (b - a)} : nat :=
  if Nat.ltb b a then 0 (* a > b *)
  else if Nat.eqb a b then f a (* a = b *)
  else f a + solution_1 f (S a) b.

(* 종료성 증명 *)
Next Obligation.
intuition.

Qed.


Program Fixpoint solution_2 (f: nat -> nat) (a: nat) (b : nat) {measure (b - a)} : nat :=
    if (Nat.ltb b a) then 0 
    else (f b) + solution_2 f a (b-1)
.


Compute solution_1 (fun x => x + 1) 1 3.





Program Fixpoint aux (a:nat) (b:nat) (f:nat->nat) (acc:nat) : nat :=
if (Nat.ltb b a) then acc else aux (a+1) b f (acc + (f a))
.

Fixpoint solution_3 (f: nat -> nat) (a: nat) (b : nat) : nat :=
aux a b f 0
.
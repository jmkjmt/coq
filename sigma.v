Require Import Arith.
Require Import Program.
Require Import Lia.

(* f : Z -> Z : a와 b가 정수형(BigInt)을 사용하므로 Z로 설정 *)
(* 종료성을 위해 measure로 b - a를 사용 *)
Theorem neq :forall a:nat, S a =? a = false.
Proof.
  intros.
  induction a.
  reflexivity.
  auto.
  Qed.
Theorem lt: forall a:nat, S a <? a = false.
Proof.
  intros.
  induction a.
  reflexivity.
  auto.
  Qed.
Theorem lt2 : forall a:nat, S a - a < 2.
Proof.
  intros.
  induction a.
  auto.
  auto.
  Qed.
Program Fixpoint solution_1 (f: nat -> nat) (a: nat) (b: nat) {measure (if Nat.eqb a b then 2 else if Nat.ltb a b then 2 + (b - a) else (a - b))}: nat :=
  if Nat.ltb b a then 0
  else if Nat.eqb a b then f a
  else f a + solution_1 f (a + 1) b.
  
  Next Obligation.
  SearchRewrite (_ + _).
  rewrite Nat.add_1_r.
  rewrite Nat.sub_succ_r.
  case (b=?a) eqn:Ha.
  rewrite Nat.eqb_eq in Ha.
  rewrite Ha.
  rewrite neq.
  Search (S _ < _).
  rewrite lt.
  rewrite Nat.ltb_irrefl.
  SearchRewrite (_ =? _).
  rewrite Nat.eqb_refl.
  apply lt2.
  

  

  
  
 



Program Fixpoint solution_2 (f: nat -> nat) (a: nat) (b : nat) : nat :=
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
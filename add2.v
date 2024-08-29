Require Import Arith.
Require Import Recdef.

(* 임의의 함수 f : nat -> nat *)
Variable f : nat -> nat.

(* 첫 번째 정의 *)
Function add1 (a b : nat) {measure (fun x => b - a) a} : nat :=
  match a <=? b with
  | true => f a + add1 (a + 1) b
  | false => 0
  end.
Proof.
  intros.
  apply Nat.leb_le in teq.
  apply Nat.sub_lt.
  - lia.
  - lia.
Defined.

(* 두 번째 정의 *)
Function add2 (a b : nat) {measure (fun x => b - a) b} : nat :=
  match a <=? b with
  | true => f b + add2 a (b - 1)
  | false => 0
  end.
Proof.
  intros.
  apply Nat.leb_le in teq.
  apply Nat.sub_lt.
  - lia.
  - lia.
Defined.


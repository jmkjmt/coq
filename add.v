Require Import Arith.

(* 임의의 함수 f : nat -> nat *)
Variable f : nat -> nat.

(* 첫 번째 정의 *)
Fixpoint add1 (a b : nat) : nat :=
  match a <=? b with
  | true => f a + add1 (a + 1) b
  | false => 0
  end.

(* 두 번째 정의 *)
Fixpoint add2 (a b : nat) : nat :=
  match a <=? b with
  | true => f b + add2 a (b - 1)
  | false => 0
  end.

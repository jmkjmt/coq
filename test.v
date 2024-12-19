From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Bool.
From Coq Require Import ZArith.
From Coq Require Import Lia.
From Coq Require Import Program.

Import ListNotations.

Inductive aexp : Set :=
| Con (n : Z)
| Var (s : string)
| Pow (s : string) (n : Z)
| Sum (xs : list aexp)
| Mul (xs : list aexp).

Fixpoint rank (x : aexp) : nat :=
  match x with
  | Con _
  | Var _
  | Pow _ _ => 1
  | Sum xs
  | Mul xs  => 1 +
      (fix ranks xs :=
        match xs with
        | []        => 0
        | x' :: xs' =>
            rank x' + ranks xs'
        end
      ) xs
  end.

Program Fixpoint diff s x {measure (rank x)} : aexp :=
  match x with
  | (* D_s n := 0 *)
    Con _ => Con 0
  | (* D_s a := a <> s ? 0 : 1 *)
    Var a =>
      Con (if negb (String.eqb a s) then 0 else 1)
  | (* D_s a**n := (n >= 0) ->
        n = 0 || a <> s ? 0 : n*(a**(n-1)) *)
    Pow a n =>
      if Z.ltb n 0 then Var "ERROR"
      else if Z.eqb n 0 ||
        negb (String.eqb a s) then Con 0
      else Mul [Con n; Pow a (n - 1)]
  | (* D_s Sum_i xi :=
        D_s x0 + D_s Sum_{i>0} xi *)
    Sum xs =>
      match xs with
      | []        => Con 0
      | x' :: xs' =>
          Sum [diff s x'; diff s (Sum xs')]
      end
  | (* D_s Mul_i xi :=
        D_s x0 * Mul_{i>0} xi +
        x0 * D_s Mul_{i>0} xi *)
    Mul xs =>
      match xs with
      | [] => Con 0
      | x' :: xs' =>
          Sum [
            Mul [diff s x'; Mul xs'];
            Mul [x'; diff s (Mul xs')]
          ]
      end
  end.
Next Obligation.
  cbn; lia.
Defined.
Next Obligation.
  destruct x'.
  all: cbn; lia.
Defined.
Next Obligation.
  destruct x'.
  all: cbn; lia.
Defined.
Next Obligation.
  destruct x'.
  all: cbn; lia.
Defined.

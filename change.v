Require Import ZArith.
Require Import Bool.
Require Import List.
Import ListNotations.

Fixpoint solution (coins: list Z) (amount: Z) : Z :=
    if Z.eqb amount 0 then 1
    else if Z.ltb amount 0 then 0
    else
    match coins with
    | [] => 0
    | hd::tl => (solution coins (amount-hd)) + (solution tl amount)
    end.
Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.

Fixpoint solution(lst: list Z) : Z :=
    match lst with
    | [] => -10000000
    | hd::[] => hd
    | hd::tl => if Z.ltb (solution tl) hd then hd else solution tl
    end.


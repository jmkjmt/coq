Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.


Fixpoint remove_elem (A:Type) (e: A) (lst:list A) : list A :=
    match lst with
    | [] => []
    | hd::tl => if e =? hd then remove_elem e tl else hd::(remove_elem e tl)
    end.

Fixpoint solution (A:Type) (lst:list A) : list A :=
    match lst with
    | [] => []
    | hd::tl => hd::(remove_elem hd (solution tl))
    end.

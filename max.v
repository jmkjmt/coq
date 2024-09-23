Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint solution(lst: list Z) : Z :=
    match lst with
    | [] => -10000000
    | hd::[] => hd
    | hd::tl => if Z.ltb (solution tl) hd then hd else solution tl
    end.

Fixpoint fold (f: Z -> Z -> Z) (l: list Z) (a: Z) : Z :=
	match l with
	| [] => a
	| hd::tl => f hd (fold f tl a)
    end.

Definition max (lst: list Z) : Z :=
	match lst with
	| [] => -10000000
	| hd::tl => fold (fun (x: Z) (y: Z) => if Z.ltb y x then x else y) lst hd
    end.

    

    

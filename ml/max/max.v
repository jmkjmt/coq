Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint ta1(lst: list Z) : Z :=
    match lst with
    | [] => 0
    | hd::[] => hd
    | hd::tl => if Z.ltb (ta1 tl) hd then hd else ta1 tl
    end.

Fixpoint fold (f: Z -> Z -> Z) (l: list Z) (a: Z) : Z :=
	match l with
	| [] => a
	| hd::tl => f hd (fold f tl a)
    end.

Fixpoint loop (fir: Z) (ilst: list Z) : Z :=
    match ilst with
    | [] => fir
    | h::t => if h >? loop fir t then h else loop fir t
    end.
Definition sol118 (lst: list Z) : Z :=
    match lst with
    | [] => 0
    | hd::tl => loop hd tl
    end.
Definition ta_aux (a b: Z) : Z :=
    if a <? b then b else a.
Definition sol164 (lst : list Z) : Z :=
    match lst with
    | [] => 0
    | hd::tl => fold ta_aux lst hd
    end.

Theorem ta1_sol118: forall lst, ta1 lst = sol118 lst.
Proof.
    unfold sol118.
    intros.
    induction lst.
    reflexivity.
    simpl.
    destruct lst.
    reflexivity.
    rewrite IHlst.
    simpl.
    case (loop z lst <? a) eqn:E.
    case (z >? loop a lst) eqn:E1.
    destruct lst.
    simpl in *.
    
    (*  very hard..... *)
    Abort.

Theorem ta1_sol164: forall lst, ta1 lst = sol164 lst.
Proof.
    unfold sol164.
    induction lst.
    reflexivity.
    simpl.
    destruct lst.
    simpl.
    unfold ta_aux.
    case (a <? a) eqn:E.
    reflexivity.
    reflexivity.
    rewrite IHlst.
    simpl.
    (* vert hard... *)
    Abort.
    


    

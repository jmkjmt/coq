Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.


Fixpoint remove_elem_1 (e: Z) (lst:list Z) : list Z :=
    match lst with
    | [] => []
    | hd::tl => if Z.eqb e hd then remove_elem_1 e tl else hd::(remove_elem_1 e tl)
    end.

Fixpoint solution_1 (lst:list Z) : list Z :=
    match lst with
    | [] => []
    | hd::tl => hd::(remove_elem_1 hd (solution_1 tl))
    end.


Fixpoint is_in_3 (lst:list Z) (a:Z) : bool :=
    match lst with
    | [] => false
    | hd::tl => if Z.eqb a hd then true else is_in_3 tl a
    end.

Fixpoint unique_3 (lst1:list Z) (lst2: list Z) : list Z :=
    match lst1 with
    | [] => lst2
    | hd::tl => if is_in_3 lst2 hd then unique_3 tl lst2 else unique_3 tl (lst2 ++ [hd])
    end.

Definition solution_3 (lst:list Z) : list Z :=
    unique_3 lst [].

Definition solution_4 (lst: list Z) : list Z :=
    let fix isNotIn_4 (tlst: list Z) (c: Z) : bool :=
        match tlst with
        | [] => true
        | hd::tl => if Z.eqb hd c then false else isNotIn_4 tl c
        end
    in
    let fix uniqSave_4 (l1:list Z) (l2:list Z) : list Z :=
        match l1 with
        | [] => l2
        | hd::tl => if isNotIn_4 l2 hd then uniqSave_4 tl (l2++[hd]) else uniqSave_4 tl l2
        end
    in
    uniqSave_4 lst [].

(* Fixpoint drop_2 (lst:list Z) (n:Z): list Z :=
    match lst with
    | [] => []
    | hd::tl => if Z.eqb hd n then drop_2 tl n else hd :: (drop_2 tl n)
    end.

Fixpoint solution_2 (lst:list Z) : list Z :=
    match lst with
    | [] => []
    | hd::tl => hd :: solution_2 (drop_2 tl hd)
    end. *)
Lemma l1 : forall lst, forall (a: Z), a:: remove_elem_1 a lst = unique_3 lst [a].
Proof.
    intros lst.
    induction lst.
    reflexivity.
    simpl.
    intros.
    case (Z.eqb a0 a) eqn: H.
    rewrite Z.eqb_eq in H.
    rewrite H.
    rewrite Z.eqb_refl.
    rewrite IHlst.
    reflexivity.
    SearchRewrite (_ =? _ ).
    rewrite Z.eqb_sym in H.
    rewrite H.
    induction lst.
    simpl.
    reflexivity.
    simpl.
    case (Z.eqb a0 a1) eqn: H1.
    rewrite Z.eqb_sym in H1.
    rewrite H1.
    rewrite IHlst in IHlst0.


Theorem eq1: forall lst: list Z, solution_1 lst = solution_3 lst. 
Proof.
    intros.
    unfold solution_3.
    induction lst.
    reflexivity.
    simpl.
    rewrite IHlst.
    induction lst.
    reflexivity.
    induction lst.



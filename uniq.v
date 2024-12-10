Require Import Arith.
Require Import List.
Require Import Bool.
Import ListNotations.
Fixpoint remove_elem_1 (e:nat) (lst:list nat) : list nat :=
    match lst with
    | nil => nil
    | hd::tl => if Nat.eqb e hd then remove_elem_1 e tl else hd::(remove_elem_1 e tl)
    end.

Fixpoint solution_1 lst :=
    match lst with
    | nil => nil
    | hd::tl => hd::(remove_elem_1 hd (solution_1 tl))
    end.


Fixpoint is_in_3 (lst:list nat) (a:nat) : bool :=
    match lst with
    | nil => false
    | hd::tl => if Nat.eqb a hd then true else is_in_3 tl a
    end.

Fixpoint unique_3 (lst1:list nat) (lst2: list nat) : list nat :=
    match lst1 with
    | nil => lst2
    | hd::tl => if is_in_3 lst2 hd then unique_3 tl lst2 else unique_3 tl (lst2 ++ hd::nil)
    end.

Definition solution_3 (lst:list nat) : list nat :=
    unique_3 lst nil.


Fixpoint isNotIN_4 (lst: list nat) (c: nat) : bool :=
    match lst with
    | nil => true
    | hd::tl => if Nat.eqb hd c then false else isNotIN_4 tl c
    end.

Fixpoint uniqSave_4 (l1:list nat) (l2:list nat) : list nat :=
    match l1 with
    | nil => l2
    | hd::tl => if isNotIN_4 l2 hd then uniqSave_4 tl (l2++hd::nil) else uniqSave_4 tl l2
    end.
Definition solution_4 (lst: list nat) : list nat := uniqSave_4 lst nil.

(* Fixpoint drop_2 (lst:list nat) (n:nat): list nat :=
    match lst with
    | nil => nil
    | hd::tl => if Nat.eqb hd n then drop_2 tl n else hd :: (drop_2 tl n)
    end.

Fixpoint solution_2 (lst:list nat) : list nat :=
    match lst with
    | nil => nil
    | hd::tl => hd :: solution_2 (drop_2 tl hd)
    end. *)
Theorem eq: forall lst, solution_3 lst = solution_4 lst.
Proof.
    assert(lemma1: forall lst1 lst2, unique_3 lst1 lst2 = uniqSave_4 lst1 lst2).
    {
        induction lst1.
        reflexivity.
        intros.
        simpl.
        rewrite IHlst1.
        rewrite IHlst1.
        case (is_in_3 lst2 a) eqn:E.
        assert(forall lst2 a ,is_in_3 lst2 a = true -> isNotIN_4 lst2 a = false).
        {
            induction lst0.
            simpl.
            discriminate.
            simpl.
            intros.
            case (Nat.eqb a0 a1) eqn:E1.
            reflexivity.
            apply IHlst0.
            rewrite Nat.eqb_sym in E1.
            rewrite E1 in H.
            apply H.
        }
        apply H in E.
        rewrite E.
        reflexivity.
        assert(forall lst2 a, is_in_3 lst2 a = false -> isNotIN_4 lst2 a = true).
        {
            induction lst0.
            simpl.
            reflexivity.
            intros.
            simpl.
            case (Nat.eqb a0 a1) eqn:E1.
            unfold is_in_3 in H.
            rewrite Nat.eqb_sym in E1.
            rewrite E1 in H.
            discriminate.
            apply IHlst0.
            unfold is_in_3 in H.
            rewrite Nat.eqb_sym in E1.
            rewrite E1 in H.
            apply H.
        }
        apply H in E.
        rewrite E.
        reflexivity.
    }
    induction lst.
    reflexivity.
    unfold solution_3.
    unfold solution_4.
    simpl.
    apply lemma1.
    Qed.

Theorem test:forall n lst, is_in_3 (unique_3 lst [n]) n = true.
Proof.
    intros.
    generalize dependent n.
    induction lst.
    simpl.
    intros.
    rewrite Nat.eqb_refl.
    reflexivity.
    simpl.
    intros.
    case (Nat.eqb a n) eqn:E.
    rewrite IHlst.
    reflexivity.
    simpl.
    
    
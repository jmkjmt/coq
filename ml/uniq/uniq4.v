Require Import Arith.
Require Import List.
Require Import Bool Program.
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

Fixpoint all_diff a lst :=
match lst with
| [] => true
| hd::tl => if a =? hd then false else all_diff a tl
end.

Fixpoint is_uniq lst :=
match lst with
| [] => true
| hd::tl => if all_diff hd tl then is_uniq tl else false
end.

Theorem equiv: forall lst, solution_1 lst = solution_4 lst.
Proof.
    unfold solution_4.
    induction lst.
    simpl.
    reflexivity.
    simpl.
    rewrite IHlst.
    destruct lst.
    simpl.
    reflexivity.
    simpl.
    case (a =? n) eqn:E.
    rewrite Nat.eqb_eq in E.
    rewrite E in *.
    destruct lst.
    simpl.
    rewrite Nat.eqb_refl.
    reflexivity.
    simpl.
    case (n =? n0) eqn:E1.
    rewrite Nat.eqb_eq in E1.
    rewrite E1 in *.
    2:{
        destruct lst.
        2:{
            simpl.
            case (n =? n1)eqn:E2.
            2:{
                case (n0 =? n1) eqn:E3.
                2:{
                    assert (forall n lst1 lst2, is_uniq (n::lst2) = true ->  n::remove_elem_1 n (uniqSave_4 lst1 (n::lst2)) = uniqSave_4 lst1 (n::lst2)).
                    {
                        clear.
                        intros.
                        generalize dependent n.
                        generalize dependent lst2.
                        induction lst1.
                        simpl.
                        intros.
                        rewrite Nat.eqb_refl.
                        assert (remove_elem_1 n lst2 = lst2).
                        {
                            induction lst2.
                            simpl.
                            reflexivity.
                            simpl in *.
                            case (n =? a) eqn:E.
                            discriminate.
                            rewrite IHlst2.
                            reflexivity.
                            case (all_diff n lst2) eqn:E1.
                            case (all_diff a lst2) eqn:E2.
                            apply H.
                            discriminate.
                            discriminate.                        
                        }
                        rewrite H0.
                        reflexivity.
                        simpl.
                        intros.
                        case (n=?a) eqn:E.
                        rewrite Nat.eqb_eq in E.
                        rewrite E in *.
                        apply IHlst1.
                        simpl.
                        apply H.
                        case (isNotIN_4 lst2 a) eqn:E1.
                        apply IHlst1.
                        simpl.
                        2:{
                            apply IHlst1.
                            simpl.
                            exact H.
                        }
                        clear IHlst1.
                        clear lst1.
                        induction lst2.
                        simpl in *.
                        rewrite E.
                        reflexivity.
                        simpl in *.
                        case (n =? a0) eqn:E2.
                        discriminate.
                        case (all_diff n (lst2 ++ [a])) eqn:E3.
                        simpl in *.
                        2:{
                            rewrite IHlst2.
                            reflexivity.
                            case (all_diff n lst2) eqn:E4.
                            case (all_diff a0 lst2) eqn:E5.
                            exact H.
                            discriminate.
                            discriminate.
                            case (a0 =?a)eqn:E4.
                            discriminate.
                            exact E1.
                        }
                        case (a0 =? a) eqn:E4.
                        discriminate.
                        (* I don't know.... *)



                    }
                }
            }
        }
    }

        (* synthesize generalize term *)
        
    Abort.
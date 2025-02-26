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
    (* unique_3's first argument is decreasing but second argument is not decreasing!*)

Definition solution_3 (lst:list nat) : list nat :=
    unique_3 lst nil.
(*     
Lemma sg : forall lst1 lst2 a, is_uniq (a::lst2) = true -> a :: remove_elem_1 a (unique_3 lst1 lst2) = unique_3 lst1 (a::lst2).
Proof.
    assert (forall lst1 lst2 lst3 a , is_uniq (lst3 ++ a::lst2) = true -> a::remove_elem_1 a (unique_3 (lst3 ++ lst1) lst2 ) = a :: remove_elem_1 a (unique_3 lst1 (lst2 ++ lst3))).
    {
        simpl.
        intros.
        generalize dependent a.
        generalize dependent lst2.
        generalize dependent lst1.
        induction lst3.
        simpl.
        intros.
        assert (lst2 ++ [] = lst2).
        {
            clear.
            induction lst2.
            simpl.
            reflexivity.
            simpl.
            rewrite IHlst2.
            reflexivity.
        }
        rewrite H0.
        reflexivity.
        simpl.
        assert (forall lst3 lst2 a a0, all_diff a (lst3 ++ a0::lst2) = true -> is_in_3 lst2 a = false).
        {
            clear.
            induction lst3.
            simpl.
            intros.
            case (a =? a0) eqn:E.
            discriminate.
            induction lst2.
            simpl in *.
            reflexivity.
            simpl in *.
            case (a =? a1) eqn:E1.
            discriminate.
            apply IHlst2.
            apply H.
            simpl.
            intros lst2 a0 a1.
            case (a0 =?a) eqn:E.
            intros.
            discriminate.
            apply IHlst3.
        }
        intros lst1 lst2 a0.
        rewrite H with (a0 := a0) (lst3 := lst3).
        simpl.
        intros.
        assert (lst2 ++ a :: lst3 = (lst2 ++ [a]) ++ lst3).
        {
            clear.
            induction lst2.
            simpl.
            reflexivity.
            simpl.
            rewrite IHlst2.
            reflexivity.        
        }
        rewrite H1.
        rewrite IHlst3.
        reflexivity.
        assert (forall a lst, is_uniq (a::lst) = is_uniq (lst ++ [a])).
        {
            clear.
            intros.
            generalize dependent a.
            induction lst.
            simpl.
            reflexivity.
            simpl in *.
            intros.
            rewrite IHlst.
            case (a0 =? a) eqn:E.
            rewrite Nat.eqb_eq in E.
            rewrite E in *.
            assert (all_diff a (lst ++ [a]) = false).
            {
                clear.
                induction lst.
                simpl.
                rewrite Nat.eqb_refl.
                reflexivity.
                simpl.
                rewrite IHlst.
                case (a =? a0).
                reflexivity.
                reflexivity.
            }
            rewrite H.
            reflexivity.
            rewrite <- IHlst.
            rewrite <- IHlst.
            induction lst.
            simpl.
            rewrite Nat.eqb_sym in E.
            rewrite E.
            reflexivity.
            simpl.
            case (a =? a1) eqn: E1.
            rewrite Nat.eqb_eq in E1.
            rewrite E1 in *.
            rewrite E in *.
            case (is_uniq lst && all_diff a1 lst) eqn:E2.
            simpl.
            case (all_diff a0 lst).
            simpl.
            reflexivity.
            reflexivity.
            reflexivity.
            case (a0 =? a1) eqn:E2.
            rewrite Nat.eqb_eq in E2.
            rewrite E2 in *.
            case (is_uniq lst && all_diff a1 lst) eqn:E3.
            simpl.
            case (all_diff a lst).
            reflexivity.
            reflexivity.
            reflexivity.











        }



    }
    
     *)

(* 

Theorem asdf: forall lst: list nat, solution_1 lst = solution_3 lst.
Proof.
    unfold solution_3.
    induction lst.
    simpl.
    reflexivity.
    simpl.
    rewrite IHlst.
    destruct lst.
    simpl.
    reflexivity.
    simpl.
    simpl in *.
    case (n =? a) eqn:E.
    rewrite Nat.eqb_eq in E.
    rewrite E in *.
    2:{
        destruct lst.
        simpl.
        rewrite Nat.eqb_sym in E.
        rewrite E.
        reflexivity.
        simpl.
        case (n0 =? n) eqn:E1.
        rewrite Nat.eqb_eq in E1.
        rewrite E1 in *.
        rewrite E.
        simpl in *.
        rewrite Nat.eqb_refl in *.
        2:{
            case (n0 =? a) eqn:E2.
            2:{
                destruct lst.
                2:{
                    simpl.

                }     






            }
        }


    } *)
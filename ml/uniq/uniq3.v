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


Theorem eq : forall lst, solution_1 lst = solution_3 lst.
Proof.
    unfold solution_3.
    induction lst.
    simpl.
    reflexivity.
    simpl.
    rewrite IHlst.
    destruct lst.
    2:{
        simpl.
        case (n=?a) eqn:E.
        2:{
            assert (forall a lst1 lst2, is_uniq (a ::lst2) = true -> a :: remove_elem_1 a (unique_3 lst1 lst2) = unique_3 lst1 (a::lst2)).
            {
                clear.
                intros.
                generalize dependent lst2.
                generalize dependent a.
                induction lst1.
                simpl.
                intros.
                assert (remove_elem_1 a lst2 = lst2).
                {
                    induction lst2.
                    simpl in *.
                    reflexivity.
                    simpl in *.
                    case (a=?a0) eqn:E.
                    discriminate.
                    rewrite IHlst2.
                    reflexivity.
                    case (all_diff a lst2) eqn:E1.
                    case (all_diff a0 lst2) eqn:E2.
                    apply H.
                    discriminate.
                    discriminate.
                }
                rewrite H0.
                reflexivity.
                simpl in *.
                intros.
                case (a =? a0) eqn:E.
                rewrite Nat.eqb_eq in E.
                rewrite E in *.
                case (is_in_3 lst2 a0) eqn:E1.
                apply IHlst1.
                apply H.
                2:{
                    case (is_in_3 lst2 a) eqn:E1.
                    apply IHlst1.
                    apply H.
                    apply IHlst1.
                    
                }
                assert (forall lst1 lst2 lst2, is_uniq (a::lst2++lst3) = true -> a :: remove_elem_1 a (unique_3 (lst1 ++lst2) (lst3)) = unique_3 lst1 (lst3++lst2)).
                {

                }







                

            }
        }
    

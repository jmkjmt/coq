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

Fixpoint drop_2 (lst:list nat) (n:nat): list nat :=
    match lst with
    | nil => nil
    | hd::tl => if Nat.eqb hd n then drop_2 tl n else hd :: (drop_2 tl n)
    end.

Program Fixpoint solution_2 (lst:list nat) {measure 0} : list nat :=
    match lst with
    | nil => nil
    | hd::tl => hd :: solution_2 (drop_2 tl hd)
    end.
Next Obligation.
Admitted.
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

Fixpoint mk_remove lst1 lst2 :=
    match lst2 with
    | [] => solution_1 lst1
    | hd::tl => remove_elem_1 hd (mk_remove lst1 tl)
    end.

Inductive AllDistinct {A : Type} : list A -> Prop :=
| Dist_nil : AllDistinct []
| Dist_cons : forall x l, 
    ~ In x l ->
    AllDistinct l -> 
    AllDistinct (x :: l).
Lemma AllDistinct_tail {A : Type} : 
  forall (a : A) (lst : list A),
    AllDistinct (a :: lst) -> AllDistinct lst.
Proof.
  intros a lst H.
  inversion H as [| x l H_not_in H_dist H_eq].
  subst.
  exact H_dist.
Qed.
Lemma AllDistinct_head {A:Type}:
    forall (a:A) (lst: list A),
    AllDistinct (a::lst) -> ~ In a lst.
Proof.
    intros a lst H.
    inversion H as [| x l H_not_in H_dist H_eq].
    subst.
    exact H_not_in.
Qed.
Theorem thm1 : forall lst1 lst2, AllDistinct lst1 -> solution_1 lst2 = unique_3 lst2 [] -> lst1 ++ mk_remove lst2 lst1 = unique_3 lst2 lst1.
Proof.
    induction lst1.
    simpl.
    intros.
    apply H0.
    simpl.
    intros.
    assert (forall a lst1 lst2, AllDistinct (a::lst1) -> solution_1 lst2 = unique_3 lst2 [] -> remove_elem_1 a (mk_remove lst2 lst1) = mk_remove (remove_elem_1 a lst2) lst1).
    {
        clear.
        intros.
        generalize dependent a.
        generalize dependent lst1.
        assert (forall a a0 lst, a0 =? a = false -> remove_elem_1 a0 (remove_elem_1 a lst) = remove_elem_1 a (remove_elem_1 a0 lst)).
        {
            clear.
            intros.
            generalize dependent a.
            generalize dependent a0.
            induction lst.
            simpl.
            reflexivity.
            simpl.
            intros.
            case (a1 =? a) eqn:E.
            rewrite Nat.eqb_eq in E.
            rewrite E in *.
            rewrite H.
            simpl.
            rewrite Nat.eqb_refl.
            apply IHlst.
            apply H.
            simpl.
            case (a0 =? a) eqn:E1.
            apply IHlst.
            apply H.
            simpl.
            rewrite E.
            rewrite IHlst.
            reflexivity.
            apply H.
        }
        induction lst1.
        simpl.
        intros.
        assert(forall a lst, remove_elem_1 a (solution_1 lst) = solution_1 (remove_elem_1 a lst)).
        {
            clear lst2 H0 a H1.
            intros.
            generalize dependent a.
            induction lst.
            simpl.
            reflexivity.
            simpl.
            intros.
            case (a0 =? a) eqn:E.
            rewrite Nat.eqb_eq in E.
            rewrite E in *.
            assert (forall a lst, remove_elem_1 a (remove_elem_1 a (lst)) = remove_elem_1 a (lst)).
            {
                clear.
                intros.
                generalize dependent a.
                induction lst.
                intros.
                reflexivity.
                simpl.
                intros.
                case (a0 =? a) eqn:E.
                rewrite Nat.eqb_eq in E.
                rewrite E in *.
                rewrite IHlst.
                reflexivity.
                simpl.
                rewrite E.
                rewrite IHlst.
                reflexivity. 
            }
            rewrite H0.
            rewrite IHlst.
            reflexivity.
            simpl.
            rewrite <- IHlst.
            rewrite H.
            reflexivity.
            apply E.
        }
        rewrite H2.
        reflexivity.
        simpl.
        intros.
        rewrite <- IHlst1.
        rewrite H.
        reflexivity.
        clear lst2 H0 H IHlst1.
        inversion H1.
        subst.
        simpl in H2.
        firstorder.
        case (a0 =? a) eqn:E.
        rewrite Nat.eqb_eq in E.
        rewrite E in *.
        firstorder.
        reflexivity.
        inversion H1.
        subst.
        inversion H5.
        subst.
        constructor.
        simpl in H4.
        firstorder.
        apply H7.        
    }
    assert(forall a lst2 lst1, a::unique_3 (remove_elem_1 a lst2) lst1 = unique_3 lst2 (a::lst1)).
    {
        clear.
        intros.
        generalize dependent a.
        generalize dependent lst1.
        induction lst2.
        simpl.
        reflexivity.
        simpl.
        intros.
        case (a0 =? a) eqn:E.
        rewrite Nat.eqb_eq in E.
        rewrite E in *.
        rewrite Nat.eqb_refl.
        apply IHlst2.
        rewrite Nat.eqb_sym in E.
        rewrite E in *.
        simpl.
        case (is_in_3 lst1 a) eqn:E1.
        rewrite IHlst2.
        reflexivity.
        simpl.
        rewrite IHlst2.
        reflexivity.
    }
    rewrite H1.
    rewrite IHlst1.
    rewrite H2.
    reflexivity.
    inversion H.
    apply H6.
    Focus 2.
    apply H.
    Focus 2.
    rewrite H0.
    reflexivity.
    (* Strong induction? *)
Abort.

Fixpoint length (lst : list nat) : nat :=
    match lst with
    | nil => 0
    | hd::tl => 1 + length tl
    end. 

Lemma elem : forall a lst, length( remove_elem_1 a lst ) <= length lst.
Proof.
    intros.
    generalize dependent a.
    induction lst.
    simpl.
    intros.
    auto.
    simpl.
    intros.
    case (a0 =? a) eqn:E.
    rewrite Nat.eqb_eq in E.
    rewrite E in *.
    auto.
    simpl.
    Search (_ <= _ -> _ <= _).
    apply le_n_S.
    apply IHlst.
Qed.
Theorem sol1sol3 : forall lst, solution_1 lst = solution_3 lst.
Proof.
    unfold solution_3.
    induction lst.
    reflexivity.
    simpl.
    induction lst.
    reflexivity.
    simpl.
    case (a =? a0) eqn:E.
    rewrite Nat.eqb_eq in E.
    rewrite E in *.
    rewrite Nat.eqb_refl.
    assert (forall a lst, remove_elem_1 a (remove_elem_1 a (lst)) = remove_elem_1 a (lst)).
    {
        clear.
        intros.
        generalize dependent a.
        induction lst.
        intros.
        reflexivity.
        simpl.
        intros.
        case (a0 =? a) eqn:E.
        rewrite Nat.eqb_eq in E.
        rewrite E in *.
        rewrite IHlst.
        reflexivity.
        simpl.
        rewrite E.
        rewrite IHlst.
        reflexivity. 
    }
    rewrite H.
    simpl in *.
    apply IHlst.
    rewrite Nat.eqb_sym in E.
    rewrite E in *.

    


    
    

    
    
    
    


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
    (* grow infinitely..*)
    assert(forall lst1 lst2 n, is_in_3 (unique_3 lst1 ([n]++lst2)) n = true).
    {
        assert (forall n: nat , forall lst, n :: lst = ([n]++lst)).
        {
            intros.
            generalize dependent n.
            induction lst0.
            simpl.
            reflexivity.
            simpl.
            reflexivity.
        }
        induction lst1.
        simpl.
        intros.
        rewrite Nat.eqb_refl.
        reflexivity.
        simpl.
        intros.
        case (a0 =? n0) eqn:E1.
        rewrite H.
        rewrite IHlst1.
        reflexivity.
        case (is_in_3 lst2 a0) eqn:E2.
        rewrite H.
        rewrite IHlst1.
        reflexivity.
        rewrite H.
        rewrite IHlst1.
        reflexivity.
    }
    assert (forall n1 : nat, forall n2, [n1;n2] = [n1]++[n2]).
    {
        intros.
        simpl.
        reflexivity.
    }
    rewrite H0.
    rewrite H.
    reflexivity.
    Qed.
    Abort.
    (* assert (forall lst1 lst2 n, is_in_3 lst1 n = true -> is_in_3 (unique_3 lst2 lst1) n = true ).
    {
        intros.
        generalize dependent n0.
        generalize dependent lst1.
        induction lst2.
        intros.
        simpl.
        rewrite H.
        reflexivity.
        simpl.
        intros.
        case (is_in_3 lst1 a0) eqn:E1.
        rewrite IHlst2.
        reflexivity.
        rewrite H.
        reflexivity.
        rewrite IHlst2.
        reflexivity. *)
Theorem q: forall n lst, remove_elem_1 n lst = drop_2 lst n.
Proof.
    induction lst.
    simpl.
    reflexivity.
    simpl.
    case (n =? a) eqn:E.
    Search (_ =? _ = true).
    rewrite Nat.eqb_eq in E.
    rewrite <- E.
    rewrite Nat.eqb_refl.
    rewrite IHlst.
    reflexivity.
    rewrite Nat.eqb_sym in E.
    rewrite E.
    rewrite IHlst.
    reflexivity.
    Qed.
    
Theorem equiv: forall lst, solution_1 lst = solution_2 lst.
Proof.
    induction lst.
    reflexivity.
    simpl.
    induction lst.
    simpl.
    cbn.
    rewrite F_unfold.
    reflexivity.
    simpl.
    case (a=?a0) eqn:E.
    rewrite Nat.eqb_eq in E.
    rewrite E in *.
    unfold solution_2.
    simpl.
    rewrite fix_sub_eq.
    simpl.
    fold solution_2.
    rewrite Nat.eqb_refl.
    


    
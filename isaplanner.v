Require Import Bool Arith ZArith List Program.

Import ListNotations.
Fixpoint count n lst : nat :=
    match lst with
    | [] => 0
    | hd::tl => if Nat.eqb hd n then S (count n tl) else count n tl
    end.
Theorem goal_52 : forall (n : nat) (xs : list nat), count n xs = count n (rev xs).
Proof.
    intros.
    induction xs.
    simpl.
    reflexivity.
    simpl.
    case (a=? n) eqn:E.
    rewrite IHxs.
    rewrite Nat.eqb_eq in E.
    rewrite E in *.
    assert (forall n lst, S (count n lst) = count n (lst ++[n])).
    {
        clear.
        intros.
        generalize dependent n.
        induction lst.
        simpl.
        intros.
        rewrite Nat.eqb_refl.
        reflexivity.
        simpl.
        intros.
        rewrite IHlst.
        case (a=?n) eqn:E.
        reflexivity.
        rewrite IHlst.
        reflexivity.
    }
    rewrite H.
    reflexivity.
    rewrite IHxs.
    assert (forall a n lst, a=?n = false -> count n lst = count n (lst ++[a])).
    {
        clear.
        intros.
        generalize dependent n.
        generalize dependent a.
        induction lst.
        simpl.
        intros.
        rewrite H.
        reflexivity.
        simpl.
        intros.
        case (a=?n) eqn:E.
        rewrite Nat.succ_inj_wd.
        apply IHlst.
        exact H.
        apply IHlst.
        exact H.
    }
    apply H.
    exact E.
Qed.

(* Theorem goal_53 : forall n xs, count n xs = count n (sort xs). *)
Fixpoint delete n lst : list nat :=
    match lst with
    | [] => []
    | hd::tl => if Nat.eqb hd n then tl else hd::(delete n tl)
    end.
Theorem goal_69 : forall n xs, length (delete n xs) <=? length xs = true.
Proof.
    induction xs.
    simpl.
    reflexivity.
    simpl.
    case (a=?n) eqn:E.
    assert (p:= Nat.le_succ_diag_r).
    Search (_ <= _ -> _ <=? _ = true).
    apply leb_correct.
    apply p.
    simpl.
    rewrite IHxs.
    reflexivity.
Qed.

Fixpoint elem n lst : bool :=
    match lst with
    | [] => false
    | hd::tl => if hd =? n then true else elem n tl
    end.

Fixpoint ins n lst : list nat :=
    match lst with
    | [] => [n]
    | hd::tl => if n <? hd then n::lst else hd::ins n tl
    end.
Theorem goal_72 : forall x y xs, x <? y = true -> elem x (ins y xs) = elem x xs.
Proof.
    intros.
    generalize dependent x.
    generalize dependent y.
    induction xs.
    intros.
    simpl.
    assert (y =? x = false).
    {
        case (y=?x) eqn:E.
        Search (_ =? _ = true).
        rewrite Nat.eqb_eq in E.
        rewrite E in *.
        Search (_ <? _).
        rewrite Nat.ltb_irrefl in *.
        discriminate.
        reflexivity.
    }
    rewrite H0.
    reflexivity.
    simpl.
    intros.
    case (y <? a) eqn:E.
    simpl.
    assert (y =? x = false).
    {
        case (y=?x) eqn:E'.
        Search (_ =? _ = true).
        rewrite Nat.eqb_eq in E'.
        rewrite E' in *.
        Search (_ <? _).
        rewrite Nat.ltb_irrefl in *.
        discriminate.
        reflexivity.
    }
    rewrite H0.
    reflexivity.
    simpl.
    case (a=?x) eqn:E'.
    reflexivity.
    apply IHxs.
    exact H.
Qed.
Fixpoint drop n lst : list nat :=
    match lst with
    | [] => []
    | hd::tl => if n =? 0 then lst else drop (n-1) tl
    end.

Fixpoint take n lst : list nat :=
    match lst with
    | [] => []
    | hd ::tl => if n=? 0 then [] else hd::take (n-1) tl
    end.
(* Theorem goal_74 : forall i xs, rev (drop i xs) = take (length xs - i) (rev xs).
Proof. *)






    
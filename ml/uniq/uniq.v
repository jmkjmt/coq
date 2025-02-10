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
    (* synthesize generalize term *)
    Abort.

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
    Abort.

Theorem equiv: forall lst, solution_1 lst = solution_4 lst.
Proof.
    unfold solution_4.
    induction lst.
    simpl.
    reflexivity.
    simpl.
    induction lst.
    simpl.
    reflexivity.
    simpl.
    case ( a=? a0) eqn:E.
    rewrite Nat.eqb_eq in E.
    rewrite E in *.

        (* synthesize generalize term *)
        
    Abort.

Fixpoint comb lst a := 
  match lst with
    [] => [a]
    |hd::tl => if hd =? a then lst else hd::(comb tl a)
  end.

Fixpoint app l1 l2 :=
  match l1 with
    [] => l2
    |hd :: tl => app tl (comb l2 hd)
  end.
    
Definition sol4 lst := app lst [].
  
Theorem ta1_sol4 : forall lst, solution_1 lst = sol4 lst.
Proof.
    unfold sol4.
    induction lst.
    simpl.
    reflexivity.
    simpl.
    induction lst.
    simpl.
    reflexivity.
    simpl.
    case (a=?a0) eqn:E.
    rewrite Nat.eqb_eq in E.
    rewrite E in *.
    (* synthesize generalize term *)
    Abort.

(* Fixpoint chk lst a :=
 match lst with
  [] => true
  |hd::tl => if (hd =? a) then false else chk tl a
 end.

Fixpoint del lst a :=
 match lst with
  [] => []
  |hd::tl => if (hd =? a) then del tl a else hd :: del tl a
 end.

Fixpoint sol5 lst :=
match lst with
  [] => []
  |hd :: tl => if (chk tl hd) then hd :: sol5 tl else hd :: sol5 (del tl hd)
  end. *)
Fixpoint rev (a accum : list nat) :=
    match a with
      |[] => accum
      |hd::tl => rev tl ([hd] ++ accum)
    end.

Definition fastrev lst := rev lst [].
  
Fixpoint search l1 e :=
  match l1 with
    |[] => false
    |hd::tl => if hd =? e then true else search tl e
    end.
  
Fixpoint delete lst :=
  match lst with
    |[] => []
    |hd::tl => if search tl hd then delete tl else [hd] ++ delete tl
    end.
  
Definition sol9 lst := fastrev (delete (fastrev lst)).

Theorem ta1_sol9 : forall lst, solution_1 lst = sol9 lst.
Proof.
    unfold sol9.
    unfold fastrev.
    induction lst.
    simpl.
    reflexivity.
    simpl.
    induction lst.
    simpl.
    reflexivity.
    simpl.
    (* snthesize generalize term *)
    Abort.
(* 
Fixpoint find x lst :=
  match lst with
    | [] => false
    | hd::tl => (x =? hd)||find x tl
  end.

Fixpoint sol20 lst :=
  match List.rev lst with
    | [] => []
    | hd::tl => if find hd tl then sol20 (List.rev tl) else (sol20 (List.rev tl)) ++ [hd]
  end. *)

(* Definition aux (s l: list nat) (f: nat -> bool) := 
match l with
[] => s
| hd::tl => if (f hd) then (s ++ (hd::(filter f tl))) else (s ++ (filter f tl))
end.
    
Fixpoint sol43 lst :=
match lst with
  [] => []
  | hd::tl => hd :: (sol43 (filter (fun x => negb (x =? hd)) tl))
end. *)
Fixpoint check item l := 
match l with
        | [] => [item]
        | hd :: tl => if hd =? item then l else hd :: check item tl
end.
Fixpoint putIn list1 list2 := 
match list1 with
    | [] => list2
    | hd :: tl =>
       putIn tl (check hd list2)
end.

Definition sol57 lst := putIn lst [].

Theorem ta1_sol57 : forall lst, solution_1 lst = sol57 lst.
Proof.
    unfold sol57.
    induction lst.
    simpl.
    reflexivity.
    simpl.
    induction lst.
    simpl.
    reflexivity.
    simpl.
    case (a=?a0) eqn:E.
    (* synthesize generalize term *)
    Abort.

Fixpoint reverse (l: list nat) :=
  match l with
    | [] => l
    | hd::tl => reverse tl ++ [hd]
end.

Fixpoint insert a l :=
  match l with
    | [] => [a]
    | hd::tl => if a <? hd then a::hd::tl 
                else hd:: (insert a tl)
end.

Fixpoint checker l1 a := 
  match l1 with
    | [] => false
    | [k] => k =? a 
    | hd::tl => if hd =? a then true else checker tl a
end.

Fixpoint finder l1 fin := 
  match l1 with
    | [] => fin
    | hd::tl => if checker fin hd then finder tl fin else finder tl (hd::fin)
end.

Definition sol75 lst :=
  match lst with
    | [] => []
    | _ => reverse (finder lst [])
end.

Theorem ta1_sol75 : forall lst, solution_1 lst = sol75 lst.
Proof.
    unfold sol75.
    induction lst.
    reflexivity.
    simpl.
    induction lst.
    simpl.
    reflexivity.
    simpl.
    case (a=? a0) eqn:E.
    (* synthesize generalize term *)
    Abort.

Fixpoint reverse89 (l:list nat) a := 
match l with 
    | [] => a
    | hd::tl => reverse89 tl (hd::a) 
end.

Fixpoint gtl e ls := 
match ls with 
          | [] => false
          | h::t => if e =? h then true else gtl e t
end.
Fixpoint checkdrop lt l := 
match lt with
  | [] => l
  | hd::tl =>  if gtl hd l then checkdrop tl l else checkdrop tl (hd::l)
  end.


Definition sol89 lst := reverse89 (checkdrop lst []) [].

Theorem ta1_sol89 : forall lst, solution_1 lst = sol89 lst.
Proof.
    unfold sol89.
    induction lst.
    reflexivity.
    simpl.
    (* syntehszie generalize term *)
    Abort.

Fixpoint fold_left (f : list nat -> nat -> list nat) (a: list nat) (l:list nat) :=
  match l with
  | [] => a
  | h::t => fold_left f (f a h) t
  end.

Fixpoint has_element lst e :=
	match lst with
	| [] => false 
	| hd::tl => (hd =? e)||(has_element tl e)
    end.

Definition sol101 (lst: list nat) :=
 fold_left (fun a x => if has_element a x then a else a ++ [x]) [] lst.

 Theorem ta1_sol101 : forall lst, solution_1 lst = sol101 lst.
 Proof.
    unfold sol101.
    induction lst.
    simpl.
    reflexivity.
    simpl.
    remember (fun (a : list nat) (x : nat) => if has_element a x then a else a ++ [x]) as f.
    induction lst.
    reflexivity.
    simpl.
    case (a =? a0) eqn:E.
    rewrite Nat.eqb_eq in E.
    rewrite E in *.
    rewrite Heqf.
    simpl.
    rewrite Nat.eqb_refl.
    simpl.
    (* rewrite <- Heqf.
    2 :{
        rewrite Heqf.
        simpl.
        rewrite E.
        simpl.
        rewrite <- Heqf.
    } *)
    (* synthesize generalize form *)
    
    Abort.
Theorem exam : forall lst, solution_3 lst = sol4 lst.
Proof.
    unfold solution_3.
    unfold sol4.
    induction lst.
    simpl.
    reflexivity.
    simpl.
    assert (forall lst lst1, unique_3 lst1 lst = app lst1 lst).
    {
        clear.
        intros.
        generalize dependent lst.
        induction  lst1.
        simpl.
        reflexivity.
        simpl.
        intros.
        case (is_in_3 lst a) eqn:E.
        rewrite IHlst1.
        assert (comb lst a = lst).
        {
            clear IHlst1 lst1.
            generalize dependent a.
            induction lst.
            simpl.
            intros.
            discriminate.
            simpl.
            intro a0.
            case (a0 =? a) eqn:E.
            intros.
            rewrite Nat.eqb_eq in E.
            rewrite E in *.
            rewrite Nat.eqb_refl.
            reflexivity.
            intros.
            rewrite Nat.eqb_sym in E.
            rewrite E.
            rewrite IHlst.
            reflexivity.
            exact E0.
        }
        rewrite H.
        reflexivity.
        rewrite IHlst1.
        assert (comb lst a = lst ++ [a]).
        {
            clear IHlst1 lst1.
            generalize dependent a.
            induction lst.
            simpl.
            intros.
            reflexivity.
            simpl.
            intro a0.
            case (a0 =? a) eqn:E.
            intros.
            discriminate.
            intros.
            rewrite Nat.eqb_sym in E.
            rewrite E.
            rewrite IHlst.
            reflexivity.
            exact E0.

        }
        rewrite H.
        reflexivity.
    }
    rewrite H.
    reflexivity.
    Qed.

    
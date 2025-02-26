Require Import String.
Require Import List.
Require Import Arith.
Import ListNotations.

Inductive lambda : Type :=
| V : string -> lambda
| P : string -> lambda -> lambda
| C : lambda -> lambda -> lambda.



Fixpoint is_mem_1 variables string : bool :=
match variables with
| nil => false
| hd::tl => if String.eqb hd string then true else is_mem_1 tl string
end.

Fixpoint sub_check_1 lambda vars : bool :=
match lambda with
| V x => is_mem_1 vars x
| P x e => sub_check_1 e (x::vars)
| C e1 e2 => (sub_check_1 e1 vars) && (sub_check_1 e2 vars)
end.

Definition solution_1 (lambda:lambda) : bool := sub_check_1 lambda [].


Open Scope string_scope.


Fixpoint varExists (var_foo : string) (var_list : list string) : bool :=
		match var_list with
		[] => false
		| h::t => 
			(if var_foo =? h then true
			else (varExists var_foo t))
    end.
			
Definition addToNameList (var_foo : string) (var_list : list string) : list string := 
		if varExists var_foo var_list then 
			var_list
		else 
			var_foo::var_list.
Fixpoint checkRec (lambda_foo : lambda) (var_list : list string) :bool := 
		match lambda_foo with
		V var_bar => 
			(varExists var_bar var_list)
		| P var_bar lambda_bar => 
			checkRec lambda_bar (addToNameList var_bar var_list)
		| C lambda_left lambda_right =>  
			(checkRec lambda_left var_list)
			&& (checkRec lambda_right var_list)
    end.
Definition sol109 (lambda_foo : lambda) : bool := checkRec lambda_foo [].

Fixpoint mk_addtonamelist (lst : list string) :=
  match lst with
  | [] => []
  | hd::tl => addToNameList hd (mk_addtonamelist tl)
  end.


Fixpoint all_diff (v:string) (l:list string) : bool :=
  match l with
  | [] => true
  | hd::tl => if String.eqb v hd then false else all_diff v tl
  end.

  Fixpoint is_uniq lst :=
  match lst with
  | [] => true
  | hd::tl => if all_diff hd tl then is_uniq tl else false
  end.

Theorem ta1_sol109: forall m, solution_1 m = sol109 m.
Proof.
  unfold solution_1.
  unfold sol109.
  induction m.
  simpl.
  reflexivity.
  simpl.
  unfold addToNameList.
  simpl.
  2:{
    simpl.
    rewrite IHm1.
    rewrite IHm2.
    reflexivity.
  }
  assert (forall m lst, is_uniq lst = true -> sub_check_1 m lst = checkRec m lst).
  {
    induction m0.
    simpl.
    induction lst.
    simpl.
    reflexivity.
    simpl.
    intros.
    rewrite IHlst.
    rewrite String.eqb_sym.
    reflexivity.
    case (all_diff a lst) eqn:E.
    exact H.
    discriminate.
    simpl.
    unfold addToNameList.
    intros.
    case (varExists s0 lst) eqn:E.
    rewrite <- IHm0.
    2:{
      exact H.
    }
    2:{
      apply IHm0.
      simpl.
      rewrite H.
      case (all_diff s0 lst) eqn:E1.
      reflexivity.
      clear H.
      induction lst.
      simpl in *.
      discriminate.
      simpl in *.
      case (s0 =? a) eqn:E2.
      discriminate.
      apply IHlst.
      exact E.
      exact E1.
    }
    2:{
      simpl.
      intros.
      rewrite IHm0_1.
      rewrite IHm0_2.
      reflexivity.
      exact H.
      exact H.
    }
    clear IHm0.
    clear s.
    assert (forall lst1 s lst2 m , varExists s lst2 = true -> sub_check_1 m (lst1 ++ [s] ++ lst2) = sub_check_1 m (lst1 ++ lst2)).
    {
      clear.
      intros.
      generalize dependent lst2.
      generalize dependent s.
      generalize dependent lst1.
      induction m.
      simpl.
      intros.
      induction lst1.
      simpl.
      case (String.eqb s0 s) eqn:E.
      rewrite String.eqb_eq in E.
      rewrite E in *.
      induction lst2.
      simpl in *.
      discriminate.
      simpl in *.
      case (s =? a) eqn:E1.
      rewrite String.eqb_eq in E1.
      rewrite E1 in *.
      rewrite String.eqb_refl.
      reflexivity.
      rewrite String.eqb_sym in E1.
      rewrite E1.
      apply IHlst2.
      apply H.
      reflexivity.
      simpl.
      rewrite IHlst1.
      reflexivity.
      simpl.
      intros.
      Open Scope list_scope.
      assert (forall lst3, s::lst1 ++ lst3 = (s::lst1) ++ lst3).
      {
        clear.
        intros.
        reflexivity.
      }
      rewrite H0.
      rewrite H0.
      apply IHm.
      apply H.
      simpl.
      intros.
      simpl in IHm1.
      simpl in IHm2.
      rewrite IHm1.
      rewrite IHm2.
      reflexivity.
      apply H.
      apply H.
    }
    assert (s0 :: lst = [] ++ [s0] ++ lst).
    {
      simpl.
      reflexivity.
    }
    rewrite H1.
    rewrite H0.
    simpl.
    reflexivity.
    apply E.    
  }
  apply H.
  simpl.
  reflexivity.
Qed.
  

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
  assert (forall m lst, is_uniq lst = true -> sub_check_1 m lst = checkRec m lst).
  {
    clear.
    induction m.
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
    apply H.
    discriminate.
    simpl.
    intros.
    unfold addToNameList.
    case (varExists s lst) eqn:E.
    rewrite IHm.
    assert (forall m s lst1 lst2 , varExists s lst2 = true -> checkRec m (lst1 ++ s::lst2) = checkRec m (lst1++lst2)).
    {
      clear.
      induction m.
      simpl.
      intros.
      induction lst1.
      simpl.
      case (String.eqb s s0) eqn:E1.
      rewrite String.eqb_eq in E1.
      rewrite E1 in *.
      rewrite H.
      reflexivity.
      reflexivity.
      simpl.
      rewrite IHlst1.
      reflexivity.
      simpl.
      unfold addToNameList.
      intros.
      case (varExists s (lst1 ++ s0 :: lst2)) eqn:E1.    
Abort.
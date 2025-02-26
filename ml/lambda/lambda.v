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




Fixpoint is_connect m :=
		match m with
		| V _ => false
		| C _ _ => true
		| P var lambda => is_connect lambda
    end.
	
	Fixpoint get_left (m: lambda) : lambda :=
		match m with
		| V _ => m
		| C l _ => l
		| P var lambda => P var (get_left lambda)
    end.
	
	Fixpoint get_right m :=
		match m with
		| V _ => m
		| C _ r => r
		| P var lambda => P var (get_right lambda)
    end.
(* 
Fixpoint check (m: lambda) : bool :=
	if is_connect m then (check (get_left m)) && (check (get_right m))
	else match m with
	| V _ => false
	| C l r => (check l) && (check r) 
	| P var lambda =>
		match lambda with
		| V s => if var=?s then true
					else false
		| C l r => (check (P var l)) && (check (P var r))
		| P var2 lambda2 => (check (P var lambda2)) || (check (P var2 lambda2))
    end
  end. *)


  Fixpoint ck (l:lambda) (lst : list string) : nat :=
  match l with
  |P va e => ck e (va::lst)
  |C ex1 ex2 => ck ex1 lst + ck ex2 lst
  |V (va) => if (is_mem_1 lst va) then 0 else 1 
  end.
  
  Definition sol530 (l:lambda) : bool :=  
     Nat.eqb (ck l []) 0 .
  
  Theorem ta1_sol530 : forall m, solution_1 m = sol530 m.
  Proof.
    assert (forall n1 n2, (andb (Nat.eqb n1 0)  (Nat.eqb n2 0)) =  Nat.eqb (n1 + n2) 0 ).
      {
        clear.
        induction n1.
        simpl.
        intros.
        reflexivity.
        simpl.
        reflexivity.
      }
    assert (forall m lst, sub_check_1 m lst  = (Nat.eqb (ck m lst) 0)).
    {
      induction m.
      simpl.
      induction lst.
      simpl.
      reflexivity.
      simpl.
      case (String.eqb a s) eqn:E.
      simpl.
      reflexivity.
      simpl.
      rewrite IHlst at 1.
      reflexivity.
      simpl.
      intros.
      rewrite IHm.
      reflexivity.
      simpl.
      intros.
      rewrite IHm1.
      rewrite IHm2.
      rewrite H.
      reflexivity.    
    }
    unfold sol530.
    unfold solution_1.
    induction m.
    simpl.
    reflexivity.
    simpl.
    apply H0.
    simpl.
    rewrite IHm1.
    rewrite IHm2.
    rewrite H.
    reflexivity.
  Qed.


  
Lemma sg109: forall m lst, sub_check_1 m lst = checkRec m (mk_addtonamelist lst).
Proof.
  induction m.
  simpl.
  induction lst.
  simpl.
  reflexivity.
  simpl.
  case (String.eqb a s) eqn:E.
  rewrite String.eqb_eq in E.
  rewrite E in *.
  unfold addToNameList.
  case (varExists s (mk_addtonamelist lst)) eqn:E1.
  rewrite E1.
  reflexivity.
  simpl.
  rewrite String.eqb_refl.
  reflexivity.
  rewrite IHlst.
  assert 

Abort.



    
Theorem ta1_sol109 : forall m, solution_1 m = sol109 m.
Proof.
  unfold solution_1.
  unfold sol109.
  intros.
  induction m.
  simpl.
  reflexivity.
  2:{simpl.
  rewrite IHm1.
  rewrite IHm2.
  reflexivity.
  }
  simpl.
  destruct m.
  simpl.
  case (String.eqb s s0) eqn:E.
  rewrite String.eqb_eq in E.
  rewrite E in *.
  rewrite String.eqb_refl.
  reflexivity.
  rewrite String.eqb_sym in E.
  rewrite E.
  reflexivity.
  simpl.
  
Qed.
  
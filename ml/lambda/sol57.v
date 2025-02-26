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


Fixpoint deleteAll (list_input : list string) (target : string) : list string :=
			match list_input with
			| l::remain_list => 
				if l =? target then deleteAll remain_list target
				else l::deleteAll remain_list target
			| [] => []
      end.

Fixpoint listStation (m_input : lambda) : list string :=
			match m_input with
			| V n => [n]
			| P n m => deleteAll (listStation m) n
			| C m1 m2 => (listStation m1) ++ (listStation m2)
      end.
Definition sol57 (lambda_input : lambda) := 
  match (listStation lambda_input) with
  | [] => true
  | _ => false
  end.

Fixpoint mk_deleteAll lst acc :=
  match lst with
  | hd::tl => mk_deleteAll tl (deleteAll acc hd)
  | [] => acc
  end.

  Open Scope list_scope.

Lemma sg57_0 : forall m lst, sub_check_1 m lst = match (mk_deleteAll lst (listStation m)) with | [] => true | _ => false end.
Proof.
  induction m.
  simpl.
  induction lst.
  simpl.
  reflexivity.
  simpl.
  case (String.eqb a s) eqn:E.
  rewrite String.eqb_sym in E.
  rewrite E.
  assert (mk_deleteAll lst [] = []).
  {
  clear.
  induction lst.
  simpl.
  reflexivity.
  simpl.
  apply IHlst.
  }
  rewrite H.
  reflexivity.
  rewrite String.eqb_sym in E.
  rewrite E.
  apply IHlst.
  simpl.
  assert (forall m s lst, mk_deleteAll lst (deleteAll (listStation m) s) = mk_deleteAll (s::lst) (listStation m)).
  {
    clear.
    simpl.
    reflexivity.
  }
  intros.
  rewrite H.
  apply IHm.
  simpl.
  intros.
  rewrite IHm1.
  rewrite IHm2.
  assert (forall lst lst1 lst2, mk_deleteAll lst (lst1 ++lst2) = (mk_deleteAll lst lst1) ++ (mk_deleteAll lst lst2) ).
  {
    clear.
    induction lst.
    simpl.
    reflexivity.
    simpl.
    intros.
    rewrite <- IHlst.
    assert (forall a lst1 lst2, deleteAll (lst1++lst2) a = deleteAll lst1 a ++ deleteAll lst2 a).
    {
      clear.
      induction lst1.
      simpl.
      reflexivity.
      simpl.
      intros.
      case (String.eqb a0 a) eqn:E.
      apply IHlst1.
      simpl.
      rewrite IHlst1.
      reflexivity.
    }
    rewrite H.
    reflexivity.
  }
  rewrite H.
  case (mk_deleteAll lst (listStation m1)) eqn:E.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

Theorem ta1_sol57 : forall m, solution_1 m = sol57 m.
Proof.
  unfold solution_1.
  unfold sol57.
  induction m.
  simpl.
  reflexivity.
  simpl.
  assert (deleteAll (listStation m) s = mk_deleteAll [s] (listStation m)).
  {
    clear.
    simpl.
    reflexivity.
  }
  rewrite H.
  apply sg57_0.
  simpl.
  rewrite IHm1.
  rewrite IHm2.
  case (listStation m1) eqn:E.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.
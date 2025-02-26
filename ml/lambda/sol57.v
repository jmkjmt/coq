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
Fixpoint valify (string_: string) (covers: lambda) : bool :=
  match covers with
  | V n => false
  | P (n) m_ => if n =? string_ then true else valify string_ m_
  | C (m1) (m2) => false
  end.

Fixpoint findStation (cur: lambda) (covers: lambda) : bool :=
  match cur with
  | V n => valify n covers
  | P (n) m_ => findStation m_ (P (n) covers)
  | C (m1) (m2) => (findStation m1 covers) && (findStation m2 covers)
  end.
Fixpoint mk_findstation lst :=
match lst with
| [] => V " "
| hd::tl => P hd (mk_findstation tl)
end.

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


Lemma sg57_0 : forall m lst, sub_check_1 m lst = match (mk_deleteAll lst (listStation m)) with | [] => true | _ => false end.
Proof.
  assert (forall lst , mk_deleteAll lst [] = []).
  {
    induction lst.
    simpl.
    reflexivity.
    simpl.
    apply IHlst.
  }
  induction m.
  simpl.
  induction lst.
  simpl.
  reflexivity.
  simpl.
  case (String.eqb a s) eqn:E.
  rewrite String.eqb_sym in E.
  rewrite E.
  2:{
    simpl.
    rewrite String.eqb_sym in E.
    rewrite E.
    apply IHlst.
  }
  2:{
    simpl.
    assert (forall lst, mk_deleteAll lst (deleteAll (listStation m) s) = mk_deleteAll (s::lst) (listStation m)).
    {
      clear.
      simpl.
      reflexivity.
    }
    intros.
    rewrite H0.
    apply IHm.
  }
  rewrite H.
  reflexivity.
  simpl.
  intros.
  rewrite IHm1.
  rewrite IHm2.
Abort.

Theorem ta1_sol57 : forall m, solution_1 m = sol57 m.
Proof.
  unfold solution_1.
  unfold sol57.
  induction m.
  simpl.
  reflexivity.
  simpl.
  destruct m.
  simpl.
  (* synthesize generalize term *)
  Abort.
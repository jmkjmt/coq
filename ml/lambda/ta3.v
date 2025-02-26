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



Fixpoint check_3 (ma: lambda) (li:list string) : bool :=
  match ma with
  | P st k => if mem st li then check_3 k li else check_3 k (st::li)
  | C me1 me2 => (check_3 me1 li) && (check_3 me2 li)
  | V na => mem na li
  end.

Definition solution_3 (m:lambda) : bool := check_3 m [].

Fixpoint mk_lst (v:string) (n:nat) : list string :=
match n with
| 0 => [v]
| S n' => v::(mk_lst v n')
end.
Lemma mem13 : forall v lst, is_mem_1 lst v = mem v lst.
Proof.
induction lst.
reflexivity.
simpl.
rewrite IHlst.
reflexivity.
Qed.
Lemma check_13 : forall m lst, sub_check_1 m lst = check_3 m lst.
Proof.
induction m.
simpl.
apply mem13.
simpl.
intros.
case (mem s lst) eqn:E.
rewrite <- IHm.
(*    
induction m.
simpl.
case (String.eqb v v0)eqn:E1.
rewrite String.eqb_eq in E1.
rewrite E1 in *.
rewrite <- E.
rewrite mem13.
reflexivity.
reflexivity.
simpl.
*)
assert (forall m v lst1 lst2, mem v lst1 = true -> sub_check_1 m (lst2++ v::lst1) = sub_check_1 m (lst2++lst1)).
{
  clear.
  induction m.
  simpl.
  intros.
  induction lst2.
  simpl.
  case (String.eqb v s) eqn:E.
  rewrite mem13.
  rewrite String.eqb_eq in E.
  rewrite E in *.
  rewrite H.
  reflexivity.
  reflexivity.
  simpl.
  case (String.eqb a s) eqn:E.
  reflexivity.
  rewrite IHlst2.
  reflexivity.
  simpl.
  intros.
  remember (v::lst2) as l.
  assert (s::lst2 ++ v::lst1 = (s::lst2) ++ v::lst1).
  reflexivity.
  rewrite H0.
  assert (s::lst2 ++ lst1 = (s::lst2) ++ lst1).
  reflexivity.
  rewrite H1.
  apply IHm.
  apply H.
  intros.
  simpl.
  assert (sub_check_1 m1 (lst2 ++ v :: lst1) = sub_check_1 m1 (lst2 ++ lst1)).
  {
    apply IHm1.
    apply H.
  }
  assert (sub_check_1 m2 (lst2 ++ v :: lst1) = sub_check_1 m2 (lst2 ++ lst1)).
  {
    apply IHm2.
    apply H.
  }
  rewrite H0.
  rewrite H1.
  reflexivity.    
}
specialize (H m s lst []).
simpl in H.
apply H.
apply E.
apply IHm.
intros.
simpl.
rewrite IHm1.
rewrite IHm2.
reflexivity.
Qed.

Theorem eq3: forall (m: lambda), solution_1 m = solution_3 m.
Proof.
unfold solution_1.
unfold solution_3.
intros.
rewrite check_13.
reflexivity.
Qed.
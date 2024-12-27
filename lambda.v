Require Import String.
Require Import List.
Import ListNotations.

Definition var := string.
Inductive lambda : Type :=
| V : var -> lambda
| P : var -> lambda -> lambda
| C : lambda -> lambda -> lambda.


Fixpoint is_mem_1 variables var : bool :=
match variables with
| nil => false
| hd::tl => if String.eqb hd var then true else is_mem_1 tl var
end.

Fixpoint sub_check_1 lambda vars : bool :=
match lambda with
| V x => is_mem_1 vars x
| P x e => sub_check_1 e (x::vars)
| C e1 e2 => (sub_check_1 e1 vars) && (sub_check_1 e2 vars)
end.

Definition solution_1 (lambda:lambda) : bool := sub_check_1 lambda [].

Fixpoint mem (v:var) (l:list var) : bool :=
  match l with
  | [] => false
  | hd::tl => if String.eqb hd v then true else mem v tl
  end.

Fixpoint check_2 (ma:lambda) (lst : list var) : bool :=
  match ma with
  | V x => mem x lst
  | P x e => check_2 e (x::lst)
  | C e1 e2 => (check_2 e1 lst) && (check_2 e2 lst)
  end.
Definition solution_2 (m: lambda) : bool :=
  match m with
  | V x => false
  | P x e => check_2 e [x]
  | C e1 e2 => check_2 e1 [] && check_2 e2 []
  end.

Fixpoint check_3 (ma: lambda) (li:list var) : bool :=
  match ma with
  | P st k => if mem st li then check_3 k li else check_3 k (st::li)
  | C me1 me2 => (check_3 me1 li) && (check_3 me2 li)
  | V na => mem na li
  end.

Definition solution_3 (m:lambda) : bool := check_3 m [].

Fixpoint exist (p : var -> bool) (l : list var) : bool :=
  match l with
  | [] => false
  | hd::tl => p hd || exist p tl
  end.
Fixpoint check_4 (ma: lambda) (li:list var) : bool :=
  match ma with
  | P st k => check_4 k (st::li)
  | C me1 me2 => (check_4 me1 li) && (check_4 me2 li)
  | V na => exist (fun x => String.eqb x na) li
  end.
Definition solution_4 (m : lambda) : bool :=
  match m with
  | P st k => check_4 k [st]
  | C me1 me2 => check_4 me1 [] && check_4 me2 []
  | V na => false
  end.

 

Theorem eq1 : forall (m : lambda), solution_1 m = solution_2 m.
Proof.
  assert(lemma1: forall m l, sub_check_1 m l = check_2 m l).
  { 
    induction m.
    simpl.
    induction l.
    simpl.
    reflexivity.
    simpl.
    rewrite IHl.
    reflexivity.
    simpl.
    intros l.
    rewrite IHm.
    reflexivity.
    intros l.
    simpl.
    rewrite IHm1.
    rewrite IHm2.
    reflexivity.
  }
  induction m.
  reflexivity.  
  unfold solution_1.
  simpl.
  apply lemma1.
  unfold solution_1.
  simpl.
  unfold solution_1 in *.
  rewrite lemma1 in *.
  rewrite lemma1.
  reflexivity.
  Qed.
  
Theorem eq2 : forall (m : lambda), solution_1 m = solution_4 m.
Proof.
  assert (lemma1: forall m lst, sub_check_1 m lst = check_4 m lst).
  {
    induction m.
    intros lst.
    simpl.
    induction lst.
    simpl.
    reflexivity.
    simpl.
    case (String.eqb a v) eqn :eq.
    reflexivity.
    simpl.
    rewrite IHlst.
    reflexivity.
    intros.
    simpl.
    rewrite IHm.
    reflexivity.
    simpl.
    intros.
    rewrite IHm1.
    rewrite IHm2.
    reflexivity.
  }
  induction m.
  unfold solution_1.
  reflexivity.
  unfold solution_1.
  simpl.  
  apply lemma1.
  unfold solution_1.
  simpl.
  rewrite lemma1.
  rewrite lemma1.
  reflexivity.
Qed.
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
  case (mem v lst) eqn:E.
  rewrite <- IHm.
  assert (forall m v lst1 lst2, mem v lst1 = true -> sub_check_1 m (lst2++ v::lst1) = sub_check_1 m (lst2++lst1)).
  {
    clear.
    induction m.
    simpl.
    intros.
    induction lst2.
    simpl.
    case (String.eqb v0 v) eqn:E.
    rewrite mem13.
    rewrite String.eqb_eq in E.
    rewrite E in *.
    rewrite H.
    reflexivity.
    reflexivity.
    simpl.
    case (String.eqb a v) eqn:E.
    reflexivity.
    rewrite IHlst2.
    reflexivity.
    simpl.
    intros.
    remember (v::lst2) as l.
    assert (v::lst2 ++ v0::lst1 = (v::lst2) ++ v0::lst1).
    reflexivity.
    rewrite H0.
    assert (v::lst2 ++ lst1 = (v::lst2) ++ lst1).
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
  specialize (H m v lst []).
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
  induction m.
  unfold solution_1.
  unfold solution_3.
  reflexivity.
  unfold solution_1.
  unfold solution_3.
  simpl.
  induction m.
  simpl.
  reflexivity.
  simpl.
  case (v=?v0) eqn:E.
  rewrite String.eqb_eq in E.
  rewrite E in *.
  assert (forall m v n, sub_check_1 m (mk_lst v n) = check_3 m [v]).
  {
    clear.
    induction n.
    simpl.
    
  
  }
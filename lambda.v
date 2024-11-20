Require Import String.
Require Import List.
Import ListNotations.
Open Scope string_scope.

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
| C e1 e2 => andb (sub_check_1 e1 vars) (sub_check_1 e2 vars)
end.

Definition solution_1 (lambda:lambda) : bool := sub_check_1 lambda [].

Fixpoint mem (v:var) (l:list var) : bool :=
  match l with
  | [] => false
  | hd::tl => if String.eqb hd v then true else mem v tl
  end.

Fixpoint check_2 (ma:lambda) (li : list var) : bool :=
  match ma with
  | P st k => check_2 k (st::li)
  | C me1 me2 => (check_2 me1 li) && (check_2 me2 li)
  | V na => mem na li
  end.
Definition solution_2 (m: lambda) : bool :=
  match m with
  | P st k => check_2 k [st]
  | C me1 me2 => check_2 me1 [] && check_2 me2 []
  | V na => false
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

Lemma l1 : forall m v, sub_check_1 m [v] = check_2 m [v].
Proof.
  induction m.
  reflexivity.
  simpl.
  intros.
  

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

  





  

  

  
  





  



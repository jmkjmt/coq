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


Fixpoint exist (p : string -> bool) (l : list string) : bool :=
  match l with
  | [] => false
  | hd::tl => p hd || exist p tl
  end.
Fixpoint check_4 (ma: lambda) (li:list string) : bool :=
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
    case (String.eqb a s) eqn :eq.
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

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


Fixpoint mem (v:string) (l:list string) : bool :=
  match l with
  | [] => false
  | hd::tl => if String.eqb hd v then true else mem v tl
  end.

Fixpoint check_2 (ma:lambda) (lst : list string) : bool :=
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
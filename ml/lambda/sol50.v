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

Definition sol50 m := findStation m (V (" " : string)).


Theorem ta1_sol50 : forall m, solution_1 m = sol50 m.
Proof.
  assert (forall s lst, mk_findstation (s::lst) = P s (mk_findstation lst)).
    {
      simpl.
      reflexivity.
    }
  assert (forall m lst, sub_check_1 m lst = findStation m (mk_findstation lst)).
  {
    induction m.
    simpl.
    induction lst.
    simpl.
    reflexivity.
    simpl.
    rewrite IHlst.
    reflexivity.
    simpl.
    intros.
    rewrite <- H.
    apply IHm.
    simpl.
    intros.
    rewrite IHm1.
    rewrite IHm2.
    reflexivity.
    }
  unfold solution_1.
  unfold sol50.
  induction m.
  unfold findStation.
  unfold valify.
  simpl sub_check_1.
  reflexivity.
  2:{
    simpl.
    rewrite IHm1.
    rewrite IHm2.
    reflexivity.
  }
  simpl.
  rewrite H0.
  simpl.
  reflexivity.
Qed.
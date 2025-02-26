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

Fixpoint check_ (m:lambda) (al : list string) (nl : list string) : bool :=
  match m with
  | V n => List.forallb (fun x => is_mem_1 al x) (n::nl)
  | P (n) m_ => check_ m_ (n::al) nl
  | C (m1) (m2) => (check_ m1 al nl) && (check_ m2 al nl)
  end.

Definition sol101 (m : lambda) := check_ m [] [].

Theorem ta1_sol101 : forall m, solution_1 m = sol101 m.
Proof.
  unfold solution_1.
  unfold sol101.
  induction m.
  simpl.
  reflexivity.
  2:{
    simpl.
    rewrite IHm1.
    rewrite IHm2.
    reflexivity.
  }
  simpl.
  assert (forall m lst, sub_check_1 m lst = check_ m lst []).
  {
    clear.
    intros.
    generalize dependent lst.
    induction m.
    simpl.
    intros.
    case (is_mem_1 lst s).
    reflexivity.
    reflexivity.
    intros.
    simpl.
    apply IHm.
    simpl.
    intros.
    rewrite IHm1.
    rewrite IHm2.
    reflexivity.
  }
  apply H.
Qed.

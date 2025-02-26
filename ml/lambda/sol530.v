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

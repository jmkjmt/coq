Require Import Arith.
Require Import String.
Require Import Ascii.
Require Import Bool.
Require Import List.
Import ListNotations.
Open Scope list_scope.

Module Export StringSyntax. End StringSyntax.

Definition var := string.
Inductive lambda : Type :=
| V : var -> lambda
| P : var -> lambda -> lambda
| C : lambda -> lambda -> lambda.

Check lambda_sind.
Check lambda_rect.
Check lambda_ind.
Check lambda_rec.

Fixpoint is_mem (variables: list var) (var:var) : bool :=
match variables with
| [] => false
| hd::tl => if String.eqb hd var then true else is_mem tl var
end.

Fixpoint sub_check (lambda:lambda) (vars: list var) : bool :=
match lambda with
| V x => is_mem vars x
| P x e => sub_check e (x::vars)
| C e1 e2 => (sub_check e1 vars) && (sub_check e2 vars)
end.

Definition check_ref (lambda:lambda) : bool := sub_check lambda [].

Fixpoint checkStation (v :var) (variables: list var) : list var :=
  match variables with
  | [] => []
  | hd::tl =>
      if String.eqb hd v then checkStation v tl
      else hd :: checkStation v tl
  end.

Fixpoint isInArea (lambda:lambda) (vars: list var) : list var :=
match lambda with
| V x => x::vars
| P x e => checkStation x (isInArea e vars)
| C e1 e2 => (isInArea e1 vars) ++ (isInArea e2 vars)
end.
Open Scope list_scope.
Definition check_sub (lambda:lambda) : bool :=
let result := (isInArea lambda []) in
match result with
| [] => true
| hd::tl => false
end.


Theorem eq: forall l: lambda, check_ref l = check_sub l.
Proof.
  intros.
  unfold check_ref.
  unfold check_sub.
  destruct (isInArea l []) eqn:H.
  induction l.
  simpl in H.
  discriminate.
  simpl.
  simpl in H.
  case (isInArea l) eqn : H1.
  Check (isInArea l []).
  

  
  





  



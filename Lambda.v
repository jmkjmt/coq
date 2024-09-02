Require Import Arith.
Require Import String.
Require Import Ascii.
Require Import Bool.
Require Import List.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Module Export StringSyntax. End StringSyntax.
Print String.eqb.
Definition var := string.
Inductive lambda : Type :=
| V : var -> lambda
| P : var * lambda -> lambda
| C : lambda * lambda -> lambda.


Fixpoint is_mem (variables: list var) (var:var) : bool :=
match variables with
| [] => false
| hd::tl => if hd =? var then true else is_mem tl var
end.

Fixpoint sub_check (lambda:lambda) (vars: list var) : bool :=
match lambda with
| V x => is_mem vars x
| P (x, e) => sub_check e (x::vars)
| C (e1, e2) => (sub_check e1 vars) && (sub_check e2 vars)
end.

Definition check_ref (lambda:lambda) : bool := sub_check lambda [].

Fixpoint checkStation (m :var) (lst: list var) : list var :=
  match lst with
  | [] => []
  | hd::tl =>
      if hd =? m then checkStation m tl
      else hd :: checkStation m tl
  end.

Fixpoint isInArea (met:lambda) (lst: list var) : list var :=
match met with
| V var => var::lst
| P (var, mtro) => checkStation var (isInArea mtro lst)
| C (met1, met2) => (isInArea met1 lst) ++ (isInArea met2 lst)
end.

Definition check_sub (lambda: lambda) : bool := 
let result := (isInArea lambda []) in
match result with
| [] => true
| hd::tl => false
end.

  
  
Theorem eq: forall l: lambda, check_sub l = check_ref l.
Proof.
  
  

  



  
  
  
  
  


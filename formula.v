Require Import ZArith.
Require Import Recdef.
Require Import Bool.
Open Scope Z_scope.

Inductive exp : Type :=
| Num : Z -> exp
| Plus : exp -> exp -> exp
| Minus : exp -> exp -> exp.
Inductive formula : Type :=
| _True
| _False
| Not : formula -> formula
| AndAlso : formula -> formula -> formula
| OrElse : formula -> formula -> formula
| Imply : formula -> formula -> formula
| Equal : exp -> exp -> formula.

Fixpoint exp_eval (exp:exp) : Z :=
match exp with
| Num n => n
| Plus e1 e2 => (exp_eval e1) + (exp_eval e2)
| Minus e1 e2 => (exp_eval e1) - (exp_eval e2)
end.


Fixpoint eval (f:formula): bool :=
match f with
| _True => true
| _False => false
| Not f => negb (eval f)
| AndAlso f1 f2 => (eval f1) && (eval f2)
| OrElse f1 f2 => (eval f1) || (eval f2)
| Imply f1 f2 => (negb (eval f1)) || (eval f2)
| Equal e1 e2 => Z.eqb (exp_eval e1)  (exp_eval e2)
end.

Fixpoint evall (exp:exp) : Z :=
match exp with
| Num a => a
| Plus a b => evall(a)+evall(b)
| Minus a b => evall(a)-evall(b)
end.

Fixpoint eval_sub (f : formula) : bool :=
  match f with
  | _True => true
  | _False => false
  | Not a => if (eval_sub a) then false else true
  | AndAlso a b => (eval_sub a) && (eval_sub b)
  | OrElse a b => (eval_sub a) || (eval_sub b)
  | Imply a b => eval_sub (Not (AndAlso a (Not b)))
  | Equal a b => if (Z.eqb (evall a) (evall b)) then true else false
  end.
    
    
       

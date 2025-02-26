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




Fixpoint is_connect m :=
		match m with
		| V _ => false
		| C _ _ => true
		| P var lambda => is_connect lambda
    end.
	
	Fixpoint get_left (m: lambda) : lambda :=
		match m with
		| V _ => m
		| C l _ => l
		| P var lambda => P var (get_left lambda)
    end.
	
	Fixpoint get_right m :=
		match m with
		| V _ => m
		| C _ r => r
		| P var lambda => P var (get_right lambda)
    end.
(* 
Fixpoint check (m: lambda) : bool :=
	if is_connect m then (check (get_left m)) && (check (get_right m))
	else match m with
	| V _ => false
	| C l r => (check l) && (check r) 
	| P var lambda =>
		match lambda with
		| V s => if var=?s then true
					else false
		| C l r => (check (P var l)) && (check (P var r))
		| P var2 lambda2 => (check (P var lambda2)) || (check (P var2 lambda2))
    end
  end. *)
(*2009-11718 1-8*)
Require Import Arith.
Require Import Ascii.
Require Import Bool.
Require Import List.
Module Export StringSyntax. End StringSyntax.

Inductive lambda : Type :=
 V: string -> lambda
 | P : string*lambda -> lambda
 | C : lambda * lambda -> lambda.

Fixpoint checkStation (m : lambda, lst : )

(* type lambda = V of var
			| P of var * lambda
			| C of lambda * lambda
	and var = string

let rec checkStation (m, lst) =
	match lst with
	| [] -> []
	| hd::tl -> (if hd=m then (checkStation (m, tl))
				else hd::(checkStation (m, tl)))

let rec check lambda =
	let rec isInArea met lst =
	match met with
	| V var -> var::lst
	| P (var, mtro) -> checkStation(var, (isInArea mtro lst))
	| C (met1, met2) -> (isInArea met1 lst)@(isInArea met2 lst)	in

	if (isInArea lambda [])=[] then
	true
	else false *)


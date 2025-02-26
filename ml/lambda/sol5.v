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


Fixpoint getStn (m: lambda) : list string :=
  match m with
  | V string => [string]
  | P (n) m' => List.filter (fun x => negb (String.eqb x n)) (getStn m')
  | C (m1) (m2) => (getStn m1) ++ (getStn m2)
  end.

Definition sol5 (m: lambda) : bool :=
  match getStn m with
  | [] => true
  | _ => false
  end.

Fixpoint mk_filter lst m :=
match lst with
| [] => getStn m
| hd::tl => filter (fun x => negb (String.eqb x hd)) (mk_filter tl m)
end.
(* Lemma sg5_0 : forall x l lst, mk_filter lst (V x) = mk_filter (lst ++ [x]) []. *)

Lemma sg5_1 : forall x l lst, mk_filter lst (P x l) = mk_filter (lst ++ [x]) l.
Proof.
  induction lst.
  simpl.
  reflexivity.
  simpl.
  rewrite IHlst.
  reflexivity.
Qed.



Theorem ta1_sol5 : forall m, solution_1 m = sol5 m.
Proof.
  unfold sol5.
  unfold solution_1.
  induction m.
  simpl.
  reflexivity.
  simpl.
  2:{
    simpl.
    rewrite IHm1.
    rewrite IHm2.
    destruct (getStn m1).
    simpl.
    reflexivity.
    simpl.
    reflexivity.
  }
  destruct m.
  simpl.
  case (String.eqb s s0) eqn:E.
  rewrite String.eqb_eq in E.
  rewrite E in *.
  rewrite String.eqb_refl.
  simpl.
  reflexivity.
  rewrite String.eqb_sym in E.
  rewrite E.
  simpl.
  reflexivity.
  simpl.
  (* synthesize generalize form *)
  Abort.
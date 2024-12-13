Require Import Program Arith ZArith Lia.

 (* Fixpoint solution_1 (f: nat -> nat) (c a: nat) {struct a}: nat :=
  match c with
  | 0 => f a
  | _ => f a + solution_1 f (c + a - 1) (a + 1)
  end.

  Next Obligation.
  Proof. 
     auto with *.
    Qed. *)

Unset Guard Checking.

CoFixpoint solution_1 (f: Z -> Z) (a b: Z): Z :=
  if Z.ltb b a then 0
  else if Z.eqb a b then f a
  else f a + solution_1 f (a + 1) b.

CoFixpoint solution_2 (f: Z -> Z) (a b : Z) : Z :=
    if (Z.ltb b a) then 0 
    else if Z.eqb a b then f b
    else (f b) + solution_2 f a (b-1).

 

(* Program Fixpoint solution_2 (f: nat -> nat) (a: nat) (b : nat) {measure (b - a)}: nat :=
    match b - a with
    | 0 => f b
    | _ => f b + solution_2 f a (b-1)
    end. *)

Open Scope Z_scope.

Theorem eq: forall f a b, a <= b -> solution_1 f a b = solution_2 f a b.
Proof.
    intros.
    pose (c := b - a).
    assert (H1: b = a + c).
    { 
        unfold c.
        assert (H2:= Z.add_sub_assoc).
        specialize H2 with a b a.
        rewrite H2.
        assert (H3:= Z.add_sub_swap).
        specialize H3 with a b a.
        rewrite H3.
        lia.
     }
    rewrite H1.
    induction c.
    rewrite Z.add_0_r in *.
    unfold solution_1.
    unfold solution_1.
    Eval compute in solution_1 f a a.
    
    
    


Program Fixpoint aux (a:nat) (b:nat) (f:nat->nat) (acc:nat) : nat :=
if (Nat.ltb b a) then acc else aux (a+1) b f (acc + (f a))
.

Fixpoint solution_3 (f: nat -> nat) (a: nat) (b : nat) : nat :=
aux a b f 0
.
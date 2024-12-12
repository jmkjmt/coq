Require Import Program Arith ZArith Lia.
 (* Program Fixpoint solution_1 (f: Z -> Z) (a b: Z) {measure (Z.to_nat (b-a + 1))}: Z :=
  if Z.ltb b a then 0
  else if Z.eqb a b then f a
  else f a + solution_1 f (a + 1) b.

  Next Obligation.
  Proof. 
    intros.
    apply Z2Nat.inj_lt.
    Open Scope Z_scope.
    -   *)
  
 Program Fixpoint solution_1 (f: nat -> nat) (a b: nat) {measure (b - a)}: nat :=
  match b - a with
  | 0 => f a
  | _ => f a + solution_1 f (a+1) b
  end.

  Next Obligation.
  Proof. 
     auto with *.
    Qed.


(* Program Fixpoint solution_2 (f: nat -> nat) (a b : nat) {measure (b-a)} : nat :=
    if (Nat.ltb b a) then 0 
    else (f b) + solution_2 f a (b-1).
  *)

Program Fixpoint solution_2 (f: nat -> nat) (a: nat) (b : nat) {measure (b - a)}: nat :=
    match b - a with
    | 0 => f b
    | _ => f b + solution_2 f a (b-1)
    end.
Next Obligation.
Proof.
    auto with *.
Qed.

Theorem eq: forall f a b, a <= b -> solution_1 f a b = solution_2 f a b.
Proof.
    intro f.
    intros.
    pose (c := b - a).
    assert (H1: b = a + c).
    { 
        unfold c.
        assert (H2:= Nat.add_sub_assoc).
        specialize H2 with a b a.
        rewrite H2.
        assert (H3:= Nat.add_sub_swap).
        specialize H3 with a b a.
        rewrite H3.
        lia.
        lia.
        apply H.
     }
    rewrite H1.
    induction c.
    rewrite Nat.add_0_r.
    


Program Fixpoint aux (a:nat) (b:nat) (f:nat->nat) (acc:nat) : nat :=
if (Nat.ltb b a) then acc else aux (a+1) b f (acc + (f a))
.

Fixpoint solution_3 (f: nat -> nat) (a: nat) (b : nat) : nat :=
aux a b f 0
.
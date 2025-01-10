Require Import Program Arith ZArith Lia.


(* Fixpoint ta1 (f: nat -> nat) (a b : nat) : nat :=
  if a <? b then 0
  else if a =? b then f a
  else f a + ta1 f (a + 1) b. *)
  
Program Fixpoint solution_1 (f: Z -> Z) (a b: Z) {measure 0}: Z :=
  if Z.ltb b a then 0
  else if Z.eqb a b then f a
  else f a + solution_1 f (a + 1) b.
Next Obligation.
  Admitted.

Program Fixpoint solution_2 (f: Z -> Z) (a b : Z) {measure 0}: Z :=
    if (Z.ltb b a) then 0 
    else if Z.eqb a b then f b
    else (f b) + solution_2 f a (b-1).
Next Obligation.
    Admitted.

Open Scope Z_scope.

Theorem eq: forall f a b, a <= b -> solution_1 f a b = solution_2 f a b.
Proof.
  intros.
  pose (c:= Z.to_nat (b - a)).
  assert (b = a + Z.of_nat c) by lia.
  rewrite H0.
  generalize dependent a.
  induction c.
  intros.
  simpl in *.
  rewrite Z.add_0_r in *.
  cbn.
  rewrite Z.ltb_irrefl.
  rewrite Z.eqb_refl.
  reflexivity.
  intros.
  unfold solution_1.
  unfold solution_2.
  unfold solution_1_func.
  unfold solution_2_func.
  simpl.
  cbn.
  Search (_ + _ < _).
  assert (forall a, Z.pos a > 0).
  {
    intros.
    lia.
  }
  assert (forall a b, b > 0 -> a <= a + b).
  {
    intros.
    lia.
  }
  assert (a + Z.pos (Pos.of_succ_nat c) <? a = false).
  {
    Search (_ <? _ = false).
    apply Z.ltb_ge.
    apply H2.
    apply H1.
  }
  rewrite H3.
  assert(forall a c, a =? a +Z.pos c = false).
  {
    intros.
    apply Z.eqb_neq.
    lia.
  }
  rewrite H4.
  Search (Fix_F_sub).
  rewrite F_unfold in *.
  
    
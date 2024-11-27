Require Import Arith ZArith List Bool String.
Definition int : Type := Z.
Inductive natural : Type :=
  | ZERO : natural
  | SUCC : natural -> natural.
Fixpoint natadd n1 n2 :=
  match n1 with
  | ZERO => n2
  | SUCC n => SUCC (natadd n n2)
  end.
Fixpoint natadd_sub n1 n2 :=
  match n1 with
  | ZERO => n2
  | SUCC n => natadd_sub n (SUCC n2)
  end.
Theorem equiv : forall arg0 arg1, natadd arg0 arg1 = natadd_sub arg0 arg1.
Proof.
(induction arg0).
(simpl in *).
reflexivity.
(simpl in *).
(intros arg1).
(simpl in *).
(rewrite <- IHarg0 in *).
(simpl in *).
(assert (forall arg0_, SUCC (natadd arg0_ arg1) = natadd arg0_ (SUCC arg1))).
(induction arg0_).
(simpl in *).
reflexivity.
(simpl in *).
(rewrite <- IHarg0_ in *).
(simpl in *).
reflexivity.
(simpl in *).
(rewrite <- H in *).
(simpl in *).
reflexivity.
Qed.
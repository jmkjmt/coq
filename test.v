Require Import Prelude.

Inductive natural : Type :=
 ZERO : natural
| SUCC : natural -> natural.

Fixpoint natadd n1 n2 :=
  match n1 with
   ZERO => n2
  | SUCC n => SUCC (natadd n n2)
  end.
Fixpoint natadd_ref n1 n2 :=
match n1 with
| ZERO => n2
| SUCC ZERO => SUCC n2
| SUCC n => SUCC (natadd_ref n n2)
end.
Fixpoint natadd2 n1 n2 :=
  match n1 with
   ZERO => n2
  | SUCC n =>  natadd2 n (SUCC n2)
  end.
Theorem equal : forall arg0 arg1, natadd arg0 arg1 = natadd_ref arg0 arg1.
Proof.
  induction arg0.
  simpl.
  reflexivity.
  simpl.
  intros.
  case arg0 eqn:H.
  simpl.
  reflexivity.
  simpl in *.
  simpl in IHarg0.
  rewrite IHarg0.
  reflexivity.
  Qed.

Theorem test: forall arg0 arg1, natadd arg0 arg1 = natadd_ref arg0 arg1.
Proof.
(induction arg0).
(simpl in *).
reflexivity.
(simpl in *).
(intros arg1).
(simpl in *).
(rewrite <- IHarg0 in *).
(simpl in *).
(destruct (arg0) eqn:arg0case).
(simpl in *).
reflexivity.
(simpl in *).
reflexivity.
Qed.

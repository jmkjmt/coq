Inductive natural : Type :=
 ZERO : natural
| SUCC : natural -> natural.

Fixpoint natadd1 (n1 n2 : natural) : natural :=
  match n1 with
   ZERO => n2
  | SUCC n => SUCC (natadd1 n n2)
  end.

Fixpoint oneadd (n1 : natural) : natural :=
  match n1 with
   ZERO => ZERO
  | SUCC (n) => SUCC (oneadd n)
  end.

Fixpoint natadd2 (n1 n2 : natural) : natural :=
  match n1 with
  | ZERO => oneadd n2
  | SUCC n => natadd2 n (SUCC n2)
  end.

Fixpoint natadd3 (n1 n2 : natural) : natural :=
  match n2 with
  | ZERO => n1
  | SUCC n => SUCC (natadd3 n1 n)
  end.

Lemma first : forall n: natural, n = oneadd n.
Proof.
  induction n.
  reflexivity.
  simpl.
  rewrite <- IHn.
  reflexivity.
  Qed.

Lemma second: forall n1 n2, SUCC (natadd2 n1 n2) = natadd2 n1 (SUCC n2).
Proof.
  induction n1.
  simpl.
  reflexivity.
  simpl.
  intros n2.
  apply IHn1.
  Qed.

Theorem eq : forall n1 n2, natadd1 n1 n2 = natadd2 n1 n2.
Proof.
  induction n1.
  simpl.
  apply first.
  simpl.
  intros n2.
  rewrite IHn1.
  apply second.
  Qed.

  
Theorem eq2: forall n1 n2, natadd1 n1 n2 = natadd3 n1 n2.
Proof.
  induction n1.
  simpl.
  induction n2.
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHn2.
  reflexivity.
  induction n2.
  simpl.
  rewrite IHn1.
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHn2.
  simpl.
  rewrite IHn1.
  rewrite IHn1.
  simpl.
  reflexivity.
  Qed.


(* Lemma example2 : forall a b:Prop, a /\ b -> b /\ a.

Proof.
intros a b H.
split.
destruct H as [H1 H2].
exact H2.
intuition.
Qed. *)





  (* Proof goes here using induction on n1 *)

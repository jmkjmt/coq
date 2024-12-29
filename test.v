Inductive natural : Type :=
  ZERO : natural
| SUCC : natural -> natural.

Fixpoint natadd1 n1 n2 :=
match n1 with
ZERO => n2
| SUCC n => SUCC (natadd1 n n2)
end.

Fixpoint natadd2 n1 n2 :=
match n2 with
| ZERO => n1
| SUCC n => SUCC (natadd2 n1 n)
end.


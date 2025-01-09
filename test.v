Require Import Arith.
Open Scope nat_scope.

Require Import List.
Import ListNotations.

Fixpoint max (lst : list nat): nat :=
match lst with
| [] => 0
| [hd] => hd
| hd::tl =>  if (max tl) <? hd then hd else max tl
end.

Fixpoint max2 lst :=
match lst with
| [] => 0
| hd::tl => if (length lst) =? 1 then hd else 
  let a := max2 tl in
  if a <? hd then hd else a
end. 
Theorem max1_eq_max : forall l, max l = max2 l.
Proof.
  induction l.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl.
  case l.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.
  
  
Print Nat.sub.
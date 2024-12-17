Require Import Bool Arith Program.

Open Scope nat_scope.
Inductive List : Type :=
| Elt : nat -> List
| Cons : nat -> List -> List.
Inductive CList : Type :=
| Single : nat -> CList
| Concat : CList -> CList -> CList.

Definition max n m := if m <? n then n else m.

Inductive Tuple3 : Type := MakeTuple3 : nat -> nat -> Tuple3.

Definition fst3 tup3 :=
match tup3 with
| MakeTuple3 x y => x end.

Fixpoint plus n m :=
match n with
| 0 => m
| S n' => S (plus n' m)
end.

Definition snd3 tup3 := match tup3 with | MakeTuple3 x y => y end.

Fixpoint tf1 lst : Tuple3 :=
match lst with
| Elt n => MakeTuple3 n (S 0)
| Cons hd tl => MakeTuple3 (max (fst3 (tf1 tl)) hd) (if (fst3 (tf1 tl)) <? hd then (S 0) else (plus (snd3 (tf1 tl)) (if negb (hd =? (fst3 (tf1 tl))) then (S 0) else 0)))
end.

Definition spec lst := snd3 (tf1 lst).

Fixpoint len lst := match lst with | Elt n => 1 | Cons hd tl => S (len tl) end.
Program Fixpoint tf3 lst1 lst2 {measure (len(lst1) + (len(lst2)))}:=
match lst2 with
| Elt n => Cons n lst1
| Cons hd tl => Cons hd (tf3 tl lst1)
end.
Next Obligation.
Proof.
    simpl.
    simpl in tf3.
    rewrite Nat.add_comm.
    rewrite <- Nat.add_lt_mono_l.
    apply Nat.lt_succ_diag_r.
Qed.
Definition cat lst1 lst2 := tf3 lst1 lst2.

Fixpoint tf5 clst :=
match clst with
| Single n => Elt n
| Concat cl1 cl2 => cat (tf5 cl1) (tf5 cl2)
end.

Definition repr clst := tf5 clst.

Definition main clst := spec (repr clst).

Fixpoint tf7 clst :=
match clst with
| Single n => MakeTuple3 (S 0) n
| Concat cl1 cl2 => MakeTuple3 (if negb ((snd3 (tf7 cl2)) =? (snd3 (tf7 cl1))) then (plus (fst3 (tf7 cl2)) (fst3 (tf7 cl1))) else (if (snd3 (tf7 cl2)) <? (snd3 (tf7 cl1)) then (fst3 (tf7 cl1)) else (fst3 (tf7 cl2)))) (max (snd3 (tf7 cl2)) (snd3 (tf7 cl1)))
end.

Definition reprNew clst := tf7 clst.

Definition mainNew clst := fst3 (reprNew clst).

Lemma l1 : forall x1 x2, snd3 (tf1 (tf3 (x1) (tf5 x2))) = snd3 (tf1 (tf5 x2)).
Proof.
    intros.
    generalize dependent x1.
    induction x2.
    simpl.
    induction x1.
    simpl.
    case (n0 <? n) eqn:E1.
    reflexivity.
    case (n =? n0) eqn:E2.
    simpl.
    reflexivity.
    simpl.
    

Theorem theorem : forall (x : CList), main x = mainNew x.
Proof.
    unfold main.
    unfold mainNew.
    unfold spec.
    unfold repr.
    unfold reprNew.
    induction x.
    simpl.
    reflexivity.
    simpl.
    unfold cat.
    case (snd3 (tf7 x2) =? snd3 (tf7 x1)) eqn:E.
    simpl.
    rewrite Nat.eqb_eq in E.
    rewrite E.
    Search (_ <? _).
    rewrite Nat.ltb_irrefl.
    rewrite <- IHx2.
    
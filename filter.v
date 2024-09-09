Require Import ZArith.
Require Import List.
Require Import Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint solution (pred:Z -> bool) (lst:list Z) : list Z :=
    match lst with
    | [] => []
    | hd::tl => if pred hd then hd :: solution pred tl else solution pred tl
    end.

Definition filter_sub (pred:Z -> bool) (lst: list Z) : list Z :=
    let fix aux (i:Z) (l :list Z) : list Z :=
    match l with
    | [] => []
    | hd::tl => if pred hd then hd:: aux (i+1) tl else aux(i+1) tl
    end in
    aux 1 lst.
  
Lemma list_eq_tail : forall (a : nat) (b c : list nat),
  a :: b = a :: c -> b = c.
Proof.
  intros a b c H.
  injection H as H1.
  exact H1.
Qed.







Theorem eq : forall pred lst, solution pred lst = filter_sub pred lst.
Proof.
    intros.
    unfold filter_sub.
    induction lst.
    simpl.
    reflexivity.
    simpl.
    case (pred a).
    rewrite IHlst.
    
    Search (_::_ ).

    
    
    

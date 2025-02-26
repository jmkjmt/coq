Require Import Arith.
Require Import List.
Require Import Bool Program.
Import ListNotations.
Fixpoint remove_elem_1 (e:nat) (lst:list nat) : list nat :=
    match lst with
    | nil => nil
    | hd::tl => if Nat.eqb e hd then remove_elem_1 e tl else hd::(remove_elem_1 e tl)
    end.

Fixpoint solution_1 lst :=
    match lst with
    | nil => nil
    | hd::tl => hd::(remove_elem_1 hd (solution_1 tl))
    end.

    Fixpoint isNotIN_4 (lst: list nat) (c: nat) : bool :=
    match lst with
    | nil => true
    | hd::tl => if Nat.eqb hd c then false else isNotIN_4 tl c
    end.

Fixpoint uniqSave_4 (l1:list nat) (l2:list nat) : list nat :=
    match l1 with
    | nil => l2
    | hd::tl => if isNotIN_4 l2 hd then uniqSave_4 tl (l2++hd::nil) else uniqSave_4 tl l2
    end.
Definition solution_4 (lst: list nat) : list nat := uniqSave_4 lst nil.

Fixpoint comb lst a := 
  match lst with
    [] => [a]
    |hd::tl => if hd =? a then lst else hd::(comb tl a)
  end.

Fixpoint app l1 l2 :=
  match l1 with
    [] => l2
    |hd :: tl => app tl (comb l2 hd)
  end.
    
Definition sol4 lst := app lst [].
  
Theorem ta1_sol4 : forall lst, solution_1 lst = sol4 lst.
Proof.
    unfold sol4.
    induction lst.
    simpl.
    reflexivity.
    simpl.
    induction lst.
    simpl.
    reflexivity.
    simpl.
    case (a=?a0) eqn:E.
    rewrite Nat.eqb_eq in E.
    rewrite E in *.
    (* synthesize generalize term *)
    Abort.
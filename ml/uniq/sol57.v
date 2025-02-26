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

    Fixpoint rev (a accum : list nat) :=
    match a with
      |[] => accum
      |hd::tl => rev tl ([hd] ++ accum)
    end.
    
    Fixpoint check item l := 
    match l with
            | [] => [item]
            | hd :: tl => if hd =? item then l else hd :: check item tl
    end.
    Fixpoint putIn list1 list2 := 
    match list1 with
        | [] => list2
        | hd :: tl =>
           putIn tl (check hd list2)
    end.
    
    Definition sol57 lst := putIn lst [].
    
    Theorem ta1_sol57 : forall lst, solution_1 lst = sol57 lst.
    Proof.
        unfold sol57.
        induction lst.
        simpl.
        reflexivity.
        simpl.
        induction lst.
        simpl.
        reflexivity.
        simpl.
        case (a=?a0) eqn:E.
        (* synthesize generalize term *)
        Abort.
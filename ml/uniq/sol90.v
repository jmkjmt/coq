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
    
    Definition fastrev lst := rev lst [].
  
    Fixpoint search l1 e :=
      match l1 with
        |[] => false
        |hd::tl => if hd =? e then true else search tl e
        end.
      
    Fixpoint delete lst :=
      match lst with
        |[] => []
        |hd::tl => if search tl hd then delete tl else [hd] ++ delete tl
        end.
      
    Definition sol9 lst := fastrev (delete (fastrev lst)).
    
    Theorem ta1_sol9 : forall lst, solution_1 lst = sol9 lst.
    Proof.
        unfold sol9.
        unfold fastrev.
        induction lst.
        simpl.
        reflexivity.
        simpl.
        induction lst.
        simpl.
        reflexivity.
        simpl.
        (* snthesize generalize term *)
        Abort.
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

    Fixpoint reverse (l: list nat) :=
    match l with
      | [] => l
      | hd::tl => reverse tl ++ [hd]
  end.
  
  Fixpoint insert a l :=
    match l with
      | [] => [a]
      | hd::tl => if a <? hd then a::hd::tl 
                  else hd:: (insert a tl)
  end.
  
  Fixpoint checker l1 a := 
    match l1 with
      | [] => false
      | [k] => k =? a 
      | hd::tl => if hd =? a then true else checker tl a
  end.
  
  Fixpoint finder l1 fin := 
    match l1 with
      | [] => fin
      | hd::tl => if checker fin hd then finder tl fin else finder tl (hd::fin)
  end.
  
  Definition sol75 lst :=
    match lst with
      | [] => []
      | _ => reverse (finder lst [])
  end.
  
  Theorem ta1_sol75 : forall lst, solution_1 lst = sol75 lst.
  Proof.
      unfold sol75.
      induction lst.
      reflexivity.
      simpl.
      induction lst.
      simpl.
      reflexivity.
      simpl.
      case (a=? a0) eqn:E.
      (* synthesize generalize term *)
      Abort.
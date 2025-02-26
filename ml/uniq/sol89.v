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

    Fixpoint reverse89 (l:list nat) a := 
match l with 
    | [] => a
    | hd::tl => reverse89 tl (hd::a) 
end.

Fixpoint gtl e ls := 
match ls with 
          | [] => false
          | h::t => if e =? h then true else gtl e t
end.
Fixpoint checkdrop lt l := 
match lt with
  | [] => l
  | hd::tl =>  if gtl hd l then checkdrop tl l else checkdrop tl (hd::l)
  end.


Definition sol89 lst := reverse89 (checkdrop lst []) [].

Theorem ta1_sol89 : forall lst, solution_1 lst = sol89 lst.
Proof.
    unfold sol89.
    induction lst.
    reflexivity.
    simpl.
    destruct lst.
    simpl.
    reflexivity.
    simpl.
    case (a =? n) eqn:E.
    rewrite Nat.eqb_sym in E.
    rewrite E in *.
    2:{
      rewrite Nat.eqb_sym in E.
      rewrite E in *.

    (* syntehszie generalize term *)
    }

    Abort.
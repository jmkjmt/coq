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

    Fixpoint fold_left (f : list nat -> nat -> list nat) (a: list nat) (l:list nat) :=
    match l with
    | [] => a
    | h::t => fold_left f (f a h) t
    end.
  
  Fixpoint has_element lst e :=
    match lst with
    | [] => false 
    | hd::tl => (hd =? e)||(has_element tl e)
      end.
  
  Definition sol101 (lst: list nat) :=
   fold_left (fun a x => if has_element a x then a else a ++ [x]) [] lst.
  
   Theorem ta1_sol101 : forall lst, solution_1 lst = sol101 lst.
   Proof.
      unfold sol101.
      induction lst.
      simpl.
      reflexivity.
      simpl.
      remember (fun (a : list nat) (x : nat) => if has_element a x then a else a ++ [x]) as f.
      induction lst.
      reflexivity.
      simpl.
      case (a =? a0) eqn:E.
      rewrite Nat.eqb_eq in E.
      rewrite E in *.
      rewrite Heqf.
      simpl.
      rewrite Nat.eqb_refl.
      simpl.
      (* rewrite <- Heqf.
      2 :{
          rewrite Heqf.
          simpl.
          rewrite E.
          simpl.
          rewrite <- Heqf.
      } *)
      (* synthesize generalize form *)
      
      Abort.
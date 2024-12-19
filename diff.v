Require Import ZArith.
Require Import String.
Require Import Ascii.
Require Import Bool.
Require Import List.
Require Import Program.
Require Import Lia.
Import ListNotations.
Module Export StringSyntax. End StringSyntax.

Inductive aexp : Type :=
| Const : Z -> aexp
| Var : string -> aexp
| Power : string -> Z -> aexp
| Times : list aexp -> aexp
| Sum : list aexp -> aexp.

(* Fixpoint map (f: aexp -> string -> aexp) (l:list aexp) (x : string) : list aexp :=
    match l with
    | [] => []
    | hd::tl => (f hd x) :: (map f tl x)
    end. *)

Fixpoint rank (e:aexp) : nat :=
    match e with
    | Const n => 1
    | Var a => 1
    | Power a n => 1
    | Times l => 1 + (fix sum_rank l :=
                        match l with
                        | [] => 0
                        | hd :: tl => (rank hd) + (sum_rank tl)
                        end) l
    | Sum l => 1 + (fix sum_rank l :=
                        match l with
                        | [] => 0
                        | hd :: tl => (rank hd) + (sum_rank tl)
                        end) l
    end.

Program Fixpoint diff (e:aexp) (x:string) {measure (rank e)} : aexp :=
    match e with
    | Const n => Const 0
    | Var a => (if negb (String.eqb a x) then Const 0 else Const 1)
    | Power a n => (if Z.ltb n  0 then Var "ERROR"
                    else if (Z.eqb n  0) || negb (String.eqb a x) then Const 0
                    else Times [Const n; (Power a (n-1))])
    | Times l => (match l with
                | [] => Var "ERROR"
                | [hd] => diff hd x
                | hd ::tl => Sum [Times ((diff hd x)::tl); Times [hd; diff (Times tl) x]]
    end)
    |Sum l => (match l with
            | [] => Var "ERROR"
            | [hd] => diff hd x
            | hd :: tl => Sum [diff hd x; diff (Sum tl) x]
            (* | _ => Sum (map (fun e => diff e x) l x) *)
            (* | _ => Sum (map (fun a => diff a x) l) *)
            end)
    end.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
(* Next Obligation.
Proof.
    cbn.
    lia.
    Qed.
Next Obligation.
Proof.
    cbn.
    lia.
Qed.
Next Obligation.
Proof.
    simpl.
    assert (forall e, rank e > 0).
    {
        induction e.
        simpl.
        firstorder.
        simpl.
        firstorder.
        simpl.
        firstorder.
        simpl.
        assert (forall n, 0 < S n).
        {
            induction n0.
            firstorder.
            firstorder.
        }
        apply H.
        simpl.
        assert (forall n, 0 < S n).
        {
            induction n0.
            firstorder.
            firstorder.
        }
        apply H.
    }
    rewrite <- Nat.add_succ_r.
    rewrite Nat.add_comm.
    rewrite <- Nat.add_0_r at 1.
    rewrite <- Nat.add_lt_mono_l.
    apply H.
    Qed.

Next Obligation.
Proof.
    simpl.
    lia.
    Qed.

Next Obligation.
Proof.
    simpl.
    lia.
Qed.
Next Obligation.
    simpl.
    rewrite plus_n_Sm.
    rewrite Nat.add_comm.
    rewrite <- Nat.add_0_r at 1.
    rewrite <- Nat.add_lt_mono_l.
    assert (forall e, rank e > 0).
    {
        induction e.
        all: simpl; lia.
    }
    apply H.
Qed. *)
Program Fixpoint bla (n:nat) {measure n} :=
match n with
| 0 => 0
| S n' => S (bla n')
end.
Lemma obvious: forall n, bla n = n.
Proof.
intro n ; induction n.
 reflexivity.
 unfold bla ; rewrite fix_sub_eq ; simpl ; fold (bla n).
 rewrite IHn ; reflexivity.

(* This can probably be automated using Ltac *)
 intros x f g Heq.
  destruct x.
  reflexivity.
  f_equal.
  apply Heq.
Qed.


Theorem eq: forall e x, diff e x = diff (Sum [e]) x.
Proof.
    intros.
    unfold diff.
    unfold diff_func.
    Search (Fix_sub).
    rewrite fix_sub_eq.
    simpl.
    f_equal.
    

    
    

    

    Print fix_sub_eq.

    

    f_equal.
    intros.
    Print f_equal.
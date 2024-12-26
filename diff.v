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

Fixpoint eq (e1 e2 : aexp) : bool :=
    match e1, e2 with
    | Const n1, Const n2 => Z.eqb n1 n2
    | Var x1, Var x2 => String.eqb x1 x2
    | Power x1 n1, Power x2 n2 => andb (String.eqb x1 x2) (Z.eqb n1 n2)
    | Times l1, Times l2 => if (length l1 =? length l2) then forallb (fun x => existsb (eq x) l2) l1
                            else false
    | Sum l1, Sum l2 => if (length l1 =? length l2) then forallb (fun x => existsb (eq x) l2) l1
                            else false
    | _, _ => false
    end.

Fixpoint nth (l:list aexp) (n:nat) : aexp :=
    match l with
    | [] => Var "ERROR"
    | hd::tl => match n with
                | 0 => hd
                | S n' => nth tl n'
                end
    end.

Fixpoint list_map (f: aexp  -> aexp) (l:list aexp) : list aexp :=
    match l with
    | [] => []
    | hd::tl => (f hd) :: (list_map f tl)
    end.

Fixpoint map (f: aexp -> string -> aexp) (l:list aexp) (x : string) : list aexp :=
    match l with
    | [] => []
    | hd::tl => (f hd x) :: (map f tl x)
    end.

Fixpoint mem (e:aexp) (l:list aexp) : bool :=
    match l with
    | [] => false
    | hd::tl => if (eq e hd) then true else mem e tl
    end.

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
Program Fixpoint diff102 (e:aexp) (x:string) {measure (rank e)} : aexp :=
    match e with
    | Const n => Const 0
    | Var a => (if negb (String.eqb a x) then Const 0 else Const 1)
    | Power a n => (if Z.ltb n  0 then Var "ERROR"
                    else if (Z.eqb n  0) || negb (String.eqb a x) then Const 0
                    else Times [Const n; (Power a (n-1))])
    | Times l => (match l with
                | [] => Var "ERROR"
                | [hd] => diff102 hd x
                | hd ::tl => Sum [Times ((diff102 hd x)::tl); Times [hd; diff102 (Times tl) x]]
    end)
    |Sum l => Sum (list_map (fun aexp2 => diff102 aexp2 x) l)
    end.

Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Theorem test: forall e x, diff e x = diff102 e x.
Proof.
    induction e.

    
Require Import Bool Arith List.
Set Implicit Arguments.
Set Asymmetric Patterns.

Inductive binop : Set := Plus | Times.
Inductive exp: Set :=
|Const : nat -> exp
|Binop : binop -> exp -> exp -> exp.

Inductive instr : Set :=
| iConst : nat -> instr
| iBinop : binop -> instr.

Definition prog := list instr.
Definition stack := list nat.

Definition binopDenote ( b: binop) : nat -> nat -> nat :=
    match b with
    | Plus => plus
    | Times => mult
    end.

Fixpoint expDenote (e:exp) : nat :=
    match e with
    | Const n => n
    | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
    end.

Definition instrDenote (i:instr) (s:stack) : option stack :=
    match i with
    | iConst n => Some (n::s)
    | iBinop b => 
        match s with
        | arg1 :: arg2 :: s' => Some ((binopDenote b) arg1 arg2 :: s')
        | _ => None
        end
    end.
Fixpoint progDenote (p:prog) (s:stack) : option stack :=
    match p with
    | nil => Some s
    | i :: p' =>
        match instrDenote i s with
        | None => None
        | Some s' => progDenote p' s'
        end
    end.
Fixpoint compile (e:exp) : prog :=
    match e with
    |Const n => iConst n :: nil
    | Binop b e1 e2 => compile e2 ++ compile e1 ++ iBinop b::nil
    end.
Lemma compile_correct' : forall e p s, progDenote (compile e ++ p) s = progDenote p ( expDenote e::s).
Proof.
    induction e.
    intros.
    unfold compile.
    unfold expDenote.
    unfold progDenote at 1.
    simpl.
    fold progDenote.
    reflexivity.
    intros.
    simpl.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite <- app_assoc.
    rewrite IHe1.
    simpl.
    reflexivity.
    Qed.
Theorem compile_correct : forall e, progDenote (compile e) nil = Some (expDenote e::nil).
Proof.
    intros.
    rewrite <- (app_nil_r (compile e)).
    rewrite compile_correct'.
    simpl.
    reflexivity.
    Qed.
    
Theorem compile_correct2 : forall e, progDenote (compile e) nil = Some (expDenote e::nil).
Proof.
    intros.
    rewrite <- (app_nil_r (compile e)).
    induction e.
    simpl.
    reflexivity.
    simpl.
    rewrite <- app_assoc.
    rewrite IHe2.
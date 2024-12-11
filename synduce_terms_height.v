Require Import Bool.

Inductive Unit : Type :=
    | Null : Unit.

Inductive ArithOp : Type :=
    | APlus : Unit -> ArithOp
    | AMinus : Unit -> ArithOp
    | AGt : Unit -> ArithOp.

Inductive BoolOp : Type :=
    | BAnd : Unit -> BoolOp
    | BOr : Unit -> BoolOp
    | BNot : Unit -> BoolOp
    | BEq : Unit -> BoolOp.

Inductive Nat : Type :=
    | Zero : Nat
    | Succ : Nat -> Nat.

Inductive Term: Type :=
    | TArithBin : ArithOp -> Term -> Term -> Term
    | TBoolBin : BoolOp -> Term -> Term -> Term
    | TArithUn : ArithOp -> Term -> Term
    | TBoolUn : BoolOp -> Term -> Term
    | TVar : Nat -> Term
    | TCInt : Nat -> Term
    | TCBool : bool -> Term.

Inductive Op : Type :=
    | OpPlus : Unit -> Op
    | OpMinus : Unit -> Op
    | OpNot : Unit -> Op
    | OpAnd : Unit -> Op
    | OpOr : Unit -> Op
    | OpGt : Unit -> Op
    | OpEq : Unit -> Op.

Inductive Term2 : Type :=
    | Bin : Op -> Term2 -> Term2 -> Term2
    | Un : Op -> Term2 -> Term2
    | Var : Nat -> Term2
    | CInt : Nat -> Term2
    | CBool : bool -> Term2.

Fixpoint eqb (n1 n2 : Nat) : bool :=
    match (n1, n2) with
    | (Zero, Zero) => true
    | (Zero, Succ _) => false
    | (Succ _ , Zero) => false
    | (Succ n1', Succ n2') => eqb n1' n2'
    end.

Definition tf0 t1 t2 op : Term :=
    match op with
    | OpPlus _ => TArithBin (APlus Null) t2 t1
    | OpMinus _ => TArithBin (AMinus Null) t2 t1
    | OpNot _ => TBoolBin (BNot Null) t2 t1
    | OpAnd _ => TBoolBin (BAnd Null) t2 t1
    | OpOr _ => TBoolBin (BOr Null) t2 t1
    | OpGt _ => TArithBin (AGt Null) t2 t1
    | OpEq _ => TBoolBin (BEq Null) t2 t1
    end.

Definition mkbin t1 t2 op : Term :=
    tf0 t1 t2 op.

Definition tf1 t1 op : Term :=
    match op with
    | OpPlus _ => TArithUn (APlus Null) t1
    | OpMinus _ => TArithUn (AMinus Null) t1
    | OpNot _ => TBoolUn (BNot Null) t1
    | OpAnd _ => TBoolUn (BAnd Null) t1
    | OpOr _ => TBoolUn (BOr Null) t1
    | OpGt _ => TArithUn (AGt Null) t1
    | OpEq _ => TBoolUn (BEq Null) t1
    end.

Definition mkun t1 op : Term :=
    tf1 t1 op.

Fixpoint tf3 (t:Term2) : Term :=
    match t with
    | Bin op t1 t2 => mkbin (tf3 t1) (tf3 t2) op
    | Un op t1 => mkun (tf3 t1) op
    | Var n => TVar n
    | CInt n => TCInt n
    | CBool b => TCBool b
    end.

Definition repr (t:Term2) : Term :=
    tf3 t.

Fixpoint lq (n1 n2 : Nat) : bool :=
    match (n1, n2) with
    | (Zero, Zero) => false
    | (Zero, Succ _) => true
    | (Succ _ , Zero) => false
    | (Succ n1', Succ n2') => lq n1' n2'
    end.

Definition max (n1 n2 : Nat) : Nat :=
    if lq n1 n2 then n2 else n1.

Fixpoint plus (n1 n2 : Nat) : Nat :=
    match n1 with
    | Zero => n2
    | Succ n1' => Succ (plus n1' n2)
    end.

Fixpoint tf5 (t:Term) : Nat :=
    match t with
    | TArithBin _ t1 t2 => plus (Succ Zero) (max (tf5 t1) (tf5 t2))
    | TBoolBin _ t1 t2 => plus (Succ Zero) (max (tf5 t1) (tf5 t2))
    | TArithUn _ t1 => plus (Succ Zero) (tf5 t1)
    | TBoolUn _ t1 => plus (Succ Zero) (tf5 t1)
    | TVar _ => (Succ Zero)
    | TCInt _ => (Succ Zero)
    | TCBool _ => (Succ Zero)
    end.

Definition spec (t:Term) : Nat :=
    tf5 t.

Fixpoint tf7 (t:Term2) : Term2 :=
    match t with
    | Bin op t1 t2 => Bin op (tf7 t1) (tf7 t2)
    | Un op t1 => Un op (tf7 t1)
    | Var n => Var n
    | CInt n => CInt n
    | CBool b => CBool b
    end.

Definition target (t:Term2) : Term2 :=
    tf7 t.

Definition main (t:Term2) : Nat :=
    spec (repr (target t)).

Fixpoint tf9 (t: Term2) : Nat :=
    match t with
    | Bin op t1 t2 => plus (Succ Zero) (max (tf9 t1) (tf9 t2))
    | Un op t1 => plus (Succ Zero) (tf9 t1)
    | Var _ => (Succ Zero)
    | CInt _ => (Succ Zero)
    | CBool _ => (Succ Zero)
    end.

Definition targetNew (t:Term2) : Nat :=
    tf9 t.

Definition mainNew (t:Term2) : Nat :=
targetNew t.
Theorem lq_symmetry : forall m n : Nat, lq m n = true -> lq n m = false.
Proof.
  intros m n.
  generalize dependent n.
  induction m as [| m' IH].
  - 
    intros n H.
    destruct n as [| n']. 
    + 
      simpl in H. discriminate. 
    + 
      simpl. reflexivity. 
  - 
    intros n H.
    destruct n as [| n'].
    + 
      simpl in H. discriminate.
    + 
      simpl in H.
      apply IH in H. 
      simpl. assumption.
Qed.
Theorem optimize : forall inp0 : Term2 , main inp0 = mainNew inp0.
Proof.
     assert (forall n m , max n m = max m n).
    {
        intros.
        unfold max.
        case (lq n m) eqn:E.
        assert (lq m n = false).
        {
            generalize dependent m.
            induction n.
            -
            intros.
            case m.
            simpl.
            reflexivity.
            +
            simpl.
            reflexivity.
            -
            intros.
            simpl in *.
            case m eqn:H.
            +
            discriminate.
            +
            simpl.
            apply IHn.
            rewrite E.
            reflexivity.      
        }
        rewrite H.
        reflexivity.
        assert (or((lq m n)= true ) ((eqb m n) = true) ).
        {
            case (lq m n) eqn:H.
            left.
            reflexivity.
            right.
            generalize dependent n.
            induction m.
            intros.
            simpl in *.
            case n eqn:H1.
            reflexivity.
            discriminate.
            intros.
            simpl in *.
            case n eqn:H1.
            discriminate.
            rewrite IHm.
            reflexivity.
            simpl in *.
            rewrite E.
            reflexivity.
            rewrite H.
            reflexivity.
        }
        case (lq m n) eqn:H1.
        reflexivity.
        apply orb_true_intro in H.
        simpl in *.
        generalize dependent n.
        induction m.
        intros.
        case n eqn:H2.
        reflexivity.
        simpl in *.
        discriminate.
        intros.
        simpl in *.
        case n eqn:H2.
        discriminate.
        simpl in *.
        apply IHm in E.
        rewrite E.
        reflexivity.
        rewrite H1.
        reflexivity.
        rewrite H.
        reflexivity.
    }
    unfold main, mainNew.
    unfold targetNew.
    unfold target.
    unfold spec.
    unfold repr.
    induction inp0.
    simpl.
    unfold mkbin.
    unfold tf0.
    case o eqn:E.
    simpl.
    rewrite IHinp0_1.
    rewrite IHinp0_2.
    rewrite H.
    reflexivity.
    simpl.
    rewrite IHinp0_1.
    rewrite IHinp0_2.
    rewrite H.
    reflexivity.
    simpl.
    rewrite IHinp0_1.
    rewrite IHinp0_2.
    rewrite H.
    reflexivity.
    simpl.
    rewrite IHinp0_1.
    rewrite IHinp0_2.
    rewrite H.
    reflexivity.
    simpl.
    rewrite IHinp0_1.
    rewrite IHinp0_2.
    rewrite H.
    reflexivity.
    simpl.
    rewrite IHinp0_1.
    rewrite IHinp0_2.
    rewrite H.
    reflexivity.
    simpl.
    rewrite IHinp0_1.
    rewrite IHinp0_2.
    rewrite H.
    reflexivity.
    simpl.
    unfold mkun.
    unfold tf1.
    case o eqn:E.
    simpl.
    rewrite IHinp0.
    reflexivity.
    simpl.
    rewrite IHinp0.
    reflexivity.
    simpl.
    rewrite IHinp0.
    reflexivity.
    simpl.
    rewrite IHinp0.
    reflexivity.
    simpl.
    rewrite IHinp0.
    reflexivity.
    simpl.
    rewrite IHinp0.
    reflexivity.
    simpl.
    rewrite IHinp0.
    reflexivity.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
Qed. 
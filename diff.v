Require Import ZArith.
Require Import String.
Require Import Ascii.
Require Import Bool.
Require Import List.
Import ListNotations.
Module Export StringSyntax. End StringSyntax.
Search ( _<>_).
Inductive aexp : Type :=
| Const : Z -> aexp
| Var : string -> aexp
| Power : string -> Z -> aexp
| Times : list aexp -> aexp
| Sum : list aexp -> aexp.

Fixpoint map (f: aexp -> string -> aexp) (l:list aexp) (x : string) : list aexp :=
    match l with
    | [] => []
    | hd::tl => (f hd x) :: (map f tl x)
    end.

Fixpoint diff (e:aexp) (x:string) : aexp :=
    match e with
    | Const n => Const 0
    | Var a => if negb (String.eqb a x) then Const 0 else Const 1
    | Power a n => if Z.ltb n  0 then Var "ERROR"
                    else if (Z.eqb n  0) || negb (String.eqb a x) then Const 0
                    else Times [Const n; (Power a (n-1))]
    | Times l => match l with
                | [] => Var "ERROR"
                | [hd] => diff hd x
                | hd ::tl => Sum [Times ((diff hd x)::tl); Times [hd; diff (Times tl) x]]
    end
    |Sum l => match l with
            | [] => Var "ERROR"
            | _ => Sum (map diff l x)
    end
    end.

Require Import Bool Arith List.
Set Implicit Arguments.
Set Asymmetric Patterns.

Definition nandb (b1 b2 :bool) : bool :=
    match b1 with
    | true => negb b2
    | false => true
    end.
Example test_nandb1: (nandb true false) = true.
Proof.
    simpl.
    reflexivity.
    Qed.

Check negb.

Inductive rgb :
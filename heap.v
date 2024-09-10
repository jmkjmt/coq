Require Import ZArith.
Open Scope Z_scope.

Definition rank := Z.
Definition value := Z.
Inductive heap : Type :=
| EMPTY : heap
| NODE : rank -> value -> heap -> heap -> heap.
Definition getrank h := 
    match h with
    | EMPTY => -1
    | NODE r _ _ _ => r
    end.

Definition shake (x:value) (lh:heap) (rh:heap) : heap :=
if Z.leb (getrank rh) (getrank lh) then NODE ((getrank rh) + 1) x lh rh
else NODE ((getrank lh) + 1) x rh lh.

Fixpoint merge (h1:heap) (h2:heap) : heap :=
    match h1,h2 with
    | EMPTY, h => h
    | h, EMPTY => h
    | NODE _ x1 lh1 rh1 , NODE _ x2 lh2 rh2 => if Z.ltb x2 x1 then shake x2 lh2 (merge h1 rh2)
                                                            else shake x2 lh1 (merge rh1 h2)
    end.

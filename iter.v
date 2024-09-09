Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Fixpoint solution (n:Z) (f:Z->Z) : Z->Z :=
if (Z.ltb n  0) then f
else if (Z.eqb n 0) then fun x:Z => x
else fun (x:Z) => f (solution (n-1) f x).
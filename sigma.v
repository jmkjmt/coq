Require Import ZArith.
Require Import Program.
Require Import Lia.
Open Scope Z_scope.


Program Fixpoint solution_1 (f: Z -> Z) (a: Z) (b: Z) {measure (b-a)}: Z :=
  if Z.ltb b a then 0
  else if Z.eqb a b then f a
  else f a + solution_1 f (a + 1) b.
  
  Next Obligation. 
  
  


  


  

  
  
 



Program Fixpoint solution_2 (f: nat -> nat) (a: nat) (b : nat) : nat :=
    if (Nat.ltb b a) then 0 
    else (f b) + solution_2 f a (b-1)
.


Compute solution_1 (fun x => x + 1) 1 3.





Program Fixpoint aux (a:nat) (b:nat) (f:nat->nat) (acc:nat) : nat :=
if (Nat.ltb b a) then acc else aux (a+1) b f (acc + (f a))
.

Fixpoint solution_3 (f: nat -> nat) (a: nat) (b : nat) : nat :=
aux a b f 0
.
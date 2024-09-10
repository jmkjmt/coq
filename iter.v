Require Import ZArith.
Require Import Arith.
Require Import Program.
Require Import Lia.
Require Import Coq.Arith.Wf_nat.


Definition foo (n: nat) (f: Z -> Z) : Z -> Z.

(* Prove termination using well-founded recursion *)
Proof.
  apply (well_founded_induction lt_wf (fun n => (Z -> Z))).

  intros n1 IH.

  (* Now define the function body using the induction hypothesis *)
  destruct (Nat.eqb n 0) eqn:H.
  - (* Base case: when n = 0 *)
    exact (fun x => x).
  - (* Recursive case: when n > 0 *)
    exact (fun x => f (IH (n - 1) (Nat.sub_lt n 0) f x)).
Defined.

Program Fixpoint sol (n: nat) (f: Z -> Z) (x: Z) {measure (n)}: Z :=
if Nat.eqb n 0 then x
else f (sol (n - 1) f x).

Next Obligation.
Proof.



induction n.
simpl.





(* fun (x: Z) => f ((sol (n - 1) f) x). *)


Fixpoint asdfasdfadfasdfas (n: nat) (f: Z -> Z): (Z -> Z) :=
if (Nat.ltb n 0) then f
else if (Nat.eqb n 0) then fun x:Z => x
else fun (x:Z) => f ((asdfasdfadfasdfas (n-1) f) x).


Program Fixpoint solution (n: nat) (f: Z -> Z) {measure (n)}: (Z -> Z) :=
if (Nat.ltb n 0) then f
else if (Nat.eqb n 0) then fun x:Z => x
else fun (x:Z) => f ((solution (n-1) f) x).

Fixpoint solution2 (n:Z) (f:Z->Z) : Z->Z :=
if (Z.ltb n 0) then f
else if (Z.eqb n 0) then fun x:Z => x
else fun (x:Z) => f (solution2 (n-1) f x).
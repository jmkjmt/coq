Inductive lst : Type :=
  | Nil : lst
  | Cons : nat -> lst -> lst.

Inductive queue : Type :=
  | Queue : lst -> lst -> queue.

Fixpoint len (l : lst) : nat :=
match l with
  | Nil => 0
  | Cons a l1 => 1 + (len l1)
end.

Definition qlen (q : queue) : nat :=
match q with
  | Queue l1 l2 => (len l1) + (len l2)
end. 
Fixpoint app (l : lst) (m: lst): lst :=
match l with
  | Nil => m
  | Cons a l1 => Cons a (app l1 m)
end.

Fixpoint rev (l: lst): lst :=
match l with
  | Nil => Nil
  | Cons a l1 => app (rev l1) (Cons a Nil)
end.

Fixpoint leb (n m : nat) : bool :=
match (n, m) with
  | (0, _) => true
  | (S n', S m') => leb n' m'
  | _ => false
end. 

Definition amortizeQueue (l1 l2 : lst) : queue :=
  if leb (len l2)  (len l1) then Queue l1 l2
  else Queue (app l1 (rev l2)) Nil.

Definition qpush (q : queue) (n : nat) : queue :=
match q with
  | Queue l1 l2 => amortizeQueue l1 (Cons n l2)
end.
Theorem queue_push : forall q n, qlen (qpush q n) = 1 + (qlen q).
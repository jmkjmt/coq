type nat = ZERO | SUCC of nat

let rec natadd n1 n2 =
  match n2 with
  | ZERO -> n1
  | SUCC n -> SUCC (natadd n1 n)
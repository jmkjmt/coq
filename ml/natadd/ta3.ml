type nat = ZERO | SUCC of nat

let rec natadd n1 n2 =
  match n1 with
  | ZERO -> n2
  | SUCC n -> natadd n (SUCC n2)
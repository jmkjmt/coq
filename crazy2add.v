Inductive crazy2 : Type :=
| NIL : crazy2
| ZERO : crazy2 -> crazy2
| ONE : crazy2 -> crazy2
| MONE : crazy2 -> crazy2.

Fixpoint crazy2add (c1:crazy2) (c2:crazy2) : crazy2 :=
    match c1 with
    | NIL => c2
    | ZERO c1' => match c2 with
                | NIL => c1
                | ZERO c2' => ZERO (crazy2add c1' c2')
                | ONE c2' => ONE (crazy2add c1' c2')
                | MONE c2' => MONE (crazy2add c1' c2')
    end
    | ONE c1' => match c2 with
                | NIL => c1
                | ZERO c2' => ONE (crazy2add c1' c2')
                | ONE c2' => ZERO (crazy2add (ONE NIL) (crazy2add c1' c2'))
                | MONE c2' => ZERO (crazy2add c1' c2')
    end
    | MONE c1' => match c2 with
                | NIL => c1
                | ZERO c2' => MONE (crazy2add c1' c2')
                | ONE c2' => ZERO (crazy2add c1' c2')
                | MONE c2' => ZERO (crazy2add (MONE NIL) (crazy2add c1' c2'))
    end
    end.
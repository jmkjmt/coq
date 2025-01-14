Require Import String.
Require Import List.
Require Import Arith.
Import ListNotations.

Inductive lambda : Type :=
| V : string -> lambda
| P : string -> lambda -> lambda
| C : lambda -> lambda -> lambda.


Fixpoint is_mem_1 variables string : bool :=
match variables with
| nil => false
| hd::tl => if String.eqb hd string then true else is_mem_1 tl string
end.

Fixpoint sub_check_1 lambda vars : bool :=
match lambda with
| V x => is_mem_1 vars x
| P x e => sub_check_1 e (x::vars)
| C e1 e2 => (sub_check_1 e1 vars) && (sub_check_1 e2 vars)
end.

Definition solution_1 (lambda:lambda) : bool := sub_check_1 lambda [].

Fixpoint mem (v:string) (l:list string) : bool :=
  match l with
  | [] => false
  | hd::tl => if String.eqb hd v then true else mem v tl
  end.

Fixpoint check_2 (ma:lambda) (lst : list string) : bool :=
  match ma with
  | V x => mem x lst
  | P x e => check_2 e (x::lst)
  | C e1 e2 => (check_2 e1 lst) && (check_2 e2 lst)
  end.
Definition solution_2 (m: lambda) : bool :=
  match m with
  | V x => false
  | P x e => check_2 e [x]
  | C e1 e2 => check_2 e1 [] && check_2 e2 []
  end.

Fixpoint check_3 (ma: lambda) (li:list string) : bool :=
  match ma with
  | P st k => if mem st li then check_3 k li else check_3 k (st::li)
  | C me1 me2 => (check_3 me1 li) && (check_3 me2 li)
  | V na => mem na li
  end.

Definition solution_3 (m:lambda) : bool := check_3 m [].

Fixpoint exist (p : string -> bool) (l : list string) : bool :=
  match l with
  | [] => false
  | hd::tl => p hd || exist p tl
  end.
Fixpoint check_4 (ma: lambda) (li:list string) : bool :=
  match ma with
  | P st k => check_4 k (st::li)
  | C me1 me2 => (check_4 me1 li) && (check_4 me2 li)
  | V na => exist (fun x => String.eqb x na) li
  end.
Definition solution_4 (m : lambda) : bool :=
  match m with
  | P st k => check_4 k [st]
  | C me1 me2 => check_4 me1 [] && check_4 me2 []
  | V na => false
  end.

 

Theorem eq1 : forall (m : lambda), solution_1 m = solution_2 m.
Proof.
  assert(lemma1: forall m l, sub_check_1 m l = check_2 m l).
  { 
    induction m.
    simpl.
    induction l.
    simpl.
    reflexivity.
    simpl.
    rewrite IHl.
    reflexivity.
    simpl.
    intros l.
    rewrite IHm.
    reflexivity.
    intros l.
    simpl.
    rewrite IHm1.
    rewrite IHm2.
    reflexivity.
  }
  induction m.
  reflexivity.  
  unfold solution_1.
  simpl.
  apply lemma1.
  unfold solution_1.
  simpl.
  unfold solution_1 in *.
  rewrite lemma1 in *.
  rewrite lemma1.
  reflexivity.
  Qed.
  
Theorem eq2 : forall (m : lambda), solution_1 m = solution_4 m.
Proof.
  assert (lemma1: forall m lst, sub_check_1 m lst = check_4 m lst).
  {
    induction m.
    intros lst.
    simpl.
    induction lst.
    simpl.
    reflexivity.
    simpl.
    case (String.eqb a s) eqn :eq.
    reflexivity.
    simpl.
    rewrite IHlst.
    reflexivity.
    intros.
    simpl.
    rewrite IHm.
    reflexivity.
    simpl.
    intros.
    rewrite IHm1.
    rewrite IHm2.
    reflexivity.
  }
  induction m.
  unfold solution_1.
  reflexivity.
  unfold solution_1.
  simpl.  
  apply lemma1.
  unfold solution_1.
  simpl.
  rewrite lemma1.
  rewrite lemma1.
  reflexivity.
Qed.
Fixpoint mk_lst (v:string) (n:nat) : list string :=
  match n with
  | 0 => [v]
  | S n' => v::(mk_lst v n')
  end.
Lemma mem13 : forall v lst, is_mem_1 lst v = mem v lst.
Proof.
  induction lst.
  reflexivity.
  simpl.
  rewrite IHlst.
  reflexivity.
Qed.
Lemma check_13 : forall m lst, sub_check_1 m lst = check_3 m lst.
Proof.
  induction m.
  simpl.
  apply mem13.
  simpl.
  intros.
  case (mem s lst) eqn:E.
  rewrite <- IHm.
  (*  
  induction m.
  simpl.
  case (String.eqb v v0)eqn:E1.
  rewrite String.eqb_eq in E1.
  rewrite E1 in *.
  rewrite <- E.
  rewrite mem13.
  reflexivity.
  reflexivity.
  simpl.
  *)
  assert (forall m v lst1 lst2, mem v lst1 = true -> sub_check_1 m (lst2++ v::lst1) = sub_check_1 m (lst2++lst1)).
  {
    clear.
    induction m.
    simpl.
    intros.
    induction lst2.
    simpl.
    case (String.eqb v s) eqn:E.
    rewrite mem13.
    rewrite String.eqb_eq in E.
    rewrite E in *.
    rewrite H.
    reflexivity.
    reflexivity.
    simpl.
    case (String.eqb a s) eqn:E.
    reflexivity.
    rewrite IHlst2.
    reflexivity.
    simpl.
    intros.
    remember (v::lst2) as l.
    assert (s::lst2 ++ v::lst1 = (s::lst2) ++ v::lst1).
    reflexivity.
    rewrite H0.
    assert (s::lst2 ++ lst1 = (s::lst2) ++ lst1).
    reflexivity.
    rewrite H1.
    apply IHm.
    apply H.
    intros.
    simpl.
    assert (sub_check_1 m1 (lst2 ++ v :: lst1) = sub_check_1 m1 (lst2 ++ lst1)).
    {
      apply IHm1.
      apply H.
    }
    assert (sub_check_1 m2 (lst2 ++ v :: lst1) = sub_check_1 m2 (lst2 ++ lst1)).
    {
      apply IHm2.
      apply H.
    }
    rewrite H0.
    rewrite H1.
    reflexivity.    
  }
  specialize (H m s lst []).
  simpl in H.
  apply H.
  apply E.
  apply IHm.
  intros.
  simpl.
  rewrite IHm1.
  rewrite IHm2.
  reflexivity.
Qed.

Theorem eq3: forall (m: lambda), solution_1 m = solution_3 m.
Proof.
  unfold solution_1.
  unfold solution_3.
  intros.
  rewrite check_13.
  reflexivity.
Qed.

Fixpoint getStn (m: lambda) : list string :=
  match m with
  | V string => [string]
  | P (n) m' => List.filter (fun x => negb (String.eqb x n)) (getStn m')
  | C (m1) (m2) => (getStn m1) ++ (getStn m2)
  end.

Definition sol5 (m: lambda) : bool :=
  match getStn m with
  | [] => true
  | _ => false
  end.
Theorem ta1_sol5 : forall m, solution_1 m = sol5 m.
Proof.
  unfold sol5.
  unfold solution_1.
  induction m.
  simpl.
  reflexivity.
  simpl.
  2:{
    simpl.
    rewrite IHm1.
    rewrite IHm2.
    destruct (getStn m1).
    simpl.
    reflexivity.
    simpl.
    reflexivity.
  }
  induction m.
  simpl.
  case (String.eqb s s0) eqn:E.
  rewrite String.eqb_sym in E.
  rewrite E.
  simpl.
  reflexivity.
  rewrite String.eqb_sym in E.
  rewrite E.
  simpl.
  reflexivity.
  simpl.
  (* synthesize generalize form *)
  Abort.
Open Scope string_scope.
Fixpoint valify (string_: string) (covers: lambda) : bool :=
  match covers with
  | V n => false
  | P (n) m_ => if n =? string_ then true else valify string_ m_
  | C (m1) (m2) => false
  end.

Fixpoint findStation (cur: lambda) (covers: lambda) : bool :=
  match cur with
  | V n => valify n covers
  | P (n) m_ => findStation m_ (P (n) covers)
  | C (m1) (m2) => (findStation m1 covers) && (findStation m2 covers)
  end.

Definition sol50 m := findStation m (V (" " : string)).

Theorem ta1_sol50 : forall m, solution_1 m = sol50 m.
Proof.
  unfold solution_1.
  unfold sol50.
  induction m.
  unfold findStation.
  unfold valify.
  simpl sub_check_1.
  reflexivity.
  2:{
    simpl.
    rewrite IHm1.
    rewrite IHm2.
    reflexivity.
  }
  simpl.
  induction m.
  simpl in *.
  reflexivity.
  simpl in *.
  (* synthesize generalize term *)
  Abort.
  
Fixpoint deleteAll (list_input : list string) (target : string) : list string :=
			match list_input with
			| l::remain_list => 
				if l =? target then deleteAll remain_list target
				else l::deleteAll remain_list target
			| [] => []
      end.

Fixpoint listStation (m_input : lambda) : list string :=
			match m_input with
			| V n => [n]
			| P n m => deleteAll (listStation m) n
			| C m1 m2 => (listStation m1) ++ (listStation m2)
      end.
Definition sol57 (lambda_input : lambda) := 
  match (listStation lambda_input) with
  | [] => true
  | _ => false
  end.

Theorem ta1_sol57 : forall m, solution_1 m = sol57 m.
Proof.
  unfold solution_1.
  unfold sol57.
  intros.
  induction m.
  simpl.
  reflexivity.
  2:{
    simpl.
    rewrite IHm1.
    rewrite IHm2.
    destruct (listStation m1).
    simpl.
    reflexivity.
    simpl.
    reflexivity.
  }
  simpl.
  induction m.
  simpl.
  case (s =? s0) eqn:E.
  rewrite String.eqb_eq in E.
  rewrite E in *.
  rewrite String.eqb_refl.
  reflexivity.
  rewrite String.eqb_sym in E.
  rewrite E.
  reflexivity.
  simpl.
  (* syn thesize generalize term *)
  Abort.

Fixpoint check_ (m:lambda) (al : list string) (nl : list string) : bool :=
  match m with
  | V n => List.forallb (fun x => is_mem_1 al x) (n::nl)
  | P (n) m_ => check_ m_ (n::al) nl
  | C (m1) (m2) => (check_ m1 al nl) && (check_ m2 al nl)
  end.

Definition sol101 (m : lambda) := check_ m [] [].

Theorem ta1_sol101 : forall m, solution_1 m = sol101 m.
Proof.
  unfold solution_1.
  unfold sol101.
  induction m.
  simpl.
  reflexivity.
  2:{
    simpl.
    rewrite IHm1.
    rewrite IHm2.
    reflexivity.
  }
  simpl.
  assert (forall m lst, sub_check_1 m lst = check_ m lst []).
  {
    clear.
    intros.
    generalize dependent lst.
    induction m.
    simpl.
    intros.
    case (is_mem_1 lst s).
    reflexivity.
    reflexivity.
    intros.
    simpl.
    apply IHm.
    simpl.
    intros.
    rewrite IHm1.
    rewrite IHm2.
    reflexivity.
  }
  apply H.
Qed.

Fixpoint varExists (var_foo : string) (var_list : list string) : bool :=
		match var_list with
		[] => false
		| h::t => 
			(if var_foo =? h then true
			else (varExists var_foo t))
    end.
			
Definition addToNameList (var_foo : string) (var_list : list string) : list string := 
		if varExists var_foo var_list then 
			var_list
		else 
			var_foo::var_list.
Fixpoint checkRec (lambda_foo : lambda) (var_list : list string) :bool := 
		match lambda_foo with
		V var_bar => 
			(varExists var_bar var_list)
		| P var_bar lambda_bar => 
			checkRec lambda_bar (addToNameList var_bar var_list)
		| C lambda_left lambda_right =>  
			(checkRec lambda_left var_list)
			&& (checkRec lambda_right var_list)
    end.
Definition sol109 (lambda_foo : lambda) : bool := checkRec lambda_foo [].

Theorem ta1_sol109 : forall m, solution_1 m = sol109 m.
Proof.
  unfold solution_1.
  unfold sol109.
  intros.
  induction m.
  simpl.
  reflexivity.
  2:{
    simpl.
    rewrite IHm1.
    rewrite IHm2.
    reflexivity.
  }
  simpl.
  (* synthesize generalize term *)
  Abort.
Fixpoint is_connect m :=
		match m with
		| V _ => false
		| C _ _ => true
		| P var lambda => is_connect lambda
    end.
	
	Fixpoint get_left (m: lambda) : lambda :=
		match m with
		| V _ => m
		| C l _ => l
		| P var lambda => P var (get_left lambda)
    end.
	
	Fixpoint get_right m :=
		match m with
		| V _ => m
		| C _ r => r
		| P var lambda => P var (get_right lambda)
    end.
(* 
Fixpoint check (m: lambda) : bool :=
	if is_connect m then (check (get_left m)) && (check (get_right m))
	else match m with
	| V _ => false
	| C l r => (check l) && (check r) 
	| P var lambda =>
		match lambda with
		| V s => if var=?s then true
					else false
		| C l r => (check (P var l)) && (check (P var r))
		| P var2 lambda2 => (check (P var lambda2)) || (check (P var2 lambda2))
    end
  end. *)

Fixpoint ck (l:lambda) (lst : list string) : nat :=
match l with
|P va e => ck e (va::lst)
|C ex1 ex2 => ck ex1 lst + ck ex2 lst
|V (va) => if (is_mem_1 lst va) then 0 else 1 
end.

Definition sol530 (l:lambda) : bool :=  
   Nat.eqb (ck l []) 0 .

Theorem ta1_sol530 : forall m, solution_1 m = sol530 m.
Proof.
  unfold solution_1.
  unfold sol530.
  induction m.
  simpl.
  reflexivity.
  2:{
    simpl.
    rewrite IHm1.
    rewrite IHm2.
    case (Nat.eqb (ck m1 []) 0) eqn:E.
    simpl.
    case (Nat.eqb (ck m2 []) 0 ) eqn:E1.
    rewrite Nat.eqb_eq in *.
    rewrite E.
    rewrite E1.
    simpl.
    reflexivity.
    rewrite Nat.eqb_eq in *.
    rewrite E.
    simpl.
    rewrite E1.
    reflexivity.
    simpl.
    rewrite Nat.eqb_neq in E.
    remember (ck m1 []) as n1.
    remember (ck m2 []) as n2.
    clear m1 m2 Heqn1 IHm1 Heqn2 IHm2.
    assert (n1 + n2 <> 0).
    {
      generalize dependent n1.
      induction n2.
      intros.
      rewrite Nat.add_0_r.
      apply E.
      intros.
      assert (n1 + S n2 = (S n1) + n2).
      {
        clear.
        generalize dependent n2.
        induction n1.
        simpl.
        reflexivity.
        simpl.
        intros.
        rewrite IHn1.
        reflexivity.
      }
      rewrite H.
      apply IHn2.
      auto.
    }
    rewrite <- Nat.eqb_neq in H.
    rewrite H.
    reflexivity.
  }
  simpl.
  assert (forall m lst, sub_check_1 m lst = Nat.eqb (ck m lst) 0).
  {
    clear.
    intros.
    generalize dependent lst.
    induction m.
    simpl.
    intros.
    case (is_mem_1 lst s).
    reflexivity.
    reflexivity.
    simpl.
    intros.
    rewrite IHm.
    reflexivity.
    simpl.
    intros.
    rewrite IHm1.
    rewrite IHm2.
    remember (ck m1 lst) as n1.
    remember (ck m2 lst) as n2.
    clear.
    induction n1.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
  }
  apply H.
Qed.
  
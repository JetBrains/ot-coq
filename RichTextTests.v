Require Import Commons Tree OtDef RichText String Basics.
Require Import mathcomp.algebra.ssrint.
Require Import ListTools.

Import intZmod.

Instance intOT : OTBase int int
 := {interp := (fun c m => Some (addz m c)); it := (fun o1 o2 f => [:: o1])}.
 rewrite /exec_all /flip /= => m n _ x x1 x2 [] <- [] <-; split. by rewrite -addzA (addzC n) -addzA. eauto.
Defined.

Instance intIP : OTInv _ _ intOT := {inv := (fun x => oppz x)}.
 move=> m x xr [] <- /=. by rewrite -addzA (addzC m) addNz addzC add0z.
Defined.

Definition nattree := tree nat.
Definition inttree := tree int.

Definition nat_tree_to_int_tree (x : nattree) : inttree :=
match decode (map (fun (n : option nat)=> match n with Some n' => Some (Posz n') | _ => @None int end) (encode x))
with Some n => n | _ => Node (Posz 0) nil end.

Definition test_model : inttree :=  nat_tree_to_int_tree
(Node 1 [::
        Node 2 [::
               Node 3 [:: Node 4 nil; Node 5 nil];
               Node 6 nil];
        Node 7 nil;
        Node 8 [:: 
               Node 9 [:: Node 10 nil; Node 11 nil];
               Node 12 nil]]).

Fixpoint read {X : eqType} (t : tree X) (idx : seq nat) :=
 match t, idx with 
  Node x ls, i :: xs => 
    match nth i ls with
      Some t' => read t' xs 
      | None => None 
    end 
  | _, nil => Some t end.

Fixpoint list_gen (range len : nat) : list (list nat) :=
 match len with
   0 => (fix f1 (n : nat) : list (list nat) :=
        match n with 0 => [::[::0]] | S n' => [::n] :: (f1 n') end) range
   | S len' => (fix f2 (n : nat) := 
     match n with
       | 0 => map (fun xs => 0 :: xs ) (list_gen range len') 
       | S n' => (map (fun xs => n :: xs ) (list_gen range len')) ++ (f2 n') 
     end) range
 end.

Fixpoint list_gen' (range len : nat) : list (list nat) :=
match len with
  0 => list_gen range len
  | S len' => (list_gen range len) ++ (list_gen' range len')
end.

Fixpoint ei (nc : int) (idx : seq nat) :=
 match idx with
   nil => @JEditLabel int_eqType int nc
   | n :: ns => JOpenRoot n (ei nc ns)
 end.

Fixpoint li l (idx : seq nat) :=
 match idx with
   nil => @JEditLabel int_eqType int (Posz O)
   | [:: n] => JInsert n l
   | n :: ns => JOpenRoot n (li l ns)
 end.

Fixpoint create_lst (n : nat) (m : nat) :=
 match n with 
   0 => nil
   | S n' => rcons (create_lst n' m) (m + n')
 end.

Fixpoint filt (x : seq (option (tree int_eqType))) :=
match x with 
 | [:: Some l] => Some [:: l]
 | (Some l) :: ls => 
   match (filt ls) with
     | Some ls' => Some (l :: ls')
     | _ => None
   end
 | _ => None
end.

Fixpoint ri (t : tree int_eqType) (idx : seq nat) (count : nat) :=
 match idx with
   nil => None
   | [:: n] => match (filt (map (fun k => read t [:: k]) (create_lst count n))) with 
                 Some l => Some (JRemove n l)
                 | _ => None end
   | n :: ns => 
     match read t [:: n] with 
      Some x =>
       match (ri x ns count) with
        Some cmd => Some (@JOpenRoot int_eqType int n cmd)
       | _ => None
       end
      | None => None
     end
 end.

Fixpoint ui (t : tree int_eqType) (idx : seq nat) (p : int * nat) :=
 let (x, count) := p in
 match idx with
   nil => None
   | [:: n] => match (filt (map (fun k => read t [:: k]) (create_lst count n))) with 
                 Some l => Some (JUnite n x l)
                 | _ => None end
   | n :: ns => 
     match read t [:: n] with 
      Some x =>
       match (ri x ns count) with
        Some cmd => Some (JOpenRoot n cmd)
       | _ => None
       end
      | None => None
     end
 end.

Fixpoint fi (t : tree int_eqType) (idx : seq nat) :=
  match idx, t with
   nil, _ => None
   | [:: n], Node x ls =>
                 match nth n ls with 
                  (Some t') => Some (JFlat n t')
                  | _ => None end
   | n :: ns, Node x ls => 
                 match nth n ls with
                  (Some t') => match fi t' ns with
                                Some cmd => Some (@JOpenRoot int_eqType int n cmd)
                                | None => None
                               end
                  | None => None
                 end
  end.

Definition all_indices := list_gen' 3 3.

Definition filter_applicable := filter (fun x => match jinterp int x (test_model) with Some _ => true | _ => false end).

Definition unite_ops := flatten (map (fun x => match x with None => nil | Some x' => [::x'] end) 
(allpairs 
 (ui test_model) all_indices [seq (x, y) | x <- [:: Negz 1; Posz 1], y <- (create_lst 3 0)])).

Definition remove_ops := flatten (map (fun x => match x with None => nil | Some x' => [::x'] end) 
                         (allpairs (ri test_model) all_indices (create_lst 3 0))).

Definition insert_ops := (map (li [::Node (Posz 100) nil]) all_indices) ++ (map (li [::Node (Posz 100) nil; Node (Posz 101) nil]) all_indices).

Definition edit_ops := (map (ei (Posz 10)) all_indices) ++ (map (ei (Negz 2)) all_indices).

Definition flat_ops := flatten (map (fun x => match x with None => nil | Some x' => [::x'] end) 
 (map (fi test_model) all_indices)).

Definition ops := filter_applicable (remove_ops ++ insert_ops ++ edit_ops ++ flat_ops ++ unite_ops).

Eval compute in size ops.

Open Scope string_scope.

Definition jt := @jit int_eqType int intOT.
Definition jp := @jinterp int_eqType int intOT.

Definition run_test (o : (jcmd int) * (jcmd int)) :=
  let (op1, op2) := o in
  let (op1', op2') := (jt op1 op2 true, jt op2 op1 false) in
  match jp op1 test_model, jp op2 test_model with
    | _ , None | None, _ => None
    | Some tm1, Some tm2 =>
    let (tm12, tm21) := (exec_all jp (Some tm1) op2', exec_all jp (Some tm2) op1') in
    if [|| tm12 == None, tm21 == None | ~~(tm12 == tm21)] then 
      Some ("OP1=", op1, "OP2=", op2, "OP1'=", op1', "OP2'=", op2', "M1=", tm1, "M2=", tm2,
             "OP1'=", op1', "OP2'=", op2', "M12=", tm12, "M21=", tm21) else None
  end.

Fixpoint run_suite tests :=
 match tests with
  t :: ts => match run_test t with
               None => run_suite ts
               | Some o => Some o
             end
  | _ => None
 end.

Eval compute in run_suite (allpairs (fun x y => (x, y)) ops ops).
Require Import Arith Commons ListTools Tree OtDef.

Section TreeOTDefinition.

Context {X : eqType} (cmd : Type) {ot : OTBase X cmd} {ip : OTInv _ _ ot}.

Inductive list_command : Type := 
 | TreeInsert of nat & seq (tree X)
 | TreeRemove of nat & seq (tree X)
 | EditLabel  of cmd.

Inductive tree_command : Type :=
 | Atomic of list_command
 | OpenRoot of nat & tree_command.

Fixpoint list_inv (c : list_command) :=
match c with
  | TreeInsert n l => TreeRemove n l
  | TreeRemove n l => if l is [::] then TreeInsert 0 [::] else TreeInsert n l
  | EditLabel c    => EditLabel (@inv X cmd ot ip c)
end.

Fixpoint tree_inv (c : tree_command) :=
match c with
  | Atomic c => Atomic (list_inv c)
  | OpenRoot n c => OpenRoot n (tree_inv c)
end.

Definition list_interp (op1 : list_command) (tr : tree_eqType X) : option (tree X) :=
match tr with Node x ls =>
 match op1 with
  | TreeInsert n l => NodeW x (ins n l ls)
  | TreeRemove n l => NodeW x (rm n l ls)
  | EditLabel c    => match @interp X cmd ot c x with Some x' => Some (Node x' ls) | _ => None end
 end 
end.

Fixpoint tree_interp (op1 : tree_command) (tr : tree_eqType X) : option (tree X) :=
match tr with Node x ls =>
 match op1 with
  | OpenRoot n c => NodeW x (rplc n (bind (tree_interp c) (nth n ls)) ls)
  | Atomic c => list_interp c tr
 end 
end.

Definition tr_ins (len : nat) (n1 n2 : nat) := 
 if (n1 < n2) then n1 else n1 + len.

Definition tr_rem (len : nat) (n1 n2 : nat) := 
 if (n1 < n2) then Some n1 else if (n1 >= n2 + len) then Some (n1 - len) else None.

Definition list_it (op1 op2 : list_command) (flag : bool) : seq list_command :=
match op1, op2 with
  | EditLabel c1, EditLabel c2 => map EditLabel (it c1 c2 flag)
  | EditLabel _, _ | _, EditLabel _ => [:: op1]

  | TreeInsert n1 l1, TreeInsert n2 l2 =>
    if (n1 == n2) then (if flag then [:: op1] else [:: TreeInsert (n1 + size l2) l1])
                  else [:: TreeInsert (tr_ins (size l2) n1 n2) l1]
  | TreeInsert n1 l1, TreeRemove n2 l2 =>
    let len := size l2 in
    if (n1 <= n2) then [:: op1] else (if (n1 >= n2 + len) then [:: TreeInsert (n1 - len) l1] else nil)

  | TreeRemove n1 l1, TreeRemove n2 l2 =>
    let (len1, len2) := (size l1, size l2) in
     if n2 + len2 <= n1 then [:: TreeRemove (n1 - len2) l1] 
     else if n1 + len1 <= n2 then [:: TreeRemove n1 l1] 
     else if n2 <= n1 then [:: TreeRemove n2 (cut l1 0 (len2 + n2 - n1))]
     else [:: TreeRemove n1 (cut l1 (n2 - n1) len2)]   
  | TreeRemove n1 l1, TreeInsert n2 l2 =>
    let (len1, len2) := (size l1, size l2) in
     if (n1 + len1 <= n2) then [:: op1] 
     else if (n2 <= n1) then [:: TreeRemove (n1 + len2) l1] 
     else match ins (n2 - n1) l2 l1  with
            | Some l1' => [:: TreeRemove n1 l1'] 
            | None => [:: op1] (* <- this branch is unused *)
     end
end.

Fixpoint tree_it (op1 op2 : tree_command) (flag : bool) : seq tree_command :=
match op1, op2 with
  | Atomic c1, Atomic c2 => map Atomic (list_it c1 c2 flag)

  | OpenRoot n1 tc1, OpenRoot n2 tc2 =>
    if n1 == n2 then map (OpenRoot n1) (tree_it tc1 tc2 flag) else [:: op1]
  | Atomic (TreeRemove n1 l1), OpenRoot n2 tc2 =>
    match tr_rem (size l1) n2 n1 with
      None => let i := n2 - n1 in 
      match rplc i ((bind (tree_interp tc2)) (nth i l1)) l1 with
        | Some l1' => [:: Atomic (TreeRemove n1 l1')]
        | _ => [:: op1]
      end
      | _ => [:: op1]
    end

  | OpenRoot n1 tc1, Atomic (TreeInsert n2 l2) => [:: OpenRoot (tr_ins (size l2) n1 n2) tc1]
  | OpenRoot n1 tc1, Atomic (TreeRemove n2 l2) => 
    match tr_rem (size l2) n1 n2 with
     | Some n1' => [:: OpenRoot n1' tc1]
     | None     => nil
    end

  | _, _ => [:: op1]
end.

Ltac inspect_nodew := repeat let x := fresh "HN" in let y := fresh "HN" in 
match goal with
 | |- (NodeW _ _ = Some (Node _ _) -> _) => rewrite nodew_some => [] [] x y; rewrite x - y
 | |- (Some (Node _ _) = NodeW _ _ -> _) => rewrite nodew_someS => [] [] x y; rewrite - x y
end.

Lemma Atomic_map_if f o1 o2: map Atomic (if f then o1 else o2) = if f then map Atomic o1 else map Atomic o2.
by destruct f. Qed.

Ltac interp_simpl := 
 rewrite ?Atomic_map_if //= /foldl /flip /= /tr_ins ?orm_id ?rm_id ?orplc_some ?oins_some ?orm_some.
Ltac interp_simpl_nw := interp_simpl; inspect_nodew.

(* Auxilary arithmetic lemmas *)
Lemma arithm1 {x y z} : x + z <= y -> y <= x = false -> y = y - z + z /\ x <= y - z.
Proof. move=> H1 H2. 
by move: (H1) => /(leq_sub2r z); rewrite -addnBA // subnn addn0;
   move: H1 => /(leq_trans (leq_addl _ z)) /subnK. 
Qed.

Lemma arithm1' {x y z} : x + z <= y -> y < x = false -> y = y - z + z /\ x <= y - z.
Proof. move=> H1 H2. 
by move: (H1) => /(leq_sub2r z); rewrite -addnBA // subnn addn0;
   move: H1 => /(leq_trans (leq_addl _ z)) /subnK. 
Qed.

Lemma arithm2 {x y z} : y + z <= x -> x = z + (x - z) /\ y <= (x - z).
Proof. move=> H1.
move: (H1) => /(leq_trans (leq_addl _ z)) /subnK. 
by move: H1 => /(leq_sub2r z); rewrite -addnBA ?subnn ?addn0 1?addnC; [|exact: leqnn]. 
Qed.

Lemma foldl_openroot (x : X) xs cs n: n < size xs ->
(exec_all tree_interp) (Some (Node x xs)) [seq OpenRoot n i | i <- cs]
= NodeW x (rplc n ((exec_all tree_interp) (nth n xs) cs) xs).
Proof. elim: cs xs => [|c cs IHcs] xs /=.
 + case Hnth: nth => [y|]; rewrite -Hnth; move: Hnth.
    * by move=> /rplc_nth_id' ->.
    * by move /nth_noneP; rewrite ltnNge; case: leq.
 + move=> Hsz. rewrite ?/flip => /=. 
   move A0: (bind (tree_interp c) (nth n xs)) => [t|] /=.
 + case A1: rplc => [t'|] /=.
     rewrite IHcs.
     * move: (A1) => /rplc_nth_eq ->.
       case: exec_all => /= [a|]; last by rewrite ?rplc_none_none /=.
       move: A1. rewrite ?orplc_some => <-. by rewrite rplc_rplcC_eq. 
     * by move: A1 A0 => /rplc_some_len <-; rewrite ltnNge; case: nth (nth_noneP n xs) => ? [].
  +  by move: A1 A0 => /rplc_none_case [] // /nth_noneP ->.
 + by rewrite rplc_none_none ?exec_all_none rplc_none_none. Qed.

Lemma foldl_editroot (x : X) xs cs:
(exec_all tree_interp) (Some (Node x xs)) [seq Atomic (EditLabel i) | i <- cs] = 
  match ((exec_all interp) (Some x) cs) with
   | Some x' => Some (Node x' xs)
   | None => None
  end.
Proof. elim: cs x xs => [|c cs IHcs] x xs //=. rewrite /flip /=.
 case Hint: interp => [x'|] //. by rewrite ?exec_all_none. Qed.

Lemma insert_remove_commutation: 
forall n1 l1 x ls (m1 m2 : tree X)  (f g: bool) (n : nat) l,
   NodeW x (ins n1 l1 ls) = Some m1 ->
   NodeW x (rm n l ls) = Some m2 ->
   (exec_all tree_interp) (Some m2)
     (tree_it (Atomic (TreeInsert n1 l1)) (Atomic (TreeRemove n l)) f) =
   (exec_all tree_interp) (Some m1)
     (tree_it (Atomic (TreeRemove n l)) (Atomic (TreeInsert n1 l1)) g)
   /\ exists os, (exec_all tree_interp) (Some m2)
     (tree_it (Atomic (TreeInsert n1 l1)) (Atomic (TreeRemove n l)) f) = Some os.
Proof. move => n1 l1 x ls [x1 ls1] [x2 ls2] _ _ n2 l2 //=; 
    case H1: (n2 + size l2 <= n1); case H2: (n1 <= n2).
   - case: l2 H1 => [|y2 ys2] //= H1; interp_simpl_nw => /=;
     first (move: HN0 => /= ->; split => //; by exists (Node x2 ls1)).
     move: H1; rewrite addnS => /(ltn_addr (size ys2)); rewrite ltnNge;
     move: H2; by rewrite -(leq_add2r (size ys2)) => ->.
   - interp_simpl_nw; move: (arithm1 H1 H2) HN0 HN2 => [] {2 4}-> /rm_insC_bef A. 
     rewrite addnC => /A B /B [] <- [os] => ->. split => //. by exists (Node x2 os).
   - interp_simpl. move: H2 => /rm_insC_aft A /nodew_some [] -> Heq'. 
     move:(Heq') =>/A B /nodew_some [] -> Heq''. move:(Heq'') => /B []. 
    rewrite addnC -Heq'' -Heq' /= =>-> [os] ->. split => //. by exists (Node x2 os).
   - move: H2; rewrite leqNgt => /negbFE => H2;
     move: H1; rewrite leqNgt => /negbFE => H1;
     case Hins: (ins (n1 - n2)) => [rm_ins|]; interp_simpl_nw.
    + simpl; case Hins': ins => [rm_ins'|].
      rewrite (rm_insC_in n2 n1 _ l1 _ rm_ins rm_ins') 1?ltnW //= => ->. split => //. 
      by exists (Node x2 ls2).
      simpl in HN0; by rewrite HN0 in Hins'. 
    + move: Hins H1 => /ins_noneP; rewrite ltn_subRL. maxapply ltn_trans. by rewrite ltnn. Qed.

Lemma remove_openroot_commutation :  
forall n1 l1 x ls (m1 m2 : tree_eqType X) (f g: bool) (t : tree_command) (n : nat),
   NodeW x (rm n1 l1 ls) = Some m1 ->
   NodeW x (rplc n ((bind (tree_interp t)) (nth n ls)) ls) = Some m2 ->
   (exec_all tree_interp) (Some m2)
     (tree_it (Atomic (TreeRemove n1 l1)) (OpenRoot n t) f) =
   (exec_all tree_interp) (Some m1)
     (tree_it (OpenRoot n t) (Atomic (TreeRemove n1 l1)) g) 
   /\ exists os, 
     (exec_all tree_interp) (Some m2) (tree_it (Atomic (TreeRemove n1 l1)) (OpenRoot n t) f) = Some os.
Proof. move=> n1 l1 x ls [x1 ls1] [x2 ls2] _ _ t n2 //=; case Htr_rem: tr_rem => [n|]. 
   + interp_simpl_nw. move: Htr_rem; rewrite /tr_rem; case H1: (n2 < n1).
    - move=> [] <-; rewrite (rm_some_nth_aft _ ls _ l1 n1) //.
      move: HN2. case: (bind (tree_interp t)) => //= [a|]; last by rewrite rplc_none_none.
      move => /rplc_some []. move => _1 _2; move: _2 _1 => _. move: HN0 => /=. move: H1. 
      maxapply (@rplc_rmC_bef (tree_eqType X)) => /(_ a) [] -> [os] -> /=. by eauto.
    - case H2: (n1 + size l1 <= n2) => //. move=> [] <-; 
      move: (arithm1'  H2 H1) HN2 => [] {2 3 4 5 8 9}-> Hleq. 
      simpl in HN0. rewrite (rm_some_nth_bef n1 ls _ l1 (n2 - size l1)) //.
      case: (bind (tree_interp t)) => [a /=|]; last by rewrite orplc_none //=.
      move=> /rplc_some []. move => _1 _2; move: _2 _1 => _. rewrite addnC. move: Hleq HN0.
      maxapply (@rplc_rmC_aft (tree_eqType X)) => /(_ a) [] -> [os] -> /=. by eauto.
   + move: Htr_rem; rewrite /tr_rem; case H1: (n2 < n1) => //; 
     case H2: (n1 + size l1 <= n2) => // ?. move:H1 => /negbT. rewrite -leqNgt => H1; 
     move: H2 => /negbT. rewrite -ltnNge => H2. case Hrplc: (rplc (n2 - n1)) => [l1'|] //=;
     interp_simpl_nw => /nodew_some [] <- Hrm_some; 
     move: (H1) (H2) => /subnKC {1 2 3}<-;
     rewrite ltn_add2l => H2'; rewrite addnC (rm_some_nth_in ls1 l1) => //. 
     - inspect_nodew.
       rewrite nodew_some; simpl in Hrm_some. rewrite (rplc_rmC_in ls1 _ l1) /=; try by eauto.
     - by move: Hrplc; rewrite rplc_none_case; move: H2'; rewrite ltnNge => /negbTE -> /=;
       case: (bind (tree_interp t)) => [? [] //|] //; rewrite rplc_none_none. Qed.

Lemma insert_openroot_commutation: 
forall n1 l1 x ls (m1 m2 : tree X) (n : nat) (t : tree_command),
   NodeW x (rplc n (bind (tree_interp t) (nth n ls)) ls) = Some m2 ->
   NodeW x (ins n1 l1 ls) = Some m1 ->
   flip tree_interp m2 (Atomic (TreeInsert n1 l1)) =
   flip tree_interp m1
     (OpenRoot (tr_ins (size l1) n n1) t)
   /\ exists node, flip tree_interp m2 (Atomic (TreeInsert n1 l1)) = Some node.
Proof.
 move=> n1 l1 x ls // [x1 ls1] [x2 ls2] n t /=. rewrite /flip /= /tr_ins.
 case Hltn: (n < n1); [|move: Hltn; rewrite leqNgt ltnS => /negbFE Hltn]; 
 rewrite ?nodew_some => [] [] <- Hrplc; move: (Hrplc); 
 rewrite (oins_some _ _ ls2) => <- [] <- => H2;
 [rewrite (ins_some_nth_aft ls l1 n1) | 
  move: Hrplc; rewrite (ins_some_nth_bef ls1 l1 n1) // => Hrplc];
 interp_simpl => //; rewrite -H2.
 * move: H2 => /ins_some [] _. move: Hltn. move=> /rplc_insC_bef A /A B.
   case: (bind (tree_interp t)) Hrplc => [ti_r|]. move: (B ti_r l1) => [] <- [os] ->. 
   split=> //. by exists (Node x os).
   by rewrite orplc_some orplc_none.
 * rewrite addnC addnC.
   case: (bind (tree_interp t)) Hrplc => [ti_r|]; last by rewrite orplc_some orplc_none.
   move: Hltn => /rplc_insC_aft A => /rplc_some [] /A B _. 
   move: (B ti_r l1) => [] -> [os] ->. split=> //. by exists (Node x os). Qed.

Theorem tree_c1 : forall (op1 op2 : tree_command) (f : bool) m (m1 m2 : tree X),
  tree_interp op1 m = Some m1 -> tree_interp op2 m = Some m2 -> 
  (exec_all tree_interp) (Some m2) (tree_it op1 op2 f) 
  = (exec_all tree_interp) (Some m1) (tree_it op2 op1 (~~f)) /\ 
  exists node, (exec_all tree_interp) (Some m2) (tree_it op1 op2 f) = Some node.
Proof. 

Ltac solve_openroot :=  interp_simpl; let X1 := fresh "X1" in let X2 := fresh "X2" in
    case X1: interp => [?|] // [] <- <-; rewrite nodew_some => [] [] <- ->;
    case X2: interp => [?|] //; move: X1 X2 => -> // [] ->; eauto.

elim => [[n1 l1 | n1 l1 | c1 ]| n1 c1 IHl1] [[n2 l2 | n2 l2 | c2] | n2 c2]
     => f [x ls] [x1 ls1] [x2 ls2] //=.

 (* Case op1 = insert *)
  *  case Heq: (n1 == n2); rewrite eq_sym Heq.
   - case: f => /=; interp_simpl; move: Heq; 
     rewrite eqn_leq => /andP [] => H1 H2; inspect_nodew; rewrite addnC ?oins_some; 
     [move: H1| move: H2] => /ins_insC A; [move: HN2| move: HN0] => /= /ins_some [] _ /A A';
     [move: (A' l1 l2)| move: (A' l2 l1)] => [] [] -> [os]; split => //; exists (Node x2 os);
     by rewrite p.
   - rewrite /tr_ins (ltnNge n2 n1) (leq_eqVlt n1 n2) Heq. 
     case Hn12: (n1 < n2) => /=; interp_simpl; inspect_nodew; rewrite addnC; move: Hn12; 
     [move=> /ltnW | rewrite ltnNge => /negbFE] => /ins_insC A;
     [move: HN2| move: HN0] => /= /ins_some [] _ /A A'; [move: (A' l1 l2)| move: (A' l2 l1)];
     move=> [] -> [os]; split => //; exists (Node x2 os); by rewrite p.
  *  move=> /insert_remove_commutation A /A B. move: (B f (~~ f)) => /= [] -> [os] ->.
     split => //. by exists os.
  * interp_simpl. case Hx: interp => [intx|] // Hins [] <- <-. 
    move: Hins => /nodew_some [] <- ->. split; by [rewrite Hx| exists (Node intx ls1)].
  *  move=> H1 /= /insert_openroot_commutation A. by move: H1 => /A. 
 (* Case op1 = remove *)
  * move=> /insert_remove_commutation A /A B. move: (B (~~f) f) => [] -> [os] ->.
    split => //. by exists os.
  * case H1: (n2 + size l2 <= n1); case H2: (n1 + size l1 <= n2); 
    interp_simpl; inspect_nodew.
   + case: l1 HN0 H2 => [|y1 ys1] Hsome1 //=.
    - case: l2 HN2 H1 => [|y2 ys2] Hsome2 //.
     * rewrite ?addn0 => H' H''. move/andP: (conj H' H''). 
       rewrite -eqn_leq rm_id orm_id => /eqP -> /=. rewrite rm_id orm_id. split => //.
       by exists (Node x2 ls).
     * rewrite addn0 addnS => H'. move: (leq_trans H' (leq_addr (size ys2) _)).
       by rewrite ltn_add2r ltnNge => /negP.
     rewrite addnS => H'. move: (leq_trans H' (leq_addr (size ys1) _)). rewrite ltn_add2r.
     move: (leq_trans H1 (leq_addr (size l2) _)). by rewrite leq_add2r leqNgt => /negP. 
   + move: (arithm2 H1) HN0 HN2 => [] {2}-> /rm_rmC A/A B/B [].
     move: H1 => /leq_addWl /(addnBA (size l2)) ->. rewrite addnC. 
     rewrite -addnBA; last exact: (leqnn _). rewrite subnn addn0 /= => -> [os] -> /=. by eauto.
   + move: (arithm2 H2) HN0 HN2 => [] {2}-> /rm_rmC A/A B/B [].
     move: H2 => /leq_addWl /(addnBA (size l1)) ->. rewrite addnC.      
     rewrite -addnBA; last exact: (leqnn _). rewrite subnn addn0 /= => -> [os] -> /=. by eauto.
   + case H3: (n2 <= n1); case H4: (n1 <= n2) => /=; rewrite /bind /flip /tree_interp;
     rewrite ?orm_some; interp_simpl; inspect_nodew; move: HN0 HN2.
     - move/andP: (conj H3 H4). rewrite -eqn_leq => /eqP ->.
       move=> /rm_cut A /A B. move: (B (leqnn _) (leq_addr _ _)).
       rewrite addnC subnn => [] [] /= -> [os]. rewrite -subnBA; last exact: (leqnn _).
       rewrite subnn subn0 => -> /=. by eauto.
     - move => _1 _2; move: _2 _1. move=> /rm_cut A /A B. move: H1 => /negbT. rewrite -ltnNge => /ltnW => /B C.
       move: (C H3) => []. rewrite addnC => -> [os] -> /=. by eauto.
     - move=> /rm_cut A /A B. move: H2 => /negbT. rewrite -ltnNge => /ltnW => /B C.
       move: (C H4) => []. rewrite addnC => -> [os] -> /=. by eauto.
     - move: (leq_total n1 n2). by rewrite H3 H4. 
  * rewrite nodew_some => [] [] <- Hrm. case Hint: interp => [c'|//]. interp_simpl_nw. 
    case Hint': interp => [c'' //|//] [] <- <-; rewrite -orm_some Hrm;
    move: Hint Hint' -> => [] [] // -> //=. by eauto.
  * maxapply remove_openroot_commutation => /(_ f (~~f)) /= [] -> [os] ->. by eauto.
 (* Case op1 = editLabel *)
  * by solve_openroot.
  * by solve_openroot.
  * case Hint1: interp => [x'|] // [] <- <-; case Hint2: interp => [x''|] // [] <- <-; 
    rewrite -?map_comp ?foldl_editroot /=. move: Hint1 Hint2. maxapply (@it_c1 X cmd) => /(_ f) /= [] -> [os] ->.
    by eauto.
  * by solve_openroot.

 (* Case op1 = open root *)
  * maxapply insert_openroot_commutation. rewrite /flip /= => [[] <-]. by eauto.
  * maxapply remove_openroot_commutation => /(_ (~~f) f) => [] [] -> [os] ->. by eauto.
  * interp_simpl. rewrite nodew_some => [] [] <-.
    case: interp => [x'|] // Hrplc [] <- <-. rewrite Hrplc /=. by eauto.

  * case Heq: (n1 == n2); rewrite ?1eq_sym Heq.
   + move/eqP: Heq ->.
     let sol := fun m ls => 
       let H := fresh 
       with Hleq := fresh "Hleq" 
       with Heq := fresh "Heq" in
      (rewrite nodew_some => [] [] <- A;
       move: (A) => /rplc_some_len Heq; move: (A) => /rplc_some []; move: (Heq) => -> Hleq [m] H;
       rewrite (foldl_openroot x) //; move: (A); 
       rewrite (orplc_some _ _ ls) H => /rplc_nth_eq ->; move: A => <-; 
       rewrite H (orplc_some _ (Some m)) rplc_rplcC_eq) in (sol m ls1; sol m' ls2).
     case B1: (nth n2 ls) H H0 => //=; maxapply IHl1 => /(_ f) [] -> [node] ->. split => //=.
     case Hrplc: rplc => [a|]; first by exists (Node x a). 
     by move: Hrplc Hleq => /rplc_noneP1; rewrite ltnNge Heq; case leq.
     
     interp_simpl_nw. rewrite eq_sym in Heq. rewrite rplc_rplcC_neq //. move: (HN0) (HN2).
     move=> /negbT in Heq. simpl in HN0, HN2.
     rewrite ?(rplc_nth_neq n2 n1 _ ls1 ((bind (tree_interp c1)) (nth n1 ls))) //.
     rewrite eq_sym in Heq.
     rewrite ?(rplc_nth_neq n1 n2 _ ls2 ((bind (tree_interp c2)) (nth n2 ls))) //.
     split => //. move: HN3 => /= /rplc_some [] Hlt' [e'] ->.
     case Hrplc: rplc => [a|]. move: Hrplc => /rplc_some_len Heqsz.
     case: (bind (tree_interp c2)) HN4 => [b _|] //=; last by rewrite rplc_none_none.
     case Hrplc': rplc => [a'|]. 
    - by exists (Node x2 a').
    - move: Hrplc' => /rplc_noneP1; move: HN2 => /rplc_some []. move => _1 _2; move: _2 _1 => _.
      rewrite Heqsz. by maxapply Nleq_ltnC.
    - move: Hrplc => /rplc_noneP1. move: HN0 => /rplc_some []. move => _1 _2; move: _2 _1 => _.
      by maxapply Nleq_ltnC.
Qed.

Theorem tree_ip1: forall (op : tree_command) m mr, 
tree_interp op m = Some mr -> 
tree_interp (tree_inv op) mr = (Some m).
Proof.
 elim => [[n l | n l | c]| n c IHc] [x ls] [xr lrs] //=.
 + by move=> /nodew_some [] <- /rm_ins_id ->.
 + case: l => [|x1 l1]; first by rewrite rm_id /= => ->.
   have: (0 < size (x1 :: l1)); first by exact (ltn0Sn _).
   move => _1 _2; move: _2 _1 => /nodew_some [] <-. maxapply (@ins_rm_id (tree_eqType X)). by move=> /= ->.
 + case Hint: interp => [a|] // [] <- <-. apply ip1 in Hint. by rewrite Hint.
 + move=> /nodew_some [] <-. case Hti: (bind (tree_interp c)) => [ti_r|]; last by rewrite rplc_none_none.
   move: Hti. case Hnth: nth => [nth_r|]; last by simpl.
   move=> /IHc. move => _1 _2; move: _2 _1. move => Hrplc. move: (Hrplc) => /rplc_nth_eq => ->. rewrite /bind => ->.
   rewrite orplc_some -Hrplc -Hnth orplc_some rplc_rplcC_eq. 
   case Horplc: orplc => [a|]. 
  - move: (Horplc) (Horplc). move /rplc_nth_id -> => //.
  - move: Horplc => /= /rplc_none_case []; first by rewrite Hnth.
    move: Hrplc => /rplc_some []. move => _1 _2; move: _2 _1 => _. by maxapply Nleq_ltnC.
Qed.

Instance treeOT: (OTBase (tree X) tree_command) := {interp := tree_interp; it := tree_it; it_c1 := tree_c1}.
Instance treeInv: (OTInv (tree X) tree_command treeOT) := {inv := tree_inv; ip1 := tree_ip1}.

End TreeOTDefinition.

Section Sandbox.

Require Import Comp.

Implicit Arguments TreeInsert [[cmd] [X]].
Implicit Arguments TreeRemove [[cmd] [X]].
Implicit Arguments OpenRoot [[cmd] [X]].
Implicit Arguments Atomic [[cmd] [X]].

Instance unitOT : OTBase nat_eqType unit := {interp := (fun c m => Some m); it := (fun _ _ _ => [:: tt])}.
move => _ _ _ m m1 m2 [] <- [] <- /=. split. done. exists m. by rewrite /flip. Qed.
Definition it1 := transform (@tree_it nat_eqType unit unitOT).

Definition abclist := [:: Node 10 [::]; Node 11 [::]; Node 12 [::]].
Definition abc := Node 1 abclist.
Definition efg := Node 2 [:: Node 14 [::]; Node 15 [::]; Node 16 [::]].

Eval compute in it1 [:: Atomic (TreeRemove 1 [::efg]); OpenRoot 0 (Atomic (TreeInsert 3 abclist))] 
 [::OpenRoot 0 (Atomic (TreeInsert 3 [:: Node 13 [::] ])); OpenRoot 1 (Atomic (TreeInsert 3 [:: Node 17 [::]]))] 100.

End Sandbox.

Section SplitMerge.

Context {X : eqType} (cmd : Type) {ot : OTBase X cmd} {ip : OTInv _ _ ot}.

Inductive tree_command_ext : Type :=
 | Atomic1 of @list_command X cmd
 | OpenRoot1   of nat & tree_command_ext
 | Split of nat & nat & X
 | Merge of nat & nat & X.

Fixpoint tree_inv_ext (c : tree_command_ext) :=
match c with 
  | Atomic1 c1 => Atomic1 (@list_inv X cmd ot ip c1)
  | Split n k c => Merge n k c 
  | Merge n k c => Split n k c
  | OpenRoot1 n c   => OpenRoot1 n (tree_inv_ext c)
end.

Fixpoint tree_it_ext (op1 op2 : tree_command_ext) (flag : bool) : seq tree_command_ext :=
match op1, op2 with
 _, _ => [:: op1]
end.

End SplitMerge.
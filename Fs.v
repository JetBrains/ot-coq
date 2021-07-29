Require Import mathcomp.ssreflect.path.
Require Import Commons Tree OtDef ListTools Comp SortedTree.
Import Bool.

Section FilesystemOT.

Parameter T : eqType.
Parameter R : rel T.
Parameter Rord : order R.

Inductive raw_fs_cmd :=
 | RawEdit   of T & T
 | RawCreate of tree T
 | RawRemove of tree T
 | RawOpen   of T & raw_fs_cmd.

Fixpoint raw_fs_inv (cmd : raw_fs_cmd) :=
  match cmd with
  | RawOpen l c => RawOpen l (raw_fs_inv c)
  | RawEdit l k => RawEdit k l
  | RawCreate t => RawRemove t
  | RawRemove t => RawCreate t
  end.

Fixpoint eq_cmd (t1 t2 : raw_fs_cmd) : bool :=
match t1, t2 with
  | RawOpen l c, RawOpen l2 c2 => (l == l2) && (eq_cmd c c2)
  | RawEdit l k, RawEdit l2 k2 => (l == l2) && (k == k2)
  | RawCreate t, RawCreate t2 => (t == t2)
  | RawRemove t, RawRemove t2 => (t == t2)
  | _, _ => false end.

Lemma eq_cmdK: @Equality.axiom raw_fs_cmd eq_cmd.
elim => [l k | t | t | l c IH] [l2 k2| t2| t2| l2 c2] /=;
(try by constructor); repeat (case A0: (eq_op _ _) => /=; move: A0 => /eqP);
try constructor; subst => // A; try by case: A.
 + subst. case A0: (eq_cmd); move: A0 => /IH;
   constructor; subst => // A. by case: A. Qed.

Canonical cmd_eqMixin := EqMixin eq_cmdK.
Canonical cmd_eqType := Eval hnf in EqType raw_fs_cmd cmd_eqMixin.

Ltac correct_label A := let H := fresh "H" in 
  move: (find_pred A) => H; rewrite /by_value /= in H; move: H => /eqP H; subst.
Ltac correct_interp_label A := let A' := fresh A in 
 (assert (A':=A); move: A' => /interp_label_indep /= A'; move: A; rewrite ?A' => [] [] A; subst).

Section FsCmd.

Inductive fs_cmd :=
 | Edit   of T & T
 | Create (c : sorted_tree R)
 | Remove (c : sorted_tree R)
 | Open   of T & fs_cmd.

Fixpoint fs_to_raw_fs (c : fs_cmd) : raw_fs_cmd := 
 match c with
 | Edit l k => RawEdit l k
 | Create c => RawCreate (treeOf c)
 | Remove t => RawRemove (treeOf t)
 | Open l c => RawOpen l (fs_to_raw_fs c)
 end.

Fixpoint fs_inv (cmd : fs_cmd) :=
 match cmd with
 | Open l c => Open l (fs_inv c)
 | Edit l k => Edit k l
 | Create t => Remove t
 | Remove t => Create t
 end. 

End FsCmd.

Section Interpretation.

Fixpoint raw_fs_interp (c : raw_fs_cmd) (t : tree T) : option (tree T) :=
 let (v, cs) := t in let without v := filter (negb \o @by_value T v) in
 match c with
 | RawCreate  tc  => [! negb (has (by_value (value tc)) cs) !] Node v (insert R tc cs)
 | RawRemove  tr  => find (by_value (value tr)) cs >>= fun tr' => [! tr == tr' !] Node v (without' (value tr) cs)
 | RawOpen vo co  => open R (fun t => raw_fs_interp co t) vo t
 | RawEdit ve ve' => find (by_value ve) cs >>= fun te  =>
                     let cs' := without' ve cs in
                     match te with | Node _ cste =>
                       [! negb (has (by_value ve') cs') !]
                       Node v (insert R (Node ve' cste) cs') end end.

Lemma interp_label_preserving c: label_preserving (raw_fs_interp c).
move: c => [s s0|t |t |s r] [vt ts] /=.
 + by case find => [[]|] //=; case: has.
 + by case has.
 + by case find => [?|] //=; case eq_op.
 + by case find => [?|] //=; case raw_fs_interp. Qed.

Lemma interp_label_indep v cs v' (op : raw_fs_cmd) t : 
raw_fs_interp op (Node v cs) = Some t ->
raw_fs_interp op (Node v' cs) = Some (Node v' (children t)).
by case: op v v' cs t => [l l'|c |c |l op] v v' cs [vt cst] /=;
 [case: find => [[??]|] //=; case: has | case has | 
  case find => [?|] //=; case eq_op | case: bind => a]; move => //= [] [] ? ->. Qed.

Corollary interp_some c t t': raw_fs_interp c t = Some t' -> value t = value t'.
move: (interp_label_preserving c t); rewrite /label_preserving.
by case: (raw_fs_interp _ _) => [a <- [] <-|]. Qed.

Lemma raw_fs_interp_sorted c (t t' : tree T): is_tree_sorted R t -> 
      raw_fs_interp (fs_to_raw_fs c) t = Some t' -> is_tree_sorted R t'.
Ltac tc1 X := by (move: X => /= /andP []; try by rewrite -?sorted_compatibility).
elim: c t t' => [l k|t1 |t1 |l c IH] [v cs] [v' cs'] A0 /=; try rewrite /without' -lock.
 + case A1: find => [[v'' cs'']| //] /=; case A2: has => [] //= [] A3 <-.
   rewrite insert_all sorted_compatibility insert_sorted /=.
  * move: A1 => /(find_sorted R v) A1. assert (A0' := A0).
    move: A0 => /A1 /= /andP [] -> ->. rewrite ?andb_true_r. 
    apply all_filter. tc1 A0'. apply Rord.
  * apply sorted_filter. by expand_order (treeR_order _ Rord). tc1 A0.
 + move: t1 => [t1 H0]. case A1: has => //= [] [] ? <-.
   rewrite insert_all H0 sorted_compatibility insert_sorted.
   by move: A0 => /= /andP [] ? ->. apply Rord. tc1 A0. 
 + case A1: find => [] //=; case A2: eq_op => [] //= [] ? <-.
   apply /andP. split. 
   + rewrite sorted_compatibility. apply sorted_filter. by expand_order (treeR_order _ Rord). tc1 A0.
   + apply all_filter. tc1 A0.
 + case A1: find => [a|] //=. case A2: raw_fs_interp => [a'|] //= [] ? <-. assert (A0' := A0).
   move: A1 => /find_sorted A1. move: A0 => /(A1 R v) A0. move: A2 => /(IH _ _ A0) A2.
   rewrite sorted_compatibility insert_sorted /= ?insert_all ?A2 ?andb_true_r.
  * apply all_without. tc1 A0'. apply Rord.
  * apply without_sorted. apply Rord. tc1 A0'. Qed.

Corollary raw_fs_interp_sorted_all c t t':
 is_tree_sorted R t -> exec_all (raw_fs_interp \o fs_to_raw_fs) (Some t) c = Some t' -> is_tree_sorted R t'.
elim: c t => [|a c IH] t //=.
 + by move => A0 [] <-.
 + move => A0. rewrite /bind /flip. case A1: (raw_fs_interp (fs_to_raw_fs a) t) => [b|].
  + apply (IH b (raw_fs_interp_sorted _ _ _ A0 A1)).
  + by rewrite exec_all_none. Qed.

(* Inversion property IP1 *)
Theorem ip1 c x y: is_tree_sorted R x -> raw_fs_interp c x = Some y -> raw_fs_interp (raw_fs_inv c) y = Some x.
 elim: c x y=> [ s c | t | t | s c IH] [l0 cs0] [l cs] S; assert (S' := S); move: S' => /= /andP [] S0 S1; rewrite sorted_compatibility in S0.
 + case A0: find => [[v1 cs1]|] /=; case A1: has => [] //= [] <- <- {l} /=.
   rewrite /without' -lock in A1. sop_simpl => /=. correct_label A0. rewrite insert_same //. apply Rord.
 + case A0: has => [] //= [] <- <- {l} /=. by sop_simpl.
 + case A0: find => [[v1 cs1]|] //=. case A1: eq_op => //= [] [] <- <- {l}. move: A1 => /eqP A1; subst.
   sop_simpl => /=. rewrite insert_same //. apply Rord.
 + rewrite /bind /=. case A0: find => [[v1 cs1]|] //=. correct_label A0.
   case A1: raw_fs_interp => [[v2 cs2]|] // [] <- <- {l}. move: (IH _ _ (find_sorted R _ _ _ _ S A0) A1) => A1'.
   correct_interp_label A1'. sop_simpl. rewrite A1'0. rewrite insert_same //. apply Rord. Qed.

Lemma ip1_e v v' t mv mcs: sorted (treeR R) mcs ->
find (by_value v) mcs = Some t -> has (by_value v') (without v mcs) = false ->
(exec_all raw_fs_interp) (Some ((Node mv mcs))) ([:: RawEdit v v'; RawEdit v' v]) = Some (Node mv mcs).
move: t => [v1 cs1] S A0 A1 /=; rewrite /bind /flip /= A0 /without' -lock A1 /=. correct_label A0. sop_simpl.
rewrite /= insert_same //. apply Rord. Qed.

End Interpretation.

Section InsFs.

Inductive ins_cmd := 
 | Ins of T 
 | IOpen of T & ins_cmd.

Fixpoint ins_fs (cmd : ins_cmd) :=
 match cmd with
  | Ins t => RawCreate (Node t [::])
  | IOpen t c => RawOpen t (ins_fs c)
 end.

Fixpoint ins_fs' (cmd : ins_cmd) :=
 match cmd with
  | Ins t => Create (SNode R t)
  | IOpen t c => Open t (ins_fs' c)
 end.

Lemma ins_fs_inj: injective ins_fs.
by elim => [t1|t1 c1 IH] [t2|t2 c2] //= [] -> // /IH ->. Qed.

Fixpoint eq_ins (t1 t2 : ins_cmd) : bool :=
match t1, t2 with
  | IOpen l c, IOpen l2 c2 => (l == l2) && (eq_ins c c2)
  | Ins t1, Ins t2 => t1 == t2
  | _, _ => false
end.

Lemma eq_insK: @Equality.axiom ins_cmd eq_ins.
elim => [t | l c IH] [t2| l2 c2] /=;
(try by constructor); repeat (case A0: (eq_op _ _) => /=; move: A0 => /eqP); 
try constructor; subst => // A; try by case: A.
 + subst. case A0: (eq_ins); move: A0 => /IH;
   constructor; subst => // A. by case: A. Qed.

Canonical ins_eqMixin := EqMixin eq_insK.
Canonical ins_cmd_eqType := Eval hnf in EqType ins_cmd ins_eqMixin.

Fixpoint subdiv (t : tree T) : seq (raw_fs_cmd) :=
match t with Node v cs => RawCreate (Node v [::]) :: (map (fun y => RawOpen v y) (flatten (map subdiv cs))) end.

Fixpoint subdiv' (t : tree T) : seq (ins_cmd) :=
match t with Node v cs => Ins v :: (map (fun y => IOpen v y) (flatten (map subdiv' cs))) end.

Lemma sd_step1 t v1 v2: 
 exec_all raw_fs_interp t [:: RawCreate v1; RawCreate v2] = 
 exec_all raw_fs_interp t [:: RawCreate v2; RawCreate v1].
 rewrite /= /flip /=. case: t => [[t ts]|] //=.
 case A0: (has (by_value (value v1)) ts); case A1: (has (by_value (value v2)) ts) => //=;
 rewrite ?has_insert ?A0 ?A1 //= /by_value /= eq_sym insert_insert //. apply Rord. Qed.

Corollary sd_commutes t v vs:
  exec_all raw_fs_interp t (map (fun t => RawCreate t) (v :: vs)) = 
  exec_all raw_fs_interp t (map (fun t => RawCreate t) (rcons vs v)).

 elim: vs v t => [|v0 vs IH] v t //. rewrite 2!map_cons 2!exec_all_ind.
 move: (sd_step1 t v0 v) => A1; rewrite /= /flip in A1.
 rewrite -A1. remember (bind (raw_fs_interp (RawCreate v0)) t) as l1.
 move: (IH v l1) => A2; rewrite /= /flip in A2. by rewrite A2 Heql1 rcons_cons. Qed.

Local Notation insert_sorted := (insert_sorted R Rord).
Local Notation without_sorted := (without_sorted R Rord).

Lemma sd_open (cmds : seq raw_fs_cmd) vs cs v: sorted (treeR R) cs -> has (by_value v) cs ->
  exec_all raw_fs_interp (Some (Node vs cs)) ((map (fun c => RawOpen v c) cmds)) = 
  open R ((flip (exec_all raw_fs_interp) cmds) \o (fun t => Some t)) v (Node vs cs).
elim: cmds vs cs => [|c cmds IH] /= vs cs A0.
 + move => /has_find [a A1]; rewrite A1 /= insert_same //. apply Rord.
 + move => A1. assert (A1':=A1). move: A1' => /has_find [[vx xs]] A2.
   rewrite /flip /= A2 /flip /bind /=.
   case A3: (raw_fs_interp c _) => [[av acs]|] /=; [| by rewrite ?exec_all_none].
   rewrite IH //; try (by apply insert_sorted, without_sorted);
   (move: A2 A3 => /find_pred; rewrite /by_value /= => /eqP -> /=);
   [|by move => /interp_some /= ->; rewrite has_insert /= eq_refl orb_true_r].  
   rewrite /flip /bind => /interp_some /= ->. sop_simpl.
   case A2: (exec_all _ _) => [a|] //. Qed.

Lemma open_create v:
  (fun t => RawOpen v (RawCreate t)) =1 (fun c => RawOpen v c) \o (fun t => RawCreate t).
 by rewrite /eqfun /=. Qed.

Lemma create_many v xs: sorted (treeR R) xs ->
  exec_all raw_fs_interp (Some (Node v [::])) [seq RawCreate t | t <- xs] = Some (Node v xs).
elim: xs => [|x xs IH] // A0. rewrite /flip sd_commutes map_rcons exec_all_rcons_ind IH /=; try by move: A0 => /path_sorted.
assert (A0' := A0). move: A0' => /= /path_has -> /=. rewrite /insert g_insert_path //. apply treeR_order, Rord. apply Rord. Qed.

Lemma subdivision_step: forall t v xs, is_tree_sorted R (Node v xs) -> is_tree_sorted R t ->
  exec_all raw_fs_interp (Some t) ((RawCreate (Node v [::])) :: (map (fun t => RawOpen v (RawCreate t)) xs)) =
  raw_fs_interp (RawCreate (Node v xs)) t.
move => [vt tcs]; intros. rewrite (@eq_map _ _ _ _ (open_create v)) exec_all_ind map_comp.
move A0: (bind (raw_fs_interp (RawCreate (Node v [::]))) (Some (Node vt tcs))) => [[va csa]|] //=;
move: A0 => /=; case A0: (has _ _) => //=; [move => [] [] -> <-| by rewrite exec_all_none].
 + rewrite sd_open. rewrite /flip /= without_insert_i //. sop_simpl. rewrite /= create_many ?has_without //.
 + use_sortedness H.
 + use_sortedness H0. apply Rord.
 + by rewrite has_insert /by_value /= eq_refl orb_true_r. Qed.

Lemma insert_subdivision: forall c t, is_tree_sorted R t -> is_tree_sorted R c -> 
  exec_all raw_fs_interp (Some t) (subdiv c) = raw_fs_interp (RawCreate c) t.
elim => [v|v cs IH] [vt ts] A0 A1.
 + by rewrite /= /flip /bind /=.
 + rewrite -subdivision_step //. simpl subdiv. rewrite ?exec_all_cons.
   move A2: (raw_fs_interp _ _) => [[a1 as1]|]; rewrite ?exec_all_none //.
   move: A2 => /=. case A2: has => [] //= [] ? <-.
   rewrite (@eq_map _ _ _ _ (open_create v)) map_comp ?sd_open; 
    try (by rewrite insert_has_t // ?/by_value /= eq_refl);
    try (by rewrite insert_sorted //; move: A0 => /= /andP []; rewrite sorted_compatibility).

   rewrite /flip /= /bind /=. case A3: (find (by_value v) _) => [a|] //.
   assert (A3': is_tree_sorted R a).
   +  move: A3 => /=. by sop_simpl => [] [] <-.
   clear A3. elim: cs IH A0 A1 a A3' => [|c cs IHcs] IH A0 A1 a A3' //. 
   rewrite ?map_cons /= /flip /bind.
   move: IH => [] A4 A5. rewrite exec_all_cat A4.
   move A6: (raw_fs_interp _ a) => [a'|].
   move: A5 => /IHcs A5. apply (A5 A0). 

 * by move: A1 => /= /andP [] /path_sorted -> /andP [] ? ->. 
 * move: A1 => /= /andP [] ? /andP [] A1 ?. case: a A6 A3' => [va csa] /=.
   case: (has _ _ ) => [] //=; try by rewrite exec_all_none. case => <-. 
  * move => /andP [] A6 A7 /=. by rewrite sorted_compatibility insert_sorted ?andb_true_l ?insert_all ?A7 // -sorted_compatibility. 
 * by rewrite ?exec_all_none.
 * done.
 * by move: A1 => /= /andP [] ? /andP []. Qed.

Fixpoint ins_it (x y : ins_cmd) (f : bool) : seq ins_cmd :=
 match x, y with
  | Ins t1, Ins t2 => if (t1 == t2) then [::] else [::Ins t1]
  | IOpen t1 c1, IOpen t2 c2 => if t1 == t2 then map (IOpen t1) (ins_it c1 c2 f) else [:: x]
  | _, _ => [::x]
 end.

Lemma ins_it1 i1 i2 f: ins_it i1 i2 f = if (i1 == i2) then [:: ] else [:: i1].
elim: i1 i2 => [t1|t1 c1 IH] [t2|t2 c2] //=. case A0: eq_op.
 + move: A0 (IH c2) => /eqP -> ->. rewrite /eq_op /= eq_refl. by case eq_ins.
 + by rewrite /eq_op /= A0. Qed.

Lemma subdiv_l1 l1 x2: uniq l1 -> 
exists n, transform ins_it l1 [:: x2] n = Some ([:: x2] \ l1, l1 \ [:: x2]).

elim: l1 => [|x1 l1 IH] U. rewrite ?seqminus_nil seqminus_nil'. by exists 1.
move: U => /= /andP [] B0 B1.
move: (IH B1) => [] n A0. exists (n.+2). remember (n.+1) as n1. simpl. rewrite ?ins_it1 eq_sym.
move: B0. case A1: eq_op. move: A1 => /eqP -> /=.
rewrite Heqn1 2!TransformApp.tr_through_nil /= /in_mem /= eq_refl /= => B0. by rewrite seqminus_singleton.
rewrite Heqn1 => B0. apply tstab with (k:=1) in A0. 
move: A0. rewrite addn1 => ->. by rewrite TransformApp.tr_through_nil /= /in_mem /= eq_sym A1 /= cats0. Qed.

Lemma subdiv_it l1 l2: uniq l1 -> uniq l2 -> 
exists n, @transform ins_cmd ins_it l1 l2 n = Some (l2 \ l1, l1 \ l2).
elim: l2 l1 => [|x2 l2 IH] [|x1 l1] //=; rewrite ?seqminus_nil; try by exists 1.

move => B1 /andP [] B2 B2'.
move: B1 => /andP [] B1 B1'.
move: (IH (l1) B1' B2') => [n' A0'].
move: (subdiv_l1 l1 x2 B1') => [n01 A01].

assert (U: uniq (x1 :: l1 \ [:: x2])). rewrite /=. apply /andP. split.
 + by rewrite /seqminus mem_filter (negbTE B1) andb_false_r.
 + by apply uniq_setminus.
move: (IH (x1 :: l1 \ [:: x2]) U B2') => [n02 A02].
remember (n01 + n02) as n.

exists ((n'+n).+2). remember ((n'+n).+1) as n1. simpl. rewrite ?ins_it1 eq_sym.
case A1: eq_op => /=. 
 + move: A1 B2 => /eqP <- B2. rewrite Heqn1 TransformApp.tr_through_nil -Heqn1 /=.
   apply tstab with (k:=n+1) in A0'. move: A0'. rewrite addnA addn1 Heqn1 => ->.
   by rewrite /in_mem /= eq_refl /= ?seqminus_cons.
 +  apply tstab with (k:=n02 + n' +1) in A01. move: A01. 
    rewrite 2!addnA -Heqn addn1 addnC -Heqn1 => ->.
    apply tstab with (k:=n01 + n' +1) in A02. move: A02.
    rewrite ?addnA (addnC n02) -Heqn addn1 addnC -Heqn1 => ->.
    rewrite /in_mem /= eq_sym A1 /= /in_mem /=.
    case C0: (@pred_of_eq_seq ins_cmd_eqType l1 x2);
    case C1: (@pred_of_eq_seq ins_cmd_eqType l2 x1) => /=; rewrite ?seqminus_cat /=;
    (rewrite -(seqminus_cons' l1 [::x2] x1); [by rewrite seqminus_p1| by rewrite /in_mem /= A1]). Qed.

Lemma subdiv_prime x: subdiv x = map ins_fs (subdiv' x).
elim: x => [x|x xs IH] //=.
elim: xs IH => [|x' xs IH'] IH //=. rewrite ?map_cat /=.
move: IH => /= [] IH0 IH1. apply IH' in IH1. clear IH'.
move: IH1 IH0 => [] <- ->. rewrite -?map_comp.
assert (A0: [eta RawOpen x] \o ins_fs =1 ins_fs \o [eta IOpen x]).
 by move => ? /=. by rewrite (@eq_map _ _ _ _ A0). Qed.

End InsFs.

 Definition merge_trees (x y : tree T) : seq raw_fs_cmd := (subdiv x) \ (subdiv y).

  Fixpoint raw_fs_it (x y : raw_fs_cmd) (f : bool) : seq raw_fs_cmd :=
    let instead a b := [:: raw_fs_inv a; b] in
    match x, y with
    | RawEdit xl xk, RawEdit yl yk =>
        match xl == yl, xk == yk with
          | false, false => [:: x]
          | true, true => [::]
          | true, false => (if f then [::] else [:: RawEdit yk xk])
          | false, true => [:: RawEdit yk yl]
        end
    | RawEdit xl xk, RawCreate  yt => if xk == value yt then instead y x else [:: x]
    | RawCreate  xt, RawEdit yl yk => if value xt == yk then [::] else [:: x]
    | RawOpen xl xc, RawOpen yl yc => if xl == yl then map (RawOpen xl) (raw_fs_it xc yc f) else [:: x]
    | RawRemove xt, RawRemove yt =>   if value xt == value yt then [::] else [:: x]
    | RawRemove xt, RawOpen yl yc =>  
       if value xt == yl
       then if raw_fs_interp yc xt is Some t then [:: RawRemove t] else [::]
       else [:: x]
    | RawOpen xl xc, RawRemove yt =>  if value yt == xl then [::] else [:: x]
    | RawOpen xl xc, RawEdit yl yk => if xl == yl then [:: RawOpen yk xc ] else [:: x]
    | RawEdit xl xk, RawRemove yt =>  if xl == value yt then [::] else [:: x]
    | RawRemove xt, RawEdit yl yk =>  if yl == value xt
                                      then [:: RawRemove (Node yk (children xt)) ] else [:: x]
    | RawCreate xt, RawCreate yt =>   if value xt == value yt then merge_trees xt yt else [:: x]
    | _, _ => [:: x]
    end.

Lemma ins_fs_comp i1 i2 f: raw_fs_it (ins_fs i1) (ins_fs i2) f = map ins_fs (ins_it i1 i2 f).
 elim: i1 i2 => [t1|t1 c1 IH] [t2|t2 c2] //=; case A0: eq_op => //=.
 + move: A0 => /eqP ->. by rewrite /merge_trees /= /in_mem /= eq_refl.
 + rewrite IH -?map_comp. apply eq_map. by rewrite /eqfun. Qed.

Section PropertyC1.

Definition C1' (op1 op2 : raw_fs_cmd) := forall (f : bool) m (m1 m2 : tree T), is_tree_sorted R m ->
  raw_fs_interp op1 m = Some m1 -> raw_fs_interp op2 m = Some m2 -> 
  let m21 := (exec_all raw_fs_interp) (Some m2) (raw_fs_it op1 op2 f) in
   let m12 := (exec_all raw_fs_interp) (Some m1) (raw_fs_it op2 op1 (~~f)) in
    m21 = m12 /\ exists node, m21 = Some node.

Lemma c1_r_r t s: C1' (RawRemove t) (RawRemove s).
move => f [v cs] [v' cs'] [v'' cs''] ?.
case A0: (eq_op (value s) (value t)); move: A0; [move => /eqP| move => A0].
 + simpl => ->. rewrite eq_refl. case A1: find => [a| //] /=.
   repeat (case: eq_op => //=). move => <- <-. by split; eauto.
 + simpl raw_fs_it. rewrite eq_sym A0 /= /flip /bind /=.
   case A1: find => [tr'|]; case A2: find => [tr''|] //=; 
   case A3: eq_op; case A4: eq_op => //=. SearchAbout filter find.
   repeat (case => -> <-). rewrite /without' -lock ?find_filter ?A1 ?A2 /= ?A3 ?A4 /=;
     [|apply by_diff_values; rewrite eq_sym| apply by_diff_values] => //.
   rewrite without_without. eauto. Qed.

Lemma c1_c_r tc tr: C1' (RawCreate tc) (RawRemove tr).
move => f [v cs] [v' cs'] [v'' cs''] S /=.
case A0: has => //= [] [] <- <-. case A1: find => [a|] //=. case A2: eq_op => //=.
move: A2 => /eqP -> [] <- <-. rewrite /flip /bind /=.
move: (find_pred A1); rewrite {1}/by_value /= => /eqP <-.
case A2: (eq_op (value tc) (value tr)).
 + move: A2 A0 => /eqP ->. move /find_absent. by rewrite A1.
 + rewrite /without' -lock has_filter ?A0 /=; [|by (apply by_diff_values; rewrite eq_sym)].
   sop_simpl. rewrite A1 /= eq_refl /= -without_insert; [ eauto | by apply Rord | by use_sortedness S | by rewrite A2]. Qed.

Lemma c1_c_e tc ve ve': C1' (RawCreate tc) (RawEdit ve ve').
move => f [v cs] [v' cs'] [v'' cs''] S /=. rewrite /without' -lock.
case A0: has => //= [] [] <- <-. case A1: find => [[av acs]|] //=. case A2: has => [] //= [] <- <-.
rewrite eq_sym. case A3: (ve' == value tc) => /=; rewrite /flip /bind /=.
 + move: A3 A2 => /eqP -> A2. sop_simpl. rewrite A1 /= A2 /=. eauto.
 +  assert (H0: (value tc) == ve = false).
      by (case H1: eq_op => //; move: H1 A1 A0 => /eqP <- /find_has ->).
    rewrite has_insert {2}/by_value /= eq_sym A3 orb_false_r; sop_simpl.
    rewrite A0 /= A1 /= -without_insert; try by apply Rord.
    + rewrite has_insert /by_value /= A3 orb_false_r A2 /= insert_insert.
     + rewrite eq_sym A3 /=. eauto.
     + apply Rord.
    + use_sortedness S.
    + by rewrite H0. Qed.

Lemma c1_r_e tr ve ve': C1' (RawRemove tr) (RawEdit ve ve').
move => f [v cs] [v' cs'] [v'' cs''] /= S. rewrite /without' -lock.
case A0: find => //= [a]. case A1: eq_op => //=. move: A1 A0 => /eqP <- A0 {a} [] <- <-.
case A1: find => //= [[va csa]]. case A2: has => //= [] [] <- <-. assert (A1':=A1). 
move: A1' A1 => /find_by_value <- A1. case A3: eq_op => //=; rewrite /flip /bind /=.
 + sop_simpl. move: A3 A1 A2 => /eqP -> /=. rewrite A0 => [] [] -> /= A2. sop_simpl. eauto.
 + assert (H0: (value tr == ve') = false).
    (case H1: eq_op => //; move: H1 A0 A2 => /eqP <- /find_has; sop_simpl => -> //).
   sop_simpl. rewrite A0 /= eq_refl /=.
   rewrite A1 /= without_without. sop_simpl.
   rewrite A2 /= -without_insert /=; [ eauto | | use_sortedness S | rewrite eq_sym H0 //]; apply Rord. Qed.

Lemma c1_e_e ve ve' vf vf': C1' (RawEdit vf vf') (RawEdit ve ve').
move => f [v cs] [v' cs'] [v'' cs''] /= S. rewrite /without' -lock.
assert (H: sorted (T:=tree_eqType T) (treeR R) cs) by use_sortedness S. 
case A0: find => //= [[fa fcs]]. case A1: has => //= [] [] <- <-.
case A0': find => //= [[ea ecs]]. case A1': has => //= [] [] <- <-.
rewrite eq_sym. case A2: eq_op => /=; rewrite eq_sym; case A2': eq_op => /=.
 + move: A2 A2' => /eqP A2 /eqP A2'; subst. by move: A0 A0' => -> [] ? <-; eauto.
 + move: A2 => /eqP A2; subst; case f; rewrite /= /bind /flip /=; sop_simpl;
   rewrite ?A1' ?A1 /=; by move: A0 A0' => -> [] ? ->; eauto.
 + move: (ip1_e vf vf' _ v _ H A0 A1). move: (ip1_e ve ve' _ v _ H A0' A1').
   by rewrite /= {2 4}/flip {2 4}/bind /= A0 A0' /= /without' -lock A1 A1' /= => -> ->; eauto.  
 + rewrite /= /bind /flip /= /without' -lock .
   case A3: (vf == ve').
   * move: A3 => /eqP A3. by assert False; by move: A0 A1' => /find_has; sop_simpl => ->.
   * case A4: (ve == vf').
    * move: A4 => /eqP A4. subst. rewrite without_has' // in A1. apply find_has in A0'. by rewrite A0' in A1. by rewrite eq_sym A2.
    * sop_simpl; rewrite A0 A0' /=. rewrite -?without_insert /=; 
        try (by rewrite eq_sym ?A3 ?A4); try apply without_sorted => //; try by apply Rord.
      rewrite ?insert_has_f /=; try rewrite /by_value //= eq_sym //.
      rewrite (without_without vf); sop_simpl; rewrite A1.
      rewrite (without_without ve); sop_simpl; rewrite A1' /=.
      rewrite insert_insert; eauto. apply Rord. Qed.

Lemma c1_o_e vc vc' vo op1: C1' (RawOpen vo op1) (RawEdit vc vc').
move => f [v cs] [v' cs'] [v'' cs''] /= S. rewrite /without' -lock.
case A0: bind => [a|] // [] <- <-. case A1: find => [[bv bcs]|] //=.
move: (find_pred A1); rewrite {1}/by_value /= => /eqP H0; subst.
case A2: has => //= [] [] <- <-. case A3: eq_op => /=.
 + move: A3 => /eqP A3. subst. rewrite /flip /bind /=. sop_simpl;
   destruct a as [va csa]. rewrite A1 /= in A0. correct_interp_label A0.   
   sop_simpl; rewrite A2 /=. eauto.
 + rewrite /flip /bind /=. case A4: (vc' == vo).
  * move: A4 => /eqP A4. subst. move: A2 A0.
    rewrite eq_sym in A3. by rewrite without_has' // => /find_absent ->.
  * rewrite find_insert_f //; [|by rewrite /by_value /= eq_sym A4].
    sop_simpl; rewrite A0.
    case: a A0 => [va csa]. case A5: find => [[vc ccs]|] //=.    
    correct_label A5 => A0. assert (A0' := A0).
    move: A0' => /interp_label_indep /= A0'. move: A0. rewrite ?A0' => [] [] A0.
    sop_simpl; rewrite A1.
    rewrite -(without_insert Rord _ bv) /=; [| by use_sortedness S; apply Rord| by rewrite A3].
    rewrite without_without. rewrite insert_has_f; [|by rewrite /by_value /= A4]. sop_simpl.
    rewrite A2 /=. rewrite -without_insert /=; [| |use_sortedness S | by rewrite A4]; try by apply Rord.
    rewrite insert_insert. eauto. apply Rord. Qed.

Lemma c1_o_r s vo op1: C1' (RawOpen vo op1) (RawRemove s).
move => f [v cs] [v' cs'] [v'' cs''] /= S. rewrite /without' -lock /=.
case A0: find => [[ev ecs]|] //=. correct_label A0.
case A1: raw_fs_interp => [[av acs]|] //= [] <- <-. correct_interp_label A1.
case A1: find => [[bv bcs]|] //=.
case A3: eq_op => [] //=; move: A3 A1 => /eqP -> /= A1 {s} [] <- <-.
 case A4: eq_op => [] /=.
 + move: A4 => /eqP A4; subst.
   move: A0. rewrite A1 => [] [] A3; subst.
   rewrite A2 /= /bind /flip /=. sop_simpl; eauto.
 + rewrite /flip /=. sop_simpl; rewrite A0 /= A2 A1 /= eq_refl -without_insert;
    [ rewrite without_without; eauto | | use_sortedness S | rewrite eq_sym A4 //]; apply Rord. Qed.

Lemma c1_o_c s vo op1: C1' (RawOpen vo op1) (RawCreate s).
move => f [v cs] [v' cs'] [v'' cs''] /= S.
case A0: find => [[av acs]|] //=. correct_label A0.
case A1: raw_fs_interp => [[bv bcs]|] //=. correct_interp_label A1 => [] [] <- <-.
case A1: has => [] //= [] <- <-. rewrite /flip /= /bind /=.
case A3: ((value s) == bv).
 + by move: A3 A0 A1=> /eqP <- /find_has ->.
 + rewrite find_insert_f; [| by rewrite /by_value /= eq_sym].
   rewrite A0 A2 insert_has_f;[| by rewrite /by_value /=]. sop_simpl;
   by rewrite /= A1 /= -without_insert; 
    [ rewrite insert_insert; eauto | | use_sortedness S | rewrite /= A3 //]; apply Rord. Qed.

Lemma C1'_C c1 c2: C1' c1 c2 -> C1' c2 c1.
rewrite /C1'; intros. move: (H (~~f) m m2 m1 H0 H2 H1) => [] => ->.
rewrite negb_involutive; eauto. Qed.

Lemma c1_o_o op1 op2: C1' op1 op2 -> 
  (forall l1 l2, C1' (RawOpen l1 op1) (RawOpen l2 op2)).

   move => IH; intros.
   rewrite /C1' => f [v cs] [v' cs'] [v'' cs''] S /=.
   rewrite eq_sym. case A3: eq_op.
  * move: A3 => /eqP A3; subst.
    move A0: (find (by_value l1) cs) => [[vf csf]|] //=.
    case A1: raw_fs_interp => [[va csa]|] //= [] [] <- <-.
    case A2: raw_fs_interp => [[vb csb]|] //= [] [] <- <-.
    move: (find_sorted R v _ _ _ S A0) => SF.
    move: (IH f (Node vf csf) _ _ SF A1 A2) => /= IH0.
    move: (find_pred A0) => H. rewrite /by_value /= in H. move: H A0 => /eqP -> A0.
    move: (interp_some _ _ _ A1) (interp_some _ _ _ A2) => /= H1 H2; subst; subst.
    rewrite ?sd_open; try (by rewrite insert_has_t // /by_value /= eq_refl);
                      try (by use_sortedness S; apply Rord).
    rewrite /flip /= /bind /=. sop_simpl;
    move: IH0 => [] -> [] x ->. eauto.

  * rewrite /bind /=.
    case A1: find => [[va csa]|] //=.
    case A2: find => [[vb csb]|] //=.
    case A4: raw_fs_interp => [[ve cse]|] //= [] [] <- <-.
    case A5: raw_fs_interp => [[vf csf]|] //= [] [] <- <-.
    move: (interp_some _ _ _ A4) (interp_some _ _ _ A5) => /= H1 H2; subst; subst.
    correct_label A1. correct_label A2.
    rewrite /= /flip /= /bind /=. sop_simpl; rewrite A1 A2 A4 A5.
    rewrite -(without_insert Rord _ ve) /=; [| by use_sortedness S; apply Rord |by rewrite A3].
    rewrite -(without_insert Rord _ vf) /=; [| by use_sortedness S; apply Rord |by rewrite eq_sym A3].
    rewrite insert_insert. rewrite without_without. eauto. apply Rord. Qed.

Ltac elem_case := first [apply c1_e_e | apply c1_c_e | apply c1_r_e | apply c1_o_e | 
                         apply c1_o_r | apply c1_r_e | apply c1_r_r | apply c1_c_r |
                         apply c1_o_c | apply c1_o_o].
Ltac elem_or_sym := (try by elem_case); (try by apply C1'_C; elem_case).

Ltac ii := let A0 := fresh "A0" in let A1 := fresh "A1" in let A2 := fresh "A2" in
move => f [v cs] [v' cs'] [v'' cs''] S; simpl raw_fs_it; rewrite eq_sym; case A0: eq_op;
[rewrite -?insert_subdivision /merge_trees // => A1 A2; rewrite -A1 -A2 |
 simpl; case A1: has => //= [] [] <- <-; case A2: has => //= [] [] <- <-;
  rewrite /flip /=; rewrite ?insert_has_f /=; (try by rewrite /by_value /= ?A0 // eq_sym ?A0);
  rewrite A1 A2 /= insert_insert; eauto].

Lemma c1_ins op1 op2: C1' (ins_fs op1) (ins_fs op2).
elim: op1 op2 => [t1|t1 c1 IH] [t2|t2 c2] /=; elem_or_sym.
 + ii. rewrite -?exec_all_cat. move: A0 A1 => /eqP ->; rewrite /= /in_mem /= eq_refl /= => /= ->. eauto. apply Rord. Qed.

Definition ins_interp (c : ins_cmd) (t : sorted_tree R) : option (tree T) := raw_fs_interp (fs_to_raw_fs (ins_fs' c)) (treeOf t).

Definition sorted_option (x : option (tree T)) := match x with None => true | Some t => is_tree_sorted R t end.

Lemma so_from_sorted (c : fs_cmd) t: is_tree_sorted R t -> sorted_option (raw_fs_interp (fs_to_raw_fs c) t).
case A0: (raw_fs_interp (fs_to_raw_fs c) t) => [t'|] A1 //=. exact (raw_fs_interp_sorted _ _ _ A1 A0). Qed.

Definition so_st (t : option (tree T)): sorted_option t -> option (sorted_tree R).
case: t => [t|] /= A0. exact (Some (STree R t A0)). exact None. Defined.

Lemma fmap_so_st t S: (fmap treeOf) (so_st t S) = t.
 rewrite /so_st. by dependent destruction t. Qed.

Definition ins_sorted (c : ins_cmd) (t : sorted_tree R) : option (sorted_tree R). 
move: t => [t S]. apply (so_st (raw_fs_interp (fs_to_raw_fs (ins_fs' c)) t)), so_from_sorted, S. Defined.
 
Lemma ins_sorted_treeOf c (s : sorted_tree R): 
 (fmap treeOf) (ins_sorted c s) = ins_interp c s.
rewrite /ins_sorted. case: s => [t S] /=. by rewrite fmap_so_st /ins_interp. Qed.

Lemma ins_compat x: fs_to_raw_fs (ins_fs' x) = ins_fs x.
elim: x => [t|t c IH] //=. by rewrite IH. Qed.

Corollary ins_compat': fs_to_raw_fs \o ins_fs' =1 ins_fs. apply /ins_compat. Qed.

Lemma exec_ins_compat: forall c s, (fmap treeOf) (exec_all ins_sorted (Some s) c) = 
  exec_all (raw_fs_interp \o ins_fs) (Some (treeOf s)) c.
apply (@last_ind ins_cmd (fun c => 
 forall s, fmap treeOf (exec_all ins_sorted (Some s) c) = exec_all (raw_fs_interp \o ins_fs) (Some (treeOf s)) c)).
 + done. 
 + intros s x IH s'. rewrite 2!exec_all_rcons_ind /= /bind /flip -IH. 
   case A0: exec_all => [b|] //=. by rewrite ins_sorted_treeOf /ins_interp ins_compat. Qed.

Lemma ins_fs_fs'_compat m c:
exec_all (raw_fs_interp \o fs_to_raw_fs) m (map ins_fs' c) = exec_all (raw_fs_interp \o ins_fs) m c.
case: m => [m|]. 
 + by rewrite (exec_all_compat _ ins_fs') (exec_all_eqfun (compA _ _ _)) (exec_all_eqfun (eq_comp (frefl _) ins_compat')).
 + by rewrite ?exec_all_none. Qed.

Instance insOT': (OTBase (sorted_tree R) ins_cmd) := {interp := ins_sorted; it := ins_it}.
intros. rewrite /m21 /m12 => {m12} {m21}.
case: m m1 m2 H H0 => [m S] [m1 S1] [m2 S2].

 move /opt_eq => H. rewrite ins_sorted_treeOf /= in H.
 move /opt_eq => H0. rewrite ins_sorted_treeOf /= in H0.

move: H H0. rewrite ?ins_sorted_treeOf /= /ins_interp /=? ins_compat => /= H H0. 
move: (c1_ins op1 op2 f m m1 m2 S H H0) => [] A0 A1. split.
 + apply opt_eq. by rewrite ?exec_ins_compat /= -?(exec_all_compat raw_fs_interp ins_fs) -?ins_fs_comp A0.
 + move: A1 => [t]. rewrite ins_fs_comp exec_all_compat -ins_fs_fs'_compat => A1. assert (A1' := A1).
   move: A1 => /raw_fs_interp_sorted_all A1. exists (STree R t (A1 S2)) => /=. apply opt_eq.
   by rewrite /= -A1' exec_ins_compat ins_fs_fs'_compat /=. Defined.

Definition firstP (x : ins_cmd) := match x with | Ins t => t | IOpen t c => t end.

Lemma firstP_subdiv' c xs: c \in flatten [seq subdiv' i | i <- xs] -> firstP c \in map value xs.
elim: xs => [|x xs IH] //=. rewrite mem_cat. case A0: in_mem => /=.
 + move => ?. destruct x. move: A0 => /=. move: (flatten _) => f. 
   destruct c => /=; rewrite /in_mem /=.
  + case A0: eq_op.  
   + move: A0 => /eqP [] ->. by rewrite eq_refl.
   + by elim: f.
  + elim: f => //= f fs IHf. case A0: eq_op.  
   + move: A0 => /eqP [] ->. by rewrite eq_refl.
   + by rewrite orb_false_l.
 + move => /IH. rewrite /in_mem /= => ->. by rewrite orb_true_r. Qed.

Lemma uniq_subdiv' {s}: is_tree_sorted R s -> uniq (subdiv' s).
expand_order Rord.
elim: s => [x|x xs IH] //= /andP [] /(sorted_uniq H2 H0) A0 A1.
apply /andP. split.
 + by elim: flatten.
 + assert (injective [eta IOpen x]). by move => ?? [].
   rewrite (map_inj_uniq H3).
   elim: xs A1 A0 IH => [|x' xs IH] //= /andP [] A0 A1 /andP [] A2 A3 [] A4 A5.
   move: (IH A1 A3 A5) => A6 {IH}. rewrite cat_uniq A6 andb_true_r (A4 A0) /=.
   apply /negP => /hasP /= [c A7 A8]. apply firstP_subdiv' in A7.
   move: (firstP_subdiv' c [::x']) => /=. rewrite cats0 => A9. apply A9 in A8. clear A9. 
   by case: c A8 A7 => [v|v c] /=; rewrite {1}/in_mem /= orb_false_r => /eqP ->;
     rewrite (negbTE A2). Qed.

Lemma c1_c_c t s : is_tree_sorted R s -> is_tree_sorted R t -> C1' (RawCreate t) (RawCreate s).
move => S1 S2. ii. move: (subdiv_it _ _ (uniq_subdiv' S1) (uniq_subdiv' S2)) => [n B0].
move: A1 A2. rewrite ?subdiv_prime ?(exec_all_compat raw_fs_interp ins_fs) -?map_seq_minus; try by apply ins_fs_inj.
move => A1 A2. assert (B1 := A1). assert (B2 := A2).
rewrite -ins_fs_fs'_compat in A1. rewrite -ins_fs_fs'_compat in A2.
move: (raw_fs_interp_sorted_all _ _ _ S A1) => SA1.
move: (raw_fs_interp_sorted_all _ _ _ S A2) => SA2.

Ltac tc2 := apply opt_eq; rewrite /= exec_ins_compat /=; by rewrite -ins_fs_fs'_compat.

assert (H: exec_all ins_sorted (Some {| treeOf := Node v cs; stp := S |}) (subdiv' s) =
        Some {| treeOf := Node v'' cs''; stp := SA2 |}). by tc2.
assert (H2: exec_all ins_sorted (Some {| treeOf := Node v cs; stp := S |}) (subdiv' t) =
        Some {| treeOf := Node v' cs'; stp := SA1 |}). by tc2.

move: (ot_execution insOT' n (subdiv' s) (subdiv' t) 
 (subdiv' s \ subdiv' t) (subdiv' t \ subdiv' s) 
 (Some (STree R _ S)) (STree R _ SA2) (STree R _ SA1) (conj H H2) B0) => [] C1 C2.

by split; [move: C1 | move: C2 => [[m3t S3]] /= C2; exists m3t; move: C2]; move => /opt_eq /=;
rewrite ?exec_ins_compat /= -?A1 -?A2 ?ins_fs_fs'_compat ?(exec_all_compat _ ins_fs). apply Rord. Qed.

Theorem c1 (op1 op2 : fs_cmd): C1' (fs_to_raw_fs op1) (fs_to_raw_fs op2).

elim: op1 op2 => [l1 l1'|c1|c1|l1 op1 IH] [l2 l2'|c2|c2|l2 op2];
 (try by elem_case); (try by apply C1'_C; elem_case).

 + apply c1_c_c. destruct c2. apply stp. destruct c1. apply stp. Qed.

End PropertyC1.

Section Computability.

Fixpoint raw_fs_sz0 (x : raw_fs_cmd) :=
 match x with
 | RawOpen l c => raw_fs_sz0 c
 | RawEdit l c => 1
 | RawCreate t => weight t
 | RawRemove t => 1
 end.

Fixpoint raw_fs_si0 (x : raw_fs_cmd) :=
 match x with
 | RawOpen l c => raw_fs_si0 c
 | RawEdit l c => 0
 | RawCreate t => weight t
 | RawRemove t => 0
 end.

Lemma sz0_open y: raw_fs_sz0 =1 raw_fs_sz0 \o (RawOpen y). by rewrite /eqfun => [] []. Qed.
Lemma si0_open y: raw_fs_si0 =1 raw_fs_si0 \o (RawOpen y). by rewrite /eqfun; case. Qed.

Definition raw_fs_sz (x : seq raw_fs_cmd) := foldl addn 0 (map raw_fs_sz0 x). 
Definition raw_fs_si (x : seq raw_fs_cmd) := foldl addn 0 (map raw_fs_si0 x).

Lemma fs_sz_cons x xs: raw_fs_sz (x :: xs) = raw_fs_sz0 x + raw_fs_sz xs.
by rewrite /raw_fs_sz /= add0n (fadd (raw_fs_sz0 x)). Qed.

Lemma fs_si_cons x xs: raw_fs_si (x :: xs) = raw_fs_si0 x + raw_fs_si xs.
by rewrite /raw_fs_si /= add0n (fadd (raw_fs_si0 x)). Qed.
 
Lemma fs_sz_cat xs1 xs2: raw_fs_sz (xs1 ++ xs2) = raw_fs_sz xs1 + raw_fs_sz xs2.
elim: xs1 xs2 => [|x xs1 IH] xs2 //=. by rewrite ?fs_sz_cons IH addnA. Qed.

Lemma fs_si_cat xs1 xs2: raw_fs_si (xs1 ++ xs2) = raw_fs_si xs1 + raw_fs_si xs2.
elim: xs1 xs2 => [|x xs1 IH] xs2 //=. by rewrite ?fs_si_cons IH addnA. Qed.

Corollary sz_open s l: raw_fs_sz [seq RawOpen s i | i <- l] = raw_fs_sz l.
case: l => [|l ls] //=. move Heqf: (RawOpen s) => f. 
by rewrite  /raw_fs_sz /= -map_comp -Heqf (eq_map (sz0_open s)). Qed.

Corollary si_open s l: raw_fs_si [seq RawOpen s i | i <- l] = raw_fs_si l.
case: l => [|l ls] //=. move Heqf: (RawOpen s) => f.
by rewrite /raw_fs_si /= -map_comp -Heqf (eq_map (si0_open s)). Qed.

Lemma weight_subdiv t1: weight t1 = raw_fs_sz (subdiv t1).
elim: t1 => [] //= v cs. elim: cs => [|c cs IH2] [] // A0 A1. apply IH2 in A1.
 move: A1. rewrite map_cons /= map_cat ?fs_sz_cons fs_sz_cat ?sz_open -A0.
 rewrite (addnA _ (weight c)) (addnC _ (weight c)) -addnA => <-. by rewrite ?weight_Node ?weights_cons addnA. Qed.

Lemma weight_subdiv_si t1: weight t1 = raw_fs_si (subdiv t1).
elim: t1 => [] //= v cs. elim: cs => [|c cs IH2] [] // A0 A1. apply IH2 in A1.
 move: A1. rewrite map_cons /= map_cat ?fs_si_cons fs_si_cat ?si_open -A0.
 rewrite (addnA _ (weight c)) (addnC _ (weight c)) -addnA => <-. by rewrite ?weight_Node ?weights_cons addnA. Qed.

Lemma sz_weight t1 t2: raw_fs_sz (merge_trees t1 t2) <= weight t1.
 rewrite /merge_trees /raw_fs_sz. move: (sum_setminus raw_fs_sz0 (subdiv t1) (subdiv t2)).
 by rewrite weight_subdiv /raw_fs_sz. Qed.
      
Lemma si_weight t1 t2: raw_fs_si (merge_trees t1 t2) <= weight t1.
 rewrite /merge_trees /raw_fs_si. move: (sum_setminus raw_fs_si0 (subdiv t1) (subdiv t2)).
 by rewrite weight_subdiv_si /raw_fs_si. Qed.

Lemma weight_nonzero (t : tree T): weight t > 0. by case: t => t l; rewrite /weight /encode. Qed.

Theorem OT_C op1 op2: computability raw_fs_it raw_fs_sz raw_fs_si op1 op2.
  rewrite /computability.
  elim: op1 op2 => [s1 c1|t1|t1|s1 r1 IH] [s2 c2|t2|t2|s2 r2] f;
  try (case: f => [] /=; rewrite (eq_sym (value t2)); case (_ == _);
  move A0: (raw_fs_sz [::_]) => f0; move A1: (raw_fs_sz [::_]) => f1;
  move A2: (raw_fs_si [::_]) => f2; move A3: (raw_fs_si [::_]) => f3;
  rewrite /raw_fs_sz /raw_fs_si /= ?add0n in A0, A1, A2, A3; subst; eauto;
  move: (sz_weight t1 t2) (sz_weight t2 t1) (si_weight t1 t2) (si_weight t2 t1) => H0 H1 H2 H3; intuition;
  try (by apply (leq_add H0 H1)); by apply (leq_add H2 H3));
  try (rewrite /= ?(eq_sym s2); case: (s1 == s2); rewrite ?sz_open ?si_open;
   move: (IH r2 f) => /=; rewrite /raw_fs_sz /raw_fs_si; intuition);
  rewrite /raw_fs_sz /raw_fs_si /= ?(eq_sym s2) ?(eq_sym c2) ?(eq_sym (value t2));
  try by intuition.
  + by case: (s1 == s2); case: (c1 == c2); case: f => /=; eauto.
  + by case: (c1 == value t2) => [] /=; move: (weight_nonzero t2); intuition.
  + by case: (s1 == value t2); intuition.
  + by case: (s1 == s2); intuition.
  + by case: (value t1 == c2); nat_norm; move: (weight_nonzero t1); intuition.
  + by case: (value t1 == s2) => /=; nat_norm; intuition.
  + by case: (value t1 == s2) => /=; nat_norm; case: (raw_fs_interp r2 t1) => [a|] /=; intuition.
  + by case: (s1 == s2); intuition.
  + case: (s1 == value t2) => /=; nat_norm; [|intuition].
   move: (raw_fs_interp _ _) => [t|] /=; intuition. Qed.

End Computability.
End FilesystemOT.
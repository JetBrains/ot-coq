Require Import OtDef Ssromega Tree Basics ArithAux Commons.
Require Export mathcomp.ssreflect.seq.
Require Import ListTools.

Section RichTextOTDefinition.

Import Equality.

Context {X : eqType} (C : Type) {otX : OTBase X C} {ipX : OTInv _ _ otX} {otcX : OTComp otX}.

Inductive jcmd : Type :=
  | JInsert of nat & seq (tree X)
  | JRemove of nat & seq (tree X)
  | JUnite of nat & X & seq (tree X)
  | JFlat of nat & (tree X)
  | JOpenRoot of nat & jcmd
  | JEditLabel of C.

(* fix unite nop (force it to be non-empty) *)
Fixpoint jinterp (cmd : jcmd) (m : tree X) : option (tree X) :=
match m with | Node x xs =>
 match cmd with
  | JInsert i es => NodeW x (ins i es xs)
  | JRemove i es => NodeW x (rm i es xs)
  | JUnite i y es => if es is [::] then Some (Node x xs) else
   if rm i es xs is Some xs' then NodeW x (ins i [:: Node y es] xs') else None
  | JFlat i (Node z zs) =>
   if nth i xs is Some (Node y ys) then 
    if (zs == ys) && (y == z) then NodeW x (oins i ys (rm i [:: Node y ys] xs)) 
    else None else None
  | JOpenRoot i cmd' => if nth i xs is Some x' then NodeW x (rplc i (jinterp cmd' x') xs) else None
  | JEditLabel cmd => if @interp X C otX cmd x is Some x' then Some (Node x' xs) else None 
 end
end.

Fixpoint jinv (cmd : jcmd) :=
match cmd with 
  | JInsert n l => JRemove n l
  | JRemove n l => if l is [::] then JInsert 0 [::] else JInsert n l
  | JUnite n x l => if l is [::] then JInsert 0 [::] else JFlat n (Node x l)
  | JFlat n (Node x l) => if l is [::] then JInsert n [:: Node x [::]] else JUnite n x l
  | JOpenRoot n c   => JOpenRoot n (jinv c)
  | JEditLabel c    => JEditLabel (inv c)
end.

Definition tr_ins (len : nat) (n1 n2 : nat) := 
 if (n1 < n2) then n1 else n1 + len.

Definition tr_rem (len : nat) (n1 n2 : nat) := 
 if (n1 < n2) then Some n1 else if (n1 >= n2 + len) then Some (n1 - len) else None.

Definition tr_uni (len : nat) (n1 n2 : nat) :=
 if (n1 < n2) then Some n1 else if (n1 >= n2 + len) then Some (n1 - len + 1) else None.

Definition openroot_in (cmd : seq (tree X) -> jcmd) n1 l1 n2 tc2 :=
  match tr_rem (size l1) n2 n1 with
    None => let i := n2 - n1 in
    if nth i l1 is Some x' then
      match rplc i (jinterp tc2 x') l1 with
        | Some l1' => [:: cmd l1']
        | _ => [:: (* unused *)]
      end
    else [:: (* unused *)]
    | _ => [:: cmd l1]
  end.  

Fixpoint jit (op1 op2 : jcmd) (flag : bool) : seq jcmd :=
match op1, op2 with
 | JEditLabel c1, JEditLabel c2 => map JEditLabel  (it c1 c2 flag)
 | _, JEditLabel _ | JEditLabel _, _ => [:: op1]
 
 | JOpenRoot n1 tc1, JOpenRoot n2 tc2 =>
   if n1 == n2 then map (JOpenRoot n1) (jit tc1 tc2 flag) else [:: op1]

 | JRemove n1 l1, JOpenRoot n2 tc2 => openroot_in (JRemove n1) n1 l1 n2 tc2
 | JOpenRoot n1 tc1, JRemove n2 l2 => 
   match tr_rem (size l2) n1 n2 with
    | Some n1' => [:: JOpenRoot n1' tc1]
    | None     => nil
   end

 | JUnite n1 x1 l1, JOpenRoot n2 tc2 => openroot_in (JUnite n1 x1) n1 l1 n2 tc2
 | JOpenRoot n1 tc1, JUnite n2 _ l2 =>
   match tr_uni (size l2) n1 n2 with
    | Some n1' => [:: JOpenRoot n1' tc1]
    | None => [:: JOpenRoot n2 (JOpenRoot (n1 - n2) tc1)]
   end

 | JFlat n1 (Node x1 l1), JOpenRoot n2 tc2 =>
   (* is it really unnecessary to check nth here? *)
   if (n1 == n2) then
    match jinterp tc2 (Node x1 l1) with
     | Some t1' => [:: JFlat n1 t1']
     | None => [:: (* unused *)]
    end
   else [:: op1]
 | JOpenRoot n1 tc1, JFlat n2 (Node x2 l2) =>
   if (n1 < n2) then [:: op1]
   else if (n2 < n1) then [:: JOpenRoot (n1 + size l2 - 1) tc1]
    else match tc1 with
      | JOpenRoot n' tc' => [:: JOpenRoot (n' + n2) tc']
      | JEditLabel c' => [::]
      | JInsert n' l' => [:: JInsert (n' + n2) l']
      | JRemove n' l' => [:: JRemove (n' + n2) l']
      | JUnite n' x' l' => [:: JUnite (n' + n2) x' l']
      | JFlat n' l' => [:: JFlat (n' + n2) l']
     end

 | _, JOpenRoot _ _ => [:: op1]
 
 | JOpenRoot n1 tc1, JInsert n2 l2 => [:: JOpenRoot (tr_ins (size l2) n1 n2) tc1]

 | JInsert n1 l1, JInsert n2 l2 =>
  if (n1 == n2) then (if flag then [:: op1] else [:: JInsert (n1 + size l2) l1])
                else [:: JInsert (tr_ins (size l2) n1 n2) l1]

 | JInsert n1 l1, JRemove n2 l2 => if l2 is [::] then [:: op1] else
   let len := size l2 in
    if (n1 <= n2) then [:: op1] else
      if (n1 >= n2 + len) then [:: JInsert (n1 - len) l1] else [::]
 | JRemove n1 l1, JInsert n2 l2 =>
   let (len1, len2) := (size l1, size l2) in
    if (n1 + len1 <= n2) then [:: op1] 
      else if (n2 <= n1) then [:: JRemove (n1 + len2) l1] 
      else match ins (n2 - n1) l2 l1 with
           | Some l1' => [:: JRemove n1 l1'] 
           | None => [:: op1] end (* <- this branch is unused *)

 | JInsert n1 l1, JUnite n2 x2 l2 =>
   if l2 is [::] then 
     if n2 <= n1 then [:: JInsert n1.+1 l1] else [:: op1]
   else if (n1 <= n2) then [:: op1]
   else if (n1 >= n2 + size l2) then [:: JInsert (n1 - size l2 + 1) l1]
   else [:: JOpenRoot n2 (JInsert (n1 - n2) l1)]
 | JUnite n1 x1 l1, JInsert n2 l2 =>
   if l1 is [::] then if n1 <= n2 then [:: op1] else [:: JUnite (n1 + size l2) x1 l2] 
   else if (n2 >= n1 + size l1) then [:: op1]
   else if (n2 <= n1) then [:: JUnite (n1 + size l2) x1 l1]
   else if (ins (n2 - n1) l2 l1) is Some zs then [:: JUnite n1 x1 zs] else [:: (* unused *)]

 | JInsert n1 l1, JFlat n2 (Node x2 l2) => 
   if (n1 <= n2) then [:: op1] else [:: JInsert (n1 + (size l2) - 1) l1]
 | JFlat n1 l1, JInsert n2 l2 =>
   if (n1 < n2) then [:: op1] else [:: JFlat (n1 + size l2) l1]

 | JRemove n1 l1, JRemove n2 l2 =>
   let (len1, len2) := (size l1, size l2) in
   interval_interval_case n1 len1 n2 len2 (mkIIChoice (seq jcmd)
     [:: op1]
     [:: JRemove (n1 - len2) l1] 
     [::]
     [:: JRemove n1 (rotr (n2 - n1) (drop len2 (rot (n2 - n1) l1)))]
     [::]
     [:: JRemove n2 (drop (n2 + len2 - n1) l1)]
     [:: JRemove n1 (take (n2 - n1) l1)])

 | JRemove n1 l1, JUnite n2 x2 l2 =>
   let (len1, len2) := (size l1, size l2) in
   if l1 is [::] then [::]
   else if l2 is [::] then [::]
    else let united := (oins (n2 - n1) [:: Node x2 l2] (rm (n2 - n1) l2 l1)) in
    interval_interval_case n1 len1 n2 len2 (mkIIChoice (seq jcmd) 
      [:: op1]
      [:: JRemove (n1 - len2).+1 l1]
      (if united is Some l1' then [::JRemove n1 l1'] else [:: (* unused *)])
      (if united is Some l1' then [::JRemove n1 l1'] else [:: (* unused *)])
      [:: JOpenRoot n2 (JRemove (n1 - n2) l1)] 
      [:: JOpenRoot n2 (JRemove (n1-n2) (take (len2 + n2 - n1) l1)); JRemove (n2.+1) (drop (len2 + n2 - n1) l1) ]
      [:: JRemove n1 (take (n2 - n1) l1); JOpenRoot n1 (JRemove 0 (drop (n2 - n1) l1))])
  | JUnite n1 x1 l1, JRemove n2 l2 =>
    let (len1, len2) := (size l1, size l2) in
    if l2 is [::] then [::op1] 
    else if l1 is [::] then [::] else
    interval_interval_case n1 len1 n2 len2 (mkIIChoice _
      [:: op1]
      [:: JUnite (n1 - len2) x1 l1]
      [::]
      [:: JUnite n1 x1 (rotr (n2 - n1) (drop len2 (rot (n2 - n1) l1)))]
      [::]
      [:: JUnite n2 x1 (drop (n2 + len2 - n1) l1)] 
      [:: JUnite n1 x1 (take (n2 - n1) l1)])

  | JRemove n1 l1, JFlat n2 (Node x l2) => 
    if l1 is [::] then [::]
    else if (n1 + size l1 <= n2) then [:: op1]
    else if (n1 > n2) then [:: JRemove (n1 + size l2 - 1) l1]
    else if rm (n2 - n1) [:: Node x l2] l1 is Some ws then
         if ins (n2 - n1) l2 ws is Some zs then 
         (if zs is nil then [::] else [:: JRemove n1 zs]) else [:: (* unused *) ] else [:: (* unused *)]
  | JFlat n1 l1, JRemove n2 l2 =>
    if l2 is [::] then [:: op1] 
    else if (n1 < n2) then [:: op1] else 
    if (n1 >= n2 + size l2) then [:: JFlat (n1 - size l2) l1]
    else [::]

  | JUnite n1 x1 l1, JUnite n2 x2 l2 =>
    let (len1, len2) := (size l1, size l2) in
    interval_interval_case n1 len1 n2 len2 (mkIIChoice _
      [:: op1] 
      [:: JUnite (n1 - len2 + 1) x1 l1]
      (if ~~flag then [:: JUnite n1 x1 [:: Node x2 l2]] 
       else [:: JOpenRoot n1 (JUnite 0 x1 l2)])
      (if rm (n2 - n1) l2 l1 is Some l1' then 
         if ins (n2 - n1) [:: Node x2 l2] l1' is Some l1'' then
           [:: JUnite n1 x1 l1''] else (* unused *) [::] else [::])
      [:: JOpenRoot n2 (JUnite (n1 - n2) x1 l1)]
      (if flag then [:: JFlat n2 (Node x2 l2); op1] else [::])
      (if flag then [:: JFlat n2 (Node x2 l2); op1] else [::]))

  | JUnite n1 x1 l1, JFlat n2 (Node x2 l2) =>
    if (n2 >= n1 + size l1) then [:: op1]
    else if (n2 < n1) then [:: JUnite (n1 + size l2 -1) x1 l1]
    else if rm (n2 - n1) [:: Node x2 l2] l1 is Some ws then
         if ins (n2 - n1) l2 ws is Some zs then 
         if zs is [::] then [:: JInsert n1 [:: Node x1 [::]]] else [:: JUnite n1 x1 zs] 
         else [:: (* unused *) ] else [:: (* unused *)]
  | JFlat n1 l1, JUnite n2 x2 l2 => 
    match tr_uni (size l2) n1 n2 with
     | Some n1' => [:: JFlat n1' l1]
     | None => [:: JOpenRoot n2 (JFlat (n1 - n2) l1)]
    end

  | JFlat n1 l1, JFlat n2 (Node x2 l2) =>
    if (n1 < n2) then [:: op1]
    else if (n1 == n2) then [::]
    else [:: JFlat (n1 + size l2 - 1) l1]
end.

Fixpoint nonempty_op (t : jcmd) : bool :=
match t with
 | (JEditLabel c) => true
 | (JRemove _ l) => l != nil
 | (JInsert _ l) => l != nil
 | (JUnite _ _ l) => l != nil
 | (JFlat _ l) => true
 | (JOpenRoot _ c) => nonempty_op c
end. 

Lemma nonempty_map n l: all nonempty_op [seq JOpenRoot n i | i <- l] = all nonempty_op l.
by elim: l => [|l ls] //= ->. Qed.

Lemma ins_nonempty {Z : eqType} n a2 l1 l2 (l1' : seq Z):  
ins n (a2 :: l2) l1 = Some l1' -> l1' != nil.
by elim: n l1 => [l1 [] <- |n IHn [|a l] // /wcons_some [] x [] _ ->]. Qed.

Lemma rplc_nonempty {Z : eqType} n t (l1 : seq Z) b: 
 l1 != nil -> rplc n t l1 = Some b -> b != nil.
elim: n l1 => [|n IHn] [|a l1] // _ /=.
 + by case: t => [t|] //= [] <-.
 + by move => /wcons_some [] x [] _ ->. Qed.

Lemma rm0 {Z : eqType} (l : seq Z): rm 0 [::] l = Some l. by case: l. Qed.
(* TODO: Show that the result of transformation of two 
         nonempty operations is a composite of nonempty operations *)

Theorem nonempty_it op1 op2 f: nonempty_op op1 -> nonempty_op op2 -> all nonempty_op (jit op1 op2 f).
 elim: op1 op2 => [n1 l1|n1 l1|n1 x1 l1|n1 [x1 l1]|n1 c1 IHc1|c1] 
                  [n2 l2|n2 l2|n2 x2 l2|n2 [x2 l2]|n2 c2|c2] //=; eauto;
 try by rewrite ?andbT.
 + (* 1/24 *) by move: (n1 == n2) f => [] [] //=; rewrite andbT. 
 + (* 2/24 *) by move: l2 (n1 <= n2) => [|a2 l2] [] //=; try case (_ <= _) => //=; rewrite andbT.
 + (* 3/24 *) by move: l2 (n1 <= n2) => [|a2 l2] [] //=; try case (_ <= _) => //=; rewrite andbT.
 + (* 4/24 *) by move: (n1 <= n2) => [] //=; rewrite ?andbT. 
 + (* 5/24 *) move A0: (_ <= _) => [] //=. 
  + by rewrite andbT.
  + move A1: (_ <= _) => [] //=. by rewrite ?andbT.
    case A2: (ins _ _ _) => [a|] //=; rewrite ?andbT => //.
    by move: l2 A2 => [|a2 l2] // /ins_nonempty.
 + (* 6/24 TODO: *) case: (interval_cases_analysisP _ _ _ _ _) => //=; rewrite andbT //.
  + rewrite -[rotr _ _ == _]size_eq0 /rotr size_rot size_drop size_rot. case: eqP => //=. 
    - move=> -> _. rewrite eq_sym leq_add2l => H [] // H'. move/andP: (conj H' H). 
      rewrite -ltn_neqAle -subn_gt0 lt0n //.
    - move/eqP. move=> A B. move/andP:(conj A B). rewrite -ltn_neqAle -subn_gt0 => H.
      move/(leq_sub2r (size l2)). rewrite -addnBA // subnn addn0.       
      move/(leq_sub2r n1). rewrite subnAC addnC -addnBA // subnn addn0 -lt0n => /(leq_trans H) //.
  + admit.
  + admit.
 + (* 7/24 TODO: *) admit.
 + (* 8/24 *) 
    by move A0: (_ <= _) l1 => [] [|a1 l1'] //=;
    move A1: (_ <= _) => []; case A2: (n2  - n1) => [|n] // _ _;
    try case: (_ == _) => [] //; case: (rm _ _ _) => // [] // a;
    rewrite -?cons_wcons; case: (ins _ _ _) => [[]|]. 
 + (* 9/24 *) rewrite /openroot_in.
   case: (tr_rem _ _ _) => [] //=; rewrite ?andbT //.
   case: (nth _ _) => [a|] //. case A0: (rplc _ _ _) => [b|] //=.
   rewrite ?andbT. by move: A0 => /rplc_nonempty A0 /A0.
 + (* 10/24 *) repeat (move: (_ <= _) => []); move: l1 l2 => [|a1 l1] [|a2 l2] //=;
   move A0: (ins _ _ _) => [a|] // _ _ /=; move: A0 => /ins_nonempty; by rewrite ?andbT.
 + (* 11/24 TODO *) admit.
 + (* 12/24 TODO *) admit.
 + (* 13/24 *) repeat (move: (_ <= _) => [] //=); try by rewrite ?andbT;
    move A0: (rm _ _ _) => [a|] //; move A1: (ins _ _ _) => [[|b bl]|] //=.
    by rewrite ?andbT. by rewrite ?andbT.
 + (* 14/24 same as 9/24 *) rewrite /openroot_in.
   case: (tr_rem _ _ _) => [] //=; rewrite ?andbT //.
   case: (nth _ _) => [a|] //. case A0: (rplc _ _ _) => [b|] //=.
   rewrite ?andbT. by move: A0 => /rplc_nonempty A0 /A0.
 + (* 15/24 *) by case: (n1 < n2).
 + (* 16/24 *) case: l2 (n1 < n2) => [|a2 l2] [] _ _ //=; case: (_ <= _) => //=.
 + (* 17/24 *) case: (tr_uni _ _ _) => [_|] //=.
 + (* 18/24 *) case: (_ < _) (_ == _) => [] [] //=.
 + (* 19/24 *) by case: (_ == _) => [] //=; case: (jinterp _ _) => [_|] /=.
 + (* 20/24 *) by case: (tr_rem _ _ _) => [_|] //=; rewrite andbT.
 + (* 21/24 *) by case: (tr_uni _ _ _) => [_|] //=; rewrite andbT.
 + (* 22/24 *) move: (n1 < n2) (n2 < n1) => [] [] //= {IHc1}; try by rewrite andbT.
               by case: c1 => //= _ l l'; rewrite andbT.
 + (* 23/24 *) case: (n1 == n2).
  - by move /(IHc1 c2) => A /A; rewrite nonempty_map.
  - by rewrite /= andbT.
 + (* 24/24 *) by elim: (it c1 c2 f) => [] //=. Admitted.

Fixpoint jcmdsi cmd : nat := 
match cmd with
 | (JEditLabel c) => @cmdsi X C otX otcX c
 | (JUnite _ _ _) => 1
 | (JInsert  _ _) => 1
 | (JOpenRoot _ c) => jcmdsi c
 | _ => 0
end.

Fixpoint jcmdsz cmd : nat := 
match cmd with 
 | (JEditLabel c) => @cmdsz X C otX otcX c
 | (JRemove _ t) => weights t
 | (JInsert _ t) => weights t
 | (JOpenRoot _ c) => jcmdsz c
 | _ => 1
end.

Definition jsz := foldl addn 0 \o map jcmdsz.
Definition jsi := foldl addn 0 \o map jcmdsi.
Definition jcomputability := computability jit jsz jsi.

Ltac comp_unfold := rewrite /jcomputability /computability /flip /jit ?/tr_uni ?/openroot_in ?/tr_rem.

(* TODO: This lemma is true only for nonempty operations *)
(* Lemma jsz_nondg : forall cmd, 0 < jcmdsz cmd.
by elim=> //=; exact: sz_nondg. Qed. *)

Section WeightLemmata.

Lemma weights_ins l1: forall (n : nat) (l : seq (tree X)) r,
  ins n l1 l = Some r -> weights r = weights l1 + weights l.
elim => [l r|n] /=.
 + by case => <-; rewrite weights_app.
 + move => IHn [] // a l r /wcons_some [] x [] /IHn A1 ->.
   by rewrite ?weights_cons addnA (addnC (weights _)) -addnA A1. Qed.

Lemma weights_rm (l1 : seq (tree X)) l2 l3 n: rm n l2 l1 = Some l3 -> 
 weights l3 + weights l2 = weights l1.
elim: n l1 l2 l3 => [|n IHn] //.
 + move => l1 l2 l3 => /rm_eq <-. by rewrite weights_app addnC.
 + case => [|a1 l1] /= [|a2 l2] l3 //. 
  + by case => <-. 
  + case => <- /=. by rewrite {2}/weights /= addn0.
  + move => /wcons_some [] x [] /IHn; rewrite ?weights_cons => <- ->.
    by rewrite weights_cons ?addnA. Qed.

Lemma weights_Node (x : X) l: weights [:: Node x l] = weights l + 1.
by rewrite {1}/weights /= weight_Node addn0. Qed.

Lemma weights_rplc {n} {t : tree X} {l l1 b}: nth n l = Some l1 -> 
rplc n (Some t) l = Some b -> weights b + weight l1 = weight t + weights l.
elim: n l b => [|n IHn] /= [|a l] // b.
 + move => [] -> [] <-. rewrite ?weights_cons. ssromega.
 + move => A0 /wcons_some [] x [] /(IHn _ _ A0) A1 ->; rewrite ?weights_cons. ssromega. Qed.

End WeightLemmata.

Lemma ins_rm_corr {l1 n1 l2 n2}: 
   jcomputability (JInsert n1 l1) (JRemove n2 l2). 
Proof.  comp_unfold => _. case: l2 => [|l2 l2s] /=.
 - rewrite addn0 [n2 <= n1]leqNgt [n1 <= n2]leqNgt; case: (ltngtP n1 n2) => /=;
   rewrite /jsz /jsi /= ?add0n ?addn0; eauto.
 - case: (int_ptP n2 (size l2s) n1) => /=; try (case A1: ins => [r_ins|] /=);
   rewrite ?leqnn ?leqnSn; eauto; rewrite /jsz /jsi /= ?add0n ?addn0 => _ _; split => //; eauto. 
   - by move: A1 => /weights_ins ->.
   - by apply /leq_addl. Qed.

Lemma ins_uni_corr {n1 l1 n2 x2 l2}: jcomputability (JInsert n1 l1) (JUnite n2 x2 l2).
comp_unfold => _. case: l2 => [|l2 l2s] /=.
+ case: (n2 <= n1); rewrite /jsz /jsi /=; nat_norm; eauto.
+ case: (n1 <= n2); case: (n2 + (size l2s).+1 <= n1);
  rewrite /jsz /jsi /=; try (case: (ins _ _ _)); nat_norm; eauto. Qed.

Lemma ins_flat_corr {n1 l1 n2 x2 l2}:
  jcomputability (JInsert n1 l1) (JFlat n2 (Node x2 l2)).
Proof. comp_unfold; rewrite [n1 <= n2]leqNgt => _.
 case: ltngtP => //=; rewrite ?leqnn ?leqnSn; intuition. Qed.

Lemma L0: forall n (l1 l2 : seq (tree_eqType X)), 
  weights (rotr n (drop (size l1) (rot n l2))) <= weights l2.
by elim => [|n IHn] l1 l2 /=; rewrite ?weights_rotr ?weights_rot;
 [set j := rot 0 l2 | set j := rot (n.+1) l2]; 
 move: (weights_drop (size l1) j); rewrite ?weights_rot. Qed.

Lemma rm_rm_corr {n1 l1 n2 l2}:
   jcomputability (JRemove n1 l1) (JRemove n2 l2).
Proof. comp_unfold => _.
 case: (interval_interval_case_analP);
 rewrite /jsz /jsi /= ?addn0 ?add0n; eauto; 
 move => _ _; try move => _; split => //;
 try (split; [done| left; split]) => //;
 (try apply leq_add); (try apply weights_drop); (try apply weights_take);
 [rewrite -ltnS -addnS; apply ltn_addl; rewrite ltnS| |
  rewrite addnC -ltnS -addnS; apply ltn_addl; rewrite ltnS |]; apply L0. Qed.

Lemma L1 (l : tree X): weights [:: l] = weight l.
by rewrite /weights /= addn0. Qed.

Lemma L2 n (l : seq (tree X)): weights (take n l) + weights (drop n l) = weights l.
elim: n l => [|n IHn] [|a l] //=. by rewrite ?weights_cons -addnA (IHn l). Qed.

Lemma rm_uni_corr {n1 l1 n2 x2 l2}:
  jcomputability (JRemove n1 l1) (JUnite n2 x2 l2).
Proof. comp_unfold.
 case: (interval_interval_case_analP) => /=;
 move: l1 l2 => [|l1 l1s] [|l2 l2s]; try (by simpl; eauto);
 move => _ _ _; try move => _;
 try (move: (l1 :: l1s) (l2 :: l2s) => l1' l2';
        case A0: (rm _ _ _) => /= [z|]; try case A1: (ins _ _) => [z2|] //=);
 rewrite /jsz /jsi /= ?addn0 ?add0n; eauto;
 (try by move: A0 => /weights_rm <-; move: A1 => /weights_ins ->; rewrite weights_Node;
   split;[ssromega| split;[|right]]);
 [move: ((size l2s).+1 + n2 - n1) => [|n] /=| move: (n2 - n1) => [|n] /=]; eauto;
   rewrite ?weights_cons -?addnA ?addnS addn0 L2 addn0; eauto. Qed.

Lemma rm_flat_corr {n1 l1 n2 x2 l2}:
  jcomputability (JRemove n1 l1) (JFlat n2 (Node x2 l2)).
Proof. comp_unfold => _; case: (int_pt_incP n1 (size l1) n2);
case: l1 => [|a1 l1]; try by (rewrite /jsz /jsi /=; nat_norm; eauto).
case: (n2 - n1) => [|d].
 + simpl. case A0: (a1 == Node x2 l2) => /= _ _; eauto.
   move: A0 => /eqP ->. rewrite rm_id. case A0: (l2 ++ l1) => [|a l]; eauto.
   move: A0 => <-; rewrite /jsz /jsi /= weights_app weights_cons weight_Node; nat_norm.
   split; try split; try done; try left; by elim: (addn _ _) => [] //.
+  move A0: (rm _ _ _) => [[|w ws]|]; try move A1: (ins _ _ _) => [[|z zs]|];
   try by rewrite /jsz /jsi /= ?add0n ?addn0; eauto.
   move: A0 => /weights_rm A0. move: A1 => /weights_ins A1.
   rewrite /jsz /jsi /= ?add0n ?addn0 A1 -A0 weights_Node; intuition.
   ssromega. left. split => //. ssromega. Qed.

Lemma weights_interp {a b c} {l : seq (tree X)} {n}: 
nth n l = Some a -> rplc n (jinterp c a) l = Some b ->
   weights b <= (jcmdsz c) + weights l /\ (weights b <= weights l \/ (0 < jcmdsi c)).
elim: c l a n b => [n1 l1|n1 l1 |n1 s l1| n1 t|n1 j IH| c] /= l a n b A0.
 + case: a A0 => [x xs]. move A0: (NodeW _ _) => [[x2 l2]|] //=.
  + move: A0 => /nodew_some [] _ /weights_ins A0 A1 /(weights_rplc A1).
    rewrite ?weight_Node A0 => A2. split. ssromega. by right.
  + by rewrite rplc_none_none.
 + case: a A0 => [x xs]. move A0: (NodeW _ _) => [[x2 l2]|] //=.
  + move: A0 => /nodew_some [] _ /weights_rm A0 A1 /(weights_rplc A1).
    rewrite ?weight_Node -A0 => A2. split. ssromega. left. ssromega.
  + by rewrite rplc_none_none.
 + case: a A0 l1 => [x xs] A0 [|a1 l1] A1.
  + move: (weights_rplc A0 A1) => A2. split. ssromega. by right.
  + move A2: (rm _ _ _) A1 => [xs'|]; try move A3: (NodeW _ _) => [[x2 l2]|] //=; 
    try by rewrite rplc_none_none. move => A4.
    move: (weights_rplc A0 A4). move: A3 => /nodew_some [] -> /weights_ins.
    move: A2 => /weights_rm. rewrite weights_Node ?weight_Node => <- ->. split. ssromega. by right.
 + case: a A0 t => [x xs] A0 [z zs]. move A1: (nth _ _) => [[y ys]|]; 
   try move A22: (_ && _) => [/andP [/eqP A21 /eqP]|]; try move A3: (rm _ _ _) => [a|] /=; 
   try move A4: (ins _ _ _) => [c|] /=; try by rewrite rplc_none_none.
   move => /(weights_rplc A0). move: A4 => /weights_ins. move: A3 => /weights_rm.
   rewrite ?weights_Node ?weight_Node => <- -> A2. split; try left; ssromega.
 + case: a A0 => [t l0] A0; case A1: (nth _ _ ) => [x'|];
   try move A2: (rplc n1 _ _) => [l1|] /=; try move => /(weights_rplc A0);
   try move: (IH _ _ _ _ A1 A2) => [] IH0 IH1; try (case A3: (jinterp _ _) A2 => [t1|]);
   try by rewrite ?rplc_none_none. rewrite ?weight_Node. move /(weights_rplc A1) => H0 H1.
   split. ssromega. move: IH1 => [H2|]. left. ssromega. by right.
 + case: a A0 => t1 l1 A1. case: (interp c t1) => [a /(weights_rplc A1)|].
   rewrite ?weight_Node => A2. have: (weights b = weights l) by ssromega. 
   move => ->. split. ssromega. left. done. by rewrite rplc_none_none. Qed.

Lemma rm_or_corr {n1 l1 n2 c2} : 
  jcomputability (JRemove n1 l1) (JOpenRoot n2 c2).
Proof. comp_unfold; rewrite /tr_rem /openroot_in /tr_rem.
 case: (int_pt_incP n1 (size l1) n2) => /=; eauto;
 case A0: nth => [a|]; eauto.
 case A1: (rplc _ _ _) => [b|]; eauto.
 move => _ _ _. rewrite /jsz /=; nat_norm.
 move: (weights_interp A0 A1) => [H0 H1].
 split. by rewrite addnC. split. done. by case: H1; [left|right]. Qed.

Lemma uni_uni_corr {n1 x1 l1 n2 x2 l2} :
  jcomputability (JUnite n1 x1 l1) (JUnite n2 x2 l2).
Proof. comp_unfold => srv. case: (interval_interval_case_analP) => /=; case: srv => /=; try (by intuition);
 case: rm => [?|]; try (by intuition); case: ins => [?|]; try (by intuition). Qed.

Lemma  uni_flat_corr {n1 x1 l1 n2 x2 l2}:
  jcomputability (JUnite n1 x1 l1) (JFlat n2 (Node x2 l2)).
Proof. comp_unfold.
 case: (int_pt_incP n1 (size l1) n2) => /=; try (by intuition).
 case: rm => [?|]; try (case: ins => [[|??]|]); by intuition. Qed.

Lemma uni_or_corr {n1 x1 l1 n2 c2}:
  jcomputability (JUnite n1 x1 l1) (JOpenRoot n2 c2).
Proof. comp_unfold.
 case: (int_pt_incP n1 (size l1) n2) => /=; try (by intuition).
 case: nth => [?|]; try (case: rplc => [?|]); by intuition. Qed.

Lemma flat_flat_corr {n1 x1 l1 n2 x2 l2}:
  jcomputability (JFlat n1 (Node x1 l1)) (JFlat n2 (Node x2 l2)).
Proof. comp_unfold => _. rewrite eq_sym.
case: (ltngtP n2 n1) => /=; by intuition. Qed.

Lemma flat_or_corr {n1 x1 l1 n2 c2}:
  jcomputability (JFlat n1 (Node x1 l1)) (JOpenRoot n2 c2).
Proof. comp_unfold => _. case: (ltngtP n1 n2) => /=; try (by intuition).
case: c2 => [n' l'|n' l'|n' x' l'|n' [x' l']|n' c'|c1']; case: jinterp => [?|] /=; by intuition. Qed.

Lemma or_or_corr {n1 c1 n2 c2}:
 (forall op2, jcomputability c1 op2) -> jcomputability (JOpenRoot n1 c1) (JOpenRoot n2 c2).
Proof. move=> IH. rewrite /jcomputability /computability /jsz /jsi /flip => /=; rewrite eq_sym.
 case: (n2 == n1) => /= srv; try (by intuition).
 move: (IH c2). rewrite /jcomputability /computability /jsz /jsi /flip => /(_ srv) /= [] H1 [] H2 H3. 
 split. rewrite -!map_comp. exact: H1.
 split. by rewrite -!map_comp. rewrite -!map_comp. case: H3 => H3. by left. right. done. Qed.

Lemma el_el_corr {c1 c2}:
  jcomputability (JEditLabel c1) (JEditLabel c2).
Proof. 
 comp_unfold; rewrite /jsz /jsi /comp => srv.
 move: (@comp_corr X C otX otcX c1 c2 srv). by rewrite /flip /si /sz -?map_comp. Qed.

Lemma ins_ins_corr {n1 l1 n2 l2} :
  jcomputability (JInsert n1 l1) (JInsert n2 l2).
Proof. by comp_unfold; rewrite eq_sym => srv; case: eqP => H; case: srv => /=; rewrite ?leqnn; intuition. Qed.

Ltac symm1 := rewrite [jsi _ + jsi _]addnC [jsz _ + jsz _]addnC (and_comm (jsz _ <= _))
                      [(jsi ([:: _])) + _]addnC [(jsz ([:: _])) + _]addnC.
Ltac symm2 := rewrite [jsi _ + jsi _]addnC [jsi [:: _] + jsi [:: _]]addnC 
                      [jsz _ + jsz _] addnC [jsz [:: _] + jsz [:: _]]addnC
                      (and_comm (jsz _ <= jsz [:: _])).

(*TODO: Fix holes in the proof *)
Theorem jcomp_corr: forall (op1 op2 : jcmd), 
  jcomputability op1 op2.
Proof. elim => [n1 l1|n1 l1|n1 x1 l1|n1 [x1 l1]|n1 c1 IHc1|c1] 
               [n2 l2|n2 l2|n2 x2 l2|n2 [x2 l2]|n2 c2|c2] srv; 
         try (simpl; by comp_unfold; nat_norm; intuition);
         move => op1' op2'; subst op1' op2'.
  + exact: ins_ins_corr.
  + exact: ins_rm_corr.
  + exact: ins_uni_corr.
  + exact: ins_flat_corr.
  + symm1. exact: ins_rm_corr.
  + exact: rm_rm_corr.
  + exact: rm_uni_corr.
  + exact: rm_flat_corr.
  + exact: rm_or_corr.
  + symm1; exact: ins_uni_corr.
  + symm1; exact: rm_uni_corr.
  + exact: uni_uni_corr.
  + exact: uni_flat_corr.
  + exact: uni_or_corr.
  + symm1; exact: ins_flat_corr.
  + symm1; exact: rm_flat_corr.
  + symm1; exact: uni_flat_corr.
  + exact: flat_flat_corr.
  + exact: flat_or_corr.
  + symm2; exact: rm_or_corr.
  + symm2; exact: uni_or_corr.
  + symm2; exact: flat_or_corr.
  + exact: or_or_corr.
  + exact: el_el_corr. Qed.

Theorem jip1 : forall op m mr, jinterp op m = Some mr -> jinterp (jinv op) mr = (Some m).
Proof. elim => [n1 l1|n1 l1|n1 x1 l1|n1 [x1 l1]|n1 c1 IHc1|c1] [x xs] [rx rxs] //=.
 + by move/nodew_some => []-> /rm_ins_id ->.
 + move/nodew_some => [] ->; case: l1 => [|x1 l1] /=.
  - by rewrite rm_id => [] [] -> /=.
  - by move/ins_rm_id => /(_ (ltn0Sn _)) ->.
 + case: l1 => [|l1 l1s] //=.
   case Hrm: rm => [r_rm|//] /nodew_some [] -> H; move:(H).
   move/ins_some_nth_in => /(_ 0 (ltn0Sn _)). rewrite addn0 => -> /=; rewrite ?eq_refl orm_some /=.
   apply/nodew_some; split => //. move/rm_ins_id: H ->.  by move/ins_rm_id: Hrm => /(_ (ltn0Sn _)).
 + case: l1 => [|l1 l1s] //; case: nth => [r_nth|] //; case: r_nth => [z zs];
   case: eqP =>// <- /=; case: eqP => // <- /nodew_some [] ->; case Hrm: rm => [r_rm|] //=.
  - move=> /ins_id <-. move: Hrm => /ins_rm_id => Hrm. by rewrite Hrm.
   by move/rm_ins_id ->; move/ins_rm_id: Hrm => /(_ (ltn0Sn _)) ->. 
 + case Hnth: nth => [r_nth|]// /nodew_some [] <-. case Hjint: jinterp => [r_jint|]; try by rewrite rplc_none_none. 
   move=> Hrplc.  move/rplc_nth_eq:(Hrplc) ->.  
   by rewrite (IHc1 _ _ Hjint) -Hnth orplc_some -Hrplc orplc_some rplc_rplcC_eq /= (rplc_nth_id' _ _ _ Hnth).
 + case Hinterp: interp => [?|] // [] <- <-.
   by move: (@ip1 _ _ _ ipX _ _ _ Hinterp) ->. Qed.

Theorem c1: forall (op1 op2 : jcmd) (f : bool) (m m1 m2 : tree X),
 jinterp op1 m = Some m1 ->
 jinterp op2 m = Some m2 ->
 let m21 := exec_all jinterp (Some m2) (jit op1 op2 f) in let m12 := exec_all jinterp (Some m1) (jit op2 op1 (~~ f)) in m21 = m12 /\ (exists node : tree X, m21 = Some node).
Admitted.

Instance jOT : OTBase (tree X) jcmd := {interp := jinterp; it := jit; it_c1:=c1}.
(*TODO: Prove commutation *)


(*TODO: Restrict to nonempty operations 
Instance jInv : OTInv (tree X) jcmd jOT := {inv := jinv; ip1 := jip1}.
Instance jCompOT : OTComp jOT := {cmdsz := jcmdsz; cmdsi := jcmdsi; (*sz_nondg := jsz_nondg; *) comp_corr := jcomp_corr}.
Admitted. *)

End RichTextOTDefinition.

Arguments JEditLabel [X] [C].
Arguments JInsert [X] [C].
Arguments JRemove [X] [C].
Arguments JUnite [X] [C].
Arguments JFlat [X] [C].
Arguments JOpenRoot [X] [C].
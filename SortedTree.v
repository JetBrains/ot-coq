Require Import eqtype seq path ssrfun.
Require Import Basics Commons Tree OtDef ListTools Comp.
Import Bool.

Definition asymmetric {T} (R : rel T) := (forall x y : T, R x y = ~~(R y x)).

Definition order {T} (R : rel T) := total R /\ irreflexive R /\ asymmetric R /\ transitive R.

Ltac expand_order X := move: X; repeat (let HN := fresh in move => [] HN); let HN := fresh in move => HN.
Ltac mf := (let f := fresh in move => f).

Lemma order_irr {T : eqType} {R} {x y : T} (Rord : order R): R x y -> (x == y) = false.
expand_order Rord. by move: (H0 x); case: eqP => // -> ->. Qed.

Section InsertRaw.

Context {X : eqType} {R : rel X} (Rord : order R).

Fixpoint g_insert x xs : seq X :=
 match xs with
 | xh :: xt => if x == xh then xs else if R x xh then x :: xs else xh :: g_insert x xt
 | _ => [:: x] end.

Lemma g_insert_ind1 x x0 xs: g_insert x (x0 :: xs) = 
      match x0 == x, R x0 x with 
       | true, _ => x0 :: xs
       | _, true => x0 :: (g_insert x xs) 
       | _, _    => x :: x0 :: xs end.
expand_order Rord => /=. rewrite H1 eq_sym.
case A0: (x0 == x). move: A0 => /eqP -> //. by case: (R x0 x) => /=. Qed.

Lemma g_insert_insert {x y xs} :
  g_insert x (g_insert y xs) = g_insert y (g_insert x xs).

expand_order Rord. elim: xs x y => [| x0 xs IH] x y.
 + by rewrite /= eq_sym H1; case A0: eq_op; case: (R _ _) A0 => // /eqP ->.
 + rewrite ?g_insert_ind1; case A0: (x0 == x); case A1: (x0 == y) => //=; rewrite ?g_insert_ind1.
  * by move: A0 A1 => /eqP -> /eqP ->.
  * move: A0 => /eqP <-. rewrite eq_sym A1 H1. by case A2: (R y x0); rewrite /= eq_refl ?A1 // H1 A2.
  * move: A1 => /eqP <-. rewrite eq_sym A0 H1. by case A2: (R x0 x); rewrite /= eq_refl ?A0 // A2.
  * by case A2: (R x0 y); case A3: (R x0 x); rewrite ?g_insert_ind1 A0 A1 A2 A3; 
    [rewrite IH // |
     have: (R x y) by apply (H2 x0 x y) => //; rewrite H1 A3 |
     have: (R y x) by apply (H2 x0 y x) => //; rewrite H1 A2 |
     rewrite eq_sym H1; (case: eqP => [->| _]); case: (R x y) => //];  
     move => A4; rewrite A4 (order_irr Rord). Qed.

Lemma path_g_insert x c cs: path R x (g_insert c cs) = path R x cs && R x c.
expand_order Rord. elim: cs c x => [|c' cs IH] c x//=. by rewrite andb_true_r. case A0: (eq_op).
 + move: A0 => /eqP -> /=. by rewrite andb_comm -andb_assoc andb_diag.
 + case A1: (R c c') => /=; 
     [rewrite A1 andb_true_l; case A2: (R x c) => //|
      rewrite IH; rewrite H1 in A1; apply negb_false_iff in A1; rewrite A1; case A2: (R x c')];
   try (by rewrite (H2 _ _ _ A2 A1) ?andb_true_l andb_true_r);
        by rewrite andb_false_l ?andb_false_r. Qed.

Lemma g_insert_path {x xs} : path R x xs -> g_insert x xs = x :: xs.
expand_order Rord. case: xs => // xh xt /=. case E: (x == xh).
 + by move /eqP in E; rewrite -E (H0 x).
 + by move /andP => [-> _]. Qed.

Local Notation "x <<: y" := (path R x y) (at level 70).

Lemma path_trans {x y xt} : R x y -> y <<: xt -> x <<: xt.
expand_order Rord. by case: xt => //= xth [|xtth xttt] H3 /andP [] G; rewrite /= (H2 _ _ _ H3 G). Qed.

Lemma g_filter_insert {p x xs} (P : p x = true) : sorted R xs
  -> g_insert x (filter p xs) = filter p (g_insert x xs). 
elim: xs => [|xh xt IHxs].
+ by rewrite /= P.
+ move => /=; case E: (x == xh).
  * by move /eqP in E; rewrite -E P /= eq_refl P.
  * by move => S; move: (S) => H; apply path_sorted, IHxs in H;
    case G: (p xh) => /=; case J: (R x xh);
    rewrite /= ?E ?P G // H // (g_insert_path (path_trans J S)) /= P. Qed.

End InsertRaw.

Section SortedTree.

Context {T : eqType} (R : rel T) (Rord : order R).

Fixpoint is_tree_sorted t := match t with Node _ cs => sorted R (map value cs) && all is_tree_sorted  cs end.

Structure sorted_tree : Type := STree {
  treeOf :> tree T;
  stp    : is_tree_sorted treeOf}.

Definition SNode (t : T) : sorted_tree. by apply (@STree (Node t [::])). Defined.

Canonical  sorted_tree_subType := Eval hnf in [subType for treeOf].
Definition sorted_tree_eqMixin := Eval hnf in [eqMixin of sorted_tree by <:].
Canonical  sorted_tree_eqType  := Eval hnf in  EqType (sorted_tree) sorted_tree_eqMixin.

Require Import ProofIrrelevance.

Lemma st_eq (t1 t2 : sorted_tree): t1 = t2 <-> treeOf t1 = treeOf t2.
 split. 
 + by move: t1 t2 => [t1 ?] [t2 ?] [].
 + case: t1 t2 => [t1 S1] [t2 S2] /= A0. subst.
   by move: (proof_irrelevance _ S1 S2) => ->. Qed.

Corollary opt_eq (t1 t2 : option sorted_tree): t1 = t2 <-> (maybe treeOf) t1 = (maybe treeOf) t2.
case: t1 t2 => [t1|] [t2|] //=. by split; case => /st_eq ->. Qed.

Definition treeR (x y : tree T) := R (value x) (value y).

Lemma treeR_order: order treeR.
 expand_order Rord. rewrite /order /total /transitive /irreflexive /asymmetric.
 by repeat (split; repeat (case; mf; mf)); rewrite /treeR /=; 
  [apply H | apply H0 | apply H1|move: H9 H10; rewrite /treeR /=; apply H2]. Qed.

Corollary sorted_tree_uniq v ls: is_tree_sorted (Node v ls) -> uniq (map value ls).
expand_order Rord. rewrite /= andb_comm => /andP [] _. by apply sorted_uniq. Qed.

Lemma path_compatibility xs x: path R (value x) (map value xs) = path treeR x xs.
elim: xs x => [|x' xs IH] //= x. by rewrite IH /treeR. Qed.

Corollary sorted_compatibility xs: sorted R (map value xs) = sorted treeR xs.
case: xs => [|x xs] //=. apply path_compatibility. Qed.

Definition by_value v : tree T -> bool := eq_op v \o value.

Lemma by_diff_values  {vx vy} : (vx == vy) = false -> negb \o (by_value vx) --- by_value vy.
 move => Eq [v cs]; rewrite /by_value /comp /negb /=.
 case H: (vx == v) => //.
 by move /eqP in H; rewrite H eq_sym in Eq. Qed.

(* Insert operation *)

Definition insert := @g_insert _ treeR.

Corollary insert_insert xt yt xs : insert xt (insert yt xs) = insert yt (insert xt xs).
rewrite /insert. rewrite g_insert_insert //. apply treeR_order. Qed.

Corollary filter_insert {p x xs} : p x = true -> sorted treeR xs -> 
   insert x (filter p xs) = filter p (insert x xs). 
rewrite /insert. by apply (@g_filter_insert _ _ treeR_order). Qed.

Lemma find_insert_t {xs p x}: p x = true -> has p xs = false -> find p (insert x xs) = Some x.
by elim: xs x => [|x0 xs IH] x /= A0;
 [intros; rewrite A0| move => A1; case A2: eq_op; [move: A2 A0 A1 => /eqP -> -> |
   case A3: (treeR _ _) => /=; [rewrite A0 | move: A1 => /orb_false_iff [] -> ?; apply IH]]]. Qed. 

Corollary find_insert_f {xs p x}: p x = false -> find p (insert x xs) = find p xs.
 elim: xs => [/= -> |xh xt IHxs] //= H; case A0: (x == xh) => /=.
   + by rewrite -(eqP A0) H.
   + by case A1: (treeR x xh) => /=; rewrite ?H ?(IHxs H). Qed.

Lemma has_insert f s cs: has f (insert s cs) = has f cs || (f s).
rewrite /insert; elim: cs => /= [| a cs IHa].
 + by rewrite orb_false_r.
 + case A0: eq_op => /=. move: A0 => /eqP ->. 
   by rewrite orb_comm -orb_assoc orb_diag.
   case: (treeR s a) => /=.
     by rewrite orb_comm.
     by rewrite IHa orb_assoc. Qed.

Corollary insert_has_f {p} x {xs} : p x = false -> has p (insert x xs) = has p xs.
 by rewrite has_insert => ->; rewrite orb_false_r. Qed.

Corollary insert_has_t {p} x {xs} : p x = true -> has p (insert x xs) = true.
 by rewrite has_insert => ->; rewrite orb_true_r. Qed.

Corollary insert_has_absent {p x xs} : has p (insert x xs) = false -> has p xs = false.
 by rewrite has_insert; move: p (has p) => [] []. Qed.

Lemma insert_sorted c cs: sorted treeR cs -> sorted treeR (insert c cs).
case: cs => [|c' cs] //= A0.
case A1: (eq_op) => //. expand_order treeR_order.
case A2: (treeR c' c); move: A2; rewrite H1.
 + move => /negb_true_iff A2. rewrite A2 /= /insert path_g_insert.
   by rewrite (H1 c' c) A2 A0. apply treeR_order.
 + move => /negb_false_iff A2. by rewrite A2 /= A0 A2. Qed.

Lemma find_by_value {v v' xs ys} : find (by_value v) xs = Some (Node v' ys) -> v = v'.
by elim: xs v => [|[xv xl] xs IHx] v //=;  rewrite /by_value /=; case: eqP => [-> [] //| _ /IHx]. Qed.

Lemma insert_all c cs p: all p (insert c cs) = all p cs && (p c).
elim: cs c => [|c' cs IH] c /=. by rewrite andb_true_r.
case A0: eq_op => [].
 + by move: A0 => /eqP -> /=; rewrite andb_comm -andb_assoc andb_diag.
 + case: (treeR _ _) => [] /=.
  * by rewrite andb_comm.
  * by rewrite IH andb_assoc. Qed.

(* Without operation *)

Definition without v := filter (negb \o (by_value v)).
Definition without' := locked without.

Lemma without_has v xs: has (by_value v) (without v xs) = false.
by elim: xs => [|[v1 xs'] xs IH]; rewrite /without -?lock //=; rewrite /by_value /=;
 case A0: eq_op => /=; rewrite ?A0 ?orb_false_l ?IH. Qed.

Lemma without_has' v v' xs: (v' == v) = false -> has (by_value v) (without v' xs) = has (by_value v) xs.
move => A0. by apply has_filter, by_diff_values. Qed.

Lemma without_find' v v' xs: (v' == v) = false -> find (by_value v) (without v' xs) = find (by_value v) xs.
move => A0. by apply find_filter, by_diff_values. Qed.

Corollary without_has_false v v' xs: has (by_value v) xs = false -> has (by_value v) (without v' xs) = false.
case A0: (v' == v).
 + move: A0 => /eqP ->. by rewrite without_has.
 + by rewrite without_has'. Qed.

Lemma without_inv v xs: without v (without v xs) = without v xs.
by elim: xs => [|x xs IH] //=; case A0: (by_value _ _); rewrite /= ?A0 /= IH. Qed.

Lemma without_without v v' xs: without v (without v' xs) = without v' (without v xs).
elim: xs => [|x xs IH] //=; case A0: by_value => //=; case A1: by_value => //=.
 + by rewrite A0. + by rewrite A0 /= IH. Qed.

Lemma without_path v c cs: path treeR c cs -> path treeR c (without v cs).
elim: cs v c => [|x cs IH] v c //= /andP [] A0 A1. rewrite /by_value /=. case A2: eq_op => /=.
 + apply IH. apply path_trans with (y := x) => //. apply treeR_order.
 + rewrite A0 /=. by apply IH. Qed.

Lemma without_insert_i t1 cs vt: value t1 = vt -> 
   without vt (insert t1 cs) = without vt cs.
elim: cs t1 vt => [|c cs IH] t1 vt //=; rewrite /by_value /=.
 + by move => ->; rewrite eq_refl /=.
 + move => <-. 
   by case A0: eq_op; [move: A0 => /eqP -> /= |
   case A1: eq_op; case: (treeR _ _) => /=; rewrite /by_value /= A1 ?eq_refl //= ?IH]. Qed.

Lemma without_insert t1 v2 cs: sorted treeR cs -> (value t1 != v2) ->
 insert t1 (without (v2) cs) = without (v2) (insert t1 cs).
elim: cs => [|c cs IH] /=. 
 + intros ?. by rewrite /by_value /= eq_sym => ->.
 + move => H0 A0. rewrite /by_value /=.
   case A1: eq_op => /=; case A2: eq_op => /=; rewrite /by_value /=.
  * move: A2 A1 A0 => /eqP <-. by rewrite eq_sym => ->.
  * case A3: treeR => /=; rewrite /by_value /= ?A1 /=.
   + rewrite eq_sym A0. apply path_trans with (x:= t1), (without_path (v2)), g_insert_path in H0;
      (try by apply treeR_order). rewrite /insert H0 //. apply A3.
   + rewrite IH => //. by move: H0 => /path_sorted.
  * by rewrite A1 /=.
  * case: (treeR t1 c) => /=; rewrite /by_value /= ?A1 /=.
   + by rewrite eq_sym A0.
   + rewrite IH => //. by move: H0 => /path_sorted. Qed.

Lemma without_first: forall cs c v w cw, path treeR c cs -> without v cs = w :: cw -> treeR c w.
elim => [|c' cs' IH] c v w cw //= /andP [] A0 A1; case (by_value _) => /=.
 + move => A2. apply (IH c') in A2; [|done]. expand_order treeR_order. by apply (H2 c' c w).
 + by case => [] <-. Qed.

Lemma without_sorted cs v: sorted treeR cs -> sorted treeR (without v cs).
elim: cs => [|c cs IH] //= A0.
 case A1: (by_value v c) => /=.
 + by move: A0 => /path_sorted /IH.
 + assert (A0' := A0). move: A0 => /path_sorted /IH.
   case A2: (without _ _) => [| w cw] //= ->. rewrite andb_true_r. 
   move: A0' A2. apply /without_first. Qed.

Lemma has_without v cs: has (by_value v) cs = false -> without v cs = cs.
elim: cs v => [|c cs IH] v //=. by case A0: (by_value v c) => //= /IH ->. Qed.

Lemma has_path c cs: path treeR c cs -> has (by_value (value c)) cs = false.
elim: cs c => [|c' cs IH] c //= /andP [] A0 A1. have: (path treeR c cs) by move: A0 A1; apply path_trans, treeR_order.
move => /IH => ->. move: A0. by rewrite orb_false_r /by_value /treeR /= => /(order_irr Rord). Qed. 

Corollary path_without vc vcs cs: path treeR (Node vc vcs) cs -> without vc cs = cs.
move => /has_path. apply has_without. Qed.

Lemma path_find t t' cs v: path treeR t cs -> find (by_value v) cs = Some t' -> R (value t) (value t').
elim: cs t t' v => [|[vc vcs] cs IH] t t' v //= /andP [] A0 A1. rewrite /by_value /=. case A2: (v == vc).
 + case => <- /=. by move: A0; rewrite /treeR.
 + apply IH. clear IH. case: cs A1 => [|[vc0 vcs0] cs] //= /andP [] A1 ->. rewrite andb_true_r.
   case: t A0 A1 => [vt vts]; rewrite /treeR /=. expand_order Rord. apply H2. Qed.

Lemma path_has x xs: path treeR x xs -> has (by_value (value x)) xs = false.
expand_order Rord. elim: xs x => [|x' xs IH] //= x /andP []; rewrite /by_value /=. case A0: (eq_op).
 + by move: A0 => /eqP /=; rewrite /treeR => ->; rewrite H0.
 + move => A1 A2; rewrite IH //. move: A1 A2. apply path_trans, treeR_order. Qed.

Lemma insert_same v a cs: sorted treeR cs -> find (by_value v) cs = Some a -> insert a (without v cs) = cs.
elim: cs a v => [|[vc vcs] cs IH] a v //=; rewrite /by_value /=. case A0: (v == vc) => /= A1 [].
 + rewrite /insert => <-. move: A0 => /eqP ->. assert (A1':=A1). move: A1' => /path_without ->.
   by rewrite g_insert_path; try apply treeR_order.
 + move => A2. case A3: (eq_op _ _) => /=. move: A3 A2 => /eqP -> /find_pred /=. by rewrite A0. 
   case A4: (treeR a _). have: (treeR (Node vc vcs) a) by move: A1 A2; apply /path_find.
   expand_order treeR_order. by rewrite H1 A4.
 + rewrite IH => //. by apply path_sorted in A1. Qed.

(* Open operation *)

Definition label_preserving (f : tree T -> option (tree T)) := 
 forall t', match f t' with Some t => value t = value t' | _ => True end.

Definition open (f : tree T -> option (tree T)) (vo : T) (t : tree T) := 
 match t with Node v cs => 
   match (optf f) (find (by_value vo) cs) with 
     Some fch => Some (Node v (insert fch (without vo cs)))
     | _ => None end end.

Lemma find_sorted v p cs t: is_tree_sorted (Node v cs) -> find p cs = Some t -> is_tree_sorted t.
elim: cs v => [|c' cs IH] v //= /andP [] A0 /andP [] A1 A2; case: (p c').
 + by case => <-.
 + apply (IH v). by move: A0 => /path_sorted /= -> /=. Qed.

Lemma all_without p v cs: all p cs -> all p (without v cs).
elim: cs => [|c cs IH] //= /andP []; case A0: by_value => /=; [intros ?|move => -> /=]; apply IH. Qed.

End SortedTree.

Implicit Arguments treeOf [[T] [R]].
Implicit Arguments without_insert [[T] [R]].

(* find/has simplification tactics *)

Ltac use_sortedness S := repeat first [apply without_sorted | apply insert_sorted | by (move: S; rewrite /is_tree_sorted => /andP []; rewrite sorted_compatibility)].

Ltac sop_simpl :=
let fi_t := rewrite find_insert_t //=; (try subst); 
            try (by rewrite ?/by_value /= eq_refl); try (by apply without_has) in
let fi_f := rewrite find_insert_f; [| by rewrite /by_value /= // eq_sym //] in
let wf' := rewrite without_find'; [| by rewrite // eq_sym] in
let wh' := rewrite without_has'; [| by rewrite // eq_sym] in
(subst; repeat first [rewrite eq_refl /= | rewrite /without' -lock | 
rewrite without_has | rewrite without_inv | match goal with
 | [ H : has (by_value ?v) ?cs = false |- context [without ?v ?cs] ] => rewrite (has_without _ _ H)
 | [ |- context [find (by_value (value ?v1)) (insert _ ?v1 _)] ]   => fi_t
 | [ |- context [find (by_value ?v1) (insert _ (Node ?v1 _) _) ] ] => fi_t
 | [ |- context [find (by_value ?v1) (insert _ ?v2 _)] ] => fi_f
 | [ |- context [without _ (insert _ _ _)]] => rewrite without_insert_i; [| by done]
 | [ H : (?v1 == ?v2) = false |- context [find (by_value ?v1) (without ?v2 _)]] => wf'
 | [ H : (?v2 == ?v1) = false |- context [find (by_value ?v1) (without ?v2 _)]] => wf'
 | [ H : (?v1 == ?v2) = false |- context [has (by_value ?v1) (without ?v2 _)]] => wh'
 | [ H : (?v2 == ?v1) = false |- context [has (by_value ?v1) (without ?v2 _)]] => wh'
end]).
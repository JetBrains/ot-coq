Require Import Commons.

Section Lists.

Context {X : eqType}.

Definition weak_cons (x : X) := bind (fun (xs : list X) => Some (x :: xs)).

Definition weak_app (xs : seq X) ys :=
match ys with
 | Some ys => Some (xs ++ ys)
 | None => None
end.

Notation "x :~: xs" := (weak_cons x xs) (at level 60, right associativity) : seq_scope.
Notation "x :++: xs" := (weak_app x xs) (at level 56, left associativity) : seq_scope.
Open Scope seq_scope.

Lemma cons_wcons (x : X) l : Some (x :: l) = x :~: Some l.
Proof. done. Qed.

Lemma wcons_none x o: x :~: o = None -> o = None. 
Proof. by move: o => []. Qed.

Lemma wcons_some x o o1: x :~: o = Some o1 -> exists o2, o = Some o2 /\ o1 = x :: o2.
Proof. by move: o => [a [<-]|] //; eauto. Qed.

Lemma weak_app_0s: forall xs, [::] :++: xs = xs.
Proof. by move=> [xs|]. Qed.

(* Insert list operation and its properties *)
Fixpoint ins (i : nat) (es : seq X) (xs : seq X) :=
 match i with
   0 => Some (es ++ xs)
   | S i' => 
     match xs with
       | x' :: xs' => x' :~: ins i' es xs'
       | _ => None
     end
 end.

Definition oins (i : nat) (es : seq X) :=
  bind (ins i es).

Lemma oins_some n es xs: ins n es xs = oins n es (Some xs).
Proof. done. Qed.
  
Lemma ins_notnil: forall xs (i : nat) y (ys : seq X), 
  ~ ins i (y :: ys) xs = Some (Nil _).
Proof. by move=> [|x xs] [|n] y ys //= /wcons_some; case => _ [] //. Qed.

Lemma ins_none' (es : seq X) k xs: ins (size xs + k.+1) es xs = None.
Proof. move: xs. by elim => [|x xs] //= ->. Qed.

Lemma ins_noneP k xs es: reflect (ins k es xs = None) (size xs < k).
elim: xs k => [|x xs IHx] [|k] /=; rewrite ?cats0; try by constructor.
case A0: (_ < k.+1); first by move: A0; rewrite ltnS => /IHx -> /=; constructor.
case A1: ins; first by constructor. move /IHx in A1.
by move: A0 A1; rewrite ltnS => ->. Qed.

(* Seems unnecessary, should we remove? *)
Lemma ins_some: forall xs es ys i, 
  ins i es xs = Some ys -> size ys = size xs + size es /\ size xs >= i.
Proof. split. elim: xs es ys i H => [|x xs IHxs] es ys. 
 + by case => [] //= [] <-; rewrite cats0 add0n.
 + case => [] /=.
   * by case => <-; rewrite size_cat /= addnC.
   * by move => n /wcons_some [] ? [] /IHxs A0 ->; rewrite /= A0. 
 move: H. move/orP: (leq_total i (size xs)) => [] //; rewrite leq_eqVlt => /orP [].
 + by move /eqP -> => //.
 + by case: (ins_noneP i xs es) => // ->. Qed.

Lemma ins_id xs ys i:
 ins i [::] xs = Some ys -> xs = ys.
Proof. 
by elim: i xs ys => [|i Hi] [|x xs] ys // [] //= /wcons_some [ys'] [] /Hi ->. Qed.

Lemma oins_Swcons (x : X) (es : seq X): forall xs i, 
  oins (i.+1) es (x :~: xs) = x :~: oins i es xs.
Proof. by case => [] [] //=. Qed.

(* Remove list opertaion and its properties*)

Fixpoint rm
 i (es : seq X) (xs : seq X) :=
 match xs, es with
 | _, [::] => Some xs
 | [::], _ => None
 | x' :: xs', e' :: es' =>
   match i with
     | 0 => if x' == e' then rm 0 es' xs' else None
     | i'.+1 => x' :~: (rm i' es xs')
   end
 end.

Definition orm (index : nat) (elements : seq X) :=
 bind (rm index elements).

Lemma orm_some n es xs: rm n es xs = orm n es (Some xs).
Proof. done. Qed.

Lemma rm_id k xs: rm k [::] xs = Some xs.
Proof. by case: xs => [|x xs] /=. Qed.

Lemma rm_len i es xs rs:  
  size es > 0 -> rm i es xs = Some rs -> exists k, size xs = i + (size es) + k /\ size rs = i + k.
Proof. elim: i es xs rs => [|i IHi] es xs rs H.
move {H}. elim: es xs rs => [|e es IHes] xs rs //=. 
 + rewrite rm_id => [] [] ->. by exists (size rs). 
 + case: xs => [|??] //=. case: eqP => // _ /IHes [k'] [].
   rewrite ?add0n => -> ->. by exists k'. 
 + move: es H => [|??] //. 
   case: xs => [|??] // /IHi => A /= /wcons_some [?] [] /A [k'] [] -> B -> /=. 
   rewrite B ?addnS ?addSn. by exists k'. 
Qed.

Corollary orm_id k xs : orm k [::] xs = xs.
Proof. by case : xs => [xs|] /=; rewrite ?rm_id. Qed.

Lemma orm_0wcons x es xs: 
  orm 0 (x :: es) (x :~: xs) = orm 0 es xs.
Proof. by case: xs => //= => xs; rewrite eq_refl; case: xs => //=. Qed.

Lemma rm_0app: forall xs1 xs2 es,
  rm 0 (xs1 ++ es) (xs1 ++ xs2) = rm 0 es xs2.
Proof. by elim => [|x1 xs1 IHxs1] xs2 es //=; rewrite eq_refl IHxs1. Qed.

Lemma rm_Scons xs x k es:
  rm k.+1 es (x :: xs) = x :~: (rm k es xs).
Proof. case: es xs => [] //= [] //=. Qed.

Lemma orm_Swcons xs x k es: 
  orm (k .+1) es (x :~: xs) = x :~: (orm k es xs).
Proof. elim: es xs => [|e es IHs] [[]|] //=.  Qed.

Lemma rm_addnapp xs ys k es:
  rm (k + size(ys)) es (ys ++ xs) = ys :++: (rm k es xs).
Proof. elim: ys xs es => [|y ys IHys] xs es //=.
  + by rewrite addn0 weak_app_0s.
  + move: es => [|e es] //=; first by rewrite ?rm_id.
    by rewrite addnS IHys; case: rm => [mr|]. Qed.

Lemma rm_none0 k xs e es: size xs <= k -> rm k (e :: es) xs = None.
Proof. by elim: xs k => [k //=|x xs IHl [|k] //= /IHl ->]. Qed.

Lemma rm_none1 {k xs es}: size es > 0 -> size xs < (size es) + k -> rm k es xs = None.
Proof. elim: xs k es => [|x xs IHxs] [|k] [|e es] // Heq /=; case: (x == e) => //;
rewrite ?addn0 ?addnS; try move=> /(IHxs _ _ Heq) -> // /(ltn_trans _ (ltnSn _)).
case Hes: (size es == 0); first by move/eqP: Hes ->. move /neq0_lt0n in Hes.
by rewrite -(addn0 (size es)) => /(IHxs _ _ Hes). Qed.

Lemma rm_eq (l1 l2 l3 : seq X): rm 0 l2 l1 = Some l3 -> l2 ++ l3 = l1.
elim: l2 l1 => [|a2 l2 IHl] [|a1 l1] //=; try by case => <-.
 + case A0: (a1 == a2) => // /IHl. by move: A0 => /eqP -> ->. Qed.

(* nth element operation and its properties *)
Fixpoint nth index xs : option X :=
 match xs, index with
   nil, _ => None
   | x :: xs, 0 => Some x
   | x :: xs, S i => nth i xs
 end.

Lemma nth_noneP i xs: reflect (nth i xs = None) (size xs <= i).
elim: xs i => [|x xs IHx] [|i] /=; try by constructor. apply IHx. Qed.

Lemma nth_nil_none (i : nat) (xs : seq X): nth i [::] = None.
Proof. move: (leq0n i). by rewrite -[0]/(size (@nil X)) => /nth_noneP. Qed.

Lemma nth_app_next xs1 xs2 k: nth (size xs1 + k) (xs1 ++ xs2) = nth k xs2.
Proof. elim: xs1 k xs2 => [|x1 xs1 IHxs1] k xs2 //=. Qed.

(* replace operation for lists and its properties *)

Fixpoint rplc (n : nat) (e : option X) (xs : seq X) :=
match n, xs with
 | 0, x :: xs' => bind (fun e' => Some (e' :: xs')) e
 | S n', x :: xs' => x :~: rplc n' e xs'
 | _, _ => None
end.

Definition orplc (index : nat) (e : option X) := bind (rplc index e).

Lemma orplc_some n e xs: rplc n e xs = orplc n e (Some xs).
Proof. done. Qed.

Lemma orplc_ind (x : X) l e i: orplc (S i) e (x :~: l)  = x :~: (orplc i e l). 
Proof. by case l. Qed.

Lemma rplc_0 xs i (e : option X): rplc i e xs = Some [::] -> False.
Proof. by move: xs i e => [|??] [|?] [?|] //=; case: rplc. Qed.
 
Lemma rplc_0none i e: rplc i e [::] = None.
Proof. by case: i e => [|i] [e|]. Qed.

Lemma rplc_noneP1 (e : X) {k} {xs}: reflect (rplc k (Some e) xs = None) (size xs <= k).
elim: xs k => [|x xs IHx] [|k] /=; try by constructor. rewrite ltnS.
by case: (rplc k (Some e) xs) (IHx k) => [a|]; case leq => [] [] //; constructor. Qed.

Lemma rplc_none_none k xs: rplc k None xs = None.
Proof. by elim: xs k => [|x xs Hxs] [|k] //=; rewrite Hxs. Qed.

Lemma rplc_lenle k xs (e : option X): size xs <= k -> rplc k e xs = None.
case: e => [a /(rplc_noneP1 a) //|] ?. by rewrite rplc_none_none. Qed.

Lemma rplc_none_case k xs (e : option X): rplc k e xs = None <-> e = None \/ size xs <= k.
Proof. case: e => [a|]; rewrite ?rplc_none_none; split;
 try move=> []; try move /rplc_noneP1; try done; by [right| left]. Qed.

Lemma rplc_some k xs (e : option X) y: rplc k e xs = Some y 
-> k < size xs /\ (exists e',  e = Some e').
Proof. case: e => [e'|]; last by rewrite rplc_none_none. 
case Hsz: (k < size xs); last by move: Hsz => /negbT; rewrite -leqNgt => 
/(rplc_lenle _ _ (Some e')) ->. by split => //; exists e'. Qed.
 
Lemma rplc_Scons xs i (x : X) y: rplc (i.+1) y (x :: xs) = x :~: (rplc i y xs).
Proof. done. Qed.

Lemma orplc_0wcons xs (x : X) y: orplc 0 (Some y) (x :~: xs) = y :~: xs.
Proof. by case: xs. Qed.

Lemma rplc_addn_app xs1 xs2 k e:
  rplc (size xs1 + k) e (xs1 ++ xs2) = xs1 :++: rplc k e xs2.
Proof. case: e => [e|]; last by rewrite ?rplc_none_none.
 by elim: xs1 => [|x1 xs1 IHxs1]; rewrite ?cat0s ?add0n //= ?IHxs1 //=; case: rplc. Qed.

Lemma orplc_Swcons xs i (x : X) y: orplc (i.+1) y (x :~: xs) = x :~: (orplc i y xs).
Proof. case: xs; done. Qed.

Lemma rplc_some_len (xs ys : seq X) i e: rplc i e xs = Some ys -> size xs = size ys.
Proof. case: e => [e|]; rewrite ?rplc_none_none //; 
 elim: i xs ys => [|i IHi] [|x xs] //= ys; first by move=> //= [] <-. 
 by move /wcons_some => [xs'] [] /IHi -> ->. Qed.

Lemma orplc_none i l: orplc i None l = None.
elim: i l => [|n IHn] [[|a l]|] //=. by move: (IHn (Some l)) => /= ->. Qed.
 
(* replace and nth propertice *)
Lemma rplc_nth_id (xs ys: seq X) i: rplc i (nth i xs) xs = Some ys -> xs = ys.
Proof. elim: i xs ys => [|i Hi] [|x xs] ys //= []; first by move ->.
  by move /wcons_some => [xs'] [] /Hi -> ->. Qed.

Lemma rplc_nth_id' i xs y: nth i xs = Some y -> rplc i (nth i xs) xs = Some xs.
Proof. by elim: i y xs => [|i IHi] y [|x xs] //= /IHi ->. Qed.

(* cut operation and its properties *)
Fixpoint cut {X} (l : seq.seq X ) sc rc :=
match sc, rc, l with
 | S sc', _, x :: xs => x :: (cut xs sc' rc) 
 | 0, S rc', x :: xs => (cut xs sc rc')
 | _, _, _ => l
end. 

Lemma cut_id {xs : seq X} {n}: cut xs n 0 = xs.
Proof. by elim: xs n => [|x xs IHxs] [|n] //=; rewrite IHxs. Qed.

Lemma cut_empty_eq {Y : Type}: forall n k, cut (@nil Y) n k = @nil Y. 
Proof. by move=> [|n] [|k]. Qed.

Lemma cut_nil {Y : Type}: forall xs, cut xs 0 (size xs) = @nil Y.
Proof. by elim. Qed.

(* insert/insert commutation *)
Lemma ins_insC': forall xs i k (e1s e2s : seq X), (i + k) <= size xs ->
oins (size e1s + (i + k)) e2s (ins i e1s xs) = oins i e1s (ins (i + k) e2s xs)
/\ exists os, oins i e1s (ins (i + k) e2s xs) = Some os.
Proof. move=> xs i. elim: i xs => [|i IHi] xs k e1s e2s. rewrite add0n /=.
 + elim: e1s => [|e1 e1s IHx] Hsz /=. rewrite add0n. 
   case Hins: (ins k) => [a|] /=; split => //; first by exists a.
   by move: Hins Hsz => /ins_noneP; rewrite ltnNge; case leq. 
 + move: (Hsz) => /IHx => [] [] IHx' IHx''.
   case Hins: (ins k) => [a|] /=; split => //; try by rewrite IHx' Hins /=. 
   by exists (e1 :: e1s ++ a). 
   by move: Hins Hsz => /ins_noneP; rewrite ltnNge; case leq.
 + case: xs => [|x xs] //=. rewrite addSn addnS => /IHi /= A. 
   move: (A e1s e2s) => []. rewrite ?oins_Swcons => -> [os] ->.
   split => //=. by exists (x :: os).
Qed.

Theorem ins_insC: forall xs i k (e1s e2s : seq X), i <= k -> k <= size xs ->
oins (size e1s + k) e2s (ins i e1s xs) = oins i e1s (ins k e2s xs)
/\ exists os, oins i e1s (ins k e2s xs) = Some os.
Proof. move=> xs i k e1s e2s /le_ex [j] <-. exact: ins_insC'. Qed.

(* remove/remove commutation *)
Lemma rm_rmC': forall xs i k (e1s e2s : seq X) rrm1 rrm2,
rm ((size e2s) + i + k) e1s xs = Some rrm1 ->
rm i e2s xs = Some rrm2 ->
orm i e2s (rm ((size e2s) + i + k) e1s xs) = orm (i + k) e1s (rm i e2s xs)
/\ exists os, orm (i + k) e1s (rm i e2s xs) = Some os.
Proof. move=> xs i. elim: i xs => [|i IHi] xs k e1s e2s rrm1 rrm2. 
 + rewrite add0n /=. elim: e2s xs e1s rrm1 rrm2 => [|e2 e2s IHe2s] [|x?] [|??] rrm1 rrm2; try by eauto.
   rewrite /= ?add0n. case: k => [|k]; rewrite orm_id => ->; by eauto.
   rewrite /= orm_id => _ ->; by eauto.
   simpl. case H: (x == e2) =>// /wcons_some [rrm1'] [] /IHe2s A _ /A [].
   move/eqP: H => ->. rewrite orm_0wcons => ->. by eauto.
 + rewrite addnS ?addSn //=. 
   move: xs e1s => [|x xs] [|e1 e1s] //=; rewrite ?orm_id //=;
   try (move=> _ ->; by eauto).
   move=> /wcons_some [rrm1'] [] /IHi A _.
   case: e2s A => [|e2 e2s] A; [move: (rm_id i xs)| move=> /wcons_some [rrm2'] []]; 
   move=> /A; rewrite ?orm_id ?rm_id ?cons_wcons ?orm_Swcons => [] []-> [os] -> /=; by eauto.
Qed.  

Theorem rm_rmC: forall xs i k (e1s e2s : seq X) rrm1 rrm2, 
i <= k ->
rm ((size e2s) + k) e1s xs = Some rrm1 ->
rm i e2s xs = Some rrm2 ->
orm i e2s (rm ((size e2s) + k) e1s xs) = orm k e1s (rm i e2s xs)
/\ exists os, orm k e1s (rm i e2s xs) = Some os.
Proof. move=> xs i k e1s e2s rrm1 rrm2 /le_ex [j] <-. rewrite addnA. 
move=> /rm_rmC' A /A []. by eauto.
Qed.

(* remove/insert commutation *)
Lemma rm_insC_bef': forall xs i k eis ers rins rrm, 
oins ((size ers) + i + k) eis xs = Some rins ->
orm i ers xs = Some rrm ->
orm i ers (oins ((size ers) + i + k) eis xs) = oins (i+k) eis (orm i ers xs)
/\ exists os, oins (i+k) eis (orm i ers xs) = Some os.
Proof. case => [] // xs i. elim: i xs => [|i IHi] xs k eis ers. rewrite addn0 add0n /=.
 + elim: ers xs eis => [xs eis|er ers IHers [|x?] eis//=] rins rrm => /=.
   rewrite add0n orm_id rm_id; split => //. by exists rins; rewrite /= H.
   case H: (x == er). 
  - move/eqP: H; move=> -> //= /wcons_some [rins'] [] /IHers A _ /A [].
    by rewrite orm_0wcons => ->. 
  - by case: ins => [res|]. 
 + move=> rins rrm; rewrite addnS addSn //=.
   move: xs => [|x xs] //=. move: ers => [|er ers]. 
  - rewrite orm_id /= => ->. split => //. by exists  rins.
   rewrite addSn orm_Swcons oins_Swcons oins_some => /wcons_some [rins'] [] /IHi A _
   /wcons_some [rrm'] []. rewrite orm_some => /A [] -> [os] -> /=; split => //. by exists (x :: os). Qed.   

Theorem rm_insC_bef xs i k eis ers rins rrm:
i <= k -> 
oins ((size ers) + k) eis xs = Some rins ->
orm i ers xs = Some rrm ->
orm i ers (oins ((size ers) + k) eis xs) = oins k eis (orm i ers xs)
/\ exists os, oins k eis (orm i ers xs) = Some os.
Proof. move=> /le_ex [?] <-. by rewrite addnA => /rm_insC_bef' A /A. Qed.

Lemma rm_insC_aft': forall i xs k eis ers rins rrm, 
ins i eis xs = Some rins -> rm (i + k) ers xs = Some rrm ->
 orm ((size eis) + (i + k)) ers (ins i eis xs) = oins i eis (rm (i + k) ers xs)
  /\ exists os, oins i eis (rm (i + k) ers xs) = Some os.
Proof.
by elim => [|i IHi] xs k eis ers rins rrm //=;
 [rewrite add0n /= {1}addnC rm_addnapp; case: rm => [mr|]| 
  move: xs ers => [|??] [|??] //=;  
  [case H: ins => [?|] //|
   rewrite ?addSn addnS orm_Swcons oins_Swcons => 
   /wcons_some [?] [] /IHi A ? /wcons_some [?] [] /A [] <- [?] ->]];
   split => //=; eauto. Qed.

Lemma rm_insC_aft xs i k eis ers rins rrm:
i <= k -> ins i eis xs = Some rins -> rm k ers xs = Some rrm ->
 orm ((size eis) + k) ers (ins i eis xs) = oins i eis (rm k ers xs)
  /\ exists os, oins i eis (rm k ers xs) = Some os.
Proof. by move=> /le_ex [?] <- /rm_insC_aft' A /A [] ->. Qed.

Lemma rm_insC_in': forall i k xs eis ers ers' xs', 
ins k eis ers = Some ers' -> ins (i+k) eis xs = Some xs' ->
  rm i ers xs = rm i ers' xs'.
Proof. elim => [|i Hi].
 +  elim => [|k Hk] [|x?] eis [|er?] ?? //=;
  try (by move=> [] <- [] <-; rewrite rm_0app).
  * move => /wcons_some [?] [] => H1 -> /wcons_some [?] [] => H2 -> /=.
    case: (x == er) H1 H2 => //. by apply /Hk.
 + by move => ? [|??] ? [|??] ? ? //= H1 /wcons_some [?] [H2 ->];
   rewrite rm_Scons -(Hi _ _ _ _ _ _ H1 H2) // ?rm_id. Qed.

Theorem rm_insC_in i k xs eis ers ers' xs': 
i <= k -> ins (k - i) eis ers = Some ers' -> 
 ins k eis xs = Some xs' -> 
  rm i ers xs = rm i ers' xs'.
Proof. move=> /le_ex [s] <-; 
rewrite addnC -addnBA // subnn addn0 addnC => *.
by apply (rm_insC_in' _ s _ eis). Qed.
 
(* replace/replace commutation *)
Lemma rplc_rplcC_neq': forall l i k t1 t2,
orplc (S (i + k)) t2 (orplc i t1 l) = orplc i t1 (orplc ((S i + k)) t2 l).
Proof. case => //. elim => [|x xs IHx]; intros. by rewrite /orplc /= rplc_0none.
case: t1 t2 => [t1|] [t2|]; try by rewrite ?orplc_none.
case: i => [/=|i]; first by case: rplc => [].
by rewrite ?addSn ?orplc_ind IHx. Qed.

Theorem rplc_rplcC_neq: forall l i k t1 t2, i == k = false ->
orplc k t2 (orplc i t1 l) = orplc i t1 (orplc k t2 l).
Proof. intros. case Hik: (i < k).
 + by move: Hik => /le_ex [j] <-; rewrite addSn rplc_rplcC_neq'.
 + case Hik': (k < i).
  - by move: Hik' => /le_ex [j] <-; rewrite addSn rplc_rplcC_neq'.
  - by move: Hik => /negbT; rewrite -leqNgt; move: Hik' => /negbT; rewrite -leqNgt => A B;
    have H': (i <= k <= i); rewrite ?B ?A //; move: H'; rewrite -eqn_leq H.
Qed.

Lemma rplc_rplcC_eq: forall xs i e1 e2,
orplc i e2 (orplc i (Some e1) xs) = orplc i e2 xs.
Proof. case=> [xs|] // i; elim: i xs => [|i IHi] xs e1 e2; first by case: xs.
 by case: xs IHi => [|x xs] IHi //=; rewrite orplc_Swcons IHi.
Qed.

(* replace/insert commutation *)

Lemma rplc_insC_aft': forall xs i k e1 e2s, i + k < size xs ->
orplc (size e2s + (i + k)) (Some e1) (ins i e2s xs) = oins i e2s (rplc (i + k) (Some e1) xs)
/\ exists os, oins i e2s (rplc (i + k) (Some e1) xs) = Some os.
Proof. move=> xs i. elim: i xs => [|i IHi] xs k e1 e2s.
 + rewrite add0n /= rplc_addn_app; case Hrplc: rplc => [rplc_r|] /=;
   first by (split => //; by exists (e2s ++ rplc_r)). move: Hrplc => /rplc_noneP1. by rewrite ltnNge; case leq.   
 + rewrite ?addSn ?addnS. case: xs => [|x xs] //=.
   rewrite ?orplc_Swcons oins_Swcons => /IHi A. move: (A e1 e2s) => [] <- [os] ->.
   split=> //. by exists (x :: os).
Qed.

Theorem rplc_insC_aft: forall xs i k e1 e2s, i <= k -> k < size xs ->
orplc (size e2s + k) (Some e1) (ins i e2s xs) = oins i e2s (rplc k (Some e1) xs)
/\ exists os, oins i e2s (rplc k (Some e1) xs) = Some os. 
Proof. move=> ??? e1 e2s /le_ex [?] <- /rplc_insC_aft' A. move: (A e1 e2s) => [] -> [os] ->. 
 split=> //. by eauto.
Qed.

Lemma rplc_insC_bef': forall xs i k e1 e2s, i + (S k) <= size xs ->
orplc i (Some e1) (ins (S (i + k)) e2s xs) = oins (S (i + k)) e2s  (rplc i (Some e1) xs)
/\ exists os, orplc i (Some e1) (ins (S (i + k)) e2s xs) = Some os.
Proof. move=>  xs i. elim: i xs => [|i IHi].
 + case=> [|x xs] k e1 e2s; rewrite add0n ?rplc_none_none //=; case Hins: ins => [ins_r|] //=. 
  - split => //. by exists (e1 :: ins_r). 
  - by move: Hins => /ins_noneP; rewrite ltnNge add0n -ltnS; case (_ <= _).
 + case=> [|x xs] k e1 e2s //. rewrite addSn /= => /IHi A. move: (A e1 e2s) => [] /=.
   rewrite orplc_Swcons oins_Swcons => -> [os] ->. split => //. by exists (x :: os).
Qed.

Theorem rplc_insC_bef: forall xs i k e1 e2s, i < k -> k <= size xs ->
orplc i (Some e1) (ins k e2s xs) = oins k e2s  (rplc i (Some e1) xs)
/\ exists os, orplc i (Some e1) (ins k e2s xs) = Some os.
Proof. move=> ??? e1 e2s /le_ex [?] <-.  rewrite ?addSn -?addnS => /rplc_insC_bef' A. 
move: (A e1 e2s) => []. rewrite addnS=> -> [os] ->. split=> //. by exists os.  Qed.

Lemma rplc_insC_in: forall xs i k e1 e2s e2s',
rplc k (Some e1) e2s = Some e2s' -> orplc (i + k) (Some e1) (ins i e2s xs) = ins i e2s' xs.
Proof. intros. elim: i xs k e1 e2s e2s' H => [|i IHi].
 + move=> xs k e1 e2s e2s'; rewrite add0n //=.
   elim: k xs e1 e2s e2s' => [|k IHk] xs e1 e2s e2s'; case: e2s => [|e2 e2s] //; rewrite cat_cons //=.
  * by move=> [] [] <-; rewrite cat_cons.
  * by move=> /wcons_some [e2s''] [] /(IHk xs) -> ->.
 + by move=> [|x xs] k e1 e2s e2s' //=; rewrite addSn orplc_Swcons => /(IHi xs) ->.
Qed.

(* replace/remove commutation *)

Lemma rplc_rmC_aft' xs i k e1 e2s rrm: 
 rm i e2s xs = Some rrm -> (size e2s + i + k) < size xs ->
  orplc (i+k) (Some e1) (rm i e2s xs) = 
  orm i e2s (rplc (size e2s + i + k) (Some e1) xs)
   /\ exists os, orplc (i+k) (Some e1) (rm i e2s xs) = Some os.
Proof. elim: i xs k e1 e2s rrm => [|i IHi] xs k e1 e2s rrm. 
 + rewrite ?addn0 add0n. elim: e2s k xs e1 => [[|k]|e2 e2s IHe2s k] [|x xs] e1; 
   rewrite ?addn0 ?orm_id ?rm_id /=; try by eauto.
  - move=> _. rewrite add0n. case Hrplc: rplc => [a|] /=. by eauto.
    move: Hrplc => /rplc_noneP1. by rewrite ltnNge ltnS => ->.
   case Heq: (x == e2) => //. move/eqP: Heq <-. rewrite orm_0wcons addSn => H1. 
   move: H1. eapply IHe2s => /(_ e1) /= [] -> [os] ->.
 + rewrite ?addSn ?addnS; move: xs IHi => [|x xs IHi]; first by case: e2s.
   rewrite rm_Scons orplc_Swcons => /wcons_some [rrm'] [].
   move => _1 _2. move: _2 _1 => _. move => _1 _2. move: _2 _1.
   rewrite addSn rplc_Scons orm_Swcons => /=. move => _1 _2. move: _2 _1.
   maxapply IHi => /(_ e1) [] -> [os] -> /=. by eauto.
Qed.

Theorem rplc_rmC_aft xs i k e1 e2s rrm: i <= k ->
 rm i e2s xs = Some rrm -> size e2s + k < size xs ->
   orplc k (Some e1) (rm i e2s xs) = 
   orm i e2s (rplc (size e2s + k) (Some e1) xs)
    /\ exists os, orplc k (Some e1) (rm i e2s xs) = Some os.
Proof. move => /le_ex [?] <-. rewrite ?addnA. 
apply rplc_rmC_aft' => /(_ e1) [] -> [os] -> /=. Qed.

Lemma rplc_rmC_bef': forall i xs k e1 e2s rrm,
 rm (S (i+k)) e2s xs = Some rrm -> i < size xs ->
  orplc i (Some e1) (rm (S (i+k)) e2s xs) = 
  orm (S (i+k)) e2s (rplc i (Some e1) xs) 
   /\ exists os, orplc i (Some e1) (rm (S (i+k)) e2s xs) = Some os.
Proof. elim => [|i IHi] xs k e1 e2s rrm. 
 + rewrite add0n; elim: e2s xs k e1 => [|er e2s IHe2s] xs k e1 /=.
  * rewrite rm_id => _ /=. case: xs => [|x xs] //= _ . by eauto.
  * case: xs => [|x xs] //=; rewrite orplc_0wcons => /wcons_some [rrm'] [] -> /=. by eauto.
 + rewrite ?addSn ?addnS. case: xs => [|x xs] //=. 
   case: e2s => [|e2 e2s] /=.
  - move=> _. case Hrplc: rplc => [rplc_r|] /=; first by eauto.
     by move: Hrplc => /rplc_noneP1; rewrite ltnNge ltnS => ->.
  - move => /wcons_some [rrm'] []. move => _1 _2. move: _2 _1 => _.
    rewrite orplc_Swcons ?orm_Swcons. maxapply IHi => /(_ e1) [] -> [os] -> /=. by eauto. Qed.

Theorem rplc_rmC_bef xs i k e1 e2s rrm:
 i < k -> rm k e2s xs = Some rrm -> i < size xs ->
  orplc i (Some e1) (orm k e2s (Some xs)) = 
  orm k e2s (rplc i (Some e1) xs)
   /\ exists os, orplc i (Some e1) (rm k e2s xs) = Some os.
Proof. move=> /le_ex [?] <-; rewrite ?addSn.
by apply rplc_rmC_bef' => /(_ e1) [] -> ? ->. Qed.

Theorem rplc_rmC_in {xs i k y}: forall ys ers' ers, 
 rplc i y ers = Some ers' -> orm k ers xs = Some ys ->
  orm k ers' (orplc (i + k) y xs) = Some ys.
Proof. case: xs i k y => [xs|*//]; intros. case: y H => [y|] //=; last by rewrite rplc_none_none. 
  elim: k xs i y ys ers ers' H0 => [|k IHk].
 + move=> xs i; elim: i xs => [|i IHi] xs y ys [|er ers] ers' //=; case: xs => [|x xs] //=;
   case Heq: (x == er) => // ?; first by move=> [] <-; rewrite eq_refl.
   by move=> /wcons_some [ers''] [] ? ->; move/eqP: Heq ->;
   rewrite orm_0wcons (IHi xs y ys ers ers'').
 + by move=> [|x xs] i y ys [|er ers] ers'; rewrite ?addnS ?rplc_0none //= orm_Swcons => 
   /wcons_some [ys' []] ? -> ?; rewrite (IHk _ _ _ ys' (er::ers)). Qed.

(* relating other operations to nth *)
Lemma ins_some_nth_aft {n ys}: forall xs es n2, n < n2 -> ins n2 es xs = Some ys
-> nth n ys = nth n xs.
Proof. elim: n ys => [|n IHn] ys [|x xs] [|e es] [|n2] //= Hltn /wcons_some [ys'] [] Hys' -> //=;
  by rewrite (IHn _ xs _ n2 _ Hys')//. Qed.

Lemma rm_some_nth_aft: forall n xs ys es n2, n < n2 -> rm n2 es xs = Some ys
-> nth n ys = nth n xs.
Proof. elim => [|n IHn] [|x xs] ys [|e es] [|n2] //= Hltn; try move=> [] <- //=; 
 move=> /wcons_some [ys'] [] Hys' -> //; rewrite (IHn xs _ _ n2 _ Hys') //. 
Qed.

Lemma rm_some_nth_bef: forall n xs ys es n2, n <= n2 -> rm n es xs = Some ys
-> nth n2 ys = nth (n2 + size es) xs.
Proof. elim => [|n IHn] xs ys es n2.
+ move=> H; elim: xs es => [|x xs IHxs] [[] <- //|e es] //=; try by rewrite addn0. 
  by case Heq: (x == e) => // /IHxs ->; rewrite addnS.
+ case: es => [|e es]; first by rewrite rm_id addn0 => _ [] ->.
  by case: xs => [|x xs] //= Hleq /wcons_some [ys'] [] ? ->; case: n2 Hleq => [|n2] // /= ?;
  rewrite (IHn xs _ (e::es)) //. Qed.

Lemma rm_some_nth_in {k i xs}: forall ys es, i < size es -> rm k es xs = Some ys -> 
nth (i + k) xs = nth i es.
Proof. by elim: k i xs => [|k IHk i]; [elim => [|i IHi] /=|]; move => [|x xs] ys [|e es] //=;
 [| |(rewrite addnS ?nth_nil_none //= => ? /wcons_some [ys'] [] ?; rewrite (IHk _ _ ys' (e::es)))];
 case Heq: (x == e) => //; [move /eqP: Heq => <- | move => ??; rewrite (IHi _ ys es)]. Qed.

Lemma ins_some_nth_bef {n xs}: forall ys es n2, n2 <= n -> ins n2 es xs = Some ys
-> nth n xs = nth (size es + n) ys.
Proof. elim: n xs => [|n IHn] xs ys es n2. 
 + by rewrite leqn0 => /eqP -> /= [] <-; rewrite nth_app_next. 
 + case: n2 => [_|n2] /=. by move=> [] <-; rewrite nth_app_next.
   by case: xs => [|x xs] // ? /wcons_some [ls'] [] ?;
      rewrite addnS (IHn _ ls' es n2) //= => ->.
Qed.

Lemma ins_some_nth_in {i k es ys xs} : k < size es -> ins i es xs = Some ys -> nth (i + k) ys = nth k es.
Proof. elim: i xs ys => [|i IHi] xs ys.
 + move=> H /= [] <-; rewrite add0n. elim: k es H => [|k IHk] [|e es] //=.
   by move /IHk.
 + by case: xs => [|x xs] //= Hlt /wcons_some [zs] [] /(IHi xs zs Hlt) <- ->. 
Qed.

Lemma rplc_nth_eq n xs ys z: rplc n (Some z) xs = Some ys -> nth n ys = Some z.
Proof. elim: n xs ys => [|n IHn] [|x xs] [|y ys] //=. 
 - by move=> [] ->.
 - by case: rplc.
 - by case Hrplc: rplc => [ls|] //= []; move: Hrplc => /IHn /= <- _ ->. Qed.

Lemma rplc_nth_neq' n1 n2 xs ys z: n1 < n2 -> 
rplc n1 z xs = Some ys -> nth n2 xs = nth n2 ys.
Proof. case: z => [z|] //; last by rewrite rplc_none_none. 
elim: n1 xs ys n2 => [|n1 IHn1] [|x xs] ys n2 //=; case: n2 => [|n2] //= ?.
 + by move => [] <-.
 + by move => /wcons_some [ys'] [] ? ->; rewrite (IHn1 _ ys'). Qed.

Lemma rplc_nth_neq'' n1 n2 xs ys z: n1 < n2 -> 
rplc n2 z xs = Some ys -> nth n1 xs = nth n1 ys.
Proof. case: z => [z|] //; last by rewrite rplc_none_none. 
elim: n2 xs ys n1 => [|n2 IHn2] [|x xs] ys [|n1] //= ? /wcons_some [ys'[? ->]] //.
by apply (IHn2 _ ys'). Qed.

Theorem rplc_nth_neq n1 n2 xs ys z: n1 != n2 -> 
rplc n2 z xs = Some ys -> nth n1 xs = nth n1 ys.
Proof. rewrite neq_ltn => /orP []; [exact: rplc_nth_neq'' |exact: rplc_nth_neq']. Qed.

(* remove/cut properties *)

Lemma rm_cut : forall xs n1 n2 es1 es2 ys1 ys2, 
 orm n1 es1 xs = Some ys1 -> orm n2 es2 xs = Some ys2 -> n1 <= n2 -> n2 <= n1 + size es1 ->
 orm n1 (cut es2 0 (n1 + size es1 - n2)) (orm n1 es1 xs) = 
 orm n1 (cut es1 (n2 - n1) (size es2)) (orm n2 es2 xs) /\
 exists os, orm n1 (cut es1 (n2 - n1) (size es2)) (orm n2 es2 xs) = Some os.
Proof. move=> [xs|] n1 //; elim: n1 xs => [|n1 IHn1].
 + elim => [|x xs IHxs].
  - move=> n2 [|??] [|??] //= [|??] [|??] //= _ _ _. 
    rewrite leqn0 => /eqP ->. rewrite subnn. by eauto.
  - move=> n2 [|e1 es1] [|e2 es2] ys1 ys2 /= H1 H2 H3;
     try (rewrite leqn0 => /eqP Hn2; move: H2; rewrite Hn2 subnn ?orm_id; 
          case: (x == e2); by eauto).
   * case: n2 H2 H3 => [|n2] //. by eauto. 
     case: n2 H3 => [|n2] // _ _; rewrite add0n ?subn0; try case: subn => [|?];
     move: H1; case: (x == e1) => //; rewrite ?cut_id orm_id => ->; by eauto.
   * move: H1. case Heq: (x == e1) => // /IHxs A.
     move: H2. case: n2 H3 => [|n2] _.
    - case: (x == e2) => // /A B. move: (B (leq0n _) (leq0n _)) => /=.
      rewrite add0n ?subn0 => [] [] -> [os] ->; by eauto.
    - move => /wcons_some [ys2'] [] /A B _. rewrite add0n => /(B (leq0n _)) /= []. 
      rewrite subn0 => ->. move/eqP: Heq ->. rewrite orm_0wcons => [] [os] ->. by eauto.
 + move=> [|x xs] [|n2] es1 es2 ys1 ys2 //; rewrite ?cons_wcons ?orm_Swcons subSS.
  - move: es1 es2 => [|??] [|??] //=; case: subn; case: subn => //=; by eauto.
   move=> /wcons_some [ys1'] [] /IHn1 A _ /wcons_some [ys2'] [] /A B _ /B C.
   rewrite addSn. move => /C [] -> [os] -> /=. by eauto.
Qed.

(* inversion theorems *)
Lemma rm_ins_id : forall n xs es ys, 
ins n es xs = Some ys -> rm n es ys = Some xs.
Proof. elim => [|n IHn] xs es ys.
 + elim: es xs ys => [[|x xs]|e es IHes xs] ys //= [] <-; try (by rewrite rm_id).
   rewrite orm_some cons_wcons orm_0wcons /= (IHes xs) //.
 + case: xs => [|x xs] //. rewrite oins_some cons_wcons oins_Swcons => /wcons_some [ys'] [].
   move=> /IHn <- ->. by rewrite orm_some cons_wcons orm_Swcons.
Qed.

Lemma ins_rm_id : forall n xs es ys,
size es > 0 -> rm n es xs = Some ys -> ins n es ys = Some xs.
Proof. elim => [|n IHn] xs es ys.
 + move=> _. elim: es xs ys => [|e es IHes] [|x xs] ys //=; try (by rewrite rm_id => -> /=).
   case Heq: (x == e) => // /IHes [] <-. by move/eqP: Heq ->.
 + case: xs => [|x xs] //. case: es => //= [] [] <-. 
   move => _1 _2. move: _2 _1.
   rewrite orm_some cons_wcons orm_Swcons.
   move=> /wcons_some => [] [ys'] []. 
   move => _1 _2. move: _2 _1 => -> /=.
   maxapply IHn. by move=> /= ->.
Qed.

Section AboutSizes.

Theorem cutSZ (xs : seq X) i n:
size (cut xs i n) = 
 if (i + n <= size xs) then size xs - n
 else if (i <= size xs) then i
 else size xs.
Proof. elim: i xs n => [|i IHi] xs n /=.
 + elim: n xs => [|n IHn] [|x xs] //=. rewrite IHn. nat_norm.
   rewrite -addn1 -(addn1 (size xs)) leq_add2r. case Hleq: (n <= size xs) => //=.
   by rewrite ?addn1 subSS.
 + move: xs => [|x xs] //=. rewrite IHi. nat_norm. 
   rewrite -(addn1 (i + n)) -(addn1 (size xs)) leq_add2r. case Hleq: (i + n <= size xs). 
   move: (Hleq) => /leq_addWl. rewrite -addn1 addnC => /addnBA ->. by rewrite addnC.
   rewrite -(addn1 i) leq_add2r. case: (i <= size xs); ssromega.
Qed.

Theorem cut_lenleq (xs : seq X) i n:
size (cut xs i n) <= size xs.
Proof. move: (cutSZ xs i n). case: ifP => Hleq.
 - move: (leq_subr n (size xs)). by (move => _1 _2; move: _2 _1 => ->).
 - case: ifP => Hleq'; move=> /eq_leq =>//. 
   move: Hleq'. move => _1 _2; move: _2 _1. by apply leq_trans. Qed.

End AboutSizes.

Section Miscellanea.

Fixpoint find {Z : Type} p (xs : seq Z) : option Z :=
 match xs with
 | xh :: xt => if p xh then Some xh else find p xt
 | _ => None end.

Lemma foldl_map (T1 T2 S : Type) (f : S -> T2 -> S) (g : T1 -> T2) (x : seq T1) (r : S):
foldl f r (map g x) = foldl (fun x => (f x) \o g) r x. 
by elim: x r => [|x xs IH] //=. Qed.

Lemma filter_filter {p p' : X -> bool} {xs} : filter p (filter p' xs) = filter p' (filter p xs).
elim: xs => //= [xh xt IHxs]. case P1: (p xh); case P2: (p' xh);  rewrite /= ?P1 ?P2 IHxs //. Qed.

Lemma all_filter p q (cs :seq X): all p cs -> all p [seq x <- cs | q x].
by elim: cs => [|c cs IH] //= /andP [] A0 /IH A1; case A2: q => /=; rewrite ?A0 A1. Qed.

Lemma has_filter p q (xs : seq X): p --- q -> has q (filter p xs) = has q xs.
intros A1. elim: xs => [|x xs IH] //=. move: (A1 x). case A0: (p x).
 + by rewrite /= IH.
 + by move => -> //. Qed.

Lemma map_inj {X' : eqType} (f : X -> X') x s: injective f -> ((f x) \in (map f s)) = (x \in s).
move => B0. elim: s => [|c s IH] //=.
case A0: (x == c) => /=.
 + move: A0 => /eqP ->. by rewrite /in_mem /= ?eq_refl.
 + move: IH. rewrite /in_mem /=. case A1: eq_op.
  * move: A1 A0 => /eqP /B0 ->. by rewrite eq_refl.
  * by move: A0 => -> ->. Qed.

Lemma find_absent {A p xs}: find p xs = @None A <-> has p xs = false.
by elim: xs => // a l [IHa IHb] /=; case: (p a); split. Qed.

Lemma has_find {A p xs}: has p xs = true -> exists (x : A), find p xs = Some x.
case H: (find p xs) => [x|].
  + by exists x.
  + by move => G; apply find_absent in H; rewrite H in G. Qed.

Lemma find_pred {xs p} {x : X}: find p xs = Some x -> p x.
elim: xs => [|xh xt IHxs] //.
 + by rewrite /=; case H: (p xh) => // [] [] <-. Qed.

Lemma find_filter p q (xs : seq X): p --- q -> find q (filter p xs) = find q xs.
intros A1. elim: xs => [|x xs IH] //=. move: (A1 x). case A0: (p x).
 + by rewrite /= IH.
 + by move => -> //. Qed.

Lemma find_has {p xs} {x : X}: find p xs = Some x -> has p xs = true.
by elim: xs => [|xh xt IHxs]; rewrite //=; case P: (p xh) => //. Qed.

End Miscellanea.

(* Sequence difference *)

Definition seqminus (x y : seq X) := filter (fun z => z \notin y) x.

Section SeqMinus.

Notation "X \ Y" := (seqminus X Y) (at level 40, left associativity).

Lemma sum_setminus (f : X -> nat) (S1 S2 : seq X): 
  foldl addn 0 (map f (S1 \ S2)) <= foldl addn 0 (map f S1).
elim: S1 S2 => [|s cs IH] S2 //=. case A0: (in_mem) => /=; move: (IH S2); rewrite ?add0n ?(fadd (f s)).
 + move: (foldl _ _ _) => a. move: (foldl _ _ _) => b. rewrite -{2}(add0n (a)). by apply leq_add.
 + by apply leq_add. Qed. 

Lemma seqminus_nil (l : seq X): l \ [::] = l.
 elim: l => [|t l IH] //=. by rewrite IH. Qed.

Lemma seqminus_nil' (l : seq X): [::] \ l = [::].
 elim: l => [|t l IH] //=. Qed.

Lemma seqminus_cons (l l2 : seq X) x: x \notin l -> l \  (x :: l2) = l \ l2.
elim: l => [|y l IH] //=. rewrite /in_mem /= eq_sym. case A0: eq_op => //= A1. by rewrite IH. Qed.

Lemma seqminus_cons' (l l2 : seq X) x: x \notin l2 -> (x :: l) \ l2 = x :: (l \ l2).
by move => /= ->. Qed.

Corollary seqminus_singleton (l : seq X) x: x \notin l -> l \ [:: x] = l.
move: (seqminus_cons l [::] x). by rewrite /= seqminus_nil. Qed.

Import Bool.

Lemma notin_setminus (l : seq X) x: x \notin (l \ [::x]).
elim: l => [|z l IH] //=. case A0: (in_mem z) => //=. move: A0.
by rewrite /in_mem /= orb_false_r eq_sym => ->. Qed.

Corollary uniq_setminus (l l2 : seq X): uniq l -> uniq (l \ l2).
rewrite /seqminus. apply filter_uniq. Qed.

Lemma filter_and (l : seq X) p1 p2: filter p2 (filter p1 l) = filter (fun x => p1 x && p2 x) l.
elim: l => [|x l IH] //=. case A0: (p1 x) => //=.
 + case A1: (p2 x) => //=. by rewrite IH. Qed.

Lemma seqminus_cat (l l1 l2 : seq X): l \ l1 \ l2 = l \ (l1 ++ l2).
rewrite /seqminus. rewrite filter_and. apply eq_filter => x /=. by rewrite mem_cat /= negb_orb. Qed.

Lemma seqminus_p1 (l1 l2 : seq X) x: x \notin l2 -> l2 \ (l1 \ [:: x]) = l2 \ l1.
rewrite /seqminus => A0. apply eq_in_filter => z A1. rewrite mem_filter /= /in_mem /= orb_false_r.
case A2: eq_op => //=. by move: A2 A1 A0 => /eqP -> ->. Qed.

End SeqMinus.

End Lists.

Notation "X \ Y" := (seqminus X Y) (at level 40, left associativity).

Lemma map_seq_minus {X X' : eqType} (s1 s2 : seq X) (f : X -> X'):
  injective f -> map f (s1 \ s2) = (map f s1) \ (map f s2).
move => B0. rewrite /seqminus. elim: s1 => [|x s1 IH] //=.
rewrite map_inj //. case A1: (x \notin s2) => /=; by rewrite IH. Qed.

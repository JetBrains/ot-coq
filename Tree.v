Require Import Commons.

(* Definition of Tree as ssreflect eqType *)
Section TreeDef.

Unset Elimination Schemes.
Inductive tree (T : Type) : Type := Node of T & seq (tree T).

Global Arguments Node [T].

Context {T : Type}.

Definition value    (t : tree T) := match t with | Node v _  => v  end.
Definition children (t : tree T) := match t with | Node _ cs => cs end.

Definition NodeW (t : T) (ls : option (seq (tree T))) := 
  match ls with Some l' => Some (Node t l') | _ => None end.

Lemma nodew_none x xs: NodeW x xs = None <-> xs = None.
Proof. split; by [case: xs => [xs|]|move=> ->]. Qed.

Lemma nodew_some x ls x2 ls2: 
NodeW x ls = Some (Node x2 ls2) <-> (x = x2 /\ ls = Some ls2).
Proof. by split; [case : ls => [ls|] //=|]; move=> [] -> ->. Qed.

Lemma nodew_someS x ls x2 ls2: 
Some (Node x2 ls2) = NodeW x ls <-> (x = x2 /\ ls = Some ls2).
Proof. by split; [case : ls => [ls|] //=|]; move=> [] -> ->. Qed.

Definition tree_rect
(K : tree T -> Type)
(IH_leaf : forall (x : T), K (Node x nil))
(IH_node : forall (x : T) (x0 : seq (tree T)), foldr (fun t : tree T => prod (K t)) unit x0 -> K (Node x x0))
: (forall s : tree T, K s) :=
fix loop t : K t := match t with
  Node x nil => IH_leaf x
  | Node x f0 =>
    let fix iter_pair f : foldr (fun t => prod (K t)) unit f :=
      if f is t :: f' then (loop t, iter_pair f') else tt in IH_node x f0 (iter_pair f0) end.

Definition tree_rec (K : tree T -> Set) := tree_rect K.

Definition tree_ind (K : tree T -> Prop) 
(IH_leaf : (forall (x : T), K (Node x nil)))
(IH_node : (forall (x : T) (x0 : seq (tree T)), foldr (fun t : tree T => and (K t)) True x0 -> K (Node x x0)))
: (forall (s : tree T), K s) :=
  fix loop t : K t : Prop := match t with
  | Node x nil => IH_leaf x
  | Node x f0 =>
    let fix iter_conj f : foldr (fun t => and (K t)) True f :=
        if f is t :: f' then conj (loop t) (iter_conj f') else Logic.I
      in IH_node x f0 (iter_conj f0)
    end.

Fixpoint encode (t : tree T) : seq (option T) :=
match t with Node x f => (Some x) :: rcons (flatten (map encode f)) (None) end.

Definition decode_step (c : option T) (fs : (seq (tree T)) * seq (seq (tree T))) := 
match c with
 Some x => (Node x fs.1 :: head [::] fs.2, behead fs.2)
 | _ => ([::], fs.1 :: fs.2)
end.

Definition decode c := ohead (foldr decode_step ([::], [::]) c).1.

Lemma codeK : pcancel encode decode.
Proof. move=> t; rewrite /decode; set fs := (_, _).
suffices ->: foldr decode_step fs (encode t) = (t :: fs.1, fs.2) by [].
elim: t => //= n f IHt in (fs) *; elim: f IHt => //= t f IHf [].
by rewrite rcons_cat foldr_cat => -> /= /IHf[-> -> ->]. Qed.

Section Weight.

Definition weight (t : tree T) : nat :=
 foldr addn 0 (map (fun o => match o with Some _ => 1 | _ => 0 end) (encode t)).

Definition weights (c : seq (tree T)) := foldr addn 0 (map weight c).

Lemma weight_Node c ch: weight (Node c ch) = weights ch + 1.
rewrite /weight /= map_rcons /weights -cats1 foldr_cat /= /weight.
elim: ch => [|a l] //=. rewrite map_cat foldr_cat /= addn0.
rewrite (faddr (foldr addn 0 _)) ?addn1 ?add1n /=.
remember (foldr addn 0 (map _ (encode a))) as h1.
by rewrite (addnC h1) -?addSn => ->. Qed.

Lemma weights_cons (a : tree T) l: weights (a :: l) = weight a + weights l. by rewrite /weights /=. Qed.
Lemma weights_app (l1 l2 : seq (tree T)): weights (l1 ++ l2) = weights l1 + weights l2.
 elim: l1 => [|a l1] //=; by rewrite ?weights_cons -addnA => ->. Qed.

Lemma weights_drop: forall n (l : seq (tree T)), weights (drop n l) <= weights l.
elim => [|n IHn] [|a l] //=. rewrite weights_cons. move: (IHn l).
rewrite -ltnS -(ltnS _ (addn _ _)) -addnS. by apply /ltn_addl. Qed.

Lemma weights_take: forall n (l : seq (tree T)), weights (take n l) <= weights l.
elim => [|n IHn] [|a l] //=. rewrite weights_cons. move: (IHn l).
by rewrite weights_cons leq_add2l. Qed.

Lemma weights_rot: forall n (l : seq (tree T)), weights (rot n l) = weights l.
elim => [|n IHn] [|a l] //=; try by rewrite rot0.
 move: (IHn l). rewrite /rot. 
 by rewrite drop_cons take_cons ?weights_app ?weights_cons
    addnA (addnC _ (weight _)) -?addnA => <-. Qed.

Corollary weights_rotr n (l : seq (tree T)): weights (rotr n l) = weights l.
by rewrite /rotr weights_rot. Qed.

End Weight.

End TreeDef.

Definition tree_eqMixin (T : eqType) := PcanEqMixin (@codeK T).
Canonical tree_eqType (T : eqType) := @EqType (tree T) (tree_eqMixin T).

Check @Node.

Lemma tree_eqP (T : eqType) (t1 t2 : T) l1 l2: Node t1 l1 == Node t2 l2 <-> (t1 = t2) /\ (l1 = l2).
split. by move /eqP => [] -> ->. by case => -> ->. Qed.

Lemma Node_eq (T : eqType) (x : T) lx y ly: ((Node x lx) == (Node y ly)) = (x == y) && (lx == ly).
case: (@eqP _ (Node x lx) (Node y ly)) => [[-> ->]| A0]. by rewrite ?eq_refl.
by case: andP A0 => // [] [] /eqP -> /eqP ->. Qed.

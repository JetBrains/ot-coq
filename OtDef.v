Require Import Commons Basics ListTools.

Section ExecAll.

Context {C : Type} {X : Type}.

Definition exec_all (f : C -> X -> option X) := foldl (flip (fun c => bind (f c))).

Lemma exec_all_none {cs : seq C} {f}: (exec_all f) (@None X) cs = None. by elim: cs. Qed.

Lemma exec_all_ind f t v vs: exec_all f t (v :: vs) = exec_all f (bind (f v) t) vs.
 by rewrite /=. Qed.

Lemma exec_all_rcons_ind f vs v t: 
      exec_all f t (rcons vs v) = bind (f v) (exec_all f t vs).
by rewrite /exec_all -cats1 foldl_cat /flip /=. Qed.

Lemma exec_all_cons f c cs t: exec_all f (Some t) (c :: cs) = exec_all f (f c t) (cs).
by rewrite /= /flip. Qed.

Lemma exec_all_cat f cs1 cs2 t: exec_all f (Some t) (cs1 ++ cs2) = 
                    exec_all f (exec_all f (Some t) cs1) cs2.
elim: cs1 t => [|c cs1 IH] t //. rewrite cat_cons ?exec_all_cons.
case: (f c t) => [a|]. by rewrite IH. by rewrite ?exec_all_none. Qed.

Lemma exec_all_eqfun {f1 f2}: f1 =1 f2 -> forall (c : seq C) (m : option X), 
 exec_all f1 m c = exec_all f2 m c.
 move => A0. elim => [|x c IH] m //=. rewrite /bind /flip. case: m => [a|] //. by rewrite A0 IH. Qed.

End ExecAll.

Corollary exec_all_compat {C1 C2 Z} {m : option Z} {l : seq C1} f1 (f2 : C1 -> C2): 
 exec_all f1 m [seq f2 i | i <- l] = exec_all (f1 \o f2) m l.
case: m => [m|]. rewrite /exec_all. by rewrite foldl_map /= /flip /comp. by rewrite ?exec_all_none. Qed.

Class OTBase (X cmd : Type) := {
 interp : cmd -> X -> option X;
 it     : cmd -> cmd -> bool -> list cmd;
 it_c1 : forall (op1 op2 : cmd) (f : bool) m (m1 m2 : X),
  interp op1 m = Some m1 -> interp op2 m = Some m2 -> 
  let m21 := (exec_all interp) (Some m2) (it op1 op2 f) in
   let m12 := (exec_all interp) (Some m1) (it op2 op1 (~~f)) in
    m21 = m12 /\ exists node, m21 = Some node}.

Fixpoint transform {cmd} (t : cmd -> cmd -> bool -> list cmd) (op1 op2 : list cmd) (nSteps : nat) : option ((list cmd) * (list cmd)) :=
match nSteps with 
| 0 => None 
| S nSteps' =>
  match op1, op2 with 
  | nil, _ | _, nil => Some (op2, op1)
  | x :: xs, y :: ys => 
    match transform t xs (t y x false) nSteps' with
    | Some (y'', xs') => 
      match transform t ((t x y true) ++ xs') ys nSteps' with
      | Some (ys', x'') => Some (y'' ++ ys', x'') 
      | _ => None end
    | _ => None end end end.

Class OTInv (X cmd : Type) (M : OTBase X cmd) := {
 inv    : cmd -> cmd;
 ip1 : forall op m mr, interp op m = Some mr -> interp (inv op) mr = (Some m)}.

Class OT_C2 (X cmd : Type) (M : OTBase X cmd) := {
 it_c2 : forall (op1 op2 op3 : cmd) (f1 f2 : bool), exists n,
  let it' := @transform cmd it in
  match it' (it op2 op3 true) (it op1 op3 true) n, it' (it op2 op1 false) (it op3 op1 false) n with
    Some (_, x), Some (_, y) => x = y
    | _, _ => False end}.

Definition computability {cmd : Type} (it : cmd -> cmd -> bool -> list cmd) 
(sz : seq cmd -> nat) (si : seq cmd -> nat) (op1 op2 : cmd) := forall srv, 
  let op1' := it op1 op2 (negb srv) in
  let op2' := it op2 op1 srv in
    (sz op1' + sz op2') <= sz [:: op1] + sz [:: op2] /\ 
    (si op1' + si op2' <= si [:: op1] + si [:: op2]) /\
    ((sz op1' <= sz [:: op1] /\ sz op2' <= sz [:: op2]) \/
    (si op1' + si op2' < si [:: op1] + si [:: op2])).

Class OTComp {X cmd} (M : OTBase X cmd) := {
  cmdsz : cmd -> nat;
  cmdsi : cmd -> nat;
  sz := foldl addn 0 \o map cmdsz;
  si := foldl addn 0 \o map cmdsi;
  sz_nondg : forall x , 0 < cmdsz x;
  comp_corr: forall (op1 op2 : cmd), computability it sz si op1 op2}.

Require Import ssreflect ssrnat ssrbool seq Ssromega OtDef Commons.

Lemma ltnSn n: n < S n. ssromega. Qed.
Lemma list_const: forall X X' (l : list X') (x : X), match l with nil => x | _ :: _ => x end = x.
Proof. intros. destruct l; reflexivity. Qed.

Lemma tstab {cmd} t: forall n k (op1 op2 op1' op2' : list cmd),
transform t op1 op2 n = Some (op2', op1') -> transform t op1 op2 (n + k) = Some (op2', op1').
Proof. elim => [|n IHn] k [|o1 op1] [|o2 op2] op1' op2' //=.
move A1: (transform t _ _ n) => [[x y]|] //; move A2: (transform t _ _ n) => [[x' y']|] // h.
by rewrite (IHn k _ _ _ _ A1) (IHn k _ _ _ _ A2) h. Qed.

(* =============================================== *)

Section OTCorrectness.

Context {X cmd : Type} (ot : OTBase X cmd) (comp : @OTComp X cmd ot).

Lemma sz_nil: sz nil = 0. by rewrite /sz. Qed.
Lemma si_nil: si nil = 0. by rewrite /si. Qed.

Lemma cats_sz (l1 l2 : list cmd): sz (l1 ++ l2) = sz l1 + sz l2.
elim: l1 l2 => [| l ls IHl] l2. by rewrite cat0s sz_nil add0n. rewrite /sz /= in IHl.
by rewrite cat_cons /sz /= ?add0n fadd (fadd (cmdsz l)) IHl addnA. Qed.

Lemma cats_si (l1 l2 : list cmd): si (l1 ++ l2) = si l1 + si l2.
elim: l1 l2 => [| l ls IHl] l2. by rewrite cat0s si_nil add0n. rewrite /si /= in IHl.
by rewrite cat_cons /si /= ?add0n fadd (fadd (cmdsi l)) IHl addnA. Qed.

Lemma execute_app: forall (op1 op2 : list cmd) (m : option X),
(exec_all interp) m (op1 ++ op2) = (exec_all interp) (exec_all interp m op1) op2.
elim => [| x xs IHx] op2 m //. rewrite cat_cons /= IHx //. Qed.

Lemma execute_none op: exec_all interp None op = None. 
by elim: op => [|x xs IHx] //=. Qed.

Lemma transform_ind: 
forall (op1 op2 : list cmd) n, transform it op1 op2 (S n) = 
  match op1, op2 with
    | nil, _ | _, nil => Some (op2, op1)
    | x :: xs, y :: ys => 
       match transform it xs (it y x false) n with
         Some (y'', xs') => 
          match transform it ((it x y true) ++ xs') ys n with
            Some (ys', x'') => Some (y'' ++ ys', x'') 
            | _ => None
          end
         | _ => None
       end
  end. done. Qed.

Theorem ot_computability': forall n m (op1 op2 : list cmd), 
(sz op1 + sz op2 < n) -> (si op1 + si op2 < m) ->
 (exists n, exists op1', exists op2', transform it op1 op2 n = Some (op2', op1') /\
 (sz op1' + sz op2' <= sz op1 + sz op2) /\ 
 (si op1' + si op2' <= si op1 + si op2) /\ 
   (((sz op1' <= sz op1) /\ (sz op2' <= sz op2)) \/
    (si op1' + si op2' < si op1 + si op2))).
 elim => [|n IHn].
 + move => m op1 op2 h. by have: False by ssromega.
 + elim => [|m IHm] // op1 op2.
  case: op1 => [*|x xs].
  + exists 1. exists (@nil cmd). exists op2. 
    rewrite ?sz_nil ?si_nil ?add0n /=. split. done.
    split. ssromega. split. ssromega. left. split; ssromega.
  + case: op2 => [*|y ys].
    + exists 1. exists (x :: xs). exists (@nil cmd).
    rewrite ?sz_nil ?si_nil ?add0n ?addn0 /=. split. done.
    split. ssromega. split. ssromega. left. split; ssromega.
      replace (x :: xs) with ([::x] ++ xs); [| by simpl].
      replace (y :: ys) with ([::y] ++ ys); [| by simpl].
    + rewrite ?cats_sz ?cats_si.
      move => h h'. assert (AA := comp_corr x y false). rewrite /computability /= in AA.
      rewrite /cat. assert (E0 := sz_nondg x). assert (E1 := sz_nondg y).
      assert (E0': sz [::x] > 0). by rewrite /sz.
      assert (E1': sz [::y] > 0). by rewrite /sz. clear E0 E1.
      move Heqy': (@it _ _ ot x y true) => x'.
      move Heqx': (@it _ _ ot y x false) => y'.
      rewrite Heqx' Heqy' in AA.
      move: AA => /= [B1[B2[[B0 B0']|B0 {B2}]]];
      [assert (A0: sz xs + sz y' < n) by ssromega;
       move: (IHn (S (si xs + si y')) xs y' A0 (ltnSn _)) |
       assert (A0: sz xs + sz y' < n.+1) by ssromega;
       assert (A0': si xs + si y' < m) by ssromega;
       move: (IHm xs y' A0 A0') ];
      move => [n'1 [xs' [y'' [C1 [C2 [C3 C4]]]]]] {A0};
      [move: C4 => [[C01 C02]|C0];
        [ assert (A0: sz (x' ++ xs') + sz ys < n) by (rewrite cats_sz; ssromega);
          move: (IHn (S (si (x' ++ xs') + si ys)) (x' ++ xs') ys A0 (ltnSn _)) => A1| 
          assert (A0: sz (x' ++ xs') + sz ys < S n) by (rewrite cats_sz; ssromega);
          assert (A0': si (x' ++ xs') + si ys < m) by (rewrite cats_si; ssromega);
          move: (IHm (x' ++ xs') ys A0 A0') => A1] |
        assert (A0: sz (x' ++ xs') + sz ys < S n) by (rewrite cats_sz; ssromega);
        clear A0'; assert (A0': si (x' ++ xs') + si ys < m) by (rewrite cats_si; ssromega);
        move: (IHm (x' ++ xs') ys A0 A0') => A1];
       rewrite cats_sz cats_si in A1;
       move: A1 => [n'2 [op1' [ys' [D1 [D2 [D3 D4]]]]]];
       apply (tstab _ _ n'2) in C1; apply (tstab _ _ n'1) in D1; rewrite addnC in D1;
       exists (S (n'1 + n'2));
       rewrite transform_ind Heqy' Heqx' C1 D1;
       exists op1'; exists (y'' ++ ys'); rewrite ?cats_sz ?cats_si;
       (split; [done|split;[ssromega|split;[ssromega|]]]).

       + move: D4 => [[D41 D42]| D4];[left; split |right]; ssromega.
       + right; ssromega.
       + right; ssromega. Qed.
 
Corollary ot_computability'' op1 op2: 
 (exists n, exists op1', exists op2', transform it op1 op2 n = Some (op2', op1') /\
 (sz op1' + sz op2' <= sz op1 + sz op2) /\ 
 (si op1' + si op2' <= si op1 + si op2) /\ 
   (((sz op1' <= sz op1) /\ (sz op2' <= sz op2)) \/
    (si op1' + si op2' < si op1 + si op2))).
by apply (ot_computability' (S (sz op1 + sz op2)) (S (si op1 + si op2)) op1 op2 (ltnSn _) (ltnSn _)). Qed.

Corollary ot_computable: forall (op1 op2 : list cmd), exists nSteps op1' op2', transform it op1 op2 nSteps = Some (op2', op1').
move => op1 op2. move: (ot_computability'' op1 op2). move => [n [op1' [op2' [A B]]]]. exists n. exists op1'. exists op2'. done. Qed.

Theorem ot_execution: forall nSteps op1 op2 op1' op2' m (m1 m2 : X), exec_all interp m op1 = Some m1 /\ exec_all interp m op2 = Some m2 ->
transform it op1 op2 nSteps = Some (op2', op1') ->
exec_all interp (Some m1) op2' = exec_all interp (Some m2) op1' /\ exists m3, exec_all interp (Some m1) op2' = Some m3.
elim => [|n IHn] op1 op2 op1' op2' m m1 m2 [h h'] H0 //. rewrite transform_ind in H0.
case: op1 H0 h => [[H0 H1] [h]| x xs H0 h].
  + rewrite -H0 -H1 -h /= h'. by eauto.
  + case: op2 H0 h' h => [[H0 H1] [h']| y ys].
    * rewrite -H0 -H1 -h' /=. eauto.
    * move A0: (it y x false) => y'. move A1: (transform it xs y' n) => [[y'' xs']|] //.
      move A2: (it x y true) => x'.  move A3: (transform it (x' ++ xs') ys n) => [[ys' x'']|] //= [H0 H1].
      rewrite -H0 -H1 execute_app {H0 H1}.
      case: m => [m|]; [|rewrite exec_all_none //]. rewrite /Basics.flip /=.
      move M1: (interp x m) => [t1|]; [|rewrite execute_none]; rewrite //.
      move M2: (interp y m) => [t2|]; [|rewrite execute_none]; move => // h h'.
      move: (it_c1 _ _ true _ _ _ M1 M2). rewrite A0 A2. move => /= [B1 [s1 B2]]. rewrite B1 in B2.
    
      move: (IHn _ _ _ _ _ _ _ (conj h' B2) A1) => /= [C1 [s2 C2]].
      assert (D1: exec_all interp (Some t2) (x' ++ xs') = Some s2). by rewrite execute_app B1 B2 -C1 C2.
      move: (IHn _ _ _ _ _ _ _ (conj D1 h) A3) => /= [E1 [s3 E2]]. rewrite -E1 C2 E2. by eauto. Qed.

Corollary ot_correctness: forall op1 op2 m (m1 m2 : X), 
exec_all interp m op1 = Some m1 /\ exec_all interp m op2 = Some m2 ->
exists nSteps op1' op2', transform it op1 op2 nSteps = Some (op2', op1') /\
exec_all interp (Some m1) op2' = exec_all interp (Some m2) op1' /\ exists m3, exec_all interp (Some m1) op2' = Some m3.
move => op1 op2 m m1 m2 H. move: (ot_computable op1 op2) => [n [op1' [op2' A0]]].
exists n. exists op1'. exists op2'. split. done. by move: (ot_execution _ _ _ _ _ _ _ _ H A0). Qed.

End OTCorrectness.

(* =============================================== *)

Module TransformApp.
Require Import ssreflect ssrbool ssrfun ssrnat.

Corollary tstab1 {cmd} t: forall n (op1 op2 op1' op2' : list cmd),
transform t op1 op2 n = Some (op2', op1') -> transform t op1 op2 (n.+1) = Some (op2', op1').
intros. apply tstab with (k:=1) in H. by rewrite -addn1. Qed.

Lemma tr_through_nil {cmd} t (l : list cmd) n: 
transform t l nil n.+1 = Some (nil, l). by rewrite /= list_const. Qed.

Lemma tr_nil {cmd} t (l : list cmd) n:
transform t nil l n.+1 = Some (l, nil). done. Qed.

Lemma part_lemma {cmd} t n: forall (y : cmd) x ys y' x',
transform t x (y :: ys) n = Some (y', x') ->
match transform t x [:: y] n with 
  Some (y', x') => match transform t x' ys n with 
                     Some (ys', x'') => Some (y' ++ ys', x'')
                     | _ => None
                   end
  | _ => None
end = Some (y', x').
intros. case: n x H => [|n] [|x xs] // H. simpl in H.
case A0: (transform t xs (t y x false) n) H => [[a b]|] // H.
case A1: (transform t (t x y true ++ b) ys n) H => [[c d]|] // [A2 A3].
remember (n.+1) as n1. rewrite {1}Heqn1 /= A0. destruct n. inversion A0.
rewrite tr_through_nil cats0. subst. apply tstab1 in A1. rewrite A1. done. Qed.

Lemma part_lemma2 {cmd} t x (y : cmd) ys y' x' y1' x'' n:
transform t x [:: y] n = Some (y', x') ->
transform t x' ys n = Some (y1', x'') ->
transform t x (y :: ys) n.+1 = Some (y' ++ y1', x'').
case A1: n => [|n1] // H H0.
simpl in H. case: x H => [|x xs] //. simpl.
 + move => [*]. subst. by case: n1 H0 => [|n1] [H0 H1]; rewrite -H0 -H1.
 + case A0: transform => [[y''0 xs']|]//. destruct n1; [inversion A0|].
   rewrite tr_through_nil cats0. move => [A2 A3]. subst.
   remember (n1.+2) as n2. apply tstab1 in A0. rewrite -Heqn2 in A0. simpl. by rewrite A0 H0. Qed.

Lemma vpart1inv {cmd} t: forall y1 (x : list cmd) y2 k,
transform t x y1 k = None -> transform t x (y1 ++ y2) k = None.
elim => [|y1 y1s IHy1]; intros. by case: k x H => [|k] [|a l].
case: k H => [|k] //. rewrite cat_cons. remember (k.+1) as k1. rewrite {1}Heqk1 /=.
destruct x. done. case A1: transform => [[y'' xs']|];[| by subst; rewrite /= A1].
case A2: transform => [[ys' x'']|] // A3 {A3}. subst. simpl. rewrite A1.
by rewrite (IHy1 _ y2 _ A2). Qed.

Theorem vpart1 {cmd} t: forall (y1 : list cmd) n x y2 y' x' y1' x'',
transform t x  y1 n = Some (y', x') ->
transform t x' y2 n = Some (y1', x'') ->
exists k, transform t x (y1 ++ y2) k = Some (y' ++ y1', x'').
elim => [|y y1s IHy] [|n] //; intros.
 + rewrite tr_through_nil in H. inversion H. subst. by exists n.+1.
 + move: (part_lemma _ _ _ _ _ _ _ H).
   case A0: transform => [[y'0 x'0]|]//.
   case A1: transform => [[ys' x''0]|]// [A2 A3].
   rewrite A3 {A3 x''0} in A1. rewrite -A2. rewrite -A2 {A2 y'} in H.
   move: (IHy _ _ _ _ _ _ _ A1 H0) => [k' A2]. apply (tstab _ _ (n.+1)) in A2.
   apply (tstab _ _ k') in A0. rewrite addSn in A0. rewrite addnS addnC in A2. 
   exists (n + k').+2. by rewrite cat_cons (part_lemma2 _ _ _ _ _ _ _ _ _ A0 A2) catA. Qed. 

Theorem vpart2 {cmd} t: forall (y1 y2 x : list cmd) y' x' n,
transform t x (y1 ++ y2) n = Some (y', x') ->
match transform t x y1 n with
  Some (y1', x') => match transform t x' y2 n with
                     Some (y2', x'') => Some (y1' ++ y2', x'')
                     | _ => None
                   end
  | _ => None
end = Some (y', x').
elim => [|y y1s IHy1] y2 x Y' X' [|n] H //.
 + rewrite /= list_const. case: x y2 H => [|a b] [|c d] //= H. by rewrite H.
 + remember (n.+1) as n1. rewrite cat_cons in H. move: (part_lemma _ _ _ _ _ _ _ H).
   case A0: transform => [[y' x']|] //. case A1: transform => [[ys' x'']|] // [B0 B1].
   rewrite -B1 -B0. rewrite -B1 -B0 {B0 B1 X' Y'} in H.
   move: (IHy1 _ _ _ _ _ A1).
   case A2: transform => [[y1' x'0]|] //.
   case A3: transform => [[y2' x''0]|] // [B2 B3].
   rewrite B3 {B3 x''0 }in A3. rewrite -B2. rewrite -B2 {B2 ys'} in H A1.
   destruct n1; [inversion A0|].
   case A4: transform => [[y1'0 x'1]|];[|by rewrite -cat_cons (vpart1inv t (y::y1s) x y2 (n1.+1) A4) in H].
   move: (part_lemma2 _ _ _ _ _ _ _ _ _ A0 A2) => H0. apply tstab1 in A4. rewrite A4 in H0. inversion H0. subst.
   by rewrite A3 catA. Qed. 

Theorem hpart2 {cmd} t n: forall (x1 x2 y y' x': list cmd),
transform t (x1 ++ x2) y n = Some (y', x') ->
exists k,
match transform t x1 y k with
  Some (y', x1') => 
   match transform t x2 y' k with
    Some (y'', x2') => Some (y'', x1' ++ x2')
    | _ => None
   end
  | _ => None
end = Some (y', x').
elim: n => [|n IHn]. done. remember (n.+1) as n1.
case => [|x1 x1s] x2 y Y' X'; intros.
 + rewrite /= in H. exists n1.+1. by rewrite tr_nil (tstab1 _ _ _ _ _ _ H).
 + case: y H => [|y ys] H.
  + rewrite Heqn1 tr_through_nil in H. move: H => [A0 A1].
    exists n1. by rewrite Heqn1 2!tr_through_nil -A0 -A1 -cat_cons.
  + move: H. rewrite {1}Heqn1 /=.
    case A0: transform => [[y'' xs']|] //.
    case A1: transform => [[ys' X'2]|] // [A2 A3].
    move: (IHn _ _ _ _ _ A0) => [k1].
    case A4: transform => [[y' x1s']|] //.
    case A5: transform => [[y''1 x2']|] // [A6 A7].
    rewrite -A7 {A7 xs'} in A1 A0. rewrite A3 {A3 X'2} catA in A1. 
    rewrite A6 {A6 y''1} in A5. rewrite -A2 {A2 Y'}.
    move: (IHn _ _ _ _ _ A1) => [k2].
    case A6: transform => [[ys0' x1'']|] //.
    case A7: transform => [[y''0 x2'']|] // [A8 A9].
    rewrite -A9. rewrite -A9 {X' A9} in A1. rewrite A8 {A8 y''0} in A7.
    apply (tstab _ _ k2) in A5. apply (tstab _ _ k1) in A7.
    apply (tstab _ _ k2) in A4. apply (tstab _ _ k1) in A6.
    rewrite addnC in A6 A7.
    move: (vpart1 _ _ _ _ _ _ _ _ _ A5 A7) => [k'' B].
    exists (k1+k2+k'').+1. remember (k1+k2+k'').+1 as k. rewrite {1}Heqk /=.
    apply (tstab _ _ k'') in A4. apply (tstab _ _ k'') in A6.
    apply (tstab _ _ (k1+k2)) in B. rewrite addnC in B.    
    by rewrite A4 A6 Heqk (tstab1 _ _ _ _ _ _ B). Qed.

End TransformApp. 

(* =============================================== *)

Module Transform2.

Fixpoint transform2 {cmd} (t : cmd -> cmd -> bool -> list cmd) (op1 op2 : list cmd) (nSteps : nat) : option ((list cmd) * (list cmd)) :=
match nSteps with 0 => None | S nSteps' =>
  match op1, op2 with
    | nil, _ | _, nil => Some (op2, op1)
    | x :: xs, y :: ys => let y' := t y x false in let x' := t x y true in
       match transform2 t xs y' nSteps', transform2 t x' ys nSteps' with
         Some (y'', xs'), Some (ys', x'') => 
          match transform2 t xs' ys' nSteps' with
            Some (ys'', xs'') => Some (y'' ++ ys'', x'' ++ xs'') 
            | _ => None
          end
         | _, _ => None
       end
  end
end.

Lemma tstab2 {cmd} t: forall n k (op1 op2 op1' op2' : list cmd),
transform2 t op1 op2 n = Some (op2', op1') -> 
transform2 t op1 op2 (n + k) = Some (op2', op1').
elim => [|n IHn] k [|o1 op1] [|o2 op2] op1' op2' //=.
case A1: transform2 => [[y'' xs']|] //. case A2: transform2 => [[ys' x'']|] //.
case A3: transform2 => [[ys'' xs'']|] // [B0 B1]. subst.
by rewrite (IHn k _ _ _ _ A1) (IHn k _ _ _ _ A2) (IHn k _ _ _ _ A3). Qed.

Corollary tstab12 {cmd} t: forall n (op1 op2 op1' op2' : list cmd),
transform2 t op1 op2 n = Some (op2', op1') -> transform2 t op1 op2 (n.+1) = Some (op2', op1').
intros. apply tstab2 with (k:=1) in H. by rewrite -addn1. Qed.

Lemma tr2_through_nil {cmd} t (l : list cmd) n: 
transform2 t l nil n.+1 = Some (nil, l). by rewrite /= list_const. Qed.

Lemma tr2_nil {cmd} t (l : list cmd) n:
transform2 t nil l n.+1 = Some (l, nil). done. Qed.

End Transform2.

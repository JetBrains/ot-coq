From Coq Require Export ssreflect ssrfun ssrbool Omega Basics Equality.
Require Export mathcomp.ssreflect.eqtype.
Require Export mathcomp.ssreflect.seq.
Require Export mathcomp.ssreflect.ssrnat.
Require Export Ssromega.

Definition bind {X} {Y} (f : X -> option Y) (x : option X) : option Y :=
 match x with Some x' => f x' | _ => None end.

Definition fmap {X Y} (f : X -> Y) : option X -> option Y :=
  fun ox =>
    match ox with
    | Some x => Some (f x)
    | None => None
    end.

Definition maybe_eq {X} (eq : X -> X -> Prop) : option X -> option X -> Prop :=
  fun a b =>
    match a, b with
    | Some a', Some b' => eq a' b'
    | None, None => True
    | _, _ => False
    end.

Lemma fadd {X} {F : X -> nat} n l: foldl addn n [seq F i | i <- l] = n + foldl addn 0 [seq F i | i <- l].
elim: l n => [|l ls IHl] //= n. by rewrite add0n (IHl (n + F l)) (IHl (F l)) addnA. Qed.

Lemma faddr {X} {F : X -> nat} n l: foldr addn n [seq F i | i <- l] = n + foldr addn 0 [seq F i | i <- l].
elim: l n => [|l ls IHl] //= n. by rewrite addnA (addnC n) -addnA -(IHl n). Qed.

(* Some Numeric facts*)

Lemma le_ex : forall i k,
 i <= k -> exists j, i + j = k.
Proof. move=> i k; elim: k i => [i|k IHk]. by rewrite leqn0 => /eqP ->; exists 0.
 case => [|i]; first by exists k.+1. 
 by rewrite (leq_add2l 1) => /IHk [x] <-; exists x. Qed.

Lemma Nleq_ltnC: forall i k, i <= k -> k < i -> false.
Proof. move=> i k. by rewrite leqNgt => /negbTE ->. Qed.

Ltac maxapply H := move: H; repeat (let NH := fresh in move => NH /NH; move: NH => _).

Lemma ltn_addWr x y z: x + y < z -> x < z.
Proof. move=> /leq_trans A. move: (A _ (leq_addr y _)). by rewrite ltn_add2r. Qed.
Lemma leq_addWr x y z: x + y <= z -> x <= z.
Proof. move=> /leq_trans A. move: (A _ (leq_addr y _)). by rewrite leq_add2r. Qed.
Lemma ltn_addWl x y z: y + x < z -> x < z.
Proof. move=> /leq_trans A. move: (A _ (leq_addl y _)). by rewrite ltn_add2l. Qed.
Lemma leq_addWl x y z: y + x <= z -> x <= z.
Proof. move=> /leq_trans A. move: (A _ (leq_addl y _)). by rewrite leq_add2l. Qed.

Section MonadicNotation.

Context {A B : Type}.

Definition true_some (b : bool) (f : B) : option B :=
 if b then Some f else None.

End MonadicNotation.

Notation "P --- Q" := (forall x, P x = false -> Q x = false) (at level 60).
Notation "ma >>=  f" := (bind f ma) (at level 60).
Notation "[! b !] f" := (true_some b f) (at level 60).

Lemma compA {A B C D} (f3 : C -> D) (f2 : B -> C) (f1 : A -> B): (f3 \o f2) \o f1 =1 f3 \o (f2 \o f1). done. Qed.

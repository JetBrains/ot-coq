Require Import ssreflect ssrbool eqtype ssrnat Ssromega.

CoInductive interval_point x sx y: bool -> bool -> Prop :=
 | IP_Left of y <= x : interval_point x sx y true false
 | IP_Right of x + sx.+1 <= y : interval_point x sx y false true
 | IP_Inside of x < y & y < x + sx.+1 : interval_point x sx y false false.

CoInductive interval_point_inclusive x sx y: bool -> bool -> Prop :=
 | IPI_Left of y < x : interval_point_inclusive x sx y true false
 | IPI_Right of x + sx <= y : interval_point_inclusive x sx y false true 
 | IPI_Inside of x <= y & y < x + sx : interval_point_inclusive x sx y false false.

Record ii_choice {Z : Type} := mkIIChoice
 { ii_f12 : Z; (* contained n1 <= n1 + len1 <= n2 <= n2 + len2 *)
   ii_f21 : Z; (* contained n2 <= n2 + len2 <= n1 <= n1 + len1 *)
   ii_feq : Z; (* coincide *)
   ii_f121 : Z; (* contained n1 = n2 <= n2 + len2 <= n1 + len1 *)
   ii_f212 : Z; (* contained n2 <= n1 <= n1 + len1 <= n2 + len2 *)
   ii_f2121 : Z; (* overlap n2 < n1 <= n2+l2 < n1+l1 *)
   ii_f1212 : Z}. (* overlap n1 < n2 <= n1 + len1 < n2 + len2*)

Definition interval_interval_case {Z : Type} (n1 len1 n2 len2 : nat) (c : @ii_choice Z) :=
 if ((n1 == n2) && (len1 == len2)) then ii_feq c (* coincide *) else 
 if (n1 + len1 <= n2) then ii_f12 c (* contained n1 <= n1 + len1 <= n2 <= n2 + len2 *) else 
 if (n2 + len2 <= n1) then ii_f21 c (* contained n2 <= n2 + len2 <= n1 <= n1 + len1 *) else
 if (n1 >= n2) then  
   if (n1 + len1 <= n2 + len2) then ii_f212 c (* contained n2 <= n1 <= n1 + len1 <= n2 + len2 *) else
   if (n1 == n2) then ii_f121 c (* contained n1 = n2 <= n2 + len2 <= n1 + len1 *) 
                 else ii_f2121 c (* overlap n2 < n1 <= n2+l2 < n1+l1 *)
 else if (n1 + len1 >= n2 + len2) then ii_f121 c (* contained n1 < n2 <= n2 + len2 <= n1 + len1 *)
                                  else ii_f1212 c (* overlap n1 < n2 <= n1 + len1 < n2 + len2*).

CoInductive interval_cases_analysis {Z : Type} (x sx y sy : nat) (c1 : ii_choice) : Z -> Prop :=
 | I_12 of x + sx <= y : 
   interval_cases_analysis x sx y sy c1 (@ii_f12 Z c1) 
 | I_21 of y + sy <= x : 
   interval_cases_analysis x sx y sy c1 (@ii_f21 Z c1) 
 | I_eq of x == y & sx == sy : 
   interval_cases_analysis x sx y sy c1 (@ii_feq Z c1) 
 | I_121 of x <= y & y + sy <= x + sx & ((x != y) \/ sx != sy): 
   interval_cases_analysis x sx y sy c1 (@ii_f121 Z c1) 
 | I_212 of y <= x & x + sx <= y + sy & ((x != y) \/ sx != sy): 
   interval_cases_analysis x sx y sy c1 (@ii_f212 Z c1) 
 | I_1212 of x < y & y < x + sx & x + sx < y + sy : 
   interval_cases_analysis x sx y sy c1 (@ii_f1212 Z c1) 
 | I_2121 of y < x & x < y + sy & y + sy < x + sx : 
   interval_cases_analysis x sx y sy c1(@ii_f2121 Z c1).
 
CoInductive interval_interval_case_anal {Z : Type} (x sx y sy : nat) (c1 c2 : ii_choice)
 : Z -> Z -> Prop :=
 | II_12 of x + sx <= y : interval_interval_case_anal x sx y sy c1 c2 (@ii_f12 Z c1) (@ii_f21 Z c2)
 | II_21 of y + sy <= x : interval_interval_case_anal x sx y sy c1 c2 (@ii_f21 Z c1) (@ii_f12 Z c2)
 | II_eq of x == y & sx == sy : interval_interval_case_anal x sx y sy c1 c2 (@ii_feq Z c1) (@ii_feq Z c2)
 | II_121 of x <= y & y + sy <= x + sx & ((x != y) \/ sx != sy)
   : interval_interval_case_anal x sx y sy c1 c2 (@ii_f121 Z c1) (@ii_f212 Z c2)
 | II_212 of y <= x & x + sx <= y + sy & ((x != y) \/ sx != sy)
   : interval_interval_case_anal x sx y sy c1 c2 (@ii_f212 Z c1) (@ii_f121 Z c2)
 | II_1212 of x < y & y < x + sx & x + sx < y + sy : 
   interval_interval_case_anal x sx y sy c1 c2 (@ii_f1212 Z c1) (@ii_f2121 Z c2)
 | II_2121 of y < x & x < y + sy & y + sy < x + sx : 
   interval_interval_case_anal x sx y sy c1 c2(@ii_f2121 Z c1) (@ii_f1212 Z c2).

Lemma int_ptP x sx y : interval_point x sx y (y <= x) (x + sx.+1 <= y).
Proof. case: (leqP y x) => H; nat_norm.
 - move/leq_trans:(H) => /(_ _ (leq_addr sx _)). rewrite leqNgt => /negbTE ->. by constructor.
 - case: ltnP => H'; nat_norm; by constructor; nat_norm.
Qed.

Lemma int_pt_incP x sx y : interval_point_inclusive x sx y (y < x) (x + sx <= y).
Proof. case: (leqP x y) => H.
 - case: (leqP (x + sx) y) => H'. by apply : IPI_Right. by apply: IPI_Inside.
 - move: (H) => /(leq_trans) => /(_ _ (leq_addr sx _)). rewrite ltnNge => /negbTE ->. by apply: IPI_Left.
Qed.

Lemma interval_cases_analysisP {Z : Type} (x sx y sy : nat) (c1 : @ii_choice Z)
 : interval_cases_analysis x sx y sy c1 (interval_interval_case x sx y sy c1).
rewrite /interval_interval_case.

 case H0: (_ == _) => /=.
 case H1: (_ == _) => /=; (try by constructor).
 case H2: (_ <= _); (try by constructor).
 case H3: (_ <= _); (try by constructor).
 case H4: (_ <= _); case H5: (_ <= _); constructor => //; try (right; rewrite H1 //); try ssromega. 
 case H2: (_ <= _); (try by constructor);
 case H3: (_ <= _); (try by constructor);
 case H4: (_ <= _); case H5: (_ <= _); constructor => //; try (left; rewrite H0 //); try ssromega.
Qed.

Lemma interval_interval_case_analP {Z : Type} (x sx y sy : nat) (c1 c2 : @ii_choice Z)
 : interval_interval_case_anal x sx y sy c1 c2
   (interval_interval_case x sx y sy c1) (interval_interval_case y sy x sx c2).
Proof. rewrite /interval_interval_case. rewrite [y == x]eq_sym [sy == sx]eq_sym.
 case: (int_pt_incP x sx y).
 + case: (int_pt_incP y sy x).
  * move/(leq_ltn_trans) => H /H /ltnW; by rewrite ltnn.
  * rewrite eq_sym. move => H H'. move/ltn_eqF: (H') -> => /=. by constructor.
  * move=> H1 H2 H3. move/gtn_eqF: (H3) -> => /=; rewrite H1 [x <= y]leqNgt H3 /=.
    case: leqP; by constructor => //; left; move/gtn_eqF: H3 => ->.
 + case: ifP.
  * move/andP => []; by constructor.
  * move: sx => [|sx]. move: sy => [|sy]. 
   - rewrite eq_refl andbT ?addn0 => F. rewrite leq_eqVlt => /orP []; first by rewrite F. 
     rewrite [y <= x]leqNgt. move=> H; rewrite H. by constructor; rewrite addn0; apply: ltnW.
   - move=> _; rewrite addn0 addnS leqNgt => /negbTE. case: ifP;
     first by move=> /(leq_ltn_trans _) => /(_ _ (leq_addr sy _)) ->. move=> _ /negbT; rewrite -leqNgt.
     by constructor; rewrite addn0.
   - move => ?. case: ifP; first by rewrite addnS; 
     move=> /(leq_trans _) => /(_ _ (leq_addr sy _)) H /(leq_ltn_trans _) => /(_ _ (leq_addr sx _)); rewrite ltnNge H.
     by constructor.
 + case: ifP; first by move/andP => [];  constructor.
   case: sy => [|sy].
  * rewrite addn0 [y <= x]leqNgt. case: (ltngtP x y)=> /=.
   - move=> H _ -> /ltnW => H'; rewrite H'. 
     constructor; [apply: ltnW| rewrite ?addn0|left; move/ltn_eqF: H => ->] => //. 
   - move/ltnW => ? _ ? /ltnW ?. by constructor; rewrite addn0.
   - move=> ->; by constructor; rewrite ?addn0.
  * case: ifP.
   - rewrite addnS => /(leq_ltn_trans _) => /(_ _ (leq_addr sy _)); by rewrite ltnNge => /negbTE ->.
   - move/negbT; rewrite -ltnNge. move => H1 H2 H3. rewrite H3. case: ifP.
    + move=> H3'; move/andP: (conj H3 H3'). rewrite -eqn_leq => /eqP Heq. rewrite -Heq in H1. rewrite -Heq in H2.
      rewrite -Heq eq_refl. rewrite [x + sx <= _]leqNgt [x + sy.+1 <= _]leqNgt. 
      case: (ltngtP (x + sx) (x + sy.+1)) => /=. 
      - constructor => //; by [apply ltnW | right; move:H2; rewrite eq_refl //= => ->].
      - constructor => //; by [apply ltnW | right; move:H2; rewrite eq_refl //= => ->].
      - by move/eqP; rewrite eqn_add2l; move: H2; rewrite eq_refl => //= ->.
    + move/negbT. rewrite -ltnNge => H. move/ltn_eqF: (H) ->. case: ifP. 
     - by constructor => //; left; move/ltn_eqF: H => ->. 
     - move/negbT; rewrite -ltnNge; constructor => //.
Qed.



Require Export monoid.
Set Implicit Arguments.
Unset Strict Implicit.
Require Import normalisation.
Require Import Coq.Logic.Classical_Prop.

Notation top' n m := (@top (mor n m)).

Section VertexColoringProgramVerification.


(** auxiliary lemmata for relation algebra *)

Lemma cap_leq `{laws} `{BL<<l} n m (Q R : X n m): Q ^ R <== Q.
Proof. ra. Qed.


Lemma cup_leq_spec `{laws} `{BL<<l} n m (Q R : X n m): Q <== R <-> Q + R == R.
Proof. split. 
  intro E. apply weq_spec. split. 
    rewrite E. now ra. 
    now ra. 
  intro E. rewrite <- E. now ra.
Qed.


Lemma unique_neg `{laws} `{BL<<l} n m (Q R : X n m): Q <== R -> Q ^ !R == 0.
Proof. intro E. apply leq_xb_iff. 
  apply leq_iff_cap in E. rewrite <- E. 
  rewrite <- capA. 
  rewrite (capneg R). now ra.
Qed.

Lemma dotAext `{laws} `{BL+STR+CNV<<l} a b c d e (Q : X a b)(R : X b c)(S : X c d)(T : X d e): 
Q*R*S*T == Q*(R*S*T).
Proof. ra. Qed. 

Lemma dot_leq_r `{laws} `{BL+STR+CNV<<l} n m p (Q R : X n m)(S : X m p): 
 Q <== R -> Q*S <== R*S. 
Proof. intro E. 
  apply leq_iff_cup in E. 
  rewrite leq_iff_cup. rewrite <- dotplsx. rewrite E. now ra.
Qed.

Lemma dot_leq_l `{laws} `{BL+STR+CNV<<l} n m p (S : X n m)(Q R : X m p): 
 Q <== R -> S*Q <== S*R. 
Proof. intro E. apply leq_iff_cup in E. 
  rewrite leq_iff_cup. rewrite <- dotxpls. rewrite E. now ra.
Qed.


Lemma leq_bot_iff `{laws} `{BL<<l} n m (R : X n m): 
R == 0 <-> R <== ! R.
Proof. split. 
  intro E. rewrite E. now ra. 
  intro E. rewrite leq_iff_cap in E. rewrite <- E. rewrite capneg. now ra.
Qed.


(** derivation of the Schroeder equivalences *)

Lemma schroeder1 `{laws} `{BL+STR+CNV<<l} n m p (Q : X n m)(R : X m p)(S : X n p): 
 Q*R <== S -> Q`*!S <== !R. 
Proof. intro E. apply unique_neg in E. 
  apply neg_unique'. apply leq_xb_iff. rewrite capdotx, cnv_invol, capC. 
  rewrite E. now ra. 
Qed.

Lemma schroeder2 `{laws} `{BL+STR+CNV<<l} n m p (Q : X n m)(R : X m p)(S : X n p): 
 Q`*!S <== !R -> Q*R <== S. 
Proof. intro E. apply unique_neg in E. rewrite negneg in E. rewrite <- (negneg S).
  apply neg_unique'. apply leq_xb_iff. rewrite capdotx, capC. 
  rewrite E. now ra.
Qed.

Lemma schroeder3 `{laws} `{BL+STR+CNV<<l} n m p (Q : X n m)(R : X m p)(S : X n p): 
 Q*R <== S -> !S* R` <== !Q . 
Proof. intro E. apply unique_neg in E. apply neg_unique'.
  apply leq_xb_iff. rewrite capxdot, cnv_invol, capC. 
  rewrite E. now ra. 
Qed.

Lemma schroeder4 `{laws} `{BL+STR+CNV<<l} n m p (Q : X n m)(R : X m p)(S : X n p): 
 !S* R` <== !Q -> Q*R <== S. 
Proof. intro E. apply unique_neg in E. rewrite negneg in E. 
  rewrite <- (negneg S). apply neg_unique'. apply leq_xb_iff. rewrite capxdot, capC.
  rewrite E. now ra.
Qed.


(** Tarski rule has to be added *)

Definition tarski_rule `{laws} : Prop := 
( forall a b c d (R : X b c), (top' a b)*R*(top' c d) == top <-> ~(R == 0)).


(** predicates for vector and point *)

Definition vector `{laws} {n} {m} : X n m -> Prop := 
fun v => v == v*top.

Definition point `{laws} {n} {m} : X n m -> Prop := 
fun p => vector p /\ p*p` <== 1 /\ (forall a, top' a m == top*p).


(** Proof of Lemma 2.1 about points of Section 2 devided in the two included statements *)

Lemma lemma_2_1_1 `{laws} `{BL+STR+CNV<<l} m n: 
tarski_rule -> forall (p : X m n), point p -> ~(p == 0).  
Proof. intro T. intros p Hp. 
  rewrite <- (T m m n n p).
    unfold point in Hp. destruct Hp as [Hp1 [Hp2 Hp3]]. 
      unfold vector in Hp1.
  rewrite <- dotA. rewrite <- Hp1. rewrite <- Hp3. 
  now ra. 
Qed.
 
Lemma lemma_2_1_2 `{laws} `{BL+STR+CNV<<l} m n o: 
tarski_rule -> forall (p : X m n)(q : X o n), point p /\ point q -> ~(p*q` == 0).  
Proof. intro E. 
    unfold tarski_rule in E.
  intros p q. intros F. 
    destruct F as [Hp Hq].
  rewrite <- (E m m o m (p*q`)). rewrite dotA. 
    unfold point in Hp. destruct Hp as [Hp1 [Hp2 Hp3]]. 
      unfold vector in Hp1.
  rewrite <- Hp3. rewrite (E m n o m (q`)). 
  rewrite <- cnv_weq_iff'. rewrite cnv0. apply lemma_2_1_1. 
  unfold tarski_rule. 
  exact E. 
  exact Hq.
Qed.


(** verification of the vertex coloring program *)

(** predicates for some specific relations *)

Definition coloringProperty `{laws} {v} {f}: X v f -> X v v -> Prop := fun C E => C*C` <== !E.
Definition total `{laws} {v} {f}: X v f -> Prop := fun C => (forall a, C*top' f a <== top).
Definition univalent `{laws} {v} {f}: X v f -> Prop := fun C => C`*C <== 1.

Definition symmetric `{laws} {v}: X v v -> Prop := fun E => E == E`.
Definition irreflexive `{laws} {v}: X v v -> Prop := fun E => E <== !1.


(** Proofs of Section 3 *)

Lemma lemma_3_1 `{laws} `{BL+STR+CNV<<l} v f (E : X v v): 
coloringProperty (zer v f) E /\ univalent (zer v f).
Proof. split.
  unfold coloringProperty. now ra. 
  unfold univalent. now ra.
Qed.

Lemma lemma_3_2 `{laws} `{BL+STR+CNV<<l} v f (C : X v f)(p : X v v)(q : X f v): 
univalent C /\ point p /\ point q /\ ~(total C) /\ p <== !(C * top) -> univalent (C + p*q`).
Proof. intro E. 
    destruct E as [E1 [E2 [E3 [E4 E5]]]]. 
      apply neg_leq_iff', schroeder1 in E5. rewrite negneg, negtop in E5. 
      apply cnv_leq_iff in E5. rewrite cnv0, cnvdot, cnv_invol, leq_xb_iff in E5. 
  unfold univalent. rewrite cnvpls, dotxpls. repeat rewrite dotplsx. repeat apply leq_cupx. 
  now apply E1. 
  rewrite cnvdot, cnv_invol. rewrite <- dotA, E5. now ra. 
  rewrite dotA. apply cnv_leq_iff. rewrite cnv1. repeat rewrite cnvdot, cnv_invol. 
  rewrite E5. now ra. 
    rewrite cnvdot, cnv_invol, dotA. 
    assert (E6 := leq_xt (p`*p)). 
      apply dot_leq_r with (S:= q`) in E6. 
      apply dot_leq_l with (S:= q) in E6. 
  rewrite dotAext, E6. rewrite dotA. 
    unfold point in E3. destruct E3 as [F1 [F2 F3]]. 
      unfold vector in F1. 
  rewrite <- F1. now exact F2. 
Qed.


Lemma lemma_3_3 `{laws} `{BL+STR+CNV<<l} v f (C : X v f)(E p : X v v)(q : X f v): 
coloringProperty C E /\ point p /\ point q /\ ~(C`*E*p == top) /\ 
q <== !(C`*E*p) /\ irreflexive E /\ symmetric E
-> coloringProperty (C + p*q`) E.
Proof. intro F. 
    destruct F as [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]]. 
      rewrite neg_leq_iff' in F5. rewrite <- dotA in F5. 
      apply schroeder1 in F5. rewrite negneg, cnv_invol in F5. rewrite neg_leq_iff' in F5.
      apply schroeder3 in F5. rewrite negneg in F5. 
      unfold point in F2, F3. 
  unfold coloringProperty. rewrite cnvpls. rewrite dotxpls. repeat rewrite dotplsx. 
  repeat apply leq_cupx. 
  now apply F1. 
    unfold symmetric in F7.
  rewrite <- cnv_leq_iff. repeat rewrite cnvdot. repeat rewrite cnv_invol. 
  rewrite dotA, cnvneg, F7, cnv_invol, F5. now ra. 
  rewrite cnvdot, cnv_invol, dotA, F5. now ra.
  rewrite cnvdot, cnv_invol, dotA, dotAext.
    destruct F2 as [G1 G2]. 
      unfold vector in G1. 
  assert (E6 := leq_xt (q `*q)). 
    apply dot_leq_r with (S:= p`) in E6. 
    apply dot_leq_l with (S:= p) in E6. 
  rewrite E6, dotA. rewrite <- G1.
    destruct G2 as [H1 H2]. 
  rewrite H1. 
    unfold irreflexive in F6. 
  rewrite neg_leq_iff'. now apply F6.
Qed.


Lemma lemma_3_4 `{laws} `{BL+STR+CNV<<l} v f (C : X v f)(E p : X v v)(q : X f v): 
tarski_rule ->
(coloringProperty C E /\ ~(total C) /\ p <== !(C * top)  /\ point p /\ point q -> 
C <== C + p*q` /\  ~(C == C + p*q`)).
Proof. intro T. intro F. split. 
  now ra. 
  rewrite weq_spec. 
  apply or_not_and. right.
  assert (G := lemma_2_1_2). assert (J := G v v f). 
  rewrite cup_spec. 
  apply or_not_and. right.
  assert (forall (p0 : X v v) (q0 : X f v), point p0 /\ point q0 -> ~(p0*q0` == 0)).
  now apply (J T). 
  assert (H2 := H1 p q). 
    destruct F as [F1 [F2 [F3 F4]]].
  assert (~ (p * q ` == 0)).
  now apply (H2 F4).
  assert (p*q` <== ! C).
  apply schroeder2. rewrite negneg. apply cnv_leq_iff. rewrite cnvneg. 
  rewrite cnv_invol, cnvdot. rewrite cnv_invol. 
  assert (H4 := dot_leq_l).
  assert (H5 := H4 f v v (C`) p (!(C * top' f v))).
  assert (C ` * p <== C ` * !(C * top' f v)).
    apply (H5 F3).
  rewrite H6.
  apply schroeder1. 
  apply dot_leq_l.
  now ra. 
    apply neg_leq_iff' in H4. 
  rewrite H4. rewrite <- leq_bot_iff. now exact H3.
Qed.


End VertexColoringProgramVerification.
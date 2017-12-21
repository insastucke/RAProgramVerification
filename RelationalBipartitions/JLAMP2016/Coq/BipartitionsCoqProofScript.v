
(** This file contains most of the proofs of the presented lemmata and 
theorems. *)

Require Import monoid kleene.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import normalisation.
Require Import kat_tac.

Notation top' n m := (@top (mor n m)).


Section Bipartitions.


(** predicates for vector and point and some specific relations *)

Definition vector `{laws} {n} {m}: X n m -> Prop := fun v => v == v*top.

Definition point `{laws} {n} {m}: X n m -> Prop := 
fun p => vector p /\ p*p` <== 1 /\ (forall a, top' a m == top*p).

Definition transitive `{laws} {m}: X m m -> Prop := fun R => R*R <== R.

Definition symmetric `{laws} {m}: X m m -> Prop := fun R => R == R`.

Definition univalent `{laws} {m} {n}: X n m -> Prop := 
fun R => R`*R <== 1.

Definition total `{laws} {m} {n}: X n m -> Prop := 
fun R => forall p, R*top' m p == top.

Definition mapping `{laws} {m} {n}: X n m -> Prop := 
fun R => univalent R /\ total R.

Definition bipartition `{laws} {m} {n}: X m m -> X m n -> X m n -> Prop := 
fun R v w => vector v /\ vector w /\ v ^ w == 0 /\ R <== v*w` + w*v`.

Definition part_equiv_rel `{laws} {m}: X m m -> Prop := 
fun P => symmetric P /\ transitive P.

Definition splitting `{laws} {m} {n}: X n m -> X n n -> Prop := 
fun S P => part_equiv_rel P /\ S*S` == P /\ S`*S == 1.



(** auxiliary facts about composition, 
most of them are automatically proven with the ra tactic (see normalisation.v) *)

Lemma dotA_lm `{laws} `{BDL+STR+CNV<<l} a b c d e (v : X a b)(w : X b c)(x : X c d)(y : X d e): 
v*w*x*y == v*(w*x)*y.
Proof. now ra. Qed. 

Lemma dotA_rm `{laws} `{BDL+STR+CNV<<l} a b c d e (v : X a b)(w : X b c)(x : X c d)(y : X d e): 
v*w*(x*y) == v*(w*x)*y.
Proof. now ra. Qed. 

Lemma dotA_rrm `{laws} `{BDL+STR+CNV<<l} a b c d e (v : X a b)(w : X b c)(x : X c d)(y : X d e): 
v*(w*x*y) == v*(w*x)*y.
Proof. now ra. Qed. 

Lemma dotA5 `{laws} `{BDL+STR+CNV<<l} b c d e f g 
(v : X b c)(w : X c d)(x : X d e)(y : X e f)(z : X f g): 
v*w*x*y*z == v*w*(x*y)*z.
Proof. now ra. Qed. 

Lemma dotA6 `{laws} `{BDL+STR+CNV<<l} a b c d e f g
(u : X a b)(v : X b c)(w : X c d)(x : X d e)(y : X e f)(z : X f g): 
u*v*w*x*y*z == u*(v*w*x*y)*z.
Proof. now ra. Qed. 

Lemma dot_leq_ext `{laws} `{BDL+STR+CNV<<l} m (x y : X m m): 
x <== y ->  x*x <== y*y.
Proof. intro E. apply dot_leq. 
  assumption. 
  assumption. 
Qed. 

Lemma dot_leq_l `{laws} `{BDL+STR+CNV<<l} n m p (S : X n m)(Q R : X m p): 
 Q <== R -> S*Q <== S*R. 
Proof. intro E. apply leq_iff_cup in E. 
  rewrite leq_iff_cup. rewrite <- dotxpls. rewrite E. now ra.
Qed.

Lemma dot_leq_r `{laws} `{BDL+STR+CNV<<l} n m p (Q R : X n m)(S : X m p): 
 Q <== R -> Q*S <== R*S. 
Proof. intro E. 
  apply leq_iff_cup in E. 
  rewrite leq_iff_cup. rewrite <- dotplsx. rewrite E. now ra.
Qed.



(** auxiliary facts about union, 
each fact is automatically proven with the ra tactic (see normalisation.v) *)

Lemma cupA_lm `{laws} `{BDL+STR+CNV<<l} a b(v w x y : X a b): 
v+w+(x+y) == v+(w+x)+y.
Proof. now ra. Qed. 

Lemma cupA_llr `{laws} `{BDL+STR+CNV<<l} a b (v w x y : X a b): 
v+w+x+y == (v+w)+(x+y).
Proof. now ra. Qed. 



(** auxiliary facts about the (reflexive) transitive closure, 
most of them are automatically proven with the ka tactic (see kat_tac.v) 
or the ra tactic (see normalisation.v) *)

Lemma aux_lemma_str `{laws} `{BDL+STR+CNV<<l} n (R : X n n): (R*R)^* + R*(R*R)^* == R^*. 
Proof. now ka. Qed. 

Lemma aux_star_trans `{laws} `{BDL+STR+CNV<<l} n (R : X n n): 
transitive R -> R == R^+.
Proof. intro E. unfold transitive in E. 
  rewrite weq_spec. split. 
    rewrite <- itr_ext. now ra. 
    apply itr_ind_l1. 
      now ra. 
      exact E.
Qed.

Lemma itr_leq_str `{laws} `{STR<<l} {n} (x: X n n): x^+ <== x^*. 
Proof. now ra. Qed.



(** some auxiliary facts about top element *)

Lemma toptop_hom `{laws} `{BDL+STR+CNV<<l} n : 
(top' n n)*(top' n n) == top' n n. 
Proof. apply leq_tx_iff. 
  assert (top' n n *1 <== top' n n * top' n n). 
    apply dot_leq_l. apply leq_xt. 
  rewrite <- H1. now ra. 
Qed. 

Lemma dotxt `{laws} `{BDL+STR+CNV<<l} n (x : X n n): 
x <== x*top.
Proof. rewrite <- (dotx1 x). rewrite <- dotA. rewrite dot1x. apply dot_leq_l. now ra. Qed. 

Lemma dottx `{laws} `{BDL+STR+CNV<<l} n m(x : X n m): 
x <== top *x.
Proof. rewrite <- (dot1x x). rewrite dotA. rewrite dotx1. apply dot_leq_r. now ra. Qed. 



(** some auxiliary facts about specific relations *)

Lemma univalent_cap `{laws} `{BDL+STR+CNV<<l} n m p (Q : X n m)(R S : X m p): 
univalent Q -> Q*(R ^ S) == (Q*R) ^ (Q*S).  
Proof. intro E. 
  apply antisym. 
    now ra. 
    rewrite capdotx, dotA. 
      unfold univalent in E. 
    rewrite E. now ra.
Qed.

Lemma point_cap `{laws} `{BDL+STR+CNV<<l} n m p (R S : X n m)(q : X m p): 
point q -> (R ^ S)*q == (R*q) ^ (S*q).  
Proof. intro E. 
  apply antisym. 
    now ra. 
    rewrite capxdot. 
      unfold point in E. destruct E as [E1 [E2 E3]]. 
    rewrite <- dotA. rewrite E2. now ra. 
Qed.

Lemma univalent_cap_cnv `{laws} `{BDL+STR+CNV<<l} n m p (Q : X n p)(R S : X m p): 
univalent Q -> (R ^ S)*Q` == (R*Q`) ^ (S*Q`).  
Proof. intro E. 
  apply antisym. 
    now ra. 
    rewrite capxdot, cnv_invol. 
      unfold univalent in E. 
    rewrite <- dotA. rewrite E. now ra.
Qed.

Lemma total_equiv `{laws} `{BDL+STR+CNV<<l} n m (R : X n m): 
1 <== R*R` <-> total R. 
Proof. split. 
  intro E. unfold total. intro p. apply leq_tx_iff. rewrite <- (dot1x (top' n p)). 
  rewrite E. rewrite <- dotA. apply dot_leq_l with (S:=R). now ra. 
  intro E. unfold total in E. 
    assert (1 == 1 ^ (R*top' m n)). symmetry. 
    rewrite <- leq_iff_cap. rewrite E. now ra. 
  rewrite H1, capC, capdotx. now ra. 
Qed.  



(** proofs of Lemma 2.1 of Section 2 devided in the occuring statements *)

Lemma lem_2_1_1_1 `{laws} `{BDL+STR+CNV<<l} n m (v w : X n m): 
 vector v /\ vector w /\ v ^ w == 0 -> v`*w == 0. 
Proof. intro E. destruct E as [E1 [E2 E3]]. unfold vector in E1. 
  apply leq_xb_iff. rewrite <- capxt. rewrite capdotx, cnv_invol.
 rewrite <- E1. rewrite capC, E3, dotx0. now ra. 
Qed.

Lemma lem_2_1_1_2 `{laws} `{BDL+STR+CNV<<l} n m (v w : X n m): 
 vector v /\ vector w /\ v ^ w == 0 -> w`*v == 0. 
Proof. intro E. destruct E as [E1 [E2 E3]]. unfold vector in E2. 
  apply leq_xb_iff. rewrite <- capxt. rewrite capdotx, cnv_invol.
  rewrite <- E2. rewrite E3, dotx0. now ra. 
Qed.

Lemma lem_2_1_2 `{laws} `{BDL+STR+CNV<<l} n m (v w : X n m): 
vector v /\ vector w /\ v ^ w == 0 -> transitive (v*v` + w*w`). 
Proof. intro E. edestruct E. destruct H2. unfold vector in H1, H2. 
  unfold transitive. rewrite dotplsx. repeat rewrite dotxpls. 
  repeat rewrite dotA, cup_spec. repeat split. 
    rewrite dotA_lm, (leq_xt (v`*v)). 
    rewrite <- H1. now ra.   
    rewrite dotA_lm. rewrite lem_2_1_1_2. now ra. rewrite capC. auto. 
    rewrite dotA_lm. rewrite lem_2_1_1_2. now ra. exact E. 
    rewrite dotA, dotA_lm. rewrite (leq_xt (w` * w)). rewrite <- H2. now ra.   
Qed.

Lemma lem_2_1_3 `{laws} `{BDL+STR+CNV<<l} n m (v w : X n m): 
vector v /\ vector w /\ v ^ w == 0 -> 
(v*w` + w*v`)*(v*w` + w*v`) <== v*v` + w*w`. 
Proof. intro E. edestruct E. destruct H2. 
  rewrite dotplsx. repeat rewrite dotxpls. rewrite cupA. repeat apply leq_cupx. 
     rewrite dotA, (dotA_lm v (w`) v (w`)), lem_2_1_1_2. now ra. 
       exact E. 
     rewrite dotA, dotA_lm, (leq_xt (w`*w)). rewrite <- H1. now ra. 
     rewrite dotA, dotA_lm, (leq_xt (v`*v)). rewrite <- H2. now ra. 
     rewrite dotA, (dotA_lm w (v`) w (v`)), lem_2_1_1_2. now ra. 
       rewrite capC. auto. 
Qed.



(** some auxiliary facts about vectors*)

Lemma aux_result1_theo_3_1 `{laws} `{BDL+STR+CNV<<l} n m (v w : X n m)(R : X n n): 
vector v /\ vector w /\ v ^ w == 0 /\ R*v <== w /\ R*w <== v -> 
R ^ (v*v`) == 0 .
Proof. intro E. firstorder. 
  rewrite <- leq_xb_iff. rewrite capC, capxdot, cnv_invol, H4, H3, dot0x. now ra.
Qed.

Lemma aux_result2_theo_3_1 `{laws} `{BDL+STR+CNV<<l} n m (v w : X n m)(R : X n n): 
vector v /\ vector w /\ v ^ w == 0 /\ R*v <== w /\ R*w <== v -> 
R ^ (w*w`) == 0.
Proof. intro E. firstorder. 
rewrite <- leq_xb_iff. rewrite capC, capxdot, cnv_invol, H5, capC, H3, dot0x. now ra.
Qed.



(** proof of Theorem 3.1 of Section 3 *) 

Lemma theo_3_1 `{laws} `{BDL+STR+CNV<<l} n m (v w : X n m)(R : X n n): 
vector v /\ vector w /\ v ^ w == 0 -> 
(R <== v*w` + w*v` <-> R*v <== w /\ R*w <== v /\ R <== (v + w)*(v + w)`).
Proof. intro E. edestruct E. destruct H2. unfold vector in H1, H2. 
  split. 
    intro H4. repeat split.
      rewrite H4, dotplsx. rewrite <- dotA. rewrite lem_2_1_1_2, dotx0, cupbx. 
      rewrite <- dotA. rewrite (leq_xt (v`*v)). rewrite <- H2. now ra. 
        exact E. 
      rewrite H4, dotplsx. rewrite <- dotA. rewrite <- dotA. rewrite dotA, lem_2_1_1_1, dotx0, cupxb. 
      rewrite <- dotA. rewrite (leq_xt (w`*w)). rewrite <- H1. now ra. 
        exact E. 
      rewrite dotplsx, cnvpls. repeat rewrite dotxpls. rewrite H4. now ra. 
    intro F. destruct F as [F1 [F2 F3]]. 
      rewrite dotplsx, cnvpls in F3. repeat rewrite dotxpls in F3. rewrite <- cupA_llr in F3. 
      rewrite cupC in F3. repeat rewrite cupA in F3. 
      rewrite leq_iff_cap in F3. repeat rewrite capcup in F3.
    rewrite leq_iff_cap, capcup.
      assert (F4 := aux_result1_theo_3_1). 
      assert (F5 := F4 n m v w R).
      rewrite F5 in F3.
      assert (F6 := aux_result2_theo_3_1). 
      assert (F7 := F6 n m v w R).
      rewrite F7 in F3. repeat rewrite cupbx in F3. 
    exact F3. 
    eauto. 
    eauto. 
Qed.



(** proof of Theorem 3.2 of Section 3 and an outsourced auxiliary fact *)

Lemma aux_result_theo_3_2 `{laws} `{BDL+STR+CNV<<l} n m (v w : X n m): 
vector v /\ vector w /\ v ^ w == 0 -> (v*w`) ^ 1 <== 0.
Proof. intro E. firstorder. 
  rewrite capdotx, dotx1. rewrite <- cnvcap. rewrite capC, H3. now ra. 
Qed. 

Lemma theo_3_2 `{laws} `{BDL+STR+CNV<<l} n m (R : X n n): 
(exists (v w : X n m), bipartition R v w) -> (R* (R*R)^*) ^ 1 <== 0.
Proof. intro E. destruct E as [v E1]. destruct E1 as [w E2]. firstorder. 
    assert (R*R <== (v*w` + w*v`)*(v*w` + w*v`)). 
    apply (dot_leq_ext H4). 
  rewrite H5, lem_2_1_3, str_itr. 
    assert (F := aux_star_trans).
  rewrite <- (F n (v*v` + w*w`)).  
  rewrite (dotxpls 1 (v*v` + w*w`) R), dotx1, dotxpls. repeat rewrite dotA. 
    assert (R*v <== w). apply theo_3_1. 
    repeat split. exact H2. exact H1. rewrite capC. exact H3. rewrite cupC. exact H4.
    assert (R*w <== v). apply theo_3_1. 
    repeat split. exact H1. exact H2. exact H3. exact H4. 
  rewrite H6, H7, H4, cupA_lm, cupI, cupC, cupA, cupI, capC, capcup. 
    assert (1 ^ (v*w`) <== 0). 
    rewrite capC. apply aux_result_theo_3_2. 
    repeat split. exact H1. exact H2. exact H3.
  apply cup_spec. split. exact H8. 
  rewrite capC. apply aux_result_theo_3_2. 
    repeat split. exact H2. exact H1. rewrite capC. exact H3. 
  apply lem_2_1_2. eauto. eauto. 
Qed.  



(** proofs of the theorems and lemmata of Section 4 and some outsourced auxiliary facts *)

Theorem theo_4_1 `{laws} `{BDL+STR+CNV<<l} n m (v w : X n m)(R : X n n): 
vector v /\ vector w -> 
(R <== v*w` + w*v` <-> R + R` <== v*w` + w*v`).
Proof. intro E. split. 
  intro F. apply cup_spec. split. 
    apply F. 
    apply cnv_leq_iff'. rewrite cnvpls. repeat rewrite cnvdot, cnv_invol. rewrite cupC. exact F. 
  intro F. apply cup_spec in F. apply F.
Qed.

Lemma aux_result1_lem_4_1 `{laws} `{BDL+STR+CNV<<l} n m (R : X n n): 
symmetric (R^*) -> 
(forall U : X n m, (R*R)^**U <== R^*`*U).
Proof. intro E. intro U. 
  rewrite (leq_xcup ((R*R)^*) (R*(R*R)^*)), aux_lemma_str. unfold symmetric in E. rewrite <- E. now ra. 
  eauto. 
Qed.

Lemma aux_result2_lem_4_1 `{laws} `{BDL+STR+CNV<<l} n m (R : X n n): 
(forall U : X n m, (R*(R*R)^**U) ^ U == 0 -> ((R*(R*R)^*)`*U) ^ ((R*R)^**U) == 0).
Proof. intro U. intro F. 
  apply leq_xb_iff. rewrite capdotx, cnv_invol, dotA, dotA_lm, str_trans, capC, F. now ra.  
Qed.

Lemma aux_result3_lem_4_1 `{laws} `{BDL+STR+CNV<<l} n m (R : X n n): 
symmetric (R^*) -> 
(forall U : X n m, (R*(R*R)^**U) ^ U == 0 -> (R*R)^* *U <== ((R*R)^*)`*U).
Proof. intro E. intro U. intro F. 
  apply leq_iff_cap. rewrite <- cupxb. 
    assert (((R*(R*R)^*)`*U) ^ ((R*R)^**U) == 0). 
    apply aux_result2_lem_4_1. exact F. 
  rewrite <- H1. 
    assert (((R*(R*R)^*)`*U) ^ ((R*R)^* *U) == ((R*R)^* *U) ^ ((R*(R*R)^*)` *U)). 
    apply capC. 
  rewrite H2. rewrite <- capcup. rewrite <- dotplsx. rewrite <- cnvpls. rewrite aux_lemma_str.  
    assert ((R*R)^**U <== R^*`*U). 
    apply aux_result1_lem_4_1. exact E. 
  apply leq_iff_cap, aux_result1_lem_4_1. exact E. 
Qed.

Lemma lem_4_1 `{laws} `{BDL+STR+CNV<<l} n m (R : X n n): 
symmetric (R^*) -> 
(forall U : X n m, (R*(R*R)^**U) ^ U == 0 -> ((R*R)^**U) ^ (R*(R*R)^**U) == 0).
Proof. intro E. intro U. intro F. 
  apply leq_xb_iff. 
    assert (((R*R)^*)`*((R*(R*R)^* *U) ^ U) == 0). 
    rewrite F. now ra. 
  rewrite <- H1. 
    assert ((R*R)^* *(R*R)^* == (R*R)^*). 
    apply str_trans. 
    assert (((R*R)^*)`*((R*(R*R)^* *U) ^ U) == ((R*R)^*)`*((R*((R*R)^* *(R*R)^*)*U) ^ U)). 
    rewrite H2. now ra.  
  rewrite H3. 
    assert (R*(R*R)^* == (R*R)^* *R). 
    apply str_dot. 
    assert (((R*R)^*)`*((R*(R*R)^* *(R*R)^* *U) ^ U) == ((R*R)^*)`*(((R*R)^* *R*(R*R)^* *U) ^ U)).   
    rewrite H4. now ra. 
  rewrite <- dotA_lm. rewrite H5, (capC ((R*R)^* *R*(R*R)^* *U) U).
    assert (H6 := capdotx (((R*R)^*)`) U (R*(R*R)^* *U)). 
    rewrite cnv_invol, dotA in H6. rewrite dotA_lm, aux_result3_lem_4_1. 
  rewrite <- H6. now ra.  
  exact E. 
  exact F.   
Qed.

Lemma aux_result_theo_4_2 `{laws} `{BDL+STR+CNV<<l} n m (u v w : X n m)(R : X n n): 
symmetric (R^*) -> 
(vector u /\ (R*(R*R)^**u) ^ u == 0 /\ R <== R^**u*u`*R^* /\ v == (R*R)^* *u /\ w == R*v
-> vector v /\ vector w /\ v ^ w == 0).
Proof. intros E F. destruct F as [F1 [F2 [F3 [F4 F5]]]]. unfold vector in F1. 
    assert (vector v). 
    unfold vector. rewrite F4. rewrite <- dotA. rewrite <- F1. now ra. 
  repeat split. 
    exact H1. 
    unfold vector. rewrite F5. 
    unfold vector in H1. rewrite <- dotA. rewrite <- H1. now ra. 
    rewrite F5, F4. 
      assert (forall U : X n m, (R*(R*R)^* *U) ^ U == 0 -> ((R*R) ^* *U) ^ (R*(R*R)^* *U) == 0). 
      apply lem_4_1. 
        exact E. 
  rewrite dotA. apply H2. exact F2. 
Qed.

Theorem theo_4_2 `{laws} `{BDL+STR+CNV<<l} n m(u v w : X n m)(R : X n n): 
symmetric (R^*) -> 
( vector u /\ (R*(R*R)^**u) ^ u == 0 /\ R <== R^**u*u`*R^* /\ v == (R*R)^* *u /\ w == R*v
-> bipartition R v w).
Proof. intros E F. 
  unfold bipartition. 
  assert (vector v /\ vector w /\ v ^ w == 0).
    assert (H1 := aux_result_theo_4_2). 
    apply H1 with (u:=u)(R:=R). 
      exact E. 
      exact F. 
  destruct F as [F1 [F2 [F3 [F4 F5]]]]. 
  firstorder. 
  apply theo_3_1. eauto. 
  repeat split.  
    rewrite F5. now ra. 
    rewrite F5, F4. repeat rewrite dotA. rewrite <- itr_str_l. rewrite itr_leq_str. now ra. 
      assert (v + w == R^* *u). 
      rewrite F5, F4, dotA. rewrite <- dotplsx. rewrite aux_lemma_str. now ra. 
  rewrite H4, cnvdot. unfold symmetric in E. rewrite <- E. rewrite dotA. exact F3. 
Qed. 

Corollary cor_4_1 `{laws} `{BDL+STR+CNV<<l} n (u v w p : X n n)(R : X n n): 
R^* == top /\ (R*(R*R)^*) ^ 1 == 0 /\ point p -> 
(v == (R*R)^**p /\ w == R*v -> 
bipartition R v w /\ v + w == top). 
Proof. intro E. destruct E as [E1 [E2 E3]]. intro F. destruct F as [F1 F2]. 
  split.
    assert (H1 := theo_4_2). 
    apply H1 with (u:=p). 
    unfold symmetric. rewrite E1. now ra. 
  repeat split. 
    unfold point in E3. destruct E3 as [E5 [E6 E7]]. 
    exact E5. 
    rewrite <- (dot1x p). rewrite dotA, dotx1. rewrite <- point_cap. rewrite E2. now ra. 
    exact E3. 
    unfold point in E3. transitivity (top' n n). now ra. 
    rewrite E1. destruct E3 as [E5 [E6 E7]]. rewrite <- E7. rewrite <- dotA. 
    rewrite <- (cnv_invol (top' n n)). rewrite <- (cnvdot ((top' n n)`) p ). 
    rewrite cnvtop. rewrite <- E7. rewrite cnvtop, toptop_hom. now ra. 
    exact F1. 
    exact F2. 
    rewrite F2, F1. rewrite dotA. rewrite <- dotplsx. rewrite aux_lemma_str, E1. 
    unfold point in E3. destruct E3 as [E4 [E5 E6]]. 
    rewrite <- E6. now ra. 
Qed. 



(** As mentioned in the presented paper, in the following we assume the relation-algebraic version 
of the axiom of choice to be true. Therefor, we define the following proposition and assume it to 
be true in the next lemma and theorem *)

Definition axiom_of_choice `{laws} : Prop := 
forall n m, forall R : X n m, exists F : X n m, 
univalent F /\ F <== R /\ forall p, F*top' m p  == R*top' m p.



(** As in the proof in presented paper we skip the proof of the fact 
that a homogeneous relation R such that R^* is symmetric has a splitting. 
Therefor we define the following proposition and assume it to be true in the Lemma 4.2 *)

Definition existing_splitting `{laws} : Prop := 
forall n, forall R : X n n, symmetric (R^*) -> exists m, exists S : X n m, splitting S (R^*).

Lemma lem_4_2 `{laws} `{BDL+STR+CNV<<l} n (R : X n n): 
axiom_of_choice /\ existing_splitting -> 
(symmetric (R^*) -> exists m, exists S : X n m, splitting S (R^*) /\ exists F : X m n, F <== S` /\ mapping F).
Proof. intro E. destruct E as [E1 E2]. intro E. unfold existing_splitting in E2. 
  assert (exists m : ob X, exists S : X n m, splitting S (R ^*)).
  apply E2. exact E. 
  destruct H1 as [m E']. destruct E' as [S G]. 
  exists m, S. 
  split. 
    exact G. 
    unfold axiom_of_choice in E1. 
      assert (exists F : X m n, univalent F /\ F <== S` /\ (forall p : ob X, F * top' n p == S` * top' n p)). 
      apply E1. 
    destruct H1 as [F H2]. 
    exists F. destruct H2 as [H3 [H4 H5]]. 
    split. 
      exact H4. 
      unfold mapping. split. 
        exact H3. 
        unfold splitting in G. destruct G as [G1 [G2 G3]]. 
        unfold total. intro p. rewrite H5. 
          assert (total (S`)). apply total_equiv. rewrite <- G3. now ra. 
        apply H1.  
Qed. 

Theorem theo_4_4 `{laws} `{BDL+STR+CNV<<l} n m (R : X n n)(S : X n m)(F : X m n): 
axiom_of_choice -> 
(symmetric (R^*) /\ (R*(R*R)^*) ^ 1 == 0 /\ R * (R * R) ^* + (R * R) ^* == R ^* /\ 
splitting S (R^*) /\ F <== S` /\ mapping F -> 
vector (F`*top' m m) /\ (R*(R*R)^* *(F`*top' m m)) ^ (F`*top' m m) == 0 /\ 
R <== R^* *(F`*top' m m)*(F`*top' m m)`*R^*).
Proof. intro Ha. intro E. destruct E as [E1 [E2 [E3 [E4 [E5 E6]]]]]. 
  unfold splitting in E4. destruct E4 as [E7 [E8 E9]]. 
  unfold mapping in E6. destruct E6 as [E6' E6'']. 
    assert (vector (F `*top' m m)). 
    unfold vector. rewrite <- dotA. rewrite toptop_hom. now ra. 
  repeat split. 
    exact H1. 
      assert (F*R*(R*R)^* *F` <== F*F`). 
      assert (R*(R*R)^* <== R^*). 
      rewrite <- E3. now ra. 
      rewrite dotA_lm. rewrite H2. rewrite <- E8. 
      assert (F*(S*S`)*F` <== S`*(S*S`)*F`). 
      assert (H4 := dot_leq_r).
      repeat rewrite <- dotA_rrm. rewrite <- (H4 m n m F (S`) ((S*S`)*F`)). 
        now ra. 
        exact E5. 
    rewrite H3. 
      assert (S`*(S*S`)*F` <== S`*(S*S`)*S). 
      assert (H5 := dot_leq_l).
      repeat rewrite dotA. rewrite dotA_lm, dotA_lm. rewrite (H5 m n m (S`*(S*S`))(F`) S). 
        now ra. 
        apply cnv_leq_iff'. exact E5. 
    rewrite H4. rewrite <- dotA_rm. rewrite E9. 
    unfold univalent in E6'. rewrite <- total_equiv in E6''. rewrite dot1x. exact E6''. 
    rewrite capC. apply leq_xb_iff. 
    transitivity (F`*((top' m m) ^ (F*(R*(R*R)^* *(F`*top' m m))))). rewrite capdotx. now ra. 
    rewrite captx. 
      assert (F*(R*(R*R)^* *F`) == (F*(R*(R*R)^* *F`)) ^ (F*F`)). 
      symmetry. rewrite <- leq_iff_cap. 
        rewrite dotA_lm in H2. rewrite <- dotA_rrm in H2.  rewrite H2. now ra. 
        repeat rewrite dotA. repeat rewrite dotA in H3. rewrite dotA6, H3. 
          assert ((F*R*(R*R)^* *F`) ^ (F*F`) == F*((R*(R*R)^*) ^ 1)*F `). 
          rewrite univalent_cap, dotx1, univalent_cap_cnv. 
            now ra. 
            exact E6'. 
            exact E6'. 
    rewrite H4, dotA, E2 . now ra. 
    transitivity (R^*). now ka. 
    transitivity (S*1*S`). rewrite dotx1, E8. now ra. 
    transitivity (S*(F*F`)*S`). rewrite <- total_equiv in E6''. rewrite E6''. now ra. 
    rewrite <- (dot1x (S`)).
    transitivity (S*(F*F`)*(F*F`)*S`). rewrite <- total_equiv in E6''. rewrite E6''. now ra. 
    transitivity (S*(S`*F`)*(F*S)*S`). assert (H3 := dot_leq_r). rewrite dotA, (H3 m n m F (S`) (F`)). 
      assert (H5 := dot_leq_l). rewrite dotA5, (H5 m n m F (F`) S). 
        now ra. 
        apply cnv_leq_iff'. exact E5. 
        exact E5. 
    repeat rewrite dotA. rewrite E8. rewrite <- dotA. rewrite E8. 
      assert (F`*F <== F`*top*F). 
      rewrite <- dotA. apply dot_leq_l, dottx. 
    rewrite dotA_lm. repeat rewrite dotA. rewrite <- toptop_hom in H2. rewrite dotA_lm, H2. now ra.
Qed.

End Bipartitions.

























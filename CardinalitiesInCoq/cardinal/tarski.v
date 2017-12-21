Require Export RelationAlgebra.relalg RelationAlgebra.lset RelationAlgebra.sums.
Require Export misc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Notation empty' n := (one n <== 0).

Class tarski (X: ops) := Tarski: forall n m (x: X n m), ~(x <== 0) <-> is_nonempty x.
Class decidable (X: ops) := leq_dec: forall n m (x y: X n m), x<==y \/ ~(x<==y).

Section s.
 Context {l} {X} {L:laws l X} {T: tarski X} {D: decidable X}.

 Lemma not_nonempty `{BOT<<l} {n m} {x: X n m} {Hx: is_nonempty x}: ~(x==0).
 Proof. apply Tarski in Hx. now rewrite <-leq_xb_iff. Qed.
 
 Lemma leq_point_vect'' {Hl: AL+TOP<<l} {n m} {p v: X n m} {Hp: is_point p} {Hv: is_vector v}:
   v <== p -> v == p \/ v <== 0.
 Proof.
   intros Hvp. destruct (leq_dec v 0) as [|Hv0]. tauto.
   left. rewrite Tarski in Hv0. now apply point_lattice_atom.
 Qed.

 Lemma leq_point_vect {Hl: AL+TOP<<l} {n m} {p v: X n m} {Hp: is_point p} {Hv: is_vector v}:
   p <== v \/ p \cap v <== 0.   
 Proof. rewrite leq_iff_cap. apply leq_point_vect''. lattice. Qed.

 Lemma leq_point_vect' {Hl: BL+CNV<<l} {n m} {p v: X n m} {Hp: is_point p} {Hv: is_vector v}:
   p <== v \/ p <== !v.
 Proof. rewrite <-leq_cap_neg'. apply leq_point_vect. Qed.

 Lemma points_eq_or_disjoint {Hl: AL+TOP<<l} n m (p q: X n m):
   is_point p -> is_point q -> p == q \/ p \cap q <== 0. 
 Proof.
   intros. 
   case (leq_point_vect (p:=p) (v:=q)); intro. 
    case (leq_point_vect (p:=q) (v:=p)); intro. 
     left. now apply antisym.
     right. now rewrite capC. 
    tauto.
 Qed.

 Lemma leq_pv {Hl: BL+CNV<<l} {n m} {p v: X n m} {Hp: is_point p} {Hv: is_vector v}: p <== v <-> ~ (p <== !v).
 Proof.
   split. intros H H'. elim (not_nonempty (x:=p)).
   apply leq_xb_iff. rewrite <-capI. rewrite H at 1. now rewrite H', capneg. 
   intro N. pose proof leq_point_vect'. tauto. 
 Qed.
 

 Lemma leq_atom_x'' {Hl: AL+TOP<<l} {n m} {a x: X n m} {Ha: is_atom a}:
   x <== a -> x == a \/ x <== 0.
 Proof.
   intros ?. destruct (leq_dec x 0) as [|Hx0]. tauto.
   left. rewrite Tarski in Hx0. now apply atom_lattice_atom.
 Qed.

 Lemma leq_atom_x {Hl: AL+TOP<<l} {n m} {a x: X n m} {Ha: is_atom a}:
   a <== x \/ a \cap x <== 0.   
 Proof. rewrite leq_iff_cap. apply leq_atom_x''. lattice. Qed.

 Lemma leq_atom_x' {Hl: BL+CNV<<l} {n m} {a x: X n m} {Ha: is_atom a}:
   a <== x \/ a <== !x.
 Proof. rewrite <-leq_cap_neg'. apply leq_atom_x. Qed.

 Lemma atoms_eq_or_disjoint {Hl: AL+TOP<<l} n m (a b: X n m):
   is_atom a -> is_atom b -> a == b \/ a \cap b <== 0. 
 Proof.
   intros. 
   case (leq_atom_x (a:=a) (x:=b)); intro. 
    case (leq_atom_x (a:=b) (x:=a)); intro. 
     left. now apply antisym.
     right. now rewrite capC. 
    tauto.
 Qed.
 
End s.

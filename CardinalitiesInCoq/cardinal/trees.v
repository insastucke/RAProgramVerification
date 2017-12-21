Require Import RelationAlgebra.relalg.
Require Import cardinal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section s.

Context `{L: laws} `{Hl: BL+CNV+STR<<l} {U: united X} {C: cardinal U} {T: tarski X} {P: pointed X}. 

Class is_forest n (x: X n n) := {
  unique_parents:> is_injective x;
  acyclic:> is_irreflexive (x^+) }.

Class is_tree n (x: X n n) (r: X n unit):= {
  tree_forest:> is_forest x;
  root_is_point:> is_point r;
  root_reaches_all_vertices: r*top <== x^* }.

Lemma no_parent_to_root n (x: X n n) (r: X n unit): is_tree x r -> x*r == 0. 
Proof. 
  intro Ht. apply leq_xb_iff. destruct (leqb_spec (x*r) 0) as [|E]. assumption. exfalso.
  apply pointic in E as [q [Hq Hq']]. 2: tc. 
  apply (not_nonempty (x:=r)).
  assert (H: r*r` <== !1).
   rewrite <-(dotx1 r) at 1. rewrite surjective.
   rewrite leq_xyp in Hq'. mrewrite Hq'.
   rewrite (leq_xt (q`)). rewrite root_reaches_all_vertices.
   rewrite <-itr_str_r. apply leq_cap_neg'. now rewrite acyclic.
  rewrite <-leq_xb_iff. apply neg_leq_iff. rewrite negbot. rewrite <-(surjective_tx (x:=r)).
  rewrite Schroeder_r, negneg. rewrite negtop.
  rewrite <-(capneg 1). rewrite <-H. rewrite <-(injective (x:=r)). lattice.
Qed.

Lemma only_root_without_parent n {x: X n n} {r p: X n unit}
  {Hxr: is_tree x r} {Hp: is_point p}:
  x * p <== 0 -> p == r.
Proof.
  intro Hxp. symmetry. apply surjective_injective_antisym.
  transitivity (x^* * p). rewrite leq_xyp. rewrite <-root_reaches_all_vertices. ra. 
  rewrite str_unfold_r. ra_normalise. mrewrite Hxp. ra. 
Qed.

Lemma card_parents_proper_node n (x: X n n) (r p: X n unit):
  is_tree x r -> is_point p -> p ^ r <== 0 ->
  card (x * p) = 1%nat.
Proof.
  intros Hxr Hp Hpr. eapply @card_point. tc. tc.  split. tc.
  unfold is_injective. ra_normalise. mrewrite (injective (x:=p)). ra_normalise. apply injective.
  rewrite <-Tarski. intro E. eapply only_root_without_parent in E; eauto.
  elim (not_nonempty (x:=p)). rewrite <-leq_xb_iff, <-Hpr, E. lattice.
Qed.

Lemma split_points n m (r: X n m) {Hr: is_point r}:
  exists x l l', r==x /\ points n m = l++x::l'.
Proof.
  apply all_points in Hr as [r' [Hr E]].
  apply In_split in Hr as [h [k ->]].
  repeat eexists; eauto.
Qed.

Theorem card_tree n (x: X n n) (r: X n unit): is_tree x r -> card x = card' n -1.
Proof. 
  intro Ht. rewrite card_points_sum.
  destruct split_points as (r'&h&k&Hr&Hhk). 
  rewrite Hhk. rewrite natsum_appC. simpl.
  rewrite <-Hr. rewrite no_parent_to_root, card0 by assumption.
  rewrite <-(length_natsum (n:=1)). rewrite card'_length, Hhk.
  rewrite 2app_length. simpl. lia.
  intros p Hp. apply card_parents_proper_node with r. assumption.
  apply points_points. rewrite Hhk. rewrite in_app_iff in *. simpl. tauto.
  destruct (disjoint_spec (disjoint_points n unit) (x:=p) (y:=r')).
  rewrite Hhk. rewrite in_app_iff in *. simpl. tauto.
  rewrite Hhk. rewrite in_app_iff in *. simpl. tauto.
  subst. elim (not_nonempty (x:=r)). 
  pose proof (disjoint_points n unit) as E.
  rewrite Hhk in E. apply disjoint_app in E as [E _].
  apply E in Hp. rewrite capI, <-Hr in Hp. now apply leq_xb_iff. 
  now rewrite Hr. 
Qed. 

Lemma card_edge n (e a: X n n): is_irreflexive e -> is_atom a -> e==a\cup a` -> card e = 2.
Proof.
  intros He Ha E.
  destruct (atoms_eq_or_disjoint (a:=a) (b:=a`)) as [|H]; try tc.
   elim (not_nonempty (x:=a)). apply leq_xb_iff.
   rewrite cnv_ext. rewrite <-H.
   pose proof irreflexive as I. rewrite E, <-H, cupI in I.
   apply leq_xb_iff in I. 
   rewrite <-(injective (x:=a)), <-H in I.
   rewrite <-(relalg.transitive (x:=a)) in I at 1. rewrite capI in I.
   rewrite I. ra.
  rewrite leq_xb_iff in H. 
  rewrite E, cardcup', H. now rewrite 2card_atom, card0.  
Qed.

End s.

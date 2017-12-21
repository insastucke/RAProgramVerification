Require Import RelationAlgebra.relalg.
Require Import cardinal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section s.

Context `{L: laws} {Hl: BL+CNV<<l} {U: united X} {C: cardinal U} {T: tarski X} {P: pointed X}. 

Section Wei.

Variables n: ob X.
Variable R: X n n. 
Variable k: nat.

(* preconditions are assumed as hypotheses as they concern variables
   that are never assigned *)
Hypothesis R_irreflexive: is_irreflexive R.
Hypothesis R_symmetric: is_symmetric R.
Hypothesis R_maxdeg: forall p: X n unit, is_point p -> card (R*p) <== k.

Notation independent v := (R*v <== !v).

Definition inv (s v: X n unit) := independent s /\ R*s \cup s == v.

Definition post (s: X n unit):= 
  independent s /\ forall t: X n unit, independent t -> card t <== ((k+1) * card s)%nat.


(* the invariant is established. *)

Lemma establish_inv: inv 0 0. 
Proof. split; ra. Qed.

(* maintenance of the invariant. *)

Lemma  maintain_inv s v p:
  inv s v -> ~(v == top) -> is_point p -> p <== !v 
  -> inv (s \cup p) (v \cup p \cup (R*p)). 
Proof. 
  intros [Hs Hv] _ Hp Hpv. split. 
  rewrite dotxpls, negcup. apply cup_spec. split. 
  apply cap_spec. split. assumption.
  apply neg_leq_iff' in Hpv. rewrite <-Hpv, <-Hv. lattice.
  apply cap_spec. split. 
  apply Schroeder_l. rewrite negneg. rewrite symmetric. 
  apply neg_leq_iff' in Hpv. rewrite <-Hpv, <-Hv. lattice.
  apply Schroeder_r. rewrite irreflexive'. rewrite 2negneg. apply injective. 
  rewrite <- Hv. ra. 
Qed.

(* consquences of the invariant at loop exit *)

Lemma  entails_inv s: inv s top -> post s. 
Proof. 
  intros [Hs Hv]. split. assumption. 
  intros t Ht. transitivity (card (top' n unit)). apply card_bound. 
  rewrite <-Hv. rewrite card_cup_leq.
  rewrite (point_ax' (v:=s)) at 1. 
  rewrite dotxsum. rewrite card_sum.
  rewrite (length_natsum_leq (n:=k)).
  rewrite <-card_vector. simpl. lia. 
  intros i Hps. rewrite R_maxdeg. reflexivity. 
  apply points_points. apply filter_In in Hps. apply Hps. 
Qed.

(* loop variant *)

Lemma loop_variant s v p:
  inv s v -> ~(v == top) -> is_point p -> p <== !v
  -> card v < card (v \cup p \cup (R*p)).
Proof.
  intros _ _ Hp Hpv.
  apply Lt.lt_le_trans with (card (v + p)). 2: apply card_leq; lattice.
  apply card_lt. lattice.
  intro E. elim (not_nonempty (x:=p)).
  apply leq_xb_iff. rewrite <-capI. rewrite Hpv at 1. rewrite <- E.
  rewrite negcup. rewrite <-capA, (capC (!p)), capneg. lattice. 
Qed.

End Wei.

Variable n: ob X.
Variable x: X n n.

Definition independent_number :=
  \max_(v\in filter (fun v => leqb (x*v) (!v)) (relations n unit)) card v.

Definition maximum_degree :=
  \max_(p\in points n unit) card (x*p).

Lemma independent_upper_bound_aux (v: X n unit): x*v <== !v -> card v ^2 <== card (!x).
Proof.
  intros Hxv. rewrite Schroeder_r, negneg in Hxv. rewrite <-Hxv.
  now rewrite card_dotvw.
Qed.
  
Theorem independent_upper_bound: independent_number ^2 <== card (!x).
Proof.
  unfold independent_number. rewrite square_max. 
  apply leq_supx. intros v. rewrite filter_In, leqb_true. intros [Hv Hv'].
  now apply independent_upper_bound_aux.
Qed.

Hypothesis Sx: is_symmetric x.
Hypothesis Ix: is_irreflexive x.

Definition maximal (v: X n unit) :=
  forall w, v <== w -> x * w <== !w -> w <== v. 

Lemma maximal_independent_iff (v: X n unit):
  x*v <== !v -> maximal v <-> x*v == !v.
Proof.
  intro H. split. intro M. apply antisym. assumption.
  neg_switch. apply leq_cap_neg. apply nopoint_empty.
  intros p Pp. rewrite cap_spec. intros [Hp Hp'].
  cut (v\cup p <== v). rewrite cup_spec. intros [_ D].
  rewrite <- D in Hp'. rewrite leq_pv, negneg in Hp'. now elim Hp'.
  apply M. lattice. rewrite dotxpls. rewrite negcup.
  apply neg_leq_iff' in Hp.
  apply cup_spec; split; apply cap_spec; split.
   assumption.
   assumption. 
   rewrite Schroeder_l, negneg, symmetric in Hp. assumption.
   apply Schroeder_r. rewrite negneg. rewrite injective.
   neg_switch. apply irreflexive'. 
  intros M w vw Hw. apply weq_spec in M as [_ H'].
   apply neg_leq_iff in H'. rewrite negneg in H'.
   rewrite <-H'. 
   apply neg_leq_iff in Hw. rewrite negneg in Hw. rewrite Hw.
   now rewrite vw. 
Qed.

Lemma maximum_maximal (v: X n unit):
  x*v <== !v -> card v = independent_number -> maximal v.
Proof.
  intros Hv Hc w VW Hw. 
  rewrite <-from_below_points. intros p Hp Hpw.
  apply leq_pv. intro D. 
  assert (card v < card w).
   apply Lt.lt_le_trans with (card (v \cup p)).
   rewrite cardcup'. apply leq_cap_neg' in D. apply leq_xb_iff in D.
   rewrite capC, D, card0. setoid_rewrite card_point. lia.
   apply card_leq. lattice.
  assert (card w <= independent_number).
   destruct (all_relations w) as (w'&Hw'&Ew). rewrite Ew. rewrite Ew in Hw. 
   apply leq_xsup. apply filter_In. split. assumption. now apply leqb_true.
  lia.
Qed.

Lemma independent_witness: exists v: X n unit, x*v <== !v /\ card v = independent_number.
Proof.
  edestruct max_reach as [E|(v&Hv&E)]. 2: setoid_rewrite <-E.
  set (h := filter _ _) in E.
  destruct (all_relations (zer n unit)) as (z&Hz&Ez).
  assert (In z h). apply filter_In. split. assumption. apply leqb_true.
  rewrite <-Ez. ra. rewrite E in H. now destruct H.
  exists v. split. 2: reflexivity.
  apply filter_In in Hv as [_ Hv]. now apply leqb_true.
Qed.

Lemma maximal_lower_bound (v: X n unit):
  x*v == !v -> card' n <== ((maximum_degree + 1) * card v)%nat.
Proof.
  intros XV.
  rewrite <-(cupneg v). rewrite card_disjoint_cup by now rewrite capneg. 
  rewrite <-XV. rewrite point_ax' at 2. rewrite dotxsum.
  rewrite card_sum. rewrite (length_natsum_leq (n:=maximum_degree)).
  rewrite card_vector. simpl. lia.
  intro p. rewrite filter_In. intros [Hp _].
  apply (leq_xsup (fun p => card (x*p))). assumption. 
Qed.

Theorem independent_lower_bound: card' n <== ((maximum_degree + 1) * independent_number)%nat.
Proof.
  intros. destruct independent_witness as (v&Hv&Hc).
  rewrite <-Hc. apply maximal_lower_bound.
  rewrite <-maximal_independent_iff by assumption.
  now apply maximum_maximal.
Qed.

End s.

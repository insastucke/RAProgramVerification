Require Export tarski points unit natmax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Class cardinal (X: ops) (U: united X) := {
 card: forall n m, X n m -> nat;
 card0: forall n m, @card n m 0 = O;
 card1: @card unit unit 1 = 1%nat;
 cardcnv: forall n m (x: X n m), card (x`) = card x;
 cardcup: forall n m (x y: X n m), (card (x \cup y) + card (x \cap y) = card x + card y)%nat;
 cardded: forall {n m p} {x: X n m} {y: X m p} {z: X n p} {Hx: is_injective x},
     card (z \cap (x*y)) <== card (x` * z\cap y);
 cardded': forall {n m p} {x: X m n} {y: X m p} {z: X p n} {Hx: is_univalent x},
     card (x \cap (y*z)) <== card (x * z`\cap y);
 card_leq:> forall n m, Proper (leq ==> leq) (@card n m) 
}.

Notation card' n := (card (top' n unit)).

Section s.
 Context {X} {l} {L: laws l X} {T: tarski X} {P: pointed X} {D: decidable X} {U: united X} {C: cardinal U}.

 Global Instance card_weq n m: Proper (weq ==> eq) (@card X U C n m).
 Proof.
   intros x y. rewrite weq_spec. intros [H H'].
   apply card_leq in H. apply card_leq in H'. simpl in *. lia. 
 Qed.
 
 Lemma card0' {Hl: BOT<<l} n m (x: X n m): x <== 0 -> card x = O.
 Proof. rewrite leq_xb_iff. intros ->. apply card0. Qed.

 Lemma cardcup': forall n m (x y: X n m), card (x \cup y) = card x + card y - card (x \cap y).
 Proof. intros. pose proof (cardcup x y). lia. Qed.

 Lemma card_cup_leq n m (x y: X n m): card (x \cup y) <== (card x + card y)%nat.
 Proof. rewrite <-cardcup. simpl. lia. Qed. 
 
 Lemma card_bound {Hl: TOP<<l} n m (x: X n m): card x <== card (top' n m).
 Proof. apply card_leq. lattice. Qed. 

 Lemma card_uniuni {Hl: AL<<l} {n m p} {x: X n m} {y: X m p} {z: X n p}
       {Hx: is_univalent x} {Hy: is_univalent y}:
   card (x*y \cap z) = card (x \cap (z*y`)).
 Proof.
   apply antisym.
   rewrite <-cardcnv, cnvcap, cnvdot, capC. rewrite cardded.
   rewrite <-cardcnv. apply card_leq. ra.
   rewrite cardded'. apply card_leq. ra.
 Qed.
 
 Lemma card_unimap {Hl: AL+TOP<<l} {n m p} {x: X n m} {y: X m p}
       {Hx: is_univalent x} {Hy: is_mapping y}:
   card (x*y) = card x.
 Proof.
   rewrite <-capxt. rewrite card_uniuni.
   rewrite surjective_tx. apply card_weq. ra.
 Qed.
 
 Lemma card_point {Hl: AL+TOP<<l} {n} {x: X n unit} {Hx: is_point x}: card x = 1%nat.
 Proof.
   rewrite <-cardcnv, <-dot1x. rewrite card_unimap. apply card1.
 Qed.

 Lemma card_atom {Hl: AL+TOP<<l} {n m} {a: X n m} {Ha: is_atom a}: card a = 1%nat.
 Proof.
   assert (is_point (a*top' _ unit)).
    rewrite <- top_nnm, dotA.
    apply gen_point. tc. apply point_a_top.    
   rewrite <-card_unimap. apply card_point.
 Qed.
 
 Lemma card_sum I J n m (f: I -> X n m):
   card (sup f J) <== natsum J (fun i => card (f i)). 
 Proof.
   induction J; simpl (sup _ _). now rewrite card0.
   rewrite cardcup'. rewrite IHJ. simpl. lia.
 Qed.
 
 Lemma card_disjoint_cup {Hl: BOT<<l} n m (x y: X n m):
   x \cap y <== 0 -> card (x + y) = (card x + card y)%nat.
 Proof. intro E. rewrite <-cardcup, (card0' (x:=_^_)). lia. assumption. Qed.

 Lemma card_disjoint_sum {Hl: DL+BOT<<l} I J n m (f: I -> X n m):
   disjoint (map f J) -> 
   card (sup f J) = natsum J (fun i => card (f i)). 
 Proof.
   induction J; simpl. intro. apply card0.
   intros [Ha H']. rewrite card_disjoint_cup.
   rewrite IHJ by assumption. lia.
   rewrite capxsup. apply leq_supx. intros b Hb. apply Ha.
   now apply in_map. 
 Qed.

 Lemma card1_atom {Hl: BL+CNV<<l} {n m} {a: X n m}: card a = 1%nat -> is_atom a.
 Proof.
   intro Ha. rewrite atom_ax' in Ha. rewrite card_disjoint_sum in Ha.
   2: rewrite map_id; apply listP_filter; apply disjoint_atoms.
   rewrite <-(length_natsum (n:=1)) in Ha.
   2: now intro; rewrite filter_In; intros [H _]; apply atoms_atoms in H; apply card_atom.
   rewrite atom_ax'. remember (filter _ _) as h.
   destruct h as [|b [|? ?]]; try discriminate.
   simpl. rewrite cupxb. apply atoms_atoms.
   assert (H: In b [b]) by now left. rewrite Heqh in H.
   rewrite filter_In in H. tauto.
 Qed.
   
 Lemma card_vector {Hl: BDL+CNV<<l} n (v: X n unit):
   card v = length (filter (fun p => leqb p v) (points n unit)).
 Proof.
   rewrite point_ax'. rewrite card_disjoint_sum.
   symmetry. rewrite <- (Mult.mult_1_l (length _)). apply length_natsum. 
   intros. apply filter_In in H as [H _]. apply points_points in H. apply card_point.
   rewrite map_id. apply listP_filter, disjoint_points.
 Qed.

 Lemma card_dotvw {Hl: BL+CNV<<l} n m (v: X n unit) (w: X m unit):
   card (v*w`) = (card v * card w)%nat.
 Proof.
   rewrite (point_ax' (v:=w)) at 1.
   rewrite cnvsum, dotxsum.
   rewrite card_disjoint_sum.
   rewrite (card_vector w).            
   symmetry. apply length_natsum.
   intros p Hp. apply filter_In in Hp as [Hp _]. apply points_points in Hp. apply card_unimap. 
   apply listP_map_filter. apply disjoint_points'.
 Qed.
   
 Lemma card_domran {Hl: BL+CNV<<l} n m p (x: X n m) (y: X m p):
   card (x*y) <== (card (dom x) * card (ran y))%nat. 
 Proof.
   rewrite (dotxt x) at 1. rewrite <-top_n1m.
   transitivity (card (x*top*(y`*top' m unit)`)). apply card_leq. ra.
   now rewrite card_dotvw.
 Qed.

 Lemma card_top {Hl: BL+CNV<<l} n m: card (top' n m) = (card' n * card' m)%nat.
 Proof.
   rewrite <-card_dotvw.
   now rewrite <-top_n1m, cnvtop.
 Qed.
 
 Lemma card_one {Hl: BL+CNV<<l} n: card (one n) = card' n.
 Proof.
   rewrite point_id, point_ax. 2: left; tc.
   rewrite 2card_disjoint_sum. apply natsum_weq. 
   intros p Hp. apply points_points in Hp. apply card_unimap. 
   rewrite map_id. apply disjoint_points.
   eapply listP_map. 2: apply disjoint_points.
   simpl. intros p q Hp Hq H. apply points_points in Hp. apply points_points in Hq.
   (* TODO: below, there could be a simpler proof *)
   rewrite leq_cap_neg'.
   rewrite Schroeder_r, negneg, cnv_invol.
   rewrite disjoint_vect_iff in H by tc.
   mrewrite H. ra.
 Qed.

 Lemma card0_eq0 {Hl: BL+CNV<<l} n m (x : X n m) : card x = 0%nat -> x == 0.
 Proof.
   rewrite atom_ax'. remember (filter _ _) as h. 
   destruct h as [|a h]. reflexivity.
   rewrite card_disjoint_sum. simpl.
   assert (is_atom a). apply atoms_atoms.
   assert (E: In a (a::h)) by now left. rewrite Heqh, filter_In in E. tauto.
   rewrite card_atom. lia.
   rewrite map_id, Heqh. apply listP_filter, disjoint_atoms.
 Qed. 

 Lemma card0_iff {Hl: BL+CNV<<l} n m (x : X n m) : card x = 0%nat <-> x == 0.
 Proof.
   split. apply card0_eq0. rewrite <-leq_xb_iff. apply card0'. 
 Qed. 

 Lemma card_lt {Hl: BL+CNV<<l} n m (x y: X n m): x<==y -> ~(y<==x) -> card x < card y.
 Proof. 
   intro Hxy. rewrite leq_cap_neg. intro E.
   rewrite <-(capxt y), <-(cupneg x), capcup. rewrite cardcup'.
   rewrite (card0' (x:=_^_^_)). 2: rewrite <-(capneg x); lattice.
   setoid_replace (y ^ x) with x by lattice.
   rewrite leq_xb_iff, <-card0_iff in E. simpl in *. lia.
 Qed.

 Lemma card'_length {Hl: BDL+CNV<<l} n: card' n = length (points n unit).
 Proof.
   rewrite point_ax. rewrite card_disjoint_sum.
   2: rewrite map_id; apply disjoint_points.
   rewrite <-(length_natsum (n:=1)). lia.
   intros. apply card_point.
 Qed.
 
 Lemma card_reflexive {Hl: BL+CNV<<l} n (x: X n n) {Hx: is_reflexive x}: card' n <== card x.
 Proof. rewrite <- card_one. now apply card_leq. Qed.

 Lemma card_points_sum {Hl: BL+CNV<<l} n m (x: X n m): 
   card x = \natsum_(p \in points m unit) card (x*p).
 Proof.
   rewrite point_rel.
   rewrite card_disjoint_sum.
   apply natsum_weq. intros p Hp. apply points_points in Hp.
   now rewrite card_unimap.
   eapply listP_map. 2: apply disjoint_points. simpl.
   intros p q Hp Hq PQ.
   (* TODO: simpler proof *)
   rewrite leq_cap_neg'. rewrite <-dotA, Schroeder_r, negneg.
   ra_normalise.
   rewrite disjoint_vect_iff in PQ. 
   mrewrite PQ. ra. 
 Qed.
 
End s.

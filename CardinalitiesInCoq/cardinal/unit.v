Require Export tarski points.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Class united (X: ops) := {
 unit: ob X;
 top_unit: top' unit unit == 1; 
 nonempty_unit:> is_nonempty' unit }.

Section s.
 Context {X} {l} {L: laws l X} {P: pointed X} {T: tarski X} {D: decidable X} {U: united X}.

 Definition dom {n m} (x: X n m): X n unit := x * top' m unit.

 Definition ran {n m} (x: X n m): X m unit := x` * top' n unit.

 Global Instance vector_nunit n (x: X n unit): is_vector x. 
 Proof. unfold is_vector. rewrite top_unit. ra. Qed.

 Global Instance univalent_nunit {Hl: TOP<<l} n (x: X n unit): is_univalent x. 
 Proof. unfold is_univalent. rewrite <-top_unit. lattice. Qed.
 
 Lemma top_n1m {Hl: TOP<<l} n m: top' n unit * top' unit m == top.
 Proof. apply top_nonempty. Qed.

 Global Instance point_oneunit {Hl: TOP+CNV<<l}: is_point (one unit).
 Proof.
   split. tc.
   unfold is_injective. rewrite <-top_unit at 3. lattice.
   tc. 
 Qed.

 Global Instance mapping_top_nunit {Hl: CNV+TOP<<l} {n}: is_mapping (top' n unit).
 Proof. split. tc. ra_normalise. rewrite top_n1m. lattice. Qed.

 Lemma unit_two {Hl: BOT+TOP<<l} (x: X unit unit): x == 0 \/ x == 1.
 Proof.
   destruct (leq_dec x 0) as [|H]. rewrite <-leq_xb_iff. tauto.
   right. rewrite Tarski in H. specialize (H unit unit).
   rewrite leq_tx_iff in H. rewrite top_unit in H.
   rewrite <- H. ra. 
 Qed.
 
 Lemma unit_point {Hl: BOT+TOP+CNV<<l} (p: X unit unit): is_point p -> p == 1.
 Proof.
   intro Hp. case (unit_two p); trivial. intro E.
   now elim (not_nonempty (x:=p)). 
 Qed. 

 Lemma point_rel {Hl: BDL+CNV<<l} n m (x: X n m): x == \sup_(p\in points m unit) x*p*p`.
 Proof.
   rewrite <- dotx1 at 1. rewrite (point_id (m:=unit)).
    rewrite dotxsum. now setoid_rewrite dotA.
   tc.
 Qed. 

End s.

Require Import RelationAlgebra.relalg.
Require Import cardinal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section s.

Context `{L: laws} {Hl: BL+CNV<<l} {U: united X} {C: cardinal U} {T: tarski X} {P: pointed X}. 

Lemma aux {n m} {x: X m n} {p: X m unit} {Hp: is_point p}: p <== x*top <-> ~ (x`*p <== 0).
Proof. rewrite Schroeder_l, cnv_invol, negbot. rewrite neg_leq_iff'. apply leq_pv. Qed.

Hypothesis choice: forall n m (x : X n m),
    exists F : X n m, is_univalent F /\ F <== x /\ F*top' m unit  == x*top' m unit.

Theorem decompose n m (x: X n m) k:
  (exists F: list (X n m),
      length F = k /\
      (forall y, In y F -> is_univalent y) /\
      disjoint F /\
      x == \sup_(y\in F) y)
  <-> forall p: X n unit, is_point p -> card (x`*p) <== k.
Proof. 
  split. intros (F&Hlength&Hunivalent&Hdisjoint&Hx) p Hp. 
  rewrite Hx. rewrite cnvsum, dotsumx, card_sum.
  rewrite (length_natsum_leq (n:=1%nat)). rewrite Hlength. simpl. lia. 
  intros u Hu. rewrite <-captx. apply Hunivalent in Hu. rewrite cardded.
  rewrite <- (card_point (x:=p)). apply card_leq. lattice. 
  
  revert x. induction k; intros x Hx.
  - exists nil; repeat split; simpl. contradiction.   
    cnv_switch; ra_normalise.
    rewrite <- dotx1,point_id,dotxsum by (left;tc). apply sup_b. 
    intros p Hp. apply points_points in Hp. apply Hx in Hp.
    rewrite leq_xb_iff in Hp. apply card0_eq0 in Hp. mrewrite Hp. ra.
  - destruct (choice x) as (F&HFu&HFx&HFx'). clear choice.
    destruct (IHk (x\cap !F)) as (Fs&Hk&HFsu&HFd&HxF); clear IHk.
     intros p Hp. assert (card (x`*p) <== k \/ card (x`*p) = S k) as [CA|CA].
      apply Hx in Hp. simpl in *. lia.
     now rewrite leq_cap_l.
     clear Hx. rewrite cnvcap, dotcapx.
     assert(Hpt: p <== x*top). apply aux. rewrite leq_xb_iff. intro E.
      rewrite E, card0 in CA. discriminate. 
     rewrite <-HFx' in Hpt. apply aux in Hpt.
     assert (aux: forall i j, i < S j -> i <= j) by (intros; lia).
     apply aux. rewrite <-CA. clear aux CA.
     apply card_lt. lattice. rewrite leq_cap_r.
     intro E. apply Hpt. rewrite cnvneg, dot_neg_point in E.
     rewrite neg_leq_iff' in E. rewrite <-HFx in E.
     rewrite <-capI. rewrite E at 2. now rewrite capneg.
    exists (F::Fs). split. simpl. congruence.
    split. clear - HFsu HFu. now firstorder subst.
    split. split. 2: assumption. intros G HG.
    rewrite (capC G). cut (F ^ G <== 0). tauto. 
    transitivity (F ^ (x ^ !F)). rewrite HxF.
    apply cap_leq. reflexivity. eapply leq_xsup'; eauto.
    rewrite capA, capC, capA, (capC (!_)), capneg. lattice.
    simpl. rewrite <-HxF. apply antisym. 2:lattice. rewrite cupcap, cupneg. lattice.
Qed.

End s.

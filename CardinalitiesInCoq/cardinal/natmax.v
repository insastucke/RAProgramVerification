Require Import RelationAlgebra.lattice RelationAlgebra.sups.
Require Import List.
Require Export Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Infix "<=" := le. 
Infix "<" := lt. 

Canonical Structure nat_ops: ops :=
  {|
  car := nat;
  leq := le;
  weq := @eq nat;
  bot := O;
  top := O;
  cap := Min.min;
  cup := Max.max;
  neg := id
  |}.


Instance nat_laws: laws (DL+BOT) nat_ops.
Proof.
  constructor; unfold leq; simpl; solve [
    discriminate_levels |
    eauto with typeclass_instances | 
    try right; intros; lia ].
Qed.

Notation "\max_ ( i \in l ) f" := (sup (X:=nat_ops) (fun i => f) l)
 (at level 41, f at level 41, i, l at level 50,
   format "'[' \max_ ( i \in  l ) '/  '  f ']'"): ra_terms.

(* Notation "\min_ ( i \in l ) f" := (sup (X:=dual nat_ops) (fun i => f) l) *)
(*  (at level 41, f at level 41, i, l at level 50, *)
(*    format "'[' \min_ ( i \in  l ) '/  '  f ']'"): ra_terms. *)

Notation "x '^2'" := ((x*x)%nat) (at level 66).

Lemma square_max I (J: list I) f: (\max_(i\in J) f i) ^2 == \max_(i\in J) (f i ^2).
Proof.
  apply (f_sup_weq (fun x => x^2)). reflexivity.
  intros x y. simpl. symmetry. apply (PeanoNat.Nat.max_mono (fun x => x^2)).
  eauto with typeclass_instances.
  simpl. intros. nia. 
Qed.

Instance plus_leq: Proper (leq ==> leq ==> leq) plus.
Proof. simpl. intros. lia. Qed. 

Instance minus_leq: Proper (leq ==> leq --> leq) minus.
Proof. simpl. intros. lia. Qed.

Instance mult_leq: Proper (leq ==> leq ==> leq) mult.
Proof. simpl. intros. nia. Qed.

Definition natsum I (l: list I) f := (fold_right (fun i x => f i + x) 0 l).

Notation "\natsum_ ( i \in l ) f" := (natsum l (fun i => f))
  (at level 41, f at level 41, i, l at level 50,
    format "'[' \natsum_ ( i \in  l ) '/  '  f ']'"): nat_scope.

Lemma natsum_leq I (l: list I) f g: (forall i, In i l -> f i <== g i) -> natsum l f <== natsum l g.
Proof.
  induction l; simpl natsum. reflexivity.
  intro H. now rewrite H, IHl by firstorder.
Qed.

Lemma natsum_weq I (l: list I) f g: (forall i, In i l -> f i = g i) -> natsum l f = natsum l g.
Proof. setoid_rewrite weq_spec. split; apply natsum_leq; firstorder. Qed.

Instance natsum_leq' I (l: list I): Proper (pwr leq ==> leq) (natsum l).
Proof. intros ? ? ?. apply natsum_leq. firstorder. Qed.

Instance natsum_weq' I (l: list I): Proper (pwr weq ==> weq) (natsum l).
Proof. intros ? ? ?. apply natsum_weq. firstorder. Qed.

Lemma foldright_plus_k I (l: list I) f k: fold_right (fun i x => f i + x) k l = k + natsum l f.
Proof. induction l; simpl; auto. rewrite IHl. lia. Qed.

Lemma natsum_app I (h k: list I) f: natsum (h++k) f = natsum h f + natsum k f.
Proof. unfold natsum. rewrite fold_right_app, foldright_plus_k. unfold natsum. lia. Qed.
  
Lemma natsum_appC I (h k: list I) f: natsum (h++k) f = natsum (k++h) f.
Proof. rewrite 2natsum_app. lia. Qed.

Lemma length_natsum I (f: I -> nat) n k:
  (forall i, In i k -> f i = n) -> (n * length k)%nat = natsum k f.
Proof.
  induction k; simpl. intros. lia. 
  intro Hk. rewrite Hk, <-IHk by firstorder. lia.
Qed.

Lemma length_natsum_leq I (f: I -> nat) n k:
  (forall i, In i k -> f i <== n) -> natsum k f <== (n * length k)%nat.
Proof.
  induction k; simpl (natsum _ _). intros. simpl. lia. 
  intro Hk. rewrite Hk, IHk by firstorder. simpl. lia. 
Qed.

Lemma max_reach I (l: list I) (f: I -> nat): l=nil \/ exists i, In i l /\ f i = sup f l.
Proof.
  induction l as [|i l IH]. tauto.
  right. destruct IH as [-> |(j&Hj&H)].
  exists i. split. now left. symmetry. apply sup_singleton.
  simpl. rewrite <- H.
  destruct (Max.max_spec (f i) (f j)) as [[_ ->]|[_ ->]]; eauto.
Qed.

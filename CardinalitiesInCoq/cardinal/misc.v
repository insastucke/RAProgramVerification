Require Export List Relations Setoid Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section l.
 Variable A: Type.
 Variable P: relation A.
 (* [listP l] holds if [P x y] holds for any elements [x] [y] 
    occuring in [l] at distinct places *)
 Fixpoint listP (l: list A): Prop :=
   match l with
   | nil => True
   | x::q => (forall y, In y q -> P x y /\ P y x) /\ listP q
   end.
 Lemma listP_map_filter I k f (g: I -> A): listP (map g k) -> listP (map g (filter f k)).
 Proof.
   induction k; simpl. tauto.
   intros [Ha Hk]. case_eq (f a); intro E. simpl.
    split. 2: now apply IHk. 
    intros b Hb. apply in_map_iff in Hb as (i&<-&Hi). apply filter_In in Hi.
    apply Ha. apply in_map. tauto.
   now apply IHk. 
 Qed.
 Lemma listP_filter k f: listP k -> listP (filter f k).
 Proof.
   rewrite <-(map_id k) at 1.
   rewrite <-(map_id (filter _ _)).
   apply listP_map_filter.
 Qed.
 Lemma listP_spec: forall k x y, listP k -> In x k -> In y k -> x=y \/ P x y.
 Proof.
   induction k; simpl. tauto.
   intros x y [Ha Hk] [->|Hx] [->|Hy].
    now left.
    right. now apply Ha.
    right. now apply Ha.
    now apply IHk. 
 Qed.
 Lemma listP_app_iff h k:
   listP (h++k) <-> listP h /\ listP k /\ forall x y, In x h -> In y k -> P x y /\ P y x.
 Proof.
   induction h as [|x h IH]; simpl. tauto.
   rewrite IH. setoid_rewrite in_app_iff. clear IH.
   firstorder subst; firstorder.
 Qed.
 Lemma listP_app h k: listP (h++k) -> listP (k++h).
 Proof. rewrite 2listP_app_iff. firstorder. Qed.
End l.
Lemma listP_map A B (P: relation A) (Q: relation B) (f: A -> B) l:
  (forall x y, In x l -> In y l -> P x y -> Q (f x) (f y)) -> listP P l -> listP Q (map f l).
Proof.
  intro Hf. induction l; simpl. tauto.
  setoid_rewrite in_map_iff. firstorder subst; auto.
Qed.
Lemma in_concat_iff A (x: A) L: In x (concat L) <-> exists l, In x l /\ In l L.
Proof.
  induction L; simpl. firstorder.
  rewrite in_app_iff, IHL. clear IHL. firstorder subst; firstorder.
Qed.
Lemma listP_concat A (P: relation A) L:
  listP (fun h k => listP P (h++k)) L ->
  (forall h, In h L -> listP P h) -> 
  listP P (concat L).
Proof.
  induction L as [|h L IH]; simpl. tauto.
  intros H1 H2. rewrite listP_app_iff. split.
  apply H2; tauto. split.
  apply IH. intros; apply H1; tauto. intros; apply H2; tauto.
  clear IH. setoid_rewrite in_concat_iff. intros x y Hx (k&Hy&Hk).
  eapply listP_app_iff; try eassumption. now apply H1. 
Qed.

Inductive reflect (P: Prop): bool -> Set :=
| r_true: P -> reflect P true
| r_false: ~P -> reflect P false.

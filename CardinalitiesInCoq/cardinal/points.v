Require Export tarski.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition nodup {X: ops} n m := listP (fun x y: X n m => ~(x==y)). 
Definition disjoint {X: ops} n m := listP (fun x y: X n m => x \cap y <== 0).

Lemma disjoint_spec `{laws} `{CAP<<l} n m (h: list (X n m)):
  disjoint h -> forall x y, In x h -> In y h -> x=y \/ x \cap y <== 0.
Proof. intros D x y. apply (listP_spec D). Qed.

Lemma disjoint_app `{laws} `{CAP<<l} n m (h k: list (X n m)):
  disjoint (h++k) -> disjoint (k++h).
Proof. apply listP_app. Qed.


Class pointed (X: ops) := {
 points: forall n m, list (X n m);
 points_points: forall n m p, In p (points n m) -> is_point p;
 points_nodup: forall n m, nodup (points n m);
 point_ax: forall n m, top == \sup_(p\in points n m) p;
 leqb: forall n m, X n m -> X n m -> bool;
 leqb_spec: forall n m (x y: X n m), reflect (x<==y) (leqb x y) }.

Hint Immediate points_points: typeclass_instances.

Instance pointed_decidable `{pointed}: decidable X.
Proof. intros n m x y. case (leqb_spec x y); tauto. Qed.

Section s.
 Context {X} {l} {L: laws l X} {T: tarski X} {P: pointed X}.

 Lemma leqb_true n m (x y: X n m): leqb x y = true <-> x <== y.
 Proof. case leqb_spec; intuition congruence. Qed.

 Lemma leqb_false n m (x y: X n m): leqb x y = false <-> ~(x <== y).
 Proof. case leqb_spec; intuition congruence. Qed.
 
 Lemma disjoint_points {Hl: AL+TOP<<l} n m: disjoint (points n m).
 Proof.
   rewrite <-map_id. eapply listP_map. 2: apply points_nodup. simpl.
   intros p q Hp Hq PQ. apply points_points in Hp. apply points_points in Hq.
   destruct (points_eq_or_disjoint Hp Hq); tauto.
 Qed.
 
 Lemma disjoint_points' {Hl: BL+CNV<<l} n m k (p: X m k):
   disjoint (map (fun q => p * q`) (points n k)).
 Proof. 
   eapply listP_map. 2: apply disjoint_points. simpl.
   intros x y Hx Hy Hxy. cnv_switch. ra_normalise.
   now apply disjoint_vect_ext.
 Qed.
 
 Lemma point_ax' {Hl: BDL+CNV<<l} {n m} {v: X n m} {Hv: is_vector v}: 
   v == \sup_(p \in List.filter (fun p => leqb p v) (points n m)) p.
 Proof.
   apply antisym.
   
   rewrite <- (capxt v). rewrite point_ax. rewrite capxsup.
   apply leq_supx. intros p Hpn.

   case (leq_point_vect (p:=p) (v:=v)); intro Hpv.
    apply leq_xsup' with p.
    apply filter_In. split. assumption. now apply leqb_true. lattice.
    rewrite capC, Hpv. lattice.
   
   apply leq_supx. intros p Hp. apply filter_In in Hp as [_ Hp]. now apply leqb_true. 
 Qed.

 Lemma point_id {Hl: BDL+CNV<<l} n m: is_nonempty' m \/ n=m -> one n == \sup_(p\in points n m) p*p`.
 Proof.
   intro Hm. apply antisym.
   
   transitivity (1\cap (top' n m *top`)). rewrite cnvtop.
   destruct Hm.
    rewrite top_nonempty. lattice.
    subst. rewrite top_nnm. lattice.
   rewrite point_ax. rewrite cnvsum. rewrite dotsumx. setoid_rewrite dotxsum.
   rewrite capxsup. setoid_rewrite capxsup.
   
   apply sup_leq'. reflexivity. intros p Hp.
   apply leq_supx. intros q Hq.
   destruct (disjoint_spec (disjoint_points n m) Hp Hq).
    subst. lattice.
    rewrite disjoint_id by assumption. lattice.

   apply leq_supx. intros p Hp. apply injective. 
 Qed.
 
 Lemma all_points {Hl: BDL+CNV<<l} n m (p: X n m):
   is_point p -> exists p', In p' (points n m) /\ p==p'.
 Proof.
   intros Hp. pose proof point_ax'. remember (filter _ _) as h.
   destruct h as [|p' h]. simpl in H.
   pose proof (nonempty (x:=p)) as E. apply Tarski in E. rewrite leq_xb_iff in E. tauto.
   assert (Hp': In p' (points n m)).
    assert (In p' (p'::h)) by now left. rewrite Heqh in H0.
    apply filter_In in H0. tauto. 
   exists p'. split. assumption. 
   symmetry. apply points_points in Hp'. apply surjective_injective_antisym. 
   rewrite H. lattice.
 Qed.

 (* below: actually the lattice-theoretic notion of atomic (restricted to points and vectors) *)
 Lemma pointic {Hl: BDL+CNV<<l} n m (v: X n m) {Hv: is_vector v}:
   ~ (v<==0) -> exists p, is_point p /\ p<==v.
 Proof.
   intros H. pose proof point_ax' as E.
   remember (filter _ _) as h. destruct h as [|p h].
    rewrite E in H. now contradict H.
    exists p. split. 2: rewrite E; simpl; lattice. 
    assert (Hp: In p (p::h)) by now left. 
    rewrite Heqh in Hp. apply filter_In in Hp. 
    apply points_points. tauto.
 Qed.

 Lemma from_below_points {Hl: BDL+CNV<<l} {n m} {v w: X n m} {Hv: is_vector v} {Hw: is_vector w}:
   (forall p, is_point p -> p <== v -> p <== w) <-> v <== w.
 Proof.
   split. intro H.
   rewrite point_ax'. apply sup_spec. 
   setoid_rewrite filter_In. intros p [Pp Hp].
   apply H. tc. now apply leqb_true. 
   intros E p _ . now rewrite E. 
 Qed.

 Lemma nopoint_empty {Hl: BDL+CNV<<l} {n m} {v: X n m} {Hv: is_vector v}:
   (forall p, is_point p -> ~ (p<==v)) -> v <== 0.
 Proof.
   assert (V0: is_vector (zer n m)) by ra. 
   intros H. rewrite <-from_below_points. 
   intros p Hp Hp'. apply H in Hp'; tauto. 
 Qed.

 Definition atoms n m := concat (map (fun p => map (fun q => p*q`) (points m n))(points n n)).

 Lemma In_atoms n m a:
   In a (atoms n m) <->
   exists p, exists q, In p (points n n) /\ In q (points m n) /\ a=p*q`.
 Proof.
   unfold atoms.
   induction (points n n) as [|p h IHh]. firstorder.
   simpl. rewrite in_app_iff, IHh, in_map_iff. clear.
   firstorder subst; do 2eexists; eauto.
 Qed.

 Lemma disjoint_atoms {Hl: BL+CNV<<l} n m: disjoint (atoms n m).
 Proof.
   apply listP_concat.
    eapply listP_map. 2: apply disjoint_points.
    simpl. intros x y Hx Hy Hxy. apply listP_app_iff. split.
    apply disjoint_points'. split. 
    apply disjoint_points'. 
    setoid_rewrite in_map_iff. intros ? ? (x'&<-&Hx') (y'&<-&Hy').
    split. now apply disjoint_vect_ext. rewrite capC. now apply disjoint_vect_ext. 
   setoid_rewrite in_map_iff. intros h (x&<-&Hx).
   eapply listP_map. 2: apply disjoint_points.
   simpl. intros y z Hy Hz Hyz. cnv_switch. ra_normalise. 
   now apply disjoint_vect_ext. 
 Qed.
 
 Lemma atoms_atoms `{AL+TOP<<l} n m a: In a (atoms n m) -> is_atom a.
 Proof. rewrite In_atoms. intros (p&q&Hp&Hq&->). apply atom_of_points. Qed.

 Hint Immediate atoms_atoms: typeclass_instances.
 
 Lemma atom_ax `{BDL+CNV<<l} n m: top' n m == \sup_(a\in atoms n m) a.
 Proof.
   rewrite <-top_nnm. rewrite <-(cnvtop m).
   rewrite 2point_ax, cnvsum, dotxsum. 
   setoid_rewrite dotsumx. apply antisym.
   apply leq_supx. intros p Hp. apply leq_supx. intros q Hq.
   eapply leq_xsup'. 2: reflexivity. rewrite In_atoms. eauto.
   apply leq_supx. intros a. rewrite In_atoms. intros (p&q&Hp&Hq&->).
   eapply leq_xsup'. eassumption.
   eapply leq_xsup'. eassumption.
   reflexivity.
 Qed.   

 Lemma atom_ax' `{BDL+CNV<<l} n m (x: X n m):
   x == \sup_(a\in filter (fun a => leqb a x) (atoms n m)) a.
 Proof.
   apply antisym.
   
   rewrite <- (capxt x). rewrite atom_ax. rewrite capxsup.
   apply leq_supx. intros a Ha.

   case (leq_atom_x (a:=a) (x:=x)); intro Hpv.
    apply leq_xsup' with a.
    apply filter_In. split. assumption. now apply leqb_true. lattice.
    rewrite capC, Hpv. lattice.
   
   apply leq_supx. intros a Ha. apply filter_In in Ha as [_ ?]. now apply leqb_true. 
 Qed.   

 Lemma all_atoms {Hl: BDL+CNV<<l} n m (a: X n m):
   is_atom a -> exists a', In a' (atoms n m) /\ a==a'.
 Proof.
   intro Ha. pose proof (nonempty_dom (x:=a)) as Hn.
   destruct atom_points as (p&q&Hp&Hq&H).
   apply all_points in Hp as (p'&?&Hp). 
   apply all_points in Hq as (q'&?&Hq). 
   exists (p'*q'`). split. rewrite In_atoms. eauto.
   now rewrite H, Hp, Hq.
 Qed.

 Lemma atomic {Hl: BDL+CNV<<l} n m (x: X n m):
   ~ (x<==0) -> exists a, is_atom a /\ a<==x.
 Proof.
   intros H. pose proof (atom_ax' x) as E.
   remember (filter _ _) as h. destruct h as [|a h].
    rewrite E in H. now contradict H.
    exists a. split. 2: rewrite E; simpl; lattice. 
    assert (Ha: In a (a::h)) by now left. 
    rewrite Heqh in Ha. apply filter_In in Ha. 
    apply atoms_atoms. tauto.
 Qed.

 Lemma from_below_atoms {Hl: BDL+CNV<<l} n m (x y: X n m):
   (forall a, is_atom a -> a <== x -> a <== y) <->
   x <== y.
 Proof.
   split. intro H. rewrite atom_ax'. apply leq_supx. intros a.
   rewrite filter_In. intros [Ha Hax]. apply H. tc.
   now apply leqb_true.  
   intros E p _ . now rewrite E. 
 Qed.

 Lemma noatom_empty {Hl: BDL+CNV<<l} {n m} {x: X n m}:
   (forall a, is_atom a -> ~ (a<==x)) -> x <== 0.
 Proof.
   intros H. rewrite <-from_below_atoms. 
   intros p Hp Hp'. apply H in Hp'; tauto. 
 Qed.

 (* cardinal can be defined in pointed relation algebra *)
 Definition card n m (x: X n m) :=
   length (filter (fun a => leqb a x) (atoms n m)).

 Fixpoint xrelations n m (l: list (X n m)) :=
   match l with
   | [] => [0]
   | a::l => xrelations l ++ map (cup a) (xrelations l)
   end.
 
 Definition relations n m:= xrelations (atoms n m).

 Lemma all_relations {Hl: BDL+CNV<<l} n m (x: X n m):
   exists y, In y (relations n m) /\ x == y.
 Proof.
   setoid_rewrite (atom_ax' x). unfold relations.
   induction (atoms n m) as [|a h IH]. simpl. now eauto.
   destruct IH as (y&Hy&Hy').
   simpl. setoid_rewrite in_app_iff.
   case leqb_spec; intro Ha.
   exists (cup a y). split. right. now apply in_map. simpl. now rewrite Hy'.
   exists y. split. now left. assumption.
 Qed. 

End s.

Hint Resolve atoms_atoms: typeclass_instances.

(* Title:      Cardinalities
   Author:     Insa Stucke (ist@informatik.uni-kiel.de)
*)

theory Relation_Algebra_Cardinal imports Main "~~/Relation_Algebra_Cardinalities/Relation_Algebra_Atoms" 

begin

text{* This theory contains the definition of a cardinality operation. 

Furthermore, all lemmata of the underlying paper are proved here. There are also proofs for many 
results not mentioned in the paper, for instance, several concerning partial identities and points. *}

declare [[show_sorts,show_types]]

context relation_algebra_fin_points
begin

text{* Since we deal with natural numbers, in this theory we have to change the previous notations. *}
no_notation
  inf (infixl "\<cdot>" 70)
  and sup (infixl "+" 65)
  and bot ("0")
  and top ("1")
  and uminus ("- _" [81] 80)
  and less (infix "<" 50)
  and less_eq (infix "\<le>" 50)

notation
  less_eq (infix "\<sqsubseteq>" 50)
  and less (infix "\<sqsubset>" 50)
  and inf (infixl "\<sqinter>" 70)
  and sup (infixl "\<squnion>" 65)

notation
  plus (infixl "+" 65)
  and uminus ("(_\<^sup>c)" [1000] 999)
  (*and uminus ("~ _" [81] 80)*)
end

class cardinal = 
  fixes cd :: "'a \<Rightarrow> nat"  ("|_|" [30] 999)

class relation_algebra_card = cardinal + relation_algebra_fin_points +
  assumes card0 : "|x| = 0 \<longleftrightarrow> x=bot"
    and cardcnv [simp]: "|x\<^sup>\<smile>| = |x|"
    and cardcup : "|x \<squnion> y| = |x| + |y| - |x \<sqinter> y|"
    and cardded : "is_p_fun x \<Longrightarrow> |y \<sqinter> x\<^sup>\<smile>;z| \<le> |(x;y) \<sqinter> z|"
    and cardded': "is_p_fun x \<Longrightarrow> |x \<sqinter> (z;y\<^sup>\<smile>)| \<le> |(x;y) \<sqinter> z|"
    and cardtone[simp]: "card {x. is_point x} = |1'|" 

context relation_algebra_card 
  begin


lemma sumsubcardleq: 
  assumes "A \<subseteq> B" 
  and "finite B" 
  shows "(\<Sum> y \<in> A. |y| ) \<le> (\<Sum> y \<in> B. |y| )"
by (simp add: assms sum_mono2)

    
lemma cardsimp [simp]: "|x \<squnion> y| + |x \<sqinter> y| = |x| + |y|"
proof -
  have aux: "|x| + |y| \<ge> |x \<sqinter> y| "
    by (metis diff_is_0_eq linear card0 cardcup inf_bot_left inf_bot_right inf_sup_absorb zero_le)
  then show ?thesis
    by (simp add: cardcup aux)
qed

lemma cardcap: "|x \<sqinter> y| = |x| + |y| - |x \<squnion> y|"
  by (metis cardsimp diff_add_inverse)

lemma card0_neq: "x \<noteq> bot \<Longrightarrow> |x| \<noteq> 0"
  using bot_nat_def card0 by auto


lemma capzero: "(x \<sqinter> y) = bot \<Longrightarrow> |x \<sqinter> y| = 0"
  using bot_nat_def card0 by auto


lemma cardbotsimp [simp]: "|bot| = 0"
  using bot_nat_def card0 by auto


lemma cardcupcap': "x \<sqinter> y = bot \<Longrightarrow> |x \<squnion> y| = |x|+ |y|"
  using capzero cardcup by auto


lemma card_sum_leq:  
  assumes fin: "finite {x |x . P x}"
  shows   "|\<Squnion>{x |x . P x}| \<le> (\<Sum> y \<in> {x |x . P x}. |y| )"
proof (induct rule: finite_induct[OF fin])
  show "|\<Squnion>{}| \<le> (\<Sum> y \<in> {}. |y| )"
    by simp
next 
  fix x :: 'a and  F ::" 'a set"
  assume finF: "finite F"
     and notinF: "x\<notin>F"
     and indhyp: " |\<Squnion>F| \<le> (\<Sum> y \<in> F. |y| )"
  show "|\<Squnion>(insert x F)| \<le> (\<Sum> y \<in> (insert x F). |y| )"
  proof -
    have a: "|\<Squnion>(insert x F)| = |x|+ |\<Squnion>F| - |x \<sqinter> \<Squnion>F|"
      by (metis finF add_sum cardcup)
    also have b: "\<dots> \<le> |x|+ (\<Sum> y \<in> F. |y| )"
      using indhyp by auto
    finally show ?thesis
      by (simp add: finF notinF)
  qed
qed
  

lemma card_sum_leq_1:  
  assumes fin: "finite {x |x . P x}"
  shows   "|\<Squnion>{f x |x . P x}| \<le> (\<Sum> y \<in> {v |v. \<exists>x. f x=v \<and>  P x}. |y| )"
proof -
  have "|\<Squnion>{f x |x . P x}| = |\<Squnion>{v |v. \<exists>x. f x=v \<and>  P x}|"
    by metis
  also have "\<dots> \<le> (\<Sum> v \<in> {v |v. \<exists>x. f x=v \<and>  P x}. |v| )"
    by (metis (no_types, lifting) Collect_cong card_sum_leq comm_monoid_add_class.sum.infinite cardbotsimp sum.infinite order_class.eq_iff)  
  finally show ?thesis
    by blast
qed

  
lemma card_sum_leq_1':  
  assumes fin: "finite {x |x . P x}"
  shows   "|\<Squnion>{f x |x . P x}| \<le> (\<Sum> y \<in> {f x |x . P x}. |y| )"
proof -
  have "|\<Squnion>{f x |x . P x}|  \<le> (\<Sum> v \<in> {v |v. \<exists>x. f x=v \<and> P x}. |v| )"
    using card_sum_leq_1 fin by blast
  also have "\<dots> = (\<Sum> v \<in> {f x |x . P x}. |v| )"
    by metis 
  finally show ?thesis
    by blast
qed
  
  
lemma card_sum_disj: 
  assumes "finite {x |x . P x}"
  shows   "pairwise_disjoint {x |x . P x} \<Longrightarrow> |\<Squnion>{x |x . P x}| = (\<Sum> y \<in> {x |x . P x}. |y| )"
proof (induct rule: finite_induct[OF assms(1)])
  show "pairwise_disjoint {} \<Longrightarrow> |\<Squnion>{}| = (\<Sum> y \<in> {}. |y| )"
    by simp
next 
  fix x :: 'a 
  and F ::" 'a set"
  assume finF: "finite F"
    and notinF: "x\<notin>F"
    and indhyp: "pairwise_disjoint F \<Longrightarrow> |\<Squnion>F| = (\<Sum> y \<in> F. |y| )"
  show "pairwise_disjoint (insert x F) \<Longrightarrow> |\<Squnion>(insert x F)| = (\<Sum> y \<in> (insert x F). |y| )"
  proof -
    assume pwd: "pairwise_disjoint (insert x F)"
    show "|\<Squnion>(insert x F)| = (\<Sum> y \<in> (insert x F). |y| )"
    proof -
    have  "|\<Squnion>(insert x F)| = |x|+ |\<Squnion>F| - |x \<sqinter> \<Squnion>F|"
      by (metis finF add_sum cardcup)
    also have "\<dots> = |x|+ (\<Sum> y \<in> F. |y| )"
      using finF indhyp pairwise_disjoint_def pwdset sum_cap_distr_left_set' notinF pwd by auto
    also have "...= (\<Sum> y \<in> (insert x F). |y| )"
      by (simp add: finF notinF)
    finally show ?thesis 
      by linarith 
    qed
  qed 
qed 


lemma card_sum_point[simp]: "|\<Squnion>{x |x . is_point x}|= (\<Sum> y \<in> {x |x . is_point x}. |y| )"
proof (rule card_sum_disj)
  show "pairwise_disjoint {x |x . is_point x}"
    by (simp add: galois_aux pairwise_disjoint_def pointneqdisjp)
next
  show "finite {x |x . is_point x}"
    using finiteness by auto
qed


lemma card_sum_point_p [simp]: "|\<Squnion>{x |x . is_point x \<and> P x}|= (\<Sum> y \<in> {x |x . is_point x \<and> P x}. |y| )"
proof (rule card_sum_disj)
  show "pairwise_disjoint {x |x . is_point x \<and> P x}"
    by (simp add: galois_aux pairwise_disjoint_def pointneqdisjp)
next
  show "finite {x |x . is_point x \<and> P x}"
    using finiteness by auto
qed


lemma card_sum_points: "|\<Squnion>{x |x.\<exists> p q. p;q\<^sup>\<smile>=x \<and> is_point p \<and> is_point q}| = (\<Sum> y \<in> {x |x.\<exists> p q. p;q\<^sup>\<smile>=x \<and> is_point p \<and> is_point q}. |y| )"
proof (rule card_sum_disj)
  show "finite {x |x. \<exists>p q. p;q\<^sup>\<smile> = x \<and> is_point p \<and> is_point q}"
    using fin_points by blast
next 
  show "pairwise_disjoint {x |x.\<exists> p q. p;q\<^sup>\<smile>=x \<and> is_point p \<and> is_point q}"
    using pwd_points by blast
qed


lemma card_sum_points_eq: "|\<Squnion>{x |x.\<exists> p. p;p\<^sup>\<smile>=x \<and> is_point p}| = (\<Sum> y \<in> {x |x.\<exists> p. p;p\<^sup>\<smile>=x \<and> is_point p}. |y| )"
proof (rule card_sum_disj)
  show "finite {x |x.\<exists> p. p;p\<^sup>\<smile>=x \<and> is_point p}"
    using finite_point_fun' by force
next 
  show "pairwise_disjoint {x |x.\<exists> p. p;p\<^sup>\<smile>=x \<and> is_point p}"
    using pwd_points_eq by blast
qed


lemma card_sum_atoms: "|\<Squnion>{x |x. is_atom x}| = (\<Sum> y \<in> {x |x. is_atom x}. |y| )"
  using card_sum_points atomeqpoints by auto


lemma card_sum_atoms_p: "|\<Squnion>{x |x. is_atom x \<and> P x}| = (\<Sum> y \<in> {x |x. is_atom x \<and> P x}. |y| )"
  using card_sum_disj atomdisj bot_unique pairwise_disjoint_def fin_atoms_p by auto

lemma sumleq:
  assumes "finite {x. P x}"
  shows   "|\<Squnion> {x. P x}| \<le> (\<Sum> y \<in> {x. P x}. |y| )"
  using assms card_sum_leq by auto  


lemma cardmono: 
  assumes "x \<sqsubseteq> y"
  shows "|x| \<le> |y|"
by (metis add.right_neutral assms cardbotsimp cardsimp le_add1 aux4 inf.commute inf.orderE inf_compl_bot_left2)

lemma cardmononeq: 
  assumes "x \<sqsubset> y"
  shows "|x| \<le> |y| \<and> |x| \<noteq> |y|"
proof (rule conjI)
  show "|x| \<sqsubseteq> |y|"
    using assms cardmono by auto
  show "|x| \<noteq> |y|"
    proof -
      have "\<And>z. x \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
        by (metis assms inf.assoc inf.strict_order_iff)
      then show ?thesis
        by (metis add_diff_cancel_left' assms cardsimp aux4 card0 inf.absorb_iff2 inf.cobounded2 inf_compl_bot less_le_not_le)
    qed
  qed
    
lemma carduniuni: 
  assumes "is_p_fun x" 
  and "is_p_fun y" 
  shows "|x;y \<sqinter> z| = |x \<sqinter> z;y\<^sup>\<smile>|"
proof (rule le_antisym)
  show "|x \<sqinter> z;y\<^sup>\<smile>| \<le> |x;y \<sqinter> z|"
    by (simp add: assms(1) cardded')
next 
  show "|x;y \<sqinter> z| \<le> |x \<sqinter> z;y\<^sup>\<smile>|"
    proof - 
      have "|x;y \<sqinter> z| = |z\<^sup>\<smile> \<sqinter> (y\<^sup>\<smile>;x\<^sup>\<smile>)|"
        by (metis cardcnv conv_contrav conv_times inf.commute)
      also have "\<dots> \<le> |(y ; z\<^sup>\<smile> \<sqinter> x\<^sup>\<smile>)\<^sup>\<smile>|"
        using assms(2) cardcnv cardded by presburger
      also have "\<dots> \<le> |x \<sqinter> z;y\<^sup>\<smile>|"
        by (simp add: inf.commute)
      finally show ?thesis
        by auto
    qed 
qed


lemma card_pfun: 
  assumes "is_p_fun x" 
  shows "|x\<^sup>\<smile>;y| \<le> |y|"
proof - 
  have "|x\<^sup>\<smile>;y| = |x\<^sup>\<smile>;y \<sqinter> x\<^sup>\<smile>;y|"
    by auto
  also have "\<dots> \<le> |x;(x\<^sup>\<smile>;y) \<sqinter> y|"
    using assms cardded by blast
  also have "\<dots> \<le> |y|"
    by (simp add: cardmono)
  finally show ?thesis
    by blast
qed


lemma cardunimap: 
  assumes "is_p_fun x" 
  and "is_map y" 
  shows "|x;y| = |x|"
by (metis (full_types) assms carduniuni inf_top.monoid_axioms is_map_def monoid.right_neutral total_one')

lemma card_inj: 
  assumes "is_inj x"
  and "y \<sqsubseteq> x;top"
  shows "|y| \<le> |x\<^sup>\<smile>;y|"
  by (metis assms(1) assms(2) cardded conv_invol inf_absorb1 inf_top.right_neutral inj_p_fun)

  
lemma cardpoint : 
  assumes "is_point x" 
  shows "|x|= |1'|"
by (metis assms cardunimap cardcnv is_test_def mult_1_left order_refl test_is_inj_fun point_cnv_map)

  
    
lemma cardvector: 
  assumes "is_vector x" 
  shows "card {p |p. is_point p \<and> p \<sqsubseteq> x}* |1'| = |x|"
proof -
  have "|x| = |\<Squnion> {p. is_point p \<and> p \<sqsubseteq> x}|" 
    by (simp add: assms)
  also have "\<dots> =  (\<Sum> y \<in> {p|p. is_point p \<and> p \<sqsubseteq> x}. |1'| )" 
    using card_sum_point_p cardpoint by force
  finally show ?thesis 
    by simp
qed


lemma cardpointscomp: 
  assumes "is_point x" 
  and "is_point y" 
  shows " 1 \<le> |x;y\<^sup>\<smile>|"
using assms card0_neq comp_points by force

(*
lemma card_vec_comp_aux: "pairwise_disjoint {z. \<exists>p. x;p\<^sup>\<smile> = z \<and> is_point p \<and> p \<sqsubseteq> y}"
unfolding pairwise_disjoint_def 
proof (intro allI,rule impI)
fix xa ya :: 'a
assume uset: " xa \<in> {z. \<exists>p. x;p\<^sup>\<smile> = z \<and> is_point p \<and> p \<sqsubseteq> y} \<and> ya \<in> {z. \<exists>p. x;p\<^sup>\<smile> = z \<and> is_point p \<and> p \<sqsubseteq> y} \<and> xa \<noteq> ya"
  obtain p q where h1: "x;p\<^sup>\<smile> = xa \<and> is_point p \<and> p \<sqsubseteq> y \<and> x;q\<^sup>\<smile> = ya \<and> is_point q \<and> q \<sqsubseteq> y"
    using uset by blast 
  have aux': "q\<^sup>\<smile>;p = bot"
    using h1 pointcompbot uset by force
  show "xa \<sqinter> ya = bot"
    using aux' h1 annir inf_bot_right mult_assoc schroeder_2 by force
qed
*)

lemma cardtop[simp]: "|1'|* |1'| = cd top"
using card_sum_point cardpoint cardtone by auto


lemma cardpointcomp: "|1'| = card {p;p\<^sup>\<smile>|p . is_point p}"  
proof - 
  have "card {x|x. is_point x} = card {p;p\<^sup>\<smile>|p . is_point p}"
    proof (rule bij_betw_same_card) 
      let ?f = "\<lambda>p. p;p\<^sup>\<smile>"
      show "bij_betw ?f {x|x. is_point x} {p;p\<^sup>\<smile>|p . is_point p}" unfolding bij_betw_def
        proof 
        show "inj_on ?f {x |x. is_point x}" unfolding inj_on_def
          using atomsareatoms by blast
        next
        show "?f ` {x|x. is_point x} = {p;p\<^sup>\<smile>|p. is_point p}" by blast
      qed
    qed
  thus ?thesis 
    by simp
qed


lemma card_setpoints': "card {p |p. is_point p} * card {q |q. is_point q} = card {(p,q) |p q. is_point p \<and> is_point q}"
proof - 
  have a: "{(p,q) |p q. is_point p \<and> is_point q} =  {p |p. is_point p} \<times> {q |q. is_point q}"
    by simp
  thus ?thesis
    by (metis Collect_cong Sigma_cong a card_cartesian_product)
qed


lemma card_setpoints: "card {(p,q) |p q. is_point p \<and> is_point q} = card {p;q\<^sup>\<smile> |p q. is_point p \<and> is_point q}"
proof (rule bij_betw_same_card) 
let ?f = "\<lambda> (p,q). p;q\<^sup>\<smile>"
  show "bij_betw ?f {(p,q) |p q. is_point p \<and> is_point q} {p;q\<^sup>\<smile> |p q. is_point p \<and> is_point q}" unfolding bij_betw_def
    proof 
    show "inj_on ?f {(p,q) |p q. is_point p \<and> is_point q}" unfolding inj_on_def
      using atomsareatoms by auto
    next 
    show "?f ` {(p,q) |p q. is_point p \<and> is_point q} = {p;q\<^sup>\<smile> |p q. is_point p \<and> is_point q}"
    proof - 
      have "?f ` {(p,q) |p q. is_point p \<and> is_point q} = {?f (p,q) |p q. is_point p \<and> is_point q}"
        by blast
      also have "{?f (p,q) |p q. is_point p \<and> is_point q} = {p;q\<^sup>\<smile> |p q. is_point p \<and> is_point q} "
        by simp
      finally show ?thesis by auto
    qed
   qed
qed


lemma card_atom_geq0: 
  assumes "is_atom x"
  shows "1 \<le> |x|"
using assms card0_neq is_atom_def by fastforce


lemma numberofatoms:  "card {x|x. is_atom x} =  |1'|* |1'|"
proof - 
  have "card {x|x. is_atom x} =  card {(p,q)| p q. is_point p \<and> is_point q}"
    using atomeqpoints card_setpoints pointssetcomp by auto
  also have "\<dots> = card {p |p. is_point p} * card {q |q. is_point q}"
    using card_setpoints' by auto
  also have "\<dots> = |1'|* |1'|"
    using cardtone by auto
  finally show ?thesis by linarith
qed


lemma sumnotin: 
  assumes "finite {x |x. P x}" 
  and "y \<in> {x |x. P x} "  
  shows "(\<Sum> z \<in> {x |x. P x}. |z| ) = |y| + (\<Sum> z \<in> {x |x. P x \<and> x\<noteq>y}. |z| )"
proof - 
  have a: "(\<Sum> z \<in> {x |x. P x}. |z| ) = (\<Sum> x \<in> (insert y {x |x. P x \<and> x\<noteq>y}). |x| )"
    proof - 
      have aux: "insert y {x |x. P x \<and> x\<noteq>y} = {x |x. P x}"
        using assms(2) by auto
      then show ?thesis 
        using aux by auto
    qed
  have b: "(\<Sum> x \<in> (insert y {x |x. P x \<and> x\<noteq>y}). |x| ) = |y| + (\<Sum> z \<in> {x |x. P x \<and> x\<noteq>y}. |z| )"
    using assms(1) by auto
  then show ?thesis
    using a by linarith 
qed


lemma cardminusone: 
  assumes "finite {x |x::'a. P x}" 
  and "y \<in> {x |x. P x} " 
  shows   "card {x |x. P x} = card {x |x. P x \<and> x\<noteq>y} + 1"
proof - 
  have  "{x |x. P x} = insert y {x |x. P x \<and> x\<noteq>y}"
    using assms by auto
  also have "card (insert y {x |x. P x \<and> x\<noteq>y}) = card {x |x. P x \<and> x\<noteq>y} + 1"
    using assms by auto
  finally show ?thesis by auto
qed


lemma cardminusone': 
  assumes "finite {x |x::'a. P x}" 
  and "y \<in> {x |x. P x} " 
  shows "card {x |x. P x} - 1 = card {x |x. P x \<and> x\<noteq>y}"
using assms cardminusone by auto


text{* The following is one of the key results saying that all atoms have cardinality 1. *}

lemma card_atom: 
  assumes "is_atom y"
  shows "|y| = 1"
proof (rule ccontr)
  assume asm: "|y| \<noteq> 1"
  have hyp: "2 \<le> |y|"
    using asm assms card_atom_geq0 by fastforce
  have y_in_at: "y\<in> {x |x. is_atom x}"
    by (simp add: assms)
  have "2 + (\<Sum> z \<in> {x |x. is_atom x \<and> x\<noteq>y}. 1 ) \<le> |y| + (\<Sum> z \<in> {x |x. is_atom x \<and> x\<noteq>y}. |z| )"
    by (metis (mono_tags, lifting) add_le_mono card_atom_geq0 hyp mem_Collect_eq sum_mono)
  also have "\<dots> = (\<Sum> z \<in> {x |x. is_atom x}. |z| )"
    using assms fin_atoms sumnotin y_in_at by auto
  finally show "False"
     using add.commute card_sum_atoms cardminusone fin_atoms topatoms' numberofatoms y_in_at by force
qed


lemma card_partial_point:
  assumes "is_partial_point x" 
  shows "|x| = 1"
using assms card_atom is_partial_point_def by blast


lemma card_test: 
  assumes "is_test y" 
  shows "|y| = card {x|x. is_partial_point x \<and> x \<sqsubseteq> y}"
proof -
  have aux: "{x|x. is_partial_point x \<and> x \<sqsubseteq> y} = {x|x. is_atom x \<and> x \<sqsubseteq> y \<and> x \<sqsubseteq> 1'}"
    using is_partial_point_def is_test_def by auto
  have "|y| = |\<Squnion>  {x|x. is_atom x \<and> x \<sqsubseteq> y \<and> x \<sqsubseteq> 1'}|"
    using assms aux test_partial_points by fastforce
  also have "\<dots> = card {x|x. is_partial_point x \<and> x \<sqsubseteq> y}"
    using aux assms test_partial_points card_atom card_sum_atoms_p by fastforce
  finally show ?thesis by linarith 
qed

  
lemma partial_point_bijection: 
  assumes "is_test y" 
  shows "card {z| z. \<exists> x. g x = z \<and> is_partial_point x \<and> x \<sqsubseteq> y} \<le> card {x|x. is_partial_point x \<and> x \<sqsubseteq> y}"
proof (rule surj_card_le)
  show "finite {x|x. is_partial_point x \<and> x \<sqsubseteq> y}"
    using local.fin_partial_points_p by auto
next
  let ?f = "\<lambda>x. g x"  
  show " {z |z. \<exists>x. g x = z \<and> is_partial_point x \<and> x \<sqsubseteq> y} \<subseteq> (?f::'a \<Rightarrow> 'b) ` {x |x::'a. is_partial_point x \<and> x \<sqsubseteq> y}"
    by auto
qed

  
lemma card_test_fun: 
  assumes "is_test y" 
  shows "card {f x|x. is_partial_point x \<and> x \<sqsubseteq> y} \<le> |y|"
proof -
  have a: "{f x|x. is_partial_point x \<and> x \<sqsubseteq> y} = {z| z. \<exists> x. f x = z \<and> is_partial_point x \<and> x \<sqsubseteq> y}"
    by blast
  have "card {f x|x. is_partial_point x \<and> x \<sqsubseteq> y} = card {z| z. \<exists> x. f x = z \<and> is_partial_point x \<and> x \<sqsubseteq> y}"
    using a by auto
  also have "\<dots> \<le> card {x|x. is_partial_point x \<and> x \<sqsubseteq> y}" 
    using partial_point_bijection assms by fastforce
  finally show ?thesis 
    using card_test assms by auto
qed


lemma pointcap_ppoint: 
  assumes "is_point x" 
  shows "is_partial_point (x \<sqinter> 1')"
unfolding is_partial_point_def 
proof 
  show "is_atom (x \<sqinter> 1')"
    by (metis assms inf.absorb2 inf_commute is_inj_def is_point_def is_vector_def one_conv pointsatom)
  show "is_test (x \<sqinter> 1')"
    by (simp add: is_test_def)
qed


lemma ppoint_point: 
  assumes "is_partial_point x" 
  shows   "is_point (x;top)"
using assms atompoint is_partial_point_def by blast


lemma bij_betw_points_partialpoints: "\<exists> f. bij_betw f {p |p. is_point p} {y |y. is_partial_point y}"
proof 
  show "bij_betw (\<lambda> p. p \<sqinter> 1') {p |p. is_point p} {y |y. is_partial_point y}" unfolding bij_betw_def
    proof (intro conjI)
      show "inj_on (\<lambda>p. p \<sqinter> 1') {p |p. is_point p}" unfolding inj_on_def
        by (metis CollectD inf_top_right is_point_def vector_3)
      show "(\<lambda>p. p \<sqinter> 1') ` {p |p. is_point p} = {y |y. is_partial_point y}" 
        using atompoint is_partial_point_def pointcap_ppoint by force
    qed
qed



lemma point_ppoint: 
  assumes "is_vector x" 
  shows "{p \<sqinter> 1'|p. is_point p \<and> p \<sqsubseteq> x} = {p|p. is_partial_point p \<and> p \<sqsubseteq> x \<sqinter> 1'}"
proof 
  show "{p \<sqinter> 1' |p. is_point p \<and> p \<sqsubseteq> x} \<subseteq> {p |p. is_partial_point p \<and> p \<sqsubseteq> x \<sqinter> 1'}"
    using meet_iso pointcap_ppoint by auto
  show "{p |p. is_partial_point p \<and> p \<sqsubseteq> x \<sqinter> 1'} \<subseteq> {p \<sqinter> 1' |p. is_point p \<and> p \<sqsubseteq> x}"       
  proof 
    fix xa
    assume asm1: "xa \<in> {p |p. is_partial_point p \<and> p \<sqsubseteq> x \<sqinter> 1'}"
    show "xa \<in> {p \<sqinter> 1' |p. is_point p \<and> p \<sqsubseteq> x}"
    proof - 
      have a: "xa = (xa;top) \<sqinter> 1' \<and> is_point (xa;top) \<and> (xa;top) \<sqsubseteq> x"
        by (metis CollectD asm1 assms is_partial_point_def is_vector_def le_infE mult_isor mult_oner test_1 ppoint_point)
      thus ?thesis using mem_Collect_eq by blast 
    qed
  qed
qed


lemma card_point_ppoint: 
  assumes "is_vector x" 
  shows   "card {p |p. is_point p \<and> p \<sqsubseteq> x} = card {y|y. is_partial_point y \<and> y \<sqsubseteq> x \<sqinter> 1'}"
proof (rule bij_betw_same_card)
let ?f = "\<lambda>p. p \<sqinter> 1'"
show "bij_betw ?f {p |p. is_point p \<and> p \<sqsubseteq> x} {y |y. is_partial_point y \<and> y \<sqsubseteq> x \<sqinter> 1'}" unfolding bij_betw_def
  proof (intro conjI)
    show "inj_on ?f {p |p. is_point p \<and> p \<sqsubseteq> x}" unfolding inj_on_def
      by (metis CollectD inf_top_right is_point_def vector_3)
    show "?f ` {p |p. is_point p \<and> p \<sqsubseteq> x} = {y |y. is_partial_point y \<and> y \<sqsubseteq> x \<sqinter> 1'}"
      using assms point_ppoint by blast
  qed
qed
  
lemma point_bijection: 
  assumes "is_vector x" 
  shows "card {y|y. \<exists> p. r;p=y \<and> is_point p \<and> p \<sqsubseteq> x} \<le> card {p|p. is_point p \<and> p \<sqsubseteq> x}"
proof (rule surj_card_le)
  show "finite {p |p. is_point p \<and> p \<sqsubseteq> x}"
  using finite_point_p_fun by fastforce
next
  let ?f = "\<lambda>p. r;p"  
  show "{y |y. \<exists>p. r ; p =y \<and> is_point p \<and> p \<sqsubseteq> x} \<subseteq> (?f::'a \<Rightarrow> 'a) ` {p |p. is_point p \<and> p \<sqsubseteq> x}"
    by auto
qed
  
lemma point_inj_cap: 
  assumes "is_vector s" 
  shows  "card {v\<sqinter>1' |v. \<exists>p. r;p=v \<and> is_point p \<and> p \<sqsubseteq> s} \<le> card {v |v. \<exists>p. r;p=v \<and> is_point p \<and> p \<sqsubseteq> s}"
proof (rule surj_card_le)
  show "finite {v |v::'a. \<exists>p::'a. r ; p = v \<and> is_point p \<and> p \<sqsubseteq> s}"
  using finite_point_p_fun' by fastforce
next
  let ?f = "\<lambda>x. x \<sqinter> 1'"  
  show "{v \<sqinter> 1' |v::'a. \<exists>p::'a. r ; p = v \<and> is_point p \<and> p \<sqsubseteq> s} \<subseteq> (?f::'a \<Rightarrow> 'a) ` {v |v::'a. \<exists>p::'a. r ; p = v \<and> is_point p \<and> p \<sqsubseteq> s}"
  proof
    fix x
    assume h: "x \<in> {v \<sqinter> 1' |v::'a. \<exists>p::'a. r ; p = v \<and> is_point p \<and> p \<sqsubseteq> s}"
    show "x \<in> ?f ` {v |v::'a. \<exists>p::'a. r ; p = v \<and> is_point p \<and> p \<sqsubseteq> s}"
    proof - 
      have a: "\<exists>v p. r ; p = v \<and> is_point p \<and> p \<sqsubseteq> s \<and> x = (v \<sqinter> 1')"
        using h by blast
      then show ?thesis 
        using a by blast
    qed
  qed   
qed

  
lemma vector_test: 
  assumes "is_vector x" 
  shows "|x| = |x \<sqinter> 1'|*|1'|"
using assms cardvector card_point_ppoint card_test is_test_def by auto


lemma cardvecpar: 
  assumes "is_vector x"
  and "is_vector y"
  and "|x| \<le> |y|"
  shows "|x \<sqinter> 1'| \<le> |y \<sqinter> 1'|"
proof - 
  have "|x \<sqinter> 1'|*|1'| = |x|"
    by (simp add: assms vector_test)
  also have "\<dots> \<le> |y|"
    by (simp add: assms)               
  also have "\<dots> = |y \<sqinter> 1'|*|1'|"                  
    by (simp add: assms vector_test)
  finally show ?thesis
    by (metis card0_neq inf_bot_right mult_cancel2 mult_le_mono1 nat_le_linear order_class.eq_iff)
qed

lemma idtest: "|1'| \<noteq> 0"
  by (simp add: card0_neq tarski)
    
lemma vector_cap_test: 
  assumes "is_vector x" 
  shows "card {p |p. is_point p \<and> p \<sqsubseteq> x} = |x \<sqinter> 1'|"
proof - 
  have "card {p |p. is_point p \<and> p \<sqsubseteq> x} = card {y|y. is_partial_point y \<and> y \<sqsubseteq> x \<sqinter> 1'}"
    using card_point_ppoint assms by blast 
  also have "\<dots> = |x \<sqinter> 1'|"
    by (simp add: card_test local.is_test_def)
  finally show ?thesis
    by blast
qed
  

lemma sumleq_fun:
  assumes "finite {x. P x}"
  shows   "|\<Squnion> {f x| x. P x}| \<le> (\<Sum> y \<in> {f x| x. P x}. |y| )"
using assms sumleq by auto
end
end


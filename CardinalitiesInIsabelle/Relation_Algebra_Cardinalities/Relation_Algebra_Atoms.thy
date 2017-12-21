(* Title:      Atoms
   Author:     Insa Stucke (ist@informatik.uni-kiel.de)
*)


theory Relation_Algebra_Atoms imports "$AFP/Relation_Algebra/Relation_Algebra"
                                       "$AFP/Relation_Algebra/Relation_Algebra_Functions"
                                       "~~/Relation_Algebra_Cardinalities/Relation_Algebra_Points"
begin

text{* Facts about atom are outsourced to this file. *}

context relation_algebra_fin_points

begin


definition is_atom:: "'a \<Rightarrow> bool"
  where "is_atom x \<equiv> x\<noteq>0 \<and> x\<^sup>\<smile>;1;x \<le> 1' \<and> x;1;x\<^sup>\<smile> \<le> 1'"


lemma topatoms: "\<Squnion> {p;q\<^sup>\<smile>|p q. is_point p \<and> is_point q} = 1" 
proof - 
  have "1 = \<Squnion> {p|p. is_point p};(\<Squnion> {q|q. is_point q})\<^sup>\<smile>"
    using pointaxiom by auto
  also have "\<dots> = \<Squnion> {p|p. is_point p};(\<Squnion> {q\<^sup>\<smile>|q. is_point q})"
    using setsum_fun_add' finiteness by auto 
  also have "\<dots> = \<Squnion> {p;q\<^sup>\<smile>|p q. is_point p \<and> is_point q}"
    using finiteness sum_sum_add_comp by blast 
  finally show ?thesis
    by simp 
qed


lemma pointssetcomp: "{x. \<exists> p q. p;q\<^sup>\<smile>=x \<and> is_point p \<and> is_point q} = {p;q\<^sup>\<smile>|p q. is_point p \<and> is_point q}"
by blast


lemma atompoint: 
  assumes "is_atom x" 
  shows "is_point (x;1)"
proof - 
have a: "is_inj (x;1)"
  by (metis assms is_atom_def conv_contrav conv_one is_inj_def mult_assoc one_idem_mult) 
have b: "(x;1)\<noteq>0"
  using assms is_atom_def ss_p18 by auto 
have c: "is_vector (x;1)"
   by (simp add: comp_assoc is_vector_def)
thus ?thesis
  by (simp add: a b is_point_def)
qed


lemma atompointcnv: 
  assumes "is_atom x" 
  shows "is_point (x\<^sup>\<smile>;1)"
by (metis assms atompoint is_atom_def conv_invol conv_zero)


lemma atompoints: 
  assumes "is_atom x" 
  shows "\<exists> p q. x=p;q\<^sup>\<smile> \<and> is_point p \<and> is_point q"
proof - 
  have hp: "is_point (x;1)"
    using atompoint assms by blast
  have hq: "is_point (x\<^sup>\<smile>;1)"
    using atompointcnv assms by blast
  have "x = (x;1);(x\<^sup>\<smile>;1)\<^sup>\<smile>"
    proof (rule antisym)
      show "x \<le> (x;1);(x\<^sup>\<smile>;1)\<^sup>\<smile>"
        by (metis conv_contrav conv_invol conv_one dedekind inf_top_left one_idem_mult)
      show "(x;1);(x\<^sup>\<smile>;1)\<^sup>\<smile> \<le> x"
        by (metis hq conv_invol conv_one dedekind_var_1 inf.absorb2 inf_top_right one_idem_mult point_cnv_map ss423 top_greatest) 
    qed
  thus ?thesis
    using hp hq by blast
qed

lemma pointsatom: 
  assumes "is_point p" 
  and "is_point q" 
  shows "is_atom (p;q\<^sup>\<smile>)"
proof (unfold is_atom_def, intro conjI)
  show "(p;q\<^sup>\<smile>)\<noteq>0"
    by (simp add: assms comp_points)
  show "(p;q\<^sup>\<smile>)\<^sup>\<smile>;1;(p;q\<^sup>\<smile>) \<le> 1'"
    by (metis assms comp_assoc conv_contrav conv_invol is_inj_def is_point_def is_vector_def points_surj surj_tx)
  show "(p;q\<^sup>\<smile>);1;(p;q\<^sup>\<smile>)\<^sup>\<smile> \<le> 1'"
    by (metis assms conv_contrav conv_one is_inj_def is_point_def is_vector_def mult_assoc points_surj surj_tx)
qed


lemma atomeqpoints: "{x|x. is_atom x} = {x. \<exists> p q. p;q\<^sup>\<smile>=x \<and> is_point p \<and> is_point q}"
proof (rule subset_antisym[OF subsetI subsetI])
  show "\<And>x. x \<in> {x |x. is_atom x} \<Longrightarrow> x \<in> {x. \<exists>p q. p;q\<^sup>\<smile> = x \<and> is_point p \<and> is_point q}"
  using atompoints by fastforce
next 
  show "\<And>x. x \<in> {x. \<exists>p q. p;q\<^sup>\<smile> = x \<and> is_point p \<and> is_point q} \<Longrightarrow> x \<in> {x |x. is_atom x}"
  proof
  fix y::'a
  assume ypoints: "y \<in> {x. \<exists>p q. p;q\<^sup>\<smile> = x \<and> is_point p \<and> is_point q}"
  show "\<exists>x. y = x \<and> is_atom x"
    proof 
      obtain p q where h1: "p;q\<^sup>\<smile> = y \<and> is_point p \<and> is_point q"
        using ypoints by blast  
      have catom: "is_atom (p;q\<^sup>\<smile>)"
        using h1 pointsatom by blast
      show "y = y \<and> is_atom y"
        using catom h1 by blast
    qed
  qed
qed


lemma topatoms': "\<Squnion> {x|x. is_atom x} = 1"
using atomeqpoints pointssetcomp topatoms by auto 


lemma atominj: 
  assumes "is_atom x" 
  shows "is_inj x"
by (meson assms is_atom_def conv_galois_2 dual_order.trans is_inj_def maddux_20)


lemma atompfun: 
  assumes "is_atom x" 
  shows "is_p_fun x"
by (metis assms is_atom_def comp_assoc dual_order.trans is_p_fun_def maddux_21 mult_isol)


lemma atomtrans: 
  assumes "is_atom x" 
  shows "is_trans x"
proof (unfold is_trans_def)
  show "x;x \<le> x"
    proof -
      have "x;x \<le> x;1 \<cdot> 1;x"
        by (simp add: mult_isol_var)
      also have "\<dots> \<le> x;x\<^sup>\<smile>;1;x"
        by (metis inf_top.left_neutral modular_1_var mult.semigroup_axioms semigroup.assoc)
      also have "\<dots> \<le> x"
        using assms is_atom_def comp_assoc mult_isol by fastforce
      finally show ?thesis
        using dual_order.trans is_trans_def by blast
    qed
qed


lemma atomid: 
  assumes "is_atom x" 
  shows "x;x \<le> 1'"
proof - 
  have "x;x \<le> x;x \<cdot> x"
    using assms atomtrans inf_absorb1 is_trans_def by auto
  also have "\<dots>  \<le> (x \<cdot> x;x\<^sup>\<smile>);(x \<cdot> x\<^sup>\<smile>;x)"
    using dedekind by blast
  also have "\<dots> \<le> x;x\<^sup>\<smile>;x\<^sup>\<smile>;x"
    by (metis comp_assoc inf.cobounded2 mult_isol_var)
  also have "\<dots> \<le> 1';x\<^sup>\<smile>;x"
    using assms atominj is_inj_def mult_isor by blast
  finally show ?thesis
    by (metis assms atompfun dual_order.trans is_p_fun_def mult_1_left)
qed


lemma atomdisj: 
  assumes "is_atom x" 
  and "is_atom y" 
  and "x\<noteq>y" 
  shows "x\<cdot>y \<le> 0"
proof - 
  obtain p q where h1: "p ; q\<^sup>\<smile> = x \<and> is_point p \<and> is_point q"
    using assms(1) atompoints by blast 
  obtain r s where h2: "r ; s\<^sup>\<smile> = y \<and> is_point r \<and> is_point s" 
    using assms(2) atompoints by blast 
  have noteq: "p\<noteq>r \<or> q\<noteq>s"
    using assms(3) h1 h2 by blast 
  have noteq: "p\<^sup>\<smile>;r \<le> 0 \<or> s\<^sup>\<smile>;q \<le> 0"
    using h1 h2 noteq pointcompbot by blast
  have "x\<cdot>y = p;q\<^sup>\<smile> \<cdot> r;s\<^sup>\<smile>"
    by (simp add: h1 h2)
  also have "\<dots> \<le> (p \<cdot> r;s\<^sup>\<smile>;q);(q\<^sup>\<smile> \<cdot> p\<^sup>\<smile>;r;s\<^sup>\<smile>)"
    by (metis comp_assoc conv_invol dedekind)
  also have "(p \<cdot> r;s\<^sup>\<smile>;q);(q\<^sup>\<smile> \<cdot> p\<^sup>\<smile>;r;s\<^sup>\<smile>) \<le> 0"
    using bot_unique mult_assoc noteq by fastforce
  finally show ?thesis
    by simp
qed


lemma pwd_points: "pairwise_disjoint {x |x.\<exists> p q. p;q\<^sup>\<smile>=x \<and> is_point p \<and> is_point q}"
using atomdisj le_bot pointsatom pairwise_disjoint_def by auto


lemma pwd_points_eq: "pairwise_disjoint {x |x.\<exists> p. p;p\<^sup>\<smile>=x \<and> is_point p}"
proof - 
  have a: "{x |x.\<exists> p. p;p\<^sup>\<smile>=x \<and> is_point p} \<subseteq> {x |x.\<exists> p q. p;q\<^sup>\<smile>=x \<and> is_point p \<and> is_point q}"
    by blast
  thus ?thesis 
    using pwd_mon pwd_points by blast
qed


lemma atomsareatoms: 
  assumes "is_point p" 
  and "is_point q" 
  and "is_point r" 
  and "is_point s" 
  and "p;q\<^sup>\<smile>=r;s\<^sup>\<smile>"
  shows "p=r \<and> q=s"
proof (rule conjI)
  show "q = s"
  proof - 
    have a: "p \<le> r;s\<^sup>\<smile>;q"
      by (metis assms comp_assoc maddux_20 pointcomptop)
    have b: "r;s\<^sup>\<smile>;q \<noteq> 0"
      by (metis a assms comp_assoc comp_points le_bot points_surj ss_p18 surj_tx)
    have c: "s\<^sup>\<smile>;q \<noteq> 0"
      using b annir comp_assoc by force
    thus ?thesis using assms c pointcompbot by blast
  qed
next 
  show "p=r"
  proof -
    have a: "p;q\<^sup>\<smile>=r;q\<^sup>\<smile>"
      by (metis assms is_point_def is_vector_def mult.semigroup_axioms points_surj surj_tx semigroup.assoc)
    thus ?thesis 
      by (metis assms comp_assoc is_point_def is_vector_def pointcomptop)  
  qed
qed


lemma fin_points: "finite {x |x. \<exists>p q. p;q\<^sup>\<smile> = x \<and> is_point p \<and> is_point q}"
proof - 
  have a: "{x |x. \<exists>p q. p;q\<^sup>\<smile> = x \<and> is_point p \<and> is_point q} = {p;q\<^sup>\<smile>|p q. is_point p \<and> is_point q}"
    by blast
  have b: " finite {p;q\<^sup>\<smile>|p q. is_point p \<and> is_point q}"
    by (metis atomeqpoints bot_unique is_atom_def pointssetcomp sum.infinite top_greatest topatoms' not_finite_existsD)
  thus ?thesis 
    using a by auto
qed


lemma fin_atoms: "finite {x |x. is_atom x}"
proof - 
  have a: "{x |x. is_atom x} = {x |x. \<exists>p q. p;q\<^sup>\<smile> = x \<and> is_point p \<and> is_point q}"
    using atompoints pointsatom by blast
  thus ?thesis 
    using a fin_points by auto
qed


lemma fin_atoms': "finite {x. is_atom x}"
using fin_atoms by auto


lemma fin_atoms_p: "finite {x |x. is_atom x \<and> P x}"
by (simp add: Collect_mono fin_atoms')


lemma atom_lattice_atom: 
  assumes "is_atom x" 
  and "y\<noteq>0" 
  and "y \<le> x"
  shows "y = x"
proof (rule univalent_antisym)
  show "is_p_fun x" 
    by (simp add: assms atompfun)
  show "x; 1 \<le> y;1" 
    by (metis assms atompoint comp_assoc inf_absorb2 is_vector_def mult_subdistr one_idem_mult point_lattice_atom ss_p18)
  show "y \<le> x" 
    by (simp add: assms)
qed


lemma leq_atom_rel: 
  assumes "is_atom x" 
  and "y \<le> x" 
  shows "y=x \<or> y \<le> 0"
using assms atom_lattice_atom by fastforce


lemma leq_atom_rel': 
  assumes "is_atom x" 
  shows "x \<le> y \<or> x \<cdot> y \<le> 0"
by (metis assms leq_atom_rel inf.cobounded1 inf.orderI)


lemma atomrel: 
  assumes "is_atom x"  
  shows "y \<cdot> x \<le> \<Squnion> {x|x. is_atom x \<and> x \<le> y}"
proof - 
   have a: "x \<le> y \<or> x \<cdot> y \<le> 0"
     by (simp add: assms leq_atom_rel')
   then have b: "y \<cdot> x \<le> \<Squnion>{x|x. is_atom x \<and> x \<le> y}"
     proof
       assume asm: "x \<cdot> y \<le> 0"
       show "y \<cdot> x \<le> \<Squnion>{x|x. is_atom x \<and> x \<le> y}"
         using asm antisym bot_least inf.commute by fastforce 
     next
       assume asm: "x \<le> y"
       show "y \<cdot> x \<le> \<Squnion>{x|x. is_atom x \<and> x \<le> y}" 
         proof (rule leq_sum_p)
           show "finite {x. is_atom x \<and> x \<le> y}"
             by (simp add: fin_atoms')
         next
           show "is_atom (y \<cdot> x) \<and> y \<cdot> x \<le> y"
             by (simp add: asm assms inf.absorb2)
         qed
      qed
  thus ?thesis 
    by blast 
qed


lemma atomaux: "\<Squnion> {y \<cdot> x|x. is_atom x} \<le> \<Squnion> {x|x. is_atom x \<and> x \<le> y}"
proof (rule lub_sum_p)
  show "finite {x. is_atom x}"
    by (simp add: fin_atoms')
next
  show "\<forall>x. is_atom x \<longrightarrow> y \<cdot> x \<le> \<Squnion> {x|x. is_atom x \<and> x \<le> y}"
    using atomrel by auto
qed 


lemma relatoms: "\<Squnion> {x|x. is_atom x \<and> x \<le> y} = y"
proof (rule antisym)
  show "\<Squnion>{x|x. is_atom x \<and> x \<le> y} \<le> y"
    by (metis (no_types, lifting) bot_least lub_sum sum.infinite mem_Collect_eq)
next 
  have "y = y \<cdot> \<Squnion> {x|x. is_atom x}"
    using topatoms' by auto
  also have "\<dots> = \<Squnion> {y \<cdot> x|x. is_atom x}"
    using fin_atoms sum_cap_distr_left by auto
  also have "\<dots> \<le> \<Squnion> {x|x. is_atom x \<and> x \<le> y}"
    using atomaux by blast
  finally show "y \<le> \<Squnion>{x|x. is_atom x \<and> x \<le> y}"
    using Collect_cong by auto
qed


definition is_partial_point:: "'a \<Rightarrow> bool"
  where "is_partial_point x \<equiv> is_atom x \<and> is_test x"


lemma sumid_partial_points: "1' = \<Squnion> {x|x. is_partial_point x}"
using relatoms is_partial_point_def is_test_def by auto


lemma test_partial_points: 
  assumes "is_test y" 
  shows "y = \<Squnion> {x|x. is_partial_point x \<and> x \<le> y}"
proof - 
  have a: "{x|x. is_atom x \<and> x \<le> y} = {x|x. is_partial_point x \<and> x \<le> y}"
    using assms is_partial_point_def dual_order.trans is_test_def by blast
  thus ?thesis 
    by (metis relatoms)
qed

lemma fin_partial_points_p: "finite {x |x. is_partial_point x \<and> P x}"
using fin_atoms is_partial_point_def by auto


lemma fin_partial_points_fun: "finite {f x |x. is_partial_point x \<and> P x}"
using finite_image_set fin_partial_points_p by auto


end
end
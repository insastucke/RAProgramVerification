theory CadeInsa
  imports Main "Relation_Algebra/Relation_Algebra" "Relation_Algebra/Relation_Algebra_Functions"  "Relation_Algebra/Relation_Algebra_Models"

begin 

context relation_algebra
begin

(* definitions/predicates *)
definition symmetric :: "'a \<Rightarrow> bool"
  where "symmetric x \<equiv> x=x\<^sup>\<smile>"

definition reflexive :: "'a \<Rightarrow> bool"
  where "reflexive x \<equiv> 1' \<le> x"

definition irreflexive :: "'a \<Rightarrow> bool"
  where "irreflexive x \<equiv> x \<le> -(1')"


(* the used libraries use different notation. We adapted the notions to fit our paper
 in case the definitions are slightly different, we show equivalence *)
definition univalent :: "'a \<Rightarrow> bool"
  where "univalent x \<equiv> x\<^sup>\<smile>;x \<le> 1'"
lemma "univalent x = is_p_fun x"
  by(simp add: univalent_def is_p_fun_def)

definition total :: "'a \<Rightarrow> bool"
  where "total x \<equiv> x;1=1"
lemma total_is_total: "total x = is_total x"
  by (simp add: total_def total_def_var_1)

definition is_function :: "'a \<Rightarrow> bool"
  where "is_function  x \<equiv> univalent x \<and> total x"
lemma "is_function x = is_map x"
  by (simp add: is_function_def is_map_def is_p_fun_def total_def_var_1 total_def univalent_def)

definition injective :: "'a \<Rightarrow> bool"
  where "injective x \<equiv> univalent (x\<^sup>\<smile>)"
lemma "injective x = is_inj x"
  unfolding injective_def is_inj_def univalent_def
  by(simp)

definition surjective :: "'a \<Rightarrow> bool"
  where "surjective x \<equiv> total (x\<^sup>\<smile>)"
lemma "surjective x = is_sur x"
  by(simp add: surjective_def total_is_total is_total_def is_sur_def)

definition coloringProperty
  where "coloringProperty x e \<equiv> x;x\<^sup>\<smile> \<le> -e"

lemmas unfold_defs = symmetric_def reflexive_def irreflexive_def univalent_def total_def is_function_def injective_def surjective_def
                      coloringProperty_def is_p_fun_def is_point_def is_vector_def is_inj_def
(* end definitions *)

(* logical equivalences in the model of relations *)
lemma rel_subset:
  "(\<forall> x y. (x,y) \<in> r \<longrightarrow> (x,y) \<in> s) = (r \<subseteq> s)"
by(auto)

lemma rel_reflexive:  
  "(\<forall> x. (x,x) \<in> r) = (Id \<subseteq> r)"
by(simp add: subset_iff)

lemma rel_irreflexive:  
  "(\<forall> x y. (x,y) \<in> r \<longrightarrow> x \<noteq> y) = (r \<subseteq> -Id)"
by(auto)

lemma rel_transitive:
  "(\<forall> x y z. ((x,y) \<in> r \<and> (y,z) \<in> r) \<longrightarrow> (x,z) \<in> r) = (r O r \<subseteq> r)"
by(auto)

lemma rel_symmetric:
  "(\<forall> x y. (x,y) \<in> r \<longrightarrow> (y,x) \<in> r) = (r =  r\<inverse>)"
by(auto simp add: subset_iff)

lemma rel_antisymmetric:
  "(\<forall> x y. (x,y) \<in> r \<and> (y,x) \<in> r \<longrightarrow> x=y) = (r \<inter> r\<inverse> \<subseteq> Id)"
by(simp add: subset_iff)

lemma rel_asymmetric:
  "(\<forall> x y. (x,y) \<in> r \<longrightarrow> (y,x) \<notin> r) = (r \<inter> r\<inverse> = {})"
by(auto simp add: subset_iff)

lemma rel_total:
  "(\<forall> x y. (x,y) \<in> r \<or> (y,x) \<in> r) = (UNIV = r \<union> r\<inverse>)"
by(auto simp add: subset_iff)
(*end logical equivalences in the model of relations *)

(* main lemmata of the paper *)
lemma lemma31:
 "univalent 0 \<and> coloringProperty 0 e"
 by(simp add: univalent_def coloringProperty_def)

lemma lemma32:
  assumes "univalent x"
      and "is_point p"
      and "is_point q"
      and "p \<le> -(x;1)"
      shows "univalent(x + p;q\<^sup>\<smile>)"  

proof (simp add: unfold_defs distrib_left distrib_right, safe)
(* after unfolding sledgehammer is impressive *)

  from assms(1) show "x\<^sup>\<smile> ; x \<le> 1'"
    by(unfold univalent_def)

  from assms(4) show goal2: "q ; p\<^sup>\<smile> ; x \<le> 1'"
    by (metis compl_bot_eq compl_le_swap1 conv_galois_1 conv_galois_2 conv_one double_compl inf.boundedE inf_compl_bot mult_assoc)

  from goal2 show "x\<^sup>\<smile> ; (p ; q\<^sup>\<smile>) \<le> 1'"
    by (metis conv_contrav conv_invol conv_iso mult_oner)

  from assms(3) and assms(4) show "q;p\<^sup>\<smile>;(p;q\<^sup>\<smile>)  \<le> 1'"
    unfolding unfold_defs
    by (metis dual_order.trans mult_isol mult_isor top_greatest mult_assoc)
qed

lemma lemma33:
  assumes "symmetric e"
      and "irreflexive e"
      and "is_point p"
      and "is_point q"
      and "coloringProperty x e"
      and "q \<le> -(x\<^sup>\<smile> ; e ; p)"
    shows "coloringProperty (x + p;q\<^sup>\<smile>) e"
proof (simp add: unfold_defs distrib_left distrib_right, safe)

  show goal1: "x ; x\<^sup>\<smile> \<le> -e" by (metis assms(5) coloringProperty_def)

  from assms(1) and assms(6) 
  show goal3: "p ; q\<^sup>\<smile> ; x\<^sup>\<smile> \<le> - e"
    by (metis symmetric_def comp_anti conv_galois_1 conv_galois_2 double_compl mult_assoc)

  from goal3 show "x ; (q ; p\<^sup>\<smile>) \<le> - e"
    by (metis assms(6) conv_galois_1 conv_galois_2 conv_invol double_compl)

  from assms(2) and assms(3) and assms(4) show "p ; q\<^sup>\<smile> ; (q ; p\<^sup>\<smile>) \<le> -e"
    unfolding unfold_defs
    by (metis dual_order.trans mult_isol mult_isor top_greatest mult_assoc compl_le_swap1)
qed

lemma lemma21:
  "\<lbrakk> is_point p ; is_point q ; (\<forall> x. (x\<noteq>0 \<longrightarrow> 1 ; x ; 1 = 1)) \<rbrakk> \<Longrightarrow> p\<noteq>0 \<and> p;q\<^sup>\<smile> \<noteq> 0"
unfolding unfold_defs
by (metis mult_assoc sur_def_var1 sur_total total_1)

lemma lemma34:
  assumes "is_point p"
      and "is_point q"
      and "x;1\<noteq>1"
      and "p \<le> -(x;1)"
      and "\<forall> x. (x\<noteq>0 \<longrightarrow> 1 ; x ; 1 = 1)"
      shows "x \<le> x + p;q\<^sup>\<smile> \<and> x \<noteq> x + p;q\<^sup>\<smile> "
proof 
  show "x \<le> x + p;q\<^sup>\<smile>" by simp

  from assms have temp: "p;q\<^sup>\<smile> \<le> -x"
    unfolding is_point_def is_vector_def is_inj_def                                     
    by (metis comp_anti comp_res_aux compl_bot_eq conv_galois_1 conv_galois_2 double_compl le_iff_inf order_trans top_greatest)
  {
    assume "x = x + p;q\<^sup>\<smile>" (* proof by contradiction *)
     with assms(1) and assms(2) and assms(5) have "False" 
     by (metis aux6 inf.orderE inf_compl_bot temp lemma21)
  }
  then show "x \<noteq> x + p;q\<^sup>\<smile>" by blast
qed
    
end
end
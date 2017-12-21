(* Title:      Orders
   Author:     Insa Stucke (ist@informatik.uni-kiel.de)
*)

section {* Relation Algebra Orders *}

theory Relation_Algebra_Orders 
    imports Main "$AFP/Relation_Algebra/Relation_Algebra" 
begin 

context relation_algebra
begin
  
text {* In this theory we define and prove some basic facts about order related relations. *}


definition is_refl :: "'a \<Rightarrow> bool"
  where "is_refl x \<equiv> 1' \<le> x"

definition is_trans :: "'a \<Rightarrow> bool"
  where "is_trans x \<equiv> x ; x \<le> x"

definition is_preorder :: "'a \<Rightarrow> bool"
  where "is_preorder x \<equiv> is_refl x \<and> is_trans x"

definition is_antisym :: "'a \<Rightarrow> bool"
  where "is_antisym x \<equiv> x \<cdot> x\<^sup>\<smile> \<le> 1'"

definition is_order :: "'a \<Rightarrow> bool"
  where "is_order x \<equiv> is_refl x \<and> is_antisym x \<and> is_trans x"

definition is_irrefl :: "'a \<Rightarrow> bool"
  where "is_irrefl x \<equiv> x \<le> -1'"

definition is_asym :: "'a \<Rightarrow> bool"
  where "is_asym x \<equiv> x \<cdot> x\<^sup>\<smile> \<le> 0"

definition is_lin :: "'a \<Rightarrow> bool"
  where "is_lin x \<equiv> x + x\<^sup>\<smile> = 1"

definition is_strictorder :: "'a \<Rightarrow> bool"
  where "is_strictorder x \<equiv> is_asym x \<and> is_trans x"



lemma reflone: "is_refl 1'"
by (simp add: is_refl_def)

lemma transone: "is_trans 1'"
by (simp add: is_trans_def)

lemma antisymmone: "is_antisym 1'"
by (simp add: is_antisym_def)

lemma preorderone: "is_preorder 1'"
by (simp add: is_preorder_def reflone transone)

lemma orderone: "is_order 1'"
by (simp add: antisymmone is_order_def reflone transone)



lemma reflcup: "is_refl x \<and> is_refl y \<longrightarrow> is_refl (x + y)"
by (simp add: is_refl_def le_supI2)

lemma reflcap: "is_refl x \<and> is_refl y \<longrightarrow> is_refl (x \<cdot> y)"
by (simp add: is_refl_def)

lemma reflcomp: "is_refl x \<and> is_refl y \<longrightarrow> is_refl (x ; y)"
by (metis is_refl_def mult_oner subdistl sup.boundedE sup_absorb2)

lemma transcap: "is_trans x \<and> is_trans y \<longrightarrow> is_trans (x \<cdot> y)"
by (meson is_trans_def inf_mono meet_interchange order.trans)

lemma preordercap: "is_preorder x \<and> is_preorder y \<longrightarrow> is_preorder (x \<cdot> y)"
by (simp add: is_preorder_def reflcap transcap)

lemma antisymcap: "is_antisym x \<and> is_antisym y \<longrightarrow> is_antisym (x \<cdot> y)"
by (meson is_antisym_def conv_self_conjugate_var dual_order.trans g_subdist inf.boundedI inf.cobounded1 inf.cobounded2)

lemma ordercap: "is_order x \<and> is_order y \<longrightarrow> is_order (x \<cdot> y)"
by (simp add: antisymcap is_order_def reflcap transcap)

lemma irreflcup: "is_irrefl x \<and> is_irrefl y \<longrightarrow> is_irrefl (x + y)"
by (simp add: is_irrefl_def)

lemma irreflcap: "is_irrefl x \<and> is_irrefl y \<longrightarrow> is_irrefl (x \<cdot> y)"
by (simp add: is_irrefl_def inf.coboundedI1)


lemma aux_refl_anti_lin: 
  assumes "is_refl x" 
  and "is_antisym x" 
  and "is_lin x" 
  shows "x\<^sup>\<smile> = 1' + -x"
proof (rule antisym)
  show "x\<^sup>\<smile> \<le> 1' + -x"
    using assms(2) is_antisym_def galois_2 inf_commute by auto
  show "1' + -x \<le> x\<^sup>\<smile>"
    using assms(1) assms(3) is_lin_def is_refl_def conv_iso galois_aux4 by fastforce
qed

lemma aux_card_lin_ord: "is_refl x \<and> is_antisym x \<longrightarrow> x \<cdot> x\<^sup>\<smile> = 1'"
  using is_antisym_def is_refl_def antisym conv_iso by fastforce

end

end
(* Title:      Points
   Author:     Insa Stucke (ist@informatik.uni-kiel.de)
*)


theory Relation_Algebra_Points imports "$AFP/Relation_Algebra/Relation_Algebra"
                                       "$AFP/Relation_Algebra/Relation_Algebra_Vectors"
                                       "~~/Relation_Algebra_Cardinalities/Relation_Algebra_Orders"
                                       "~~/Relation_Algebra_Cardinalities/Relation_Algebra_Tarski"
                                       "~~/Relation_Algebra_Cardinalities/Relation_Algebra_Sums"
begin

text{* Here we define the Point Axiom and assume that we deal with finite relations. *}

class relation_algebra_fin_points = relation_algebra_tarski +
  assumes finiteness:       "finite {x. is_point x}" 
  and     pointaxiom [simp]:"\<Squnion> {x. is_point x} = top"


context relation_algebra_fin_points

begin

lemma compvecpoi: 
  assumes "is_point p" 
  shows "is_vector (x;p)"
using assms local.comp_assoc local.is_point_def local.is_vector_def by auto


lemma pointvec: 
  assumes "is_point x" 
  and "is_vector y" 
  shows "y \<cdot> x \<le> \<Squnion>{p |p. is_point p \<and> p \<le> y}"
proof - 
   have a: "x \<le> y \<or> x \<cdot> y \<le> 0"
     by (simp add: assms leq_point_vect')
   then have b: "y \<cdot> x \<le> \<Squnion>{p |p. is_point p \<and> p \<le> y}"
    proof
      assume asm: "x \<cdot> y \<le> 0"
      show "y \<cdot> x \<le> \<Squnion>{p |p. is_point p \<and> p \<le> y}"
        using asm antisym bot_least inf.commute by fastforce 
    next
      assume asm: "x \<le> y"
      show "y \<cdot> x \<le> \<Squnion>{p |p. is_point p \<and> p \<le> y}" 
      proof (rule leq_sum_p)
          show "finite {x. is_point x \<and> x \<le> y}"
            by (simp add: finiteness)
        next
          show "is_point (y \<cdot> x) \<and> y \<cdot> x \<le> y"
            by (simp add: asm assms(1) inf.absorb2)
        qed
    qed
 thus ?thesis
   by blast 
qed


lemma pointaux: 
  assumes "is_vector y" 
  shows "\<Squnion> {y \<cdot> p |p. is_point p} \<le> \<Squnion> {p |p. is_point p \<and> p \<le> y}"
using lub_sum_p assms pointvec finiteness by blast


lemma pointax' [simp]: 
  assumes "is_vector x" 
  shows "\<Squnion> {p. is_point p \<and> p \<le> x} = x"
proof (rule antisym)
  show "\<Squnion>{p. is_point p \<and> p \<le> x} \<le> x"
    by (metis (no_types, lifting) bot_least lub_sum sum.infinite mem_Collect_eq)
next
  have "x = x \<cdot> \<Squnion> {p |p. is_point p}"
    using pointaxiom by auto
  also have "\<dots> = \<Squnion> {x \<cdot> p |p. is_point p}"
    using pointaxiom finiteness sum_cap_distr_left by blast
  also have "\<dots> \<le> \<Squnion> {p |p. is_point p \<and> p \<le> x}"
    using assms pointaux by blast
  finally show "x \<le> \<Squnion>{p. is_point p \<and> p \<le> x}"
    using Collect_cong by auto
qed


lemma point_sum_add_comp: "x; (\<Squnion>{p\<^sup>\<smile>|p. is_point p \<and> p \<le> y}) = \<Squnion>{x;p\<^sup>\<smile>|p. is_point p \<and> p \<le> y}"
by (simp add: finiteness sum_comp_distr_right_fun)


lemma sumid [simp]: "\<Squnion> {p ; p\<^sup>\<smile>|p . is_point p}=1'"  
proof (rule antisym)
  have "1' = 1' \<cdot> \<Squnion>{p |p. is_point p}"
    using pointaxiom by auto
  also have "\<dots>= \<Squnion>{1' \<cdot> p |p. is_point p}"
    using finiteness sum_cap_distr_left by blast
  also have "\<dots> \<le> \<Squnion> {p ; p\<^sup>\<smile>|p . is_point p}"
    proof (rule sum_leq)
      show "finite {x. is_point x}"
        by (simp add: finiteness)
    next 
      show "\<forall>x. is_point x \<longrightarrow> 1' \<cdot> x \<le> x ; x\<^sup>\<smile>"
        by (metis inf.boundedE maddux_20 meet_isor one_conv)
    qed
  finally show "1' \<le> \<Squnion>{p ; p\<^sup>\<smile> |p. is_point p}"
    by blast
next 
  show "\<Squnion>{p ; p\<^sup>\<smile> |p. is_point p} \<le> 1'"
    proof (rule lub_sum)
      show "finite {p ; p\<^sup>\<smile> |p. is_point p}"
        by (simp add: finiteness)
    next
      show "\<forall>x\<in>{p ; p\<^sup>\<smile> |p. is_point p}. x \<le> 1'"
        using is_inj_def is_point_def by blast
  qed
qed


lemma finite_point_p_fun: "finite {f x| x. is_point x \<and> P x}"
by (simp add: finiteness)


lemma card_leq_im: 
  assumes "finite {x. P x}" 
  shows "card {f x| x.  P x} \<le> card {x|x.  P x} "
by (simp add: setcompr_eq_image assms card_image_le)


lemma finite_point_p_fun': "finite {x| x. \<exists> p. f p= x \<and> is_point p \<and> P p}"
proof - 
  have a: "{x| x. \<exists> p. f p= x \<and> is_point p \<and> P p} = {f p| p. is_point p \<and> P p}" 
    by metis
  have b: "card {f p| p. is_point p \<and> P p} \<le> card {p| p. is_point p \<and> P p}"
    using card_leq_im finiteness by blast 
  thus ?thesis 
    using a finite_point_p_fun by fastforce 
qed



lemma finite_point_fun': "finite {x |x. \<exists>p. f p = x \<and> is_point p }" 
proof - 
  have a: "{x |x. \<exists>p. f p = x \<and> is_point p } = {f x |x. is_point x}" 
    by metis 
  have b: "finite  {f x |x. is_point x}"
    by (simp add: finiteness) 
  thus ?thesis 
    using a by auto 
qed


lemma conv_sum: 
  assumes "finite {x|x. P x}" 
  shows "(\<Squnion> {x|x . P x })\<^sup>\<smile> = \<Squnion>({x\<^sup>\<smile>|x. P x })"
using setsum_fun_add' finiteness assms by auto 


lemma pointssetcomp: "{x. \<exists> p q. p;q\<^sup>\<smile>=x \<and> is_point p \<and> is_point q} = {p;q\<^sup>\<smile>|p q. is_point p \<and> is_point q}"
by blast


lemma pointneqdisjp: 
  assumes "is_point x" 
  and "is_point y" 
  and "x\<noteq>y" 
  shows "x \<le> -y"
using assms dual_order.antisym galois_aux inf.commute is_point_def le_bot leq_point_vect' by blast


lemma pointcompbot: 
  assumes "is_point x" 
  and "is_point y" 
  and "x\<noteq>y" 
  shows "x\<^sup>\<smile>;y = 0"
by (metis assms compl_bot_eq double_compl galois_aux2 is_point_def is_vector_def schroeder_1 top_unique pointneqdisjp)


lemma pointcomptop: 
  assumes "is_point x" 
  and "is_point y" 
  and "x=y" 
  shows "x\<^sup>\<smile>;y = 1"
proof - 
  have a: "y;1 \<le> x"
    using assms(2) assms(3) is_point_def is_vector_def by auto
  have b: "1;y\<^sup>\<smile> \<le> x\<^sup>\<smile>"
    using a conv_iso by fastforce
  have c: "-(x\<^sup>\<smile>);y \<le> 0"
    using b conv_galois_2 by auto
  show "x\<^sup>\<smile>;y = 1"
    using assms(2) b ss423 top_unique point_cnv_map by auto
qed



lemma compl_total:
  assumes "is_total x"
  shows "-(x;y) \<le> x;-y"
using assms ss424i by auto


lemma compl_inj:
  assumes "is_inj y"
  shows "-x;y \<le> -(x;y)"
by (metis assms conv_compl conv_contrav conv_invol conv_iso is_inj_def is_p_fun_def p_fun_compl)


lemma compl_sur:
  assumes "is_sur y"
  shows "-(x;y) \<le> -x;y"
by (metis assms compl_total conv_compl conv_contrav conv_iso sur_total)


lemma total_one': "is_total x \<Longrightarrow> top;x\<^sup>\<smile> = top"
by (metis conv_contrav conv_one total_def_var_1)

definition "is_linear x \<longleftrightarrow> x + x\<^sup>\<smile> = top"


lemma pointscompleq: 
  assumes "is_point p"
  shows "-x;p = -(x;p)"
using assms compl_inj compl_sur local.antisym_conv local.is_point_def local.points_surj by blast


text{* Set of points is nonempty. *}
(*
lemma pointsnotempty: "{y . is_point y} \<noteq> {}"
using pointaxiom tarski by fastforce


lemma pointscompnotempty: "{x;y |y . is_point y} \<noteq> {}"
using pointsnotempty by blast
*)

lemma vectorcontpoint: 
  assumes "is_vector v"
  and "v \<noteq> bot"
  shows "{y |y . is_point y \<and> y \<le> v} \<noteq> {}"
proof - 
  have a: " \<Squnion> {p. is_point p \<and> p \<le> v} = v" 
    by (simp add : assms)
  have b: "\<Squnion> {p. is_point p \<and> p \<le> v} \<noteq> bot"
    by (simp add: a assms(2))
  thus ?thesis
    by (metis (mono_tags, lifting) Collect_empty_eq sum.empty)
qed
  
  
lemma vectorparcap: 
  assumes "is_vector x"
  and "is_vector y"
  and "x\<cdot>1' \<le> y\<cdot>1'"
  shows "x \<le> y"
  by (metis assms(1) assms(2) assms(3) local.inf.orderE local.inf_absorb2 local.mult_subdistr local.top_greatest local.vector_3)

end
end
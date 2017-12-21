(* Title:      Sums
   Author:     Insa Stucke (ist@informatik.uni-kiel.de)
*)

theory Relation_Algebra_Sums imports Groups "$AFP/Relation_Algebra/Relation_Algebra_Functions"

begin

text{* We provide the basics to reason about finite unions in relation algebras . Especially, 
if one wants to deals with the Point Axiom many of the following properties are necessary. 

In cardinalities.thy we often use another notation for set. Thus, we have to tackle problems 
concerning this by proving some of the results for both representations. *}

declare [[show_sorts,show_types]]

context relation_algebra
begin

abbreviation Summ ("\<Squnion>_" [1000] 999)
  where "Summ \<equiv> comm_monoid_add.sum op + 0 (\<lambda>x . x)"


lemma leq_sum:
  assumes "finite X"
  and "x \<in> X"
  shows "x \<le> \<Squnion>X"
using assms sum.remove by fastforce

lemma leq_sum_p:
  assumes "finite { x . P x }"
  and "P y"
  shows "g y \<le> \<Squnion> { z. \<exists> x. z= g x \<and> P x }"
proof -
  have "finite { g x | x . P x }"
    by (simp add: assms)
  thus ?thesis
    using assms leq_sum by blast
qed

lemma lub_sum:
  assumes "finite X"
  and "\<forall>x\<in>X . x \<le> y"
  shows "\<Squnion>X \<le> y"
proof -
  have "(\<forall>x\<in>X . x \<le> y) \<longrightarrow> \<Squnion>X \<le> y"
    by (rule finite_induct) (simp_all add: assms)
  thus ?thesis
    by (simp add: assms)
qed


lemma setsum_sup:
  assumes "finite X"
  shows "\<Squnion>X \<le> y \<longleftrightarrow> (\<forall>x \<in> X. x \<le> y)"
using assms dual_order.trans lub_sum leq_sum by blast


lemma lub_sum_p:
  assumes fin: "finite { x . P x }"
  and ub: "\<forall>x . P x \<longrightarrow> f x \<le> y"
  shows "\<Squnion> { f x | x . P x } \<le> y"
proof -
  have "finite { f x | x . P x }"
    by (simp add: fin)
  thus ?thesis
    using lub_sum ub by auto
qed


lemma sum_leq:
  assumes fin: "finite { x . P x }"
  assumes leq: "\<forall>x . P x \<longrightarrow> f x \<le> g x"
  shows "\<Squnion> { f x | x . P x } \<le> \<Squnion> { g x | x . P x }"
proof (rule lub_sum_p)
  show "finite { x . P x }"
    by (simp add: fin)
next
  have "\<forall>x . P x \<longrightarrow> g x \<le> \<Squnion> { g x | x . P x }"
    by (simp add: fin leq_sum_p)
  thus "\<forall>x . P x \<longrightarrow> f x \<le> \<Squnion> { g x | x . P x }"
    using leq order.trans by blast
qed


lemma setsum_fun_add:
  assumes "finite { x . P x }"
  and fstrict: "f 0 = 0"
  and fadd: "\<And>x y. f (x + y) = f x + f y"
  shows "f (\<Squnion> { x . P x }) = \<Squnion>(f ` { x . P x })"
proof (induct rule: finite_induct[OF assms(1)])
  show "f (\<Squnion>{}) = \<Squnion>(f ` {})"
    by (simp add: fstrict)
  fix x :: 'a and  F ::" 'a set"
  assume finF: "finite F"
    and indhyp: "f (\<Squnion>F) = \<Squnion>(f ` F)"
  have "f (\<Squnion>(insert x F)) = f x + \<Squnion>(f ` F)"
    by (metis finF insert_absorb less_eq_def sum.insert leq_sum fadd indhyp)
  also have "... = \<Squnion>(f ` (insert x F))"
    by (metis (mono_tags, lifting) finF finite_imageI image_insert leq_sum local.less_eq_def local.sum.insert_if)
  finally show "f (\<Squnion>(insert x F)) = \<Squnion>(f ` insert x F)" .
qed



lemma setsum_fun_add':
  assumes "finite { x . P x }"
  and fstrict: "f 0 = 0"
  and fadd: "\<And>x y. f (x + y) = f x + f y"
  shows "f (\<Squnion> {x|x . P x }) = \<Squnion>({f x |x. P x })"
by (simp add: assms(1) fadd fstrict image_Collect setsum_fun_add)


lemma add_sum: 
  assumes "finite F"
  shows "y + \<Squnion> F = \<Squnion> (insert y F)"
by (metis assms insert_absorb sum.insert sum.insert_remove sup.left_idem)


text{* Next we prove some distributivity laws. *}


lemma finite_p_fun: 
  assumes "finite {x| x . P x }" 
  shows "finite {f x| x. P x }"
proof -
  have a: "f ` {x| x . P x } = {f x| x. P x }"
    by auto
  thus ?thesis using assms by auto
qed
                    

lemma sum_comp_distr_right:
  assumes "finite { x . P x }"
  shows "y;\<Squnion> {x|x . P x } = \<Squnion>{y;x| x. P x}"
by (simp add: assms image_Collect distrib_left setsum_fun_add)
                               
lemma sum_comp_distr_right_fun: 
  assumes "finite { x . P x }"
  shows "y;\<Squnion> {f x|x. P x } = \<Squnion>{y;(f x)| x. P x}"
proof - 
  have "y;\<Squnion> {f x|x. P x } = y;\<Squnion> {z|z .\<exists>x. f x=z \<and> P x}" by metis
  also have "\<dots> = \<Squnion>{y;z|z .\<exists>x. f x=z \<and> P x}"
    proof (rule sum_comp_distr_right)
      show "finite {z.\<exists>x. f x=z \<and> P x}"
        proof - 
          have a: "{z|z .\<exists>x. f x=z \<and> P x} = {f x | x. P x}" by blast
          thus ?thesis by (simp add: assms finite_image_set)
        qed
    qed
  also have "\<dots> = \<Squnion>{y;f x| x. P x}" by metis
  finally show ?thesis
    by blast 
qed     


lemma sum_comp_distr_left:
  assumes "finite {x . P x }"
  shows "(\<Squnion> {x|x . P x });y = \<Squnion>{x;y| x. P x}"
proof (rule setsum_fun_add')
  show "finite {x::'a. P x}" 
    by (simp add: assms)
  next 
  show "0 ; y = 0" 
    by simp
  next 
  show "\<And>(x::'a) ya::'a. (x + ya) ; y = x ; y + ya ; y" 
    by simp
qed


lemma sum_cap_distr_left: 
  assumes "finite {x . P x}"
  shows "y \<cdot> \<Squnion> {x | x . P x} = \<Squnion> {y \<cdot> x | x . P x}"
using setsum_fun_add' assms inf_sup_distrib1 by simp


lemma sum_cap_distr_right: 
  assumes "finite {x . P x}"
  shows "\<Squnion> {x | x . P x} \<cdot> y = \<Squnion> {x\<cdot>y | x . P x}"
  using inf_commute assms sum_cap_distr_left inf_commute by auto
    

lemma sum_cap_distr_right_fun: 
  assumes "finite {x . P x}"
  shows "\<Squnion> {f x | x . P x} \<cdot> y = \<Squnion> {(f x)\<cdot>y | x . P x}"
proof - 
  have "\<Squnion> {f x | x . P x} \<cdot> y = \<Squnion> {z|z .\<exists>x. f x=z \<and> P x} \<cdot> y" 
    by metis
  also have "\<dots> = \<Squnion>{z\<cdot>y|z .\<exists>x. f x=z \<and> P x}"
    proof (rule sum_cap_distr_right)
      show "finite {z.\<exists>x. f x=z \<and> P x}"
        proof - 
          have a: "{z|z .\<exists>x. f x=z \<and> P x} = {f x | x. P x}" by blast
          thus ?thesis by (simp add: assms finite_image_set)
        qed
    qed
  also have "\<dots> = \<Squnion>{(f x)\<cdot>y| x. P x}" 
    by metis
  finally show ?thesis
    by blast 
qed     
  
(*
lemma sum_cap_distr_right_f: 
  assumes "finite {x . P x}"
  shows "\<Squnion> {f x | x . P x} \<cdot> y = \<Squnion> {(f x)\<cdot>y | x . P x}"
lemma sum_cap_distr_right': 
  assumes "finite {x |x . P x}"
  shows "\<Squnion> {x | x . P x} \<cdot> y = \<Squnion> {x\<cdot>y | x . P x}"
proof (rule sum_cap_distr_right)
  show "finite {x. P x}" 
    using assms by auto 
qed
*)


lemma sum_cap_distr_left_set: 
  assumes "finite F"
  shows "y \<cdot> \<Squnion> {x | x . x\<in>F} = \<Squnion> {y \<cdot> x | x . x\<in>F}"
proof (rule sum_cap_distr_left)
  show "finite {x::'a. x \<in> F}"
    by (simp add: assms)
qed


lemma sum_cap_distr_left_set': 
  assumes "finite F"
  shows "y \<cdot> \<Squnion> F = \<Squnion> {y \<cdot> x | x . x\<in>F}"
using assms sum_cap_distr_left_set by auto


lemma sum_sum_comp: 
  assumes  "finite {x . Q x}"
  shows "\<Squnion>{x;\<Squnion>{y|y . Q y}|x . P x} = \<Squnion>{\<Squnion>{x;y|y . Q y}|x . P x}"
using assms sum_comp_distr_right by auto


lemma setsum_fun_image_sup:
  assumes "finite A"
  shows "\<Squnion>(f ` A) \<le> z \<longleftrightarrow> (\<forall>x \<in> A. f x \<le> z)"
by (simp add: assms setsum_sup)

text{* The proofs of the following two lemmata follow the ones in in Kleene Algebra. *}

lemma flatten1_im:
  assumes "finite (A :: 'a set)"
  and "finite (B :: 'a set)"
  shows "\<Squnion>((\<lambda>x. \<Squnion>(f x ` B)) ` A) = \<Squnion>((\<lambda>p. f (fst p) (snd p)) ` (A \<times> B))"
proof -
  have "\<forall>z. \<Squnion>((\<lambda>x. \<Squnion>(f x ` B)) ` A) \<le> z \<longleftrightarrow> \<Squnion>((\<lambda>p. f (fst p) (snd p)) ` (A \<times> B)) \<le> z"
    by (simp add: assms finite_cartesian_product setsum_fun_image_sup)
  thus ?thesis
    using antisym by blast
qed


lemma flatten1_im_p:
  assumes "finite {x. P x }"
  and "finite {x. Q x }"
  shows "\<Squnion>((\<lambda>x. \<Squnion>(f x ` {x. Q x })) ` {x. P x }) = \<Squnion>((\<lambda>p. f (fst p) (snd p)) ` ({x. P x } \<times> {x. Q x }))"
proof -
  have "\<forall>z. \<Squnion>((\<lambda>x. \<Squnion>(f x ` {x. Q x })) ` {x. P x }) \<le> z \<longleftrightarrow> \<Squnion>((\<lambda>p. f (fst p) (snd p)) ` ({x. P x } \<times> {x. Q x })) \<le> z"
    by (simp add: assms finite_cartesian_product setsum_fun_image_sup)
  thus ?thesis
    using antisym by blast
qed


lemma setsum_flatten1:
  assumes "finite (A :: 'a set)"
  and "finite (B :: 'a set)"
  shows "\<Squnion>{\<Squnion>{f x y |y. y \<in> B} |x. x \<in> A} = \<Squnion>{f x y |x y. x \<in> A \<and> y \<in> B}"
 apply (simp add: Setcompr_eq_image assms flatten1_im)
 apply (subst Setcompr_eq_image[symmetric])
 apply simp
done

lemma setsum_flatten1_p:
  assumes "finite {x|x ::'a. P x}"
  and "finite {x|x ::'a. Q x}"
  shows "\<Squnion>{\<Squnion>{f x y |y. P y} |x. Q x} = \<Squnion>{f x y |x y. Q x \<and> P y}"
proof -
  have "\<Squnion>{\<Squnion>{f x y |y. P y} |x. Q x} = \<Squnion>{\<Squnion>{f x y |y. y\<in> {z . P z}} |x. x \<in> {z . Q z}}"
    by simp
  also have "\<dots> = \<Squnion>{f x y |x y. x \<in> {z . Q z} \<and> y\<in> {z . P z}}"
    proof (rule setsum_flatten1)
      show "finite {z. Q z}"
        using assms by auto
      next
      show "finite {z. P z}"
        using assms by auto
    qed
  also have "\<dots> = \<Squnion>{f x y |x y. Q x \<and> P y}"
    by simp
  finally show ?thesis by auto
qed

  
lemma sum_sum_add_comp: 
  assumes "finite {x . P x}" 
  and "finite {y . Q y}"
  shows "\<Squnion>{x|x . P x};\<Squnion>{y\<^sup>\<smile>|y . Q y} = \<Squnion>{x;y\<^sup>\<smile>| x y. P x \<and> Q y}"
proof - 
  have aux: "{y\<^sup>\<smile>|y . Q y}={z|z .\<exists>x. x\<^sup>\<smile>=z \<and>  Q x}"
    by blast
  have "\<Squnion>{x|x . P x};\<Squnion>{y\<^sup>\<smile>|y . Q y} = \<Squnion>{x;\<Squnion>{y\<^sup>\<smile>|y . Q y}|x . P x}"
    using assms(1) sum_comp_distr_left by blast
  also have "\<dots> = \<Squnion>{x;\<Squnion>{z|z .\<exists>x. x\<^sup>\<smile>=z \<and>  Q x}|x . P x}"
    by (simp add: aux)
  also have "\<dots> = \<Squnion>{\<Squnion>{x;z|z .\<exists>x. x\<^sup>\<smile>=z \<and>  Q x}|x . P x}"
    proof (rule sum_sum_comp)
      show "finite {x. \<exists>xa. xa\<^sup>\<smile> = x \<and> Q xa}"
        proof - 
          have a: "{x. \<exists>z. z\<^sup>\<smile> = x \<and> Q z}={x\<^sup>\<smile> | x. Q x}"
            by blast
          thus ?thesis by (simp add: assms finite_image_set)
        qed
    qed
  also have "\<Squnion>{\<Squnion>{x;z|z .\<exists>x. x\<^sup>\<smile>=z \<and> Q x}|x . P x}= \<Squnion>{x;z|x z. P x \<and> (\<exists>y. y\<^sup>\<smile>=z \<and> Q y)}"
    proof (rule setsum_flatten1_p)
      show "finite {x |x. \<exists>xa. xa\<^sup>\<smile> = x \<and> Q xa}"
        by (metis assms(2) aux finite_imageI image_Collect)
      next
      show "finite {x |x. P x}"
        using assms(1) by auto
    qed
  also have "\<dots> = \<Squnion>{x;y\<^sup>\<smile>| x y. P x \<and> Q y}"
    by metis
  finally show ?thesis by auto
qed


text{* Definition of pairwise disjoint and some properties. *}


definition pairwise_disjoint:: "'a set \<Rightarrow> bool"
  where "pairwise_disjoint F \<equiv> \<forall> x y. x\<in>F \<and> y\<in>F \<and> x\<noteq>y \<longrightarrow> x\<cdot>y=0"


lemma pwd_insert: 
  assumes "pairwise_disjoint (insert x F)" 
  shows "\<forall> y. y\<in>F \<and> x\<noteq>y \<longrightarrow> x\<cdot>y=0"
using assms pairwise_disjoint_def by auto


lemma pwdset: 
  assumes "finite F"
  and "pairwise_disjoint (insert x F)"
  and "x\<notin>F" 
  shows "\<Squnion>{x \<cdot> y| y. y\<in> F} = 0"
proof (rule antisym)
  show "\<Squnion>{x \<cdot> y |y. y \<in> F} \<le> 0"
    proof (rule lub_sum_p)
      show "finite {x. x \<in> F}"
        by (simp add: assms)
    next 
      show "\<forall>xa. xa \<in> F \<longrightarrow> x \<cdot> xa \<le> 0"
        using assms pwd_insert by blast
    qed
next 
  show "0 \<le> \<Squnion>{x \<cdot> y |y::'a. y \<in> F}"
    by simp
qed 


lemma pwd_mon: 
  assumes "A\<subseteq>B" 
  and "pairwise_disjoint B" 
  shows "pairwise_disjoint A"
by (meson assms pairwise_disjoint_def subset_iff)

(*
lemma aux_sum: "{x |x. P x \<or> Q x} = {x |x. P x} + {x |x. Q x}"
by auto

lemma aux_sum': "finite A \<and> finite B \<longrightarrow> \<Squnion> (A+B) = \<Squnion>A + \<Squnion>B"
using setsum.union_diff2 setsum.union_inter by fastforce

lemma aux_sum'': 
  assumes "finite {x |x. P x}" 
  shows "\<Squnion>{x |x. P x} = \<Squnion>{x |x. P x \<and> Q x} + \<Squnion>{x |x. P x \<and> \<not>(Q x)}"
proof - 
  have aux: "{x |x. (P x \<and> Q x) \<or> (P x \<and> \<not>(Q x))} = {x |x. P x \<and> Q x} + {x |x. P x \<and> \<not>(Q x)}"
    by auto
  have "\<Squnion>{x |x. P x} = \<Squnion>{x |x. (P x \<and> Q x) \<or> (P x \<and> \<not>(Q x))}"
    by meson
  also have "\<dots> = \<Squnion>{x |x. P x \<and> Q x} + \<Squnion>{x |x. P x \<and> \<not>(Q x)}"
    using assms aux_sum' aux  by auto
  finally show ?thesis
    by auto
qed

*)

end
end
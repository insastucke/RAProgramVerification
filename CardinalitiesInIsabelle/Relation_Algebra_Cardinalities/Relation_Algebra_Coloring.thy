(* Title:      Coloring
   Author:     Insa Stucke (ist@informatik.uni-kiel.de)
*)

theory Relation_Algebra_Coloring imports  "~~/src/HOL/Hoare/Hoare_Logic" 
                                          "~~/Relation_Algebra_Cardinalities/Relation_Algebra_Orders"
                                          "~~/Relation_Algebra_Cardinalities/Relation_Algebra_Cardinal" 
begin

text{* This theory contains the relational program for approximating 
a vertex coloring of an undirected graph. The correctness proof is done by using 
Hoare logic. *}


declare [[show_sorts,show_types]]

text{* minpoint is a function selecting a point contained in a nonempty vector. It is defined by 
the following properties. *}

class minpoint =
  fixes minpoint :: "'a \<Rightarrow> 'a" 

class relation_algebra_minpoint = relation_algebra_card + minpoint +
  assumes minpoint_sub:  "is_vector x \<and> x \<noteq> bot \<longrightarrow> minpoint x \<le> x" 
  and     minpoint_point:"is_vector x \<and> x \<noteq> bot \<longrightarrow> is_point (minpoint x)"
  and     minpoint_empty:"x = bot \<longrightarrow> minpoint x = bot"

context relation_algebra_minpoint 
  begin


text{* ";" is a symbol used in Hoare_Logic, thus we have to change the notation here.*}

no_notation
  composition (infixl ";" 75)
notation
  composition (infixl "\<bullet>" 75)


(*
(* We omit the proof of the coloring property here since it has already been done in [2]. *)
definition has_color_prop  :: "'a \<Rightarrow> 'a  \<Rightarrow> bool"
  where "has_color_prop e c \<equiv> c\<bullet>c\<^sup>\<smile> \<sqsubseteq> ~e"
*)

text{* Below we define the maximum degree and prove some properties about it. *}

definition max_deg  :: "'a \<Rightarrow> nat"
  where "max_deg x \<equiv> Max { |x\<bullet>y \<sqinter> 1'| |y . is_point y}"


definition max_degv  :: "'a \<Rightarrow> 'a \<Rightarrow> nat"
  where "max_degv x v \<equiv> Max { |x\<bullet>y \<sqinter> 1'| |y . is_point y \<and> y \<sqsubseteq> v}"

lemma maxdegtop: "max_degv x top = max_deg x"
using max_deg_def max_degv_def by auto


lemma maxdegin: 
  assumes "is_vector v"
  and "v \<noteq> bot"
  shows "{ |x\<bullet>y \<sqinter> 1'| |y . is_point y \<and> y \<sqsubseteq> v} \<noteq> {}"
using assms vectorcontpoint by blast




lemma mon_max_degv: 
  assumes "x \<sqsubseteq> y"
  and "is_vector x \<and> is_vector y"
  and "x \<noteq>bot"
  and "y \<noteq>bot"
  shows "max_degv e x \<le> max_degv e y" 
unfolding max_degv_def
proof - 
  have aux: "Max {|e\<bullet>z \<sqinter> 1'| |z. is_point z \<and> z \<sqsubseteq> x} \<in> { |e\<bullet>z\<sqinter> 1'| |z . is_point z \<and> z \<sqsubseteq> x}"
    proof (rule Max_in)
      show "finite {|e\<bullet>z \<sqinter> 1'| |z. is_point z \<and> z \<sqsubseteq> x}" 
        by (simp add: finite_point_p_fun)
      next 
      show "{|e\<bullet>y \<sqinter> 1'| |y. is_point y\<and> y \<sqsubseteq> x} \<noteq> {}" 
        using assms maxdegin by auto
    qed
  obtain p where h1: "Max {|e\<bullet>y\<sqinter> 1'| |y. is_point y \<and> y \<sqsubseteq> x} = |e\<bullet>p\<sqinter> 1'| \<and> is_point p"
    using aux by blast
  have pleq: "|e\<bullet>p\<sqinter> 1'| \<le> Max { |e\<bullet>z\<sqinter> 1'| |z . is_point z\<and> z \<sqsubseteq> y}"
    proof (rule Max_ge)
      show "finite {|e\<bullet>z \<sqinter> 1'| |z. is_point z \<and> z \<sqsubseteq> y}"
        by (simp add: local.finite_point_p_fun)
      next 
      show "|e\<bullet>p \<sqinter> 1'| \<in> {|e\<bullet>z \<sqinter> 1'| |z. is_point z \<and> z \<sqsubseteq> y}"
        using assms(1) h1 aux by auto
      qed
  show "Max {|e\<bullet>y \<sqinter> 1'| |y. is_point y \<and> y \<sqsubseteq> x} \<sqsubseteq> Max {|e\<bullet>ya \<sqinter> 1'| |ya. is_point ya \<and> ya \<sqsubseteq> y}"
    by (simp add: h1 pleq)
qed


text{* The following lemma correspond to Lemma 3.3 in the paper. *}
lemma linorderaux: 
  assumes "is_linear m \<and> is_order m"
  shows "m\<^sup>\<smile> = 1' \<squnion> m\<^sup>c"
proof (rule antisym)
  show "m\<^sup>\<smile> \<sqsubseteq> 1' \<squnion> m\<^sup>c"
    using assms aux_refl_anti_lin is_lin_def is_linear_def is_order_def by auto
  next 
  show "1' \<squnion> m\<^sup>c \<sqsubseteq> m\<^sup>\<smile>"
    by (metis assms aux_card_lin_ord galois_aux3 is_linear_def is_order_def is_refl_def le_inf_iff reflone sup_least)
qed


definition is_symm :: "'a \<Rightarrow> bool"
  where "is_symm x \<longleftrightarrow> x = x\<^sup>\<smile>"

text{* The pre-, postcondition and invariant is defined below. *}

definition pre :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
where "pre e m \<longleftrightarrow> is_irrefl e \<and> is_symm e \<and> is_order m \<and> is_linear m"

definition post where "post e c \<longleftrightarrow> |c\<^sup>\<smile>\<bullet>top\<sqinter> 1'| \<le> max_deg e +1"

definition inv :: "'a \<Rightarrow> 'a \<Rightarrow> 'a  \<Rightarrow> bool"
where "inv e m c \<longleftrightarrow> pre e m \<and> is_p_fun c \<and> (c\<^sup>\<smile>\<bullet>top) \<sqsubseteq> (m\<^sup>c\<bullet>(c\<^sup>\<smile>\<bullet>top)\<^sup>c)\<^sup>c \<and> |c\<^sup>\<smile>\<bullet>top \<sqinter> 1'| \<le> max_degv e (c\<bullet>top) +1"

text{* In the following we prove the programs correctness. *}

theorem correctness: "VARS e m c p q
  { pre e m }
  c := bot;
  WHILE c\<bullet>top \<noteq> top
    INV { inv e m c }
     DO p := minpoint ((c\<bullet>top)\<^sup>c);
        q := minpoint ((c\<^sup>\<smile>\<bullet>e\<bullet>p)\<^sup>c \<sqinter> (m\<^sup>c\<bullet>(c\<^sup>\<smile>\<bullet>e\<bullet>p)\<^sup>c)\<^sup>c);
        c := c \<squnion> p\<bullet>q\<^sup>\<smile>
     OD
  { post e c}"
proof (vcg_simp)
  (* Proof of (PO1) *)
  fix e and m
  assume hpre: "pre e m"
  show "inv e m bot" by (simp add: hpre inv_def is_p_fun_def) 
next 
  (* Proof of (PO2) *)
  fix e m c :: 'a 
  assume hinv: "inv e m c \<and> c\<bullet>top = top"
  show "post e c" unfolding post_def
    using hinv local.inv_def maxdegtop by auto
next
  (* Proof of (PO3) *)
  fix e m c :: 'a 
  let ?p = "minpoint ((c\<bullet>top)\<^sup>c)"
  let ?q = "minpoint ((c\<^sup>\<smile>\<bullet>e\<bullet>?p)\<^sup>c \<sqinter> (m\<^sup>c\<bullet>(c\<^sup>\<smile>\<bullet>e\<bullet>?p)\<^sup>c)\<^sup>c)"
  assume hinv: "inv e m c \<and> c\<bullet>top \<noteq> top"
    have auxvec1: "is_vector ((c\<bullet>top)\<^sup>c)"
      by (simp add: is_vector_def one_compl)
    have ppoint: "is_point ?p"
      by (metis auxvec1 hinv compl_bot_eq double_compl minpoint_point)
    have auxvec2: "is_vector ((c\<^sup>\<smile>\<bullet>e\<bullet>?p)\<^sup>c)"
      by (simp add: compvecpoi local.vector_compl ppoint)
    have auxvec3: "is_vector ((c\<^sup>\<smile>\<bullet>e\<bullet>?p)\<^sup>c \<sqinter> (m\<^sup>c\<bullet>((c\<^sup>\<smile>\<bullet>e\<bullet>?p)\<^sup>c))\<^sup>c)"
      using auxvec2 is_vector_def mult_assoc vector_compl vector_mult by auto
    have aux_q: "is_point (?q) \<or> ?q = bot"
      using auxvec3 minpoint_empty minpoint_point by blast
  show "inv e m (c \<squnion> ?p\<bullet>?q\<^sup>\<smile>)" unfolding inv_def
  proof (intro conjI)    
    show "|(c \<squnion> ?p\<bullet>?q\<^sup>\<smile>)\<^sup>\<smile>\<bullet>top \<sqinter> 1'| \<le> max_degv e ((c \<squnion> ?p\<bullet>?q\<^sup>\<smile>)\<bullet>top) +1" 
      proof - 
        have "is_point (?q) \<or> ?q = bot"
          using aux_q by blast
        then show "|(c \<squnion> ?p\<bullet>?q\<^sup>\<smile>)\<^sup>\<smile>\<bullet>top\<sqinter> 1'| \<le> max_degv e ((c \<squnion> ?p\<bullet>?q\<^sup>\<smile>)\<bullet>top) +1" 
          proof 
            assume qbot: "?q = bot"
            show "|(c \<squnion> ?p\<bullet>?q\<^sup>\<smile>)\<^sup>\<smile>\<bullet>top\<sqinter> 1'| \<le> max_degv e ((c \<squnion> ?p\<bullet>?q\<^sup>\<smile>)\<bullet>top) +1"
              using hinv inv_def qbot by auto
            next
            assume qbot: "is_point (?q)"
            have qincl: "?q \<sqsubseteq> c\<^sup>\<smile>\<bullet>top \<or> ?q \<sqsubseteq> (c\<^sup>\<smile>\<bullet>top)\<^sup>c"
              using comp_assoc is_vector_def leq_point_vect'' qbot by auto
            then show "|(c \<squnion> ?p\<bullet>?q\<^sup>\<smile>)\<^sup>\<smile>\<bullet>top \<sqinter> 1'| \<le> max_degv e ((c \<squnion> ?p\<bullet>?q\<^sup>\<smile>)\<bullet>top) +1"
              proof
                assume case1: "?q \<sqsubseteq> c\<^sup>\<smile>\<bullet>top"
                have "|(c \<squnion> ?p\<bullet>?q\<^sup>\<smile>)\<^sup>\<smile>\<bullet>top \<sqinter> 1'| = |c\<^sup>\<smile>\<bullet>top \<sqinter> 1'|"
                  by (simp add: comp_points_top sup.absorb1 ppoint qbot case1)
                also have "\<dots> \<le> max_degv e (c\<bullet>top) +1"
                  using hinv inv_def by blast
                also have "\<dots> \<le> max_degv e ((c \<squnion> ?p\<bullet>?q\<^sup>\<smile>)\<bullet>top) +1"
                  proof -
                    have a: "max_degv e (c\<bullet>top) \<le> max_degv e ((c \<squnion> ?p\<bullet>?q\<^sup>\<smile>)\<bullet>top)"
                      proof (rule mon_max_degv)
                      show "is_vector (c\<bullet>top) \<and> is_vector ((c \<squnion> ?p\<bullet>?q\<^sup>\<smile>)\<bullet>top)"
                        by (simp add: is_vector_def mult_assoc)
                      next 
                      show "c\<bullet>top \<noteq>bot"
                        using is_point_def le_bot ss_p18 qbot case1 by auto
                      next 
                      show "(c \<squnion> ?p\<bullet>?q\<^sup>\<smile>)\<bullet>top \<noteq>bot"
                        by (simp add: comp_points ss_p18 ppoint qbot)
                      next 
                      show "c\<bullet>top \<sqsubseteq> (c \<squnion> ?p\<bullet>?q\<^sup>\<smile>)\<bullet>top"
                        by simp
                      qed
                    thus ?thesis
                      using add_le_cancel_right by blast
                  qed
                finally show ?thesis
                  by blast
                next 
                assume case2: "?q \<sqsubseteq> (c\<^sup>\<smile>\<bullet>top)\<^sup>c"
                have aux: "?q \<squnion> m\<^sup>c\<bullet>?q \<sqsubseteq> (c\<^sup>\<smile>\<bullet>top)\<^sup>c"
                  proof - 
                    have "?q \<squnion> m\<^sup>c\<bullet>?q \<sqsubseteq> (c\<^sup>\<smile>\<bullet>top)\<^sup>c \<squnion> m\<^sup>c\<bullet>(c\<^sup>\<smile>\<bullet>top)\<^sup>c"
                      using mult_isol sup.mono case2 by blast
                    also have "\<dots> \<sqsubseteq> (c\<^sup>\<smile>\<bullet>top)\<^sup>c"
                      by (metis hinv inv_def aux6_var galois_aux) 
                    finally show ?thesis
                      by blast
                  qed
                have aux1: "c\<^sup>\<smile>\<bullet>top \<sqsubseteq> ?q\<^sup>c \<sqinter> (m\<^sup>c\<bullet>?q)\<^sup>c"
                  using aux comp_anti by fastforce
                have aux2: "?q\<^sup>c \<sqinter> (m\<^sup>c\<bullet>?q)\<^sup>c \<sqsubseteq> c\<^sup>\<smile>\<bullet>e\<bullet>?p"
                  proof - 
                    have 1: "?q \<sqsubseteq> (m\<^sup>c\<bullet>(c\<^sup>\<smile>\<bullet>e\<bullet>?p)\<^sup>c)\<^sup>c"
                      using auxvec3 minpoint_empty minpoint_sub by fastforce
                    have 2: "(m\<^sup>\<smile>)\<^sup>c\<bullet> ?q \<sqsubseteq> c\<^sup>\<smile>\<bullet>e\<bullet>?p"
                      by (simp add: "1" conv_compl conv_galois_1)
                    have 3: "(1' \<squnion> m\<^sup>c)\<^sup>c\<bullet> ?q \<sqsubseteq> c\<^sup>\<smile>\<bullet>e\<bullet>?p"
                      using "2" linorderaux hinv inv_def pre_def by auto 
                    have 4: "((1' \<squnion> m\<^sup>c)\<bullet> ?q)\<^sup>c \<sqsubseteq> c\<^sup>\<smile>\<bullet>e\<bullet>?p"
                      by (metis "3" pointscompleq qbot)
                    thus ?thesis
                      by (simp add: compl_sup distrib_right mult_onel)
                  qed
                have aux: "|c\<^sup>\<smile>\<bullet>top\<sqinter> 1'| \<le> |e\<bullet>?p\<sqinter> 1'|"
                  proof - 
                    have "|c\<^sup>\<smile>\<bullet>top\<sqinter> 1'| \<le> |?q\<^sup>c \<sqinter> (m\<^sup>c\<bullet>?q)\<^sup>c\<sqinter> 1'|"
                      using aux1 cardmono meet_iso by blast
                    also have "\<dots> \<le> |c\<^sup>\<smile>\<bullet>e\<bullet>?p\<sqinter> 1'|"
                      using aux2 cardmono meet_iso by blast
                    also have "\<dots> \<le> |e\<bullet>?p\<sqinter> 1'|"
                      proof (rule cardvecpar)
                      show "is_vector (c\<^sup>\<smile>\<bullet>e\<bullet>?p)"
                        using auxvec2 vector_compl by force
                      next 
                      show "is_vector (e \<bullet>?p)"
                        by (metis comp_assoc comp_points_top is_vector_def one_idem_mult ppoint)
                      show  "|c\<^sup>\<smile>\<bullet>e\<bullet>?p|\<le> |e\<bullet>?p|"
                        using hinv inv_def card_pfun comp_assoc by auto
                      qed
                  finally show ?thesis
                    by blast
                  qed
                have "|(c \<squnion> ?p\<bullet>?q\<^sup>\<smile>)\<^sup>\<smile>\<bullet>top \<sqinter> 1'| = |c\<^sup>\<smile>\<bullet>top\<sqinter> 1'| + 1 "
                  proof - 
                    have "|(c \<squnion> ?p\<bullet>?q\<^sup>\<smile>)\<^sup>\<smile>\<bullet>top \<sqinter> 1'| = |(c\<^sup>\<smile>\<bullet>top \<squnion> ?q) \<sqinter> 1'|"
                      by (simp add: comp_points_top ppoint qbot)
                    also have "\<dots> = |(c\<^sup>\<smile>\<bullet>top\<sqinter> 1') \<squnion> (?q \<sqinter> 1')|"
                      by (simp add: inf_sup_distrib2)
                    also have "\<dots> = |c\<^sup>\<smile>\<bullet>top\<sqinter> 1'| + |?q\<sqinter> 1'| - |(c\<^sup>\<smile>\<bullet>top\<sqinter> 1') \<sqinter> (?q \<sqinter> 1')|"
                      using cardcup by blast
                    also have "\<dots> = |c\<^sup>\<smile>\<bullet>top\<sqinter> 1'| + |?q\<sqinter> 1'| - |c\<^sup>\<smile>\<bullet>top \<sqinter> ?q\<sqinter> 1'|"
                    proof - 
                      have aux: "(c\<^sup>\<smile>\<bullet>top\<sqinter> 1') \<sqinter> (?q \<sqinter> 1') = c\<^sup>\<smile>\<bullet>top \<sqinter> ?q\<sqinter> 1'"
                        by (simp add: inf.absorb2 inf.assoc)
                      then show ?thesis
                        by simp
                    qed
                    also have "\<dots> = |c\<^sup>\<smile>\<bullet>top\<sqinter> 1'| + |?q\<sqinter> 1'|" 
                      proof - 
                        have a: "c\<^sup>\<smile>\<bullet>top \<sqinter> ?q\<sqinter> 1' = bot"
                          by (metis aux6_var inf.assoc inf_compl_bot_left1 sup.absorb1 case2)
                        thus ?thesis 
                          using a card0 by auto
                      qed
                    finally show ?thesis
                      using card_partial_point pointcap_ppoint qbot by auto
                  qed
                also have "\<dots> \<le> |e\<bullet>?p\<sqinter> 1'| + |?q\<sqinter> 1'|"
                  by (simp add: aux card_partial_point pointcap_ppoint qbot)
                also have "\<dots> = |e\<bullet>?p\<sqinter> 1'| + 1"
                  by (simp add: card_partial_point pointcap_ppoint qbot)
                also have "\<dots> \<le> max_degv e (c\<bullet>top \<squnion> ?p) +1"
                  proof -
                    have aux: "|e\<bullet>?p\<sqinter> 1'| \<le> Max {|e\<bullet>y \<sqinter> 1'| |y. is_point y \<and> y \<sqsubseteq> (c\<bullet>top \<squnion> ?p)}"
                      proof (rule Max_ge)
                      show "finite {|e\<bullet>y \<sqinter> 1'| |y. is_point y \<and> y \<sqsubseteq> c\<bullet>top \<squnion> ?p}"
                        by (simp add: finite_point_p_fun)
                      next 
                      show "|e\<bullet>?p \<sqinter> 1'| \<in> {|e\<bullet>y \<sqinter> 1'| |y. is_point y \<and> y \<sqsubseteq> c\<bullet>top \<squnion> ?p}"
                        using ppoint by auto
                      qed
                    thus ?thesis
                      by (simp add: add_le_cancel_right max_degv_def)
                  qed
                finally show ?thesis
                  by (simp add: comp_points_top ppoint qbot)
              qed
            qed
          qed
    next
    show "pre e m"
      using hinv inv_def by blast
    next 
    have hp: "c\<^sup>\<smile>\<bullet>?p \<sqsubseteq>  bot"
      by (metis is_vector_def one_compl hinv compl_bot_eq compl_eq_compl_iff compl_top_eq conv_galois_1 conv_invol minpoint_sub)     
    show "is_p_fun (c \<squnion> ?p\<bullet>?q\<^sup>\<smile>)" unfolding is_p_fun_def  
      apply (simp add: distrib_left)
      proof (intro conjI)
        show "c\<^sup>\<smile>\<bullet>c \<sqsubseteq> 1'"
          using hinv inv_def is_p_fun_def by blast
        next 
        show "?q\<bullet>?p\<^sup>\<smile>\<bullet>c \<sqsubseteq> 1'"
          by (metis hp annir bot_least comp_assoc conv_contrav conv_invol conv_zero le_bot)
        next 
        show "c\<^sup>\<smile>\<bullet>(?p\<bullet>(?q)\<^sup>\<smile>) \<sqsubseteq> 1'"
          by (metis hp annil bot_least le_bot mult.semigroup_axioms semigroup.assoc) 
        show "(?q\<bullet>?p\<^sup>\<smile>)\<bullet>(?p\<bullet>?q\<^sup>\<smile>) \<sqsubseteq> 1'" 
          proof - 
            have "(?q\<bullet>?p\<^sup>\<smile>)\<bullet>(?p\<bullet>?q\<^sup>\<smile>) \<sqsubseteq> ?q\<bullet>top\<bullet>?q\<^sup>\<smile>"
              by (metis mult_assoc mult_double_iso top_greatest)
            also have "\<dots> \<sqsubseteq> ?q\<bullet>?q\<^sup>\<smile>" 
              proof -
                have qp: "is_point ?q \<or> ?q = bot"
                  using aux_q by blast
                    then show ?thesis
                      proof
                        assume qpoint: "is_point ?q"
                        show ?thesis
                          by (metis local.comp_assoc local.comp_points_top local.eq_refl local.one_idem_mult qpoint) 
                        next
                        assume qbot: "?q = bot"
                        show ?thesis
                          by (simp add: qbot)
                      qed
              qed
            also have "\<dots> \<sqsubseteq> 1'" 
              using aux_q annir bot_least conv_invol conv_zero eq_refl mult_onel point_cnv_map ss423 by presburger 
            finally show ?thesis
              by blast
          qed
       qed
    next
    show "(c \<squnion> ?p\<bullet>?q\<^sup>\<smile>)\<^sup>\<smile>\<bullet>top \<sqsubseteq> (m\<^sup>c\<bullet>((c \<squnion> ?p\<bullet>?q\<^sup>\<smile>)\<^sup>\<smile>\<bullet>top)\<^sup>c)\<^sup>c"
      proof - 
        have aux1: "?q\<bullet>?p\<^sup>\<smile>\<bullet>top \<sqsubseteq> ?q"
          using aux_q annil comp_points_top eq_refl ppoint by presburger
        have aux2: "m\<^sup>c\<bullet>(c\<^sup>\<smile>\<bullet>top)\<^sup>c \<sqsubseteq> (c\<^sup>\<smile>\<bullet>top)\<^sup>c"
          using hinv inv_def compl_le_swap1 by blast
        have aux3: "m\<^sup>c\<bullet>(c\<^sup>\<smile>\<bullet>top)\<^sup>c \<sqsubseteq> ?q\<^sup>c"
          proof - 
            have 1: "c\<^sup>\<smile>\<bullet>e\<bullet>?p \<sqsubseteq> c\<^sup>\<smile>\<bullet>top"
              by (simp add: mult_assoc mult_isol_var)
            have 2: "(m\<^sup>c\<bullet>(c\<^sup>\<smile>\<bullet>e\<bullet>?p)\<^sup>c)\<^sup>c \<sqsubseteq> (m\<^sup>c\<bullet>(c\<^sup>\<smile>\<bullet>top)\<^sup>c)\<^sup>c"
              using "1" compl_mono mult_isol by blast
            have 3: "m\<^sup>c\<bullet>(c\<^sup>\<smile>\<bullet>top)\<^sup>c \<sqsubseteq> ?q\<^sup>c"
              proof -
                have a: "?q \<sqsubseteq> (c\<^sup>\<smile>\<bullet>e\<bullet>?p)\<^sup>c \<sqinter> (m\<^sup>c\<bullet>(c\<^sup>\<smile>\<bullet>e\<bullet>?p)\<^sup>c)\<^sup>c"
                  using auxvec3 local.bot_unique local.minpoint_empty local.minpoint_sub by blast
                then show ?thesis
                  by (meson "2" local.compl_le_swap1 local.dual_order.trans local.inf.boundedE)
              qed
            thus ?thesis
              by blast
          qed
        have "m\<^sup>c\<bullet>((c \<squnion> ?p\<bullet>?q\<^sup>\<smile>)\<^sup>\<smile>\<bullet>top)\<^sup>c = m\<^sup>c\<bullet>(c\<^sup>\<smile>\<bullet>top \<squnion> ?q\<bullet>?p\<^sup>\<smile>\<bullet>top)\<^sup>c"
          by simp
        also have "\<dots> \<sqsubseteq> m\<^sup>c\<bullet>(c\<^sup>\<smile>\<bullet>top \<squnion> ?q)\<^sup>c" 
          by (metis aux1 aux_q comp_points_top eq_iff le_bot ppoint)
        also have "\<dots> \<sqsubseteq> m\<^sup>c\<bullet>((c\<^sup>\<smile>\<bullet>top)\<^sup>c \<sqinter> ?q\<^sup>c)"
          by simp 
        also have "\<dots> \<sqsubseteq> (c\<^sup>\<smile>\<bullet>top)\<^sup>c \<sqinter> ?q\<^sup>c"
          using aux2 aux3 local.dual_order.trans local.inf.boundedI local.mult_subdistl by blast
        also have "\<dots> \<sqsubseteq> ((c\<^sup>\<smile> \<squnion> ?q\<bullet>?p\<^sup>\<smile>)\<bullet>top)\<^sup>c"
          by (metis aux1 aux_q local.comp_points_top local.compl_sup local.distrib_right' local.eq_iff local.le_bot ppoint)
        also have "\<dots> \<sqsubseteq> ((c \<squnion> ?p\<bullet>?q\<^sup>\<smile>)\<^sup>\<smile>\<bullet>top)\<^sup>c"
          by simp
        finally show ?thesis
          using local.compl_le_swap1 by blast
      qed
    qed
qed
end

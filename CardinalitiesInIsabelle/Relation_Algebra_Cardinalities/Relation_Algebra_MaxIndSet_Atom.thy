
theory Relation_Algebra_MaxIndSet_Atom 
  imports "~~/src/HOL/Hoare/Hoare_Logic"
          "~~/Relation_Algebra_Cardinalities/Relation_Algebra_Cardinal"
           "~~/Relation_Algebra_Cardinalities/Relation_Algebra_Orders"
            "~~/Relation_Algebra_Cardinalities/Relation_Algebra_Points"
  

begin
text{* This theory contains the correctness proof of the Maximum Independent Set algorithm 
presented in "Cardinality of Relations and Relational Approximation Algorithms" by Berghammer et al. 
Our version of the program uses partial identities and partial points, instead of vectors and points.*}


declare [[show_sorts,show_types]]


text{* minpoint is called the function point() in the underlying paper. It is defined by the 
properties it should fulfill. *}

class minatom =
  fixes minatom :: "'a \<Rightarrow> 'a" 

class relation_algebra_minatom = relation_algebra_card + minatom + 
  assumes minatom_sub:  "minatom x \<le> x" 
  and     minatom_point:"x \<noteq> bot \<longrightarrow> is_partial_point (minatom x)"

context relation_algebra_minatom
  begin


text{* ";" is a symbol used in Hoare_Logic, thus we have to change the notation here.*}

no_notation
  composition (infixl ";" 75)
notation
  composition (infixl "\<bullet>" 75)


text{* Below we define the maximum degree and prove some properties about it. *}

definition max_deg  :: "'a \<Rightarrow> nat"
   where "max_deg x \<equiv> Max { |x\<bullet>y\<bullet>top \<sqinter> 1'| |y . is_partial_point y}"
  
     
definition is_symm :: "'a \<Rightarrow> bool"
  where "is_symm x \<longleftrightarrow> x = x\<^sup>\<smile>"

    
lemma auxmax_1:
  assumes fin: "finite  { x . P x }"
    and "v \<in> { x . P x }"
  shows "f v \<le> Max { f y |y. P y }"
proof(rule Max_ge)
  show "finite {f y |y::'b. P y}"
    by (simp add: fin)
next
  show "f v \<in> {f y |y::'b. P y}"
    using assms(2) by blast
qed
  
  
lemma sum_bounded:
  fixes K:: "nat"
    (*f:: 'a \<Rightarrow> nat   (Betrags-Funktion) *)
  assumes leq: "\<And>x. x\<in>A \<Longrightarrow> f x \<le> K"
    and fin: "finite A"
  shows "( \<Sum>x\<in>A . f x ) \<le> (card A)*K"
  using leq sum_bounded_above by force

     
text{* The pre-, postcondition and invariant are defined below. *}
   

definition pre :: "'a \<Rightarrow> nat \<Rightarrow> bool"
 where "pre r k  \<longleftrightarrow> is_irrefl r \<and> is_symm r \<and> k = max_deg r"

   
definition post :: "'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool"
  where "post r k s \<longleftrightarrow> 
    r\<bullet>s\<bullet>top \<sqinter> 1' \<sqsubseteq> s\<^sup>c \<sqinter> 1' \<and> (\<forall>t .is_test t \<and> r\<bullet>t\<bullet>top \<sqinter> 1' \<sqsubseteq> t\<^sup>c \<sqinter> 1' \<longrightarrow> |t| \<le> |s| * (k+1))"
    

definition inv :: "'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a  \<Rightarrow> bool"
  where "inv r k s v \<longleftrightarrow> 
    pre r k \<and> r\<bullet>s\<bullet>top \<sqinter> 1' \<sqsubseteq> s\<^sup>c \<sqinter> 1' \<and> (r\<bullet>s\<bullet>top \<sqinter> 1') \<squnion> s = v \<and> is_test s \<and> is_test v"

    
text{* In the following we prove the correctness of the program. *}

  
theorem correctness: "VARS r k s v p
  { pre r k }
  s := bot;
  v := bot;
  WHILE v \<noteq> 1'
    INV { inv r k s v }
     DO p := minatom (v\<^sup>c \<sqinter> 1');
        s := s \<squnion> p;
        v := v \<squnion> p \<squnion> (r\<bullet>p\<bullet>top \<sqinter> 1')
     OD
  { post r k s }"
  
  
proof (vcg_simp)
  (* Proof of first ProofObligation (PO1) *)
  fix r::'a and k::nat
  assume hpre: "pre r k"
  show "inv r k bot bot"
    by (simp add: hpre local.inv_def local.is_test_def)
next
  (* Proof of (PO3)*)
  fix r s v :: 'a and k :: nat
  let ?p = "minatom (v\<^sup>c \<sqinter> 1')"
  assume hinv: "inv r k s v \<and> v \<noteq> 1'" 
  have auxvec1: "is_test(v\<^sup>c \<sqinter> 1')"
    by (simp add: local.is_test_def)
  have ppoint: "is_partial_point ?p"
    by (metis hinv local.antisym local.galois_aux2 local.inf.commute local.inv_def local.is_test_def local.minatom_point)
  have aux: "s \<sqsubseteq> v "
    using hinv local.inv_def by auto
  have aux1: "r\<bullet>s\<bullet>top \<sqinter> 1' \<sqsubseteq> v"
    using hinv local.inv_def by auto
  have aux2: "(r\<bullet>s\<bullet>top \<sqinter> 1') \<squnion> s = v"
    using hinv local.inv_def by blast
  have hp: "r\<bullet>?p\<bullet>top \<sqsubseteq> ?p\<^sup>c"
          proof - 
            have a: "?p\<bullet>top\<bullet>?p\<^sup>\<smile> \<sqsubseteq> 1'"
              using local.is_atom_def local.is_partial_point_def ppoint by blast
            have b: "?p\<bullet>top\<bullet>?p\<^sup>\<smile> \<sqsubseteq> r\<^sup>c"
              by (metis a hinv local.comp_anti local.double_compl local.dual_order.trans local.inv_def local.is_irrefl_def pre_def) 
            thus ?thesis
              by (simp add: local.compl_le_swap1 local.conv_galois_2)
          qed
  show "inv r k (s \<squnion> ?p) (v \<squnion> ?p \<squnion> r\<bullet>?p\<bullet>top \<sqinter> 1')" unfolding inv_def
  proof (intro conjI)
    show hpre: "pre r k"
      using hinv inv_def by blast
    next
    show "is_test (s \<squnion> ?p)"
      using hinv local.inv_def local.is_partial_point_def local.test_sum ppoint by blast
    next
    show "is_test (v \<squnion> ?p \<squnion> r \<bullet>?p\<bullet>top \<sqinter> 1')"
      using hinv local.inv_def local.is_partial_point_def local.is_test_def ppoint by auto
    show "(r\<bullet>(s \<squnion> ?p)\<bullet>top \<sqinter> 1') \<squnion> (s \<squnion> ?p) = v \<squnion> ?p \<squnion> (r\<bullet>?p\<bullet>top \<sqinter> 1')"
    proof - 
      have "(r\<bullet>(s \<squnion> ?p)\<bullet>top \<sqinter> 1') \<squnion> (s \<squnion> ?p) = (r\<bullet>s\<bullet>top \<sqinter> 1') \<squnion> (r\<bullet>?p\<bullet>top \<sqinter> 1') \<squnion> (s \<squnion> ?p)"
        by (simp add: local.distrib_left local.distrib_right local.inf_sup_distrib2)
      also have "\<dots> = ((r\<bullet>s\<bullet>top \<sqinter> 1') \<squnion> s) \<squnion> (r\<bullet>?p\<bullet>top \<sqinter> 1') \<squnion> ?p"
        by (simp add: local.sup_assoc local.sup_left_commute)
      also have "\<dots> = v \<squnion> ?p \<squnion> (r\<bullet>?p\<bullet>top \<sqinter> 1')"
        using aux2 local.sup.assoc local.sup.commute by auto
      finally show ?thesis
        by blast
    qed
    show a: "r\<bullet>(s \<squnion> ?p)\<bullet>top \<sqinter> 1' \<sqsubseteq> (s \<squnion> ?p)\<^sup>c \<sqinter> 1'"
      apply(simp add: distrib_left distrib_right)  
    proof (intro conjI)
      show b:"(r\<bullet>s\<bullet>top \<squnion> r\<bullet>?p\<bullet>top) \<sqinter> 1' \<sqsubseteq> ?p\<^sup>c"
        apply (simp add: inf_sup_distrib2) 
      proof (intro conjI)
        show  "r\<bullet>?p\<bullet>top \<sqinter> 1' \<sqsubseteq> ?p\<^sup>c"
          using hp local.inf.coboundedI1 by blast
        show "r\<bullet>s\<bullet>top \<sqinter> 1' \<sqsubseteq> ?p\<^sup>c"
        proof -
          have a: "r\<bullet>s\<bullet>top \<sqinter> 1' \<sqsubseteq> v "
            by (simp add: aux1)
          also have "\<dots> \<sqsubseteq> v \<squnion> 1'\<^sup>c"
            by simp
          also have "\<dots> \<sqsubseteq> ?p\<^sup>c"
            by (metis local.comp_anti local.compl_sup local.double_compl local.minatom_sub)
          finally show ?thesis
            by blast
        qed
      qed
      show "(r\<bullet>s\<bullet>top \<squnion> r\<bullet>?p\<bullet>top) \<sqinter> 1' \<sqsubseteq> s\<^sup>c"
        apply (simp add: inf_sup_distrib2) 
      proof (intro conjI)
        show "r\<bullet>s\<bullet>top \<sqinter> 1' \<sqsubseteq> s\<^sup>c"
          using hinv local.inv_def by auto
        show "r\<bullet>?p\<bullet>top \<sqinter> 1' \<sqsubseteq> s\<^sup>c"
        proof -
          have 1: "r\<bullet>s\<bullet>top \<sqsubseteq> ?p\<^sup>c"
            by (smt b local.dual_order.trans local.galois_2 local.inf.bounded_iff local.inf.cobounded2 local.less_eq_def local.minatom_sub local.sup_ge1)
          have 2: "r\<^sup>\<smile>\<bullet>s \<sqsubseteq> (?p\<bullet>top)\<^sup>c"
            using "1" hinv is_symm_def local.conv_galois_2 local.inv_def pre_def by auto
          have 3: "r\<bullet>?p\<bullet>top \<sqsubseteq> s\<^sup>c"
            by (metis "2" local.comp_assoc local.compl_le_swap1 local.conv_galois_1 local.double_compl)
          thus ?thesis
            by (simp add: local.inf.coboundedI1)
        qed
      qed
    qed
  qed
next 
    (* Proof of (PO2) *)
  fix r s v :: 'a and k :: nat
  assume hinv: "inv r k s v \<and> v = 1'" 
  show "post r k s" unfolding post_def
    proof (intro conjI)
      show "r\<bullet>s\<bullet>top \<sqinter> 1' \<sqsubseteq> s\<^sup>c \<sqinter> 1'"
        using hinv local.inv_def by blast
      next
      show "\<forall>t. is_test t \<and> r\<bullet>t\<bullet>top \<sqinter> 1' \<sqsubseteq> t\<^sup>c \<sqinter> 1' \<longrightarrow> |t| \<le> |s| * (k+1)"
        proof 
          fix t 
          show "is_test t \<and> r\<bullet>t\<bullet>top \<sqinter> 1' \<sqsubseteq> t\<^sup>c \<sqinter> 1' \<longrightarrow> |t| \<le> |s| * (k+1)"
            proof 
            assume ht: "is_test t \<and> r\<bullet>t\<bullet>top \<sqinter> 1' \<sqsubseteq> t\<^sup>c \<sqinter> 1'"
            show "|t| \<le> |s| * (k+1)"
            proof - 
              have finpp: "finite {x|x. is_partial_point x \<and> x \<sqsubseteq> s}"
                using fin_partial_points_p by auto
              have finppf: "finite {x\<bullet>top|x. is_partial_point x \<and> x \<sqsubseteq> s}"
                using fin_partial_points_fun by fastforce
              have "|t| \<le> |1'|"
                using ht local.cardmono local.is_test_def by auto
              also have "\<dots> = |v|"
                by (simp add: hinv)
              also have "\<dots> = |(r\<bullet>s\<bullet>top \<sqinter> 1') \<squnion> s|"
                using hinv local.inv_def by auto
              also have "\<dots> \<le> |(r\<bullet>s\<bullet>top \<sqinter> 1')| + |s|"
                by (metis le_add1 local.cardsimp)
              also have "\<dots> = |r\<bullet>\<Squnion> {x|x. is_partial_point x \<and> x \<sqsubseteq> s}\<bullet>top \<sqinter> 1'| + |s|"
                using hinv local.inv_def local.test_partial_points by auto
              also have "\<dots> = |r\<bullet>\<Squnion> {x\<bullet>top|x. is_partial_point x \<and> x \<sqsubseteq> s} \<sqinter> 1'| + |s|"
                using sum_comp_distr_left finpp local.mult_assoc by fastforce
              also have "\<dots> = |\<Squnion> {r\<bullet>(x\<bullet>top)|x. is_partial_point x \<and> x \<sqsubseteq> s} \<sqinter> 1'| + |s|"
                using sum_comp_distr_right_fun finpp by fastforce
              also have "\<dots> = |\<Squnion> {r\<bullet>(x\<bullet>top) \<sqinter> 1'|x. is_partial_point x \<and> x \<sqsubseteq> s}| + |s|"
                using sum_cap_distr_right_fun finpp by fastforce
              also have "\<dots> \<le> (\<Sum> z \<in> {r\<bullet>(x\<bullet>top) \<sqinter> 1'|x. is_partial_point x \<and> x \<sqsubseteq> s}. |z| ) + |s|"
                using sumleq_fun finpp by auto
              also have "\<dots> \<le> (\<Sum> z \<in> {r\<bullet>(x\<bullet>top) \<sqinter> 1'|x. is_partial_point x \<and> x \<sqsubseteq> s}. k ) + |s|"
                proof - 
     have a: "(\<Sum> z \<in> {r\<bullet>(x\<bullet>top) \<sqinter> 1'|x. is_partial_point x \<and> x \<sqsubseteq> s}. |z| ) \<le> card {r\<bullet>(x\<bullet>top) \<sqinter> 1'|x. is_partial_point x \<and> x \<sqsubseteq> s} * k"
      proof (rule sum_bounded)
        show "finite {r\<bullet>(x\<bullet>top) \<sqinter> 1' |x::'a. is_partial_point x \<and> x \<sqsubseteq> s}"
          using fin_partial_points_fun by fastforce
        show "\<And>z. z \<in> {r\<bullet>(x\<bullet>top) \<sqinter> 1' |x. is_partial_point x \<and> x \<sqsubseteq> s} \<Longrightarrow> |z| \<le> k"
          proof -
          fix z
          assume h: "z \<in> {r\<bullet>(x\<bullet>top) \<sqinter> 1' |x. is_partial_point x \<and> x \<sqsubseteq> s}"
          show "|z| \<le> k"
          proof - 
              have  "|z| \<le> Max { |r\<bullet>(x\<bullet>top) \<sqinter> 1'| |x . is_partial_point x \<and> x \<sqsubseteq> s}"
                proof (rule Max_ge)
                  show "finite {|r \<bullet> (x \<bullet> top) \<sqinter> 1'| |x::'a. is_partial_point x \<and> x \<sqsubseteq> s}"
                    by (simp add: local.fin_partial_points_fun)
                  show "|z| \<in> {|r \<bullet> (x \<bullet> top) \<sqinter> 1'| |x::'a. is_partial_point x \<and> x \<sqsubseteq> s}"
                    using h by blast
                qed
              also have "\<dots> \<le> Max { |r\<bullet>(x\<bullet>top) \<sqinter> 1'| |x . is_partial_point x \<and> x \<sqsubseteq> top}"
                 proof (rule Max_mono) 
                  show "{ |r\<bullet>(x\<bullet>top) \<sqinter> 1'| |x . is_partial_point x \<and> x \<sqsubseteq> s} \<subseteq> { |r\<bullet>(x\<bullet>top) \<sqinter> 1'| |x . is_partial_point x \<and> x \<sqsubseteq> top}"
                    by auto
                  show "{|r\<bullet>(x\<bullet>top) \<sqinter> 1'| |x. is_partial_point x \<and> x \<sqsubseteq> s} \<noteq> {}"
                    using h by blast
                  show "finite {|r\<bullet>(x\<bullet>top) \<sqinter> 1'| |x. is_partial_point x \<and> x \<sqsubseteq> top}"
                    using local.fin_partial_points_fun by fastforce
                qed
              also have "\<dots> = Max { |r\<bullet>(x\<bullet>top) \<sqinter> 1'| |x . is_partial_point x}"
                by simp
              also have "\<dots> = max_deg r"
                by (simp add: local.comp_assoc max_deg_def)
              also have "\<dots> = k"
                using hinv local.inv_def pre_def by auto
              finally show ?thesis
                by blast
            qed
          qed
        qed
      thus ?thesis
        by simp
      qed
    also have "\<dots> \<le> card {r\<bullet>(x\<bullet>top) \<sqinter> 1'|x. is_partial_point x \<and> x \<sqsubseteq> s} * k + |s|"
      by simp
    also have "\<dots> \<le> |s| * k + |s|"
      using card_test_fun inv_def hinv by fastforce
    finally show ?thesis
      by simp
  qed
qed
qed
qed
qed
  
end


  
         
          
          
theory CombinatorLaws
imports BananasLanguage
begin

definition domain :: "expr \<Rightarrow> val set" where
  "domain e = { v. \<exists>v'. e \<cdot> v \<Down> v' }"

(* kludged in order to deal with mismatching domains - ie, polymorphic ones *)
definition expression_equality :: "expr \<Rightarrow> expr \<Rightarrow> bool" (infix "\<simeq>" 50) where
  "e\<^sub>1 \<simeq> e\<^sub>2 = ((domain e\<^sub>1 \<subseteq> domain e\<^sub>2 \<and> (\<forall>v v'. (e\<^sub>1 \<cdot> v \<Down> v') \<longrightarrow> (e\<^sub>2 \<cdot> v \<Down> v'))) 
            \<or> (domain e\<^sub>2 \<subseteq> domain e\<^sub>1 \<and> (\<forall>v v'. (e\<^sub>2 \<cdot> v \<Down> v') \<longrightarrow> (e\<^sub>1 \<cdot> v \<Down> v'))))"

(* other combinators *)

definition tuple_pair :: "expr \<Rightarrow> expr \<Rightarrow> expr" (infix "\<triangle>" 80) where
  "e\<^sub>1 \<triangle> e\<^sub>2 = e\<^sub>1 \<parallel> e\<^sub>2 \<cdot> \<Theta>"

definition case_strip :: "expr \<Rightarrow> expr \<Rightarrow> expr" (infix "\<nabla>" 80) where
  "e\<^sub>l \<nabla> e\<^sub>r = \<Xi> \<cdot> e\<^sub>l \<bar> e\<^sub>r"

lemma tc_tup_pair [simp]: "f\<^sub>1 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> f\<^sub>2 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>3 \<Longrightarrow> f\<^sub>1 \<triangle> f\<^sub>2 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<otimes> t\<^sub>3"
  proof (unfold tuple_pair_def)
    assume "f\<^sub>1 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2"
       and "f\<^sub>2 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>3"
    hence "f\<^sub>1 \<parallel> f\<^sub>2 \<turnstile> t\<^sub>1 \<otimes> t\<^sub>1 \<rightarrow> t\<^sub>2 \<otimes> t\<^sub>3" by simp
    thus "f\<^sub>1 \<parallel> f\<^sub>2 \<cdot> \<Theta> \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<otimes> t\<^sub>3" by simp
  qed

lemma tc_cse_str [simp]: "f\<^sub>l \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>3 \<Longrightarrow> f\<^sub>r \<turnstile> t\<^sub>2 \<rightarrow> t\<^sub>3 \<Longrightarrow> f\<^sub>l \<nabla> f\<^sub>r \<turnstile> t\<^sub>1 \<oplus> t\<^sub>2 \<rightarrow> t\<^sub>3"
  proof (unfold case_strip_def)
    assume "f\<^sub>l \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>3"
       and "f\<^sub>r \<turnstile> t\<^sub>2 \<rightarrow> t\<^sub>3"
    hence "f\<^sub>l \<bar> f\<^sub>r \<turnstile> t\<^sub>1 \<oplus> t\<^sub>2 \<rightarrow> t\<^sub>3 \<oplus> t\<^sub>3" by simp
    moreover have "\<Xi> \<turnstile> t\<^sub>3 \<oplus> t\<^sub>3 \<rightarrow> t\<^sub>3" by simp
    ultimately show "\<Xi> \<cdot> f\<^sub>l \<bar> f\<^sub>r \<turnstile> t\<^sub>1 \<oplus> t\<^sub>2 \<rightarrow> t\<^sub>3" by (metis tc_comp)
  qed

lemma ev_tup_pair [simp]: "f\<^sub>1 \<cdot> v \<Down> v\<^sub>1 \<Longrightarrow> f\<^sub>2 \<cdot> v \<Down> v\<^sub>2 \<Longrightarrow> f\<^sub>1 \<triangle> f\<^sub>2 \<cdot> v \<Down> PairV v\<^sub>1 v\<^sub>2"
  proof (unfold tuple_pair_def)
    assume "f\<^sub>1 \<cdot> v \<Down> v\<^sub>1"
       and "f\<^sub>2 \<cdot> v \<Down> v\<^sub>2"
    moreover have "\<Theta> \<cdot> v \<Down> PairV v v" by simp
    ultimately show "(f\<^sub>1 \<parallel> f\<^sub>2 \<cdot> \<Theta>) \<cdot> v \<Down> PairV v\<^sub>1 v\<^sub>2" by fastforce
  qed

lemma ev_cse_str_l [simp]: "f\<^sub>l \<cdot> v \<Down> v' \<Longrightarrow> f\<^sub>l \<nabla> f\<^sub>r \<cdot> InlV v \<Down> v'"
  proof (unfold case_strip_def)
    assume "f\<^sub>l \<cdot> v \<Down> v'"
    hence "f\<^sub>l \<bar> f\<^sub>r \<cdot> InlV v \<Down> InlV v'" by simp
    thus "(\<Xi> \<cdot> f\<^sub>l \<bar> f\<^sub>r) \<cdot> InlV v \<Down> v'" by fastforce
  qed

lemma ev_cse_str_r [simp]: "f\<^sub>r \<cdot> v \<Down> v' \<Longrightarrow> f\<^sub>l \<nabla> f\<^sub>r \<cdot> InrV v \<Down> v'"
  proof (unfold case_strip_def)
    assume "f\<^sub>r \<cdot> v \<Down> v'"
    hence "f\<^sub>l \<bar> f\<^sub>r \<cdot> InrV v \<Down> InrV v'" by simp
    thus "(\<Xi> \<cdot> f\<^sub>l \<bar> f\<^sub>r) \<cdot> InrV v \<Down> v'" by fastforce
  qed

(* helper lemmas *)

(*

lemma [elim]: "v ~ (e\<^sub>1 \<cdot> e\<^sub>2) \<cdot> e\<^sub>3 \<leadsto> v' \<Longrightarrow> v ~ e\<^sub>1 \<cdot> e\<^sub>2 \<cdot> e\<^sub>3 \<leadsto> v'"
  proof (induction v "(e\<^sub>1 \<cdot> e\<^sub>2) \<cdot> e\<^sub>3" v' rule: evaluate.induct)
  case (ev_comp v v' v'')
    with ev_comp(3) show ?case 
      by (induction v' "e\<^sub>1 \<cdot> e\<^sub>2" v'' rule: evaluate.induct) (metis evaluate.ev_comp)
  qed

lemma [elim]: "v ~ \<epsilon> \<leadsto> v' \<Longrightarrow> v = v'"
  by (induction v \<epsilon> v' rule: evaluate.induct) simp_all

lemma [elim]: "PairV v\<^sub>1 v\<^sub>2 ~ \<pi>\<^sub>1 \<leadsto> v \<Longrightarrow> v\<^sub>1 = v"
  by (induction "PairV v\<^sub>1 v\<^sub>2" \<pi>\<^sub>1 v rule: evaluate.induct) simp_all

lemma [elim]: "PairV v\<^sub>1 v\<^sub>2 ~ \<pi>\<^sub>2 \<leadsto> v \<Longrightarrow> v\<^sub>2 = v"
  by (induction "PairV v\<^sub>1 v\<^sub>2" \<pi>\<^sub>2 v rule: evaluate.induct) simp_all

lemma [elim]: "v ~ \<iota>\<^sub>l \<leadsto> v' \<Longrightarrow> v' = InlV v"
  by (induction v \<iota>\<^sub>l v' rule: evaluate.induct) simp_all

lemma [elim]: "v ~ \<iota>\<^sub>l \<leadsto> InlV v' \<Longrightarrow> v' = v"
  by (induction v \<iota>\<^sub>l "InlV v'" rule: evaluate.induct) simp_all

lemma [elim]: "v ~ \<iota>\<^sub>l \<leadsto> InrV v' \<Longrightarrow> False"
  by (induction v \<iota>\<^sub>l "InrV v'" rule: evaluate.induct)

lemma [elim]: "v ~ \<iota>\<^sub>r \<leadsto> v' \<Longrightarrow> v' = InrV v"
  by (induction v \<iota>\<^sub>r v' rule: evaluate.induct) simp_all

lemma [elim]: "v ~ \<iota>\<^sub>r \<leadsto> InrV v' \<Longrightarrow> v' = v"
  by (induction v \<iota>\<^sub>r "InrV v'" rule: evaluate.induct) simp_all

lemma [elim]: "v ~ \<iota>\<^sub>r \<leadsto> InlV v' \<Longrightarrow> False"
  by (induction v \<iota>\<^sub>r "InlV v'" rule: evaluate.induct)

lemma [elim]: "v ~ \<epsilon> \<cdot> e \<leadsto> v' \<Longrightarrow> v ~ e \<leadsto> v'"
  proof (induction v "\<epsilon> \<cdot> e" v' rule: evaluate.induct)
  case (ev_comp v v' v'')
    moreover hence "v' = v''" by auto
    ultimately show ?case by simp
  qed

lemma [elim]: "v ~ e \<cdot> \<epsilon> \<leadsto> v' \<Longrightarrow> v ~ e \<leadsto> v'"
  proof (induction v "e \<cdot> \<epsilon>" v' rule: evaluate.induct)
  case (ev_comp v v' v'')
    moreover hence "v = v'" by auto
    ultimately show ?case by simp
  qed

lemma [elim]: "v ~ \<pi>\<^sub>1 \<leadsto> v\<^sub>1 \<Longrightarrow> v ~ \<pi>\<^sub>2 \<leadsto> v\<^sub>2 \<Longrightarrow> v = PairV v\<^sub>1 v\<^sub>2"
  proof (induction v \<pi>\<^sub>1 v\<^sub>1 rule: evaluate.induct)
  case (ev_fst v\<^sub>1 v\<^sub>2')
    thus ?case by (induction "PairV v\<^sub>1 v\<^sub>2'" \<pi>\<^sub>2 v\<^sub>2 rule: evaluate.induct) simp_all
  qed

lemma [simp]: "v ~ \<pi>\<^sub>1 \<triangle> \<pi>\<^sub>2 \<leadsto> v' \<Longrightarrow> v ~ \<epsilon> \<leadsto> v'"
  proof (induction v "\<pi>\<^sub>1 \<triangle> \<pi>\<^sub>2" v' rule: evaluate.induct)
  case (ev_tup v v\<^sub>1 v\<^sub>2)
    hence "v = PairV v\<^sub>1 v\<^sub>2" by auto
    thus ?case by simp
  qed

lemma [simp]: "v ~ e\<^sub>1 \<triangle> e\<^sub>2 \<cdot> e\<^sub>3 \<leadsto> v' \<Longrightarrow> v ~ (e\<^sub>1 \<cdot> e\<^sub>3) \<triangle> (e\<^sub>2 \<cdot> e\<^sub>3) \<leadsto> v'"
  proof (induction v "e\<^sub>1 \<triangle> e\<^sub>2 \<cdot> e\<^sub>3" v' rule: evaluate.induct)
  case (ev_comp v v' v'')
    with ev_comp(3) show ?case by (induction v' "e\<^sub>1 \<triangle> e\<^sub>2" v'' rule: evaluate.induct) simp_all
  qed

lemma [elim]: "v ~ \<pi>\<^sub>1 \<cdot> e\<^sub>1 \<triangle> e\<^sub>2 \<leadsto> v' \<Longrightarrow> v ~ e\<^sub>1 \<leadsto> v'"
  proof (induction v "\<pi>\<^sub>1 \<cdot> e\<^sub>1 \<triangle> e\<^sub>2" v' rule: evaluate.induct)
  case (ev_comp v v' v'')
    thus ?case 
      proof (induction v "e\<^sub>1 \<triangle> e\<^sub>2" v' rule: evaluate.induct)
      case (ev_tup v v\<^sub>1 v\<^sub>2)
        moreover hence "v\<^sub>1 = v''" by auto
        ultimately show ?case by simp
      qed
  qed

lemma [elim]: "v ~ \<pi>\<^sub>2 \<cdot> e\<^sub>1 \<triangle> e\<^sub>2 \<leadsto> v' \<Longrightarrow> v ~ e\<^sub>2 \<leadsto> v'"
  proof (induction v "\<pi>\<^sub>2 \<cdot> e\<^sub>1 \<triangle> e\<^sub>2" v' rule: evaluate.induct)
  case (ev_comp v v' v'')
    thus ?case 
      proof (induction v "e\<^sub>1 \<triangle> e\<^sub>2" v' rule: evaluate.induct)
      case (ev_tup v v\<^sub>1 v\<^sub>2)
        moreover hence "v\<^sub>2 = v''" by auto
        ultimately show ?case by simp
      qed
  qed

lemma [simp]: "v ~ \<iota>\<^sub>l \<nabla> \<iota>\<^sub>r \<leadsto> v' \<Longrightarrow> v ~ \<epsilon> \<leadsto> v'"
  proof (induction v "\<iota>\<^sub>l \<nabla> \<iota>\<^sub>r" v' rule: evaluate.induct)
  case (ev_csl v v')
    hence "v' = InlV v" by auto
    thus ?case by simp
  next case (ev_csr v v')
    hence "v' = InrV v" by auto
    thus ?case by simp
  qed

lemma [simp]: "v ~ e\<^sub>3 \<cdot> e\<^sub>1 \<nabla> e\<^sub>2 \<leadsto> v' \<Longrightarrow> v ~ (e\<^sub>3 \<cdot> e\<^sub>1) \<nabla> (e\<^sub>3 \<cdot> e\<^sub>2) \<leadsto> v'"
  proof (induction v "e\<^sub>3 \<cdot> e\<^sub>1 \<nabla> e\<^sub>2" v' rule: evaluate.induct)
  case (ev_comp v v' v'')
    thus ?case by (induction v "e\<^sub>1 \<nabla> e\<^sub>2" v' rule: evaluate.induct) simp_all
  qed

lemma [elim]: "v ~ e\<^sub>1 \<nabla> e\<^sub>2 \<cdot> \<iota>\<^sub>l \<leadsto> v' \<Longrightarrow> v ~ e\<^sub>1 \<leadsto> v'"
  proof (induction v "e\<^sub>1 \<nabla> e\<^sub>2 \<cdot> \<iota>\<^sub>l" v' rule: evaluate.induct)
  case (ev_comp v v' v'')
    with ev_comp(2) show ?case
      proof (induction v' "e\<^sub>1 \<nabla> e\<^sub>2" v'' rule: evaluate.induct)
      case (ev_csl v' v'')
        moreover hence "v' = v" by auto
        ultimately show ?case by simp
      next case (ev_csr v' v'')
        hence False by auto
        thus ?case by simp
      qed
  qed

lemma [elim]: "v ~ e\<^sub>1 \<nabla> e\<^sub>2 \<cdot> \<iota>\<^sub>r \<leadsto> v' \<Longrightarrow> v ~ e\<^sub>2 \<leadsto> v'"
  proof (induction v "e\<^sub>1 \<nabla> e\<^sub>2 \<cdot> \<iota>\<^sub>r" v' rule: evaluate.induct)
  case (ev_comp v v' v'')
    with ev_comp(2) show ?case
      proof (induction v' "e\<^sub>1 \<nabla> e\<^sub>2" v'' rule: evaluate.induct)
      case (ev_csl v' v'')
        hence False by auto
        thus ?case by blast
      next case (ev_csr v' v'')
        moreover hence "v' = v" by auto
        ultimately show ?case by blast
      qed
  qed

*)

(* in terms of the actual expression equality *)

lemma equiv_refl [simp]: "e\<^sub>1 \<simeq> e\<^sub>1"
  by (auto simp add: expression_equality_def)

lemma equiv_sym [sym]: "e\<^sub>1 \<simeq> e\<^sub>2 \<Longrightarrow> e\<^sub>2 \<simeq> e\<^sub>1"
  by (auto simp add: expression_equality_def)

lemma equiv_trans [simp, trans]: "e\<^sub>1 \<simeq> e\<^sub>2 \<Longrightarrow> e\<^sub>2 \<simeq> e\<^sub>3 \<Longrightarrow> e\<^sub>1 \<simeq> e\<^sub>3"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>1 \<simeq> e\<^sub>2 \<Longrightarrow> e\<^sub>3 \<simeq> e\<^sub>4 \<Longrightarrow> e\<^sub>1 \<cdot> e\<^sub>3 \<simeq> e\<^sub>2 \<cdot> e\<^sub>4"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>1 \<simeq> e\<^sub>2 \<Longrightarrow> e\<^sub>3 \<simeq> e\<^sub>4 \<Longrightarrow>  e\<^sub>1 \<triangle> e\<^sub>3 \<simeq> e\<^sub>2 \<triangle> e\<^sub>4"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>1 \<simeq> e\<^sub>2 \<Longrightarrow> e\<^sub>3 \<simeq> e\<^sub>4 \<Longrightarrow>  e\<^sub>1 \<nabla> e\<^sub>3 \<simeq> e\<^sub>2 \<nabla> e\<^sub>4"
  by (auto simp add: expression_equality_def)

lemma [simp]: "(e\<^sub>1 \<cdot> e\<^sub>2) \<cdot> e\<^sub>3 \<simeq> e\<^sub>1 \<cdot> e\<^sub>2 \<cdot> e\<^sub>3"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<epsilon> \<cdot> e \<simeq> e"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e \<cdot> \<epsilon> \<simeq> e"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<pi>\<^sub>1 \<triangle> \<pi>\<^sub>2 \<simeq> \<epsilon>"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>1 \<triangle> e\<^sub>2 \<cdot> e\<^sub>3 \<simeq> (e\<^sub>1 \<cdot> e\<^sub>3) \<triangle> (e\<^sub>2 \<cdot> e\<^sub>3)"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<pi>\<^sub>1 \<cdot> e\<^sub>1 \<triangle> e\<^sub>2 \<simeq> e\<^sub>1"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<pi>\<^sub>2 \<cdot> e\<^sub>1 \<triangle> e\<^sub>2 \<simeq> e\<^sub>2"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<iota>\<^sub>l \<nabla> \<iota>\<^sub>r \<simeq> \<epsilon>"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>3 \<cdot> e\<^sub>1 \<nabla> e\<^sub>2 \<simeq> (e\<^sub>3 \<cdot> e\<^sub>1) \<nabla> (e\<^sub>3 \<cdot> e\<^sub>2)"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>1 \<nabla> e\<^sub>2 \<cdot> \<iota>\<^sub>l \<simeq> e\<^sub>1"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>1 \<nabla> e\<^sub>2 \<cdot> \<iota>\<^sub>r \<simeq> e\<^sub>2"
  by (auto simp add: expression_equality_def)

lemma [simp]: "g \<cdot> f \<simeq> \<epsilon> \<Longrightarrow> g \<leftarrow> f \<simeq> \<epsilon>"
  by (auto simp add: expression_equality_def)

end
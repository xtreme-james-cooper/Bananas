theory CombinatorLaws
imports BananasLanguage
begin

(* derived combinators *)

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

(* expression equality *)

definition domain :: "expr \<Rightarrow> val set" where
  "domain e = { v. \<exists>v'. e \<cdot> v \<Down> v' }"

(* kludged in order to deal with mismatching domains - ie, polymorphic ones *)
definition expression_equality :: "expr \<Rightarrow> expr \<Rightarrow> bool" (infix "\<simeq>" 50) where
  "e\<^sub>1 \<simeq> e\<^sub>2 = ((domain e\<^sub>1 \<subseteq> domain e\<^sub>2 \<and> (\<forall>v v'. (e\<^sub>1 \<cdot> v \<Down> v') \<longrightarrow> (e\<^sub>2 \<cdot> v \<Down> v'))) 
            \<or> (domain e\<^sub>2 \<subseteq> domain e\<^sub>1 \<and> (\<forall>v v'. (e\<^sub>2 \<cdot> v \<Down> v') \<longrightarrow> (e\<^sub>1 \<cdot> v \<Down> v'))))"

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
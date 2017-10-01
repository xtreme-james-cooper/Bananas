theory CombinatorLaws
imports DerivedCombinators
begin

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

lemma [simp]: "\<epsilon> \<parallel> \<epsilon> \<simeq> \<epsilon>"
  by (auto simp add: expression_equality_def)

lemma [simp]: "(e\<^sub>1\<^sub>1 \<cdot> e\<^sub>1\<^sub>2) \<parallel> (e\<^sub>2\<^sub>1 \<cdot> e\<^sub>2\<^sub>2) \<simeq> e\<^sub>1\<^sub>1 \<parallel> e\<^sub>2\<^sub>1 \<cdot> e\<^sub>1\<^sub>2 \<parallel> e\<^sub>2\<^sub>2"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<pi>\<^sub>1 \<cdot> e\<^sub>1 \<parallel> e\<^sub>2 \<simeq> e\<^sub>1 \<cdot> \<pi>\<^sub>1"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<pi>\<^sub>2 \<cdot> e\<^sub>1 \<parallel> e\<^sub>2 \<simeq> e\<^sub>2 \<cdot> \<pi>\<^sub>2"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<iota>\<^sub>l \<nabla> \<iota>\<^sub>r \<simeq> \<epsilon>"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>3 \<cdot> e\<^sub>1 \<nabla> e\<^sub>2 \<simeq> (e\<^sub>3 \<cdot> e\<^sub>1) \<nabla> (e\<^sub>3 \<cdot> e\<^sub>2)"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>1 \<nabla> e\<^sub>2 \<cdot> \<iota>\<^sub>l \<simeq> e\<^sub>1"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>1 \<nabla> e\<^sub>2 \<cdot> \<iota>\<^sub>r \<simeq> e\<^sub>2"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<epsilon> \<bar> \<epsilon> \<simeq> \<epsilon>"
  by (auto simp add: expression_equality_def)

lemma [simp]: "(e\<^sub>1\<^sub>1 \<cdot> e\<^sub>1\<^sub>2) \<bar> (e\<^sub>2\<^sub>1 \<cdot> e\<^sub>2\<^sub>2) \<simeq> (e\<^sub>1\<^sub>1 \<bar> e\<^sub>2\<^sub>1) \<cdot> (e\<^sub>1\<^sub>2 \<bar> e\<^sub>2\<^sub>2)"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>1 \<bar> e\<^sub>2 \<cdot> \<iota>\<^sub>l \<simeq> \<iota>\<^sub>l \<cdot> e\<^sub>1"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>1 \<bar> e\<^sub>2 \<cdot> \<iota>\<^sub>r \<simeq> \<iota>\<^sub>r \<cdot> e\<^sub>2"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<epsilon> \<leftarrow> \<epsilon> \<simeq> \<epsilon>"
  by (auto simp add: expression_equality_def)

lemma [simp]: "(e\<^sub>1\<^sub>1 \<cdot> e\<^sub>1\<^sub>2) \<leftarrow> (e\<^sub>2\<^sub>1 \<cdot> e\<^sub>2\<^sub>2) \<simeq> e\<^sub>1\<^sub>1 \<leftarrow> e\<^sub>2\<^sub>1 \<cdot> e\<^sub>1\<^sub>2 \<leftarrow> e\<^sub>2\<^sub>2"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<kappa> v \<cdot> f \<simeq> \<kappa> v"
  by (auto simp add: expression_equality_def)

lemma [simp]: "? p \<cdot> f \<simeq> f \<bar> f \<cdot> ? (p \<cdot> f)"
  by (auto simp add: expression_equality_def)

end
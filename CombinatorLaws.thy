theory CombinatorLaws
imports DerivedCombinators Map
begin

(* expression equality *)

definition expression_equality :: "expr \<Rightarrow> type \<Rightarrow> expr \<Rightarrow> bool" (infix "\<simeq>\<^bsub>_\<^esub>" 50) where
  "(e\<^sub>1 \<simeq>\<^bsub>t\<^esub> e\<^sub>2) = (\<forall>v v'. v \<turnstile> t \<longrightarrow> (e\<^sub>1 \<cdot> v \<Down> v') = (e\<^sub>2 \<cdot> v \<Down> v'))"

lemma equiv_refl [simp]: "e\<^sub>1 \<simeq>\<^bsub>t\<^esub> e\<^sub>1"
  by (auto simp add: expression_equality_def)

lemma equiv_sym [sym]: "e\<^sub>1 \<simeq>\<^bsub>t\<^esub> e\<^sub>2 \<Longrightarrow> e\<^sub>2 \<simeq>\<^bsub>t\<^esub> e\<^sub>1"
  by (auto simp add: expression_equality_def)

lemma equiv_trans [simp, trans]: "e\<^sub>1 \<simeq>\<^bsub>t\<^esub> e\<^sub>2 \<Longrightarrow> e\<^sub>2 \<simeq>\<^bsub>t\<^esub> e\<^sub>3 \<Longrightarrow> e\<^sub>1 \<simeq>\<^bsub>t\<^esub> e\<^sub>3"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>1 \<simeq>\<^bsub>t\<^sub>2\<^esub> e\<^sub>2 \<Longrightarrow> e\<^sub>3 \<simeq>\<^bsub>t\<^sub>1\<^esub> e\<^sub>4 \<Longrightarrow> e\<^sub>1 \<cdot> e\<^sub>3 \<simeq>\<^bsub>t\<^sub>1\<^esub> e\<^sub>2 \<cdot> e\<^sub>4"
  proof (unfold expression_equality_def, rule, rule, rule)
    fix v v'
    assume "\<forall>v v'. v \<turnstile> t\<^sub>2 \<longrightarrow> (e\<^sub>1 \<cdot> v \<Down> v') = e\<^sub>2 \<cdot> v \<Down> v'"
    assume "\<forall>v v'. v \<turnstile> t\<^sub>1 \<longrightarrow> (e\<^sub>3 \<cdot> v \<Down> v') = e\<^sub>4 \<cdot> v \<Down> v'"
    assume "v \<turnstile> t\<^sub>1"

    show "((e\<^sub>1 \<cdot> e\<^sub>3) \<cdot> v \<Down> v') = (e\<^sub>2 \<cdot> e\<^sub>4) \<cdot> v \<Down> v'" by simp
  qed

lemma [simp]: "e\<^sub>1 \<simeq>\<^bsub>t\<^sub>1\<^esub> e\<^sub>2 \<Longrightarrow> e\<^sub>3 \<simeq>\<^bsub>t\<^sub>2\<^esub> e\<^sub>4 \<Longrightarrow> e\<^sub>1 \<triangle> e\<^sub>3 \<simeq>\<^bsub>t\<^sub>1 \<otimes> t\<^sub>2\<^esub> e\<^sub>2 \<triangle> e\<^sub>4"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>1 \<simeq>\<^bsub>t\<^sub>1\<^esub> e\<^sub>2 \<Longrightarrow> e\<^sub>3 \<simeq>\<^bsub>t\<^sub>2\<^esub> e\<^sub>4 \<Longrightarrow>  e\<^sub>1 \<nabla> e\<^sub>3 \<simeq>\<^bsub>t\<^sub>1 \<oplus> t\<^sub>2\<^esub> e\<^sub>2 \<nabla> e\<^sub>4"
  by (auto simp add: expression_equality_def)

lemma [simp]: "(e\<^sub>1 \<cdot> e\<^sub>2) \<cdot> e\<^sub>3 \<simeq>\<^bsub>t\<^esub> e\<^sub>1 \<cdot> e\<^sub>2 \<cdot> e\<^sub>3"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<epsilon> \<cdot> e \<simeq>\<^bsub>t\<^esub> e"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e \<cdot> \<epsilon> \<simeq>\<^bsub>t\<^esub> e"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<pi>\<^sub>1 \<triangle> \<pi>\<^sub>2 \<simeq>\<^bsub>t\<^sub>1 \<otimes> t\<^sub>2\<^esub> \<epsilon>"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>1 \<triangle> e\<^sub>2 \<cdot> e\<^sub>3 \<simeq>\<^bsub>t\<^esub> (e\<^sub>1 \<cdot> e\<^sub>3) \<triangle> (e\<^sub>2 \<cdot> e\<^sub>3)"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<pi>\<^sub>1 \<cdot> e\<^sub>1 \<triangle> e\<^sub>2 \<simeq>\<^bsub>t\<^sub>1 \<otimes> t\<^sub>2\<^esub> e\<^sub>1"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<pi>\<^sub>2 \<cdot> e\<^sub>1 \<triangle> e\<^sub>2 \<simeq>\<^bsub>t\<^sub>1 \<otimes> t\<^sub>2\<^esub> e\<^sub>2"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<epsilon> \<parallel> \<epsilon> \<simeq>\<^bsub>t\<^sub>1 \<otimes> t\<^sub>2\<^esub> \<epsilon>"
  by (auto simp add: expression_equality_def)

lemma [simp]: "(e\<^sub>1\<^sub>1 \<cdot> e\<^sub>1\<^sub>2) \<parallel> (e\<^sub>2\<^sub>1 \<cdot> e\<^sub>2\<^sub>2) \<simeq>\<^bsub>t\<^sub>1 \<otimes> t\<^sub>2\<^esub> e\<^sub>1\<^sub>1 \<parallel> e\<^sub>2\<^sub>1 \<cdot> e\<^sub>1\<^sub>2 \<parallel> e\<^sub>2\<^sub>2"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<pi>\<^sub>1 \<cdot> e\<^sub>1 \<parallel> e\<^sub>2 \<simeq>\<^bsub>t\<^sub>1 \<otimes> t\<^sub>2\<^esub> e\<^sub>1 \<cdot> \<pi>\<^sub>1"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<pi>\<^sub>2 \<cdot> e\<^sub>1 \<parallel> e\<^sub>2 \<simeq>\<^bsub>t\<^sub>1 \<otimes> t\<^sub>2\<^esub> e\<^sub>2 \<cdot> \<pi>\<^sub>2"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<iota>\<^sub>l \<nabla> \<iota>\<^sub>r \<simeq>\<^bsub>t\<^sub>1 \<oplus> t\<^sub>2\<^esub> \<epsilon>"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>3 \<cdot> e\<^sub>1 \<nabla> e\<^sub>2 \<simeq>\<^bsub>t\<^sub>1 \<oplus> t\<^sub>2\<^esub> (e\<^sub>3 \<cdot> e\<^sub>1) \<nabla> (e\<^sub>3 \<cdot> e\<^sub>2)"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>1 \<nabla> e\<^sub>2 \<cdot> \<iota>\<^sub>l \<simeq>\<^bsub>t\<^esub> e\<^sub>1"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>1 \<nabla> e\<^sub>2 \<cdot> \<iota>\<^sub>r \<simeq>\<^bsub>t\<^esub> e\<^sub>2"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<epsilon> \<bar> \<epsilon> \<simeq>\<^bsub>t\<^sub>1 \<oplus> t\<^sub>2\<^esub> \<epsilon>"
  by (auto simp add: expression_equality_def)

lemma [simp]: "(e\<^sub>1\<^sub>1 \<cdot> e\<^sub>1\<^sub>2) \<bar> (e\<^sub>2\<^sub>1 \<cdot> e\<^sub>2\<^sub>2) \<simeq>\<^bsub>t\<^sub>1 \<oplus> t\<^sub>2\<^esub> (e\<^sub>1\<^sub>1 \<bar> e\<^sub>2\<^sub>1) \<cdot> (e\<^sub>1\<^sub>2 \<bar> e\<^sub>2\<^sub>2)"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>1 \<bar> e\<^sub>2 \<cdot> \<iota>\<^sub>l \<simeq>\<^bsub>t\<^esub> \<iota>\<^sub>l \<cdot> e\<^sub>1"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>1 \<bar> e\<^sub>2 \<cdot> \<iota>\<^sub>r \<simeq>\<^bsub>t\<^esub> \<iota>\<^sub>r \<cdot> e\<^sub>2"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<epsilon> \<leftarrow> \<epsilon> \<simeq>\<^bsub>t\<^esub> \<epsilon>"
  by (auto simp add: expression_equality_def)

lemma [simp]: "(e\<^sub>1\<^sub>1 \<cdot> e\<^sub>1\<^sub>2) \<leftarrow> (e\<^sub>2\<^sub>1 \<cdot> e\<^sub>2\<^sub>2) \<simeq>\<^bsub>t\<^esub> e\<^sub>1\<^sub>1 \<leftarrow> e\<^sub>2\<^sub>1 \<cdot> e\<^sub>1\<^sub>2 \<leftarrow> e\<^sub>2\<^sub>2"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<kappa> v \<cdot> f \<simeq>\<^bsub>t\<^esub> \<kappa> v"
  by (auto simp add: expression_equality_def)

lemma [simp]: "p? \<cdot> f \<simeq>\<^bsub>t\<^esub> f \<bar> f \<cdot> ((p \<cdot> f)?)"
  by (auto simp add: expression_equality_def)

end
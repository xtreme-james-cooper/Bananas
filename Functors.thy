theory Functors
imports CombinatorLaws
begin

definition monofunctor :: "(type \<Rightarrow> type) \<Rightarrow> (expr \<Rightarrow> expr) \<Rightarrow> bool" where
  "monofunctor F f = (
     (\<forall>e t\<^sub>1 t\<^sub>2. (e \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2) \<longrightarrow> (f e \<turnstile> F t\<^sub>1 \<rightarrow> F t\<^sub>2)) 
       \<and> f \<epsilon> \<simeq> \<epsilon> 
       \<and> (\<forall>e\<^sub>1 e\<^sub>2. f (e\<^sub>1 \<cdot> e\<^sub>2) \<simeq> f e\<^sub>1 \<cdot> f e\<^sub>2))"

definition bifunctor :: "(type \<Rightarrow> type \<Rightarrow>  type) \<Rightarrow> (expr \<Rightarrow> expr \<Rightarrow> expr) \<Rightarrow> bool" where
  "bifunctor F f = (
     (\<forall>e\<^sub>1 e\<^sub>2 t\<^sub>1\<^sub>1 t\<^sub>1\<^sub>2 t\<^sub>2\<^sub>1 t\<^sub>2\<^sub>2. (e\<^sub>1 \<turnstile> t\<^sub>1\<^sub>1 \<rightarrow> t\<^sub>1\<^sub>2) \<longrightarrow> (e\<^sub>2 \<turnstile> t\<^sub>2\<^sub>1 \<rightarrow> t\<^sub>2\<^sub>2) \<longrightarrow> (f e\<^sub>1 e\<^sub>2 \<turnstile> F t\<^sub>1\<^sub>1 t\<^sub>2\<^sub>1 \<rightarrow> F t\<^sub>1\<^sub>2 t\<^sub>2\<^sub>2)) 
       \<and> f \<epsilon> \<epsilon> \<simeq> \<epsilon> 
       \<and> (\<forall>e\<^sub>1\<^sub>1 e\<^sub>1\<^sub>2 e\<^sub>2\<^sub>1 e\<^sub>2\<^sub>2. f (e\<^sub>1\<^sub>1 \<cdot> e\<^sub>1\<^sub>2) (e\<^sub>2\<^sub>1 \<cdot> e\<^sub>2\<^sub>2) \<simeq> f e\<^sub>1\<^sub>1 e\<^sub>2\<^sub>1 \<cdot> f e\<^sub>1\<^sub>2 e\<^sub>2\<^sub>2))"

lemma [simp]: "(\<epsilon> \<cdot> \<pi>\<^sub>1) \<triangle> (\<epsilon> \<cdot> \<pi>\<^sub>2) \<simeq> \<epsilon>" 
  proof -
    have "(\<epsilon> \<cdot> \<pi>\<^sub>1) \<triangle> (\<epsilon> \<cdot> \<pi>\<^sub>2) \<simeq> \<pi>\<^sub>1 \<triangle> \<pi>\<^sub>2" by simp
    moreover have "\<pi>\<^sub>1 \<triangle> \<pi>\<^sub>2 \<simeq> \<epsilon>" by simp
    ultimately show "(\<epsilon> \<cdot> \<pi>\<^sub>1) \<triangle> (\<epsilon> \<cdot> \<pi>\<^sub>2) \<simeq> \<epsilon>" by (metis equiv_trans)
  qed

lemma [simp]: "((e\<^sub>1\<^sub>1 \<cdot> e\<^sub>1\<^sub>2) \<cdot> \<pi>\<^sub>1) \<triangle> ((e\<^sub>2\<^sub>1 \<cdot> e\<^sub>2\<^sub>2) \<cdot> \<pi>\<^sub>2) \<simeq> (e\<^sub>1\<^sub>1 \<cdot> \<pi>\<^sub>1) \<triangle> (e\<^sub>2\<^sub>1 \<cdot> \<pi>\<^sub>2) \<cdot> (e\<^sub>1\<^sub>2 \<cdot> \<pi>\<^sub>1) \<triangle> (e\<^sub>2\<^sub>2 \<cdot> \<pi>\<^sub>2)"
  proof -
    have "(e\<^sub>1\<^sub>1 \<cdot> \<pi>\<^sub>1) \<cdot> (e\<^sub>1\<^sub>2 \<cdot> \<pi>\<^sub>1) \<triangle> (e\<^sub>2\<^sub>2 \<cdot> \<pi>\<^sub>2) \<simeq> e\<^sub>1\<^sub>1 \<cdot> \<pi>\<^sub>1 \<cdot> (e\<^sub>1\<^sub>2 \<cdot> \<pi>\<^sub>1) \<triangle> (e\<^sub>2\<^sub>2 \<cdot> \<pi>\<^sub>2)" by simp
    moreover have "e\<^sub>1\<^sub>1 \<cdot> \<pi>\<^sub>1 \<cdot> (e\<^sub>1\<^sub>2 \<cdot> \<pi>\<^sub>1) \<triangle> (e\<^sub>2\<^sub>2 \<cdot> \<pi>\<^sub>2) \<simeq> e\<^sub>1\<^sub>1 \<cdot> e\<^sub>1\<^sub>2 \<cdot> \<pi>\<^sub>1" by simp
    moreover have "(e\<^sub>1\<^sub>1 \<cdot> e\<^sub>1\<^sub>2) \<cdot> \<pi>\<^sub>1 \<simeq> e\<^sub>1\<^sub>1 \<cdot> e\<^sub>1\<^sub>2 \<cdot> \<pi>\<^sub>1" by simp
    ultimately have X: "(e\<^sub>1\<^sub>1 \<cdot> \<pi>\<^sub>1) \<cdot> (e\<^sub>1\<^sub>2 \<cdot> \<pi>\<^sub>1) \<triangle> (e\<^sub>2\<^sub>2 \<cdot> \<pi>\<^sub>2) \<simeq> (e\<^sub>1\<^sub>1 \<cdot> e\<^sub>1\<^sub>2) \<cdot> \<pi>\<^sub>1" 
      by (metis equiv_trans equiv_sym)
    have "(e\<^sub>2\<^sub>1 \<cdot> \<pi>\<^sub>2) \<cdot> (e\<^sub>1\<^sub>2 \<cdot> \<pi>\<^sub>1) \<triangle> (e\<^sub>2\<^sub>2 \<cdot> \<pi>\<^sub>2) \<simeq> e\<^sub>2\<^sub>1 \<cdot> \<pi>\<^sub>2 \<cdot> (e\<^sub>1\<^sub>2 \<cdot> \<pi>\<^sub>1) \<triangle> (e\<^sub>2\<^sub>2 \<cdot> \<pi>\<^sub>2)" by simp
    moreover have "e\<^sub>2\<^sub>1 \<cdot> \<pi>\<^sub>2 \<cdot> (e\<^sub>1\<^sub>2 \<cdot> \<pi>\<^sub>1) \<triangle> (e\<^sub>2\<^sub>2 \<cdot> \<pi>\<^sub>2) \<simeq> e\<^sub>2\<^sub>1 \<cdot> e\<^sub>2\<^sub>2 \<cdot> \<pi>\<^sub>2" by simp
    moreover have "(e\<^sub>2\<^sub>1 \<cdot> e\<^sub>2\<^sub>2) \<cdot> \<pi>\<^sub>2 \<simeq> e\<^sub>2\<^sub>1 \<cdot> e\<^sub>2\<^sub>2 \<cdot> \<pi>\<^sub>2" by simp
    ultimately have Y: "(e\<^sub>2\<^sub>1 \<cdot> \<pi>\<^sub>2) \<cdot> (e\<^sub>1\<^sub>2 \<cdot> \<pi>\<^sub>1) \<triangle> (e\<^sub>2\<^sub>2 \<cdot> \<pi>\<^sub>2) \<simeq> (e\<^sub>2\<^sub>1 \<cdot> e\<^sub>2\<^sub>2) \<cdot> \<pi>\<^sub>2" 
      by (metis equiv_trans equiv_sym)
    have "(e\<^sub>1\<^sub>1 \<cdot> \<pi>\<^sub>1) \<triangle> (e\<^sub>2\<^sub>1 \<cdot> \<pi>\<^sub>2) \<cdot> (e\<^sub>1\<^sub>2 \<cdot> \<pi>\<^sub>1) \<triangle> (e\<^sub>2\<^sub>2 \<cdot> \<pi>\<^sub>2) \<simeq> 
      ((e\<^sub>1\<^sub>1 \<cdot> \<pi>\<^sub>1) \<cdot> (e\<^sub>1\<^sub>2 \<cdot> \<pi>\<^sub>1) \<triangle> (e\<^sub>2\<^sub>2 \<cdot> \<pi>\<^sub>2)) \<triangle> ((e\<^sub>2\<^sub>1 \<cdot> \<pi>\<^sub>2) \<cdot> (e\<^sub>1\<^sub>2 \<cdot> \<pi>\<^sub>1) \<triangle> (e\<^sub>2\<^sub>2 \<cdot> \<pi>\<^sub>2))" by simp
    moreover with X Y have "((e\<^sub>1\<^sub>1 \<cdot> \<pi>\<^sub>1) \<cdot> (e\<^sub>1\<^sub>2 \<cdot> \<pi>\<^sub>1) \<triangle> (e\<^sub>2\<^sub>2 \<cdot> \<pi>\<^sub>2)) \<triangle> ((e\<^sub>2\<^sub>1 \<cdot> \<pi>\<^sub>2) \<cdot> (e\<^sub>1\<^sub>2 \<cdot> \<pi>\<^sub>1) \<triangle> (e\<^sub>2\<^sub>2 \<cdot> \<pi>\<^sub>2)) \<simeq> 
      ((e\<^sub>1\<^sub>1 \<cdot> e\<^sub>1\<^sub>2) \<cdot> \<pi>\<^sub>1) \<triangle> ((e\<^sub>2\<^sub>1 \<cdot> e\<^sub>2\<^sub>2) \<cdot> \<pi>\<^sub>2)" by simp
    ultimately have "(e\<^sub>1\<^sub>1 \<cdot> \<pi>\<^sub>1) \<triangle> (e\<^sub>2\<^sub>1 \<cdot> \<pi>\<^sub>2) \<cdot> (e\<^sub>1\<^sub>2 \<cdot> \<pi>\<^sub>1) \<triangle> (e\<^sub>2\<^sub>2 \<cdot> \<pi>\<^sub>2) \<simeq> 
      ((e\<^sub>1\<^sub>1 \<cdot> e\<^sub>1\<^sub>2) \<cdot> \<pi>\<^sub>1) \<triangle> ((e\<^sub>2\<^sub>1 \<cdot> e\<^sub>2\<^sub>2) \<cdot> \<pi>\<^sub>2)" using equiv_trans by blast
    thus "((e\<^sub>1\<^sub>1 \<cdot> e\<^sub>1\<^sub>2) \<cdot> \<pi>\<^sub>1) \<triangle> ((e\<^sub>2\<^sub>1 \<cdot> e\<^sub>2\<^sub>2) \<cdot> \<pi>\<^sub>2) \<simeq> (e\<^sub>1\<^sub>1 \<cdot> \<pi>\<^sub>1) \<triangle> (e\<^sub>2\<^sub>1 \<cdot> \<pi>\<^sub>2) \<cdot> (e\<^sub>1\<^sub>2 \<cdot> \<pi>\<^sub>1) \<triangle> (e\<^sub>2\<^sub>2 \<cdot> \<pi>\<^sub>2)" 
      by (metis equiv_sym)
  qed

theorem prod_bifunctor: "bifunctor (op \<otimes>) (\<lambda>f g. (f \<cdot> \<pi>\<^sub>1) \<triangle> (g \<cdot> \<pi>\<^sub>2))"
  by (simp add: bifunctor_def)

lemma [simp]: "e\<^sub>1 \<turnstile> t\<^sub>1\<^sub>1 \<rightarrow> t\<^sub>1\<^sub>2 \<Longrightarrow> e\<^sub>2 \<turnstile> t\<^sub>2\<^sub>1 \<rightarrow> t\<^sub>2\<^sub>2 \<Longrightarrow> (\<iota>\<^sub>l \<cdot> e\<^sub>1) \<nabla> (\<iota>\<^sub>r \<cdot> e\<^sub>2) \<turnstile> t\<^sub>1\<^sub>1 \<oplus> t\<^sub>2\<^sub>1 \<rightarrow> t\<^sub>1\<^sub>2 \<oplus> t\<^sub>2\<^sub>2"
  proof -
    assume "e\<^sub>1 \<turnstile> t\<^sub>1\<^sub>1 \<rightarrow> t\<^sub>1\<^sub>2"
    moreover have "\<iota>\<^sub>l \<turnstile> t\<^sub>1\<^sub>2 \<rightarrow> t\<^sub>1\<^sub>2 \<oplus> t\<^sub>2\<^sub>2" by simp
    ultimately have X: "\<iota>\<^sub>l \<cdot> e\<^sub>1 \<turnstile> t\<^sub>1\<^sub>1 \<rightarrow> t\<^sub>1\<^sub>2 \<oplus> t\<^sub>2\<^sub>2" by (metis tc_comp)
    assume "e\<^sub>2 \<turnstile> t\<^sub>2\<^sub>1 \<rightarrow> t\<^sub>2\<^sub>2"
    moreover have "\<iota>\<^sub>r \<turnstile> t\<^sub>2\<^sub>2 \<rightarrow> t\<^sub>1\<^sub>2 \<oplus> t\<^sub>2\<^sub>2" by simp
    ultimately have "\<iota>\<^sub>r \<cdot> e\<^sub>2 \<turnstile> t\<^sub>2\<^sub>1 \<rightarrow> t\<^sub>1\<^sub>2 \<oplus> t\<^sub>2\<^sub>2" by (metis tc_comp)
    with X show "(\<iota>\<^sub>l \<cdot> e\<^sub>1) \<nabla> (\<iota>\<^sub>r \<cdot> e\<^sub>2) \<turnstile> t\<^sub>1\<^sub>1 \<oplus> t\<^sub>2\<^sub>1 \<rightarrow> t\<^sub>1\<^sub>2 \<oplus> t\<^sub>2\<^sub>2" by simp
  qed

lemma [simp]: "(\<iota>\<^sub>l \<cdot> \<epsilon>) \<nabla> (\<iota>\<^sub>r \<cdot> \<epsilon>) \<simeq> \<epsilon>"
  proof -
    have "(\<iota>\<^sub>l \<cdot> \<epsilon>) \<nabla> (\<iota>\<^sub>r \<cdot> \<epsilon>) \<simeq> \<iota>\<^sub>l \<nabla> \<iota>\<^sub>r" by simp
    moreover have "\<iota>\<^sub>l \<nabla> \<iota>\<^sub>r \<simeq> \<epsilon>" by simp
    ultimately show "(\<iota>\<^sub>l \<cdot> \<epsilon>) \<nabla> (\<iota>\<^sub>r \<cdot> \<epsilon>) \<simeq> \<epsilon>" by (metis equiv_trans)
  qed

lemma [simp]: "(\<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>1 \<cdot> e\<^sub>1\<^sub>2) \<nabla> (\<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>1 \<cdot> e\<^sub>2\<^sub>2) \<simeq> (\<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>1) \<nabla> (\<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>1) \<cdot> (\<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>2) \<nabla> (\<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>2)"
  proof -
    have "(((\<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>1) \<nabla> (\<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>1) \<cdot> \<iota>\<^sub>l) \<cdot> e\<^sub>1\<^sub>2) \<nabla> (((\<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>1) \<nabla> (\<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>1) \<cdot> \<iota>\<^sub>r) \<cdot> e\<^sub>2\<^sub>2) \<simeq> 
      ((\<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>1) \<nabla> (\<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>1) \<cdot> \<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>2) \<nabla> ((\<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>1) \<nabla> (\<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>1) \<cdot> \<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>2)" by simp
    hence "((\<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>1) \<nabla> (\<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>1) \<cdot> \<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>2) \<nabla> ((\<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>1) \<nabla> (\<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>1) \<cdot> \<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>2) \<simeq> 
      (((\<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>1) \<nabla> (\<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>1) \<cdot> \<iota>\<^sub>l) \<cdot> e\<^sub>1\<^sub>2) \<nabla> (((\<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>1) \<nabla> (\<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>1) \<cdot> \<iota>\<^sub>r) \<cdot> e\<^sub>2\<^sub>2)" by (metis equiv_sym)
    moreover have "(\<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>1) \<nabla> (\<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>1) \<cdot> (\<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>2) \<nabla> (\<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>2) \<simeq> 
      ((\<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>1) \<nabla> (\<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>1) \<cdot> \<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>2) \<nabla> ((\<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>1) \<nabla> (\<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>1) \<cdot> \<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>2)" by simp
    moreover have "(((\<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>1) \<nabla> (\<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>1) \<cdot> \<iota>\<^sub>l) \<cdot> e\<^sub>1\<^sub>2) \<nabla> (((\<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>1) \<nabla> (\<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>1) \<cdot> \<iota>\<^sub>r) \<cdot> e\<^sub>2\<^sub>2) \<simeq> 
      ((\<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>1) \<cdot> e\<^sub>1\<^sub>2) \<nabla> ((\<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>1) \<cdot> e\<^sub>2\<^sub>2)" by simp
    moreover have "((\<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>1) \<cdot> e\<^sub>1\<^sub>2) \<nabla> ((\<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>1) \<cdot> e\<^sub>2\<^sub>2) \<simeq> (\<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>1 \<cdot> e\<^sub>1\<^sub>2) \<nabla> (\<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>1 \<cdot> e\<^sub>2\<^sub>2)" by simp
    ultimately have "(\<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>1) \<nabla> (\<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>1) \<cdot> (\<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>2) \<nabla> (\<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>2) \<simeq> (\<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>1 \<cdot> e\<^sub>1\<^sub>2) \<nabla> (\<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>1 \<cdot> e\<^sub>2\<^sub>2)" 
      using equiv_trans by blast
    thus "(\<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>1 \<cdot> e\<^sub>1\<^sub>2) \<nabla> (\<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>1 \<cdot> e\<^sub>2\<^sub>2) \<simeq> (\<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>1) \<nabla> (\<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>1) \<cdot> (\<iota>\<^sub>l \<cdot> e\<^sub>1\<^sub>2) \<nabla> (\<iota>\<^sub>r \<cdot> e\<^sub>2\<^sub>2)" 
      by (metis equiv_sym)
  qed

theorem sum_bifunctor: "bifunctor (op \<oplus>) (\<lambda>f g. (\<iota>\<^sub>l \<cdot> f) \<nabla> (\<iota>\<^sub>r \<cdot> g))"
  by (simp add: bifunctor_def)

theorem arrow_bifunctor: "bifunctor (op \<hookrightarrow>) (\<lambda>f g. g \<leftarrow> f)"
  by (simp add: bifunctor_def)

end
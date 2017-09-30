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

lemma prod_bifunctor: "bifunctor (op \<otimes>) (\<lambda>f g. (f \<cdot> \<pi>\<^sub>1) \<triangle> (g \<cdot> \<pi>\<^sub>2))"
  by (simp add: bifunctor_def)

end
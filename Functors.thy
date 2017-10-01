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

theorem identity_monofunctor: "monofunctor id id"
  by (simp add: monofunctor_def)

theorem const_monofunctor: "monofunctor (\<lambda>_. t) (\<lambda>_. \<epsilon>)"
  proof -    
    have "\<epsilon> \<cdot> \<epsilon> \<simeq> \<epsilon>" by simp
    hence "\<epsilon> \<simeq> \<epsilon> \<cdot> \<epsilon>" by (metis equiv_sym)
    thus ?thesis by (simp add: monofunctor_def)
  qed

theorem lifted_monofunctor: "monofunctor F f \<Longrightarrow> monofunctor G g \<Longrightarrow> monofunctor (G o F) (g o f)"
  by (simp add: monofunctor_def)

theorem lifted_bifunctor: "monofunctor F f \<Longrightarrow> monofunctor G g \<Longrightarrow> bifunctor H h \<Longrightarrow> 
    monofunctor (\<lambda>t. H (G t) (F t)) (\<lambda>e. h (g e) (f e))"
  by (simp add: monofunctor_def bifunctor_def)

theorem prod_bifunctor: "bifunctor (op \<otimes>) (op \<parallel>)"
  by (simp add: bifunctor_def)

theorem sum_bifunctor: "bifunctor (op \<oplus>) (op \<bar>)"
  by (simp add: bifunctor_def)

theorem arrow_bifunctor: "bifunctor (op \<hookrightarrow>) (op \<leftarrow>)"
  by (simp add: bifunctor_def) (* not solved because the contravariant types don't line up :( *)

end
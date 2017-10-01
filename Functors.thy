theory Functors
imports CombinatorLaws
begin

datatype monofunctor = MONOF "type \<Rightarrow> type" "expr \<Rightarrow> expr"
datatype bifunctor = BIF "type \<Rightarrow> type \<Rightarrow> type" "expr \<Rightarrow> expr \<Rightarrow> expr"

definition identity_monof :: "monofunctor" where
  "identity_monof = MONOF id id"

definition const_monof :: "type \<Rightarrow> monofunctor" where
  "const_monof t = MONOF (\<lambda>_. t) (\<lambda>_. \<epsilon>)"

fun comp_monof :: "monofunctor \<Rightarrow> monofunctor \<Rightarrow> monofunctor" where
  "comp_monof (MONOF F f) (MONOF G g) = MONOF (G o F) (g o f)"

fun comp_bif :: "monofunctor \<Rightarrow> monofunctor \<Rightarrow> bifunctor \<Rightarrow> monofunctor" where
  "comp_bif (MONOF F f) (MONOF G g) (BIF H h) = MONOF (\<lambda>t. H (G t) (F t)) (\<lambda>e. h (g e) (f e))"

primrec section\<^sub>L_bif :: "bifunctor \<Rightarrow> type \<Rightarrow> monofunctor" where
  "section\<^sub>L_bif (BIF F f) t = MONOF (F t) (f \<epsilon>)"

primrec section\<^sub>R_bif :: "bifunctor \<Rightarrow> type \<Rightarrow> monofunctor" where
  "section\<^sub>R_bif (BIF F f) t = MONOF (\<lambda>x. F x t) (\<lambda>x. f x \<epsilon>)"

definition prod_bif :: bifunctor where
  "prod_bif = BIF (op \<otimes>) (op \<parallel>)"

definition sum_bif :: bifunctor where
  "sum_bif = BIF (op \<oplus>) (op \<bar>)"

definition arrow_bif :: bifunctor where
  "arrow_bif = BIF (op \<hookrightarrow>) (op \<leftarrow>)"

(* mono/bifunctor rules *)

primrec apply_monofunctor_type :: "type \<Rightarrow> monofunctor \<Rightarrow> type" (infixl "\<rangle>\<rangle>" 70) where
  "t \<rangle>\<rangle> MONOF F f = F t"

primrec apply_monofunctor_expr :: "expr \<Rightarrow> monofunctor \<Rightarrow> expr" (infixl "\<rangle>" 70) where
  "e \<rangle> MONOF F f = f e"

primrec apply_bifunctor_type :: "type \<Rightarrow> bifunctor \<Rightarrow> type \<Rightarrow> type" (infixl "\<langle>\<langle> _ \<rangle>\<rangle>" 70) where
  "(t\<^sub>1 \<langle>\<langle> BIF F f \<rangle>\<rangle> t\<^sub>2) = F t\<^sub>1 t\<^sub>2"

primrec apply_bifunctor_expr :: "expr \<Rightarrow> bifunctor \<Rightarrow> expr \<Rightarrow> expr" (infixl "\<langle> _ \<rangle>" 70) where
  "(e\<^sub>1 \<langle> BIF F f \<rangle> e\<^sub>2) = f e\<^sub>1 e\<^sub>2"

definition valid_monofunctor :: "monofunctor \<Rightarrow> bool" where
  "valid_monofunctor F = (
     (\<forall>e t\<^sub>1 t\<^sub>2. (e \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2) \<longrightarrow> (e \<rangle> F \<turnstile> t\<^sub>1 \<rangle>\<rangle> F \<rightarrow> t\<^sub>2 \<rangle>\<rangle> F)) 
       \<and> \<epsilon> \<rangle> F \<simeq> \<epsilon> 
       \<and> (\<forall>e\<^sub>1 e\<^sub>2. (e\<^sub>1 \<cdot> e\<^sub>2) \<rangle> F \<simeq> e\<^sub>1 \<rangle> F \<cdot> e\<^sub>2 \<rangle> F))"

definition valid_bifunctor :: "bifunctor \<Rightarrow> bool" where
  "valid_bifunctor F = (
     (\<forall>e\<^sub>1 e\<^sub>2 t\<^sub>1\<^sub>1 t\<^sub>1\<^sub>2 t\<^sub>2\<^sub>1 t\<^sub>2\<^sub>2. (e\<^sub>1 \<turnstile> t\<^sub>1\<^sub>1 \<rightarrow> t\<^sub>1\<^sub>2) \<longrightarrow> (e\<^sub>2 \<turnstile> t\<^sub>2\<^sub>1 \<rightarrow> t\<^sub>2\<^sub>2) \<longrightarrow> ((e\<^sub>1 \<langle> F \<rangle> e\<^sub>2) \<turnstile> (t\<^sub>1\<^sub>1 \<langle>\<langle> F \<rangle>\<rangle> t\<^sub>2\<^sub>1) \<rightarrow> (t\<^sub>1\<^sub>2 \<langle>\<langle> F \<rangle>\<rangle> t\<^sub>2\<^sub>2))) 
       \<and> (\<epsilon> \<langle> F \<rangle> \<epsilon>) \<simeq> \<epsilon> 
       \<and> (\<forall>e\<^sub>1\<^sub>1 e\<^sub>1\<^sub>2 e\<^sub>2\<^sub>1 e\<^sub>2\<^sub>2. ((e\<^sub>1\<^sub>1 \<cdot> e\<^sub>1\<^sub>2) \<langle> F \<rangle> (e\<^sub>2\<^sub>1 \<cdot> e\<^sub>2\<^sub>2)) \<simeq> (e\<^sub>1\<^sub>1 \<langle> F \<rangle> e\<^sub>2\<^sub>1) \<cdot> (e\<^sub>1\<^sub>2 \<langle> F \<rangle> e\<^sub>2\<^sub>2)))"

lemma [simp]: "valid_monofunctor identity_monof"
  by (simp add: identity_monof_def valid_monofunctor_def)

lemma [simp]: "valid_monofunctor (const_monof t)"
  proof -    
    have "\<epsilon> \<cdot> \<epsilon> \<simeq> \<epsilon>" by simp
    hence "\<epsilon> \<simeq> \<epsilon> \<cdot> \<epsilon>" by (metis equiv_sym)
    thus ?thesis by (simp add: const_monof_def valid_monofunctor_def)
  qed

lemma [simp]: "valid_monofunctor F \<Longrightarrow> valid_monofunctor G \<Longrightarrow> valid_monofunctor (comp_monof F G)"
  by (induction F G rule: comp_monof.induct) (simp_all add: valid_monofunctor_def)

lemma [simp]: "valid_monofunctor F \<Longrightarrow> valid_monofunctor G \<Longrightarrow> valid_bifunctor H \<Longrightarrow> 
    valid_monofunctor (comp_bif F G H)"
  by (induction F G H rule: comp_bif.induct) (simp_all add: valid_monofunctor_def valid_bifunctor_def)

lemma [simp]: "valid_bifunctor F \<Longrightarrow> valid_monofunctor (section_bif F t)"
  by (induction F) (simp_all add: valid_monofunctor_def valid_bifunctor_def)

lemma [simp]: "t\<^sub>2 \<rangle>\<rangle> section\<^sub>L_bif F t\<^sub>1 = t\<^sub>1 \<langle>\<langle> F \<rangle>\<rangle> t\<^sub>2"
  by (induction F) simp_all

lemma [simp]: "e\<^sub>2 \<rangle> section\<^sub>L_bif F e\<^sub>1 = \<epsilon> \<langle> F \<rangle> e\<^sub>2"
  by (induction F) simp_all

lemma [simp]: "t\<^sub>1 \<rangle>\<rangle> section\<^sub>R_bif F t\<^sub>2 = t\<^sub>1 \<langle>\<langle> F \<rangle>\<rangle> t\<^sub>2"
  by (induction F) simp_all

lemma [simp]: "e\<^sub>1 \<rangle> section\<^sub>R_bif F e\<^sub>2 = e\<^sub>1 \<langle> F \<rangle> \<epsilon>"
  by (induction F) simp_all

lemma [simp]: "valid_bifunctor prod_bif"
  by (simp add: prod_bif_def valid_bifunctor_def)

lemma [simp]: "valid_bifunctor sum_bif"
  by (simp add: sum_bif_def valid_bifunctor_def)

lemma [simp]: "valid_bifunctor arrow_bif"
  by (simp add: arrow_bif_def valid_bifunctor_def) (* not solved because the contravariant types don't line up :( *)

end
theory Bananas
imports Main
begin

datatype type = 
  Unit
| Prod type type
| Sum type type
| Func type type (infixr "\<rightarrow>" 80)
| Mu funct
and funct =
  Id
| K type
| ProdF funct funct
| SumF funct funct

primrec apply_functor :: "funct \<Rightarrow> type \<Rightarrow> type" where
  "apply_functor Id t = t"
| "apply_functor (K t') t = t'"
| "apply_functor (ProdF f\<^sub>1 f\<^sub>2) t = Prod (apply_functor f\<^sub>1 t) (apply_functor f\<^sub>2 t)"
| "apply_functor (SumF f\<^sub>1 f\<^sub>2) t = Sum (apply_functor f\<^sub>1 t) (apply_functor f\<^sub>2 t)"

datatype expr = 
  Apply expr expr (infixl "\<star>" 80)
| UnitV
| Pair | Fst | Snd
| Inl | Inr | Case
| Inj funct | Outj funct

inductive typecheck :: "expr \<Rightarrow> type \<Rightarrow> bool" (infix "\<turnstile>" 60) where
  tc_app [simp]: "e\<^sub>1 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> e\<^sub>2 \<turnstile> t\<^sub>1 \<Longrightarrow> e\<^sub>1 \<star> e\<^sub>2 \<turnstile> t\<^sub>2"
| tc_unit [simp]: "UnitV \<turnstile> Unit"
| tc_pair [simp]: "Pair \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<rightarrow> Prod t\<^sub>1 t\<^sub>2"
| tc_fst [simp]: "Fst \<turnstile> Prod t\<^sub>1 t\<^sub>2 \<rightarrow> t\<^sub>1"
| tc_snd [simp]: "Snd \<turnstile> Prod t\<^sub>1 t\<^sub>2 \<rightarrow> t\<^sub>2"
| tc_inl [simp]: "Inl \<turnstile> t\<^sub>1 \<rightarrow> Sum t\<^sub>1 t\<^sub>2"
| tc_inr [simp]: "Inr \<turnstile> t\<^sub>2 \<rightarrow> Sum t\<^sub>1 t\<^sub>2"
| tc_case [simp]: "Case \<turnstile> Sum t\<^sub>1 t\<^sub>2 \<rightarrow> (t\<^sub>1 \<rightarrow> t\<^sub>3) \<rightarrow> (t\<^sub>2 \<rightarrow> t\<^sub>3) \<rightarrow> t\<^sub>3"
| tc_inj [simp]: "Inj f \<turnstile> apply_functor f (Mu f) \<rightarrow> Mu f"
| tc_outj [simp]: "Outj f \<turnstile> Mu f \<rightarrow> apply_functor f (Mu f)"

inductive_cases [elim]: "e\<^sub>1 \<star> e\<^sub>2 \<turnstile> t"
inductive_cases [elim]: "UnitV \<turnstile> t"
inductive_cases [elim]: "Pair \<turnstile> t"
inductive_cases [elim]: "Fst \<turnstile> t"
inductive_cases [elim]: "Snd \<turnstile> t"
inductive_cases [elim]: "Inl \<turnstile> t"
inductive_cases [elim]: "Inr \<turnstile> t"
inductive_cases [elim]: "Case \<turnstile> t"
inductive_cases [elim]: "Inj f \<turnstile> t"
inductive_cases [elim]: "Outj f \<turnstile> t"

fun is_value :: "expr \<Rightarrow> bool"
and is_value_1 :: "expr \<Rightarrow> bool"
and is_value_2 :: "expr \<Rightarrow> bool"
and is_value_3 :: "expr \<Rightarrow> bool" where
  "is_value (e\<^sub>1 \<star> e\<^sub>2) = (is_value_1 e\<^sub>1 \<and> is_value e\<^sub>2)"
| "is_value _ = True"
| "is_value_1 (e\<^sub>1 \<star> e\<^sub>2) = (is_value_2 e\<^sub>1 \<and> is_value e\<^sub>2)"
| "is_value_1 Fst = False"
| "is_value_1 Snd = False"
| "is_value_1 (Outj _) = False"
| "is_value_1 _ = True"
| "is_value_2 (e\<^sub>1 \<star> e\<^sub>2) = (is_value_3 e\<^sub>1 \<and> is_value e\<^sub>2)"
| "is_value_2 _ = True"
| "is_value_3 (e\<^sub>1 \<star> e\<^sub>2) = (is_value_3 e\<^sub>1 \<and> is_value e\<^sub>2)"
| "is_value_3 Case = False"
| "is_value_3 _ = True"

inductive evaluate :: "expr \<Rightarrow> expr \<Rightarrow> bool" (infix "\<leadsto>" 60) where
  ev_fun [simp]: "e\<^sub>1 \<leadsto> e\<^sub>1' \<Longrightarrow> e\<^sub>1 \<star> e\<^sub>2 \<leadsto> e\<^sub>1' \<star> e\<^sub>2"
| ev_arg [simp]: "is_value e\<^sub>1 \<Longrightarrow> e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> e\<^sub>1 \<star> e\<^sub>2 \<leadsto> e\<^sub>1 \<star> e\<^sub>2'"
| ev_fst [simp]: "Fst \<star> (Pair \<star> e\<^sub>1 \<star> e\<^sub>2) \<leadsto> e\<^sub>1"
| ev_snd [simp]: "Snd \<star> (Pair \<star> e\<^sub>1 \<star> e\<^sub>2) \<leadsto> e\<^sub>2"
| ev_csl [simp]: "Case \<star> (Inl \<star> e) \<star> fl \<star> fr \<leadsto> fl \<star> e"
| ev_csr [simp]: "Case \<star> (Inr \<star> e) \<star> fl \<star> fr \<leadsto> fr \<star> e"
| ev_out [simp]: "Outj f \<star> (Inj f \<star> e) \<leadsto> e"

theorem preservation: "e \<leadsto> e' \<Longrightarrow> e \<turnstile> t \<Longrightarrow> e' \<turnstile> t"
  proof (induction e e' arbitrary: t rule: evaluate.induct)
  case (ev_fun e\<^sub>1 e\<^sub>1' e\<^sub>2)
    then obtain tt where "e\<^sub>1 \<turnstile> tt \<rightarrow> t \<and> e\<^sub>2 \<turnstile> tt" by blast
    moreover with ev_fun have "e\<^sub>1' \<turnstile> tt \<rightarrow> t" by simp
    ultimately show ?case by auto
  next case (ev_arg e\<^sub>1 e\<^sub>2 e\<^sub>2')
    then obtain tt where "e\<^sub>1 \<turnstile> tt \<rightarrow> t \<and> e\<^sub>2 \<turnstile> tt" by blast
    moreover with ev_arg have "e\<^sub>2' \<turnstile> tt" by simp
    ultimately show ?case by auto
  qed fastforce+

theorem values_terminal: "is_value e \<Longrightarrow> \<not> (\<exists>e'. e \<leadsto> e')"
  apply (induction e)
  defer
  using evaluate.simps apply blast
  using evaluate.simps apply blast
  using evaluate.simps apply blast
  using evaluate.simps apply blast
  using evaluate.simps apply blast
  using evaluate.simps apply blast
  using evaluate.simps apply blast
  using evaluate.simps apply blast
  using evaluate.simps apply blast
  by simp

theorem progress: "e \<turnstile> t \<Longrightarrow> is_value e \<or> (\<exists>e'. e \<leadsto> e')"
  proof (induction e t rule: typecheck.induct)
  case (tc_app e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
    thus ?case by simp
  qed simp_all
 
end
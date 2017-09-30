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

primrec is_value_until :: "expr \<Rightarrow> nat \<Rightarrow> bool" where
  "is_value_until (e\<^sub>1 \<star> e\<^sub>2) n = (is_value_until e\<^sub>1 (Suc n) \<and> is_value_until e\<^sub>2 0)"
| "is_value_until UnitV n = True"
| "is_value_until Pair n = True"
| "is_value_until Fst n = (n = 0)"
| "is_value_until Snd n = (n = 0)"
| "is_value_until Inl n = True"
| "is_value_until Inr n = True"
| "is_value_until Case n = (n < 3)"
| "is_value_until (Inj f) n = True"
| "is_value_until (Outj f) n = (n = 0)"

definition is_value :: "expr \<Rightarrow> bool" where
  "is_value e = is_value_until e 0"

inductive evaluate :: "expr \<Rightarrow> expr \<Rightarrow> bool" (infix "\<leadsto>" 60) where
  ev_fun [simp]: "e\<^sub>1 \<leadsto> e\<^sub>1' \<Longrightarrow> e\<^sub>1 \<star> e\<^sub>2 \<leadsto> e\<^sub>1' \<star> e\<^sub>2"
| ev_arg [simp]: "is_value e\<^sub>1 \<Longrightarrow> e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> e\<^sub>1 \<star> e\<^sub>2 \<leadsto> e\<^sub>1 \<star> e\<^sub>2'"
| ev_fst [simp]: "Fst \<star> (Pair \<star> e\<^sub>1 \<star> e\<^sub>2) \<leadsto> e\<^sub>1"
| ev_snd [simp]: "Snd \<star> (Pair \<star> e\<^sub>1 \<star> e\<^sub>2) \<leadsto> e\<^sub>2"
| ev_csl [simp]: "Case \<star> (Inl \<star> e) \<star> fl \<star> fr \<leadsto> fl \<star> e"
| ev_csr [simp]: "Case \<star> (Inr \<star> e) \<star> fl \<star> fr \<leadsto> fr \<star> e"
| ev_out [simp]: "Outj f \<star> (Inj f \<star> e) \<leadsto> e"

(* safety *)

abbreviation dne :: "expr \<Rightarrow> bool" where
  "dne e \<equiv> (\<not> (\<exists>e'. e \<leadsto> e'))"

primrec constructor_headed :: "expr \<Rightarrow> bool" where
  "constructor_headed (e\<^sub>1 \<star> e\<^sub>2) = (constructor_headed e\<^sub>1 \<and> dne e\<^sub>2)"
| "constructor_headed UnitV = True"
| "constructor_headed Pair = True"
| "constructor_headed Fst = False"
| "constructor_headed Snd = False"
| "constructor_headed Inl = True"
| "constructor_headed Inr = True"
| "constructor_headed Case = False"
| "constructor_headed (Inj f) = True"
| "constructor_headed (Outj f) = False"

lemma [simp]: "dne Fst"
  using evaluate.simps by blast

lemma [simp]: "dne Snd"
  using evaluate.simps by blast

lemma [simp]: "dne (Outj f)"
  using evaluate.simps by blast

lemma [simp]: "dne Case"
  using evaluate.simps by blast

lemma [elim]: "Case \<star> e\<^sub>1 \<leadsto> e' \<Longrightarrow> dne e\<^sub>1 \<Longrightarrow> False"
  proof (induction "Case \<star> e\<^sub>1" e' rule: evaluate.induct)
  case ev_fun
    thus ?case using evaluate.simps by blast
  qed simp_all

lemma [elim]: "Case \<star> e\<^sub>1 \<star> e\<^sub>2 \<leadsto> e' \<Longrightarrow> dne e\<^sub>1 \<Longrightarrow> dne e\<^sub>2 \<Longrightarrow> False"
  by (induction "Case \<star> e\<^sub>1 \<star> e\<^sub>2" e' rule: evaluate.induct) auto

lemma [elim]: "e\<^sub>1 \<star> e\<^sub>2 \<leadsto> e' \<Longrightarrow> constructor_headed e\<^sub>1 \<Longrightarrow> dne e\<^sub>1 \<Longrightarrow> dne e\<^sub>2 \<Longrightarrow> False"
  by (induction "e\<^sub>1 \<star> e\<^sub>2" e' rule: evaluate.induct) auto

lemma [simp]: "constructor_headed e \<Longrightarrow> dne e"
  proof (induction e)
  case UnitV
    thus ?case using evaluate.simps by blast
  next case Pair
    thus ?case using evaluate.simps by blast
  next case Inl
    thus ?case using evaluate.simps by blast
  next case Inr
    thus ?case using evaluate.simps by blast
  next case Inj
    thus ?case using evaluate.simps by blast
  qed auto

lemma [simp]: "\<forall>e'\<in>set es. dne e' \<Longrightarrow> constructor_headed e \<Longrightarrow> dne (fold (\<lambda>e\<^sub>2 e\<^sub>1. e\<^sub>1 \<star> e\<^sub>2) es e)"
  by (induction es arbitrary: e) simp_all

lemma fold_value_dne: "is_value_until e (length es) \<Longrightarrow> \<forall>e' \<in> set es. dne e' \<Longrightarrow> 
    dne (fold (\<lambda>e\<^sub>2 e\<^sub>1. e\<^sub>1 \<star> e\<^sub>2) es e)"
  proof (induction e arbitrary: es)
  case (Apply e\<^sub>1 e\<^sub>2)
    hence "is_value_until e\<^sub>2 (length []) \<Longrightarrow> \<forall>e'\<in>set []. dne e' \<Longrightarrow> dne (fold (\<lambda>e\<^sub>2 e\<^sub>1. e\<^sub>1 \<star> e\<^sub>2) [] e\<^sub>2)" 
      by (smt list.size(3))
    with Apply have X: "dne e\<^sub>2" by simp
    from Apply have "is_value_until e\<^sub>1 (length (e\<^sub>2 # es)) \<Longrightarrow> \<forall>e'\<in>set (e\<^sub>2 # es). dne e' \<Longrightarrow> 
      dne (fold (\<lambda>e\<^sub>2 e\<^sub>1. e\<^sub>1 \<star> e\<^sub>2) (e\<^sub>2 # es) e\<^sub>1)" by (smt list.size(3))
    with Apply X show ?case by simp
  next case Case
    thus ?case
      proof (cases es)
      case (Cons e es)
        with Case show ?thesis by (cases es) auto
      qed simp_all
  qed simp_all

theorem value_does_not_evaluate: "is_value e \<Longrightarrow> dne e"
  proof -
    assume "is_value e"
    hence "is_value_until e (length [])" by (simp add: is_value_def)
    thus "dne e" using fold_value_dne by fastforce
  qed

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

theorem progress: "e \<turnstile> t \<Longrightarrow> is_value e \<or> (\<exists>e'. e \<leadsto> e')"
  proof (induction e t rule: typecheck.induct)
  case (tc_app e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
    thus ?case
      proof (cases "is_value e\<^sub>1")
      case True note T = True
        thus ?thesis
          proof (cases "is_value e\<^sub>2")
          case True
            from tc_app have "e\<^sub>1 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2" by simp
            from tc_app have "e\<^sub>2 \<turnstile> t\<^sub>1" by simp
        
        

            have "(is_value_until e\<^sub>1 (Suc 0) \<and> is_value_until e\<^sub>2 0) \<or> (\<exists>a. e\<^sub>1 \<star> e\<^sub>2 \<leadsto> a)" by simp
            thus ?thesis by (simp add: is_value_def)
          next case False
            with tc_app obtain e\<^sub>2' where "e\<^sub>2 \<leadsto> e\<^sub>2'" by blast
            with True have "e\<^sub>1 \<star> e\<^sub>2 \<leadsto> e\<^sub>1 \<star> e\<^sub>2'" by simp
            thus ?thesis by auto
          qed
      next case False
        with tc_app obtain e\<^sub>1' where "e\<^sub>1 \<leadsto> e\<^sub>1'" by blast
        hence "e\<^sub>1 \<star> e\<^sub>2 \<leadsto> e\<^sub>1' \<star> e\<^sub>2" by simp
        thus ?thesis by auto
      qed
  qed (simp_all add: is_value_def)
 
end
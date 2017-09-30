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
| Pair expr expr | Fst | Snd
| Inl expr | Inr expr | Case expr expr
| Inj funct expr | Outj funct

inductive typecheck :: "expr \<Rightarrow> type \<Rightarrow> bool" (infix "\<turnstile>" 60) where
  tc_app [simp]: "e\<^sub>1 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> e\<^sub>2 \<turnstile> t\<^sub>1 \<Longrightarrow> e\<^sub>1 \<star> e\<^sub>2 \<turnstile> t\<^sub>2"
| tc_unit [simp]: "UnitV \<turnstile> Unit"
| tc_pair [simp]: "e\<^sub>1 \<turnstile> t\<^sub>1 \<Longrightarrow> e\<^sub>2 \<turnstile> t\<^sub>2 \<Longrightarrow> Pair e\<^sub>1 e\<^sub>2 \<turnstile> Prod t\<^sub>1 t\<^sub>2"
| tc_fst [simp]: "Fst \<turnstile> Prod t\<^sub>1 t\<^sub>2 \<rightarrow> t\<^sub>1"
| tc_snd [simp]: "Snd \<turnstile> Prod t\<^sub>1 t\<^sub>2 \<rightarrow> t\<^sub>2"
| tc_inl [simp]: "e \<turnstile> t\<^sub>1 \<Longrightarrow> Inl e \<turnstile> Sum t\<^sub>1 t\<^sub>2"
| tc_inr [simp]: "e \<turnstile> t\<^sub>2 \<Longrightarrow> Inr e \<turnstile> Sum t\<^sub>1 t\<^sub>2"
| tc_case [simp]: "e\<^sub>1 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>3 \<Longrightarrow> e\<^sub>2 \<turnstile> t\<^sub>2 \<rightarrow> t\<^sub>3 \<Longrightarrow> Case e\<^sub>1 e\<^sub>2 \<turnstile> Sum t\<^sub>1 t\<^sub>2 \<rightarrow> t\<^sub>3"
| tc_inj [simp]: "e \<turnstile> apply_functor f (Mu f) \<Longrightarrow> Inj f e \<turnstile> Mu f"
| tc_outj [simp]: "Outj f \<turnstile> Mu f \<rightarrow> apply_functor f (Mu f)"

inductive_cases [elim]: "e\<^sub>1 \<star> e\<^sub>2 \<turnstile> t"
inductive_cases [elim]: "UnitV \<turnstile> t"
inductive_cases [elim]: "Pair e\<^sub>1 e\<^sub>2 \<turnstile> t"
inductive_cases [elim]: "Fst \<turnstile> t"
inductive_cases [elim]: "Snd \<turnstile> t"
inductive_cases [elim]: "Inl e \<turnstile> t"
inductive_cases [elim]: "Inr e \<turnstile> t"
inductive_cases [elim]: "Case e\<^sub>1 e\<^sub>2 \<turnstile> t"
inductive_cases [elim]: "Inj f e \<turnstile> t"
inductive_cases [elim]: "Outj f \<turnstile> t"

fun is_value :: "expr \<Rightarrow> bool" where
  "is_value (e\<^sub>1 \<star> e\<^sub>2) = False"
| "is_value _ = True"

inductive evaluate :: "expr \<Rightarrow> expr \<Rightarrow> bool" (infix "\<leadsto>" 60) where
  ev_fun [simp]: "e\<^sub>1 \<leadsto> e\<^sub>1' \<Longrightarrow> e\<^sub>1 \<star> e\<^sub>2 \<leadsto> e\<^sub>1' \<star> e\<^sub>2"
| ev_arg [simp]: "is_value e\<^sub>1 \<Longrightarrow> e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> e\<^sub>1 \<star> e\<^sub>2 \<leadsto> e\<^sub>1 \<star> e\<^sub>2'"
| ev_fst [simp]: "Fst \<star> (Pair e\<^sub>1 e\<^sub>2) \<leadsto> e\<^sub>1"
| ev_snd [simp]: "Snd \<star> (Pair e\<^sub>1 e\<^sub>2) \<leadsto> e\<^sub>2"
| ev_csl [simp]: "Case fl fr \<star> (Inl e) \<leadsto> fl \<star> e"
| ev_csr [simp]: "Case fl fr \<star> (Inr e) \<leadsto> fr \<star> e"
| ev_out [simp]: "Outj f \<star> (Inj f e) \<leadsto> e"

(* safety *)

abbreviation dne :: "expr \<Rightarrow> bool" where
  "dne e \<equiv> (\<not> (\<exists>e'. e \<leadsto> e'))"

lemma [simp]: "dne UnitV" using evaluate.simps by blast
lemma [simp]: "dne (Pair e\<^sub>1 e\<^sub>2)" using evaluate.simps by blast
lemma [simp]: "dne Fst" using evaluate.simps by blast
lemma [simp]: "dne Snd" using evaluate.simps by blast
lemma [simp]: "dne (Inl e)" using evaluate.simps by blast
lemma [simp]: "dne (Inr e)" using evaluate.simps by blast
lemma [simp]: "dne (Case fl fr)" using evaluate.simps by blast
lemma [simp]: "dne (Inj f e)" using evaluate.simps by blast
lemma [simp]: "dne (Outj f)" using evaluate.simps by blast

theorem value_does_not_evaluate: "is_value e \<Longrightarrow> dne e"
  by (induction e) simp_all

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

lemma canonical_unit: "e \<turnstile> Unit \<Longrightarrow> is_value e \<Longrightarrow> e = UnitV"
  by (induction e Unit rule: typecheck.induct) simp_all

lemma canonical_prod: "e \<turnstile> Prod t\<^sub>1 t\<^sub>2 \<Longrightarrow> is_value e \<Longrightarrow> \<exists>e\<^sub>1 e\<^sub>2. e = Pair e\<^sub>1 e\<^sub>2"
  by (induction e "Prod t\<^sub>1 t\<^sub>2" rule: typecheck.induct) simp_all

lemma canonical_sum: "e \<turnstile> Sum t\<^sub>1 t\<^sub>2 \<Longrightarrow> is_value e \<Longrightarrow> \<exists>e'. e = Inl e' \<or> e = Inr e'"
  by (induction e "Sum t\<^sub>1 t\<^sub>2" rule: typecheck.induct) simp_all

lemma canonical_mu: "e \<turnstile> Mu f \<Longrightarrow> is_value e \<Longrightarrow> \<exists>e'. e = Inj f e'"
  by (induction e "Mu f" rule: typecheck.induct) simp_all

theorem progress: "e \<turnstile> t \<Longrightarrow> is_value e \<or> (\<exists>e'. e \<leadsto> e')"
  proof (induction e t rule: typecheck.induct)
  case (tc_app e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
    thus ?case
      proof (cases "is_value e\<^sub>1")
      case True note T = True
        thus ?thesis
          proof (cases "is_value e\<^sub>2")
          case True
            with tc_app T show ?thesis
              proof (induction e\<^sub>1 "t\<^sub>1 \<rightarrow> t\<^sub>2" arbitrary: t\<^sub>1 t\<^sub>2 rule: typecheck.induct)
              case tc_fst
                then obtain e\<^sub>2\<^sub>1 e\<^sub>2\<^sub>2 where "e\<^sub>2 = Pair e\<^sub>2\<^sub>1 e\<^sub>2\<^sub>2" using canonical_prod by blast
                moreover have "Fst \<star> Pair e\<^sub>2\<^sub>1 e\<^sub>2\<^sub>2 \<leadsto> e\<^sub>2\<^sub>1" by simp
                ultimately show ?case by fastforce
              next case tc_snd
                then obtain e\<^sub>2\<^sub>1 e\<^sub>2\<^sub>2 where "e\<^sub>2 = Pair e\<^sub>2\<^sub>1 e\<^sub>2\<^sub>2" using canonical_prod by blast
                moreover have "Snd \<star> Pair e\<^sub>2\<^sub>1 e\<^sub>2\<^sub>2 \<leadsto> e\<^sub>2\<^sub>2" by simp
                ultimately show ?case by fastforce
              next case (tc_case fl t\<^sub>1 t\<^sub>3 fr t\<^sub>2)
                then obtain e' where E: "e\<^sub>2 = Inl e' \<or> e\<^sub>2 = Inr e'" using canonical_sum by blast
                thus ?case
                  proof (cases "e\<^sub>2 = Inl e'")
                  case True
                    moreover have "Case fl fr \<star> Inl e' \<leadsto> fl \<star> e'" by simp
                    ultimately show ?thesis by fastforce
                  next case False
                    have "Case fl fr \<star> Inr e' \<leadsto> fr \<star> e'" by simp
                    with False E show ?thesis by fastforce
                  qed
              next case (tc_outj f)
                then obtain e' where "e\<^sub>2 = Inj f e'" using canonical_mu by blast
                moreover have "Outj f \<star> Inj f e' \<leadsto> e'" by simp
                ultimately show ?case by fastforce
              qed simp_all
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
  qed simp_all
 
end
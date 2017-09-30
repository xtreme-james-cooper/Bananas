theory Bananas
imports Main
begin

datatype type = 
  Unit
| Prod type type (infixr "\<otimes>" 80)
| Sum type type (infixr "\<oplus>" 80)
| Func type type (infixr "\<rightarrow>" 70)
| \<mu> funct
and funct =
  Id
| K type
| ProdF funct funct
| SumF funct funct

primrec apply_functor :: "funct \<Rightarrow> type \<Rightarrow> type" (infixr "\<star>" 80) where
  "Id \<star> t = t"
| "K t' \<star> t = t'"
| "ProdF f\<^sub>1 f\<^sub>2 \<star> t = (f\<^sub>1 \<star> t) \<otimes> (f\<^sub>2 \<star> t)"
| "SumF f\<^sub>1 f\<^sub>2 \<star> t = (f\<^sub>1 \<star> t) \<oplus> (f\<^sub>2 \<star> t)"

datatype expr = 
  Apply expr expr (infixl "\<cdot>" 70)
| UnitV
| PairV expr expr 
| InlV expr
| InrV expr

| \<pi>\<^sub>1 
| \<pi>\<^sub>2 
| Tuple expr expr (infix "\<triangle>" 80)
| \<iota>\<^sub>l 
| \<iota>\<^sub>r 
| Case expr expr (infix "\<nabla>" 80)
| Inj funct expr 
| Outj funct

inductive typecheck :: "expr \<Rightarrow> type \<Rightarrow> bool" (infix "\<turnstile>" 60) where
  tc_app [simp]: "e\<^sub>1 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> e\<^sub>2 \<turnstile> t\<^sub>1 \<Longrightarrow> e\<^sub>1 \<cdot> e\<^sub>2 \<turnstile> t\<^sub>2"
| tc_unit [simp]: "UnitV \<turnstile> Unit"
| tc_pair [simp]: "e\<^sub>1 \<turnstile> t\<^sub>1 \<Longrightarrow> e\<^sub>2 \<turnstile> t\<^sub>2 \<Longrightarrow> PairV e\<^sub>1 e\<^sub>2 \<turnstile> t\<^sub>1 \<otimes> t\<^sub>2"
| tc_inlv [simp]: "e \<turnstile> t\<^sub>1 \<Longrightarrow> InlV e \<turnstile> t\<^sub>1 \<oplus> t\<^sub>2"
| tc_inrv [simp]: "e \<turnstile> t\<^sub>2 \<Longrightarrow> InrV e \<turnstile> t\<^sub>1 \<oplus> t\<^sub>2"
| tc_fst [simp]: "\<pi>\<^sub>1 \<turnstile> t\<^sub>1 \<otimes> t\<^sub>2 \<rightarrow> t\<^sub>1"
| tc_snd [simp]: "\<pi>\<^sub>2 \<turnstile> t\<^sub>1 \<otimes> t\<^sub>2 \<rightarrow> t\<^sub>2"
| tc_tup [simp]: "f\<^sub>1 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> f\<^sub>2 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>3 \<Longrightarrow> f\<^sub>1 \<triangle> f\<^sub>2 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<otimes> t\<^sub>3"
| tc_inl [simp]: "\<iota>\<^sub>l \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>1 \<oplus> t\<^sub>2"
| tc_inr [simp]: "\<iota>\<^sub>r \<turnstile> t\<^sub>2 \<rightarrow> t\<^sub>1 \<oplus> t\<^sub>2"
| tc_case [simp]: "f\<^sub>l \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>3 \<Longrightarrow> f\<^sub>r \<turnstile> t\<^sub>2 \<rightarrow> t\<^sub>3 \<Longrightarrow> f\<^sub>l \<nabla> f\<^sub>r \<turnstile> t\<^sub>1 \<oplus> t\<^sub>2 \<rightarrow> t\<^sub>3"
| tc_inj [simp]: "e \<turnstile> f \<star> \<mu> f \<Longrightarrow> Inj f e \<turnstile> \<mu> f"
| tc_outj [simp]: "Outj f \<turnstile> \<mu> f \<rightarrow> f \<star> \<mu> f"

inductive_cases [elim]: "e\<^sub>1 \<cdot> e\<^sub>2 \<turnstile> t"
inductive_cases [elim]: "UnitV \<turnstile> t"
inductive_cases [elim]: "PairV e\<^sub>1 e\<^sub>2 \<turnstile> t"
inductive_cases [elim]: "InrV e \<turnstile> t"
inductive_cases [elim]: "InlV e \<turnstile> t"
inductive_cases [elim]: "\<pi>\<^sub>1 \<turnstile> t"
inductive_cases [elim]: "\<pi>\<^sub>2 \<turnstile> t"
inductive_cases [elim]: "f\<^sub>1 \<triangle> f\<^sub>2 \<turnstile> t"
inductive_cases [elim]: "\<iota>\<^sub>l \<turnstile> t"
inductive_cases [elim]: "\<iota>\<^sub>r \<turnstile> t"
inductive_cases [elim]: "f\<^sub>l \<nabla> f\<^sub>r \<turnstile> t"
inductive_cases [elim]: "Inj f e \<turnstile> t"
inductive_cases [elim]: "Outj f \<turnstile> t"

fun is_value :: "expr \<Rightarrow> bool" where
  "is_value (e\<^sub>1 \<cdot> e\<^sub>2) = False"
| "is_value _ = True"

inductive evaluate :: "expr \<Rightarrow> expr \<Rightarrow> bool" (infix "\<leadsto>" 60) where
  ev_fun [simp]: "e\<^sub>1 \<leadsto> e\<^sub>1' \<Longrightarrow> e\<^sub>1 \<cdot> e\<^sub>2 \<leadsto> e\<^sub>1' \<cdot> e\<^sub>2"
| ev_arg [simp]: "is_value e\<^sub>1 \<Longrightarrow> e\<^sub>2 \<leadsto> e\<^sub>2' \<Longrightarrow> e\<^sub>1 \<cdot> e\<^sub>2 \<leadsto> e\<^sub>1 \<cdot> e\<^sub>2'"
| ev_fst [simp]: "\<pi>\<^sub>1 \<cdot> (PairV e\<^sub>1 e\<^sub>2) \<leadsto> e\<^sub>1"
| ev_snd [simp]: "\<pi>\<^sub>2 \<cdot> (PairV e\<^sub>1 e\<^sub>2) \<leadsto> e\<^sub>2"
| ev_tup [simp]: "f\<^sub>1 \<triangle> f\<^sub>2 \<cdot> e \<leadsto> PairV (f\<^sub>1 \<cdot> e) (f\<^sub>2 \<cdot> e)"
| ev_inl [simp]: "\<iota>\<^sub>l \<cdot> e \<leadsto> InlV e"
| ev_inr [simp]: "\<iota>\<^sub>r \<cdot> e \<leadsto> InrV e"
| ev_csl [simp]: "f\<^sub>l \<nabla> f\<^sub>r \<cdot> (InlV e) \<leadsto> f\<^sub>l \<cdot> e"
| ev_csr [simp]: "f\<^sub>l \<nabla> f\<^sub>r \<cdot> (InrV e) \<leadsto> f\<^sub>r \<cdot> e"
| ev_out [simp]: "Outj f \<cdot> (Inj f e) \<leadsto> e"

(* safety *)

abbreviation dne :: "expr \<Rightarrow> bool" where
  "dne e \<equiv> (\<not> (\<exists>e'. e \<leadsto> e'))"

lemma [simp]: "dne UnitV" using evaluate.simps by blast
lemma [simp]: "dne (PairV e\<^sub>1 e\<^sub>2)" using evaluate.simps by blast
lemma [simp]: "dne (InlV e)" using evaluate.simps by blast
lemma [simp]: "dne (InrV e)" using evaluate.simps by blast
lemma [simp]: "dne \<pi>\<^sub>1" using evaluate.simps by blast
lemma [simp]: "dne \<pi>\<^sub>2" using evaluate.simps by blast
lemma [simp]: "dne (f\<^sub>1 \<triangle> f\<^sub>2)" using evaluate.simps by blast
lemma [simp]: "dne \<iota>\<^sub>l" using evaluate.simps by blast
lemma [simp]: "dne \<iota>\<^sub>r" using evaluate.simps by blast
lemma [simp]: "dne (f\<^sub>l \<nabla> f\<^sub>r)" using evaluate.simps by blast
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

lemma canonical_prod: "e \<turnstile> t\<^sub>1 \<otimes> t\<^sub>2 \<Longrightarrow> is_value e \<Longrightarrow> \<exists>e\<^sub>1 e\<^sub>2. e = PairV e\<^sub>1 e\<^sub>2"
  by (induction e "Prod t\<^sub>1 t\<^sub>2" rule: typecheck.induct) simp_all

lemma canonical_sum: "e \<turnstile> t\<^sub>1 \<oplus> t\<^sub>2 \<Longrightarrow> is_value e \<Longrightarrow> \<exists>e'. e = InlV e' \<or> e = InrV e'"
  by (induction e "Sum t\<^sub>1 t\<^sub>2" rule: typecheck.induct) simp_all

lemma canonical_mu: "e \<turnstile> \<mu> f \<Longrightarrow> is_value e \<Longrightarrow> \<exists>e'. e = Inj f e'"
  by (induction e "\<mu> f" rule: typecheck.induct) simp_all

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
                then obtain e\<^sub>2\<^sub>1 e\<^sub>2\<^sub>2 where "e\<^sub>2 = PairV e\<^sub>2\<^sub>1 e\<^sub>2\<^sub>2" using canonical_prod by blast
                moreover have "\<pi>\<^sub>1 \<cdot> PairV e\<^sub>2\<^sub>1 e\<^sub>2\<^sub>2 \<leadsto> e\<^sub>2\<^sub>1" by simp
                ultimately show ?case by fastforce
              next case tc_snd
                then obtain e\<^sub>2\<^sub>1 e\<^sub>2\<^sub>2 where "e\<^sub>2 = PairV e\<^sub>2\<^sub>1 e\<^sub>2\<^sub>2" using canonical_prod by blast
                moreover have "\<pi>\<^sub>2 \<cdot> PairV e\<^sub>2\<^sub>1 e\<^sub>2\<^sub>2 \<leadsto> e\<^sub>2\<^sub>2" by simp
                ultimately show ?case by fastforce
              next case (tc_tup f\<^sub>1 _ _ f\<^sub>2)
                have "f\<^sub>1 \<triangle> f\<^sub>2 \<cdot> e\<^sub>2 \<leadsto> PairV (f\<^sub>1 \<cdot> e\<^sub>2) (f\<^sub>2 \<cdot> e\<^sub>2)" by simp
                thus ?case by fastforce
              next case tc_inl
                have "\<iota>\<^sub>l \<cdot> e\<^sub>2 \<leadsto> InlV e\<^sub>2" by simp
                thus ?case by fastforce
              next case tc_inr
                have "\<iota>\<^sub>r \<cdot> e\<^sub>2 \<leadsto> InrV e\<^sub>2" by simp
                thus ?case by fastforce
              next case (tc_case f\<^sub>l _ _ f\<^sub>r)
                then obtain e' where E: "e\<^sub>2 = InlV e' \<or> e\<^sub>2 = InrV e'" using canonical_sum by blast
                thus ?case
                  proof (cases "e\<^sub>2 = InlV e'")
                  case True
                    moreover have "f\<^sub>l \<nabla> f\<^sub>r \<cdot> InlV e' \<leadsto> f\<^sub>l \<cdot> e'" by simp
                    ultimately show ?thesis by fastforce
                  next case False
                    have "f\<^sub>l \<nabla> f\<^sub>r \<cdot> InrV e' \<leadsto> f\<^sub>r \<cdot> e'" by simp
                    with False E show ?thesis by fastforce
                  qed
              next case (tc_outj f)
                then obtain e' where "e\<^sub>2 = Inj f e'" using canonical_mu by blast
                moreover have "Outj f \<cdot> Inj f e' \<leadsto> e'" by simp
                ultimately show ?case by fastforce
              qed simp_all
          next case False
            with tc_app obtain e\<^sub>2' where "e\<^sub>2 \<leadsto> e\<^sub>2'" by blast
            with True have "e\<^sub>1 \<cdot> e\<^sub>2 \<leadsto> e\<^sub>1 \<cdot> e\<^sub>2'" by simp
            thus ?thesis by auto
          qed
      next case False
        with tc_app obtain e\<^sub>1' where "e\<^sub>1 \<leadsto> e\<^sub>1'" by blast
        hence "e\<^sub>1 \<cdot> e\<^sub>2 \<leadsto> e\<^sub>1' \<cdot> e\<^sub>2" by simp
        thus ?thesis by auto
      qed
  qed simp_all
 
end
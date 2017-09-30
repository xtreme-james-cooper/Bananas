theory BananasLanguage
imports Main
begin

datatype type = 
  Unit
| Prod type type (infixr "\<otimes>" 80)
| Sum type type (infixr "\<oplus>" 80)
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

datatype val = 
  UnitV
| PairV val val 
| InlV val | InrV val
| InjV funct val 

datatype expr = 
  \<epsilon> | Comp expr expr (infixr "\<cdot>" 70)
| \<pi>\<^sub>1 | \<pi>\<^sub>2 | Tuple expr expr (infix "\<triangle>" 80)
| \<iota>\<^sub>l | \<iota>\<^sub>r | Case expr expr (infix "\<nabla>" 80)
| Outj funct

inductive typecheck\<^sub>v :: "val \<Rightarrow> type \<Rightarrow> bool" (infix "\<turnstile>" 60) where
  tc_unit [simp]: "UnitV \<turnstile> Unit"
| tc_pair [simp]: "v\<^sub>1 \<turnstile> t\<^sub>1 \<Longrightarrow> v\<^sub>2 \<turnstile> t\<^sub>2 \<Longrightarrow> PairV v\<^sub>1 v\<^sub>2 \<turnstile> t\<^sub>1 \<otimes> t\<^sub>2"
| tc_inlv [simp]: "v \<turnstile> t\<^sub>1 \<Longrightarrow> InlV v \<turnstile> t\<^sub>1 \<oplus> t\<^sub>2"
| tc_inrv [simp]: "v \<turnstile> t\<^sub>2 \<Longrightarrow> InrV v \<turnstile> t\<^sub>1 \<oplus> t\<^sub>2"
| tc_inj [simp]: "v \<turnstile> f \<star> \<mu> f \<Longrightarrow> InjV f v \<turnstile> \<mu> f"

inductive_cases [elim]: "UnitV \<turnstile> t"
inductive_cases [elim]: "PairV e\<^sub>1 e\<^sub>2 \<turnstile> t"
inductive_cases [elim]: "InrV e \<turnstile> t"
inductive_cases [elim]: "InlV e \<turnstile> t"
inductive_cases [elim]: "InjV f e \<turnstile> t"

inductive typecheck\<^sub>e :: "expr \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" (infix "\<turnstile> _ \<rightarrow>" 60) where
  tc_id [simp]: "\<epsilon> \<turnstile> t \<rightarrow> t"
| tc_comp [simp]: "f \<turnstile> t\<^sub>2 \<rightarrow> t\<^sub>3 \<Longrightarrow> g \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> f \<cdot> g \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>3"
| tc_fst [simp]: "\<pi>\<^sub>1 \<turnstile> t\<^sub>1 \<otimes> t\<^sub>2 \<rightarrow> t\<^sub>1"
| tc_snd [simp]: "\<pi>\<^sub>2 \<turnstile> t\<^sub>1 \<otimes> t\<^sub>2 \<rightarrow> t\<^sub>2"
| tc_tup [simp]: "f\<^sub>1 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> f\<^sub>2 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>3 \<Longrightarrow> f\<^sub>1 \<triangle> f\<^sub>2 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<otimes> t\<^sub>3"
| tc_inl [simp]: "\<iota>\<^sub>l \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>1 \<oplus> t\<^sub>2"
| tc_inr [simp]: "\<iota>\<^sub>r \<turnstile> t\<^sub>2 \<rightarrow> t\<^sub>1 \<oplus> t\<^sub>2"
| tc_case [simp]: "f\<^sub>l \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>3 \<Longrightarrow> f\<^sub>r \<turnstile> t\<^sub>2 \<rightarrow> t\<^sub>3 \<Longrightarrow> f\<^sub>l \<nabla> f\<^sub>r \<turnstile> t\<^sub>1 \<oplus> t\<^sub>2 \<rightarrow> t\<^sub>3"
| tc_outj [simp]: "Outj f \<turnstile> \<mu> f \<rightarrow> f \<star> \<mu> f"

inductive_cases [elim]: "\<epsilon> \<turnstile> t \<rightarrow> t'"
inductive_cases [elim]: "f \<cdot> g \<turnstile> t \<rightarrow> t'"
inductive_cases [elim]: "\<pi>\<^sub>1 \<turnstile> t \<rightarrow> t'"
inductive_cases [elim]: "\<pi>\<^sub>2 \<turnstile> t \<rightarrow> t'"
inductive_cases [elim]: "f\<^sub>1 \<triangle> f\<^sub>2 \<turnstile> t \<rightarrow> t'"
inductive_cases [elim]: "\<iota>\<^sub>l \<turnstile> t \<rightarrow> t'"
inductive_cases [elim]: "\<iota>\<^sub>r \<turnstile> t \<rightarrow> t'"
inductive_cases [elim]: "f\<^sub>l \<nabla> f\<^sub>r \<turnstile> t \<rightarrow> t'"
inductive_cases [elim]: "Outj f \<turnstile> t \<rightarrow> t'"

inductive evaluate :: "val \<Rightarrow> expr \<Rightarrow> val \<Rightarrow> bool" (infix "~ _ \<leadsto>" 60) where
  ev_id [simp]: "v ~ \<epsilon> \<leadsto> v"
| ev_comp [simp]: "v ~ g \<leadsto> v' \<Longrightarrow> v' ~ f \<leadsto> v'' \<Longrightarrow> v ~ f \<cdot> g \<leadsto> v''"
| ev_fst [simp]: "PairV v\<^sub>1 v\<^sub>2 ~ \<pi>\<^sub>1 \<leadsto> v\<^sub>1"
| ev_snd [simp]: "PairV v\<^sub>1 v\<^sub>2 ~ \<pi>\<^sub>2 \<leadsto> v\<^sub>2"
| ev_tup [simp]: "v ~ f\<^sub>1 \<leadsto> v\<^sub>1 \<Longrightarrow> v ~ f\<^sub>2 \<leadsto> v\<^sub>2 \<Longrightarrow> v ~ f\<^sub>1 \<triangle> f\<^sub>2 \<leadsto> PairV v\<^sub>1 v\<^sub>2"
| ev_inl [simp]: "v ~ \<iota>\<^sub>l \<leadsto> InlV v"
| ev_inr [simp]: "v ~ \<iota>\<^sub>r \<leadsto> InrV v"
| ev_csl [simp]: "v ~ f\<^sub>l \<leadsto> v' \<Longrightarrow> InlV v ~ f\<^sub>l \<nabla> f\<^sub>r \<leadsto> v'"
| ev_csr [simp]: "v ~ f\<^sub>r \<leadsto> v' \<Longrightarrow> InrV v ~ f\<^sub>l \<nabla> f\<^sub>r \<leadsto> v'"
| ev_out [simp]: "InjV f v ~ Outj f \<leadsto> v"

(* safety *)

theorem preservation: "v ~ e \<leadsto> v' \<Longrightarrow> e \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> v \<turnstile> t\<^sub>1 \<Longrightarrow> v' \<turnstile> t\<^sub>2"
  by (induction v e v' arbitrary: t\<^sub>1 t\<^sub>2 rule: evaluate.induct) fastforce+

lemma canonical_unit: "v \<turnstile> Unit \<Longrightarrow> v = UnitV"
  by (induction v Unit rule: typecheck\<^sub>v.induct) simp_all

lemma canonical_prod: "v \<turnstile> t\<^sub>1 \<otimes> t\<^sub>2 \<Longrightarrow> \<exists>v\<^sub>1 v\<^sub>2. v\<^sub>1 \<turnstile> t\<^sub>1 \<and> v\<^sub>2 \<turnstile> t\<^sub>2 \<and> v = PairV v\<^sub>1 v\<^sub>2"
  by (induction v "Prod t\<^sub>1 t\<^sub>2" rule: typecheck\<^sub>v.induct) simp_all

lemma canonical_sum: "v \<turnstile> t\<^sub>1 \<oplus> t\<^sub>2 \<Longrightarrow> \<exists>v'. (v' \<turnstile> t\<^sub>1 \<and> v = InlV v') \<or> (v' \<turnstile> t\<^sub>2 \<and> v = InrV v')"
  by (induction v "Sum t\<^sub>1 t\<^sub>2" rule: typecheck\<^sub>v.induct) simp_all

lemma canonical_mu: "v \<turnstile> \<mu> f \<Longrightarrow> \<exists>v'. v' \<turnstile> f \<star> \<mu> f \<and> v = InjV f v'"
  by (induction v "\<mu> f" rule: typecheck\<^sub>v.induct) simp_all

theorem progress: "e \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> v \<turnstile> t\<^sub>1 \<Longrightarrow> \<exists>v'. v' \<turnstile> t\<^sub>2 \<and> v ~ e \<leadsto> v'"
  proof (induction e t\<^sub>1 t\<^sub>2 arbitrary: v rule: typecheck\<^sub>e.induct)
  case tc_id
    moreover have "v ~ \<epsilon> \<leadsto> v" by simp
    ultimately show ?case by fastforce
  next case (tc_comp f t\<^sub>2 t\<^sub>3 g t\<^sub>1)
    moreover then obtain v' where V: "v' \<turnstile> t\<^sub>2 \<and> v ~ g \<leadsto> v'" by blast
    ultimately obtain v'' where "v'' \<turnstile> t\<^sub>3 \<and> v' ~ f \<leadsto> v''" by blast
    moreover with V have "v ~ f \<cdot> g \<leadsto> v''" by auto
    ultimately show ?case by fastforce
  next case (tc_fst t\<^sub>1 t\<^sub>2)
    then obtain v\<^sub>1 v\<^sub>2 where "v\<^sub>1 \<turnstile> t\<^sub>1 \<and> v\<^sub>2 \<turnstile> t\<^sub>2 \<and> v = PairV v\<^sub>1 v\<^sub>2" using canonical_prod by blast
    moreover hence "v ~ \<pi>\<^sub>1 \<leadsto> v\<^sub>1" by simp
    ultimately show ?case by fastforce
  next case (tc_snd t\<^sub>1 t\<^sub>2)
    then obtain v\<^sub>1 v\<^sub>2 where "v\<^sub>1 \<turnstile> t\<^sub>1 \<and> v\<^sub>2 \<turnstile> t\<^sub>2 \<and> v = PairV v\<^sub>1 v\<^sub>2" using canonical_prod by blast
    moreover hence "v ~ \<pi>\<^sub>2 \<leadsto> v\<^sub>2" by simp
    ultimately show ?case by fastforce
  next case (tc_tup f\<^sub>1 t\<^sub>1 t\<^sub>2 f\<^sub>2 t\<^sub>3)
    then obtain v\<^sub>1 where V: "v\<^sub>1 \<turnstile> t\<^sub>2 \<and> v ~ f\<^sub>1 \<leadsto> v\<^sub>1" by blast
    moreover from tc_tup obtain v\<^sub>2 where "v\<^sub>2 \<turnstile> t\<^sub>3 \<and> v ~ f\<^sub>2 \<leadsto> v\<^sub>2" by blast
    ultimately have "PairV v\<^sub>1 v\<^sub>2 \<turnstile> t\<^sub>2 \<otimes> t\<^sub>3 \<and> v ~ f\<^sub>1 \<triangle> f\<^sub>2 \<leadsto> PairV v\<^sub>1 v\<^sub>2" by simp
    thus ?case by fastforce
  next case (tc_inl t\<^sub>1 t\<^sub>2)
    hence "InlV v \<turnstile> t\<^sub>1 \<oplus> t\<^sub>2 \<and> v ~ \<iota>\<^sub>l \<leadsto> InlV v" by simp
    thus ?case by fastforce
  next case (tc_inr t\<^sub>2 t\<^sub>1)
    hence "InrV v \<turnstile> t\<^sub>1 \<oplus> t\<^sub>2 \<and> v ~ \<iota>\<^sub>r \<leadsto> InrV v" by simp
    thus ?case by fastforce
  next case (tc_case f\<^sub>l t\<^sub>1 t\<^sub>3 f\<^sub>r t\<^sub>2)
    then obtain v' where V: "(v' \<turnstile> t\<^sub>1 \<and> v = InlV v') \<or> (v' \<turnstile> t\<^sub>2 \<and> v = InrV v')" 
      using canonical_sum by blast
    thus ?case
      proof (cases "v' \<turnstile> t\<^sub>1 \<and> v = InlV v'")
      case True
        with tc_case obtain v\<^sub>1 where "v\<^sub>1 \<turnstile> t\<^sub>3 \<and> v' ~ f\<^sub>l \<leadsto> v\<^sub>1" by blast 
        moreover with True have "v ~ f\<^sub>l \<nabla> f\<^sub>r \<leadsto> v\<^sub>1" by simp
        ultimately show ?thesis by fastforce
      next case False
        from tc_case False V obtain v\<^sub>2 where "v\<^sub>2 \<turnstile> t\<^sub>3 \<and> v' ~ f\<^sub>r \<leadsto> v\<^sub>2" by blast 
        moreover with False V have "v ~ f\<^sub>l \<nabla> f\<^sub>r \<leadsto> v\<^sub>2" by auto
        ultimately show ?thesis by fastforce
      qed
  next case (tc_outj f)
    then obtain v' where "v' \<turnstile> f \<star> \<mu> f \<and> v = InjV f v'" using canonical_mu by blast
    moreover hence "v ~ Outj f \<leadsto> v'" by simp
    ultimately show ?case by fastforce
  qed
 
end
theory BananasLanguage
imports Main
begin

datatype type = 
  Unit ("\<one>")
| Prod type type (infixr "\<otimes>" 85)
| Sum type type (infixr "\<oplus>" 80)
| Func type type (infixr "\<hookrightarrow>" 70)
| \<mu> funct
and funct =
  Id
| K type
| ProdF funct funct (infixr "\<Otimes>" 85)
| SumF funct funct (infixr "\<Oplus>" 80)

datatype expr = 
  Identity ("\<epsilon>") | Comp expr expr (infixr "\<cdot>" 65) | Const val ("\<kappa>")
| Proj1 ("\<pi>\<^sub>1") | Proj2 ("\<pi>\<^sub>2") | Duplicate ("\<Theta>") | Pairwise expr expr (infix "\<parallel>" 80)
| Injl ("\<iota>\<^sub>l") | Injr ("\<iota>\<^sub>r") | Strip ("\<Xi>") |  Case expr expr (infix "\<bar>" 80)
| Distribute ("\<rhd>")
| Apply | Arrow expr expr (infix "\<leftarrow>" 70)
| Outj funct
and val = 
  UnitV
| PairV val val 
| InlV val | InrV val
| FunV expr
| InjV funct val 

(* typechecking *)

primrec apply_functor :: "funct \<Rightarrow> type \<Rightarrow> type" (infixr "\<star>" 80) where
  "Id \<star> t = t"
| "K t' \<star> t = t'"
| "ProdF f\<^sub>1 f\<^sub>2 \<star> t = (f\<^sub>1 \<star> t) \<otimes> (f\<^sub>2 \<star> t)"
| "SumF f\<^sub>1 f\<^sub>2 \<star> t = (f\<^sub>1 \<star> t) \<oplus> (f\<^sub>2 \<star> t)"

inductive typecheck\<^sub>e :: "expr \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" (infix "\<turnstile> _ \<rightarrow>" 60)
      and typecheck\<^sub>v :: "val \<Rightarrow> type \<Rightarrow> bool" (infix "\<turnstile>" 60) where
  tc_id [simp]: "\<epsilon> \<turnstile> t \<rightarrow> t"
| tc_con [simp]: "v \<turnstile> t\<^sub>2 \<Longrightarrow> \<kappa> v \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2"
| tc_comp [simp]: "f \<turnstile> t\<^sub>2 \<rightarrow> t\<^sub>3 \<Longrightarrow> g \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> f \<cdot> g \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>3"
| tc_fst [simp]: "\<pi>\<^sub>1 \<turnstile> t\<^sub>1 \<otimes> t\<^sub>2 \<rightarrow> t\<^sub>1"
| tc_snd [simp]: "\<pi>\<^sub>2 \<turnstile> t\<^sub>1 \<otimes> t\<^sub>2 \<rightarrow> t\<^sub>2"
| tc_tup [simp]: "\<Theta> \<turnstile> t \<rightarrow> t \<otimes> t"
| tc_pair [simp]: "f\<^sub>1 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> f\<^sub>2 \<turnstile> t\<^sub>3 \<rightarrow> t\<^sub>4 \<Longrightarrow> f\<^sub>1 \<parallel> f\<^sub>2 \<turnstile> t\<^sub>1 \<otimes> t\<^sub>3 \<rightarrow> t\<^sub>2 \<otimes> t\<^sub>4"
| tc_inl [simp]: "\<iota>\<^sub>l \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>1 \<oplus> t\<^sub>2"
| tc_inr [simp]: "\<iota>\<^sub>r \<turnstile> t\<^sub>2 \<rightarrow> t\<^sub>1 \<oplus> t\<^sub>2"
| tc_str [simp]: "\<Xi> \<turnstile> t\<^sub>1 \<oplus> t\<^sub>1 \<rightarrow> t\<^sub>1"
| tc_case [simp]: "f\<^sub>l \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>3 \<Longrightarrow> f\<^sub>r \<turnstile> t\<^sub>2 \<rightarrow> t\<^sub>4 \<Longrightarrow> f\<^sub>l \<bar> f\<^sub>r \<turnstile> t\<^sub>1 \<oplus> t\<^sub>2 \<rightarrow> t\<^sub>3 \<oplus> t\<^sub>4"
| tc_dst [simp]: "\<rhd> \<turnstile> (t\<^sub>1 \<oplus> t\<^sub>2) \<otimes> t\<^sub>3 \<rightarrow> t\<^sub>1 \<otimes> t\<^sub>3 \<oplus> t\<^sub>2 \<otimes> t\<^sub>3"
| tc_app [simp]: "Apply \<turnstile> (t\<^sub>1 \<hookrightarrow> t\<^sub>2) \<otimes> t\<^sub>1 \<rightarrow> t\<^sub>2"
| tc_arr [simp]: "f \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> g \<turnstile> t\<^sub>3 \<rightarrow> t\<^sub>4 \<Longrightarrow> g \<leftarrow> f \<turnstile> t\<^sub>2 \<hookrightarrow> t\<^sub>3 \<rightarrow> t\<^sub>1 \<hookrightarrow> t\<^sub>4"
| tc_outj [simp]: "Outj f \<turnstile> \<mu> f \<rightarrow> f \<star> \<mu> f"

| tcv_unit [simp]: "UnitV \<turnstile> \<one>"
| tcv_pair [simp]: "v\<^sub>1 \<turnstile> t\<^sub>1 \<Longrightarrow> v\<^sub>2 \<turnstile> t\<^sub>2 \<Longrightarrow> PairV v\<^sub>1 v\<^sub>2 \<turnstile> t\<^sub>1 \<otimes> t\<^sub>2"
| tcv_inl [simp]: "v \<turnstile> t\<^sub>1 \<Longrightarrow> InlV v \<turnstile> t\<^sub>1 \<oplus> t\<^sub>2"
| tcv_inr [simp]: "v \<turnstile> t\<^sub>2 \<Longrightarrow> InrV v \<turnstile> t\<^sub>1 \<oplus> t\<^sub>2"
| tcv_fun [simp]: "e \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> FunV e \<turnstile> t\<^sub>1 \<hookrightarrow> t\<^sub>2"
| tcv_inj [simp]: "v \<turnstile> f \<star> \<mu> f \<Longrightarrow> InjV f v \<turnstile> \<mu> f"

inductive_cases [elim]: "\<epsilon> \<turnstile> t \<rightarrow> t'"
inductive_cases [elim]: "\<kappa> v \<turnstile> t \<rightarrow> t'"
inductive_cases [elim]: "f \<cdot> g \<turnstile> t \<rightarrow> t'"
inductive_cases [elim]: "\<pi>\<^sub>1 \<turnstile> t \<rightarrow> t'"
inductive_cases [elim]: "\<pi>\<^sub>2 \<turnstile> t \<rightarrow> t'"
inductive_cases [elim]: "\<Theta> \<turnstile> t \<rightarrow> t'"
inductive_cases [elim]: "f\<^sub>l \<parallel> f\<^sub>r \<turnstile> t \<rightarrow> t'"
inductive_cases [elim]: "\<iota>\<^sub>l \<turnstile> t \<rightarrow> t'"
inductive_cases [elim]: "\<iota>\<^sub>r \<turnstile> t \<rightarrow> t'"
inductive_cases [elim]: "\<Xi> \<turnstile> t \<rightarrow> t'"
inductive_cases [elim]: "f\<^sub>l \<bar> f\<^sub>r \<turnstile> t \<rightarrow> t'"
inductive_cases [elim]: "\<rhd> \<turnstile> t \<rightarrow> t'"
inductive_cases [elim]: "Apply \<turnstile> t \<rightarrow> t'"
inductive_cases [elim]: "g \<leftarrow> f \<turnstile> t \<rightarrow> t'"
inductive_cases [elim]: "Outj f \<turnstile> t \<rightarrow> t'"

inductive_cases [elim]: "UnitV \<turnstile> t"
inductive_cases [elim]: "PairV v\<^sub>1 v\<^sub>2 \<turnstile> t"
inductive_cases [elim]: "InrV v \<turnstile> t"
inductive_cases [elim]: "InlV v \<turnstile> t"
inductive_cases [elim]: "FunV e \<turnstile> t"
inductive_cases [elim]: "InjV f v \<turnstile> t"

(* evaluation *)

inductive evaluate :: "expr \<Rightarrow> val \<Rightarrow> expr \<Rightarrow> val \<Rightarrow> bool" (infix "\<cdot> _ \<leadsto> _ \<cdot>" 60) where
  ev_con [simp]: "\<kappa> v\<^sub>1 \<cdot> v\<^sub>2 \<leadsto> \<epsilon> \<cdot> v\<^sub>1"
| ev_comp1 [simp]: "g \<cdot> v \<leadsto> g' \<cdot> v' \<Longrightarrow> (f \<cdot> g) \<cdot> v \<leadsto> (f \<cdot> g') \<cdot> v'"
| ev_comp2 [simp]: "(f \<cdot> \<epsilon>) \<cdot> v \<leadsto> f \<cdot> v"
| ev_fst [simp]: "\<pi>\<^sub>1 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> \<epsilon> \<cdot> v\<^sub>1"
| ev_snd [simp]: "\<pi>\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> \<epsilon> \<cdot> v\<^sub>2"
| ev_pair1 [simp]: "f\<^sub>1 \<cdot> v\<^sub>1 \<leadsto> f\<^sub>1' \<cdot> v\<^sub>1' \<Longrightarrow> f\<^sub>1 \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> f\<^sub>1' \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1' v\<^sub>2"
| ev_pair2 [simp]: "f\<^sub>2 \<cdot> v\<^sub>2 \<leadsto> f\<^sub>2' \<cdot> v\<^sub>2' \<Longrightarrow> \<epsilon> \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> \<epsilon> \<parallel> f\<^sub>2' \<cdot> PairV v\<^sub>1 v\<^sub>2'"
| ev_pair3 [simp]: "\<epsilon> \<parallel> \<epsilon> \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> \<epsilon> \<cdot> PairV v\<^sub>1 v\<^sub>2"
| ev_tup [simp]: "\<Theta> \<cdot> v \<leadsto> \<epsilon> \<cdot> PairV v v"
| ev_inl [simp]: "\<iota>\<^sub>l \<cdot> v \<leadsto> \<epsilon> \<cdot> InlV v"
| ev_inr [simp]: "\<iota>\<^sub>r \<cdot> v \<leadsto> \<epsilon> \<cdot> InrV v"
| ev_strl [simp]: "\<Xi> \<cdot> InlV v \<leadsto> \<epsilon> \<cdot> v"
| ev_strr [simp]: "\<Xi> \<cdot> InrV v \<leadsto> \<epsilon> \<cdot> v"
| ev_csl [simp]: "f\<^sub>l \<bar> f\<^sub>r \<cdot> InlV v \<leadsto> (\<iota>\<^sub>l \<cdot> f\<^sub>l) \<cdot> v"
| ev_csr [simp]: "f\<^sub>l \<bar> f\<^sub>r \<cdot> InrV v \<leadsto> (\<iota>\<^sub>r \<cdot> f\<^sub>r) \<cdot> v"
| ev_dstl [simp]: "\<rhd> \<cdot> PairV (InlV v\<^sub>1) v\<^sub>2 \<leadsto> \<epsilon> \<cdot> InlV (PairV v\<^sub>1 v\<^sub>2)"
| ev_dstr [simp]: "\<rhd> \<cdot> PairV (InrV v\<^sub>1) v\<^sub>2 \<leadsto> \<epsilon> \<cdot> InrV (PairV v\<^sub>1 v\<^sub>2)"
| ev_app [simp]: "Apply \<cdot> PairV (FunV e) v \<leadsto> e \<cdot> v"
| ev_arr [simp]: "g \<leftarrow> f \<cdot> FunV e \<leadsto> \<epsilon> \<cdot> FunV (g \<cdot> e \<cdot> f)"
| ev_out [simp]: "Outj f \<cdot> InjV f v \<leadsto> \<epsilon> \<cdot> v"

(* safety *)

lemma canonical_unit: "v \<turnstile> \<one> \<Longrightarrow> v = UnitV"
  by (cases v \<one> rule: typecheck\<^sub>v.cases) simp_all

lemma canonical_prod: "v \<turnstile> t\<^sub>1 \<otimes> t\<^sub>2 \<Longrightarrow> \<exists>v\<^sub>1 v\<^sub>2. v\<^sub>1 \<turnstile> t\<^sub>1 \<and> v\<^sub>2 \<turnstile> t\<^sub>2 \<and> v = PairV v\<^sub>1 v\<^sub>2"
  by (cases v "t\<^sub>1 \<otimes> t\<^sub>2" rule: typecheck\<^sub>v.cases) simp_all

lemma canonical_sum: "v \<turnstile> t\<^sub>1 \<oplus> t\<^sub>2 \<Longrightarrow> \<exists>v'. (v' \<turnstile> t\<^sub>1 \<and> v = InlV v') \<or> (v' \<turnstile> t\<^sub>2 \<and> v = InrV v')"
  by (cases v "t\<^sub>1 \<oplus> t\<^sub>2" rule: typecheck\<^sub>v.cases) simp_all

lemma canonical_arrow: "v \<turnstile> t\<^sub>1 \<hookrightarrow> t\<^sub>2 \<Longrightarrow> \<exists>e. (e \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2) \<and> v = FunV e"
  by (cases v "t\<^sub>1 \<hookrightarrow> t\<^sub>2" rule: typecheck\<^sub>v.cases) simp_all

lemma canonical_mu: "v \<turnstile> \<mu> f \<Longrightarrow> \<exists>v'. v' \<turnstile> f \<star> \<mu> f \<and> v = InjV f v'"
  by (cases v "\<mu> f" rule: typecheck\<^sub>v.cases) simp_all

theorem progress: "e \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> v \<turnstile> t\<^sub>1 \<Longrightarrow> e \<noteq> \<epsilon> \<Longrightarrow> \<exists>e' v'. e \<cdot> v \<leadsto> e' \<cdot> v'"
    and "v \<turnstile> t\<^sub>1 \<Longrightarrow> True"
  proof (induction e t\<^sub>1 t\<^sub>2 arbitrary: v rule: typecheck\<^sub>e_typecheck\<^sub>v.inducts)
  case (tc_con v\<^sub>2 t\<^sub>2 t\<^sub>1)
    have "\<kappa> v\<^sub>2 \<cdot> v \<leadsto> \<epsilon> \<cdot> v\<^sub>2" by simp
    thus ?case by fastforce
  next case (tc_comp f t\<^sub>2 t\<^sub>3 g t\<^sub>1)
    thus ?case
      proof (cases "g = \<epsilon>")
      case True
        hence "(f \<cdot> g) \<cdot> v \<leadsto> f \<cdot> v" by simp
        thus ?thesis by fastforce
      next case False
        with tc_comp obtain g' v' where "g \<cdot> v \<leadsto> g' \<cdot> v'" by blast
        with tc_comp have "(f \<cdot> g) \<cdot> v \<leadsto> (f \<cdot> g') \<cdot> v'" by simp
        thus ?thesis by fastforce
      qed
  next case (tc_fst t\<^sub>1 t\<^sub>2)
    then obtain v\<^sub>1 v\<^sub>2 where "v = PairV v\<^sub>1 v\<^sub>2" using canonical_prod by blast
    hence "\<pi>\<^sub>1 \<cdot> v \<leadsto> \<epsilon> \<cdot> v\<^sub>1" by simp
    thus ?case by fastforce
  next case (tc_snd t\<^sub>1 t\<^sub>2)
    then obtain v\<^sub>1 v\<^sub>2 where "v = PairV v\<^sub>1 v\<^sub>2" using canonical_prod by blast
    hence "\<pi>\<^sub>2 \<cdot> v \<leadsto> \<epsilon> \<cdot> v\<^sub>2" by simp
    thus ?case by fastforce
  next case (tc_tup t)
    hence "\<Theta> \<cdot> v \<leadsto> \<epsilon> \<cdot> PairV v v" by simp
    thus ?case by fastforce
  next case (tc_pair f\<^sub>1 t\<^sub>1 t\<^sub>2 f\<^sub>2 t\<^sub>3 t\<^sub>4)
    then obtain v\<^sub>1 v\<^sub>2 where V: "v\<^sub>1 \<turnstile> t\<^sub>1 \<and> v\<^sub>2 \<turnstile> t\<^sub>3 \<and> v = PairV v\<^sub>1 v\<^sub>2" using canonical_prod by blast
    thus ?case
      proof (cases "f\<^sub>1 = \<epsilon>")
      case True note T = True
        thus ?thesis
          proof (cases "f\<^sub>2 = \<epsilon>")
          case True
            have "\<epsilon> \<parallel> \<epsilon> \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> \<epsilon> \<cdot> PairV v\<^sub>1 v\<^sub>2" by simp
            with T True V show ?thesis by fastforce
          next case False
            with tc_pair V obtain f\<^sub>2' v\<^sub>2' where "f\<^sub>2 \<cdot> v\<^sub>2 \<leadsto> f\<^sub>2' \<cdot> v\<^sub>2'" by blast
            hence "\<epsilon> \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> \<epsilon> \<parallel> f\<^sub>2' \<cdot> PairV v\<^sub>1 v\<^sub>2'" by simp
            with True V show ?thesis by fastforce
          qed
      next case False
        with tc_pair V obtain f\<^sub>1' v\<^sub>1' where "f\<^sub>1 \<cdot> v\<^sub>1 \<leadsto> f\<^sub>1' \<cdot> v\<^sub>1'" by blast    
        hence "f\<^sub>1 \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> f\<^sub>1' \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1' v\<^sub>2" by simp
        with V show ?thesis by fastforce
      qed
  next case (tc_inl t\<^sub>1 t\<^sub>2)
    hence "\<iota>\<^sub>l \<cdot> v \<leadsto> \<epsilon> \<cdot> InlV v" by simp
    thus ?case by fastforce
  next case (tc_inr t\<^sub>2 t\<^sub>1)
    hence "\<iota>\<^sub>r \<cdot> v \<leadsto> \<epsilon> \<cdot> InrV v" by simp
    thus ?case by fastforce
  next case tc_str
    then obtain v' where V: "v = InlV v' \<or> v = InrV v'" using canonical_sum by blast
    thus ?case
      proof (cases "v = InlV v'")
      case True
        hence "\<Xi> \<cdot> v \<leadsto> \<epsilon> \<cdot> v'" by simp
        thus ?thesis by fastforce
      next case False
        with V have "\<Xi> \<cdot> v \<leadsto> \<epsilon> \<cdot> v'" by simp
        thus ?thesis by fastforce
      qed
  next case (tc_case f\<^sub>l t\<^sub>1 t\<^sub>3 f\<^sub>r t\<^sub>2)
    then obtain v' where V: "v = InlV v' \<or> v = InrV v'" using canonical_sum by blast
    thus ?case
      proof (cases "v = InlV v'")
      case True
        hence "f\<^sub>l \<bar> f\<^sub>r \<cdot> v \<leadsto> (\<iota>\<^sub>l \<cdot> f\<^sub>l) \<cdot> v'" by simp
        thus ?thesis by fastforce
      next case False
        with V have "f\<^sub>l \<bar> f\<^sub>r \<cdot> v \<leadsto> (\<iota>\<^sub>r \<cdot> f\<^sub>r) \<cdot> v'" by simp
        thus ?thesis by fastforce
      qed
  next case (tc_dst t\<^sub>1 t\<^sub>2 t\<^sub>3)
    then obtain v\<^sub>1 v\<^sub>2 where V: "v = PairV (InlV v\<^sub>1) v\<^sub>2 \<or> v = PairV (InrV v\<^sub>1) v\<^sub>2" 
      using canonical_prod canonical_sum by blast
    thus ?case
      proof (cases "v = PairV (InlV v\<^sub>1) v\<^sub>2")
      case True
        hence "\<rhd> \<cdot> v \<leadsto> \<epsilon> \<cdot> InlV (PairV v\<^sub>1 v\<^sub>2)" by simp
        thus ?thesis by fastforce
      next case False
        with V have "\<rhd> \<cdot> v \<leadsto> \<epsilon> \<cdot> InrV (PairV v\<^sub>1 v\<^sub>2)" by simp
        thus ?thesis by fastforce
      qed
  next case (tc_app t\<^sub>1 t\<^sub>2)
    then obtain e v' where V: "v = PairV (FunV e) v'" using canonical_prod canonical_arrow by blast
    moreover hence "Apply \<cdot> v \<leadsto> e \<cdot> v'" by simp
    ultimately show ?case by fastforce
  next case (tc_arr f t\<^sub>1 t\<^sub>2 g t\<^sub>3 t\<^sub>4)
    then obtain e where "v = FunV e" using canonical_arrow by blast
    moreover hence "g \<leftarrow> f \<cdot> FunV e \<leadsto> \<epsilon> \<cdot> FunV (g \<cdot> e \<cdot> f)" by simp
    ultimately show ?case by fastforce
  next case (tc_outj f)
    then obtain v' where "v = InjV f v'" using canonical_mu by blast
    moreover hence "Outj f \<cdot> v \<leadsto> \<epsilon> \<cdot> v'" by simp
    ultimately show ?case by fastforce
  qed simp_all

theorem preservation: "e \<cdot> v \<leadsto> e' \<cdot> v' \<Longrightarrow> e \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> v \<turnstile> t\<^sub>1 \<Longrightarrow> 
    \<exists>t\<^sub>3. (e' \<turnstile> t\<^sub>3 \<rightarrow> t\<^sub>2) \<and> (v' \<turnstile> t\<^sub>3)"
  proof (induction e v e' v' arbitrary: t\<^sub>1 t\<^sub>2 rule: evaluate.induct)
  case (ev_pair1 f\<^sub>1 v\<^sub>1 f\<^sub>1' v\<^sub>1' f\<^sub>2 v\<^sub>2)
    then obtain t\<^sub>1\<^sub>1 t\<^sub>1\<^sub>2 t\<^sub>2\<^sub>1 t\<^sub>2\<^sub>2 t\<^sub>1\<^sub>1' where T: "v\<^sub>1 \<turnstile> t\<^sub>1\<^sub>1 \<and> v\<^sub>2 \<turnstile> t\<^sub>1\<^sub>2 \<and> (f\<^sub>1 \<turnstile> t\<^sub>1\<^sub>1 \<rightarrow> t\<^sub>2\<^sub>1) \<and> (f\<^sub>2 \<turnstile> t\<^sub>1\<^sub>2 \<rightarrow> t\<^sub>2\<^sub>2) \<and> 
      t\<^sub>1 = t\<^sub>1\<^sub>1 \<otimes> t\<^sub>1\<^sub>2 \<and> t\<^sub>2 = t\<^sub>2\<^sub>1 \<otimes> t\<^sub>2\<^sub>2 \<and> (f\<^sub>1' \<turnstile> t\<^sub>1\<^sub>1' \<rightarrow> t\<^sub>2\<^sub>1) \<and> v\<^sub>1' \<turnstile> t\<^sub>1\<^sub>1'" by fastforce
    hence "(f\<^sub>1' \<parallel> f\<^sub>2 \<turnstile> t\<^sub>1\<^sub>1' \<otimes> t\<^sub>1\<^sub>2 \<rightarrow> t\<^sub>2) \<and> PairV v\<^sub>1' v\<^sub>2 \<turnstile> t\<^sub>1\<^sub>1' \<otimes> t\<^sub>1\<^sub>2" by simp
    thus ?case by fastforce
  next case (ev_pair2 f\<^sub>2 v\<^sub>2 f\<^sub>2' v\<^sub>2' v\<^sub>1)
    then obtain t\<^sub>1\<^sub>1 t\<^sub>1\<^sub>2 t\<^sub>2\<^sub>2 t\<^sub>1\<^sub>2' where T: "v\<^sub>1 \<turnstile> t\<^sub>1\<^sub>1 \<and> v\<^sub>2 \<turnstile> t\<^sub>1\<^sub>2 \<and> (f\<^sub>2 \<turnstile> t\<^sub>1\<^sub>2 \<rightarrow> t\<^sub>2\<^sub>2) \<and> 
      t\<^sub>1 = t\<^sub>1\<^sub>1 \<otimes> t\<^sub>1\<^sub>2 \<and> t\<^sub>2 = t\<^sub>1\<^sub>1 \<otimes> t\<^sub>2\<^sub>2 \<and> (f\<^sub>2' \<turnstile> t\<^sub>1\<^sub>2' \<rightarrow> t\<^sub>2\<^sub>2) \<and> v\<^sub>2' \<turnstile> t\<^sub>1\<^sub>2'" by fastforce
    hence "(\<epsilon> \<parallel> f\<^sub>2' \<turnstile> t\<^sub>1\<^sub>1 \<otimes> t\<^sub>1\<^sub>2' \<rightarrow> t\<^sub>2) \<and> PairV v\<^sub>1 v\<^sub>2' \<turnstile> t\<^sub>1\<^sub>1 \<otimes> t\<^sub>1\<^sub>2'" by simp
    thus ?case by fastforce
  next case (ev_tup v)
    hence "t\<^sub>2 = t\<^sub>1 \<otimes> t\<^sub>1" by fastforce
    moreover from ev_tup have "(\<epsilon> \<turnstile> t\<^sub>1 \<otimes> t\<^sub>1 \<rightarrow> t\<^sub>1 \<otimes> t\<^sub>1) \<and> PairV v v \<turnstile> t\<^sub>1 \<otimes> t\<^sub>1" by simp
    ultimately show ?case by fastforce
  next case (ev_inl v)
    moreover then obtain t\<^sub>3 where "t\<^sub>2 = t\<^sub>1 \<oplus> t\<^sub>3" by fastforce
    ultimately have "(\<epsilon> \<turnstile> t\<^sub>1 \<oplus> t\<^sub>3 \<rightarrow> t\<^sub>2) \<and> InlV v \<turnstile> t\<^sub>1 \<oplus> t\<^sub>3" by simp
    thus ?case by fastforce
  next case (ev_inr v)
    moreover then obtain t\<^sub>3 where "t\<^sub>2 = t\<^sub>3 \<oplus> t\<^sub>1" by fastforce
    ultimately have "(\<epsilon> \<turnstile> t\<^sub>3 \<oplus> t\<^sub>1 \<rightarrow> t\<^sub>2) \<and> InrV v \<turnstile> t\<^sub>3 \<oplus> t\<^sub>1" by simp
    thus ?case by fastforce
  next case (ev_csl f\<^sub>l f\<^sub>r v)
    then obtain t\<^sub>1\<^sub>l t\<^sub>1\<^sub>r t\<^sub>2\<^sub>l t\<^sub>2\<^sub>r where V: "(f\<^sub>l \<turnstile> t\<^sub>1\<^sub>l \<rightarrow> t\<^sub>2\<^sub>l) \<and> (f\<^sub>r \<turnstile> t\<^sub>1\<^sub>r \<rightarrow> t\<^sub>2\<^sub>r) \<and> (v \<turnstile> t\<^sub>1\<^sub>l) \<and>
      t\<^sub>1 = t\<^sub>1\<^sub>l \<oplus> t\<^sub>1\<^sub>r \<and> t\<^sub>2 = t\<^sub>2\<^sub>l \<oplus> t\<^sub>2\<^sub>r" by fastforce
    hence "\<iota>\<^sub>l \<cdot> f\<^sub>l \<turnstile> t\<^sub>1\<^sub>l \<rightarrow> t\<^sub>2\<^sub>l \<oplus> t\<^sub>2\<^sub>r" by (metis tc_inl tc_comp)
    with V show ?case by fastforce
  next case (ev_csr f\<^sub>l f\<^sub>r v)
    then obtain t\<^sub>1\<^sub>l t\<^sub>1\<^sub>r t\<^sub>2\<^sub>l t\<^sub>2\<^sub>r where V: "(f\<^sub>l \<turnstile> t\<^sub>1\<^sub>l \<rightarrow> t\<^sub>2\<^sub>l) \<and> (f\<^sub>r \<turnstile> t\<^sub>1\<^sub>r \<rightarrow> t\<^sub>2\<^sub>r) \<and> (v \<turnstile> t\<^sub>1\<^sub>r) \<and>
      t\<^sub>1 = t\<^sub>1\<^sub>l \<oplus> t\<^sub>1\<^sub>r \<and> t\<^sub>2 = t\<^sub>2\<^sub>l \<oplus> t\<^sub>2\<^sub>r" by fastforce
    hence "\<iota>\<^sub>r \<cdot> f\<^sub>r \<turnstile> t\<^sub>1\<^sub>r \<rightarrow> t\<^sub>2\<^sub>l \<oplus> t\<^sub>2\<^sub>r" by (metis tc_inr tc_comp)
    with V show ?case by fastforce
  next case (ev_dstl v\<^sub>1 v\<^sub>2)
    then obtain t\<^sub>3 t\<^sub>4 t\<^sub>5 where "v\<^sub>1 \<turnstile> t\<^sub>3 \<and> v\<^sub>2 \<turnstile> t\<^sub>5 \<and> t\<^sub>1 = (t\<^sub>3 \<oplus> t\<^sub>4) \<otimes> t\<^sub>5 \<and> t\<^sub>2 = t\<^sub>3 \<otimes> t\<^sub>5 \<oplus> t\<^sub>4 \<otimes> t\<^sub>5" 
      by fastforce
    hence "(\<epsilon> \<turnstile> t\<^sub>2 \<rightarrow> t\<^sub>2) \<and> InlV (PairV v\<^sub>1 v\<^sub>2) \<turnstile> t\<^sub>2" by simp
    thus ?case by fastforce
  next case (ev_dstr v\<^sub>1 v\<^sub>2)
    then obtain t\<^sub>3 t\<^sub>4 t\<^sub>5 where "v\<^sub>1 \<turnstile> t\<^sub>4 \<and> v\<^sub>2 \<turnstile> t\<^sub>5 \<and> t\<^sub>1 = (t\<^sub>3 \<oplus> t\<^sub>4) \<otimes> t\<^sub>5 \<and> t\<^sub>2 = t\<^sub>3 \<otimes> t\<^sub>5 \<oplus> t\<^sub>4 \<otimes> t\<^sub>5" 
      by fastforce
    hence "(\<epsilon> \<turnstile> t\<^sub>2 \<rightarrow> t\<^sub>2) \<and> InrV (PairV v\<^sub>1 v\<^sub>2) \<turnstile> t\<^sub>2" by simp
    thus ?case by fastforce
  next case (ev_arr g f e)
    then obtain t\<^sub>1\<^sub>1 t\<^sub>1\<^sub>2 t\<^sub>2\<^sub>1 t\<^sub>2\<^sub>2 where "(f \<turnstile> t\<^sub>2\<^sub>1 \<rightarrow> t\<^sub>1\<^sub>1) \<and> (g \<turnstile> t\<^sub>1\<^sub>2 \<rightarrow> t\<^sub>2\<^sub>2) \<and> (e \<turnstile> t\<^sub>1\<^sub>1 \<rightarrow> t\<^sub>1\<^sub>2) \<and>
      t\<^sub>1 = t\<^sub>1\<^sub>1 \<hookrightarrow> t\<^sub>1\<^sub>2 \<and> t\<^sub>2 = t\<^sub>2\<^sub>1 \<hookrightarrow> t\<^sub>2\<^sub>2" by fastforce
    hence "(\<epsilon> \<turnstile> t\<^sub>2\<^sub>1 \<hookrightarrow> t\<^sub>2\<^sub>2 \<rightarrow> t\<^sub>2) \<and> FunV (g \<cdot> e \<cdot> f) \<turnstile> t\<^sub>2\<^sub>1 \<hookrightarrow> t\<^sub>2\<^sub>2" by fastforce
    thus ?case by fastforce
  qed force+

(* big-step evaluation *) 

inductive total_eval :: "expr \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool" (infix "\<cdot> _ \<Down>" 60) where
  tev_base [simp]: "\<epsilon> \<cdot> v \<Down> v"
| tev_step [simp]: "e \<cdot> v \<leadsto> e' \<cdot> v' \<Longrightarrow> e' \<cdot> v' \<Down> v'' \<Longrightarrow> e \<cdot> v \<Down> v''"

lemma [elim]: "f \<cdot> v \<Down> v' \<Longrightarrow> g \<cdot> v' \<Down> v'' \<Longrightarrow> (g \<cdot> f) \<cdot> v \<Down> v''"
  proof (induction f v v' rule: total_eval.induct)
  case (tev_base v)
    moreover have "(g \<cdot> \<epsilon>) \<cdot> v \<leadsto> g \<cdot> v" by simp
    ultimately show ?case by (metis tev_step)
  next case (tev_step f v f' v' v''')
    hence "(g \<cdot> f) \<cdot> v \<leadsto> (g \<cdot> f') \<cdot> v'" by simp
    moreover from tev_step have "(g \<cdot> f') \<cdot> v' \<Down> v''" by simp
    ultimately show ?case by (metis total_eval.tev_step)
  qed

lemma [simp]: "e \<cdot> v \<leadsto> \<epsilon> \<cdot> v' \<Longrightarrow> e \<cdot> v \<Down> v'"
  by rule (simp, simp)

lemma [elim]: "\<epsilon> \<cdot> v \<Down> v' \<Longrightarrow> v = v'"
  proof (induction \<epsilon> v v' rule: total_eval.induct)
  case (tev_step v e' v' v'')
    thus ?case by (induction \<epsilon> v e' v' rule: evaluate.induct)
  qed simp_all

lemma [simp]: "f\<^sub>2 \<cdot> v\<^sub>2 \<Down> v\<^sub>4 \<Longrightarrow> \<epsilon> \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<Down> PairV v\<^sub>1 v\<^sub>4"
  proof (induction f\<^sub>2 v\<^sub>2 v\<^sub>4 rule: total_eval.induct)
  case (tev_step f\<^sub>2 v\<^sub>2 f\<^sub>2' v\<^sub>2' v\<^sub>4)
    hence "\<epsilon> \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> \<epsilon> \<parallel> f\<^sub>2' \<cdot> PairV v\<^sub>1 v\<^sub>2'" by simp
    moreover from tev_step have "\<epsilon> \<parallel> f\<^sub>2' \<cdot> PairV v\<^sub>1 v\<^sub>2' \<Down> PairV v\<^sub>1 v\<^sub>4" by simp
    ultimately show ?case by simp
  qed simp_all

lemma [simp]: "f\<^sub>1 \<cdot> v\<^sub>1 \<Down> v\<^sub>3 \<Longrightarrow> f\<^sub>2 \<cdot> v\<^sub>2 \<Down> v\<^sub>4 \<Longrightarrow> f\<^sub>1 \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<Down> PairV v\<^sub>3 v\<^sub>4"
  proof (induction f\<^sub>1 v\<^sub>1 v\<^sub>3 rule: total_eval.induct)
  case (tev_step f\<^sub>1 v\<^sub>1 f\<^sub>1' v\<^sub>1' v\<^sub>3)
    hence "f\<^sub>1 \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> f\<^sub>1' \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1' v\<^sub>2" by simp
    moreover from tev_step have "f\<^sub>1' \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1' v\<^sub>2 \<Down> PairV v\<^sub>3 v\<^sub>4" by simp
    ultimately show ?case by simp
  qed simp_all

lemma [simp]: "f\<^sub>l \<cdot> v \<Down> v' \<Longrightarrow> f\<^sub>l \<bar> f\<^sub>r \<cdot> InlV v \<Down> InlV v'"
  proof
    show "f\<^sub>l \<bar> f\<^sub>r \<cdot> InlV v \<leadsto> (\<iota>\<^sub>l \<cdot> f\<^sub>l) \<cdot> v" by simp
    show "f\<^sub>l \<cdot> v \<Down> v' \<Longrightarrow> (\<iota>\<^sub>l \<cdot> f\<^sub>l) \<cdot> v \<Down> InlV v'" by auto
  qed

lemma [simp]: "f\<^sub>r \<cdot> v \<Down> v' \<Longrightarrow> f\<^sub>l \<bar> f\<^sub>r \<cdot> InrV v \<Down> InrV v'"
  proof
    show "f\<^sub>l \<bar> f\<^sub>r \<cdot> InrV v \<leadsto> (\<iota>\<^sub>r \<cdot> f\<^sub>r) \<cdot> v" by simp
    show "f\<^sub>r \<cdot> v \<Down> v' \<Longrightarrow> (\<iota>\<^sub>r \<cdot> f\<^sub>r) \<cdot> v \<Down> InrV v'" by auto
  qed

(* since we are a turing-complete language, total progress is not provable *)

theorem total_preservation: "e \<cdot> v \<Down> v' \<Longrightarrow> e \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> v \<turnstile> t\<^sub>1 \<Longrightarrow> v' \<turnstile> t\<^sub>2"
  proof (induction e v v' arbitrary: t\<^sub>1 rule: total_eval.induct)
  case (tev_step e v e' v' v'')
    moreover then obtain t\<^sub>3 where "(e' \<turnstile> t\<^sub>3 \<rightarrow> t\<^sub>2) \<and> (v' \<turnstile> t\<^sub>3)" by (metis preservation)
    ultimately show ?case by fastforce
  qed auto

end
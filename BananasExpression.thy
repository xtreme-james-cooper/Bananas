theory BananasExpression
imports Main
begin

typedecl name

datatype type = 
  Unit ("\<one>")
| Poly nat
| Prod type type (infixr "\<otimes>" 85)
| Sum type type (infixr "\<oplus>" 80)
| Func type type (infixr "\<hookrightarrow>" 70)
| Fix funct ("\<mu>")
and funct =
  Id
| K type
| ProdF funct funct (infixr "\<Otimes>" 85)
| SumF funct funct (infixr "\<Oplus>" 80)

datatype expr = 
  Identity ("\<epsilon>") | Const val ("\<kappa>") | Comp expr expr (infixr "\<cdot>" 65)
| Proj1 ("\<pi>\<^sub>1") | Proj2 ("\<pi>\<^sub>2") | Duplicate ("\<Theta>") | Pairwise expr expr (infixr "\<parallel>" 85)
| Injl ("\<iota>\<^sub>l") | Injr ("\<iota>\<^sub>r") | Strip ("\<Xi>") |  Case expr expr (infixr "\<bar>" 80)
| Distribute ("\<rhd>")
| Apply ("$") | Arrow expr expr (infixl "\<leftarrow>" 70)
| Inj funct ("\<succ>\<^bsub>_\<^esub>") | Outj funct ("\<prec>\<^bsub>_\<^esub>")
| Cata expr funct ("\<lparr> _ \<rparr>\<^bsub>_\<^esub>") | Ana expr funct ("\<lbrakk> _ \<rbrakk>\<^bsub>_\<^esub>")
| Var name
and val = 
  UnitV
| PairV val val 
| InlV val | InrV val
| FunV expr
| InjV funct val 

(* typechecking *)

fun apply_functor_type :: "type \<Rightarrow> funct \<Rightarrow> type" (infixl "\<star>" 75) where
  "t \<star> Id = t"
| "t \<star> K t' = t'"
| "t \<star> f\<^sub>1 \<Otimes> f\<^sub>2 = (t \<star> f\<^sub>1) \<otimes> (t \<star> f\<^sub>2)"
| "t \<star> f\<^sub>1 \<Oplus> f\<^sub>2 = (t \<star> f\<^sub>1) \<oplus> (t \<star> f\<^sub>2)"

inductive typecheck\<^sub>e :: "(name \<rightharpoonup> type \<times> type) \<Rightarrow> expr \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" (infix "\<turnstile> _ : _ \<rightarrow>" 60)
      and typecheck\<^sub>v :: "(name \<rightharpoonup> type \<times> type) \<Rightarrow> val \<Rightarrow> type \<Rightarrow> bool" (infix "\<turnstile> _ :" 60) where
  tc_id [simp]: "\<Gamma> \<turnstile> \<epsilon> : t \<rightarrow> t"
| tc_con [simp]: "\<Gamma> \<turnstile> v : t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> \<kappa> v : t\<^sub>1 \<rightarrow> t\<^sub>2"
| tc_comp [simp]: "\<Gamma> \<turnstile> f : t\<^sub>2 \<rightarrow> t\<^sub>3 \<Longrightarrow> \<Gamma> \<turnstile> g : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> f \<cdot> g : t\<^sub>1 \<rightarrow> t\<^sub>3"
| tc_fst [simp]: "\<Gamma> \<turnstile> \<pi>\<^sub>1 : t\<^sub>1 \<otimes> t\<^sub>2 \<rightarrow> t\<^sub>1"
| tc_snd [simp]: "\<Gamma> \<turnstile> \<pi>\<^sub>2 : t\<^sub>1 \<otimes> t\<^sub>2 \<rightarrow> t\<^sub>2"
| tc_tup [simp]: "\<Gamma> \<turnstile> \<Theta> : t \<rightarrow> t \<otimes> t"
| tc_pair [simp]: "\<Gamma> \<turnstile> f\<^sub>1 : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> f\<^sub>2 : t\<^sub>3 \<rightarrow> t\<^sub>4 \<Longrightarrow> \<Gamma> \<turnstile> f\<^sub>1 \<parallel> f\<^sub>2 : t\<^sub>1 \<otimes> t\<^sub>3 \<rightarrow> t\<^sub>2 \<otimes> t\<^sub>4"
| tc_inl [simp]: "\<Gamma> \<turnstile> \<iota>\<^sub>l : t\<^sub>1 \<rightarrow> t\<^sub>1 \<oplus> t\<^sub>2"
| tc_inr [simp]: "\<Gamma> \<turnstile> \<iota>\<^sub>r : t\<^sub>2 \<rightarrow> t\<^sub>1 \<oplus> t\<^sub>2"
| tc_str [simp]: "\<Gamma> \<turnstile> \<Xi> : t\<^sub>1 \<oplus> t\<^sub>1 \<rightarrow> t\<^sub>1"
| tc_case [simp]: "\<Gamma> \<turnstile> f\<^sub>l : t\<^sub>1 \<rightarrow> t\<^sub>3 \<Longrightarrow> \<Gamma> \<turnstile> f\<^sub>r : t\<^sub>2 \<rightarrow> t\<^sub>4 \<Longrightarrow> \<Gamma> \<turnstile> f\<^sub>l \<bar> f\<^sub>r : t\<^sub>1 \<oplus> t\<^sub>2 \<rightarrow> t\<^sub>3 \<oplus> t\<^sub>4"
| tc_dst [simp]: "\<Gamma> \<turnstile> \<rhd> : (t\<^sub>1 \<oplus> t\<^sub>2) \<otimes> t\<^sub>3 \<rightarrow> t\<^sub>1 \<otimes> t\<^sub>3 \<oplus> t\<^sub>2 \<otimes> t\<^sub>3"
| tc_app [simp]: "\<Gamma> \<turnstile> $ : (t\<^sub>1 \<hookrightarrow> t\<^sub>2) \<otimes> t\<^sub>1 \<rightarrow> t\<^sub>2"
| tc_arr [simp]: "\<Gamma> \<turnstile> f : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> g : t\<^sub>3 \<rightarrow> t\<^sub>4 \<Longrightarrow> \<Gamma> \<turnstile> g \<leftarrow> f : t\<^sub>2 \<hookrightarrow> t\<^sub>3 \<rightarrow> t\<^sub>1 \<hookrightarrow> t\<^sub>4"
| tc_inj [simp]: "\<Gamma> \<turnstile> \<succ>\<^bsub>F\<^esub> : \<mu> F \<star> F \<rightarrow> \<mu> F"
| tc_outj [simp]: "\<Gamma> \<turnstile> \<prec>\<^bsub>F\<^esub> : \<mu> F \<rightarrow> \<mu> F \<star> F"
| tc_cata [simp]: "\<Gamma> \<turnstile> f : t \<star> F \<rightarrow> t \<Longrightarrow> \<Gamma> \<turnstile> \<lparr> f \<rparr>\<^bsub>F\<^esub> : \<mu> F \<rightarrow> t"
| tc_ana [simp]: "\<Gamma> \<turnstile> f : t \<rightarrow> t \<star> F \<Longrightarrow> \<Gamma> \<turnstile> \<lbrakk> f \<rbrakk>\<^bsub>F\<^esub> : t \<rightarrow> \<mu> F"
| tc_var [simp]: "\<Gamma> x = Some (t\<^sub>1, t\<^sub>2) \<Longrightarrow> \<Gamma> \<turnstile> Var x : t\<^sub>1 \<rightarrow> t\<^sub>2"

| tcv_unit [simp]: "\<Gamma> \<turnstile> UnitV : \<one>"
| tcv_pair [simp]: "\<Gamma> \<turnstile> v\<^sub>1 : t\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile> v\<^sub>2 : t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> PairV v\<^sub>1 v\<^sub>2 : t\<^sub>1 \<otimes> t\<^sub>2"
| tcv_inl [simp]: "\<Gamma> \<turnstile> v : t\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile> InlV v : t\<^sub>1 \<oplus> t\<^sub>2"
| tcv_inr [simp]: "\<Gamma> \<turnstile> v : t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> InrV v : t\<^sub>1 \<oplus> t\<^sub>2"
| tcv_fun [simp]: "\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> FunV e : t\<^sub>1 \<hookrightarrow> t\<^sub>2"
| tcv_inj [simp]: "\<Gamma> \<turnstile> v : \<mu> F \<star> F \<Longrightarrow> \<Gamma> \<turnstile> InjV F v : \<mu> F"

inductive_cases [elim]: "\<Gamma> \<turnstile> \<epsilon> : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> \<kappa> v : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> f \<cdot> g : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> \<pi>\<^sub>1 : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> \<pi>\<^sub>2 : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> \<Theta> : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> f\<^sub>l \<parallel> f\<^sub>r : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> \<iota>\<^sub>l : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> \<iota>\<^sub>r : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> \<Xi> : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> f\<^sub>l \<bar> f\<^sub>r : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> \<rhd> : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> $ : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> g \<leftarrow> f : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> \<prec>\<^bsub>F\<^esub> : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> \<succ>\<^bsub>F\<^esub> : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> \<lparr> f \<rparr>\<^bsub>F\<^esub> : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> \<lbrakk> f \<rbrakk>\<^bsub>F\<^esub> : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> Var x : t \<rightarrow> t'"

inductive_cases [elim]: "\<Gamma> \<turnstile> UnitV : t"
inductive_cases [elim]: "\<Gamma> \<turnstile> PairV v\<^sub>1 v\<^sub>2 : t"
inductive_cases [elim]: "\<Gamma> \<turnstile> InrV v : t"
inductive_cases [elim]: "\<Gamma> \<turnstile> InlV v : t"
inductive_cases [elim]: "\<Gamma> \<turnstile> FunV e : t"
inductive_cases [elim]: "\<Gamma> \<turnstile> InjV f v : t"

definition typecheck_context :: "(name \<rightharpoonup> type \<times> type) \<Rightarrow> (name \<rightharpoonup> expr) \<Rightarrow> bool" 
    (infix "\<tturnstile>" 60) where
  "\<Gamma> \<tturnstile> \<Lambda> = (\<forall>x t\<^sub>1 t\<^sub>2. \<Gamma> x = Some (t\<^sub>1, t\<^sub>2) \<longrightarrow> (\<exists>e. \<Lambda> x = Some e \<and> \<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2))"

(* evaluation *)

fun apply_functor_expr :: "expr \<Rightarrow> funct \<Rightarrow> expr" (infixl "\<bullet>" 75) where
  "e \<bullet> Id = e"
| "e \<bullet> K t = \<epsilon>"
| "e \<bullet> f\<^sub>1 \<Otimes> f\<^sub>2 = (e \<bullet> f\<^sub>1) \<parallel> (e \<bullet> f\<^sub>2)"
| "e \<bullet> f\<^sub>1 \<Oplus> f\<^sub>2 = (e \<bullet> f\<^sub>1) \<bar> (e \<bullet> f\<^sub>2)"

inductive evaluate :: "(name \<rightharpoonup> expr) \<Rightarrow> expr \<Rightarrow> val \<Rightarrow> expr \<Rightarrow> val \<Rightarrow> bool" 
    (infix "\<turnstile> _ \<cdot> _ \<leadsto> _ \<cdot>" 60) where
  ev_con [simp]: "\<Lambda> \<turnstile> \<kappa> v\<^sub>1 \<cdot> v\<^sub>2 \<leadsto> \<epsilon> \<cdot> v\<^sub>1"
| ev_comp1 [simp]: "\<Lambda> \<turnstile> g \<cdot> v \<leadsto> g' \<cdot> v' \<Longrightarrow> \<Lambda> \<turnstile> (f \<cdot> g) \<cdot> v \<leadsto> (f \<cdot> g') \<cdot> v'"
| ev_comp2 [simp]: "\<Lambda> \<turnstile> (f \<cdot> \<epsilon>) \<cdot> v \<leadsto> f \<cdot> v"
| ev_fst [simp]: "\<Lambda> \<turnstile> \<pi>\<^sub>1 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> \<epsilon> \<cdot> v\<^sub>1"
| ev_snd [simp]: "\<Lambda> \<turnstile> \<pi>\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> \<epsilon> \<cdot> v\<^sub>2"
| ev_pair1 [simp]: "\<Lambda> \<turnstile> f\<^sub>1 \<cdot> v\<^sub>1 \<leadsto> f\<^sub>1' \<cdot> v\<^sub>1' \<Longrightarrow> \<Lambda> \<turnstile> f\<^sub>1 \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> f\<^sub>1' \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1' v\<^sub>2"
| ev_pair2 [simp]: "\<Lambda> \<turnstile> f\<^sub>2 \<cdot> v\<^sub>2 \<leadsto> f\<^sub>2' \<cdot> v\<^sub>2' \<Longrightarrow> \<Lambda> \<turnstile> \<epsilon> \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> \<epsilon> \<parallel> f\<^sub>2' \<cdot> PairV v\<^sub>1 v\<^sub>2'"
| ev_pair3 [simp]: "\<Lambda> \<turnstile> \<epsilon> \<parallel> \<epsilon> \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> \<epsilon> \<cdot> PairV v\<^sub>1 v\<^sub>2"
| ev_tup [simp]: "\<Lambda> \<turnstile> \<Theta> \<cdot> v \<leadsto> \<epsilon> \<cdot> PairV v v"
| ev_inl [simp]: "\<Lambda> \<turnstile> \<iota>\<^sub>l \<cdot> v \<leadsto> \<epsilon> \<cdot> InlV v"
| ev_inr [simp]: "\<Lambda> \<turnstile> \<iota>\<^sub>r \<cdot> v \<leadsto> \<epsilon> \<cdot> InrV v"
| ev_strl [simp]: "\<Lambda> \<turnstile> \<Xi> \<cdot> InlV v \<leadsto> \<epsilon> \<cdot> v"
| ev_strr [simp]: "\<Lambda> \<turnstile> \<Xi> \<cdot> InrV v \<leadsto> \<epsilon> \<cdot> v"
| ev_csl [simp]: "\<Lambda> \<turnstile> f\<^sub>l \<bar> f\<^sub>r \<cdot> InlV v \<leadsto> (\<iota>\<^sub>l \<cdot> f\<^sub>l) \<cdot> v"
| ev_csr [simp]: "\<Lambda> \<turnstile> f\<^sub>l \<bar> f\<^sub>r \<cdot> InrV v \<leadsto> (\<iota>\<^sub>r \<cdot> f\<^sub>r) \<cdot> v"
| ev_dstl [simp]: "\<Lambda> \<turnstile> \<rhd> \<cdot> PairV (InlV v\<^sub>1) v\<^sub>2 \<leadsto> \<epsilon> \<cdot> InlV (PairV v\<^sub>1 v\<^sub>2)"
| ev_dstr [simp]: "\<Lambda> \<turnstile> \<rhd> \<cdot> PairV (InrV v\<^sub>1) v\<^sub>2 \<leadsto> \<epsilon> \<cdot> InrV (PairV v\<^sub>1 v\<^sub>2)"
| ev_app [simp]: "\<Lambda> \<turnstile> $ \<cdot> PairV (FunV e) v \<leadsto> e \<cdot> v"
| ev_arr [simp]: "\<Lambda> \<turnstile> g \<leftarrow> f \<cdot> FunV e \<leadsto> \<epsilon> \<cdot> FunV (g \<cdot> e \<cdot> f)"
| ev_inj [simp]: "\<Lambda> \<turnstile> \<succ>\<^bsub>F\<^esub> \<cdot> v \<leadsto> \<epsilon> \<cdot> InjV F v"
| ev_outj [simp]: "\<Lambda> \<turnstile> \<prec>\<^bsub>F\<^esub> \<cdot> InjV F v \<leadsto> \<epsilon> \<cdot> v"
| ev_cata [simp]: "\<Lambda> \<turnstile> \<lparr> f \<rparr>\<^bsub>F\<^esub> \<cdot> v \<leadsto> (f \<cdot> \<lparr> f \<rparr>\<^bsub>F\<^esub> \<bullet> F \<cdot> \<prec>\<^bsub>F\<^esub>) \<cdot> v"
| ev_ana [simp]: "\<Lambda> \<turnstile> \<lbrakk> f \<rbrakk>\<^bsub>F\<^esub> \<cdot> v \<leadsto> (\<succ>\<^bsub>F\<^esub> \<cdot> \<lbrakk> f \<rbrakk>\<^bsub>F\<^esub> \<bullet> F \<cdot> f) \<cdot> v"
| ev_var [simp]: "\<Lambda> x = Some e \<Longrightarrow> \<Lambda> \<turnstile> Var x \<cdot> v \<leadsto> e \<cdot> v"

(* safety *)

lemma canonical_unit: "\<Gamma> \<turnstile> v : \<one> \<Longrightarrow> v = UnitV"
  by (cases \<Gamma> v \<one> rule: typecheck\<^sub>v.cases) simp_all

lemma canonical_prod: "\<Gamma> \<turnstile> v : t\<^sub>1 \<otimes> t\<^sub>2 \<Longrightarrow> \<exists>v\<^sub>1 v\<^sub>2. (\<Gamma> \<turnstile> v\<^sub>1 : t\<^sub>1) \<and> (\<Gamma> \<turnstile> v\<^sub>2 : t\<^sub>2) \<and> v = PairV v\<^sub>1 v\<^sub>2"
  by (cases \<Gamma> v "t\<^sub>1 \<otimes> t\<^sub>2" rule: typecheck\<^sub>v.cases) simp_all

lemma canonical_sum: "\<Gamma> \<turnstile> v : t\<^sub>1 \<oplus> t\<^sub>2 \<Longrightarrow> 
    \<exists>v'. ((\<Gamma> \<turnstile> v' : t\<^sub>1) \<and> v = InlV v') \<or> ((\<Gamma> \<turnstile> v' : t\<^sub>2) \<and> v = InrV v')"
  by (cases \<Gamma> v "t\<^sub>1 \<oplus> t\<^sub>2" rule: typecheck\<^sub>v.cases) simp_all

lemma canonical_arrow: "\<Gamma> \<turnstile> v : t\<^sub>1 \<hookrightarrow> t\<^sub>2 \<Longrightarrow> \<exists>e. (\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2) \<and> v = FunV e"
  by (cases \<Gamma> v "t\<^sub>1 \<hookrightarrow> t\<^sub>2" rule: typecheck\<^sub>v.cases) simp_all

lemma canonical_mu: "\<Gamma> \<turnstile> v : \<mu> F \<Longrightarrow> \<exists>v'. (\<Gamma> \<turnstile> v' : \<mu> F \<star> F) \<and> v = InjV F v'"
  by (cases \<Gamma> v "\<mu> F" rule: typecheck\<^sub>v.cases) simp_all

theorem progress [simp]: "\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> v : t\<^sub>1 \<Longrightarrow> \<Gamma> \<tturnstile> \<Lambda> \<Longrightarrow> e \<noteq> \<epsilon> \<Longrightarrow> 
    \<exists>e' v'. \<Lambda> \<turnstile> e \<cdot> v \<leadsto> e' \<cdot> v'"
    and "\<Gamma> \<turnstile> v : t\<^sub>1 \<Longrightarrow> True"
  proof (induction \<Gamma> e t\<^sub>1 t\<^sub>2 arbitrary: v rule: typecheck\<^sub>e_typecheck\<^sub>v.inducts)
  case (tc_con \<Gamma> v\<^sub>2 t\<^sub>2 t\<^sub>1)
    have "\<Lambda> \<turnstile> \<kappa> v\<^sub>2 \<cdot> v \<leadsto> \<epsilon> \<cdot> v\<^sub>2" by simp
    thus ?case by fastforce
  next case (tc_comp \<Gamma> f t\<^sub>2 t\<^sub>3 g)
    thus ?case
      proof (cases "g = \<epsilon>")
      case True
        hence "\<Lambda> \<turnstile> (f \<cdot> g) \<cdot> v \<leadsto> f \<cdot> v" by simp
        thus ?thesis by fastforce
      next case False
        with tc_comp obtain g' v' where "\<Lambda> \<turnstile> g \<cdot> v \<leadsto> g' \<cdot> v'" by blast
        with tc_comp have "\<Lambda> \<turnstile> (f \<cdot> g) \<cdot> v \<leadsto> (f \<cdot> g') \<cdot> v'" by simp
        thus ?thesis by fastforce
      qed
  next case tc_fst
    then obtain v\<^sub>1 v\<^sub>2 where "v = PairV v\<^sub>1 v\<^sub>2" using canonical_prod by blast
    hence "\<Lambda> \<turnstile> \<pi>\<^sub>1 \<cdot> v \<leadsto> \<epsilon> \<cdot> v\<^sub>1" by simp
    thus ?case by fastforce
  next case tc_snd
    then obtain v\<^sub>1 v\<^sub>2 where "v = PairV v\<^sub>1 v\<^sub>2" using canonical_prod by blast
    hence "\<Lambda> \<turnstile> \<pi>\<^sub>2 \<cdot> v \<leadsto> \<epsilon> \<cdot> v\<^sub>2" by simp
    thus ?case by fastforce
  next case tc_tup
    hence "\<Lambda> \<turnstile> \<Theta> \<cdot> v \<leadsto> \<epsilon> \<cdot> PairV v v" by simp
    thus ?case by fastforce
  next case (tc_pair \<Gamma> f\<^sub>1 t\<^sub>1 t\<^sub>2 f\<^sub>2)
    then obtain v\<^sub>1 v\<^sub>2 where V: "v = PairV v\<^sub>1 v\<^sub>2" using canonical_prod by blast
    thus ?case
      proof (cases "f\<^sub>1 = \<epsilon>")
      case True note T = True
        thus ?thesis
          proof (cases "f\<^sub>2 = \<epsilon>")
          case True
            have "\<Lambda> \<turnstile> \<epsilon> \<parallel> \<epsilon> \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> \<epsilon> \<cdot> PairV v\<^sub>1 v\<^sub>2" by simp
            with T True V show ?thesis by fastforce
          next case False
            with tc_pair V obtain f\<^sub>2' v\<^sub>2' where "\<Lambda> \<turnstile> f\<^sub>2 \<cdot> v\<^sub>2 \<leadsto> f\<^sub>2' \<cdot> v\<^sub>2'" by blast
            hence "\<Lambda> \<turnstile> \<epsilon> \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> \<epsilon> \<parallel> f\<^sub>2' \<cdot> PairV v\<^sub>1 v\<^sub>2'" by simp
            with True V show ?thesis by fastforce
          qed
      next case False
        with tc_pair V obtain f\<^sub>1' v\<^sub>1' where "\<Lambda> \<turnstile> f\<^sub>1 \<cdot> v\<^sub>1 \<leadsto> f\<^sub>1' \<cdot> v\<^sub>1'" by blast    
        hence "\<Lambda> \<turnstile> f\<^sub>1 \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> f\<^sub>1' \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1' v\<^sub>2" by simp
        with V show ?thesis by fastforce
      qed
  next case tc_inl
    hence "\<Lambda> \<turnstile> \<iota>\<^sub>l \<cdot> v \<leadsto> \<epsilon> \<cdot> InlV v" by simp
    thus ?case by fastforce
  next case tc_inr
    hence "\<Lambda> \<turnstile> \<iota>\<^sub>r \<cdot> v \<leadsto> \<epsilon> \<cdot> InrV v" by simp
    thus ?case by fastforce
  next case tc_str
    then obtain v' where V: "v = InlV v' \<or> v = InrV v'" using canonical_sum by blast
    thus ?case
      proof (cases "v = InlV v'")
      case True
        hence "\<Lambda> \<turnstile> \<Xi> \<cdot> v \<leadsto> \<epsilon> \<cdot> v'" by simp
        thus ?thesis by fastforce
      next case False
        with V have "\<Lambda> \<turnstile> \<Xi> \<cdot> v \<leadsto> \<epsilon> \<cdot> v'" by simp
        thus ?thesis by fastforce
      qed
  next case (tc_case \<Gamma> f\<^sub>l t\<^sub>1 t\<^sub>3 f\<^sub>r)
    then obtain v' where V: "v = InlV v' \<or> v = InrV v'" using canonical_sum by blast
    thus ?case
      proof (cases "v = InlV v'")
      case True
        hence "\<Lambda> \<turnstile> f\<^sub>l \<bar> f\<^sub>r \<cdot> v \<leadsto> (\<iota>\<^sub>l \<cdot> f\<^sub>l) \<cdot> v'" by simp
        thus ?thesis by fastforce
      next case False
        with V have "\<Lambda> \<turnstile> f\<^sub>l \<bar> f\<^sub>r \<cdot> v \<leadsto> (\<iota>\<^sub>r \<cdot> f\<^sub>r) \<cdot> v'" by simp
        thus ?thesis by fastforce
      qed
  next case tc_dst
    then obtain v\<^sub>1 v\<^sub>2 where V: "v = PairV (InlV v\<^sub>1) v\<^sub>2 \<or> v = PairV (InrV v\<^sub>1) v\<^sub>2" 
      using canonical_prod canonical_sum by blast
    thus ?case
      proof (cases "v = PairV (InlV v\<^sub>1) v\<^sub>2")
      case True
        hence "\<Lambda> \<turnstile> \<rhd> \<cdot> v \<leadsto> \<epsilon> \<cdot> InlV (PairV v\<^sub>1 v\<^sub>2)" by simp
        thus ?thesis by fastforce
      next case False
        with V have "\<Lambda> \<turnstile> \<rhd> \<cdot> v \<leadsto> \<epsilon> \<cdot> InrV (PairV v\<^sub>1 v\<^sub>2)" by simp
        thus ?thesis by fastforce
      qed
  next case tc_app
    then obtain e v' where V: "v = PairV (FunV e) v'" using canonical_prod canonical_arrow by blast
    moreover hence "\<Lambda> \<turnstile> $ \<cdot> v \<leadsto> e \<cdot> v'" by simp
    ultimately show ?case by fastforce
  next case (tc_arr \<Gamma> f t\<^sub>1 t\<^sub>2 g)
    then obtain e where "v = FunV e" using canonical_arrow by blast
    moreover hence "\<Lambda> \<turnstile> g \<leftarrow> f \<cdot> FunV e \<leadsto> \<epsilon> \<cdot> FunV (g \<cdot> e \<cdot> f)" by simp
    ultimately show ?case by fastforce
  next case (tc_inj \<Gamma> F)
    hence "\<Lambda> \<turnstile> \<succ>\<^bsub>F\<^esub> \<cdot> v \<leadsto> \<epsilon> \<cdot> InjV F v" by simp
    thus ?case by fastforce
  next case (tc_outj \<Gamma> F)
    then obtain v' where "v = InjV F v'" using canonical_mu by blast
    moreover hence "\<Lambda> \<turnstile> \<prec>\<^bsub>F\<^esub> \<cdot> v \<leadsto> \<epsilon> \<cdot> v'" by simp
    ultimately show ?case by fastforce
  next case (tc_cata \<Gamma> f t F)
    hence "\<Lambda> \<turnstile> \<lparr> f \<rparr>\<^bsub>F\<^esub> \<cdot> v \<leadsto> (f \<cdot> \<lparr> f \<rparr>\<^bsub>F\<^esub> \<bullet> F \<cdot> \<prec>\<^bsub>F\<^esub>) \<cdot> v" by simp
    thus ?case by fastforce
  next case (tc_ana \<Gamma> f t F)
    hence "\<Lambda> \<turnstile> \<lbrakk> f \<rbrakk>\<^bsub>F\<^esub> \<cdot> v \<leadsto> (\<succ>\<^bsub>F\<^esub> \<cdot> \<lbrakk> f \<rbrakk>\<^bsub>F\<^esub> \<bullet> F \<cdot> f) \<cdot> v" by simp
    thus ?case by fastforce
  next case (tc_var \<Gamma> x t\<^sub>1 t\<^sub>2)
    then obtain e where "\<Lambda> x = Some e \<and> \<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2" by (metis typecheck_context_def)
    hence "\<Lambda> \<turnstile> Var x \<cdot> v \<leadsto> e \<cdot> v" by simp
    thus ?case by fastforce
  qed simp_all

lemma [simp]: "\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> e \<bullet> F : t\<^sub>1 \<star> F \<rightarrow> t\<^sub>2 \<star> F"
  by (induction e F rule: apply_functor_expr.induct) simp_all

theorem preservation [simp]: "\<Lambda> \<turnstile> e \<cdot> v \<leadsto> e' \<cdot> v' \<Longrightarrow> \<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> v : t\<^sub>1 \<Longrightarrow> \<Gamma> \<tturnstile> \<Lambda> \<Longrightarrow>
    \<exists>t\<^sub>3. (\<Gamma> \<turnstile> e' : t\<^sub>3 \<rightarrow> t\<^sub>2) \<and> (\<Gamma> \<turnstile> v' : t\<^sub>3)"
  proof (induction \<Lambda> e v e' v' arbitrary: t\<^sub>1 t\<^sub>2 rule: evaluate.induct)
  case (ev_pair1 \<Lambda> f\<^sub>1 v\<^sub>1 f\<^sub>1' v\<^sub>1' f\<^sub>2 v\<^sub>2)
    then obtain t\<^sub>1\<^sub>1 t\<^sub>1\<^sub>2 t\<^sub>2\<^sub>1 t\<^sub>2\<^sub>2 t\<^sub>1\<^sub>1' where T: "(\<Gamma> \<turnstile> v\<^sub>1 : t\<^sub>1\<^sub>1) \<and> (\<Gamma> \<turnstile> v\<^sub>2 : t\<^sub>1\<^sub>2) \<and> 
      (\<Gamma> \<turnstile> f\<^sub>1 : t\<^sub>1\<^sub>1 \<rightarrow> t\<^sub>2\<^sub>1) \<and> (\<Gamma> \<turnstile> f\<^sub>2 : t\<^sub>1\<^sub>2 \<rightarrow> t\<^sub>2\<^sub>2) \<and> t\<^sub>1 = t\<^sub>1\<^sub>1 \<otimes> t\<^sub>1\<^sub>2 \<and> t\<^sub>2 = t\<^sub>2\<^sub>1 \<otimes> t\<^sub>2\<^sub>2 \<and> 
        (\<Gamma> \<turnstile> f\<^sub>1' : t\<^sub>1\<^sub>1' \<rightarrow> t\<^sub>2\<^sub>1) \<and> \<Gamma> \<turnstile> v\<^sub>1' : t\<^sub>1\<^sub>1'" by fastforce
    hence "(\<Gamma> \<turnstile> f\<^sub>1' \<parallel> f\<^sub>2 : t\<^sub>1\<^sub>1' \<otimes> t\<^sub>1\<^sub>2 \<rightarrow> t\<^sub>2) \<and> \<Gamma> \<turnstile> PairV v\<^sub>1' v\<^sub>2 : t\<^sub>1\<^sub>1' \<otimes> t\<^sub>1\<^sub>2" by simp
    thus ?case by fastforce
  next case (ev_pair2 \<Lambda> f\<^sub>2 v\<^sub>2 f\<^sub>2' v\<^sub>2' v\<^sub>1)
    then obtain t\<^sub>1\<^sub>1 t\<^sub>1\<^sub>2 t\<^sub>2\<^sub>2 t\<^sub>1\<^sub>2' where T: "(\<Gamma> \<turnstile> v\<^sub>1 : t\<^sub>1\<^sub>1) \<and> (\<Gamma> \<turnstile> v\<^sub>2 : t\<^sub>1\<^sub>2) \<and> (\<Gamma> \<turnstile> f\<^sub>2 : t\<^sub>1\<^sub>2 \<rightarrow> t\<^sub>2\<^sub>2) \<and> 
      t\<^sub>1 = t\<^sub>1\<^sub>1 \<otimes> t\<^sub>1\<^sub>2 \<and> t\<^sub>2 = t\<^sub>1\<^sub>1 \<otimes> t\<^sub>2\<^sub>2 \<and> (\<Gamma> \<turnstile> f\<^sub>2' : t\<^sub>1\<^sub>2' \<rightarrow> t\<^sub>2\<^sub>2) \<and> \<Gamma> \<turnstile> v\<^sub>2' : t\<^sub>1\<^sub>2'" by fastforce
    hence "(\<Gamma> \<turnstile> \<epsilon> \<parallel> f\<^sub>2' : t\<^sub>1\<^sub>1 \<otimes> t\<^sub>1\<^sub>2' \<rightarrow> t\<^sub>2) \<and> \<Gamma> \<turnstile> PairV v\<^sub>1 v\<^sub>2' : t\<^sub>1\<^sub>1 \<otimes> t\<^sub>1\<^sub>2'" by simp
    thus ?case by fastforce
  next case (ev_tup \<Lambda> v)
    hence "t\<^sub>2 = t\<^sub>1 \<otimes> t\<^sub>1" by fastforce
    moreover from ev_tup have "(\<Gamma> \<turnstile> \<epsilon> : t\<^sub>1 \<otimes> t\<^sub>1 \<rightarrow> t\<^sub>1 \<otimes> t\<^sub>1) \<and> \<Gamma> \<turnstile> PairV v v : t\<^sub>1 \<otimes> t\<^sub>1" by simp
    ultimately show ?case by fastforce
  next case (ev_inl \<Lambda> v)
    moreover then obtain t\<^sub>3 where "t\<^sub>2 = t\<^sub>1 \<oplus> t\<^sub>3" by fastforce
    ultimately have "(\<Gamma> \<turnstile> \<epsilon> : t\<^sub>1 \<oplus> t\<^sub>3 \<rightarrow> t\<^sub>2) \<and> \<Gamma> \<turnstile> InlV v : t\<^sub>1 \<oplus> t\<^sub>3" by simp
    thus ?case by fastforce
  next case (ev_inr \<Lambda> v)
    moreover then obtain t\<^sub>3 where "t\<^sub>2 = t\<^sub>3 \<oplus> t\<^sub>1" by fastforce
    ultimately have "(\<Gamma> \<turnstile> \<epsilon> : t\<^sub>3 \<oplus> t\<^sub>1 \<rightarrow> t\<^sub>2) \<and> \<Gamma> \<turnstile> InrV v : t\<^sub>3 \<oplus> t\<^sub>1" by simp
    thus ?case by fastforce
  next case (ev_csl \<Lambda> f\<^sub>l f\<^sub>r v)
    then obtain t\<^sub>1\<^sub>l t\<^sub>1\<^sub>r t\<^sub>2\<^sub>l t\<^sub>2\<^sub>r where V: "(\<Gamma> \<turnstile> f\<^sub>l : t\<^sub>1\<^sub>l \<rightarrow> t\<^sub>2\<^sub>l) \<and> (\<Gamma> \<turnstile> f\<^sub>r : t\<^sub>1\<^sub>r \<rightarrow> t\<^sub>2\<^sub>r) \<and> 
      (\<Gamma> \<turnstile> v : t\<^sub>1\<^sub>l) \<and> t\<^sub>1 = t\<^sub>1\<^sub>l \<oplus> t\<^sub>1\<^sub>r \<and> t\<^sub>2 = t\<^sub>2\<^sub>l \<oplus> t\<^sub>2\<^sub>r" by fastforce
    hence "\<Gamma> \<turnstile> \<iota>\<^sub>l \<cdot> f\<^sub>l : t\<^sub>1\<^sub>l \<rightarrow> t\<^sub>2\<^sub>l \<oplus> t\<^sub>2\<^sub>r" by (metis tc_inl tc_comp)
    with V show ?case by fastforce
  next case (ev_csr \<Lambda> f\<^sub>l f\<^sub>r v)
    then obtain t\<^sub>1\<^sub>l t\<^sub>1\<^sub>r t\<^sub>2\<^sub>l t\<^sub>2\<^sub>r where V: "(\<Gamma> \<turnstile> f\<^sub>l : t\<^sub>1\<^sub>l \<rightarrow> t\<^sub>2\<^sub>l) \<and> (\<Gamma> \<turnstile> f\<^sub>r : t\<^sub>1\<^sub>r \<rightarrow> t\<^sub>2\<^sub>r) \<and> 
      (\<Gamma> \<turnstile> v : t\<^sub>1\<^sub>r) \<and> t\<^sub>1 = t\<^sub>1\<^sub>l \<oplus> t\<^sub>1\<^sub>r \<and> t\<^sub>2 = t\<^sub>2\<^sub>l \<oplus> t\<^sub>2\<^sub>r" by fastforce
    hence "\<Gamma> \<turnstile> \<iota>\<^sub>r \<cdot> f\<^sub>r : t\<^sub>1\<^sub>r \<rightarrow> t\<^sub>2\<^sub>l \<oplus> t\<^sub>2\<^sub>r" by (metis tc_inr tc_comp)
    with V show ?case by fastforce
  next case (ev_dstl \<Lambda> v\<^sub>1 v\<^sub>2)
    then obtain t\<^sub>3 t\<^sub>4 t\<^sub>5 where "(\<Gamma> \<turnstile> v\<^sub>1 : t\<^sub>3) \<and> (\<Gamma> \<turnstile> v\<^sub>2 : t\<^sub>5) \<and> t\<^sub>1 = (t\<^sub>3 \<oplus> t\<^sub>4) \<otimes> t\<^sub>5 \<and> 
      t\<^sub>2 = t\<^sub>3 \<otimes> t\<^sub>5 \<oplus> t\<^sub>4 \<otimes> t\<^sub>5" by fastforce
    hence "(\<Gamma> \<turnstile> \<epsilon> : t\<^sub>2 \<rightarrow> t\<^sub>2) \<and> \<Gamma> \<turnstile> InlV (PairV v\<^sub>1 v\<^sub>2) : t\<^sub>2" by simp
    thus ?case by fastforce
  next case (ev_dstr \<Lambda> v\<^sub>1 v\<^sub>2)
    then obtain t\<^sub>3 t\<^sub>4 t\<^sub>5 where "(\<Gamma> \<turnstile> v\<^sub>1 : t\<^sub>4) \<and> (\<Gamma> \<turnstile> v\<^sub>2 : t\<^sub>5) \<and> t\<^sub>1 = (t\<^sub>3 \<oplus> t\<^sub>4) \<otimes> t\<^sub>5 \<and> 
      t\<^sub>2 = t\<^sub>3 \<otimes> t\<^sub>5 \<oplus> t\<^sub>4 \<otimes> t\<^sub>5" by fastforce
    hence "(\<Gamma> \<turnstile> \<epsilon> : t\<^sub>2 \<rightarrow> t\<^sub>2) \<and> \<Gamma> \<turnstile> InrV (PairV v\<^sub>1 v\<^sub>2) : t\<^sub>2" by simp
    thus ?case by fastforce
  next case (ev_arr \<Lambda> g f e)
    then obtain t\<^sub>1\<^sub>1 t\<^sub>1\<^sub>2 t\<^sub>2\<^sub>1 t\<^sub>2\<^sub>2 where "(\<Gamma> \<turnstile> f : t\<^sub>2\<^sub>1 \<rightarrow> t\<^sub>1\<^sub>1) \<and> (\<Gamma> \<turnstile> g : t\<^sub>1\<^sub>2 \<rightarrow> t\<^sub>2\<^sub>2) \<and> 
      (\<Gamma> \<turnstile> e : t\<^sub>1\<^sub>1 \<rightarrow> t\<^sub>1\<^sub>2) \<and> t\<^sub>1 = t\<^sub>1\<^sub>1 \<hookrightarrow> t\<^sub>1\<^sub>2 \<and> t\<^sub>2 = t\<^sub>2\<^sub>1 \<hookrightarrow> t\<^sub>2\<^sub>2" by fastforce
    hence "(\<Gamma> \<turnstile> \<epsilon> : t\<^sub>2\<^sub>1 \<hookrightarrow> t\<^sub>2\<^sub>2 \<rightarrow> t\<^sub>2) \<and> \<Gamma> \<turnstile> FunV (g \<cdot> e \<cdot> f) : t\<^sub>2\<^sub>1 \<hookrightarrow> t\<^sub>2\<^sub>2" by fastforce
    thus ?case by fastforce
  next case (ev_inj \<Lambda> F v)
    hence "(\<Gamma> \<turnstile> \<epsilon> : t\<^sub>2 \<rightarrow> t\<^sub>2) \<and> \<Gamma> \<turnstile> InjV F v : t\<^sub>2" by fastforce
    thus ?case by fastforce
  next case (ev_cata \<Lambda> f F v)
    hence V: "(\<Gamma> \<turnstile> f : t\<^sub>2 \<star> F \<rightarrow> t\<^sub>2) \<and> \<Gamma> \<turnstile> v : \<mu> F" by fastforce
    moreover from ev_cata have "\<Gamma> \<turnstile> \<lparr> f \<rparr>\<^bsub>F\<^esub> \<bullet> F : \<mu> F \<star> F \<rightarrow> t\<^sub>2 \<star> F" by fastforce
    moreover have "\<Gamma> \<turnstile> \<prec>\<^bsub>F\<^esub> : \<mu> F \<rightarrow> \<mu> F \<star> F" by simp
    ultimately have "\<Gamma> \<turnstile> f \<cdot> \<lparr> f \<rparr>\<^bsub>F\<^esub> \<bullet> F \<cdot> \<prec>\<^bsub>F\<^esub> : \<mu> F \<rightarrow> t\<^sub>2" by (metis tc_comp)
    with V have "(\<Gamma> \<turnstile> f \<cdot> \<lparr> f \<rparr>\<^bsub>F\<^esub> \<bullet> F \<cdot> \<prec>\<^bsub>F\<^esub> : \<mu> F \<rightarrow> t\<^sub>2) \<and> \<Gamma> \<turnstile> v : \<mu> F" by simp
    thus ?case by fastforce
  next case (ev_ana \<Lambda> f F v)
    hence V: "(\<Gamma> \<turnstile> f : t\<^sub>1 \<rightarrow> t\<^sub>1 \<star> F) \<and> (\<Gamma> \<turnstile> v : t\<^sub>1) \<and> t\<^sub>2 = \<mu> F" by fastforce
    hence "\<Gamma> \<turnstile> \<succ>\<^bsub>F\<^esub> : t\<^sub>2 \<star> F \<rightarrow> t\<^sub>2" by simp
    moreover from ev_ana have "\<Gamma> \<turnstile> \<lbrakk> f \<rbrakk>\<^bsub>F\<^esub> \<bullet> F : t\<^sub>1 \<star> F \<rightarrow> t\<^sub>2 \<star> F" by simp
    moreover from V have "\<Gamma> \<turnstile> f : t\<^sub>1 \<rightarrow> t\<^sub>1 \<star> F" by simp
    ultimately have "\<Gamma> \<turnstile> \<succ>\<^bsub>F\<^esub> \<cdot> \<lbrakk> f \<rbrakk>\<^bsub>F\<^esub> \<bullet> F \<cdot> f : t\<^sub>1 \<rightarrow> t\<^sub>2" by simp
    with V show ?case by fastforce
  next case (ev_var \<Lambda> x e v)
    hence "\<Gamma> x = Some (t\<^sub>1, t\<^sub>2)" by fastforce
    with ev_var obtain e' where "\<Lambda> x = Some e' \<and> \<Gamma> \<turnstile> e' : t\<^sub>1 \<rightarrow> t\<^sub>2" by (metis typecheck_context_def)
    with ev_var show ?case by fastforce
  qed force+

lemma [simp]: "\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> x \<notin> dom \<Gamma> \<Longrightarrow> \<Gamma>(x \<mapsto> tt) \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2"
  and [simp]: "\<Gamma> \<turnstile> v : t \<Longrightarrow> x \<notin> dom \<Gamma> \<Longrightarrow> \<Gamma>(x \<mapsto> tt) \<turnstile> v : t"
  proof (induction \<Gamma> e t\<^sub>1 t\<^sub>2 and \<Gamma> v t rule: typecheck\<^sub>e_typecheck\<^sub>v.inducts) 
  case (tc_var \<Gamma> y t\<^sub>1 t\<^sub>2)
    moreover hence "x \<noteq> y" by auto
    ultimately show ?case by simp
  qed simp_all

(* big-step evaluation *) 

inductive total_eval :: "(name \<rightharpoonup> expr) \<Rightarrow> expr \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool" (infix "\<turnstile> _ \<cdot> _ \<Down>" 60) where
  tev_base [simp]: "\<Lambda> \<turnstile> \<epsilon> \<cdot> v \<Down> v"
| tev_step [simp]: "\<Lambda> \<turnstile> e \<cdot> v \<leadsto> e' \<cdot> v' \<Longrightarrow> \<Lambda> \<turnstile> e' \<cdot> v' \<Down> v'' \<Longrightarrow> \<Lambda> \<turnstile> e \<cdot> v \<Down> v''"

lemma [elim]: "\<Lambda> \<turnstile> f \<cdot> v \<Down> v' \<Longrightarrow> \<Lambda> \<turnstile> g \<cdot> v' \<Down> v'' \<Longrightarrow> \<Lambda> \<turnstile> (g \<cdot> f) \<cdot> v \<Down> v''"
  proof (induction \<Lambda> f v v' rule: total_eval.induct)
  case (tev_base \<Lambda> v)
    moreover have "\<Lambda> \<turnstile> (g \<cdot> \<epsilon>) \<cdot> v \<leadsto> g \<cdot> v" by simp
    ultimately show ?case by (metis tev_step)
  next case (tev_step \<Lambda> f v f' v' v''')
    hence "\<Lambda> \<turnstile> (g \<cdot> f) \<cdot> v \<leadsto> (g \<cdot> f') \<cdot> v'" by simp
    moreover from tev_step have "\<Lambda> \<turnstile> (g \<cdot> f') \<cdot> v' \<Down> v''" by simp
    ultimately show ?case by (metis total_eval.tev_step)
  qed

lemma [simp]: "\<Lambda> \<turnstile> e \<cdot> v \<leadsto> \<epsilon> \<cdot> v' \<Longrightarrow> \<Lambda> \<turnstile> e \<cdot> v \<Down> v'"
  by rule (simp, simp)

lemma eps_big_eval [elim]: "\<Lambda> \<turnstile> \<epsilon> \<cdot> v \<Down> v' \<Longrightarrow> v = v'"
  proof (induction \<Lambda> \<epsilon> v v' rule: total_eval.induct)
  case (tev_step \<Lambda> v e' v' v'')
    thus ?case by (induction \<epsilon> v e' v' rule: evaluate.induct)
  qed simp_all

lemma [simp]: "\<Lambda> \<turnstile> f\<^sub>2 \<cdot> v\<^sub>2 \<Down> v\<^sub>4 \<Longrightarrow> \<Lambda> \<turnstile> \<epsilon> \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<Down> PairV v\<^sub>1 v\<^sub>4"
  proof (induction \<Lambda> f\<^sub>2 v\<^sub>2 v\<^sub>4 rule: total_eval.induct)
  case (tev_step \<Lambda> f\<^sub>2 v\<^sub>2 f\<^sub>2' v\<^sub>2' v\<^sub>4)
    hence "\<Lambda> \<turnstile> \<epsilon> \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> \<epsilon> \<parallel> f\<^sub>2' \<cdot> PairV v\<^sub>1 v\<^sub>2'" by simp
    moreover from tev_step have "\<Lambda> \<turnstile> \<epsilon> \<parallel> f\<^sub>2' \<cdot> PairV v\<^sub>1 v\<^sub>2' \<Down> PairV v\<^sub>1 v\<^sub>4" by simp
    ultimately show ?case by simp
  qed simp_all

lemma [simp]: "\<Lambda> \<turnstile> f\<^sub>1 \<cdot> v\<^sub>1 \<Down> v\<^sub>3 \<Longrightarrow> \<Lambda> \<turnstile> f\<^sub>2 \<cdot> v\<^sub>2 \<Down> v\<^sub>4 \<Longrightarrow> \<Lambda> \<turnstile> f\<^sub>1 \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<Down> PairV v\<^sub>3 v\<^sub>4"
  proof (induction \<Lambda> f\<^sub>1 v\<^sub>1 v\<^sub>3 rule: total_eval.induct)
  case (tev_step \<Lambda> f\<^sub>1 v\<^sub>1 f\<^sub>1' v\<^sub>1' v\<^sub>3)
    hence "\<Lambda> \<turnstile> f\<^sub>1 \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> f\<^sub>1' \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1' v\<^sub>2" by simp
    moreover from tev_step have "\<Lambda> \<turnstile> f\<^sub>1' \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1' v\<^sub>2 \<Down> PairV v\<^sub>3 v\<^sub>4" by simp
    ultimately show ?case by simp
  qed simp_all

lemma pair_big_eval [elim]: "\<Lambda> \<turnstile> f\<^sub>1 \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<Down> PairV v\<^sub>3 v\<^sub>4 \<Longrightarrow> 
    (\<Lambda> \<turnstile> f\<^sub>1 \<cdot> v\<^sub>1 \<Down> v\<^sub>3) \<and> \<Lambda> \<turnstile> f\<^sub>2 \<cdot> v\<^sub>2 \<Down> v\<^sub>4"
  proof (induction \<Lambda> "f\<^sub>1 \<parallel> f\<^sub>2" "PairV v\<^sub>1 v\<^sub>2" "PairV v\<^sub>3 v\<^sub>4" 
         arbitrary: f\<^sub>1 f\<^sub>2 v\<^sub>1 v\<^sub>2 rule: total_eval.induct)
  case (tev_step \<Lambda> e' v')
    thus ?case
      proof (induction \<Lambda> "f\<^sub>1 \<parallel> f\<^sub>2" "PairV v\<^sub>1 v\<^sub>2" e' v' arbitrary: f\<^sub>1 f\<^sub>2 v\<^sub>1 v\<^sub>2 rule: evaluate.induct)
      case (ev_pair3 \<Lambda> v\<^sub>1 v\<^sub>2)
        hence "PairV v\<^sub>1 v\<^sub>2 = PairV v\<^sub>3 v\<^sub>4" by (metis eps_big_eval)
        thus ?case by simp
      qed simp_all
  qed

lemma [simp]: "\<Lambda> \<turnstile> f\<^sub>l \<cdot> v \<Down> v' \<Longrightarrow> \<Lambda> \<turnstile> f\<^sub>l \<bar> f\<^sub>r \<cdot> InlV v \<Down> InlV v'"
  proof
    show "\<Lambda> \<turnstile> f\<^sub>l \<bar> f\<^sub>r \<cdot> InlV v \<leadsto> (\<iota>\<^sub>l \<cdot> f\<^sub>l) \<cdot> v" by simp
    show "\<Lambda> \<turnstile> f\<^sub>l \<cdot> v \<Down> v' \<Longrightarrow> \<Lambda> \<turnstile> (\<iota>\<^sub>l \<cdot> f\<^sub>l) \<cdot> v \<Down> InlV v'" by auto
  qed

lemma [simp]: "\<Lambda> \<turnstile> f\<^sub>r \<cdot> v \<Down> v' \<Longrightarrow> \<Lambda> \<turnstile> f\<^sub>l \<bar> f\<^sub>r \<cdot> InrV v \<Down> InrV v'"
  proof
    show "\<Lambda> \<turnstile> f\<^sub>l \<bar> f\<^sub>r \<cdot> InrV v \<leadsto> (\<iota>\<^sub>r \<cdot> f\<^sub>r) \<cdot> v" by simp
    show "\<Lambda> \<turnstile> f\<^sub>r \<cdot> v \<Down> v' \<Longrightarrow> \<Lambda> \<turnstile> (\<iota>\<^sub>r \<cdot> f\<^sub>r) \<cdot> v \<Down> InrV v'" by auto
  qed

(* since we are a turing-complete language, total progress is not provable *)

theorem total_preservation [simp]: "\<Lambda> \<turnstile> e \<cdot> v \<Down> v' \<Longrightarrow> \<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> v : t\<^sub>1 \<Longrightarrow> \<Gamma> \<tturnstile> \<Lambda> \<Longrightarrow> 
    \<Gamma> \<turnstile> v' : t\<^sub>2"
  proof (induction \<Lambda> e v v' arbitrary: t\<^sub>1 rule: total_eval.induct)
  case (tev_step \<Lambda> e v e' v' v'')
    moreover then obtain t\<^sub>3 where "(\<Gamma> \<turnstile> e' : t\<^sub>3 \<rightarrow> t\<^sub>2) \<and> (\<Gamma> \<turnstile> v' : t\<^sub>3)" by (metis preservation)
    ultimately show ?case by fastforce
  qed auto

end
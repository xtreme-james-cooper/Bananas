theory BananasExpression
imports Main
begin

type_synonym name = string

datatype type = 
  Void ("\<zero>")
| Unit ("\<one>")
| Poly nat
| Named name
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
| Inj name ("\<succ>\<^bsub>_\<^esub>") | Outj name ("\<prec>\<^bsub>_\<^esub>")
| Cata expr name ("\<lparr> _ \<rparr>\<^bsub>_\<^esub>") | Ana expr name ("\<lbrakk> _ \<rbrakk>\<^bsub>_\<^esub>")
| Var name
and val = 
  UnitV
| PairV val val 
| InlV val | InrV val
| FunV expr
| InjV name val 

(* typechecking *)

fun apply_functor_type :: "type \<Rightarrow> funct \<Rightarrow> type" (infixl "\<star>" 75) where
  "t \<star> Id = t"
| "t \<star> K t' = t'"
| "t \<star> f\<^sub>1 \<Otimes> f\<^sub>2 = (t \<star> f\<^sub>1) \<otimes> (t \<star> f\<^sub>2)"
| "t \<star> f\<^sub>1 \<Oplus> f\<^sub>2 = (t \<star> f\<^sub>1) \<oplus> (t \<star> f\<^sub>2)"

inductive typecheck\<^sub>e :: "(name \<rightharpoonup> type \<times> type) \<Rightarrow> (name \<rightharpoonup> funct) \<Rightarrow> expr \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" 
    (infix "& _ \<turnstile> _ : _ \<rightarrow>" 60)
      and typecheck\<^sub>v :: "(name \<rightharpoonup> type \<times> type) \<Rightarrow> (name \<rightharpoonup> funct) \<Rightarrow> val \<Rightarrow> type \<Rightarrow> bool" 
    (infix "& _ \<turnstile> _ :" 60) where
  tc_id [simp]: "\<Gamma> & \<Sigma> \<turnstile> \<epsilon> : t \<rightarrow> t"
| tc_con [simp]: "\<Gamma> & \<Sigma> \<turnstile> v : t\<^sub>2 \<Longrightarrow> \<Gamma> & \<Sigma> \<turnstile> \<kappa> v : t\<^sub>1 \<rightarrow> t\<^sub>2"
| tc_comp [simp]: "\<Gamma> & \<Sigma> \<turnstile> f : t\<^sub>2 \<rightarrow> t\<^sub>3 \<Longrightarrow> \<Gamma> & \<Sigma> \<turnstile> g : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> & \<Sigma> \<turnstile> f \<cdot> g : t\<^sub>1 \<rightarrow> t\<^sub>3"
| tc_fst [simp]: "\<Gamma> & \<Sigma> \<turnstile> \<pi>\<^sub>1 : t\<^sub>1 \<otimes> t\<^sub>2 \<rightarrow> t\<^sub>1"
| tc_snd [simp]: "\<Gamma> & \<Sigma> \<turnstile> \<pi>\<^sub>2 : t\<^sub>1 \<otimes> t\<^sub>2 \<rightarrow> t\<^sub>2"
| tc_tup [simp]: "\<Gamma> & \<Sigma> \<turnstile> \<Theta> : t \<rightarrow> t \<otimes> t"
| tc_pair [simp]: "\<Gamma> & \<Sigma> \<turnstile> f\<^sub>1 : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> & \<Sigma> \<turnstile> f\<^sub>2 : t\<^sub>3 \<rightarrow> t\<^sub>4 \<Longrightarrow> 
    \<Gamma> & \<Sigma> \<turnstile> f\<^sub>1 \<parallel> f\<^sub>2 : t\<^sub>1 \<otimes> t\<^sub>3 \<rightarrow> t\<^sub>2 \<otimes> t\<^sub>4"
| tc_inl [simp]: "\<Gamma> & \<Sigma> \<turnstile> \<iota>\<^sub>l : t\<^sub>1 \<rightarrow> t\<^sub>1 \<oplus> t\<^sub>2"
| tc_inr [simp]: "\<Gamma> & \<Sigma> \<turnstile> \<iota>\<^sub>r : t\<^sub>2 \<rightarrow> t\<^sub>1 \<oplus> t\<^sub>2"
| tc_str [simp]: "\<Gamma> & \<Sigma> \<turnstile> \<Xi> : t\<^sub>1 \<oplus> t\<^sub>1 \<rightarrow> t\<^sub>1"
| tc_case [simp]: "\<Gamma> & \<Sigma> \<turnstile> f\<^sub>l : t\<^sub>1 \<rightarrow> t\<^sub>3 \<Longrightarrow> \<Gamma> & \<Sigma> \<turnstile> f\<^sub>r : t\<^sub>2 \<rightarrow> t\<^sub>4 \<Longrightarrow> 
    \<Gamma> & \<Sigma> \<turnstile> f\<^sub>l \<bar> f\<^sub>r : t\<^sub>1 \<oplus> t\<^sub>2 \<rightarrow> t\<^sub>3 \<oplus> t\<^sub>4"
| tc_dst [simp]: "\<Gamma> & \<Sigma> \<turnstile> \<rhd> : (t\<^sub>1 \<oplus> t\<^sub>2) \<otimes> t\<^sub>3 \<rightarrow> t\<^sub>1 \<otimes> t\<^sub>3 \<oplus> t\<^sub>2 \<otimes> t\<^sub>3"
| tc_app [simp]: "\<Gamma> & \<Sigma> \<turnstile> $ : (t\<^sub>1 \<hookrightarrow> t\<^sub>2) \<otimes> t\<^sub>1 \<rightarrow> t\<^sub>2"
| tc_arr [simp]: "\<Gamma> & \<Sigma> \<turnstile> f : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> & \<Sigma> \<turnstile> g : t\<^sub>3 \<rightarrow> t\<^sub>4 \<Longrightarrow> 
    \<Gamma> & \<Sigma> \<turnstile> g \<leftarrow> f : t\<^sub>2 \<hookrightarrow> t\<^sub>3 \<rightarrow> t\<^sub>1 \<hookrightarrow> t\<^sub>4"
| tc_inj [simp]: "\<Sigma> n = Some F \<Longrightarrow> \<Gamma> & \<Sigma> \<turnstile> \<succ>\<^bsub>n\<^esub> : \<mu> F \<star> F \<rightarrow> \<mu> F"
| tc_outj [simp]: "\<Sigma> n = Some F \<Longrightarrow> \<Gamma> & \<Sigma> \<turnstile> \<prec>\<^bsub>n\<^esub> : \<mu> F \<rightarrow> \<mu> F \<star> F"
| tc_cata [simp]: "\<Sigma> n = Some F \<Longrightarrow> \<Gamma> & \<Sigma> \<turnstile> f : t \<star> F \<rightarrow> t \<Longrightarrow> \<Gamma> & \<Sigma> \<turnstile> \<lparr> f \<rparr>\<^bsub>n\<^esub> : \<mu> F \<rightarrow> t"
| tc_ana [simp]: "\<Sigma> n = Some F \<Longrightarrow> \<Gamma> & \<Sigma> \<turnstile> f : t \<rightarrow> t \<star> F \<Longrightarrow> \<Gamma> & \<Sigma> \<turnstile> \<lbrakk> f \<rbrakk>\<^bsub>n\<^esub> : t \<rightarrow> \<mu> F"
| tc_var [simp]: "\<Gamma> x = Some (t\<^sub>1, t\<^sub>2) \<Longrightarrow> \<Gamma> & \<Sigma> \<turnstile> Var x : t\<^sub>1 \<rightarrow> t\<^sub>2"

| tcv_unit [simp]: "\<Gamma> & \<Sigma> \<turnstile> UnitV : \<one>"
| tcv_pair [simp]: "\<Gamma> & \<Sigma> \<turnstile> v\<^sub>1 : t\<^sub>1 \<Longrightarrow> \<Gamma> & \<Sigma> \<turnstile> v\<^sub>2 : t\<^sub>2 \<Longrightarrow> \<Gamma> & \<Sigma> \<turnstile> PairV v\<^sub>1 v\<^sub>2 : t\<^sub>1 \<otimes> t\<^sub>2"
| tcv_inl [simp]: "\<Gamma> & \<Sigma> \<turnstile> v : t\<^sub>1 \<Longrightarrow> \<Gamma> & \<Sigma> \<turnstile> InlV v : t\<^sub>1 \<oplus> t\<^sub>2"
| tcv_inr [simp]: "\<Gamma> & \<Sigma> \<turnstile> v : t\<^sub>2 \<Longrightarrow> \<Gamma> & \<Sigma> \<turnstile> InrV v : t\<^sub>1 \<oplus> t\<^sub>2"
| tcv_fun [simp]: "\<Gamma> & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> & \<Sigma> \<turnstile> FunV e : t\<^sub>1 \<hookrightarrow> t\<^sub>2"
| tcv_inj [simp]: "\<Sigma> n = Some F \<Longrightarrow> \<Gamma> & \<Sigma> \<turnstile> v : \<mu> F \<star> F \<Longrightarrow> \<Gamma> & \<Sigma> \<turnstile> InjV n v : \<mu> F"

inductive_cases [elim]: "\<Gamma> & \<Sigma> \<turnstile> \<epsilon> : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> & \<Sigma> \<turnstile> \<kappa> v : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> & \<Sigma> \<turnstile> f \<cdot> g : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> & \<Sigma> \<turnstile> \<pi>\<^sub>1 : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> & \<Sigma> \<turnstile> \<pi>\<^sub>2 : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> & \<Sigma> \<turnstile> \<Theta> : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> & \<Sigma> \<turnstile> f\<^sub>l \<parallel> f\<^sub>r : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> & \<Sigma> \<turnstile> \<iota>\<^sub>l : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> & \<Sigma> \<turnstile> \<iota>\<^sub>r : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> & \<Sigma> \<turnstile> \<Xi> : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> & \<Sigma> \<turnstile> f\<^sub>l \<bar> f\<^sub>r : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> & \<Sigma> \<turnstile> \<rhd> : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> & \<Sigma> \<turnstile> $ : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> & \<Sigma> \<turnstile> g \<leftarrow> f : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> & \<Sigma> \<turnstile> \<prec>\<^bsub>F\<^esub> : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> & \<Sigma> \<turnstile> \<succ>\<^bsub>F\<^esub> : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> & \<Sigma> \<turnstile> \<lparr> f \<rparr>\<^bsub>F\<^esub> : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> & \<Sigma> \<turnstile> \<lbrakk> f \<rbrakk>\<^bsub>F\<^esub> : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> & \<Sigma> \<turnstile> Var x : t \<rightarrow> t'"

inductive_cases [elim]: "\<Gamma> & \<Sigma> \<turnstile> UnitV : t"
inductive_cases [elim]: "\<Gamma> & \<Sigma> \<turnstile> PairV v\<^sub>1 v\<^sub>2 : t"
inductive_cases [elim]: "\<Gamma> & \<Sigma> \<turnstile> InrV v : t"
inductive_cases [elim]: "\<Gamma> & \<Sigma> \<turnstile> InlV v : t"
inductive_cases [elim]: "\<Gamma> & \<Sigma> \<turnstile> FunV e : t"
inductive_cases [elim]: "\<Gamma> & \<Sigma> \<turnstile> InjV f v : t"

definition typecheck_context :: "(name \<rightharpoonup> type \<times> type) \<Rightarrow> (name \<rightharpoonup> funct) \<Rightarrow> (name \<rightharpoonup> expr) \<Rightarrow> bool" 
    (infix "& _ \<tturnstile>" 60) where
  "(\<Gamma> & \<Sigma> \<tturnstile> \<Lambda>) = (\<forall>x t\<^sub>1 t\<^sub>2. \<Gamma> x = Some (t\<^sub>1, t\<^sub>2) \<longrightarrow> (\<exists>e. \<Lambda> x = Some e \<and> \<Gamma> & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2))"

(* evaluation *)

fun apply_functor_expr :: "expr \<Rightarrow> funct \<Rightarrow> expr" (infixl "\<bullet>" 75) where
  "e \<bullet> Id = e"
| "e \<bullet> K t = \<epsilon>"
| "e \<bullet> f\<^sub>1 \<Otimes> f\<^sub>2 = (e \<bullet> f\<^sub>1) \<parallel> (e \<bullet> f\<^sub>2)"
| "e \<bullet> f\<^sub>1 \<Oplus> f\<^sub>2 = (e \<bullet> f\<^sub>1) \<bar> (e \<bullet> f\<^sub>2)"

inductive evaluate :: "(name \<rightharpoonup> expr) \<Rightarrow> (name \<rightharpoonup> funct) \<Rightarrow> expr \<Rightarrow> val \<Rightarrow> expr \<Rightarrow> val \<Rightarrow> bool" 
    (infix "& _ \<turnstile> _ \<cdot> _ \<leadsto> _ \<cdot>" 60) where
  ev_con [simp]: "\<Lambda> & \<Sigma> \<turnstile> \<kappa> v\<^sub>1 \<cdot> v\<^sub>2 \<leadsto> \<epsilon> \<cdot> v\<^sub>1"
| ev_comp1 [simp]: "\<Lambda> & \<Sigma> \<turnstile> g \<cdot> v \<leadsto> g' \<cdot> v' \<Longrightarrow> \<Lambda> & \<Sigma> \<turnstile> (f \<cdot> g) \<cdot> v \<leadsto> (f \<cdot> g') \<cdot> v'"
| ev_comp2 [simp]: "\<Lambda> & \<Sigma> \<turnstile> (f \<cdot> \<epsilon>) \<cdot> v \<leadsto> f \<cdot> v"
| ev_fst [simp]: "\<Lambda> & \<Sigma> \<turnstile> \<pi>\<^sub>1 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> \<epsilon> \<cdot> v\<^sub>1"
| ev_snd [simp]: "\<Lambda> & \<Sigma> \<turnstile> \<pi>\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> \<epsilon> \<cdot> v\<^sub>2"
| ev_pair1 [simp]: "\<Lambda> & \<Sigma> \<turnstile> f\<^sub>1 \<cdot> v\<^sub>1 \<leadsto> f\<^sub>1' \<cdot> v\<^sub>1' \<Longrightarrow> 
    \<Lambda> & \<Sigma> \<turnstile> f\<^sub>1 \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> f\<^sub>1' \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1' v\<^sub>2"
| ev_pair2 [simp]: "\<Lambda> & \<Sigma> \<turnstile> f\<^sub>2 \<cdot> v\<^sub>2 \<leadsto> f\<^sub>2' \<cdot> v\<^sub>2' \<Longrightarrow> 
    \<Lambda> & \<Sigma> \<turnstile> \<epsilon> \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> \<epsilon> \<parallel> f\<^sub>2' \<cdot> PairV v\<^sub>1 v\<^sub>2'"
| ev_pair3 [simp]: "\<Lambda> & \<Sigma> \<turnstile> \<epsilon> \<parallel> \<epsilon> \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> \<epsilon> \<cdot> PairV v\<^sub>1 v\<^sub>2"
| ev_tup [simp]: "\<Lambda> & \<Sigma> \<turnstile> \<Theta> \<cdot> v \<leadsto> \<epsilon> \<cdot> PairV v v"
| ev_inl [simp]: "\<Lambda> & \<Sigma> \<turnstile> \<iota>\<^sub>l \<cdot> v \<leadsto> \<epsilon> \<cdot> InlV v"
| ev_inr [simp]: "\<Lambda> & \<Sigma> \<turnstile> \<iota>\<^sub>r \<cdot> v \<leadsto> \<epsilon> \<cdot> InrV v"
| ev_strl [simp]: "\<Lambda> & \<Sigma> \<turnstile> \<Xi> \<cdot> InlV v \<leadsto> \<epsilon> \<cdot> v"
| ev_strr [simp]: "\<Lambda> & \<Sigma> \<turnstile> \<Xi> \<cdot> InrV v \<leadsto> \<epsilon> \<cdot> v"
| ev_csl [simp]: "\<Lambda> & \<Sigma> \<turnstile> f\<^sub>l \<bar> f\<^sub>r \<cdot> InlV v \<leadsto> (\<iota>\<^sub>l \<cdot> f\<^sub>l) \<cdot> v"
| ev_csr [simp]: "\<Lambda> & \<Sigma> \<turnstile> f\<^sub>l \<bar> f\<^sub>r \<cdot> InrV v \<leadsto> (\<iota>\<^sub>r \<cdot> f\<^sub>r) \<cdot> v"
| ev_dstl [simp]: "\<Lambda> & \<Sigma> \<turnstile> \<rhd> \<cdot> PairV (InlV v\<^sub>1) v\<^sub>2 \<leadsto> \<epsilon> \<cdot> InlV (PairV v\<^sub>1 v\<^sub>2)"
| ev_dstr [simp]: "\<Lambda> & \<Sigma> \<turnstile> \<rhd> \<cdot> PairV (InrV v\<^sub>1) v\<^sub>2 \<leadsto> \<epsilon> \<cdot> InrV (PairV v\<^sub>1 v\<^sub>2)"
| ev_app [simp]: "\<Lambda> & \<Sigma> \<turnstile> $ \<cdot> PairV (FunV e) v \<leadsto> e \<cdot> v"
| ev_arr [simp]: "\<Lambda> & \<Sigma> \<turnstile> g \<leftarrow> f \<cdot> FunV e \<leadsto> \<epsilon> \<cdot> FunV (g \<cdot> e \<cdot> f)"
| ev_inj [simp]: "\<Lambda> & \<Sigma> \<turnstile> \<succ>\<^bsub>n\<^esub> \<cdot> v \<leadsto> \<epsilon> \<cdot> InjV n v"
(* Should have n = m, but makes progress harder. Also, typechecking guarantees it.  *)
| ev_outj [simp]: "\<Lambda> & \<Sigma> \<turnstile> \<prec>\<^bsub>n\<^esub> \<cdot> InjV m v \<leadsto> \<epsilon> \<cdot> v" 
| ev_cata [simp]: "\<Sigma> n = Some F \<Longrightarrow> \<Lambda> & \<Sigma> \<turnstile> \<lparr> f \<rparr>\<^bsub>n\<^esub> \<cdot> v \<leadsto> (f \<cdot> \<lparr> f \<rparr>\<^bsub>n\<^esub> \<bullet> F \<cdot> \<prec>\<^bsub>n\<^esub>) \<cdot> v"
| ev_ana [simp]: "\<Sigma> n = Some F \<Longrightarrow> \<Lambda> & \<Sigma> \<turnstile> \<lbrakk> f \<rbrakk>\<^bsub>n\<^esub> \<cdot> v \<leadsto> (\<succ>\<^bsub>n\<^esub> \<cdot> \<lbrakk> f \<rbrakk>\<^bsub>n\<^esub> \<bullet> F \<cdot> f) \<cdot> v"
| ev_var [simp]: "\<Lambda> x = Some e \<Longrightarrow> \<Lambda> & \<Sigma> \<turnstile> Var x \<cdot> v \<leadsto> e \<cdot> v"

(* safety *)

lemma canonical_unit: "\<Gamma> & \<Sigma> \<turnstile> v : \<one> \<Longrightarrow> v = UnitV"
  by (cases \<Gamma> \<Sigma> v \<one> rule: typecheck\<^sub>v.cases) simp_all

lemma canonical_prod: "\<Gamma> & \<Sigma> \<turnstile> v : t\<^sub>1 \<otimes> t\<^sub>2 \<Longrightarrow> 
    \<exists>v\<^sub>1 v\<^sub>2. (\<Gamma> & \<Sigma> \<turnstile> v\<^sub>1 : t\<^sub>1) \<and> (\<Gamma> & \<Sigma> \<turnstile> v\<^sub>2 : t\<^sub>2) \<and> v = PairV v\<^sub>1 v\<^sub>2"
  by (cases \<Gamma> \<Sigma> v "t\<^sub>1 \<otimes> t\<^sub>2" rule: typecheck\<^sub>v.cases) simp_all

lemma canonical_sum: "\<Gamma> & \<Sigma> \<turnstile> v : t\<^sub>1 \<oplus> t\<^sub>2 \<Longrightarrow> 
    \<exists>v'. ((\<Gamma> & \<Sigma> \<turnstile> v' : t\<^sub>1) \<and> v = InlV v') \<or> ((\<Gamma> & \<Sigma> \<turnstile> v' : t\<^sub>2) \<and> v = InrV v')"
  by (cases \<Gamma> \<Sigma> v "t\<^sub>1 \<oplus> t\<^sub>2" rule: typecheck\<^sub>v.cases) simp_all

lemma canonical_arrow: "\<Gamma> & \<Sigma> \<turnstile> v : t\<^sub>1 \<hookrightarrow> t\<^sub>2 \<Longrightarrow> \<exists>e. (\<Gamma> & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2) \<and> v = FunV e"
  by (cases \<Gamma> \<Sigma> v "t\<^sub>1 \<hookrightarrow> t\<^sub>2" rule: typecheck\<^sub>v.cases) simp_all

lemma canonical_mu: "\<Gamma> & \<Sigma> \<turnstile> v : \<mu> F \<Longrightarrow> 
    \<exists>v' n. (\<Gamma> & \<Sigma> \<turnstile> v' : \<mu> F \<star> F) \<and> v = InjV n v' \<and> \<Sigma> n = Some F"
  by (cases \<Gamma> \<Sigma> v "\<mu> F" rule: typecheck\<^sub>v.cases) simp_all

theorem progress [simp]: "\<Gamma> & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> & \<Sigma> \<turnstile> v : t\<^sub>1 \<Longrightarrow> \<Gamma> & \<Sigma> \<tturnstile> \<Lambda> \<Longrightarrow> e \<noteq> \<epsilon> \<Longrightarrow> 
    \<exists>e' v'. \<Lambda> & \<Sigma> \<turnstile> e \<cdot> v \<leadsto> e' \<cdot> v'"
    and "\<Gamma> & \<Sigma> \<turnstile> v : t\<^sub>1 \<Longrightarrow> True"
  proof (induction \<Gamma> \<Sigma> e t\<^sub>1 t\<^sub>2 arbitrary: v rule: typecheck\<^sub>e_typecheck\<^sub>v.inducts)
  case (tc_con \<Gamma> \<Sigma> v\<^sub>2 t\<^sub>2 t\<^sub>1)
    have "\<Lambda> & \<Sigma> \<turnstile> \<kappa> v\<^sub>2 \<cdot> v \<leadsto> \<epsilon> \<cdot> v\<^sub>2" by simp
    thus ?case by fastforce
  next case (tc_comp \<Gamma> \<Sigma> f t\<^sub>2 t\<^sub>3 g)
    thus ?case
      proof (cases "g = \<epsilon>")
      case True
        hence "\<Lambda> & \<Sigma> \<turnstile> (f \<cdot> g) \<cdot> v \<leadsto> f \<cdot> v" by simp
        thus ?thesis by fastforce
      next case False
        with tc_comp obtain g' v' where "\<Lambda> & \<Sigma> \<turnstile> g \<cdot> v \<leadsto> g' \<cdot> v'" by blast
        with tc_comp have "\<Lambda> & \<Sigma> \<turnstile> (f \<cdot> g) \<cdot> v \<leadsto> (f \<cdot> g') \<cdot> v'" by simp
        thus ?thesis by fastforce
      qed
  next case (tc_fst \<Gamma> \<Sigma>)
    then obtain v\<^sub>1 v\<^sub>2 where "v = PairV v\<^sub>1 v\<^sub>2" using canonical_prod by blast
    hence "\<Lambda> & \<Sigma> \<turnstile> \<pi>\<^sub>1 \<cdot> v \<leadsto> \<epsilon> \<cdot> v\<^sub>1" by simp
    thus ?case by fastforce
  next case (tc_snd \<Gamma> \<Sigma>)
    then obtain v\<^sub>1 v\<^sub>2 where "v = PairV v\<^sub>1 v\<^sub>2" using canonical_prod by blast
    hence "\<Lambda> & \<Sigma> \<turnstile> \<pi>\<^sub>2 \<cdot> v \<leadsto> \<epsilon> \<cdot> v\<^sub>2" by simp
    thus ?case by fastforce
  next case (tc_tup \<Gamma> \<Sigma>)
    hence "\<Lambda> & \<Sigma> \<turnstile> \<Theta> \<cdot> v \<leadsto> \<epsilon> \<cdot> PairV v v" by simp
    thus ?case by fastforce
  next case (tc_pair \<Gamma> \<Sigma> f\<^sub>1 t\<^sub>1 t\<^sub>2 f\<^sub>2)
    then obtain v\<^sub>1 v\<^sub>2 where V: "v = PairV v\<^sub>1 v\<^sub>2" using canonical_prod by blast
    thus ?case
      proof (cases "f\<^sub>1 = \<epsilon>")
      case True note T = True
        thus ?thesis
          proof (cases "f\<^sub>2 = \<epsilon>")
          case True
            have "\<Lambda> & \<Sigma> \<turnstile> \<epsilon> \<parallel> \<epsilon> \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> \<epsilon> \<cdot> PairV v\<^sub>1 v\<^sub>2" by simp
            with T True V show ?thesis by fastforce
          next case False
            with tc_pair V obtain f\<^sub>2' v\<^sub>2' where "\<Lambda> & \<Sigma> \<turnstile> f\<^sub>2 \<cdot> v\<^sub>2 \<leadsto> f\<^sub>2' \<cdot> v\<^sub>2'" by blast
            hence "\<Lambda> & \<Sigma> \<turnstile> \<epsilon> \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> \<epsilon> \<parallel> f\<^sub>2' \<cdot> PairV v\<^sub>1 v\<^sub>2'" by simp
            with True V show ?thesis by fastforce
          qed
      next case False
        with tc_pair V obtain f\<^sub>1' v\<^sub>1' where "\<Lambda> & \<Sigma> \<turnstile> f\<^sub>1 \<cdot> v\<^sub>1 \<leadsto> f\<^sub>1' \<cdot> v\<^sub>1'" by blast    
        hence "\<Lambda> & \<Sigma> \<turnstile> f\<^sub>1 \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> f\<^sub>1' \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1' v\<^sub>2" by simp
        with V show ?thesis by fastforce
      qed
  next case (tc_inl \<Gamma> \<Sigma>)
    hence "\<Lambda> & \<Sigma> \<turnstile> \<iota>\<^sub>l \<cdot> v \<leadsto> \<epsilon> \<cdot> InlV v" by simp
    thus ?case by fastforce
  next case (tc_inr \<Gamma> \<Sigma>)
    hence "\<Lambda> & \<Sigma> \<turnstile> \<iota>\<^sub>r \<cdot> v \<leadsto> \<epsilon> \<cdot> InrV v" by simp
    thus ?case by fastforce
  next case (tc_str \<Gamma> \<Sigma>)
    then obtain v' where V: "v = InlV v' \<or> v = InrV v'" using canonical_sum by blast
    thus ?case
      proof (cases "v = InlV v'")
      case True
        hence "\<Lambda> & \<Sigma> \<turnstile> \<Xi> \<cdot> v \<leadsto> \<epsilon> \<cdot> v'" by simp
        thus ?thesis by fastforce
      next case False
        with V have "\<Lambda> & \<Sigma> \<turnstile> \<Xi> \<cdot> v \<leadsto> \<epsilon> \<cdot> v'" by simp
        thus ?thesis by fastforce
      qed
  next case (tc_case \<Gamma> \<Sigma> f\<^sub>l t\<^sub>1 t\<^sub>3 f\<^sub>r)
    then obtain v' where V: "v = InlV v' \<or> v = InrV v'" using canonical_sum by blast
    thus ?case
      proof (cases "v = InlV v'")
      case True
        hence "\<Lambda> & \<Sigma> \<turnstile> f\<^sub>l \<bar> f\<^sub>r \<cdot> v \<leadsto> (\<iota>\<^sub>l \<cdot> f\<^sub>l) \<cdot> v'" by simp
        thus ?thesis by fastforce
      next case False
        with V have "\<Lambda> & \<Sigma> \<turnstile> f\<^sub>l \<bar> f\<^sub>r \<cdot> v \<leadsto> (\<iota>\<^sub>r \<cdot> f\<^sub>r) \<cdot> v'" by simp
        thus ?thesis by fastforce
      qed
  next case (tc_dst \<Gamma> \<Sigma>)
    then obtain v\<^sub>1 v\<^sub>2 where V: "v = PairV (InlV v\<^sub>1) v\<^sub>2 \<or> v = PairV (InrV v\<^sub>1) v\<^sub>2" 
      using canonical_prod canonical_sum by blast
    thus ?case
      proof (cases "v = PairV (InlV v\<^sub>1) v\<^sub>2")
      case True
        hence "\<Lambda> & \<Sigma> \<turnstile> \<rhd> \<cdot> v \<leadsto> \<epsilon> \<cdot> InlV (PairV v\<^sub>1 v\<^sub>2)" by simp
        thus ?thesis by fastforce
      next case False
        with V have "\<Lambda> & \<Sigma> \<turnstile> \<rhd> \<cdot> v \<leadsto> \<epsilon> \<cdot> InrV (PairV v\<^sub>1 v\<^sub>2)" by simp
        thus ?thesis by fastforce
      qed
  next case (tc_app \<Gamma> \<Sigma>)
    then obtain e v' where V: "v = PairV (FunV e) v'" using canonical_prod canonical_arrow by blast
    moreover hence "\<Lambda> & \<Sigma> \<turnstile> $ \<cdot> v \<leadsto> e \<cdot> v'" by simp
    ultimately show ?case by fastforce
  next case (tc_arr \<Gamma> \<Sigma> f t\<^sub>1 t\<^sub>2 g)
    then obtain e where "v = FunV e" using canonical_arrow by blast
    moreover hence "\<Lambda> & \<Sigma> \<turnstile> g \<leftarrow> f \<cdot> FunV e \<leadsto> \<epsilon> \<cdot> FunV (g \<cdot> e \<cdot> f)" by simp
    ultimately show ?case by fastforce
  next case (tc_inj \<Sigma> n)
    hence "\<Lambda> & \<Sigma> \<turnstile> \<succ>\<^bsub>n\<^esub> \<cdot> v \<leadsto> \<epsilon> \<cdot> InjV n v" by simp
    thus ?case by fastforce
  next case (tc_outj \<Sigma> n F \<Gamma>)
    then obtain v' m where "v = InjV m v' \<and> \<Sigma> m = Some F" using canonical_mu by blast
    moreover hence "\<Lambda> & \<Sigma> \<turnstile> \<prec>\<^bsub>n\<^esub> \<cdot> v \<leadsto> \<epsilon> \<cdot> v'" by simp
    ultimately show ?case by fastforce
  next case (tc_cata \<Sigma> n F \<Gamma> f)
    hence "\<Lambda> & \<Sigma> \<turnstile> \<lparr> f \<rparr>\<^bsub>n\<^esub> \<cdot> v \<leadsto> (f \<cdot> \<lparr> f \<rparr>\<^bsub>n\<^esub> \<bullet> F \<cdot> \<prec>\<^bsub>n\<^esub>) \<cdot> v" by simp
    thus ?case by fastforce
  next case (tc_ana \<Sigma> n F \<Gamma> f)
    hence "\<Lambda> & \<Sigma> \<turnstile> \<lbrakk> f \<rbrakk>\<^bsub>n\<^esub> \<cdot> v \<leadsto> (\<succ>\<^bsub>n\<^esub> \<cdot> \<lbrakk> f \<rbrakk>\<^bsub>n\<^esub> \<bullet> F \<cdot> f) \<cdot> v" by simp
    thus ?case by fastforce
  next case (tc_var \<Gamma> x t\<^sub>1 t\<^sub>2 \<Sigma>)
    then obtain e where "\<Lambda> x = Some e \<and> \<Gamma> & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2" by (metis typecheck_context_def)
    hence "\<Lambda> & \<Sigma> \<turnstile> Var x \<cdot> v \<leadsto> e \<cdot> v" by simp
    thus ?case by fastforce
  qed simp_all

lemma [simp]: "\<Gamma> & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> & \<Sigma> \<turnstile> e \<bullet> F : t\<^sub>1 \<star> F \<rightarrow> t\<^sub>2 \<star> F"
  by (induction e F rule: apply_functor_expr.induct) simp_all

theorem preservation [simp]: "\<Lambda> & \<Sigma> \<turnstile> e \<cdot> v \<leadsto> e' \<cdot> v' \<Longrightarrow> \<Gamma> & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> 
    \<Gamma> & \<Sigma> \<turnstile> v : t\<^sub>1 \<Longrightarrow> \<Gamma> & \<Sigma> \<tturnstile> \<Lambda> \<Longrightarrow> \<exists>t\<^sub>3. (\<Gamma> & \<Sigma> \<turnstile> e' : t\<^sub>3 \<rightarrow> t\<^sub>2) \<and> (\<Gamma> & \<Sigma> \<turnstile> v' : t\<^sub>3)"
  proof (induction \<Lambda> \<Sigma> e v e' v' arbitrary: t\<^sub>1 t\<^sub>2 rule: evaluate.induct)
  case (ev_pair1 \<Lambda> \<Sigma> f\<^sub>1 v\<^sub>1 f\<^sub>1' v\<^sub>1' f\<^sub>2 v\<^sub>2)
    then obtain t\<^sub>1\<^sub>1 t\<^sub>1\<^sub>2 t\<^sub>2\<^sub>1 t\<^sub>2\<^sub>2 t\<^sub>1\<^sub>1' where T: "(\<Gamma> & \<Sigma> \<turnstile> v\<^sub>1 : t\<^sub>1\<^sub>1) \<and> (\<Gamma> & \<Sigma> \<turnstile> v\<^sub>2 : t\<^sub>1\<^sub>2) \<and> 
      (\<Gamma> & \<Sigma> \<turnstile> f\<^sub>1 : t\<^sub>1\<^sub>1 \<rightarrow> t\<^sub>2\<^sub>1) \<and> (\<Gamma> & \<Sigma> \<turnstile> f\<^sub>2 : t\<^sub>1\<^sub>2 \<rightarrow> t\<^sub>2\<^sub>2) \<and> t\<^sub>1 = t\<^sub>1\<^sub>1 \<otimes> t\<^sub>1\<^sub>2 \<and> t\<^sub>2 = t\<^sub>2\<^sub>1 \<otimes> t\<^sub>2\<^sub>2 \<and> 
        (\<Gamma> & \<Sigma> \<turnstile> f\<^sub>1' : t\<^sub>1\<^sub>1' \<rightarrow> t\<^sub>2\<^sub>1) \<and> \<Gamma> & \<Sigma> \<turnstile> v\<^sub>1' : t\<^sub>1\<^sub>1'" by fastforce
    hence "(\<Gamma> & \<Sigma> \<turnstile> f\<^sub>1' \<parallel> f\<^sub>2 : t\<^sub>1\<^sub>1' \<otimes> t\<^sub>1\<^sub>2 \<rightarrow> t\<^sub>2) \<and> \<Gamma> & \<Sigma> \<turnstile> PairV v\<^sub>1' v\<^sub>2 : t\<^sub>1\<^sub>1' \<otimes> t\<^sub>1\<^sub>2" by simp
    thus ?case by fastforce
  next case (ev_pair2 \<Lambda> \<Sigma> f\<^sub>2 v\<^sub>2 f\<^sub>2' v\<^sub>2' v\<^sub>1)
    then obtain t\<^sub>1\<^sub>1 t\<^sub>1\<^sub>2 t\<^sub>2\<^sub>2 t\<^sub>1\<^sub>2' where T: "(\<Gamma> & \<Sigma> \<turnstile> v\<^sub>1 : t\<^sub>1\<^sub>1) \<and> (\<Gamma> & \<Sigma> \<turnstile> v\<^sub>2 : t\<^sub>1\<^sub>2) \<and> 
      (\<Gamma> & \<Sigma> \<turnstile> f\<^sub>2 : t\<^sub>1\<^sub>2 \<rightarrow> t\<^sub>2\<^sub>2) \<and> t\<^sub>1 = t\<^sub>1\<^sub>1 \<otimes> t\<^sub>1\<^sub>2 \<and> t\<^sub>2 = t\<^sub>1\<^sub>1 \<otimes> t\<^sub>2\<^sub>2 \<and> (\<Gamma> & \<Sigma> \<turnstile> f\<^sub>2' : t\<^sub>1\<^sub>2' \<rightarrow> t\<^sub>2\<^sub>2) \<and> 
        \<Gamma> & \<Sigma> \<turnstile> v\<^sub>2' : t\<^sub>1\<^sub>2'" by fastforce
    hence "(\<Gamma> & \<Sigma> \<turnstile> \<epsilon> \<parallel> f\<^sub>2' : t\<^sub>1\<^sub>1 \<otimes> t\<^sub>1\<^sub>2' \<rightarrow> t\<^sub>2) \<and> \<Gamma> & \<Sigma> \<turnstile> PairV v\<^sub>1 v\<^sub>2' : t\<^sub>1\<^sub>1 \<otimes> t\<^sub>1\<^sub>2'" by simp
    thus ?case by fastforce
  next case (ev_tup \<Lambda> \<Sigma> v)
    hence "t\<^sub>2 = t\<^sub>1 \<otimes> t\<^sub>1" by fastforce
    moreover from ev_tup have "(\<Gamma> & \<Sigma> \<turnstile> \<epsilon> : t\<^sub>1 \<otimes> t\<^sub>1 \<rightarrow> t\<^sub>1 \<otimes> t\<^sub>1) \<and> \<Gamma> & \<Sigma> \<turnstile> PairV v v : t\<^sub>1 \<otimes> t\<^sub>1" 
      by simp
    ultimately show ?case by fastforce
  next case (ev_inl \<Lambda> \<Sigma> v)
    moreover then obtain t\<^sub>3 where "t\<^sub>2 = t\<^sub>1 \<oplus> t\<^sub>3" by fastforce
    ultimately have "(\<Gamma> & \<Sigma> \<turnstile> \<epsilon> : t\<^sub>1 \<oplus> t\<^sub>3 \<rightarrow> t\<^sub>2) \<and> \<Gamma> & \<Sigma> \<turnstile> InlV v : t\<^sub>1 \<oplus> t\<^sub>3" by simp
    thus ?case by fastforce
  next case (ev_inr \<Lambda> \<Sigma> v)
    moreover then obtain t\<^sub>3 where "t\<^sub>2 = t\<^sub>3 \<oplus> t\<^sub>1" by fastforce
    ultimately have "(\<Gamma> & \<Sigma> \<turnstile> \<epsilon> : t\<^sub>3 \<oplus> t\<^sub>1 \<rightarrow> t\<^sub>2) \<and> \<Gamma> & \<Sigma> \<turnstile> InrV v : t\<^sub>3 \<oplus> t\<^sub>1" by simp
    thus ?case by fastforce
  next case (ev_csl \<Lambda> \<Sigma> f\<^sub>l f\<^sub>r v)
    then obtain t\<^sub>1\<^sub>l t\<^sub>1\<^sub>r t\<^sub>2\<^sub>l t\<^sub>2\<^sub>r where V: "(\<Gamma> & \<Sigma> \<turnstile> f\<^sub>l : t\<^sub>1\<^sub>l \<rightarrow> t\<^sub>2\<^sub>l) \<and> (\<Gamma> & \<Sigma> \<turnstile> f\<^sub>r : t\<^sub>1\<^sub>r \<rightarrow> t\<^sub>2\<^sub>r) \<and> 
      (\<Gamma> & \<Sigma> \<turnstile> v : t\<^sub>1\<^sub>l) \<and> t\<^sub>1 = t\<^sub>1\<^sub>l \<oplus> t\<^sub>1\<^sub>r \<and> t\<^sub>2 = t\<^sub>2\<^sub>l \<oplus> t\<^sub>2\<^sub>r" by fastforce
    hence "\<Gamma> & \<Sigma> \<turnstile> \<iota>\<^sub>l \<cdot> f\<^sub>l : t\<^sub>1\<^sub>l \<rightarrow> t\<^sub>2\<^sub>l \<oplus> t\<^sub>2\<^sub>r" by (metis tc_inl tc_comp)
    with V show ?case by fastforce
  next case (ev_csr \<Lambda> \<Sigma> f\<^sub>l f\<^sub>r v)
    then obtain t\<^sub>1\<^sub>l t\<^sub>1\<^sub>r t\<^sub>2\<^sub>l t\<^sub>2\<^sub>r where V: "(\<Gamma> & \<Sigma> \<turnstile> f\<^sub>l : t\<^sub>1\<^sub>l \<rightarrow> t\<^sub>2\<^sub>l) \<and> (\<Gamma> & \<Sigma> \<turnstile> f\<^sub>r : t\<^sub>1\<^sub>r \<rightarrow> t\<^sub>2\<^sub>r) \<and> 
      (\<Gamma> & \<Sigma> \<turnstile> v : t\<^sub>1\<^sub>r) \<and> t\<^sub>1 = t\<^sub>1\<^sub>l \<oplus> t\<^sub>1\<^sub>r \<and> t\<^sub>2 = t\<^sub>2\<^sub>l \<oplus> t\<^sub>2\<^sub>r" by fastforce
    hence "\<Gamma> & \<Sigma> \<turnstile> \<iota>\<^sub>r \<cdot> f\<^sub>r : t\<^sub>1\<^sub>r \<rightarrow> t\<^sub>2\<^sub>l \<oplus> t\<^sub>2\<^sub>r" by (metis tc_inr tc_comp)
    with V show ?case by fastforce
  next case (ev_dstl \<Lambda> \<Sigma> v\<^sub>1 v\<^sub>2)
    then obtain t\<^sub>3 t\<^sub>4 t\<^sub>5 where "(\<Gamma> & \<Sigma> \<turnstile> v\<^sub>1 : t\<^sub>3) \<and> (\<Gamma> & \<Sigma> \<turnstile> v\<^sub>2 : t\<^sub>5) \<and> t\<^sub>1 = (t\<^sub>3 \<oplus> t\<^sub>4) \<otimes> t\<^sub>5 \<and> 
      t\<^sub>2 = t\<^sub>3 \<otimes> t\<^sub>5 \<oplus> t\<^sub>4 \<otimes> t\<^sub>5" by fastforce
    hence "(\<Gamma> & \<Sigma> \<turnstile> \<epsilon> : t\<^sub>2 \<rightarrow> t\<^sub>2) \<and> \<Gamma> & \<Sigma> \<turnstile> InlV (PairV v\<^sub>1 v\<^sub>2) : t\<^sub>2" by simp
    thus ?case by fastforce
  next case (ev_dstr \<Lambda> \<Sigma> v\<^sub>1 v\<^sub>2)
    then obtain t\<^sub>3 t\<^sub>4 t\<^sub>5 where "(\<Gamma> & \<Sigma> \<turnstile> v\<^sub>1 : t\<^sub>4) \<and> (\<Gamma> & \<Sigma> \<turnstile> v\<^sub>2 : t\<^sub>5) \<and> t\<^sub>1 = (t\<^sub>3 \<oplus> t\<^sub>4) \<otimes> t\<^sub>5 \<and> 
      t\<^sub>2 = t\<^sub>3 \<otimes> t\<^sub>5 \<oplus> t\<^sub>4 \<otimes> t\<^sub>5" by fastforce
    hence "(\<Gamma> & \<Sigma> \<turnstile> \<epsilon> : t\<^sub>2 \<rightarrow> t\<^sub>2) \<and> \<Gamma> & \<Sigma> \<turnstile> InrV (PairV v\<^sub>1 v\<^sub>2) : t\<^sub>2" by simp
    thus ?case by fastforce
  next case (ev_arr \<Lambda> \<Sigma> g f e)
    then obtain t\<^sub>1\<^sub>1 t\<^sub>1\<^sub>2 t\<^sub>2\<^sub>1 t\<^sub>2\<^sub>2 where "(\<Gamma> & \<Sigma> \<turnstile> f : t\<^sub>2\<^sub>1 \<rightarrow> t\<^sub>1\<^sub>1) \<and> (\<Gamma> & \<Sigma> \<turnstile> g : t\<^sub>1\<^sub>2 \<rightarrow> t\<^sub>2\<^sub>2) \<and> 
      (\<Gamma> & \<Sigma> \<turnstile> e : t\<^sub>1\<^sub>1 \<rightarrow> t\<^sub>1\<^sub>2) \<and> t\<^sub>1 = t\<^sub>1\<^sub>1 \<hookrightarrow> t\<^sub>1\<^sub>2 \<and> t\<^sub>2 = t\<^sub>2\<^sub>1 \<hookrightarrow> t\<^sub>2\<^sub>2" by fastforce
    hence "(\<Gamma> & \<Sigma> \<turnstile> \<epsilon> : t\<^sub>2\<^sub>1 \<hookrightarrow> t\<^sub>2\<^sub>2 \<rightarrow> t\<^sub>2) \<and> \<Gamma> & \<Sigma> \<turnstile> FunV (g \<cdot> e \<cdot> f) : t\<^sub>2\<^sub>1 \<hookrightarrow> t\<^sub>2\<^sub>2" by fastforce
    thus ?case by fastforce
  next case (ev_inj \<Lambda> \<Sigma> F v)
    hence "(\<Gamma> & \<Sigma> \<turnstile> \<epsilon> : t\<^sub>2 \<rightarrow> t\<^sub>2) \<and> \<Gamma> & \<Sigma> \<turnstile> InjV F v : t\<^sub>2" by fastforce
    thus ?case by fastforce
  next case (ev_cata \<Sigma> n F \<Lambda> f v)
    hence V: "(\<Gamma> & \<Sigma> \<turnstile> f : t\<^sub>2 \<star> F \<rightarrow> t\<^sub>2) \<and> \<Gamma> & \<Sigma> \<turnstile> v : \<mu> F" by fastforce
    moreover from ev_cata have "\<Gamma> & \<Sigma> \<turnstile> \<lparr> f \<rparr>\<^bsub>n\<^esub> \<bullet> F : \<mu> F \<star> F \<rightarrow> t\<^sub>2 \<star> F" by fastforce
    moreover from ev_cata have "\<Gamma> & \<Sigma> \<turnstile> \<prec>\<^bsub>n\<^esub> : \<mu> F \<rightarrow> \<mu> F \<star> F" by simp
    ultimately have "\<Gamma> & \<Sigma> \<turnstile> f \<cdot> \<lparr> f \<rparr>\<^bsub>n\<^esub> \<bullet> F \<cdot> \<prec>\<^bsub>n\<^esub> : \<mu> F \<rightarrow> t\<^sub>2" by (metis tc_comp)
    with V have "(\<Gamma> & \<Sigma> \<turnstile> f \<cdot> \<lparr> f \<rparr>\<^bsub>n\<^esub> \<bullet> F \<cdot> \<prec>\<^bsub>n\<^esub> : \<mu> F \<rightarrow> t\<^sub>2) \<and> \<Gamma> & \<Sigma> \<turnstile> v : \<mu> F" by simp
    thus ?case by fastforce
  next case (ev_ana \<Sigma> n F \<Lambda> f v)
    moreover hence V: "(\<Gamma> & \<Sigma> \<turnstile> f : t\<^sub>1 \<rightarrow> t\<^sub>1 \<star> F) \<and> (\<Gamma> & \<Sigma> \<turnstile> v : t\<^sub>1) \<and> t\<^sub>2 = \<mu> F" by fastforce
    ultimately have "\<Gamma> & \<Sigma> \<turnstile> \<succ>\<^bsub>n\<^esub> : t\<^sub>2 \<star> F \<rightarrow> t\<^sub>2" by simp
    moreover from ev_ana have "\<Gamma> & \<Sigma> \<turnstile> \<lbrakk> f \<rbrakk>\<^bsub>n\<^esub> \<bullet> F : t\<^sub>1 \<star> F \<rightarrow> t\<^sub>2 \<star> F" by simp
    moreover from V have "\<Gamma> & \<Sigma> \<turnstile> f : t\<^sub>1 \<rightarrow> t\<^sub>1 \<star> F" by simp
    ultimately have "\<Gamma> & \<Sigma> \<turnstile> \<succ>\<^bsub>n\<^esub> \<cdot> \<lbrakk> f \<rbrakk>\<^bsub>n\<^esub> \<bullet> F \<cdot> f : t\<^sub>1 \<rightarrow> t\<^sub>2" by simp
    with V show ?case by fastforce
  next case (ev_var \<Lambda> x e \<Sigma> v)
    hence "\<Gamma> x = Some (t\<^sub>1, t\<^sub>2)" by fastforce
    with ev_var obtain e' where "\<Lambda> x = Some e' \<and> \<Gamma> & \<Sigma> \<turnstile> e' : t\<^sub>1 \<rightarrow> t\<^sub>2" 
      by (metis typecheck_context_def)
    with ev_var show ?case by fastforce
  qed force+

(* big-step evaluation *) 

inductive total_eval :: "(name \<rightharpoonup> expr) \<Rightarrow> (name \<rightharpoonup> funct) \<Rightarrow> expr \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool" 
    (infix "& _ \<turnstile> _ \<cdot> _ \<Down>" 60) where
  tev_base [simp]: "\<Lambda> & \<Sigma> \<turnstile> \<epsilon> \<cdot> v \<Down> v"
| tev_step [simp]: "\<Lambda> & \<Sigma> \<turnstile> e \<cdot> v \<leadsto> e' \<cdot> v' \<Longrightarrow> \<Lambda> & \<Sigma> \<turnstile> e' \<cdot> v' \<Down> v'' \<Longrightarrow> \<Lambda> & \<Sigma> \<turnstile> e \<cdot> v \<Down> v''"

lemma [elim]: "\<Lambda> & \<Sigma> \<turnstile> f \<cdot> v \<Down> v' \<Longrightarrow> \<Lambda> & \<Sigma> \<turnstile> g \<cdot> v' \<Down> v'' \<Longrightarrow> \<Lambda> & \<Sigma> \<turnstile> (g \<cdot> f) \<cdot> v \<Down> v''"
  proof (induction \<Lambda> \<Sigma> f v v' rule: total_eval.induct)
  case (tev_base \<Lambda> \<Sigma> v)
    moreover have "\<Lambda> & \<Sigma> \<turnstile> (g \<cdot> \<epsilon>) \<cdot> v \<leadsto> g \<cdot> v" by simp
    ultimately show ?case by (metis tev_step)
  next case (tev_step \<Lambda> \<Sigma> f v f' v' v''')
    hence "\<Lambda> & \<Sigma> \<turnstile> (g \<cdot> f) \<cdot> v \<leadsto> (g \<cdot> f') \<cdot> v'" by simp
    moreover from tev_step have "\<Lambda> & \<Sigma> \<turnstile> (g \<cdot> f') \<cdot> v' \<Down> v''" by simp
    ultimately show ?case by (metis total_eval.tev_step)
  qed

lemma [simp]: "\<Lambda> & \<Sigma> \<turnstile> e \<cdot> v \<leadsto> \<epsilon> \<cdot> v' \<Longrightarrow> \<Lambda> & \<Sigma> \<turnstile> e \<cdot> v \<Down> v'"
  by rule (simp, simp)

lemma eps_big_eval [elim]: "\<Lambda> & \<Sigma> \<turnstile> \<epsilon> \<cdot> v \<Down> v' \<Longrightarrow> v = v'"
  proof (induction \<Lambda> \<Sigma> \<epsilon> v v' rule: total_eval.induct)
  case (tev_step \<Lambda> \<Sigma> v e' v' v'')
    thus ?case by (induction \<epsilon> v e' v' rule: evaluate.induct)
  qed simp_all

lemma [simp]: "\<Lambda> & \<Sigma> \<turnstile> f\<^sub>2 \<cdot> v\<^sub>2 \<Down> v\<^sub>4 \<Longrightarrow> \<Lambda> & \<Sigma> \<turnstile> \<epsilon> \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<Down> PairV v\<^sub>1 v\<^sub>4"
  proof (induction \<Lambda> \<Sigma> f\<^sub>2 v\<^sub>2 v\<^sub>4 rule: total_eval.induct)
  case (tev_step \<Lambda> \<Sigma> f\<^sub>2 v\<^sub>2 f\<^sub>2' v\<^sub>2' v\<^sub>4)
    hence "\<Lambda> & \<Sigma> \<turnstile> \<epsilon> \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> \<epsilon> \<parallel> f\<^sub>2' \<cdot> PairV v\<^sub>1 v\<^sub>2'" by simp
    moreover from tev_step have "\<Lambda> & \<Sigma> \<turnstile> \<epsilon> \<parallel> f\<^sub>2' \<cdot> PairV v\<^sub>1 v\<^sub>2' \<Down> PairV v\<^sub>1 v\<^sub>4" by simp
    ultimately show ?case by simp
  qed simp_all

lemma [simp]: "\<Lambda> & \<Sigma> \<turnstile> f\<^sub>1 \<cdot> v\<^sub>1 \<Down> v\<^sub>3 \<Longrightarrow> \<Lambda> & \<Sigma> \<turnstile> f\<^sub>2 \<cdot> v\<^sub>2 \<Down> v\<^sub>4 \<Longrightarrow> 
    \<Lambda> & \<Sigma> \<turnstile> f\<^sub>1 \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<Down> PairV v\<^sub>3 v\<^sub>4"
  proof (induction \<Lambda> \<Sigma> f\<^sub>1 v\<^sub>1 v\<^sub>3 rule: total_eval.induct)
  case (tev_step \<Lambda> \<Sigma> f\<^sub>1 v\<^sub>1 f\<^sub>1' v\<^sub>1' v\<^sub>3)
    hence "\<Lambda> & \<Sigma> \<turnstile> f\<^sub>1 \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> f\<^sub>1' \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1' v\<^sub>2" by simp
    moreover from tev_step have "\<Lambda> & \<Sigma> \<turnstile> f\<^sub>1' \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1' v\<^sub>2 \<Down> PairV v\<^sub>3 v\<^sub>4" by simp
    ultimately show ?case by simp
  qed simp_all

lemma pair_big_eval [elim]: "\<Lambda> & \<Sigma> \<turnstile> f\<^sub>1 \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<Down> PairV v\<^sub>3 v\<^sub>4 \<Longrightarrow> 
    (\<Lambda> & \<Sigma> \<turnstile> f\<^sub>1 \<cdot> v\<^sub>1 \<Down> v\<^sub>3) \<and> \<Lambda> & \<Sigma> \<turnstile> f\<^sub>2 \<cdot> v\<^sub>2 \<Down> v\<^sub>4"
  proof (induction \<Lambda> \<Sigma> "f\<^sub>1 \<parallel> f\<^sub>2" "PairV v\<^sub>1 v\<^sub>2" "PairV v\<^sub>3 v\<^sub>4" 
         arbitrary: f\<^sub>1 f\<^sub>2 v\<^sub>1 v\<^sub>2 rule: total_eval.induct)
  case (tev_step \<Lambda> \<Sigma> e' v')
    thus ?case
      proof (induction \<Lambda> \<Sigma> "f\<^sub>1 \<parallel> f\<^sub>2" "PairV v\<^sub>1 v\<^sub>2" e' v' arbitrary: f\<^sub>1 f\<^sub>2 v\<^sub>1 v\<^sub>2 rule: evaluate.induct)
      case (ev_pair3 \<Lambda> \<Sigma> v\<^sub>1 v\<^sub>2)
        hence "PairV v\<^sub>1 v\<^sub>2 = PairV v\<^sub>3 v\<^sub>4" by (metis eps_big_eval)
        thus ?case by simp
      qed simp_all
  qed

lemma [simp]: "\<Lambda> & \<Sigma> \<turnstile> f\<^sub>l \<cdot> v \<Down> v' \<Longrightarrow> \<Lambda> & \<Sigma> \<turnstile> f\<^sub>l \<bar> f\<^sub>r \<cdot> InlV v \<Down> InlV v'"
  proof
    show "\<Lambda> & \<Sigma> \<turnstile> f\<^sub>l \<bar> f\<^sub>r \<cdot> InlV v \<leadsto> (\<iota>\<^sub>l \<cdot> f\<^sub>l) \<cdot> v" by simp
    show "\<Lambda> & \<Sigma> \<turnstile> f\<^sub>l \<cdot> v \<Down> v' \<Longrightarrow> \<Lambda> & \<Sigma> \<turnstile> (\<iota>\<^sub>l \<cdot> f\<^sub>l) \<cdot> v \<Down> InlV v'" by auto
  qed

lemma [simp]: "\<Lambda> & \<Sigma> \<turnstile> f\<^sub>r \<cdot> v \<Down> v' \<Longrightarrow> \<Lambda> & \<Sigma> \<turnstile> f\<^sub>l \<bar> f\<^sub>r \<cdot> InrV v \<Down> InrV v'"
  proof
    show "\<Lambda> & \<Sigma> \<turnstile> f\<^sub>l \<bar> f\<^sub>r \<cdot> InrV v \<leadsto> (\<iota>\<^sub>r \<cdot> f\<^sub>r) \<cdot> v" by simp
    show "\<Lambda> & \<Sigma> \<turnstile> f\<^sub>r \<cdot> v \<Down> v' \<Longrightarrow> \<Lambda> & \<Sigma> \<turnstile> (\<iota>\<^sub>r \<cdot> f\<^sub>r) \<cdot> v \<Down> InrV v'" by auto
  qed

(* since we are a turing-complete language, total progress is not provable *)

theorem total_preservation [simp]: "\<Lambda> & \<Sigma> \<turnstile> e \<cdot> v \<Down> v' \<Longrightarrow> \<Gamma> & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> 
    \<Gamma> & \<Sigma> \<turnstile> v : t\<^sub>1 \<Longrightarrow> \<Gamma> & \<Sigma> \<tturnstile> \<Lambda> \<Longrightarrow> \<Gamma> & \<Sigma> \<turnstile> v' : t\<^sub>2"
  proof (induction \<Lambda> \<Sigma> e v v' arbitrary: t\<^sub>1 rule: total_eval.induct)
  case (tev_step \<Lambda> \<Sigma> e v e' v' v'')
    moreover then obtain t\<^sub>3 where "(\<Gamma> & \<Sigma> \<turnstile> e' : t\<^sub>3 \<rightarrow> t\<^sub>2) \<and> (\<Gamma> & \<Sigma> \<turnstile> v' : t\<^sub>3)" 
      by (metis preservation)
    ultimately show ?case by fastforce
  qed auto

(* misc lemmas *)

lemma [simp]: "\<Gamma> & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> x \<notin> dom \<Gamma> \<Longrightarrow> \<Gamma>(x \<mapsto> tt) & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2"
  and [simp]: "\<Gamma> & \<Sigma> \<turnstile> v : t \<Longrightarrow> x \<notin> dom \<Gamma> \<Longrightarrow> \<Gamma>(x \<mapsto> tt) & \<Sigma> \<turnstile> v : t"
  proof (induction \<Gamma> \<Sigma> e t\<^sub>1 t\<^sub>2 and \<Gamma> \<Sigma> v t rule: typecheck\<^sub>e_typecheck\<^sub>v.inducts) 
  case (tc_var \<Gamma> y t\<^sub>1 t\<^sub>2)
    moreover hence "x \<noteq> y" by auto
    ultimately show ?case by simp
  qed simp_all

lemma [simp]: "\<Gamma> & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma>' ++ \<Gamma> & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2"
  and [simp]: "\<Gamma> & \<Sigma> \<turnstile> v : t \<Longrightarrow> \<Gamma>' ++ \<Gamma> & \<Sigma> \<turnstile> v : t"
  by (induction \<Gamma> \<Sigma> e t\<^sub>1 t\<^sub>2 and \<Gamma> \<Sigma> v t rule: typecheck\<^sub>e_typecheck\<^sub>v.inducts) simp_all

lemma [simp]: "\<Gamma> & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> dom \<Gamma> \<inter> dom \<Gamma>' = {} \<Longrightarrow> \<Gamma> ++ \<Gamma>' & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2"
  and [simp]: "\<Gamma> & \<Sigma> \<turnstile> v : t \<Longrightarrow> dom \<Gamma> \<inter> dom \<Gamma>' = {} \<Longrightarrow> \<Gamma> ++ \<Gamma>' & \<Sigma> \<turnstile> v : t"
  proof (induction \<Gamma> \<Sigma> e t\<^sub>1 t\<^sub>2 and \<Gamma> \<Sigma> v t rule: typecheck\<^sub>e_typecheck\<^sub>v.inducts) 
  case (tc_var \<Gamma> x t\<^sub>1 t\<^sub>2 \<Sigma>)
    moreover hence "\<Gamma>' x = None" by auto
    ultimately show ?case by (simp add: map_add_def)
  qed simp_all

lemma [simp]: "\<Gamma> & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> x \<notin> dom \<Sigma> \<Longrightarrow> \<Gamma> & \<Sigma>(x \<mapsto> F) \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2"
  and [simp]: "\<Gamma> & \<Sigma> \<turnstile> v : t \<Longrightarrow> x \<notin> dom \<Sigma> \<Longrightarrow> \<Gamma> & \<Sigma>(x \<mapsto> F) \<turnstile> v : t"
  proof (induction \<Gamma> \<Sigma> e t\<^sub>1 t\<^sub>2 and \<Gamma> \<Sigma> v t rule: typecheck\<^sub>e_typecheck\<^sub>v.inducts)
  case (tc_inj \<Sigma> n F' \<Gamma>)
    hence "(\<Sigma>(x \<mapsto> F)) n = Some F'" by auto
    thus ?case by simp
  next case (tc_outj \<Sigma> n F' \<Gamma>)
    hence "(\<Sigma>(x \<mapsto> F)) n = Some F'" by auto
    thus ?case by simp
  next case (tc_cata \<Sigma> n F' \<Gamma>)
    moreover hence "(\<Sigma>(x \<mapsto> F)) n = Some F'" by auto
    ultimately show ?case by simp
  next case (tc_ana \<Sigma> n F' \<Gamma>)
    moreover hence "(\<Sigma>(x \<mapsto> F)) n = Some F'" by auto
    ultimately show ?case by simp
  next case (tcv_inj \<Sigma> n F' \<Gamma>)
    moreover hence "(\<Sigma>(x \<mapsto> F)) n = Some F'" by auto
    ultimately show ?case by simp
  qed simp_all

lemma [simp]: "\<Gamma> & \<Sigma> \<tturnstile> \<Lambda> \<Longrightarrow> x \<notin> dom \<Sigma> \<Longrightarrow> \<Gamma> & \<Sigma>(x \<mapsto> F) \<tturnstile> \<Lambda>"
  proof (unfold typecheck_context_def, rule, rule, rule, rule)
    fix y t\<^sub>1 t\<^sub>2
    assume "\<forall>x t\<^sub>1 t\<^sub>2. \<Gamma> x = Some (t\<^sub>1, t\<^sub>2) \<longrightarrow> (\<exists>e. \<Lambda> x = Some e \<and> \<Gamma> & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2)"
       and "\<Gamma> y = Some (t\<^sub>1, t\<^sub>2)"
    then obtain e where "\<Lambda> y = Some e \<and> \<Gamma> & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2" by blast
    moreover assume "x \<notin> dom \<Sigma>"
    ultimately show "\<exists>e. \<Lambda> y = Some e \<and> \<Gamma> & \<Sigma>(x \<mapsto> F) \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2" by simp
  qed

lemma [simp]: "\<Gamma> & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> & \<Sigma> \<tturnstile> \<Lambda> \<Longrightarrow> x \<notin> dom \<Lambda> \<Longrightarrow> 
    \<Gamma>(x \<mapsto> (t\<^sub>1, t\<^sub>2)) & \<Sigma> \<tturnstile> \<Lambda>(x \<mapsto> e)"
  proof (unfold typecheck_context_def, rule, rule, rule, rule)
    fix y t\<^sub>1' t\<^sub>2'
    assume A: "\<Gamma> & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2"
       and B: "\<forall>x t\<^sub>1 t\<^sub>2. \<Gamma> x = Some (t\<^sub>1, t\<^sub>2) \<longrightarrow> (\<exists>e. \<Lambda> x = Some e \<and> \<Gamma> & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2)"
       and C: "x \<notin> dom \<Lambda>"
       and D: "(\<Gamma>(x \<mapsto> (t\<^sub>1, t\<^sub>2))) y = Some (t\<^sub>1', t\<^sub>2')"
    moreover hence E: "x \<notin> dom \<Gamma>" by auto
    ultimately show "\<exists>e'. (\<Lambda>(x \<mapsto> e)) y = Some e' \<and> \<Gamma>(x \<mapsto> (t\<^sub>1, t\<^sub>2)) & \<Sigma> \<turnstile> e' : t\<^sub>1' \<rightarrow> t\<^sub>2'"
      proof (cases "x = y")
      case False
        with B D obtain e' where "\<Lambda> y = Some e' \<and> \<Gamma> & \<Sigma> \<turnstile> e' : t\<^sub>1' \<rightarrow> t\<^sub>2'" by fastforce
        with E False show ?thesis by simp
      qed simp_all
  qed

lemma [simp]: "\<Gamma> & \<Sigma> \<tturnstile> \<Lambda> \<Longrightarrow> \<Gamma>' & \<Sigma> \<tturnstile> \<Lambda>' \<Longrightarrow> dom \<Gamma> \<inter> dom \<Gamma>' = {} \<Longrightarrow> dom \<Lambda> \<inter> dom \<Lambda>' = {} \<Longrightarrow> 
    \<Gamma> ++ \<Gamma>' & \<Sigma> \<tturnstile> \<Lambda> ++ \<Lambda>'"
  proof (unfold typecheck_context_def, rule, rule, rule, rule)
    fix x t\<^sub>1 t\<^sub>2
    assume A: "\<forall>x t\<^sub>1 t\<^sub>2. \<Gamma> x = Some (t\<^sub>1, t\<^sub>2) \<longrightarrow> (\<exists>e. \<Lambda> x = Some e \<and> \<Gamma> & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2)"
    assume B: "\<forall>x t\<^sub>1 t\<^sub>2. \<Gamma>' x = Some (t\<^sub>1, t\<^sub>2) \<longrightarrow> (\<exists>e. \<Lambda>' x = Some e \<and> \<Gamma>' & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2)"
    assume C: "dom \<Gamma> \<inter> dom \<Gamma>' = {}"
    assume D: "dom \<Lambda> \<inter> dom \<Lambda>' = {}"
    assume E: "(\<Gamma> ++ \<Gamma>') x = Some (t\<^sub>1, t\<^sub>2)"
    show "\<exists>e. (\<Lambda> ++ \<Lambda>') x = Some e \<and> \<Gamma> ++ \<Gamma>' & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2" 
      proof (cases "x \<in> dom \<Gamma>'")
      case True
        with B E obtain e where "\<Lambda>' x = Some e \<and> \<Gamma>' & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2" by fastforce
        thus ?thesis by simp
      next case False
        with A E obtain e where F: "\<Lambda> x = Some e \<and> \<Gamma> & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2" by fastforce
        with D have "\<Lambda>' x = None" by auto
        with F have "(\<Lambda> ++ \<Lambda>') x = Some e" by (simp add: map_add_def)
        with C F show ?thesis by simp
      qed
  qed

end
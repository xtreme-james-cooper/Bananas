theory BananasStatics
imports BananasLanguage
begin

record static_environment = 
  var\<^sub>e_type :: "name \<rightharpoonup> type \<times> type" 
  var\<^sub>v_type :: "name \<rightharpoonup> type list \<times> type" 
  var\<^sub>t_type :: "name \<rightharpoonup> funct"

definition empty_static :: static_environment where
  "empty_static = \<lparr> var\<^sub>e_type = Map.empty, var\<^sub>v_type = Map.empty, var\<^sub>t_type = Map.empty \<rparr>"

definition extend\<^sub>e\<^sub>s :: "name \<Rightarrow> type \<times> type \<Rightarrow> static_environment \<Rightarrow> static_environment" where
  "extend\<^sub>e\<^sub>s x t \<Gamma> = \<Gamma>\<lparr> var\<^sub>e_type := var\<^sub>e_type \<Gamma>(x \<mapsto> t) \<rparr>"

definition extend\<^sub>v\<^sub>s :: "name \<Rightarrow> type list \<times> type \<Rightarrow> static_environment \<Rightarrow> static_environment" where
  "extend\<^sub>v\<^sub>s x t \<Gamma> = \<Gamma>\<lparr> var\<^sub>v_type := var\<^sub>v_type \<Gamma>(x \<mapsto> t) \<rparr>"

definition combine\<^sub>s :: "static_environment \<Rightarrow> static_environment \<Rightarrow> static_environment" where
  "combine\<^sub>s \<Gamma> \<Gamma>' = \<lparr> 
      var\<^sub>e_type = var\<^sub>e_type \<Gamma> ++ var\<^sub>e_type \<Gamma>', 
      var\<^sub>v_type = var\<^sub>v_type \<Gamma> ++ var\<^sub>v_type \<Gamma>', 
      var\<^sub>t_type = var\<^sub>t_type \<Gamma> ++ var\<^sub>t_type \<Gamma>' \<rparr>"

definition domain\<^sub>s :: "static_environment \<Rightarrow> name set" where
  "domain\<^sub>s \<Gamma> = dom (var\<^sub>e_type \<Gamma>) \<union> dom (var\<^sub>v_type \<Gamma>) \<union> dom (var\<^sub>t_type \<Gamma>)"

fun apply_functor_type :: "type \<Rightarrow> funct \<Rightarrow> type" (infixl "\<star>" 75) where
  "t \<star> Id = t"
| "t \<star> K t' = t'"
| "t \<star> f\<^sub>1 \<Otimes> f\<^sub>2 = (t \<star> f\<^sub>1) \<otimes> (t \<star> f\<^sub>2)"
| "t \<star> f\<^sub>1 \<Oplus> f\<^sub>2 = (t \<star> f\<^sub>1) \<oplus> (t \<star> f\<^sub>2)"

inductive typecheck\<^sub>e :: "static_environment \<Rightarrow> expr \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" (infix "\<turnstile> _ : _ \<rightarrow>" 60)
      and typecheck\<^sub>v :: "static_environment \<Rightarrow> val \<Rightarrow> type \<Rightarrow> bool" (infix "\<turnstile> _ :" 60) where
  tc_id [simp]: "\<Gamma> \<turnstile> \<epsilon> : t \<rightarrow> t"
| tc_con [simp]: "\<Gamma> \<turnstile> v : t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> \<kappa> v : t\<^sub>1 \<rightarrow> t\<^sub>2"
| tc_comp [simp]: "\<Gamma> \<turnstile> f : t\<^sub>2 \<rightarrow> t\<^sub>3 \<Longrightarrow> \<Gamma> \<turnstile> g : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> f \<cdot> g : t\<^sub>1 \<rightarrow> t\<^sub>3"
| tc_fst [simp]: "\<Gamma> \<turnstile> \<pi>\<^sub>1 : t\<^sub>1 \<otimes> t\<^sub>2 \<rightarrow> t\<^sub>1"
| tc_snd [simp]: "\<Gamma> \<turnstile> \<pi>\<^sub>2 : t\<^sub>1 \<otimes> t\<^sub>2 \<rightarrow> t\<^sub>2"
| tc_tup [simp]: "\<Gamma> \<turnstile> \<Theta> : t \<rightarrow> t \<otimes> t"
| tc_pair [simp]: "\<Gamma> \<turnstile> f\<^sub>1 : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> f\<^sub>2 : t\<^sub>3 \<rightarrow> t\<^sub>4 \<Longrightarrow> 
    \<Gamma> \<turnstile> f\<^sub>1 \<parallel> f\<^sub>2 : t\<^sub>1 \<otimes> t\<^sub>3 \<rightarrow> t\<^sub>2 \<otimes> t\<^sub>4"
| tc_inl [simp]: "\<Gamma> \<turnstile> \<iota>\<^sub>l : t\<^sub>1 \<rightarrow> t\<^sub>1 \<oplus> t\<^sub>2"
| tc_inr [simp]: "\<Gamma> \<turnstile> \<iota>\<^sub>r : t\<^sub>2 \<rightarrow> t\<^sub>1 \<oplus> t\<^sub>2"
| tc_str [simp]: "\<Gamma> \<turnstile> \<Xi> : t\<^sub>1 \<oplus> t\<^sub>1 \<rightarrow> t\<^sub>1"
| tc_case [simp]: "\<Gamma> \<turnstile> f\<^sub>l : t\<^sub>1 \<rightarrow> t\<^sub>3 \<Longrightarrow> \<Gamma> \<turnstile> f\<^sub>r : t\<^sub>2 \<rightarrow> t\<^sub>4 \<Longrightarrow> 
    \<Gamma> \<turnstile> f\<^sub>l \<bar> f\<^sub>r : t\<^sub>1 \<oplus> t\<^sub>2 \<rightarrow> t\<^sub>3 \<oplus> t\<^sub>4"
| tc_dst [simp]: "\<Gamma> \<turnstile> \<rhd> : (t\<^sub>1 \<oplus> t\<^sub>2) \<otimes> t\<^sub>3 \<rightarrow> t\<^sub>1 \<otimes> t\<^sub>3 \<oplus> t\<^sub>2 \<otimes> t\<^sub>3"
| tc_app [simp]: "\<Gamma> \<turnstile> $ : (t\<^sub>1 \<hookrightarrow> t\<^sub>2) \<otimes> t\<^sub>1 \<rightarrow> t\<^sub>2"
| tc_arr [simp]: "\<Gamma> \<turnstile> f : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> g : t\<^sub>3 \<rightarrow> t\<^sub>4 \<Longrightarrow> 
    \<Gamma> \<turnstile> g \<leftarrow> f : t\<^sub>2 \<hookrightarrow> t\<^sub>3 \<rightarrow> t\<^sub>1 \<hookrightarrow> t\<^sub>4"
| tc_inj [simp]: "var\<^sub>t_type \<Gamma> n = Some F \<Longrightarrow> \<Gamma> \<turnstile> \<succ>\<^bsub>n\<^esub> : \<mu> F \<star> F \<rightarrow> \<mu> F"
| tc_outj [simp]: "var\<^sub>t_type \<Gamma> n = Some F \<Longrightarrow> \<Gamma> \<turnstile> \<prec>\<^bsub>n\<^esub> : \<mu> F \<rightarrow> \<mu> F \<star> F"
| tc_cata [simp]: "var\<^sub>t_type \<Gamma> n = Some F \<Longrightarrow> \<Gamma> \<turnstile> f : t \<star> F \<rightarrow> t \<Longrightarrow> \<Gamma> \<turnstile> \<lparr> f \<rparr>\<^bsub>n\<^esub> : \<mu> F \<rightarrow> t"
| tc_ana [simp]: "var\<^sub>t_type \<Gamma> n = Some F \<Longrightarrow> \<Gamma> \<turnstile> f : t \<rightarrow> t \<star> F \<Longrightarrow> \<Gamma> \<turnstile> \<lbrakk> f \<rbrakk>\<^bsub>n\<^esub> : t \<rightarrow> \<mu> F"
| tc_var [simp]: "var\<^sub>e_type \<Gamma> x = Some (t\<^sub>1, t\<^sub>2) \<Longrightarrow> \<Gamma> \<turnstile> Var x : t\<^sub>1 \<rightarrow> t\<^sub>2"

| tcv_unit [simp]: "\<Gamma> \<turnstile> UnitV : \<one>"
| tcv_pair [simp]: "\<Gamma> \<turnstile> v\<^sub>1 : t\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile> v\<^sub>2 : t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> PairV v\<^sub>1 v\<^sub>2 : t\<^sub>1 \<otimes> t\<^sub>2"
| tcv_inl [simp]: "\<Gamma> \<turnstile> v : t\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile> InlV v : t\<^sub>1 \<oplus> t\<^sub>2"
| tcv_inr [simp]: "\<Gamma> \<turnstile> v : t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> InrV v : t\<^sub>1 \<oplus> t\<^sub>2"
| tcv_fun [simp]: "\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> FunV e : t\<^sub>1 \<hookrightarrow> t\<^sub>2"
| tcv_inj [simp]: "var\<^sub>t_type \<Gamma> n = Some F \<Longrightarrow> \<Gamma> \<turnstile> v : \<mu> F \<star> F \<Longrightarrow> \<Gamma> \<turnstile> InjV n v : \<mu> F"

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
inductive_cases [elim]: "\<Gamma> \<turnstile> \<prec>\<^bsub>n\<^esub> : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> \<succ>\<^bsub>n\<^esub> : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> \<lparr> f \<rparr>\<^bsub>n\<^esub> : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> \<lbrakk> f \<rbrakk>\<^bsub>n\<^esub> : t \<rightarrow> t'"
inductive_cases [elim]: "\<Gamma> \<turnstile> Var x : t \<rightarrow> t'"

inductive_cases [elim]: "\<Gamma> \<turnstile> UnitV : t"
inductive_cases [elim]: "\<Gamma> \<turnstile> PairV v\<^sub>1 v\<^sub>2 : t"
inductive_cases [elim]: "\<Gamma> \<turnstile> InrV v : t"
inductive_cases [elim]: "\<Gamma> \<turnstile> InlV v : t"
inductive_cases [elim]: "\<Gamma> \<turnstile> FunV e : t"
inductive_cases [elim]: "\<Gamma> \<turnstile> InjV f v : t"

inductive typecheck\<^sub>c\<^sub>e :: "static_environment \<Rightarrow> funct \<Rightarrow> (name \<times> name list) list \<Rightarrow> 
    (name \<rightharpoonup> type \<times> type) \<Rightarrow> bool" where
  tcce_nil [simp]: "typecheck\<^sub>c\<^sub>e \<Gamma> F [] Map.empty" 
| tcce_cons [simp]: "typecheck\<^sub>c\<^sub>e \<Gamma> F cts \<Gamma>\<^sub>e \<Longrightarrow> 
    those (map (map_option \<mu> o var\<^sub>t_type \<Gamma>) ts) = Some ts' \<Longrightarrow> 
      typecheck\<^sub>c\<^sub>e \<Gamma> F ((x, ts) # cts) (\<Gamma>\<^sub>e(x \<mapsto> (foldr (op \<otimes>) ts' \<one>, \<mu> F)))"

inductive typecheck\<^sub>c\<^sub>v :: "static_environment \<Rightarrow> funct \<Rightarrow> (name \<times> name list) list \<Rightarrow> 
    (name \<rightharpoonup> type list \<times> type) \<Rightarrow> bool" where
  tccv_nil [simp]: "typecheck\<^sub>c\<^sub>v \<Gamma> F [] Map.empty"
| tccv_cons [simp]: "typecheck\<^sub>c\<^sub>v \<Gamma> F cts \<Gamma>\<^sub>v \<Longrightarrow> 
    those (map (map_option \<mu> o var\<^sub>t_type \<Gamma>) ts) = Some ts' \<Longrightarrow> 
      typecheck\<^sub>c\<^sub>v \<Gamma> F ((x, ts) # cts) (\<Gamma>\<^sub>v(x \<mapsto> (ts', \<mu> F)))"

fun typecheck\<^sub>c\<^sub>t_arg :: "static_environment \<Rightarrow> name \<Rightarrow> name \<Rightarrow> funct option" where
  "typecheck\<^sub>c\<^sub>t_arg \<Gamma> tn t = (if t = tn then Some Id else map_option (K o \<mu>) (var\<^sub>t_type \<Gamma> t))"

primrec typecheck\<^sub>c\<^sub>t :: "static_environment \<Rightarrow> name \<Rightarrow> name \<times> name list \<Rightarrow> funct option" where
  "typecheck\<^sub>c\<^sub>t \<Gamma> tn (x, ts) = 
    map_option (\<lambda>fs. foldr (op \<Otimes>) fs (K \<one>)) (those (map (typecheck\<^sub>c\<^sub>t_arg \<Gamma> tn) ts))"

definition typecheck\<^sub>c\<^sub>t\<^sub>s :: "static_environment \<Rightarrow> name \<Rightarrow> (name \<times> name list) list \<Rightarrow> funct option" 
    where
  "typecheck\<^sub>c\<^sub>t\<^sub>s \<Gamma> x cts = 
    map_option (\<lambda>fs. foldr (op \<Oplus>) fs (K \<zero>)) (those (map (typecheck\<^sub>c\<^sub>t \<Gamma> x) cts))"

inductive typecheck\<^sub>d\<^sub>t :: "static_environment \<Rightarrow> name \<Rightarrow> (name \<times> name list) list \<Rightarrow> 
    static_environment \<Rightarrow> bool" where
  tcdt [simp]: "typecheck\<^sub>c\<^sub>t\<^sub>s \<Gamma> n cts = Some F \<Longrightarrow> typecheck\<^sub>c\<^sub>e \<Gamma> F cts \<Gamma>\<^sub>e \<Longrightarrow> 
    typecheck\<^sub>c\<^sub>v \<Gamma> F cts \<Gamma>\<^sub>v \<Longrightarrow> 
      typecheck\<^sub>d\<^sub>t \<Gamma> n cts \<lparr> var\<^sub>e_type = \<Gamma>\<^sub>e, var\<^sub>v_type = \<Gamma>\<^sub>v, var\<^sub>t_type = [n \<mapsto> F] \<rparr>"

inductive typecheck_decl :: "static_environment \<Rightarrow> decl \<Rightarrow> static_environment \<Rightarrow> bool" 
    (infix "\<Turnstile> _ :" 60) where
  tcd_type [simp]: "typecheck\<^sub>d\<^sub>t \<Gamma> x cts \<Gamma>' \<Longrightarrow> \<Gamma> \<Turnstile> TypeDecl x cts : combine\<^sub>s \<Gamma> \<Gamma>'"
| tcd_val [simp]: "\<Gamma> \<turnstile> v : t \<Longrightarrow> \<Gamma> \<Turnstile> ValDecl x v : extend\<^sub>v\<^sub>s x ([], t) \<Gamma>"
| tcd_expr [simp]: "\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<Turnstile> ExprDecl x e : extend\<^sub>e\<^sub>s x (t\<^sub>1, t\<^sub>2) \<Gamma>"

inductive_cases [elim]: "\<Gamma> \<Turnstile> TypeDecl x F : \<Gamma>'"
inductive_cases [elim]: "\<Gamma> \<Turnstile> ValDecl x v : \<Gamma>'"
inductive_cases [elim]: "\<Gamma> \<Turnstile> ExprDecl x e : \<Gamma>'"

inductive typecheck_decls :: "static_environment \<Rightarrow> decl list \<Rightarrow> static_environment \<Rightarrow> bool" 
    (infix "\<Turnstile> _ ::" 60) where
  tcd_nil [simp]: "\<Gamma> \<Turnstile> [] :: \<Gamma>"
| tcd_cons [simp]: "\<Gamma> \<Turnstile> \<delta> : \<Gamma>' \<Longrightarrow> binders\<^sub>d \<delta> \<inter> domain\<^sub>s \<Gamma> = {} \<Longrightarrow> \<Gamma>' \<Turnstile> \<Delta> :: \<Gamma>'' \<Longrightarrow> 
    \<Gamma> \<Turnstile> \<delta> # \<Delta> :: \<Gamma>''"

inductive_cases [elim]: "\<Gamma> \<Turnstile> [] :: \<Gamma>'"
inductive_cases [elim]: "\<Gamma> \<Turnstile> \<delta> # \<Lambda> :: \<Gamma>'"

inductive typecheck_prog :: "prog \<Rightarrow> static_environment \<Rightarrow> type \<Rightarrow> bool" (infix "\<TTurnstile> _ \<rightarrow>" 60) where
  tcp_prog [simp]: "empty_static \<Turnstile> \<Delta> :: \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> v : t\<^sub>1 \<Longrightarrow> 
    Prog \<Delta> e v \<TTurnstile> \<Gamma> \<rightarrow> t\<^sub>2"

inductive_cases [elim]: "Prog \<Delta> e v \<TTurnstile> \<Gamma> \<rightarrow> t"

(* useful properties *)

lemma [simp]: "var\<^sub>e_type (extend\<^sub>e\<^sub>s x (t\<^sub>1, t\<^sub>2) \<Gamma>) = (var\<^sub>e_type \<Gamma>)(x \<mapsto> (t\<^sub>1, t\<^sub>2))"
  by (simp add: extend\<^sub>e\<^sub>s_def)

lemma [simp]: "var\<^sub>v_type (extend\<^sub>e\<^sub>s x (t\<^sub>1, t\<^sub>2) \<Gamma>) = var\<^sub>v_type \<Gamma>"
  by (simp add: extend\<^sub>e\<^sub>s_def)

lemma [simp]: "var\<^sub>t_type (extend\<^sub>e\<^sub>s x (t\<^sub>1, t\<^sub>2) \<Gamma>) = var\<^sub>t_type \<Gamma>"
  by (simp add: extend\<^sub>e\<^sub>s_def)

lemma [simp]: "var\<^sub>v_type (extend\<^sub>v\<^sub>s x t \<Gamma>) = (var\<^sub>v_type \<Gamma>)(x \<mapsto> t)"
  by (simp add: extend\<^sub>v\<^sub>s_def)

lemma [simp]: "var\<^sub>e_type (extend\<^sub>v\<^sub>s x t \<Gamma>) = var\<^sub>e_type \<Gamma>"
  by (simp add: extend\<^sub>v\<^sub>s_def)

lemma [simp]: "var\<^sub>t_type (extend\<^sub>v\<^sub>s x t \<Gamma>) = var\<^sub>t_type \<Gamma>"
  by (simp add: extend\<^sub>v\<^sub>s_def)

lemma [simp]: "\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> x \<notin> domain\<^sub>s \<Gamma> \<Longrightarrow> extend\<^sub>e\<^sub>s x (t\<^sub>1', t\<^sub>2') \<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2"
  and [simp]: "\<Gamma> \<turnstile> v : t \<Longrightarrow> x \<notin> domain\<^sub>s \<Gamma> \<Longrightarrow> extend\<^sub>e\<^sub>s x (t\<^sub>1', t\<^sub>2') \<Gamma> \<turnstile> v : t"
  proof (induction \<Gamma> e t\<^sub>1 t\<^sub>2 and \<Gamma> v t rule: typecheck\<^sub>e_typecheck\<^sub>v.inducts) 
  case (tc_var \<Gamma> y t\<^sub>1 t\<^sub>2)
    moreover hence "x \<noteq> y" by (auto simp add: domain\<^sub>s_def)
    ultimately show ?case by simp
  qed (simp_all add: extend\<^sub>e\<^sub>s_def)

lemma [simp]: "\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> x \<notin> domain\<^sub>s \<Gamma> \<Longrightarrow> extend\<^sub>v\<^sub>s x t' \<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2"
  and [simp]: "\<Gamma> \<turnstile> v : t \<Longrightarrow> x \<notin> domain\<^sub>s \<Gamma> \<Longrightarrow> extend\<^sub>v\<^sub>s x t' \<Gamma> \<turnstile> v : t"
  by (induction \<Gamma> e t\<^sub>1 t\<^sub>2 and \<Gamma> v t rule: typecheck\<^sub>e_typecheck\<^sub>v.inducts) simp_all

(* static uniqueness *)

(* not actually true! fix once we have polymorphism *)
lemma unique_typechecking\<^sub>e [elim]: "\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> e : t\<^sub>1' \<rightarrow> t\<^sub>2' \<Longrightarrow> t\<^sub>1 = t\<^sub>1' \<and> t\<^sub>2 = t\<^sub>2'"
  and unique_typechecking\<^sub>v [elim]: "\<Gamma> \<turnstile> v : t \<Longrightarrow> \<Gamma> \<turnstile> v : t' \<Longrightarrow> t = t'"
  by (induction \<Gamma> e t\<^sub>1 t\<^sub>2 and \<Gamma> v t rule: typecheck\<^sub>e_typecheck\<^sub>v.inducts) simp_all

lemma unique_typechecking\<^sub>c\<^sub>e [elim]: "typecheck\<^sub>c\<^sub>e \<Gamma> F cts \<Gamma>\<^sub>e \<Longrightarrow> typecheck\<^sub>c\<^sub>e \<Gamma> F cts \<Gamma>\<^sub>e' \<Longrightarrow> \<Gamma>\<^sub>e = \<Gamma>\<^sub>e'"
  proof (induction \<Gamma> F cts \<Gamma>\<^sub>e arbitrary: \<Gamma>\<^sub>e' rule: typecheck\<^sub>c\<^sub>e.induct)
  case (tcce_nil \<Gamma> F)
    thus ?case 
      by (induction \<Gamma> F "[]::(name \<times> name list) list" \<Gamma>\<^sub>e' rule: typecheck\<^sub>c\<^sub>e.induct) simp_all
  next case (tcce_cons \<Gamma> F cts \<Gamma>\<^sub>e ts ts' x)
    with tcce_cons(4) show ?case 
      by (induction \<Gamma> F "(x, ts) # cts" \<Gamma>\<^sub>e' rule: typecheck\<^sub>c\<^sub>e.induct) simp_all
  qed

lemma unique_typechecking\<^sub>c\<^sub>v [elim]: "typecheck\<^sub>c\<^sub>v \<Gamma> F cts \<Gamma>\<^sub>v \<Longrightarrow> typecheck\<^sub>c\<^sub>v \<Gamma> F cts \<Gamma>\<^sub>v' \<Longrightarrow> \<Gamma>\<^sub>v = \<Gamma>\<^sub>v'"
  proof (induction \<Gamma> F cts \<Gamma>\<^sub>v arbitrary: \<Gamma>\<^sub>v' rule: typecheck\<^sub>c\<^sub>v.induct)
  case (tccv_nil \<Gamma> F)
    thus ?case 
      by (induction \<Gamma> F "[]::(name \<times> name list) list" \<Gamma>\<^sub>v' rule: typecheck\<^sub>c\<^sub>v.induct) simp_all
  next case (tccv_cons \<Gamma> F cts \<Gamma>\<^sub>v ts ts' x)
    with tccv_cons(4) show ?case 
      by (induction \<Gamma> F "(x, ts) # cts" \<Gamma>\<^sub>v' rule: typecheck\<^sub>c\<^sub>v.induct) simp_all
  qed

lemma unique_typechecking\<^sub>d\<^sub>t [elim]: "typecheck\<^sub>d\<^sub>t \<Gamma> x cts \<Gamma>' \<Longrightarrow> typecheck\<^sub>d\<^sub>t \<Gamma> x cts \<Gamma>'' \<Longrightarrow> \<Gamma>' = \<Gamma>''"
  proof (induction \<Gamma> x cts \<Gamma>' rule: typecheck\<^sub>d\<^sub>t.induct)
  case (tcdt \<Gamma> x cts F \<Gamma>\<^sub>e \<Gamma>\<^sub>v)
    with tcdt(4) show ?case
      by (induction \<Gamma> x cts \<Gamma>'' rule: typecheck\<^sub>d\<^sub>t.induct)
         (simp, metis unique_typechecking\<^sub>c\<^sub>e unique_typechecking\<^sub>c\<^sub>v)
  qed

lemma [elim]: "\<Gamma> \<Turnstile> \<delta> : \<Gamma>' \<Longrightarrow> \<Gamma> \<Turnstile> \<delta> : \<Gamma>'' \<Longrightarrow> \<Gamma>' = \<Gamma>''"
  proof (induction \<Gamma> \<delta> \<Gamma>' rule: typecheck_decl.induct)
  case (tcd_expr \<Gamma> e t\<^sub>1 t\<^sub>2 x)
    with tcd_expr(2) show ?case 
      by (induction \<Gamma> "ExprDecl x e" \<Gamma>'' rule: typecheck_decl.induct) (metis unique_typechecking\<^sub>e)
  next case (tcd_val \<Gamma> v t x)
    with tcd_val(2) show ?case
      by (induction \<Gamma> "ValDecl x v" \<Gamma>'' rule: typecheck_decl.induct) (metis unique_typechecking\<^sub>v)
  next case (tcd_type \<Gamma> x cts \<Gamma>')
    with tcd_type(2) show ?case
      by (induction \<Gamma> "TypeDecl x cts" \<Gamma>'' rule: typecheck_decl.induct) 
         (metis unique_typechecking\<^sub>d\<^sub>t)
  qed

end
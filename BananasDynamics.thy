theory BananasDynamics
imports BananasStatics
begin

record dynamic_environment = 
  var\<^sub>e_bind :: "name \<rightharpoonup> expr" 
  var\<^sub>v_bind :: "name \<rightharpoonup> val list \<Rightarrow> val" 
  var\<^sub>t_bind :: "name \<rightharpoonup> funct"

definition empty_dynamic :: dynamic_environment where
  "empty_dynamic = \<lparr> var\<^sub>e_bind = Map.empty, var\<^sub>v_bind = Map.empty, var\<^sub>t_bind = Map.empty \<rparr>"

definition extend\<^sub>e\<^sub>d :: "name \<Rightarrow> expr \<Rightarrow> dynamic_environment \<Rightarrow> dynamic_environment" where
  "extend\<^sub>e\<^sub>d x t \<Lambda> = \<Lambda>\<lparr> var\<^sub>e_bind := var\<^sub>e_bind \<Lambda>(x \<mapsto> t) \<rparr>"

definition extend\<^sub>v\<^sub>d :: "name \<Rightarrow> (val list \<Rightarrow> val) \<Rightarrow> dynamic_environment \<Rightarrow> dynamic_environment" 
    where
  "extend\<^sub>v\<^sub>d x t \<Lambda> = \<Lambda>\<lparr> var\<^sub>v_bind := var\<^sub>v_bind \<Lambda>(x \<mapsto> t) \<rparr>"

definition combine\<^sub>d :: "dynamic_environment \<Rightarrow> dynamic_environment \<Rightarrow> dynamic_environment" where
  "combine\<^sub>d \<Lambda> \<Lambda>' = \<lparr> 
      var\<^sub>e_bind = var\<^sub>e_bind \<Lambda> ++ var\<^sub>e_bind \<Lambda>', 
      var\<^sub>v_bind = var\<^sub>v_bind \<Lambda> ++ var\<^sub>v_bind \<Lambda>', 
      var\<^sub>t_bind = var\<^sub>t_bind \<Lambda> ++ var\<^sub>t_bind \<Lambda>' \<rparr>"

definition domain\<^sub>d :: "dynamic_environment \<Rightarrow> name set" where
  "domain\<^sub>d \<Lambda> = dom (var\<^sub>e_bind \<Lambda>) \<union> dom (var\<^sub>v_bind \<Lambda>) \<union> dom (var\<^sub>t_bind \<Lambda>)"

definition typecheck_env\<^sub>e :: "static_environment \<Rightarrow> (name \<rightharpoonup> (type \<times> type)) \<Rightarrow> (name \<rightharpoonup> expr) \<Rightarrow> 
    bool" where
  "typecheck_env\<^sub>e \<Gamma> \<Gamma>\<^sub>e \<Lambda>\<^sub>e = (dom \<Gamma>\<^sub>e = dom \<Lambda>\<^sub>e \<and> 
    (\<forall>x t\<^sub>1 t\<^sub>2. \<Gamma>\<^sub>e x = Some (t\<^sub>1, t\<^sub>2) \<longrightarrow> (\<exists>e. \<Lambda>\<^sub>e x = Some e \<and> \<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2)))"

definition typecheck_env\<^sub>v :: "static_environment \<Rightarrow> (name \<rightharpoonup> (type list \<times> type)) \<Rightarrow> 
    (name \<rightharpoonup> val list \<Rightarrow> val) \<Rightarrow> bool" where
  "typecheck_env\<^sub>v \<Gamma> \<Gamma>\<^sub>v \<Lambda>\<^sub>v = (dom \<Gamma>\<^sub>v = dom \<Lambda>\<^sub>v \<and> 
      (\<forall>x ts t. \<Gamma>\<^sub>v x = Some (ts, t) \<longrightarrow> (\<forall>vs. length vs = length ts \<longrightarrow> 
        (\<forall>i < length vs. \<Gamma> \<turnstile> vs ! i : ts ! i) \<longrightarrow> (\<exists>v. \<Lambda>\<^sub>v x = Some v \<and> \<Gamma> \<turnstile> v vs : t))))"

definition typecheck_environment :: "static_environment \<Rightarrow> dynamic_environment \<Rightarrow> bool" 
    (infix "\<tturnstile>" 60) where
  "\<Gamma> \<tturnstile> \<Lambda> = (var\<^sub>t_type \<Gamma> = var\<^sub>t_bind \<Lambda> \<and> typecheck_env\<^sub>e \<Gamma> (var\<^sub>e_type \<Gamma>) (var\<^sub>e_bind \<Lambda>) \<and> 
    typecheck_env\<^sub>v \<Gamma> (var\<^sub>v_type \<Gamma>) (var\<^sub>v_bind \<Lambda>))"

fun apply_functor_expr :: "expr \<Rightarrow> funct \<Rightarrow> expr" (infixl "\<bullet>" 75) where
  "e \<bullet> Id = e"
| "e \<bullet> K t = \<epsilon>"
| "e \<bullet> f\<^sub>1 \<Otimes> f\<^sub>2 = (e \<bullet> f\<^sub>1) \<parallel> (e \<bullet> f\<^sub>2)"
| "e \<bullet> f\<^sub>1 \<Oplus> f\<^sub>2 = (e \<bullet> f\<^sub>1) \<bar> (e \<bullet> f\<^sub>2)"

inductive evaluate :: "dynamic_environment \<Rightarrow> expr \<Rightarrow> val \<Rightarrow> expr \<Rightarrow> val \<Rightarrow> bool" 
    (infix "\<turnstile> _ \<cdot> _ \<leadsto> _ \<cdot>" 60) where
  ev_con [simp]: "\<Lambda> \<turnstile> \<kappa> v\<^sub>1 \<cdot> v\<^sub>2 \<leadsto> \<epsilon> \<cdot> v\<^sub>1"
| ev_comp1 [simp]: "\<Lambda> \<turnstile> g \<cdot> v \<leadsto> g' \<cdot> v' \<Longrightarrow> \<Lambda> \<turnstile> (f \<cdot> g) \<cdot> v \<leadsto> (f \<cdot> g') \<cdot> v'"
| ev_comp2 [simp]: "\<Lambda> \<turnstile> (f \<cdot> \<epsilon>) \<cdot> v \<leadsto> f \<cdot> v"
| ev_fst [simp]: "\<Lambda> \<turnstile> \<pi>\<^sub>1 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> \<epsilon> \<cdot> v\<^sub>1"
| ev_snd [simp]: "\<Lambda> \<turnstile> \<pi>\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> \<epsilon> \<cdot> v\<^sub>2"
| ev_pair1 [simp]: "\<Lambda> \<turnstile> f\<^sub>1 \<cdot> v\<^sub>1 \<leadsto> f\<^sub>1' \<cdot> v\<^sub>1' \<Longrightarrow> 
    \<Lambda> \<turnstile> f\<^sub>1 \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> f\<^sub>1' \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1' v\<^sub>2"
| ev_pair2 [simp]: "\<Lambda> \<turnstile> f\<^sub>2 \<cdot> v\<^sub>2 \<leadsto> f\<^sub>2' \<cdot> v\<^sub>2' \<Longrightarrow> 
    \<Lambda> \<turnstile> \<epsilon> \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<leadsto> \<epsilon> \<parallel> f\<^sub>2' \<cdot> PairV v\<^sub>1 v\<^sub>2'"
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
| ev_inj [simp]: "\<Lambda> \<turnstile> \<succ>\<^bsub>n\<^esub> \<cdot> v \<leadsto> \<epsilon> \<cdot> InjV n v"
(* Should have n = m, but makes progress harder. Also, typechecking guarantees it.  *)
| ev_outj [simp]: "\<Lambda> \<turnstile> \<prec>\<^bsub>n\<^esub> \<cdot> InjV m v \<leadsto> \<epsilon> \<cdot> v" 
| ev_cata [simp]: "var\<^sub>t_bind \<Lambda> n = Some F \<Longrightarrow> \<Lambda> \<turnstile> \<lparr> f \<rparr>\<^bsub>n\<^esub> \<cdot> v \<leadsto> (f \<cdot> \<lparr> f \<rparr>\<^bsub>n\<^esub> \<bullet> F \<cdot> \<prec>\<^bsub>n\<^esub>) \<cdot> v"
| ev_ana [simp]: "var\<^sub>t_bind \<Lambda> n = Some F \<Longrightarrow> \<Lambda> \<turnstile> \<lbrakk> f \<rbrakk>\<^bsub>n\<^esub> \<cdot> v \<leadsto> (\<succ>\<^bsub>n\<^esub> \<cdot> \<lbrakk> f \<rbrakk>\<^bsub>n\<^esub> \<bullet> F \<cdot> f) \<cdot> v"
| ev_var [simp]: "var\<^sub>e_bind \<Lambda> x = Some e \<Longrightarrow> \<Lambda> \<turnstile> Var x \<cdot> v \<leadsto> e \<cdot> v"

primrec right_inject :: "nat \<Rightarrow> expr" where
  "right_inject 0 = \<iota>\<^sub>l"
| "right_inject (Suc x) = \<iota>\<^sub>r \<cdot> right_inject x"

fun assemble_context\<^sub>c\<^sub>e :: "name \<Rightarrow> nat \<Rightarrow> (name \<times> name list) list \<Rightarrow> (name \<rightharpoonup> expr)" where
  "assemble_context\<^sub>c\<^sub>e n depth [] = Map.empty"
| "assemble_context\<^sub>c\<^sub>e n depth ((x, t) # cts) = 
    (assemble_context\<^sub>c\<^sub>e n (Suc depth) cts)(x \<mapsto> \<succ>\<^bsub>n\<^esub> \<cdot> right_inject depth)"

fun assemble_context\<^sub>c\<^sub>v :: "name \<Rightarrow> (name \<times> name list) list \<Rightarrow> (name \<rightharpoonup> val list \<Rightarrow> val)" where
  "assemble_context\<^sub>c\<^sub>v n [] = Map.empty"
| "assemble_context\<^sub>c\<^sub>v n ((x, ts) # cts) = (assemble_context\<^sub>c\<^sub>v n cts)(x \<mapsto> \<lambda>vs. foldr PairV vs UnitV)"

primrec assemble_context' :: "static_environment \<Rightarrow> decl \<Rightarrow> dynamic_environment" where
  "assemble_context' \<Gamma> (TypeDecl x cts) = \<lparr> 
    var\<^sub>e_bind = assemble_context\<^sub>c\<^sub>e x 0 cts, 
    var\<^sub>v_bind = assemble_context\<^sub>c\<^sub>v x cts, 
    var\<^sub>t_bind = [x \<mapsto> the (typecheck\<^sub>c\<^sub>t\<^sub>s \<Gamma> x cts)] \<rparr>" (* TODO get rid of "the" *)
| "assemble_context' \<Gamma> (ValDecl x v) = empty_dynamic \<lparr> var\<^sub>v_bind := [x \<mapsto> \<lambda>x. v] \<rparr>"
| "assemble_context' \<Gamma> (ExprDecl x e) = empty_dynamic \<lparr> var\<^sub>e_bind := [x \<mapsto> e] \<rparr>"

inductive assemble_context :: "static_environment \<Rightarrow> decl list \<Rightarrow> dynamic_environment \<Rightarrow> bool" where
  [simp]: "assemble_context \<Gamma> [] empty_dynamic"
| [simp]: "\<Gamma> \<Turnstile> \<delta> : \<Gamma>' \<Longrightarrow> assemble_context \<Gamma>' \<Delta> \<Lambda> \<Longrightarrow> 
    assemble_context \<Gamma> (\<delta> # \<Delta>) (combine\<^sub>d (assemble_context' \<Gamma> \<delta>) \<Lambda>)"

inductive_cases [elim]: "assemble_context \<Gamma> [] \<Lambda>"
inductive_cases [elim]: "assemble_context \<Gamma> (\<delta> # \<Delta>) \<Lambda>"

primrec is_completed :: "prog \<Rightarrow> bool" where
  "is_completed (Prog \<Delta> e v) = (e = \<epsilon>)"

inductive evaluate_prog :: "prog \<Rightarrow> prog \<Rightarrow> bool" (infix "\<leadsto>" 60) where
  ev_prog [simp]: "assemble_context empty_static \<Delta> \<Lambda> \<Longrightarrow> \<Lambda> \<turnstile> e \<cdot> v \<leadsto> e' \<cdot> v' \<Longrightarrow> 
    Prog \<Delta> e v \<leadsto> Prog \<Delta> e' v'"

inductive_cases [elim]: "Prog \<Delta> e v \<leadsto> \<Pi>"

(* useful properties *)

lemma [simp]: "var\<^sub>e_bind (extend\<^sub>e\<^sub>d x e \<Lambda>) = (var\<^sub>e_bind \<Lambda>)(x \<mapsto> e)"
  by (simp add: extend\<^sub>e\<^sub>d_def)

lemma [simp]: "var\<^sub>v_bind (extend\<^sub>e\<^sub>d x e \<Lambda>) = var\<^sub>v_bind \<Lambda>"
  by (simp add: extend\<^sub>e\<^sub>d_def)

lemma [simp]: "var\<^sub>t_bind (extend\<^sub>e\<^sub>d x e \<Lambda>) = var\<^sub>t_bind \<Lambda>"
  by (simp add: extend\<^sub>e\<^sub>d_def)

lemma [simp]: "var\<^sub>v_bind (extend\<^sub>v\<^sub>d x v \<Lambda>) = (var\<^sub>v_bind \<Lambda>)(x \<mapsto> v)"
  by (simp add: extend\<^sub>v\<^sub>d_def)

lemma [simp]: "var\<^sub>e_bind (extend\<^sub>v\<^sub>d x v \<Lambda>) = var\<^sub>e_bind \<Lambda>"
  by (simp add: extend\<^sub>v\<^sub>d_def)

lemma [simp]: "var\<^sub>t_bind (extend\<^sub>v\<^sub>d x v \<Lambda>) = var\<^sub>t_bind \<Lambda>"
  by (simp add: extend\<^sub>v\<^sub>d_def)

end
theory BananasSafety
imports BananasDynamics
begin

(* canonical values *)

lemma canonical_unit: "\<Gamma> \<turnstile> v : \<one> \<Longrightarrow> v = UnitV"
  by (cases \<Gamma> v \<one> rule: typecheck\<^sub>v.cases) simp_all

lemma canonical_prod: "\<Gamma> \<turnstile> v : t\<^sub>1 \<otimes> t\<^sub>2 \<Longrightarrow> \<exists>v\<^sub>1 v\<^sub>2. (\<Gamma> \<turnstile> v\<^sub>1 : t\<^sub>1) \<and> (\<Gamma> \<turnstile> v\<^sub>2 : t\<^sub>2) \<and> v = PairV v\<^sub>1 v\<^sub>2"
  by (cases \<Gamma> v "t\<^sub>1 \<otimes> t\<^sub>2" rule: typecheck\<^sub>v.cases) simp_all

lemma canonical_sum: "\<Gamma> \<turnstile> v : t\<^sub>1 \<oplus> t\<^sub>2 \<Longrightarrow> 
    \<exists>v'. ((\<Gamma> \<turnstile> v' : t\<^sub>1) \<and> v = InlV v') \<or> ((\<Gamma> \<turnstile> v' : t\<^sub>2) \<and> v = InrV v')"
  by (cases \<Gamma> v "t\<^sub>1 \<oplus> t\<^sub>2" rule: typecheck\<^sub>v.cases) simp_all

lemma canonical_arrow: "\<Gamma> \<turnstile> v : t\<^sub>1 \<hookrightarrow> t\<^sub>2 \<Longrightarrow> \<exists>e. (\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2) \<and> v = FunV e"
  by (cases \<Gamma> v "t\<^sub>1 \<hookrightarrow> t\<^sub>2" rule: typecheck\<^sub>v.cases) simp_all

lemma canonical_mu: "\<Gamma> \<turnstile> v : \<mu> F \<Longrightarrow> 
    \<exists>v' n. (\<Gamma> \<turnstile> v' : \<mu> F \<star> F) \<and> v = InjV n v' \<and> var\<^sub>t_type \<Gamma> n = Some F"
  by (cases \<Gamma> v "\<mu> F" rule: typecheck\<^sub>v.cases) simp_all

(* environment lemmas *)

lemma [simp]: "combine\<^sub>d empty_dynamic \<Lambda> = \<Lambda>"
  by (simp add: combine\<^sub>d_def empty_dynamic_def)

lemma [simp]: "combine\<^sub>d \<Lambda> empty_dynamic = \<Lambda>"
  by (simp add: combine\<^sub>d_def empty_dynamic_def)

lemma [simp]: "combine\<^sub>d (combine\<^sub>d \<Lambda>\<^sub>1 \<Lambda>\<^sub>2) \<Lambda>\<^sub>3 = combine\<^sub>d \<Lambda>\<^sub>1 (combine\<^sub>d \<Lambda>\<^sub>2 \<Lambda>\<^sub>3)"
  by (simp add: combine\<^sub>d_def empty_dynamic_def)

lemma [simp]: "\<lparr>var\<^sub>e_bind = var\<^sub>e_bind \<Lambda>(x \<mapsto> e), var\<^sub>t_bind = var\<^sub>t_bind \<Lambda>\<rparr> = extend\<^sub>e\<^sub>d x e \<Lambda>"
  by (simp add: extend\<^sub>e\<^sub>d_def)






lemma tce_right_inject_helper [simp]: "typecheck_env\<^sub>e \<lparr>var\<^sub>e_type = \<Gamma>\<^sub>e', var\<^sub>t_type = [x \<mapsto> F]\<rparr> 
  \<Gamma>\<^sub>e' (assemble_context\<^sub>c\<^sub>e x (Suc (length Fs)) cts) \<Longrightarrow> x \<notin> domain\<^sub>s \<Gamma> \<Longrightarrow> y \<notin> domain\<^sub>s \<Gamma> \<Longrightarrow> 
    F = foldr op \<Oplus> (Fs @ [ctor_funct ts'']) F' \<Longrightarrow> 
      typecheck_env\<^sub>e \<lparr>var\<^sub>e_type = \<Gamma>\<^sub>e'(y \<mapsto> (ctor_type ts', \<mu> F)), var\<^sub>t_type = [x \<mapsto> F]\<rparr> 
        (\<Gamma>\<^sub>e'(y \<mapsto> (ctor_type ts', \<mu> F))) 
          (assemble_context\<^sub>c\<^sub>e x (Suc (length Fs)) cts(y \<mapsto> \<succ>\<^bsub>x\<^esub> \<cdot> right_inject (length Fs)))"
  proof (unfold typecheck_env\<^sub>e_def, rule, simp, rule, rule, rule, rule)
    fix z t\<^sub>1 t\<^sub>2
    assume "dom \<Gamma>\<^sub>e' = dom (assemble_context\<^sub>c\<^sub>e x (Suc (length Fs)) cts) \<and>
       (\<forall>xa t\<^sub>1 t\<^sub>2. \<Gamma>\<^sub>e' xa = Some (t\<^sub>1, t\<^sub>2) \<longrightarrow> 
          (\<exists>e. assemble_context\<^sub>c\<^sub>e x (Suc (length Fs)) cts xa = Some e \<and>
            \<lparr>var\<^sub>e_type = \<Gamma>\<^sub>e', var\<^sub>t_type = [x \<mapsto> F]\<rparr> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2))"
       and "x \<notin> domain\<^sub>s \<Gamma>"
       and "y \<notin> domain\<^sub>s \<Gamma>"
       and "F = foldr op \<Oplus> (Fs @ [BananasStatics.ctor_funct ts'']) F'"
       and "(\<Gamma>\<^sub>e'(y \<mapsto> (BananasStatics.ctor_type ts', \<mu> F))) z = Some (t\<^sub>1, t\<^sub>2)"
    thus "\<exists>e. (assemble_context\<^sub>c\<^sub>e x (Suc (length Fs)) cts(y \<mapsto> \<succ>\<^bsub>x\<^esub> \<cdot> right_inject (length Fs))) z = 
      Some e \<and> \<lparr>var\<^sub>e_type = \<Gamma>\<^sub>e'(y \<mapsto> (BananasStatics.ctor_type ts', \<mu> F)), var\<^sub>t_type = [x \<mapsto> F]\<rparr> \<turnstile> 
        e : t\<^sub>1 \<rightarrow> t\<^sub>2"
      proof (cases "z = y")
      case True
        thus ?thesis by simp
      next case False
        thus ?thesis by simp
      qed
  qed

lemma [simp]: "typecheck\<^sub>c\<^sub>t\<^sub>s \<Gamma> x cts = Some F \<Longrightarrow> 
  typecheck\<^sub>c\<^sub>e \<Gamma> (foldr (op \<Oplus>) Fs F) cts \<Gamma>\<^sub>e \<Longrightarrow> 
    x \<notin> domain\<^sub>s \<Gamma> \<Longrightarrow> fst ` set cts \<inter> domain\<^sub>s \<Gamma> = {} \<Longrightarrow> 
      typecheck_env\<^sub>e \<lparr>var\<^sub>e_type = \<Gamma>\<^sub>e, var\<^sub>t_type = [x \<mapsto> foldr (op \<Oplus>) Fs F]\<rparr> \<Gamma>\<^sub>e 
        (assemble_context\<^sub>c\<^sub>e x (length Fs) cts)"
  proof (induction x "length Fs" cts arbitrary: \<Gamma>\<^sub>e F Fs rule: assemble_context\<^sub>c\<^sub>e.induct)
  case 1
    thus ?case using typecheck_env\<^sub>e_def by fastforce 
  next case (2 x y ts cts)
    then obtain \<Gamma>\<^sub>e' ts' where G: "\<Gamma>\<^sub>e = \<Gamma>\<^sub>e'(y \<mapsto> (ctor_type ts', \<mu> (foldr (op \<Oplus>) Fs F))) \<and> 
      typecheck\<^sub>c\<^sub>e \<Gamma> (foldr (op \<Oplus>) Fs F) cts \<Gamma>\<^sub>e' \<and> 
        those (map (map_option \<mu> o var\<^sub>t_type \<Gamma>) ts) = Some ts'" by fastforce
    from 2 obtain ts'' F' where F: "those (map (typecheck\<^sub>c\<^sub>t_arg \<Gamma> x) ts) = Some ts'' \<and> 
      typecheck\<^sub>c\<^sub>t\<^sub>s \<Gamma> x cts = Some F' \<and> ctor_funct ts'' \<Oplus> F' = F" by (metis unfold_tc_cts)
    let ?F = "foldr op \<Oplus> (Fs @ [ctor_funct ts'']) F'"
    from F G have Y: "typecheck\<^sub>c\<^sub>e \<Gamma> ?F  cts \<Gamma>\<^sub>e'" by simp
    have X: "Suc (length Fs) = length (Fs @ [ctor_funct ts''])" by simp
    from 2 have "fst ` set cts \<inter> domain\<^sub>s \<Gamma> = {}" by simp
    with 2 F X Y have "typecheck_env\<^sub>e \<lparr>var\<^sub>e_type = \<Gamma>\<^sub>e', var\<^sub>t_type = [x \<mapsto> ?F]\<rparr> 
      \<Gamma>\<^sub>e' (assemble_context\<^sub>c\<^sub>e x (length (Fs @ [ctor_funct ts''])) cts)" by blast
    hence "typecheck_env\<^sub>e \<lparr>var\<^sub>e_type = \<Gamma>\<^sub>e', var\<^sub>t_type = [x \<mapsto> ?F]\<rparr> 
      \<Gamma>\<^sub>e' (assemble_context\<^sub>c\<^sub>e x (Suc (length Fs)) cts)" by simp
    moreover from 2 have "x \<notin> domain\<^sub>s \<Gamma>" by simp
    moreover from 2 have "y \<notin> domain\<^sub>s \<Gamma>" by simp
    ultimately have "typecheck_env\<^sub>e \<lparr>var\<^sub>e_type = \<Gamma>\<^sub>e'(y \<mapsto> (ctor_type ts', \<mu> ?F)), 
      var\<^sub>t_type = [x \<mapsto> ?F ]\<rparr> (\<Gamma>\<^sub>e'(y \<mapsto> (ctor_type ts', \<mu> ?F)))
        (assemble_context\<^sub>c\<^sub>e x (Suc (length Fs)) cts(y \<mapsto> \<succ>\<^bsub>x\<^esub> \<cdot> right_inject (length Fs)))" 
      by (metis tce_right_inject_helper)
    with G F show ?case by simp
  qed

lemma [simp]: "typecheck\<^sub>c\<^sub>t\<^sub>s \<Gamma> x cts = Some F \<Longrightarrow> typecheck\<^sub>c\<^sub>e \<Gamma> F cts \<Gamma>\<^sub>e \<Longrightarrow> x \<notin> domain\<^sub>s \<Gamma> \<Longrightarrow> 
  fst ` set cts \<inter> domain\<^sub>s \<Gamma> = {} \<Longrightarrow> 
    typecheck_env\<^sub>e \<lparr>var\<^sub>e_type = \<Gamma>\<^sub>e, var\<^sub>t_type = [x \<mapsto> F]\<rparr> \<Gamma>\<^sub>e (assemble_context\<^sub>c\<^sub>e x 0 cts)"
  proof -
    assume "typecheck\<^sub>c\<^sub>t\<^sub>s \<Gamma> x cts = Some F"
       and "x \<notin> domain\<^sub>s \<Gamma>"
       and "fst ` set cts \<inter> domain\<^sub>s \<Gamma> = {}"
    hence "\<And>fs. typecheck\<^sub>c\<^sub>e \<Gamma> (foldr (op \<Oplus>) fs F) cts \<Gamma>\<^sub>e \<Longrightarrow> 
      typecheck_env\<^sub>e \<lparr>var\<^sub>e_type = \<Gamma>\<^sub>e, var\<^sub>t_type = [x \<mapsto> foldr (op \<Oplus>) fs F]\<rparr> \<Gamma>\<^sub>e 
        (assemble_context\<^sub>c\<^sub>e x (length fs) cts)" by simp
    hence "typecheck\<^sub>c\<^sub>e \<Gamma> (foldr (op \<Oplus>) [] F) cts \<Gamma>\<^sub>e \<Longrightarrow> 
      typecheck_env\<^sub>e \<lparr>var\<^sub>e_type = \<Gamma>\<^sub>e, var\<^sub>t_type = [x \<mapsto> foldr (op \<Oplus>) [] F]\<rparr> \<Gamma>\<^sub>e 
        (assemble_context\<^sub>c\<^sub>e x (length []) cts)" by fastforce
    moreover assume "typecheck\<^sub>c\<^sub>e \<Gamma> F cts \<Gamma>\<^sub>e"
    ultimately show "typecheck_env\<^sub>e \<lparr>var\<^sub>e_type = \<Gamma>\<^sub>e, var\<^sub>t_type = [x \<mapsto> F]\<rparr> \<Gamma>\<^sub>e 
      (assemble_context\<^sub>c\<^sub>e x 0 cts)" by simp
  qed

lemma [simp]: "\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<tturnstile> \<Lambda> \<Longrightarrow> x \<notin> domain\<^sub>s \<Gamma> \<Longrightarrow> 
    extend\<^sub>e\<^sub>s x (t\<^sub>1, t\<^sub>2) \<Gamma> \<tturnstile> extend\<^sub>e\<^sub>d x e \<Lambda>"
  using typecheck_environment_def typecheck_env\<^sub>e_def by fastforce

lemma [simp]: "typecheck\<^sub>d\<^sub>t \<Gamma>\<^sub>1 x cts \<Gamma>\<^sub>2 \<Longrightarrow> x \<notin> domain\<^sub>s \<Gamma>\<^sub>1 \<Longrightarrow> fst ` set cts \<inter> domain\<^sub>s \<Gamma>\<^sub>1 = {} \<Longrightarrow> 
    \<Gamma>\<^sub>2 \<tturnstile> \<lparr>var\<^sub>e_bind = assemble_context\<^sub>c\<^sub>e x 0 cts, var\<^sub>t_bind = [x \<mapsto> the (typecheck\<^sub>c\<^sub>t\<^sub>s \<Gamma>\<^sub>1 x cts)]\<rparr>"
  by (induction \<Gamma>\<^sub>1 x cts \<Gamma>\<^sub>2 rule: typecheck\<^sub>d\<^sub>t.induct) (simp_all add: typecheck_environment_def)

lemma [simp]: "typecheck_env\<^sub>e \<Gamma>\<^sub>1 (var\<^sub>e_type \<Gamma>\<^sub>1) (var\<^sub>e_bind \<Lambda>\<^sub>1) \<Longrightarrow> 
  typecheck_env\<^sub>e \<Gamma>\<^sub>2 (var\<^sub>e_type \<Gamma>\<^sub>2) (var\<^sub>e_bind \<Lambda>\<^sub>2) \<Longrightarrow> domain\<^sub>s \<Gamma>\<^sub>1 \<inter> domain\<^sub>s \<Gamma>\<^sub>2 = {} \<Longrightarrow>
    typecheck_env\<^sub>e (combine\<^sub>s \<Gamma>\<^sub>1 \<Gamma>\<^sub>2) (var\<^sub>e_type (combine\<^sub>s \<Gamma>\<^sub>1 \<Gamma>\<^sub>2)) (var\<^sub>e_bind (combine\<^sub>d \<Lambda>\<^sub>1 \<Lambda>\<^sub>2))"
  apply (simp add: typecheck_env\<^sub>e_def)
  by simp

lemma [simp]: "var\<^sub>t_type \<Gamma>\<^sub>1 = var\<^sub>t_bind \<Lambda>\<^sub>1 \<Longrightarrow> var\<^sub>t_type \<Gamma>\<^sub>2 = var\<^sub>t_bind \<Lambda>\<^sub>2 \<Longrightarrow> 
    var\<^sub>t_type (combine\<^sub>s \<Gamma>\<^sub>1 \<Gamma>\<^sub>2) = var\<^sub>t_bind (combine\<^sub>d \<Lambda>\<^sub>1 \<Lambda>\<^sub>2)"
  by (simp add: combine\<^sub>s_def combine\<^sub>d_def)

lemma [simp]: "\<Gamma>\<^sub>1 \<tturnstile> \<Lambda>\<^sub>1 \<Longrightarrow> \<Gamma>\<^sub>2 \<tturnstile> \<Lambda>\<^sub>2 \<Longrightarrow> domain\<^sub>s \<Gamma>\<^sub>1 \<inter> domain\<^sub>s \<Gamma>\<^sub>2 = {} \<Longrightarrow> 
    combine\<^sub>s \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 \<tturnstile> combine\<^sub>d \<Lambda>\<^sub>1 \<Lambda>\<^sub>2"
  by (simp add: typecheck_environment_def)

lemma [simp]: "typecheck\<^sub>c\<^sub>e \<Gamma> F cts \<Gamma>\<^sub>e \<Longrightarrow> dom \<Gamma>\<^sub>e = fst ` set cts"
  by (induction \<Gamma> F cts \<Gamma>\<^sub>e rule: typecheck\<^sub>c\<^sub>e.induct) (auto simp add: Map.dom_if)

lemma [simp]: "typecheck\<^sub>d\<^sub>t \<Gamma>\<^sub>1 x cts \<Gamma>\<^sub>2 \<Longrightarrow> x \<notin> domain\<^sub>s \<Gamma>\<^sub>1 \<Longrightarrow> fst ` set cts \<inter> domain\<^sub>s \<Gamma>\<^sub>1 = {} \<Longrightarrow> 
    domain\<^sub>s \<Gamma>\<^sub>1 \<inter> domain\<^sub>s \<Gamma>\<^sub>2 = {}"
  by (induction \<Gamma>\<^sub>1 x cts \<Gamma>\<^sub>2 rule: typecheck\<^sub>d\<^sub>t.induct) (auto simp add: domain\<^sub>s_def)

lemma [simp]: "\<Gamma>\<^sub>1 \<Turnstile> \<delta> : \<Gamma>\<^sub>2 \<Longrightarrow> \<Gamma>\<^sub>1 \<tturnstile> \<Lambda> \<Longrightarrow> binders\<^sub>d \<delta> \<inter> domain\<^sub>s \<Gamma>\<^sub>1 = {} \<Longrightarrow> 
    \<Gamma>\<^sub>2 \<tturnstile> combine\<^sub>d \<Lambda> (assemble_context' \<Gamma>\<^sub>1 \<delta>)"
  proof (induction \<Gamma>\<^sub>1 \<delta> \<Gamma>\<^sub>2 rule: typecheck_decl.induct)
  case tcd_type
    thus ?case by simp
  qed (simp_all add: combine\<^sub>d_def empty_dynamic_def)

lemma tc_defs_parts [simp]: "\<Gamma> \<Turnstile> \<Delta> :: \<Gamma>' \<Longrightarrow> \<Gamma> \<tturnstile> \<Lambda> \<Longrightarrow> 
    \<exists>\<Lambda>'. assemble_context \<Gamma> \<Delta> \<Lambda>' \<and> \<Gamma>' \<tturnstile> combine\<^sub>d \<Lambda> \<Lambda>'"
  proof (induction \<Gamma> \<Delta> \<Gamma>' arbitrary: \<Lambda> rule: typecheck_decls.induct)  
  case (tcd_nil \<Gamma>)
    hence "assemble_context \<Gamma> [] empty_dynamic \<and> \<Gamma> \<tturnstile> combine\<^sub>d \<Lambda> empty_dynamic" by simp
    thus ?case by fastforce
  next case (tcd_cons \<Gamma>\<^sub>1 \<delta> \<Gamma>\<^sub>2 \<Delta> \<Gamma>\<^sub>3)
    hence "\<Gamma>\<^sub>2 \<tturnstile> combine\<^sub>d \<Lambda> (assemble_context' \<Gamma>\<^sub>1 \<delta>)" by fastforce
    with tcd_cons obtain \<Lambda>\<^sub>3 where "assemble_context \<Gamma>\<^sub>2 \<Delta> \<Lambda>\<^sub>3 \<and> \<Gamma>\<^sub>3 \<tturnstile> 
      combine\<^sub>d (combine\<^sub>d \<Lambda> (assemble_context' \<Gamma>\<^sub>1 \<delta>)) \<Lambda>\<^sub>3" by fastforce
    moreover with tcd_cons have "assemble_context \<Gamma>\<^sub>1 (\<delta> # \<Delta>) (combine\<^sub>d (assemble_context' \<Gamma>\<^sub>1 \<delta>) \<Lambda>\<^sub>3)" 
      by simp
    ultimately show ?case by fastforce
  qed

lemma [simp]: "empty_static \<tturnstile> empty_dynamic" 
  by (simp add: typecheck_environment_def empty_static_def empty_dynamic_def typecheck_env\<^sub>e_def)

lemma [simp]: "empty_static \<Turnstile> \<Delta> :: \<Gamma> \<Longrightarrow>  \<exists>\<Lambda>. assemble_context empty_static \<Delta> \<Lambda> \<and> \<Gamma> \<tturnstile> \<Lambda>"
  proof -
    assume "empty_static \<Turnstile> \<Delta> :: \<Gamma>"
    moreover have "empty_static \<tturnstile> empty_dynamic" by simp
    ultimately obtain \<Lambda> where "assemble_context empty_static \<Delta> \<Lambda> \<and> \<Gamma> \<tturnstile> combine\<^sub>d empty_dynamic \<Lambda>" 
      by (metis tc_defs_parts)
    thus ?thesis by auto
  qed

lemma assemble_defs_parts [simp]: "\<Gamma> \<Turnstile> \<Delta> :: \<Gamma>' \<Longrightarrow> assemble_context \<Gamma> \<Delta> \<Lambda>' \<Longrightarrow> \<Gamma> \<tturnstile> \<Lambda> \<Longrightarrow> 
    \<Gamma>' \<tturnstile> combine\<^sub>d \<Lambda> \<Lambda>'"
  proof (induction \<Gamma> \<Delta> \<Gamma>' arbitrary: \<Lambda> \<Lambda>' rule: typecheck_decls.induct)  
  case (tcd_cons \<Gamma>\<^sub>1 \<delta> \<Gamma>\<^sub>2 \<Delta> \<Gamma>\<^sub>3)
    moreover then obtain \<Gamma>\<^sub>2' \<Lambda>\<^sub>2 where G: "(\<Gamma>\<^sub>1 \<Turnstile> \<delta> : \<Gamma>\<^sub>2') \<and> assemble_context \<Gamma>\<^sub>2' \<Delta> \<Lambda>\<^sub>2 \<and> 
      \<Lambda>' = combine\<^sub>d (assemble_context' \<Gamma>\<^sub>1 \<delta>) \<Lambda>\<^sub>2" by auto
    moreover with tcd_cons have "\<Gamma>\<^sub>2 = \<Gamma>\<^sub>2'" by auto
    moreover from tcd_cons have "\<Gamma>\<^sub>2 \<tturnstile> combine\<^sub>d \<Lambda> (assemble_context' \<Gamma>\<^sub>1 \<delta>)" by simp
    ultimately have "\<Gamma>\<^sub>3 \<tturnstile> combine\<^sub>d (combine\<^sub>d \<Lambda> (assemble_context' \<Gamma>\<^sub>1 \<delta>)) \<Lambda>\<^sub>2" by blast
    with G show ?case by simp
  qed fastforce+

lemma [simp]: "assemble_context empty_static \<Delta> \<Lambda> \<Longrightarrow> empty_static \<Turnstile> \<Delta> :: \<Gamma> \<Longrightarrow> \<Gamma> \<tturnstile> \<Lambda>"
  proof -
    assume "empty_static \<Turnstile> \<Delta> :: \<Gamma>"
       and "assemble_context empty_static \<Delta> \<Lambda>"
    moreover have "empty_static \<tturnstile> empty_dynamic" by simp
    ultimately have "\<Gamma> \<tturnstile> combine\<^sub>d empty_dynamic \<Lambda>" by (metis assemble_defs_parts)
    thus ?thesis by simp
  qed

(* progress *)

theorem expr_progress [simp]: "\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> v : t\<^sub>1 \<Longrightarrow> \<Gamma> \<tturnstile> \<Lambda> \<Longrightarrow> e \<noteq> \<epsilon> \<Longrightarrow> 
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
  next case (tc_inj \<Gamma> n)
    hence "\<Lambda> \<turnstile> \<succ>\<^bsub>n\<^esub> \<cdot> v \<leadsto> \<epsilon> \<cdot> InjV n v" by simp
    thus ?case by fastforce
  next case (tc_outj \<Gamma> n F)
    then obtain v' m where "v = InjV m v' \<and> var\<^sub>t_type \<Gamma> m = Some F" using canonical_mu by blast
    moreover hence "\<Lambda> \<turnstile> \<prec>\<^bsub>n\<^esub> \<cdot> v \<leadsto> \<epsilon> \<cdot> v'" by simp
    ultimately show ?case by fastforce
  next case (tc_cata \<Gamma> n F f t)
    hence "var\<^sub>t_bind \<Lambda> n = Some F" by (simp add: typecheck_environment_def)
    hence "\<Lambda> \<turnstile> \<lparr> f \<rparr>\<^bsub>n\<^esub> \<cdot> v \<leadsto> (f \<cdot> \<lparr> f \<rparr>\<^bsub>n\<^esub> \<bullet> F \<cdot> \<prec>\<^bsub>n\<^esub>) \<cdot> v" by simp
    thus ?case by fastforce
  next case (tc_ana \<Gamma> n F f t)
    hence "var\<^sub>t_bind \<Lambda> n = Some F" by (simp add: typecheck_environment_def)
    hence "\<Lambda> \<turnstile> \<lbrakk> f \<rbrakk>\<^bsub>n\<^esub> \<cdot> v \<leadsto> (\<succ>\<^bsub>n\<^esub> \<cdot> \<lbrakk> f \<rbrakk>\<^bsub>n\<^esub> \<bullet> F \<cdot> f) \<cdot> v" by simp
    thus ?case by fastforce
  next case (tc_var \<Gamma> x t\<^sub>1 t\<^sub>2)
    then obtain e where "var\<^sub>e_bind \<Lambda> x = Some e \<and> \<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2" 
      using typecheck_environment_def typecheck_env\<^sub>e_def by fastforce
    hence "\<Lambda> \<turnstile> Var x \<cdot> v \<leadsto> e \<cdot> v" by simp
    thus ?case by fastforce
  qed simp_all

theorem progress [simp]: "\<Pi> \<TTurnstile> \<Gamma> \<rightarrow> t \<Longrightarrow> is_completed \<Pi> \<or> (\<exists>\<Pi>'. \<Pi> \<leadsto> \<Pi>')"
  proof (induction \<Pi> \<Gamma> t rule: typecheck_prog.induct)
  case (tcp_prog \<Delta> \<Gamma> e t\<^sub>1 t\<^sub>2 v)
    moreover have "empty_static \<tturnstile> empty_dynamic" by simp
    ultimately obtain \<Lambda> where L: "assemble_context empty_static \<Delta> \<Lambda> \<and> \<Gamma> \<tturnstile> \<Lambda>" by fastforce
    thus ?case 
      proof (cases "e = \<epsilon>")
      case False
        with tcp_prog L obtain e' v' where "\<Lambda> \<turnstile> e \<cdot> v \<leadsto> e' \<cdot> v'" by fastforce
        with L have "Prog \<Delta> e v \<leadsto> Prog \<Delta> e' v'" by fastforce
        thus ?thesis by fastforce
      qed simp_all
  qed

(* preservation *)

lemma [simp]: "\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> e \<bullet> F : t\<^sub>1 \<star> F \<rightarrow> t\<^sub>2 \<star> F"
  by (induction e F rule: apply_functor_expr.induct) simp_all

theorem expr_preservation [simp]: "\<Lambda> \<turnstile> e \<cdot> v \<leadsto> e' \<cdot> v' \<Longrightarrow> \<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> 
    \<Gamma> \<turnstile> v : t\<^sub>1 \<Longrightarrow> \<Gamma> \<tturnstile> \<Lambda> \<Longrightarrow> \<exists>t\<^sub>3. (\<Gamma> \<turnstile> e' : t\<^sub>3 \<rightarrow> t\<^sub>2) \<and> (\<Gamma> \<turnstile> v' : t\<^sub>3)"
  proof (induction \<Lambda> e v e' v' arbitrary: t\<^sub>1 t\<^sub>2 rule: evaluate.induct)
  case (ev_con \<Lambda> v\<^sub>1 v\<^sub>2)
    hence "(\<Gamma> \<turnstile> \<epsilon> : t\<^sub>2 \<rightarrow> t\<^sub>2) \<and> \<Gamma> \<turnstile> v\<^sub>1 : t\<^sub>2" by fastforce
    thus ?case by fastforce
  next case (ev_comp1 \<Lambda> g v g' v' f)
    moreover then obtain t\<^sub>3 where "(\<Gamma> \<turnstile> f : t\<^sub>3 \<rightarrow> t\<^sub>2) \<and> \<Gamma> \<turnstile> g : t\<^sub>1 \<rightarrow> t\<^sub>3" by fastforce
    ultimately obtain t\<^sub>4 where "(\<Gamma> \<turnstile> f \<cdot> g' : t\<^sub>4 \<rightarrow> t\<^sub>2) \<and> \<Gamma> \<turnstile> v' : t\<^sub>4" by fastforce
    thus ?case by fastforce
  next case (ev_fst \<Lambda> v\<^sub>1 v\<^sub>2)
    hence "(\<Gamma> \<turnstile> \<epsilon> : t\<^sub>2 \<rightarrow> t\<^sub>2) \<and> \<Gamma> \<turnstile> v\<^sub>1 : t\<^sub>2" by fastforce
    thus ?case by fastforce
  next case (ev_snd \<Lambda> v\<^sub>1 v\<^sub>2)
    hence "(\<Gamma> \<turnstile> \<epsilon> : t\<^sub>2 \<rightarrow> t\<^sub>2) \<and> \<Gamma> \<turnstile> v\<^sub>2 : t\<^sub>2" by fastforce
    thus ?case by fastforce
  next case (ev_pair1 \<Lambda> f\<^sub>1 v\<^sub>1 f\<^sub>1' v\<^sub>1' f\<^sub>2 v\<^sub>2)
    then obtain t\<^sub>1\<^sub>1 t\<^sub>1\<^sub>2 t\<^sub>2\<^sub>1 t\<^sub>2\<^sub>2 t\<^sub>1\<^sub>1' where T: "(\<Gamma> \<turnstile> v\<^sub>1 : t\<^sub>1\<^sub>1) \<and> (\<Gamma> \<turnstile> v\<^sub>2 : t\<^sub>1\<^sub>2) \<and> 
      (\<Gamma> \<turnstile> f\<^sub>1 : t\<^sub>1\<^sub>1 \<rightarrow> t\<^sub>2\<^sub>1) \<and> (\<Gamma> \<turnstile> f\<^sub>2 : t\<^sub>1\<^sub>2 \<rightarrow> t\<^sub>2\<^sub>2) \<and> t\<^sub>1 = t\<^sub>1\<^sub>1 \<otimes> t\<^sub>1\<^sub>2 \<and> t\<^sub>2 = t\<^sub>2\<^sub>1 \<otimes> t\<^sub>2\<^sub>2 \<and> 
        (\<Gamma> \<turnstile> f\<^sub>1' : t\<^sub>1\<^sub>1' \<rightarrow> t\<^sub>2\<^sub>1) \<and> \<Gamma> \<turnstile> v\<^sub>1' : t\<^sub>1\<^sub>1'" by fastforce
    hence "(\<Gamma> \<turnstile> f\<^sub>1' \<parallel> f\<^sub>2 : t\<^sub>1\<^sub>1' \<otimes> t\<^sub>1\<^sub>2 \<rightarrow> t\<^sub>2) \<and> \<Gamma> \<turnstile> PairV v\<^sub>1' v\<^sub>2 : t\<^sub>1\<^sub>1' \<otimes> t\<^sub>1\<^sub>2" by simp
    thus ?case by fastforce
  next case (ev_pair2 \<Lambda> f\<^sub>2 v\<^sub>2 f\<^sub>2' v\<^sub>2' v\<^sub>1)
    then obtain t\<^sub>1\<^sub>1 t\<^sub>1\<^sub>2 t\<^sub>2\<^sub>2 t\<^sub>1\<^sub>2' where T: "(\<Gamma> \<turnstile> v\<^sub>1 : t\<^sub>1\<^sub>1) \<and> (\<Gamma> \<turnstile> v\<^sub>2 : t\<^sub>1\<^sub>2) \<and> 
      (\<Gamma> \<turnstile> f\<^sub>2 : t\<^sub>1\<^sub>2 \<rightarrow> t\<^sub>2\<^sub>2) \<and> t\<^sub>1 = t\<^sub>1\<^sub>1 \<otimes> t\<^sub>1\<^sub>2 \<and> t\<^sub>2 = t\<^sub>1\<^sub>1 \<otimes> t\<^sub>2\<^sub>2 \<and> (\<Gamma> \<turnstile> f\<^sub>2' : t\<^sub>1\<^sub>2' \<rightarrow> t\<^sub>2\<^sub>2) \<and> 
        \<Gamma> \<turnstile> v\<^sub>2' : t\<^sub>1\<^sub>2'" by fastforce
    hence "(\<Gamma> \<turnstile> \<epsilon> \<parallel> f\<^sub>2' : t\<^sub>1\<^sub>1 \<otimes> t\<^sub>1\<^sub>2' \<rightarrow> t\<^sub>2) \<and> \<Gamma> \<turnstile> PairV v\<^sub>1 v\<^sub>2' : t\<^sub>1\<^sub>1 \<otimes> t\<^sub>1\<^sub>2'" by simp
    thus ?case by fastforce
  next case (ev_pair3 \<Lambda> v\<^sub>1 v\<^sub>2)
    hence "(\<Gamma> \<turnstile> \<epsilon> : t\<^sub>1 \<rightarrow> t\<^sub>2) \<and> \<Gamma> \<turnstile> PairV v\<^sub>1 v\<^sub>2 : t\<^sub>1" by fastforce
    thus ?case by fastforce
  next case (ev_tup \<Lambda> v)
    hence "t\<^sub>2 = t\<^sub>1 \<otimes> t\<^sub>1" by fastforce
    moreover from ev_tup have "(\<Gamma> \<turnstile> \<epsilon> : t\<^sub>1 \<otimes> t\<^sub>1 \<rightarrow> t\<^sub>1 \<otimes> t\<^sub>1) \<and> \<Gamma> \<turnstile> PairV v v : t\<^sub>1 \<otimes> t\<^sub>1" 
      by simp
    ultimately show ?case by fastforce
  next case (ev_inl \<Lambda> v)
    moreover then obtain t\<^sub>3 where "t\<^sub>2 = t\<^sub>1 \<oplus> t\<^sub>3" by fastforce
    ultimately have "(\<Gamma> \<turnstile> \<epsilon> : t\<^sub>1 \<oplus> t\<^sub>3 \<rightarrow> t\<^sub>2) \<and> \<Gamma> \<turnstile> InlV v : t\<^sub>1 \<oplus> t\<^sub>3" by simp
    thus ?case by fastforce
  next case (ev_inr \<Lambda> v)
    moreover then obtain t\<^sub>3 where "t\<^sub>2 = t\<^sub>3 \<oplus> t\<^sub>1" by fastforce
    ultimately have "(\<Gamma> \<turnstile> \<epsilon> : t\<^sub>3 \<oplus> t\<^sub>1 \<rightarrow> t\<^sub>2) \<and> \<Gamma> \<turnstile> InrV v : t\<^sub>3 \<oplus> t\<^sub>1" by simp
    thus ?case by fastforce
  next case (ev_strl \<Lambda> v)
    hence "(\<Gamma> \<turnstile> \<epsilon> : t\<^sub>2 \<rightarrow> t\<^sub>2) \<and> \<Gamma> \<turnstile> v : t\<^sub>2" by fastforce
    thus ?case by fastforce
  next case (ev_strr \<Lambda> v)
    hence "(\<Gamma> \<turnstile> \<epsilon> : t\<^sub>2 \<rightarrow> t\<^sub>2) \<and> \<Gamma> \<turnstile> v : t\<^sub>2" by fastforce
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
  next case (ev_outj \<Lambda> m F v)
    hence "(\<Gamma> \<turnstile> \<epsilon> : t\<^sub>2 \<rightarrow> t\<^sub>2) \<and> \<Gamma> \<turnstile> v : t\<^sub>2" by fastforce
    thus ?case by fastforce
  next case (ev_cata \<Lambda> n F f v)
    hence V: "(\<Gamma> \<turnstile> f : t\<^sub>2 \<star> F \<rightarrow> t\<^sub>2) \<and> \<Gamma> \<turnstile> v : \<mu> F" using typecheck_environment_def by fastforce
    moreover from ev_cata have "\<Gamma> \<turnstile> \<lparr> f \<rparr>\<^bsub>n\<^esub> \<bullet> F : \<mu> F \<star> F \<rightarrow> t\<^sub>2 \<star> F" 
      using typecheck_environment_def by fastforce
    moreover from ev_cata have "\<Gamma> \<turnstile> \<prec>\<^bsub>n\<^esub> : \<mu> F \<rightarrow> \<mu> F \<star> F" using typecheck_environment_def by simp
    ultimately have "\<Gamma> \<turnstile> f \<cdot> \<lparr> f \<rparr>\<^bsub>n\<^esub> \<bullet> F \<cdot> \<prec>\<^bsub>n\<^esub> : \<mu> F \<rightarrow> t\<^sub>2" by (metis tc_comp)
    with V have "(\<Gamma> \<turnstile> f \<cdot> \<lparr> f \<rparr>\<^bsub>n\<^esub> \<bullet> F \<cdot> \<prec>\<^bsub>n\<^esub> : \<mu> F \<rightarrow> t\<^sub>2) \<and> \<Gamma> \<turnstile> v : \<mu> F" by simp
    thus ?case by fastforce
  next case (ev_ana \<Lambda> n F f v)
    moreover hence V: "(\<Gamma> \<turnstile> f : t\<^sub>1 \<rightarrow> t\<^sub>1 \<star> F) \<and> (\<Gamma> \<turnstile> v : t\<^sub>1) \<and> t\<^sub>2 = \<mu> F"
      using typecheck_environment_def by fastforce
    ultimately have "\<Gamma> \<turnstile> \<succ>\<^bsub>n\<^esub> : t\<^sub>2 \<star> F \<rightarrow> t\<^sub>2" using typecheck_environment_def by simp
    moreover from ev_ana have "\<Gamma> \<turnstile> \<lbrakk> f \<rbrakk>\<^bsub>n\<^esub> \<bullet> F : t\<^sub>1 \<star> F \<rightarrow> t\<^sub>2 \<star> F" by simp
    moreover from V have "\<Gamma> \<turnstile> f : t\<^sub>1 \<rightarrow> t\<^sub>1 \<star> F" by simp
    ultimately have "\<Gamma> \<turnstile> \<succ>\<^bsub>n\<^esub> \<cdot> \<lbrakk> f \<rbrakk>\<^bsub>n\<^esub> \<bullet> F \<cdot> f : t\<^sub>1 \<rightarrow> t\<^sub>2" by simp
    with V show ?case by fastforce
  next case (ev_var \<Lambda> x e v)
    hence "var\<^sub>e_type \<Gamma> x = Some (t\<^sub>1, t\<^sub>2)" by fastforce
    with ev_var obtain e' where "var\<^sub>e_bind \<Lambda> x = Some e' \<and> \<Gamma> \<turnstile> e' : t\<^sub>1 \<rightarrow> t\<^sub>2" 
      using typecheck_environment_def typecheck_env\<^sub>e_def by fastforce 
    with ev_var show ?case by fastforce
  qed fastforce+

theorem preservation [simp]: "\<Pi> \<leadsto> \<Pi>' \<Longrightarrow> \<Pi> \<TTurnstile> \<Gamma> \<rightarrow> t \<Longrightarrow> \<Pi>' \<TTurnstile> \<Gamma> \<rightarrow> t"
  proof (induction \<Pi> \<Pi>' rule: evaluate_prog.induct)
  case (ev_prog \<Delta> \<Lambda> e v e' v')
    moreover then obtain t\<^sub>1 where T: "(empty_static \<Turnstile> \<Delta> :: \<Gamma>) \<and> (\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t) \<and> \<Gamma> \<turnstile> v : t\<^sub>1" 
      by blast
    ultimately obtain t\<^sub>2 where "(\<Gamma> \<turnstile> e' : t\<^sub>2 \<rightarrow> t) \<and> (\<Gamma> \<turnstile> v' : t\<^sub>2)" by fastforce
    with T show ?case by fastforce
  qed

end
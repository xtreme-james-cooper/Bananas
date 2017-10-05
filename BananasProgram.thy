theory BananasProgram
imports BananasExpression
begin

datatype decl = 
  TypeDecl name "(name \<times> type list) list"
| ValDecl name val
| ExprDecl name expr

primrec binders\<^sub>d :: "decl \<Rightarrow> name set" where
  "binders\<^sub>d (TypeDecl x cts) = insert x (fst ` set cts)"
| "binders\<^sub>d (ValDecl x v) = {x}"
| "binders\<^sub>d (ExprDecl x e) = {x}"

fun binders :: "decl list \<Rightarrow> name set" where
  "binders \<Lambda> = \<Union> (binders\<^sub>d ` set \<Lambda>)"

datatype prog = Prog "decl list" expr val

fun typecheck\<^sub>c\<^sub>e :: "funct \<Rightarrow> (name \<times> type list) list \<Rightarrow> (name \<rightharpoonup> type \<times> type)" where
  "typecheck\<^sub>c\<^sub>e F [] y = None" 
| "typecheck\<^sub>c\<^sub>e F ((x, ts) # cts) y = 
    (if y = x then Some (foldr (op \<otimes>) ts \<one>, \<mu> F) else typecheck\<^sub>c\<^sub>e F cts y)"

definition typecheck\<^sub>c\<^sub>v :: "funct \<Rightarrow> (name \<times> type list) list \<Rightarrow> (name \<rightharpoonup> type)" where
  "typecheck\<^sub>c\<^sub>v F cts x = (if x \<in> fst ` set cts then Some (\<mu> F) else None)"

primrec typecheck\<^sub>c\<^sub>t :: "name \<times> type list \<Rightarrow> funct" where
  "typecheck\<^sub>c\<^sub>t (x, ts) = K (foldr (op \<otimes>) ts \<one>)"

definition typecheck\<^sub>c\<^sub>t\<^sub>s :: "(name \<times> type list) list \<Rightarrow> funct" where
  "typecheck\<^sub>c\<^sub>t\<^sub>s cts = foldr (op \<Oplus> o typecheck\<^sub>c\<^sub>t) cts (K \<zero>)"

definition typecheck\<^sub>d :: "name \<Rightarrow> (name \<times> type list) list \<Rightarrow> static_environment" where
  "typecheck\<^sub>d n cts = (
      let F = typecheck\<^sub>c\<^sub>t\<^sub>s cts 
      in \<lparr> var\<^sub>e_type = typecheck\<^sub>c\<^sub>e F cts, var\<^sub>v_type = typecheck\<^sub>c\<^sub>v F cts, var\<^sub>t_type = [n \<mapsto> F] \<rparr>)"

inductive typecheck_decl :: "static_environment \<Rightarrow> decl \<Rightarrow> static_environment \<Rightarrow> bool" 
    (infix "\<Turnstile> _ :" 60) where
  tcd_type [simp]: "\<Gamma> \<Turnstile> TypeDecl x cts : combine\<^sub>s \<Gamma> (typecheck\<^sub>d x cts)"
| tcd_val [simp]: "\<Gamma> \<turnstile> v : t \<Longrightarrow> \<Gamma> \<Turnstile> ValDecl x v : extend\<^sub>v\<^sub>s x t \<Gamma>"
| tcd_expr [simp]: "\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<Turnstile> ExprDecl x e : extend\<^sub>e\<^sub>s x (t\<^sub>1, t\<^sub>2) \<Gamma>"

inductive_cases [elim]: "\<Gamma> \<Turnstile> TypeDecl x F : \<Gamma>'"
inductive_cases [elim]: "\<Gamma> \<Turnstile> ValDecl x v : \<Gamma>'"
inductive_cases [elim]: "\<Gamma> \<Turnstile> ExprDecl x e : \<Gamma>'"

inductive typecheck_decls :: "static_environment \<Rightarrow> decl list \<Rightarrow> static_environment \<Rightarrow> bool" 
    (infix "\<Turnstile> _ ::" 60) where
  tcd_nil [simp]: "\<Gamma> \<Turnstile> [] :: \<Gamma>"
| tcd_cons [simp]: "\<Gamma> \<Turnstile> \<delta> : \<Gamma>' \<Longrightarrow> binders\<^sub>d \<delta> \<inter> domain\<^sub>s \<Gamma> = {} \<Longrightarrow> \<Gamma>' \<Turnstile> \<Lambda> :: \<Gamma>'' \<Longrightarrow> 
    \<Gamma> \<Turnstile> \<delta> # \<Lambda> :: \<Gamma>''"

inductive_cases [elim]: "\<Gamma> \<Turnstile> [] :: \<Gamma>'"
inductive_cases [elim]: "\<Gamma> \<Turnstile> \<delta> # \<Lambda> :: \<Gamma>'"

definition empty_static :: static_environment where
  "empty_static = \<lparr> var\<^sub>e_type = Map.empty, var\<^sub>v_type = Map.empty, var\<^sub>t_type = Map.empty \<rparr>"

inductive typecheck_prog :: "prog \<Rightarrow> static_environment \<Rightarrow> type \<Rightarrow> bool" (infix "\<TTurnstile> _ \<rightarrow> " 60) where
  tcp_prog [simp]: "empty_static \<Turnstile> \<Lambda> :: \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> v : t\<^sub>1 \<Longrightarrow> 
    Prog \<Lambda> e v \<TTurnstile> \<Gamma> \<rightarrow> t\<^sub>2"

inductive_cases [elim]: "Prog \<Lambda> e v \<TTurnstile> \<Gamma>  \<rightarrow> t"

definition empty_dynamic :: dynamic_environment where
  "empty_dynamic = \<lparr> var\<^sub>e_bind = Map.empty, var\<^sub>v_bind = Map.empty, var\<^sub>t_bind = Map.empty \<rparr>"

primrec right_inject :: "nat \<Rightarrow> expr" where
  "right_inject 0 = \<iota>\<^sub>l"
| "right_inject (Suc x) = \<iota>\<^sub>r \<cdot> right_inject x"

fun assemble_context\<^sub>c\<^sub>e :: "name \<Rightarrow> nat \<Rightarrow> (name \<times> type list) list \<Rightarrow> (name \<rightharpoonup> expr)" where
  "assemble_context\<^sub>c\<^sub>e n depth [] = Map.empty"
| "assemble_context\<^sub>c\<^sub>e n depth ((x, t) # cts) = 
    (assemble_context\<^sub>c\<^sub>e n (Suc depth) cts)(x \<mapsto> \<succ>\<^bsub>n\<^esub> \<cdot> right_inject depth)"

fun assemble_context\<^sub>c\<^sub>v :: "name \<Rightarrow> (name \<times> type list) list \<Rightarrow> (name \<rightharpoonup> val)" where
  "assemble_context\<^sub>c\<^sub>v n [] = Map.empty"
| "assemble_context\<^sub>c\<^sub>v n ((x, t) # cts) = (assemble_context\<^sub>c\<^sub>v n cts)(x \<mapsto> UnitV)" (* TODO! *)

primrec assemble_context' :: "decl \<Rightarrow> dynamic_environment" where
  "assemble_context' (TypeDecl x cts) = \<lparr> 
    var\<^sub>e_bind = assemble_context\<^sub>c\<^sub>e x 0 cts, 
    var\<^sub>v_bind = assemble_context\<^sub>c\<^sub>v x cts, 
    var\<^sub>t_bind = [x \<mapsto> typecheck\<^sub>c\<^sub>t\<^sub>s cts] \<rparr>"
| "assemble_context' (ValDecl x v) = empty_dynamic \<lparr> var\<^sub>v_bind := [x \<mapsto> v] \<rparr>"
| "assemble_context' (ExprDecl x e) = empty_dynamic \<lparr> var\<^sub>e_bind := [x \<mapsto> e] \<rparr>"

primrec assemble_context :: "decl list \<Rightarrow> dynamic_environment" where
  "assemble_context [] = empty_dynamic"
| "assemble_context (\<delta> # \<Lambda>) = combine\<^sub>d (assemble_context' \<delta>) (assemble_context \<Lambda>)"

primrec is_completed :: "prog \<Rightarrow> bool" where
  "is_completed (Prog \<Lambda> e v) = (e = \<epsilon>)"

inductive evaluate_prog :: "prog \<Rightarrow> prog \<Rightarrow> bool" (infix "\<leadsto>" 60) where
  ev_prog [simp]: "assemble_context \<Lambda> \<turnstile> e \<cdot> v \<leadsto> e' \<cdot> v' \<Longrightarrow> Prog \<Lambda> e v \<leadsto> Prog \<Lambda> e' v'"

inductive_cases [elim]: "Prog \<Lambda> e v \<leadsto> \<Pi>"

(* safety *)

lemma [simp]: "combine\<^sub>d empty_dynamic \<Lambda> = \<Lambda>"
  by (simp add: combine\<^sub>d_def empty_dynamic_def)

lemma [simp]: "combine\<^sub>d \<Lambda> empty_dynamic = \<Lambda>"
  by (simp add: combine\<^sub>d_def empty_dynamic_def)

lemma [simp]: "combine\<^sub>d (combine\<^sub>d \<Lambda>\<^sub>1 \<Lambda>\<^sub>2) \<Lambda>\<^sub>3 = combine\<^sub>d \<Lambda>\<^sub>1 (combine\<^sub>d \<Lambda>\<^sub>2 \<Lambda>\<^sub>3)"
  by (simp add: combine\<^sub>d_def empty_dynamic_def)

lemma [simp]: "combine\<^sub>d \<Lambda> (empty_dynamic\<lparr>var\<^sub>e_bind := [x \<mapsto> e]\<rparr>) = extend\<^sub>e\<^sub>d x e \<Lambda>"
  by (simp add: combine\<^sub>d_def empty_dynamic_def extend\<^sub>e\<^sub>d_def)

lemma [simp]: "combine\<^sub>d \<Lambda> (empty_dynamic\<lparr>var\<^sub>v_bind := [x \<mapsto> v]\<rparr>) = extend\<^sub>v\<^sub>d x v \<Lambda>"
  by (simp add: combine\<^sub>d_def empty_dynamic_def extend\<^sub>v\<^sub>d_def)

lemma [simp]: "typecheck\<^sub>c\<^sub>e F cts x = Some (t\<^sub>1, t\<^sub>2) \<Longrightarrow> \<exists>e. assemble_context\<^sub>c\<^sub>e n d cts x = Some e"
  by (induction F cts x arbitrary: d rule: typecheck\<^sub>c\<^sub>e.induct) auto

lemma [simp]: "assemble_context\<^sub>c\<^sub>e n d cts x = Some e \<Longrightarrow> \<exists>t\<^sub>1 t\<^sub>2. typecheck\<^sub>c\<^sub>e F cts x = Some (t\<^sub>1, t\<^sub>2)"
  by (induction n d cts arbitrary: e rule: assemble_context\<^sub>c\<^sub>e.induct) auto

lemma [elim]: "\<Gamma> \<turnstile> right_inject (length cts') : t\<^sub>1 \<rightarrow> t\<^sub>2 \<star> typecheck\<^sub>c\<^sub>t\<^sub>s (cts' @ cts) \<Longrightarrow> 
    \<Gamma>' \<turnstile> right_inject (length cts') : t\<^sub>1 \<rightarrow> t\<^sub>2 \<star> typecheck\<^sub>c\<^sub>t\<^sub>s (cts' @ cts)"
  proof (induction cts')
  case (Cons ct cts')
    let ?F = "typecheck\<^sub>c\<^sub>t\<^sub>s (ct # cts' @ cts)"
    let ?F' = "typecheck\<^sub>c\<^sub>t\<^sub>s (cts' @ cts)" 
    from Cons have "(\<Gamma> \<turnstile> \<iota>\<^sub>r : t\<^sub>2 \<star> ?F' \<rightarrow> (t\<^sub>2 \<star> typecheck\<^sub>c\<^sub>t ct) \<oplus> (t\<^sub>2 \<star> ?F')) \<and> 
      \<Gamma> \<turnstile> right_inject (length cts') : t\<^sub>1 \<rightarrow> t\<^sub>2 \<star> ?F'" using typecheck\<^sub>c\<^sub>t\<^sub>s_def by fastforce
    with Cons have "\<Gamma>' \<turnstile> right_inject (length cts') : t\<^sub>1 \<rightarrow> t\<^sub>2 \<star> ?F'" by simp
    moreover have "\<Gamma>' \<turnstile> \<iota>\<^sub>r : t\<^sub>2 \<star> ?F' \<rightarrow> t\<^sub>2 \<star> ?F" by (simp add: typecheck\<^sub>c\<^sub>t\<^sub>s_def)
    ultimately show ?case by simp
  qed fastforce+

lemma assembled_no_free_vars: "assemble_context\<^sub>c\<^sub>e n (length cts') cts x = Some e \<Longrightarrow> 
    var\<^sub>t_type \<Gamma> n = Some (typecheck\<^sub>c\<^sub>t\<^sub>s (cts' @ cts)) \<Longrightarrow> 
      var\<^sub>t_type \<Gamma>' n = Some (typecheck\<^sub>c\<^sub>t\<^sub>s (cts' @ cts)) \<Longrightarrow> \<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma>' \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2" 
  proof (induction n "length cts'" cts arbitrary: cts' rule: assemble_context\<^sub>c\<^sub>e.induct)
  case (2 n y t cts)
    moreover have "Suc (length cts') = length (cts' @ [(y, t)])" by simp
    moreover from 2 have "var\<^sub>t_type \<Gamma> n = Some (typecheck\<^sub>c\<^sub>t\<^sub>s ((cts' @ [(y, t)]) @ cts))" by simp
    moreover from 2 have "var\<^sub>t_type \<Gamma>' n = Some (typecheck\<^sub>c\<^sub>t\<^sub>s ((cts' @ [(y, t)]) @ cts))" by simp
    ultimately have IH: "assemble_context\<^sub>c\<^sub>e n (length (cts' @ [(y, t)])) cts x = Some e \<Longrightarrow> 
      \<Gamma>' \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2" by blast
    with 2 show ?case
      proof (cases "x = y")
      case True
        let ?F = "typecheck\<^sub>c\<^sub>t\<^sub>s (cts' @ (y, t) # cts)"
        from True 2 have "(\<Gamma> \<turnstile> right_inject (length cts') : t\<^sub>1 \<rightarrow> \<mu> ?F \<star> ?F) \<and> t\<^sub>2 = \<mu> ?F"
          by fastforce
        moreover hence "\<Gamma>' \<turnstile> right_inject (length cts') : t\<^sub>1 \<rightarrow> \<mu> ?F \<star> ?F" by fastforce
        moreover from 2 have "\<Gamma>' \<turnstile> \<succ>\<^bsub>n\<^esub> : \<mu> ?F \<star> ?F \<rightarrow> \<mu> ?F" by simp
        ultimately have "\<Gamma>' \<turnstile> \<succ>\<^bsub>n\<^esub> \<cdot> right_inject (length cts') : t\<^sub>1 \<rightarrow> t\<^sub>2" by simp
        with True 2 show ?thesis by simp
      qed simp_all
   qed simp_all

lemma [simp]: "typecheck\<^sub>c\<^sub>t\<^sub>s (cts @ (x, ts) # cts') = F \<Longrightarrow> 
    \<Gamma> \<turnstile> right_inject (length cts) : foldr op \<otimes> ts \<one> \<rightarrow> t \<star> F"
  proof (induction cts arbitrary: F)
  case Nil
    hence "F = typecheck\<^sub>c\<^sub>t (x, ts) \<Oplus> typecheck\<^sub>c\<^sub>t\<^sub>s cts'" by (simp add: typecheck\<^sub>c\<^sub>t\<^sub>s_def)
    thus ?case by (simp add: typecheck\<^sub>c\<^sub>t\<^sub>s_def)
  next case (Cons ct cts)
    let ?F = "typecheck\<^sub>c\<^sub>t\<^sub>s (cts @ (x, ts) # cts')"
    from Cons have "F = typecheck\<^sub>c\<^sub>t ct \<Oplus> ?F" by (simp add: typecheck\<^sub>c\<^sub>t\<^sub>s_def)
    hence X: "\<Gamma> \<turnstile> \<iota>\<^sub>r : t \<star> ?F \<rightarrow> t \<star> F" by (simp add: typecheck\<^sub>c\<^sub>t\<^sub>s_def)
    from Cons have "\<Gamma> \<turnstile> right_inject (length cts) : foldr op \<otimes> ts \<one> \<rightarrow> t \<star> ?F" by simp
    with X show ?case by simp
  qed

lemma tc_assembled_e: "typecheck\<^sub>c\<^sub>e F cts x = Some (t\<^sub>1, t\<^sub>2) \<Longrightarrow> typecheck\<^sub>c\<^sub>t\<^sub>s (cts' @ cts) = F \<Longrightarrow>
  \<exists>e. assemble_context\<^sub>c\<^sub>e n (length cts') cts x = Some e \<and> \<lparr>var\<^sub>e_type = typecheck\<^sub>c\<^sub>e F cts, 
    var\<^sub>v_type = typecheck\<^sub>c\<^sub>v F cts, var\<^sub>t_type = [n \<mapsto> F]\<rparr> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2"
  proof (induction F cts x arbitrary: cts' rule: typecheck\<^sub>c\<^sub>e.induct)
  case (2 F y ts cts x)
    let ?\<Gamma> = "\<lparr>var\<^sub>e_type = typecheck\<^sub>c\<^sub>e F ((y, ts) # cts), 
               var\<^sub>v_type = typecheck\<^sub>c\<^sub>v F ((y, ts) # cts), 
               var\<^sub>t_type = [n \<mapsto> F]\<rparr>"
    show ?case
      proof (cases "x = y")
      case True
        have X: "?\<Gamma> \<turnstile> \<succ>\<^bsub>n\<^esub> : \<mu> F \<star> F \<rightarrow> \<mu> F" by simp
        from 2 have "?\<Gamma> \<turnstile> right_inject (length cts') : foldr op \<otimes> ts \<one> \<rightarrow> \<mu> F \<star> F" by simp
        with 2 True X have "?\<Gamma> \<turnstile> \<succ>\<^bsub>n\<^esub> \<cdot> right_inject (length cts') : t\<^sub>1 \<rightarrow> t\<^sub>2" by simp
        with True show ?thesis by fastforce
      next case False        
        with 2 have X: "typecheck\<^sub>c\<^sub>e F cts x = Some (t\<^sub>1, t\<^sub>2)" by simp
        let ?\<Gamma>' = "\<lparr>var\<^sub>e_type = typecheck\<^sub>c\<^sub>e F cts, var\<^sub>v_type = typecheck\<^sub>c\<^sub>v F cts, 
          var\<^sub>t_type = [n \<mapsto> F]\<rparr>"
        from 2 have F: "typecheck\<^sub>c\<^sub>t\<^sub>s ((cts' @ [(y, ts)]) @ cts) = F" by simp
        with 2 False X obtain e where "
          assemble_context\<^sub>c\<^sub>e n (length (cts' @ [(y, ts)])) cts x = Some e \<and> ?\<Gamma>' \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2" 
            by blast
        moreover hence "assemble_context\<^sub>c\<^sub>e n (Suc (length cts')) cts x = Some e" by simp
        moreover from F have "var\<^sub>t_type ?\<Gamma>' n = Some (typecheck\<^sub>c\<^sub>t\<^sub>s ((cts' @ [(y, ts)]) @ cts))" 
          by simp
        moreover from F have "var\<^sub>t_type ?\<Gamma> n = Some (typecheck\<^sub>c\<^sub>t\<^sub>s ((cts' @ [(y, ts)]) @ cts))" 
          by simp
        ultimately have "assemble_context\<^sub>c\<^sub>e n (Suc (length cts')) cts x = Some e \<and> 
          ?\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2" by (metis assembled_no_free_vars length_append_singleton)
        with False show ?thesis by fastforce
      qed
  qed simp_all

lemma [simp]: "typecheck\<^sub>c\<^sub>e (typecheck\<^sub>c\<^sub>t\<^sub>s cts) cts x = Some (t\<^sub>1, t\<^sub>2) \<Longrightarrow> 
  \<exists>e. assemble_context\<^sub>c\<^sub>e n 0 cts x = Some e \<and> \<lparr>var\<^sub>e_type = typecheck\<^sub>c\<^sub>e (typecheck\<^sub>c\<^sub>t\<^sub>s cts) cts, 
    var\<^sub>v_type = typecheck\<^sub>c\<^sub>v (typecheck\<^sub>c\<^sub>t\<^sub>s cts) cts, var\<^sub>t_type = [n \<mapsto> typecheck\<^sub>c\<^sub>t\<^sub>s cts]\<rparr> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2"
  proof -
    assume "typecheck\<^sub>c\<^sub>e (typecheck\<^sub>c\<^sub>t\<^sub>s cts) cts x = Some (t\<^sub>1, t\<^sub>2)"
    hence "typecheck\<^sub>c\<^sub>e (typecheck\<^sub>c\<^sub>t\<^sub>s ([] @ cts)) cts x = Some (t\<^sub>1, t\<^sub>2)" by simp
    thus ?thesis using tc_assembled_e by fastforce
  qed

lemma [simp]: "typecheck\<^sub>c\<^sub>v (typecheck\<^sub>c\<^sub>t\<^sub>s cts) cts xa = Some t \<Longrightarrow> 
  \<exists>v. assemble_context\<^sub>c\<^sub>v n cts xa = Some v \<and> \<lparr>var\<^sub>e_type = typecheck\<^sub>c\<^sub>e (typecheck\<^sub>c\<^sub>t\<^sub>s cts) cts, 
    var\<^sub>v_type = typecheck\<^sub>c\<^sub>v (typecheck\<^sub>c\<^sub>t\<^sub>s cts) cts, var\<^sub>t_type = [n \<mapsto> typecheck\<^sub>c\<^sub>t\<^sub>s cts]\<rparr> \<turnstile> v : t"
  by simp

lemma tc_typedecl: "typecheck\<^sub>d x cts \<tturnstile> assemble_context' (TypeDecl x cts)"
  by (auto simp add: typecheck_environment_def typecheck\<^sub>d_def Let_def)

lemma [simp]: "dom (typecheck\<^sub>c\<^sub>e x cts) = fst ` set cts"
  by (induction cts rule: assemble_context\<^sub>c\<^sub>e.induct) (auto, force)

lemma [simp]: "dom (typecheck\<^sub>c\<^sub>v x cts) = fst ` set cts"
  by (auto simp add: typecheck\<^sub>c\<^sub>v_def) (force split: if_splits)+

lemma [simp]: "domain\<^sub>s (typecheck\<^sub>d x cts) = insert x (fst ` set cts)"
  by (simp add: domain\<^sub>s_def typecheck\<^sub>d_def Let_def)

lemma [simp]: "\<Gamma>\<^sub>1 \<Turnstile> \<delta> : \<Gamma>\<^sub>2 \<Longrightarrow> \<Gamma>\<^sub>1 \<tturnstile> \<Lambda>\<^sub>1 \<Longrightarrow> binders\<^sub>d \<delta> \<inter> domain\<^sub>s \<Gamma>\<^sub>1 = {} \<Longrightarrow> 
    \<Gamma>\<^sub>2 \<tturnstile> combine\<^sub>d \<Lambda>\<^sub>1 (assemble_context' \<delta>)"
  proof (induction \<Gamma>\<^sub>1 \<delta> \<Gamma>\<^sub>2 rule: typecheck_decl.induct)
  case (tcd_type \<Gamma> x cts)
    hence "domain\<^sub>s \<Gamma> \<inter> domain\<^sub>s (typecheck\<^sub>d x cts) = {}" by auto
    with tcd_type show ?case by (metis typecheck_combine tc_typedecl)
  qed simp_all

lemma tc_defs_parts [simp]: "\<Gamma>\<^sub>1 \<Turnstile> \<Lambda>\<^sub>2 :: \<Gamma>\<^sub>2 \<Longrightarrow> \<Gamma>\<^sub>1 \<tturnstile> \<Lambda>\<^sub>1 \<Longrightarrow> \<Gamma>\<^sub>2 \<tturnstile> combine\<^sub>d \<Lambda>\<^sub>1 (assemble_context \<Lambda>\<^sub>2)"
  proof (induction \<Gamma>\<^sub>1 \<Lambda>\<^sub>2 \<Gamma>\<^sub>2 arbitrary: \<Lambda>\<^sub>1 rule: typecheck_decls.induct)
  case (tcd_cons \<Gamma>\<^sub>1 \<delta> \<Gamma>\<^sub>2 \<Lambda>\<^sub>2 \<Gamma>\<^sub>3)
    moreover hence "\<Gamma>\<^sub>2 \<tturnstile> combine\<^sub>d \<Lambda>\<^sub>1 (assemble_context' \<delta>)" by simp
    ultimately show ?case by fastforce
  qed simp_all

lemma [simp]: "empty_static \<tturnstile> empty_dynamic" 
  by (simp add: typecheck_environment_def empty_static_def empty_dynamic_def)

lemma [simp]: "empty_static \<Turnstile> \<Lambda> :: \<Gamma> \<Longrightarrow> \<Gamma> \<tturnstile> assemble_context \<Lambda>"
  proof -
    assume "empty_static \<Turnstile> \<Lambda> :: \<Gamma>"
    moreover have "empty_static \<tturnstile> empty_dynamic" by simp
    ultimately have "\<Gamma> \<tturnstile> combine\<^sub>d empty_dynamic (assemble_context \<Lambda>)" by (metis tc_defs_parts)
    thus "\<Gamma> \<tturnstile> assemble_context \<Lambda>" by simp
  qed                                                                  

theorem progress [simp]: "\<Pi> \<TTurnstile> \<Gamma> \<rightarrow> t \<Longrightarrow> is_completed \<Pi> \<or> (\<exists>\<Pi>'. \<Pi> \<leadsto> \<Pi>')"
  proof (induction \<Pi> \<Gamma> t rule: typecheck_prog.induct)
  case (tcp_prog \<Lambda> \<Gamma> e t\<^sub>1 t\<^sub>2 v)
    thus ?case 
      proof (cases "e = \<epsilon>")
      case False
        with tcp_prog obtain e' v' where "assemble_context \<Lambda> \<turnstile> e \<cdot> v \<leadsto> e' \<cdot> v'" by fastforce
        with tcp_prog have "Prog \<Lambda> e v \<leadsto> Prog \<Lambda> e' v'" by simp
        thus ?thesis by fastforce
      qed simp_all
  qed

theorem preservation [simp]: "\<Pi> \<leadsto> \<Pi>' \<Longrightarrow> \<Pi> \<TTurnstile> \<Gamma> \<rightarrow> t \<Longrightarrow> \<Pi>' \<TTurnstile> \<Gamma> \<rightarrow> t"
  proof (induction \<Pi> \<Pi>' rule: evaluate_prog.induct)
  case (ev_prog \<Lambda> e v e' v')
    moreover then obtain t\<^sub>1 where T: "(empty_static \<Turnstile> \<Lambda> :: \<Gamma>) \<and> (\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t) \<and> \<Gamma> \<turnstile> v : t\<^sub>1" 
      by blast
    ultimately obtain t\<^sub>2 where "(\<Gamma> \<turnstile> e' : t\<^sub>2 \<rightarrow> t) \<and> (\<Gamma> \<turnstile> v' : t\<^sub>2)" by fastforce
    with T show ?case by fastforce
  qed

(* big step evaluation *)

inductive total_evaluate_prog :: "prog \<Rightarrow> val \<Rightarrow> bool" (infix "\<Down>" 60) where
  ptev_base [simp]: "Prog \<Lambda> \<epsilon> v \<Down> v"
| ptev_step [simp]: "Prog \<Lambda> e v \<leadsto> Prog \<Lambda> e' v' \<Longrightarrow> Prog \<Lambda> e' v' \<Down> v'' \<Longrightarrow> Prog \<Lambda> e v \<Down> v''"

inductive total_evaluate_prog' :: "prog \<Rightarrow> val \<Rightarrow> bool" (infix "\<Down>\<Down>" 60) where
  ptev_step' [simp]: "assemble_context \<Lambda> \<turnstile> e \<cdot> v \<Down> v' \<Longrightarrow> Prog \<Lambda> e v \<Down>\<Down> v'"

inductive_cases [elim]: "Prog \<Lambda> e v \<Down>\<Down> v'"

lemma [simp]: "\<Pi> \<Down> v = \<Pi> \<Down>\<Down> v"
  proof
    show "\<Pi> \<Down> v \<Longrightarrow> \<Pi> \<Down>\<Down> v" by (induction \<Pi> v rule: total_evaluate_prog.induct) fastforce+
  next 
    assume "\<Pi> \<Down>\<Down> v"
    thus "\<Pi> \<Down> v"
      proof (induction \<Pi> v rule: total_evaluate_prog'.induct)
      case (ptev_step' \<Lambda> e v v')
        thus ?case 
          proof (induction "assemble_context \<Lambda>" e v v' rule: total_eval.induct)
          case (tev_step e v e' v' v'')
            moreover hence "Prog \<Lambda> e v \<leadsto> Prog \<Lambda> e' v'" by simp
            ultimately show ?case by (metis total_evaluate_prog.ptev_step)
          qed simp_all
      qed
  qed

(* since we are a turing-complete language, total progress is not provable *)

lemma [simp]: "\<Pi> \<Down>\<Down> v \<Longrightarrow> \<Pi> \<TTurnstile> \<Gamma> \<rightarrow> t \<Longrightarrow> \<Gamma> \<turnstile> v : t"
  by (induction \<Pi> v rule: total_evaluate_prog'.induct) auto

theorem total_preservation: "\<Pi> \<Down> v \<Longrightarrow> \<Pi> \<TTurnstile> \<Gamma> \<rightarrow> t \<Longrightarrow> \<Gamma> \<turnstile> v : t"
  by simp

end
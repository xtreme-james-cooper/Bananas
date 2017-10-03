theory BananasProgram
imports BananasExpression
begin

datatype decl = 
  TypeDecl name funct
| ExprDecl name expr

primrec "binder" :: "decl \<Rightarrow> name set" where
  "binder (TypeDecl x F) = {}"
| "binder (ExprDecl x e) = {x}"

fun binders :: "decl list \<Rightarrow> name set" where
  "binders \<Lambda> = \<Union> (binder ` set \<Lambda>)"

datatype prog = 
  Prog "decl list" expr val

inductive typecheck_decl :: "(name \<rightharpoonup> type \<times> type) \<Rightarrow> decl \<Rightarrow> (name \<rightharpoonup> type \<times> type) \<Rightarrow> bool" 
    (infix "\<Turnstile> _ :" 60) where
  tcd_type [simp]: "\<Gamma> \<Turnstile> TypeDecl x F : \<Gamma>"
| tcd_expr [simp]: "\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<Turnstile> ExprDecl x e : \<Gamma>(x \<mapsto> (t\<^sub>1, t\<^sub>2))"

inductive_cases [elim]: "\<Gamma> \<Turnstile> TypeDecl x F : \<Gamma>'"
inductive_cases [elim]: "\<Gamma> \<Turnstile> ExprDecl x e : \<Gamma>'"

inductive typecheck_decls :: "(name \<rightharpoonup> type \<times> type) \<Rightarrow> decl list \<Rightarrow> (name \<rightharpoonup> type \<times> type) \<Rightarrow> bool" 
    (infix "\<Turnstile> _ ::" 60) where
  tcd_nil [simp]: "\<Gamma> \<Turnstile> [] :: \<Gamma>"
| tcd_cons [simp]: "\<Gamma> \<Turnstile> \<delta> : \<Gamma>' \<Longrightarrow> binder \<delta> \<inter> binders \<Lambda> = {} \<Longrightarrow> \<Gamma>' \<Turnstile> \<Lambda> :: \<Gamma>'' \<Longrightarrow> 
    \<Gamma> \<Turnstile> \<delta> # \<Lambda> :: \<Gamma>''"

inductive_cases [elim]: "\<Gamma> \<Turnstile> [] :: \<Gamma>'"
inductive_cases [elim]: "\<Gamma> \<Turnstile> \<delta> # \<Lambda> :: \<Gamma>'"

inductive typecheck_prog :: "prog \<Rightarrow> (name \<rightharpoonup> type \<times> type) \<Rightarrow> type \<Rightarrow> bool" 
    (infix "\<TTurnstile> _ :" 60) where
  tcp_prog [simp]: "Map.empty \<Turnstile> \<Lambda> :: \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> v : t\<^sub>1 \<Longrightarrow> 
    Prog \<Lambda> e v \<TTurnstile> \<Gamma> : t\<^sub>2"

inductive_cases [elim]: "Prog \<Lambda> e v \<TTurnstile> \<Gamma> : t"

primrec assemble_context' :: "decl \<Rightarrow> name \<rightharpoonup> expr" where
  "assemble_context' (TypeDecl x F) = Map.empty"
| "assemble_context' (ExprDecl x e) = [x \<mapsto> e]"

primrec assemble_context :: "decl list \<Rightarrow> name \<rightharpoonup> expr" where
  "assemble_context [] = Map.empty"
| "assemble_context (\<delta> # \<Lambda>) = assemble_context' \<delta> ++ assemble_context \<Lambda>"

primrec is_completed :: "prog \<Rightarrow> bool" where
  "is_completed (Prog \<Lambda> e v) = (e = \<epsilon>)"

inductive evaluate_prog :: "prog \<Rightarrow> prog \<Rightarrow> bool" (infix "\<leadsto>" 60) where
  ev_prog [simp]: "assemble_context \<Lambda> \<turnstile> e \<cdot> v \<leadsto> e' \<cdot> v' \<Longrightarrow> Prog \<Lambda> e v \<leadsto> Prog \<Lambda> e' v'"

inductive_cases [elim]: "Prog \<Lambda> e v \<leadsto> \<Pi>"

(* safety *)

lemma [simp]: "assemble_context (\<Lambda> @ \<Lambda>') = assemble_context \<Lambda> ++ assemble_context \<Lambda>'"
  by (induction \<Lambda>) simp_all

lemma [simp]: "x \<notin> binder a \<Longrightarrow> x \<notin> dom (assemble_context' a)"
  by (induction a) simp_all

lemma [simp]: "x \<notin> binders \<Lambda> \<Longrightarrow> x \<notin> dom (assemble_context \<Lambda>)"
  by (induction \<Lambda>) simp_all

lemma [simp]: "\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<tturnstile> \<Lambda> \<Longrightarrow> x \<notin> dom \<Lambda> \<Longrightarrow> \<Gamma>(x \<mapsto> (t\<^sub>1, t\<^sub>2)) \<tturnstile> \<Lambda>(x \<mapsto> e)"
  proof (unfold typecheck_context_def, rule, rule, rule, rule)
    fix y t\<^sub>1' t\<^sub>2'
    assume A: "\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2"
       and B: "\<forall>x t\<^sub>1 t\<^sub>2. \<Gamma> x = Some (t\<^sub>1, t\<^sub>2) \<longrightarrow> (\<exists>e. \<Lambda> x = Some e \<and> \<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2)"
       and C: "x \<notin> dom \<Lambda>"
       and D: "(\<Gamma>(x \<mapsto> (t\<^sub>1, t\<^sub>2))) y = Some (t\<^sub>1', t\<^sub>2')"
    moreover hence E: "x \<notin> dom \<Gamma>" by auto
    ultimately show "\<exists>e'. (\<Lambda>(x \<mapsto> e)) y = Some e' \<and> \<Gamma>(x \<mapsto> (t\<^sub>1, t\<^sub>2)) \<turnstile> e' : t\<^sub>1' \<rightarrow> t\<^sub>2'"
      proof (cases "x = y")
      case False
        with B D obtain e' where "\<Lambda> y = Some e' \<and> \<Gamma> \<turnstile> e' : t\<^sub>1' \<rightarrow> t\<^sub>2'" by fastforce
        with E False show ?thesis by simp
      qed simp_all
  qed

lemma assemble_postpend: "\<Gamma> \<Turnstile> \<delta> : \<Gamma>' \<Longrightarrow> \<Gamma> \<tturnstile> assemble_context \<Lambda> \<Longrightarrow> binder \<delta> \<inter> binders \<Lambda> = {} \<Longrightarrow> 
    \<Gamma>' \<tturnstile> assemble_context (\<Lambda> @ [\<delta>])"
  proof (induction \<Gamma> \<delta> \<Gamma>' rule: typecheck_decl.induct)
  case (tcd_expr \<Gamma> e t\<^sub>1 t\<^sub>2 x)
    hence "\<Gamma>(x \<mapsto> (t\<^sub>1, t\<^sub>2)) \<tturnstile> assemble_context (\<Lambda> @ [ExprDecl x e])" by simp
    thus ?case by blast
  qed simp_all

lemma tc_assemble_context [simp]: "\<Gamma> \<Turnstile> \<Lambda>' :: \<Gamma>' \<Longrightarrow> \<Gamma> \<tturnstile> assemble_context \<Lambda> \<Longrightarrow> 
    binders \<Lambda> \<inter> binders \<Lambda>' = {} \<Longrightarrow> \<Gamma>' \<tturnstile> assemble_context \<Lambda> ++ assemble_context \<Lambda>'"
  proof (induction \<Gamma> \<Lambda>' \<Gamma>' arbitrary: \<Lambda> rule: typecheck_decls.induct)
  case tcd_nil
    thus ?case by simp
  next case (tcd_cons \<Gamma> \<delta> \<Gamma>' \<Lambda>' \<Gamma>'')
    moreover hence "\<Gamma>' \<tturnstile> assemble_context (\<Lambda> @ [\<delta>])" using assemble_postpend by fastforce
    moreover from tcd_cons have "binders (\<Lambda> @ [\<delta>]) \<inter> binders \<Lambda>' = {}" by auto
    ultimately have "\<Gamma>'' \<tturnstile> assemble_context (\<Lambda> @ [\<delta>]) ++ assemble_context \<Lambda>'" by blast
    thus ?case by simp
  qed

lemma [simp]: "Map.empty \<Turnstile> \<Lambda> :: \<Gamma> \<Longrightarrow> \<Gamma> \<tturnstile> assemble_context \<Lambda>"
  proof -
    assume "Map.empty \<Turnstile> \<Lambda> :: \<Gamma>"
    moreover have "Map.empty \<tturnstile> assemble_context []" by (simp add: typecheck_context_def)
    ultimately show "\<Gamma> \<tturnstile> assemble_context \<Lambda>" using tc_assemble_context by fastforce
  qed

theorem progress [simp]: "\<Pi> \<TTurnstile> \<Gamma> : t \<Longrightarrow> is_completed \<Pi> \<or> (\<exists>\<Pi>'. \<Pi> \<leadsto> \<Pi>')"
  proof (induction \<Pi> \<Gamma> t rule: typecheck_prog.induct)
  case (tcp_prog \<Lambda> \<Gamma> e t\<^sub>1 t\<^sub>2 v)
    thus ?case 
      proof (cases "e = \<epsilon>")
      case False
        with tcp_prog obtain e' v' where "assemble_context \<Lambda> \<turnstile> e \<cdot> v \<leadsto> e' \<cdot> v'" by fastforce
        hence "Prog \<Lambda> e v \<leadsto> Prog \<Lambda> e' v'" by simp
        thus ?thesis by fastforce
      qed simp_all
  qed

theorem preservation [simp]: "\<Pi> \<leadsto> \<Pi>' \<Longrightarrow> \<Pi> \<TTurnstile> \<Gamma> : t \<Longrightarrow> \<Pi>' \<TTurnstile> \<Gamma> : t"
  proof (induction \<Pi> \<Pi>' rule: evaluate_prog.induct)
  case (ev_prog \<Lambda> e v e' v')
    then obtain t\<^sub>1 where "(Map.empty \<Turnstile> \<Lambda> :: \<Gamma>) \<and> (\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t) \<and> \<Gamma> \<turnstile> v : t\<^sub>1" by fastforce
    moreover with ev_prog obtain t\<^sub>3 where "(\<Gamma> \<turnstile> e' : t\<^sub>3 \<rightarrow> t) \<and> \<Gamma> \<turnstile> v' : t\<^sub>3" by fastforce
    ultimately show ?case by fastforce
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

lemma [simp]: "\<Pi> \<Down>\<Down> v \<Longrightarrow> \<Pi> \<TTurnstile> \<Gamma> : t \<Longrightarrow> \<Gamma> \<turnstile> v : t"
  by (induction \<Pi> v rule: total_evaluate_prog'.induct) auto

theorem total_preservation: "\<Pi> \<Down> v \<Longrightarrow> \<Pi> \<TTurnstile> \<Gamma> : t \<Longrightarrow> \<Gamma> \<turnstile> v : t"
  by simp

end
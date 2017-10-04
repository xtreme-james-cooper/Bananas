theory BananasProgram
imports BananasExpression
begin

datatype decl = 
  TypeDecl name "(name \<times> type list) list"
| ExprDecl name expr

primrec binders\<^sub>d :: "decl \<Rightarrow> name set" where
  "binders\<^sub>d (TypeDecl x cts) = fst ` set cts"
| "binders\<^sub>d (ExprDecl x e) = {x}"

fun binders :: "decl list \<Rightarrow> name set" where
  "binders \<Lambda> = \<Union> (binders\<^sub>d ` set \<Lambda>)"

datatype prog = Prog "decl list" expr val

fun typecheck\<^sub>c :: "(name \<times> type list) list \<Rightarrow> (name \<rightharpoonup> type) \<times> funct" where
  "typecheck\<^sub>c [] = (Map.empty, K \<zero>)" 
| "typecheck\<^sub>c ((x, ts) # cts) = (
    let (\<Gamma>, Fs) = typecheck\<^sub>c cts
    in (\<Gamma>(x \<mapsto> foldr (op \<otimes>) ts \<one>), Fs \<Oplus> (foldr (\<lambda>t f. K t \<Otimes> f) ts (K \<one>))))"

fun bind_with_names :: "name \<Rightarrow> (name \<rightharpoonup> type) \<Rightarrow> name \<rightharpoonup> type \<times> type" where
  "bind_with_names n \<Gamma> x = map_option (\<lambda>t. (t, Named n)) (\<Gamma> x)"

inductive typecheck_decl :: "(name \<rightharpoonup> type \<times> type) \<Rightarrow> (name \<rightharpoonup> funct) \<Rightarrow> decl \<Rightarrow> 
    (name \<rightharpoonup> type \<times> type) \<Rightarrow> (name \<rightharpoonup> funct) \<Rightarrow> bool" (infix " & _ \<Turnstile> _ : _ &" 60) where
  tcd_type [simp]: "typecheck\<^sub>c cts = (\<Gamma>', F) \<Longrightarrow> 
    \<Gamma> & \<Sigma> \<Turnstile> TypeDecl x cts : \<Gamma> ++ bind_with_names x \<Gamma>' & \<Sigma>(x \<mapsto> F)"
| tcd_expr [simp]: "\<Gamma> & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> & \<Sigma> \<Turnstile> ExprDecl x e : \<Gamma>(x \<mapsto> (t\<^sub>1, t\<^sub>2)) & \<Sigma>"

inductive_cases [elim]: "\<Gamma> & \<Sigma> \<Turnstile> TypeDecl x F : \<Gamma>' & \<Sigma>'"
inductive_cases [elim]: "\<Gamma> & \<Sigma> \<Turnstile> ExprDecl x e : \<Gamma>' & \<Sigma>'"

inductive typecheck_decls :: "(name \<rightharpoonup> type \<times> type) \<Rightarrow> (name \<rightharpoonup> funct) \<Rightarrow> decl list \<Rightarrow> 
    (name \<rightharpoonup> type \<times> type) \<Rightarrow> (name \<rightharpoonup> funct) \<Rightarrow> bool" (infix "& _ \<Turnstile> _ :: _ &" 60) where
  tcd_nil [simp]: "\<Gamma> & \<Sigma> \<Turnstile> [] :: \<Gamma> & \<Sigma>"
| tcd_cons [simp]: "\<Gamma> & \<Sigma> \<Turnstile> \<delta> : \<Gamma>' & \<Sigma>' \<Longrightarrow> binders\<^sub>d \<delta> \<inter> binders \<Lambda> = {} \<Longrightarrow> 
    \<Gamma>' & \<Sigma> \<Turnstile> \<Lambda> :: \<Gamma>'' & \<Sigma>'' \<Longrightarrow> \<Gamma> & \<Sigma> \<Turnstile> \<delta> # \<Lambda> :: \<Gamma>'' & \<Sigma>''"

inductive_cases [elim]: "\<Gamma> & \<Sigma> \<Turnstile> [] :: \<Gamma>' & \<Sigma>'"
inductive_cases [elim]: "\<Gamma> & \<Sigma> \<Turnstile> \<delta> # \<Lambda> :: \<Gamma>' & \<Sigma>'"

inductive typecheck_prog :: "prog \<Rightarrow> (name \<rightharpoonup> type \<times> type) \<Rightarrow> (name \<rightharpoonup> funct) \<Rightarrow> type \<Rightarrow> bool" 
    (infix "\<TTurnstile> _ & _ :" 60) where
  tcp_prog [simp]: "Map.empty & Map.empty \<Turnstile> \<Lambda> :: \<Gamma> & \<Sigma> \<Longrightarrow> \<Gamma> & \<Sigma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> 
    \<Gamma> & \<Sigma> \<turnstile> v : t\<^sub>1 \<Longrightarrow> Prog \<Lambda> e v \<TTurnstile> \<Gamma> & \<Sigma> : t\<^sub>2"

inductive_cases [elim]: "Prog \<Lambda> e v \<TTurnstile> \<Gamma> & \<Sigma> : t"

fun assemble_context\<^sub>c :: "name \<Rightarrow> (name \<times> type list) list \<Rightarrow> name \<rightharpoonup> expr" where
  "assemble_context\<^sub>c n [] = Map.empty"
| "assemble_context\<^sub>c n ((x, t) # cts) = 
    (map_option (op \<cdot> \<iota>\<^sub>r) o assemble_context\<^sub>c n cts)(x \<mapsto> \<prec>\<^bsub>n\<^esub> \<cdot> \<iota>\<^sub>l)"

primrec assemble_context' :: "decl \<Rightarrow> name \<rightharpoonup> expr" where
  "assemble_context' (TypeDecl x cts) = assemble_context\<^sub>c x cts"
| "assemble_context' (ExprDecl x e) = [x \<mapsto> e]"

primrec assemble_context :: "decl list \<Rightarrow> name \<rightharpoonup> expr" where
  "assemble_context [] = Map.empty"
| "assemble_context (\<delta> # \<Lambda>) = assemble_context' \<delta> ++ assemble_context \<Lambda>"

primrec is_completed :: "prog \<Rightarrow> bool" where
  "is_completed (Prog \<Lambda> e v) = (e = \<epsilon>)"

inductive evaluate_prog :: "prog \<Rightarrow> prog \<Rightarrow> bool" (infix "\<leadsto>" 60) where
  ev_prog [simp]: "assemble_context \<Lambda> & \<Sigma> \<turnstile> e \<cdot> v \<leadsto> e' \<cdot> v' \<Longrightarrow> Prog \<Lambda> e v \<leadsto> Prog \<Lambda> e' v'"

inductive_cases [elim]: "Prog \<Lambda> e v \<leadsto> \<Pi>"

(* safety *)

lemma [simp]: "assemble_context (\<Lambda> @ \<Lambda>') = assemble_context \<Lambda> ++ assemble_context \<Lambda>'"
  by (induction \<Lambda>) simp_all

lemma [simp]: "x \<notin> fst ` set cts \<Longrightarrow> x \<notin> dom (assemble_context\<^sub>c F cts)"
  by (induction cts rule: assemble_context\<^sub>c.induct) simp_all

lemma [simp]: "x \<notin> binders\<^sub>d a \<Longrightarrow> x \<notin> dom (assemble_context' a)"
  by (induction a) simp_all

lemma [simp]: "x \<notin> binders \<Lambda> \<Longrightarrow> x \<notin> dom (assemble_context \<Lambda>)"
  by (induction \<Lambda>) simp_all

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

lemma [simp]: "bind_with_names x Map.empty = Map.empty"
  by auto

lemma [simp]: "bind_with_names x (\<Gamma>(y \<mapsto> t)) = (bind_with_names x \<Gamma>)(y \<mapsto> (t, Named x))"
  by auto

lemma add_constructors: "typecheck\<^sub>c cts = (\<Gamma>', F) \<Longrightarrow> \<Gamma> & \<Sigma> \<tturnstile> assemble_context \<Lambda> \<Longrightarrow> 
  fst ` set cts \<inter> binders \<Lambda> = {} \<Longrightarrow> 
    \<Gamma> ++ bind_with_names x \<Gamma>' & \<Sigma> \<tturnstile> assemble_context \<Lambda> ++ assemble_context\<^sub>c F cts"
  proof (induction cts arbitrary: \<Gamma>' F rule: typecheck\<^sub>c.induct)
  case (2 y ts cts)
    then obtain \<Gamma>'' Fs where G: "typecheck\<^sub>c cts = (\<Gamma>'', Fs) \<and> \<Gamma>' = \<Gamma>''(y \<mapsto> foldr op \<otimes> ts \<one>) \<and> 
      F = Fs \<Oplus> foldr (\<lambda>t. op \<Otimes> (K t)) ts (K \<one>)" by (auto split: prod.splits)
    with 2 have "\<Gamma> ++ bind_with_names x \<Gamma>'' \<tturnstile> assemble_context \<Lambda> ++ assemble_context\<^sub>c Fs cts" by fastforce

    let ?t = "foldr op \<otimes> ts \<one>"
    let ?F = "Fs \<Oplus> foldr (\<lambda>t. op \<Otimes> (K t)) ts (K \<one>)"
    let ?\<Lambda> = "assemble_context \<Lambda>"


    from 2 have "\<Gamma> \<tturnstile> assemble_context \<Lambda>" by simp
    from 2 have "y \<notin> binders \<Lambda>" by simp
    from 2 have "fst ` set cts \<inter> binders \<Lambda> = {}" by simp


    have X: "(\<Gamma> ++ bind_with_names x \<Gamma>'') \<turnstile> \<prec>\<^bsub>?F\<^esub> \<cdot> \<iota>\<^sub>l : ?t \<rightarrow> Named x" by simp


    have Y: "(\<Gamma> ++ bind_with_names x \<Gamma>'') \<tturnstile> (?\<Lambda> ++ (map_option (op \<cdot> \<iota>\<^sub>r) \<circ> assemble_context\<^sub>c ?F cts))" by simp


    have "y \<notin> dom (?\<Lambda> ++ (map_option (op \<cdot> \<iota>\<^sub>r) \<circ> assemble_context\<^sub>c ?F cts))" by simp
    with X Y G have "\<Gamma> ++ bind_with_names x \<Gamma>' \<tturnstile> ?\<Lambda> ++ assemble_context\<^sub>c F ((y, ts) # cts)" by simp
    thus ?case by blast
  qed auto

lemma assemble_postpend: "\<Gamma> & \<Sigma> \<Turnstile> \<delta> : \<Gamma>' & \<Sigma>' \<Longrightarrow> \<Gamma> \<tturnstile> assemble_context \<Lambda> \<Longrightarrow> 
    binders\<^sub>d \<delta> \<inter> binders \<Lambda> = {} \<Longrightarrow> \<Gamma>' \<tturnstile> assemble_context (\<Lambda> @ [\<delta>])"
  proof (induction \<Gamma> \<Sigma> \<delta> \<Gamma>' \<Sigma>' rule: typecheck_decl.induct)
  case tcd_type
    thus ?case using add_constructors by simp
  next case (tcd_expr \<Gamma> e t\<^sub>1 t\<^sub>2 \<Sigma> x)
    hence "\<Gamma>(x \<mapsto> (t\<^sub>1, t\<^sub>2)) \<tturnstile> assemble_context (\<Lambda> @ [ExprDecl x e])" by simp
    thus ?case by blast
  qed

lemma tc_assemble_context [simp]: "\<Gamma> & \<Sigma> \<Turnstile> \<Lambda>' :: \<Gamma>' & \<Sigma>' \<Longrightarrow> \<Gamma> \<tturnstile> assemble_context \<Lambda> \<Longrightarrow> 
    binders \<Lambda> \<inter> binders \<Lambda>' = {} \<Longrightarrow> \<Gamma>' \<tturnstile> assemble_context \<Lambda> ++ assemble_context \<Lambda>'"
  proof (induction \<Gamma> \<Sigma> \<Lambda>' \<Gamma>' \<Sigma>' arbitrary: \<Lambda> rule: typecheck_decls.induct)
  case tcd_nil
    thus ?case by simp
  next case (tcd_cons \<Gamma> \<Sigma> \<delta> \<Gamma>' \<Sigma>' \<Lambda>' \<Gamma>'')
    moreover hence "\<Gamma>' \<tturnstile> assemble_context (\<Lambda> @ [\<delta>])" using assemble_postpend by fastforce
    moreover from tcd_cons have "binders (\<Lambda> @ [\<delta>]) \<inter> binders \<Lambda>' = {}" by auto
    ultimately have "\<Gamma>'' \<tturnstile> assemble_context (\<Lambda> @ [\<delta>]) ++ assemble_context \<Lambda>'" by blast
    thus ?case by simp
  qed

lemma [simp]: "Map.empty & Map.empty \<Turnstile> \<Lambda> :: \<Gamma> & \<Sigma> \<Longrightarrow> \<Gamma> \<tturnstile> assemble_context \<Lambda>"
  proof -
    assume "Map.empty & Map.empty \<Turnstile> \<Lambda> :: \<Gamma> & \<Sigma>"
    moreover have "Map.empty \<tturnstile> assemble_context []" by (simp add: typecheck_context_def)
    ultimately show "\<Gamma> \<tturnstile> assemble_context \<Lambda>" using tc_assemble_context by fastforce
  qed

theorem progress [simp]: "\<Pi> \<TTurnstile> \<Gamma> & \<Sigma> : t \<Longrightarrow> is_completed \<Pi> \<or> (\<exists>\<Pi>'. \<Pi> \<leadsto> \<Pi>')"
  proof (induction \<Pi> \<Gamma> \<Sigma> t rule: typecheck_prog.induct)
  case (tcp_prog \<Lambda> \<Gamma> \<Sigma> e t\<^sub>1 t\<^sub>2 v)
    thus ?case 
      proof (cases "e = \<epsilon>")
      case False
        with tcp_prog obtain e' v' where "assemble_context \<Lambda> \<turnstile> e \<cdot> v \<leadsto> e' \<cdot> v'" by fastforce
        hence "Prog \<Lambda> e v \<leadsto> Prog \<Lambda> e' v'" by simp
        thus ?thesis by fastforce
      qed simp_all
  qed

theorem preservation [simp]: "\<Pi> \<leadsto> \<Pi>' \<Longrightarrow> \<Pi> \<TTurnstile> \<Gamma> & \<Sigma> : t \<Longrightarrow> \<Pi>' \<TTurnstile> \<Gamma> & \<Sigma> : t"
  proof (induction \<Pi> \<Pi>' rule: evaluate_prog.induct)
  case (ev_prog \<Lambda> e v e' v')
    then obtain t\<^sub>1 where "(Map.empty & Map.empty \<Turnstile> \<Lambda> :: \<Gamma> & \<Sigma>) \<and> (\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t) \<and> \<Gamma> \<turnstile> v : t\<^sub>1" 
      by fastforce
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

lemma [simp]: "\<Pi> \<Down>\<Down> v \<Longrightarrow> \<Pi> \<TTurnstile> \<Gamma> & \<Sigma> : t \<Longrightarrow> \<Gamma> \<turnstile> v : t"
  by (induction \<Pi> v rule: total_evaluate_prog'.induct) auto

theorem total_preservation: "\<Pi> \<Down> v \<Longrightarrow> \<Pi> \<TTurnstile> \<Gamma> & \<Sigma> : t \<Longrightarrow> \<Gamma> \<turnstile> v : t"
  by simp

end
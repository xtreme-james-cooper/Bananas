theory BananasBigStepDynamics
imports BananasSafety
begin

inductive total_eval :: "dynamic_environment \<Rightarrow> expr \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool" 
    (infix "\<turnstile> _ \<cdot> _ \<Down>" 60) where
  tev_base [simp]: "\<Lambda> \<turnstile> \<epsilon> \<cdot> v \<Down> v"
| tev_step [simp]: "\<Lambda> \<turnstile> e \<cdot> v \<leadsto> e' \<cdot> v' \<Longrightarrow> \<Lambda> \<turnstile> e' \<cdot> v' \<Down> v'' \<Longrightarrow> \<Lambda> \<turnstile> e \<cdot> v \<Down> v''"

inductive total_evaluate_prog :: "prog \<Rightarrow> val \<Rightarrow> bool" (infix "\<Down>" 60) where
  ptev_base [simp]: "Prog \<Delta> \<epsilon> v \<Down> v"
| ptev_step [simp]: "Prog \<Delta> e v \<leadsto> Prog \<Delta> e' v' \<Longrightarrow> Prog \<Delta> e' v' \<Down> v'' \<Longrightarrow> Prog \<Delta> e v \<Down> v''"

inductive total_evaluate_prog' :: "prog \<Rightarrow> val \<Rightarrow> bool" (infix "\<Down>\<Down>" 60) where
  ptev_step' [simp]: "assemble_context empty_static \<Delta> \<Lambda> \<Longrightarrow> \<Lambda> \<turnstile> e \<cdot> v \<Down> v' \<Longrightarrow> Prog \<Delta> e v \<Down>\<Down> v'"

inductive_cases [elim]: "Prog \<Lambda> e v \<Down>\<Down> v'"

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

lemma [simp]: "\<Lambda> \<turnstile> f\<^sub>1 \<cdot> v\<^sub>1 \<Down> v\<^sub>3 \<Longrightarrow> \<Lambda> \<turnstile> f\<^sub>2 \<cdot> v\<^sub>2 \<Down> v\<^sub>4 \<Longrightarrow> 
    \<Lambda> \<turnstile> f\<^sub>1 \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<Down> PairV v\<^sub>3 v\<^sub>4"
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

lemma [simp]: "\<Pi> \<Down> v = \<Pi> \<Down>\<Down> v"
  proof
    show "\<Pi> \<Down> v \<Longrightarrow> \<Pi> \<Down>\<Down> v" by (induction \<Pi> v rule: total_evaluate_prog.induct) fastforce+
  next 
    assume "\<Pi> \<Down>\<Down> v"
    thus "\<Pi> \<Down> v"
      proof (induction \<Pi> v rule: total_evaluate_prog'.induct)
      case (ptev_step' \<Delta> \<Lambda> e v v')
        with ptev_step'(2) show ?case 
          proof (induction \<Lambda> e v v' rule: total_eval.induct)
          case (tev_step \<Lambda> e v e' v' v'')
            moreover hence "Prog \<Delta> e v \<leadsto> Prog \<Delta> e' v'" by simp
            ultimately show ?case by (metis total_evaluate_prog.ptev_step)
          qed simp_all
      qed
  qed

(* since we are a turing-complete language, total progress is not provable *)

theorem total_expr_preservation [simp]: "\<Lambda> \<turnstile> e \<cdot> v \<Down> v' \<Longrightarrow> \<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> 
    \<Gamma> \<turnstile> v : t\<^sub>1 \<Longrightarrow> \<Gamma> \<tturnstile> \<Lambda> \<Longrightarrow> \<Gamma> \<turnstile> v' : t\<^sub>2"
  proof (induction \<Lambda> e v v' arbitrary: t\<^sub>1 rule: total_eval.induct)
  case (tev_step \<Lambda> e v e' v' v'')
    moreover then obtain t\<^sub>3 where "(\<Gamma> \<turnstile> e' : t\<^sub>3 \<rightarrow> t\<^sub>2) \<and> (\<Gamma> \<turnstile> v' : t\<^sub>3)" 
      by (metis expr_preservation)
    ultimately show ?case by fastforce
  qed auto

lemma [simp]: "\<Pi> \<Down>\<Down> v \<Longrightarrow> \<Pi> \<TTurnstile> \<Gamma> \<rightarrow> t \<Longrightarrow> \<Gamma> \<turnstile> v : t"
  by (induction \<Pi> v rule: total_evaluate_prog'.induct) auto

theorem total_preservation: "\<Pi> \<Down> v \<Longrightarrow> \<Pi> \<TTurnstile> \<Gamma> \<rightarrow> t \<Longrightarrow> \<Gamma> \<turnstile> v : t"
  by simp

end
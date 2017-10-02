theory PartialEvaluation
imports BananasLanguage
begin

fun partial_evaluation :: "nat \<Rightarrow> expr \<Rightarrow> val \<Rightarrow> val option" where
  "partial_evaluation n \<epsilon> v = Some v"
| "partial_evaluation n (\<kappa> v\<^sub>1) v\<^sub>2 = Some v\<^sub>1"
| "partial_evaluation n (f \<cdot> g) v = (case partial_evaluation n g v of 
      Some v' \<Rightarrow> partial_evaluation n f v'
    | None \<Rightarrow> None)"
| "partial_evaluation n \<pi>\<^sub>1 (PairV v\<^sub>1 v\<^sub>2) = Some v\<^sub>1"
| "partial_evaluation n \<pi>\<^sub>1 _ = None"
| "partial_evaluation n \<pi>\<^sub>2 (PairV v\<^sub>1 v\<^sub>2) = Some v\<^sub>2"
| "partial_evaluation n \<pi>\<^sub>2 _ = None"
| "partial_evaluation n (f\<^sub>1 \<parallel> f\<^sub>2) (PairV v\<^sub>1 v\<^sub>2) = (case partial_evaluation n f\<^sub>1 v\<^sub>1 of 
      Some v\<^sub>1' \<Rightarrow> (case partial_evaluation n f\<^sub>2 v\<^sub>2 of 
          Some v\<^sub>2' \<Rightarrow> Some (PairV v\<^sub>1' v\<^sub>2')
        | None \<Rightarrow> None)
    | None \<Rightarrow> None)"
| "partial_evaluation n (f\<^sub>1 \<parallel> f\<^sub>2) _ = None"
| "partial_evaluation n \<Theta> v = Some (PairV v v)"
| "partial_evaluation n \<iota>\<^sub>l v = Some (InlV v)"
| "partial_evaluation n \<iota>\<^sub>r v = Some (InrV v)"
| "partial_evaluation n \<Xi> (InlV v) = Some v"
| "partial_evaluation n \<Xi> (InrV v) = Some v"
| "partial_evaluation n \<Xi> _ = None"
| "partial_evaluation n (f\<^sub>l \<bar> f\<^sub>r) (InlV v) = partial_evaluation n (\<iota>\<^sub>l \<cdot> f\<^sub>l) v"
| "partial_evaluation n (f\<^sub>l \<bar> f\<^sub>r) (InrV v) = partial_evaluation n (\<iota>\<^sub>r \<cdot> f\<^sub>r) v"
| "partial_evaluation n (f\<^sub>l \<bar> f\<^sub>r) _ = None"
| "partial_evaluation n \<rhd> (PairV (InlV v\<^sub>1) v\<^sub>2) = Some (InlV (PairV v\<^sub>1 v\<^sub>2))"
| "partial_evaluation n \<rhd> (PairV (InrV v\<^sub>1) v\<^sub>2) = Some (InrV (PairV v\<^sub>1 v\<^sub>2))"
| "partial_evaluation n \<rhd> _ = None"
| "partial_evaluation (Suc n) $ (PairV (FunV e) v) = partial_evaluation n e v"
| "partial_evaluation n $ _ = None"
| "partial_evaluation n (g \<leftarrow> f) (FunV e) = Some (FunV (g \<cdot> e \<cdot> f))"
| "partial_evaluation n (g \<leftarrow> f) _ = None"
| "partial_evaluation n \<succ>\<^bsub>F\<^esub> v = Some (InjV F v)"
| "partial_evaluation n \<prec>\<^bsub>F\<^esub> (InjV G v) = (if F = G then Some v else None)"
| "partial_evaluation n \<prec>\<^bsub>F\<^esub> _ = None"
| "partial_evaluation (Suc n) \<lparr> f \<rparr>\<^bsub>F\<^esub> v = partial_evaluation n (f \<cdot> \<lparr> f \<rparr>\<^bsub>F\<^esub> \<bullet> F \<cdot> \<prec>\<^bsub>F\<^esub>) v"
| "partial_evaluation 0 \<lparr> f \<rparr>\<^bsub>F\<^esub> _ = None"
| "partial_evaluation (Suc n) \<lbrakk> f \<rbrakk>\<^bsub>F\<^esub> v = partial_evaluation n (\<succ>\<^bsub>F\<^esub> \<cdot> \<lbrakk> f \<rbrakk>\<^bsub>F\<^esub> \<bullet> F \<cdot> f) v"
| "partial_evaluation 0 \<lbrakk> f \<rbrakk>\<^bsub>F\<^esub> _ = None"

theorem soundness: "partial_evaluation n e v = Some v' \<Longrightarrow> e \<cdot> v \<Down> v'"
  proof (induction n e v arbitrary: v' rule: partial_evaluation.induct)
  case 3
    thus ?case by (simp split: option.splits) fastforce
  next case 8
    thus ?case by (auto split: option.splits)
  next case (16 n f\<^sub>l f\<^sub>r v)
    hence "(\<iota>\<^sub>l \<cdot> f\<^sub>l) \<cdot> v \<Down> v'" by simp
    moreover have "f\<^sub>l \<bar> f\<^sub>r \<cdot> InlV v \<leadsto> (\<iota>\<^sub>l \<cdot> f\<^sub>l) \<cdot> v" by simp
    ultimately show ?case by (metis tev_step)
  next case (17 n f\<^sub>l f\<^sub>r v)
    hence "(\<iota>\<^sub>r \<cdot> f\<^sub>r) \<cdot> v \<Down> v'" by simp
    moreover have "f\<^sub>l \<bar> f\<^sub>r \<cdot> InrV v \<leadsto> (\<iota>\<^sub>r \<cdot> f\<^sub>r) \<cdot> v" by simp
    ultimately show ?case by (metis tev_step)
  next case (22 n e v)
    hence "e \<cdot> v \<Down> v'" by simp
    moreover have "$ \<cdot> PairV (FunV e) v \<leadsto> e \<cdot> v" by simp
    ultimately show ?case by (metis tev_step)
  next case 27
    thus ?case by (simp split: if_splits)
  next case (29 n f F v)
    hence "(f \<cdot> \<lparr> f \<rparr>\<^bsub>F\<^esub> \<bullet> F \<cdot> \<prec>\<^bsub>F\<^esub>) \<cdot> v \<Down> v'" by (auto split: option.splits)
    moreover have "\<lparr> f \<rparr>\<^bsub>F\<^esub> \<cdot> v \<leadsto> (f \<cdot> \<lparr> f \<rparr>\<^bsub>F\<^esub> \<bullet> F \<cdot> \<prec>\<^bsub>F\<^esub>) \<cdot> v" by simp
    ultimately show ?case by (metis tev_step)
  next case (31 n f F v)
    hence "(\<succ>\<^bsub>F\<^esub> \<cdot> \<lbrakk> f \<rbrakk>\<^bsub>F\<^esub> \<bullet> F \<cdot> f) \<cdot> v \<Down> v'" by (auto split: option.splits)
    moreover have "\<lbrakk> f \<rbrakk>\<^bsub>F\<^esub> \<cdot> v \<leadsto> (\<succ>\<^bsub>F\<^esub> \<cdot> \<lbrakk> f \<rbrakk>\<^bsub>F\<^esub> \<bullet> F \<cdot> f) \<cdot> v" by simp
    ultimately show ?case by (metis tev_step)
  qed auto

lemma pev_larger [elim]: "partial_evaluation n e v = Some v' \<Longrightarrow> n \<le> m \<Longrightarrow> 
    partial_evaluation m e v = Some v'"
  proof (induction n e v arbitrary: m rule: partial_evaluation.induct)
  case 3
    thus ?case by simp
  next case 8
    thus ?case by simp
  next case 22
    thus ?case by simp
  next case 29
    thus ?case by simp
  next case 31
    thus ?case by simp
  qed simp_all

theorem completeness: "e \<cdot> v \<Down> v' \<Longrightarrow> \<exists>n. partial_evaluation n e v = Some v'"
  proof (induction e v v' rule: total_eval.induct)
  case (tev_step e v e' v' v'')
    thus ?case
      proof (induction e v e' v' arbitrary: v'' rule: evaluate.induct)
      case (ev_comp1 g v g' v' f)
        moreover then obtain n v\<^sub>1 where N: "partial_evaluation n g' v' = Some v\<^sub>1 \<and> 
          partial_evaluation n f v\<^sub>1 = Some v''" by (auto split: option.splits)
        moreover hence "g' \<cdot> v' \<Down> v\<^sub>1" by (metis soundness)
        ultimately obtain m where M: "partial_evaluation m g v = Some v\<^sub>1" by auto
        have "max n m \<ge> m \<and> max n m \<ge> n" by simp
        with M N have "partial_evaluation (max n m) f v\<^sub>1 = Some v'' \<and> 
          partial_evaluation (max n m) g v = Some v\<^sub>1" by (metis pev_larger)
        hence "partial_evaluation (max n m) (f \<cdot> g) v = Some v''" by simp
        thus ?case by fastforce
      next case (ev_pair1 f\<^sub>1 v\<^sub>1 f\<^sub>1' v\<^sub>1' f\<^sub>2 v\<^sub>2)
        then obtain n v\<^sub>1'' v\<^sub>2' where N: "partial_evaluation n f\<^sub>1' v\<^sub>1' = Some v\<^sub>1'' \<and> 
          partial_evaluation n f\<^sub>2 v\<^sub>2 = Some v\<^sub>2' \<and> v'' = PairV v\<^sub>1'' v\<^sub>2'" 
            by (auto split: option.splits) fastforce
        with ev_pair1 have "f\<^sub>1' \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1' v\<^sub>2 \<Down> PairV v\<^sub>1'' v\<^sub>2'" by simp
        hence "(f\<^sub>1' \<cdot> v\<^sub>1' \<Down> v\<^sub>1'') \<and> f\<^sub>2 \<cdot> v\<^sub>2 \<Down> v\<^sub>2'" by (metis pair_big_eval)
        with ev_pair1 N obtain m where M: "partial_evaluation m f\<^sub>1 v\<^sub>1 = Some v\<^sub>1''" by auto
        have "max n m \<ge> m \<and> max n m \<ge> n" by simp
        with M N have "partial_evaluation (max n m) f\<^sub>1 v\<^sub>1 = Some v\<^sub>1'' \<and> 
          partial_evaluation (max n m) f\<^sub>2 v\<^sub>2 = Some v\<^sub>2'" by (metis pev_larger)
        with N have "partial_evaluation (max n m) (f\<^sub>1 \<parallel> f\<^sub>2) (PairV v\<^sub>1 v\<^sub>2) = Some v''" by simp
        thus ?case by fastforce
      next case (ev_pair2 f\<^sub>2 v\<^sub>2 f\<^sub>2' v\<^sub>2' v\<^sub>1)
        then obtain n v\<^sub>2'' where V: "partial_evaluation n f\<^sub>2' v\<^sub>2' = Some v\<^sub>2'' \<and> v'' = PairV v\<^sub>1 v\<^sub>2''" 
          by (auto split: option.splits)
        with ev_pair2 have "\<epsilon> \<parallel> f\<^sub>2' \<cdot> PairV v\<^sub>1 v\<^sub>2' \<Down> PairV v\<^sub>1 v\<^sub>2''" by simp
        hence "f\<^sub>2' \<cdot> v\<^sub>2' \<Down> v\<^sub>2''" by (metis pair_big_eval)
        with ev_pair2 V obtain m where "partial_evaluation m f\<^sub>2 v\<^sub>2 = Some v\<^sub>2''" by auto
        with V have "partial_evaluation m (\<epsilon> \<parallel> f\<^sub>2) (PairV v\<^sub>1 v\<^sub>2) = Some v''" by simp
        thus ?case by fastforce
      next case (ev_app e v)
        then obtain n where "partial_evaluation n e v = Some v''" by blast
        hence "partial_evaluation (Suc n) $ (PairV (FunV e) v) = Some v''" by simp
        thus ?case by fastforce
      next case (ev_cata f F v)
        then obtain n where "partial_evaluation n (f \<cdot> \<lparr> f \<rparr>\<^bsub>F\<^esub> \<bullet> F \<cdot> \<prec>\<^bsub>F\<^esub>) v = Some v''" by blast
        hence "partial_evaluation (Suc n) \<lparr> f \<rparr>\<^bsub>F\<^esub> v = Some v''" by simp
        thus ?case by fastforce
      next case (ev_ana f F v)
        then obtain n where "partial_evaluation n (\<succ>\<^bsub>F\<^esub> \<cdot> \<lbrakk> f \<rbrakk>\<^bsub>F\<^esub> \<bullet> F \<cdot> f) v = Some v''" by blast
        hence "partial_evaluation (Suc n) \<lbrakk> f \<rbrakk>\<^bsub>F\<^esub> v = Some v''" by simp
        thus ?case by fastforce
      qed auto 
  qed simp_all

end
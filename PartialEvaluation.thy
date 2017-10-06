theory PartialEvaluation
imports BananasProgram
begin

fun partial_evaluation :: "dynamic_environment \<Rightarrow> nat \<Rightarrow> expr \<Rightarrow> val \<Rightarrow> val option" where
  "partial_evaluation \<Lambda> n \<epsilon> v = Some v"
| "partial_evaluation \<Lambda> n (\<kappa> v\<^sub>1) v\<^sub>2 = Some v\<^sub>1"
| "partial_evaluation \<Lambda> n (f \<cdot> g) v = (case partial_evaluation \<Lambda> n g v of 
      Some v' \<Rightarrow> partial_evaluation \<Lambda> n f v'
    | None \<Rightarrow> None)"
| "partial_evaluation \<Lambda> n \<pi>\<^sub>1 (PairV v\<^sub>1 v\<^sub>2) = Some v\<^sub>1"
| "partial_evaluation \<Lambda> n \<pi>\<^sub>1 _ = None"
| "partial_evaluation \<Lambda> n \<pi>\<^sub>2 (PairV v\<^sub>1 v\<^sub>2) = Some v\<^sub>2"
| "partial_evaluation \<Lambda> n \<pi>\<^sub>2 _ = None"
| "partial_evaluation \<Lambda> n (f\<^sub>1 \<parallel> f\<^sub>2) (PairV v\<^sub>1 v\<^sub>2) = (case partial_evaluation \<Lambda> n f\<^sub>1 v\<^sub>1 of 
      Some v\<^sub>1' \<Rightarrow> (case partial_evaluation \<Lambda> n f\<^sub>2 v\<^sub>2 of 
          Some v\<^sub>2' \<Rightarrow> Some (PairV v\<^sub>1' v\<^sub>2')
        | None \<Rightarrow> None)
    | None \<Rightarrow> None)"
| "partial_evaluation \<Lambda> n (f\<^sub>1 \<parallel> f\<^sub>2) _ = None"
| "partial_evaluation \<Lambda> n \<Theta> v = Some (PairV v v)"
| "partial_evaluation \<Lambda> n \<iota>\<^sub>l v = Some (InlV v)"
| "partial_evaluation \<Lambda> n \<iota>\<^sub>r v = Some (InrV v)"
| "partial_evaluation \<Lambda> n \<Xi> (InlV v) = Some v"
| "partial_evaluation \<Lambda> n \<Xi> (InrV v) = Some v"
| "partial_evaluation \<Lambda> n \<Xi> _ = None"
| "partial_evaluation \<Lambda> n (f\<^sub>l \<bar> f\<^sub>r) (InlV v) = partial_evaluation \<Lambda> n (\<iota>\<^sub>l \<cdot> f\<^sub>l) v"
| "partial_evaluation \<Lambda> n (f\<^sub>l \<bar> f\<^sub>r) (InrV v) = partial_evaluation \<Lambda> n (\<iota>\<^sub>r \<cdot> f\<^sub>r) v"
| "partial_evaluation \<Lambda> n (f\<^sub>l \<bar> f\<^sub>r) _ = None"
| "partial_evaluation \<Lambda> n \<rhd> (PairV (InlV v\<^sub>1) v\<^sub>2) = Some (InlV (PairV v\<^sub>1 v\<^sub>2))"
| "partial_evaluation \<Lambda> n \<rhd> (PairV (InrV v\<^sub>1) v\<^sub>2) = Some (InrV (PairV v\<^sub>1 v\<^sub>2))"
| "partial_evaluation \<Lambda> n \<rhd> _ = None"
| "partial_evaluation \<Lambda> (Suc n) $ (PairV (FunV e) v) = partial_evaluation \<Lambda> n e v"
| "partial_evaluation \<Lambda> n $ _ = None"
| "partial_evaluation \<Lambda> n (g \<leftarrow> f) (FunV e) = Some (FunV (g \<cdot> e \<cdot> f))"
| "partial_evaluation \<Lambda> n (g \<leftarrow> f) _ = None"
| "partial_evaluation \<Lambda> n \<succ>\<^bsub>x\<^esub> v = Some (InjV x v)"
| "partial_evaluation \<Lambda> n \<prec>\<^bsub>x\<^esub> (InjV y v) = Some v"
| "partial_evaluation \<Lambda> n \<prec>\<^bsub>x\<^esub> _ = None"
| "partial_evaluation \<Lambda> (Suc n) \<lparr> f \<rparr>\<^bsub>x\<^esub> v = (case var\<^sub>t_bind \<Lambda> x of 
      Some F \<Rightarrow> partial_evaluation \<Lambda> n (f \<cdot> \<lparr> f \<rparr>\<^bsub>x\<^esub> \<bullet> F \<cdot> \<prec>\<^bsub>x\<^esub>) v
    | None \<Rightarrow> None)"
| "partial_evaluation \<Lambda> 0 \<lparr> f \<rparr>\<^bsub>x\<^esub> _ = None"
| "partial_evaluation \<Lambda> (Suc n) \<lbrakk> f \<rbrakk>\<^bsub>x\<^esub> v = (case var\<^sub>t_bind \<Lambda> x of 
      Some F \<Rightarrow> partial_evaluation \<Lambda> n (\<succ>\<^bsub>x\<^esub> \<cdot> \<lbrakk> f \<rbrakk>\<^bsub>x\<^esub> \<bullet> F \<cdot> f) v
    | None \<Rightarrow> None)"
| "partial_evaluation \<Lambda> 0 \<lbrakk> f \<rbrakk>\<^bsub>x\<^esub> _ = None"
| "partial_evaluation \<Lambda> 0 (Var x) _ = None"
| "partial_evaluation \<Lambda> (Suc n) (Var x) v = (case var\<^sub>e_bind \<Lambda> x of 
      Some e \<Rightarrow> partial_evaluation \<Lambda> n e v 
    | None \<Rightarrow> None )"

primrec partial_eval_prog :: "nat \<Rightarrow> prog \<Rightarrow> val option" where
  "partial_eval_prog n (Prog \<Lambda> e v) = partial_evaluation (assemble_context \<Lambda>) n e v"

(* correctness *)

lemma soundness': "partial_evaluation \<Lambda> n e v = Some v' \<Longrightarrow> \<Lambda> \<turnstile> e \<cdot> v \<Down> v'"
  proof (induction \<Lambda> n e v arbitrary: v' rule: partial_evaluation.induct)
  case 3
    thus ?case by (simp split: option.splits) fastforce
  next case 8
    thus ?case by (auto split: option.splits)
  next case (16 \<Lambda> n f\<^sub>l f\<^sub>r v)
    hence "\<Lambda> \<turnstile> (\<iota>\<^sub>l \<cdot> f\<^sub>l) \<cdot> v \<Down> v'" by simp
    moreover have "\<Lambda> \<turnstile> f\<^sub>l \<bar> f\<^sub>r \<cdot> InlV v \<leadsto> (\<iota>\<^sub>l \<cdot> f\<^sub>l) \<cdot> v" by simp
    ultimately show ?case by (metis tev_step)
  next case (17 \<Lambda> n f\<^sub>l f\<^sub>r v)
    hence "\<Lambda> \<turnstile> (\<iota>\<^sub>r \<cdot> f\<^sub>r) \<cdot> v \<Down> v'" by simp
    moreover have "\<Lambda> \<turnstile> f\<^sub>l \<bar> f\<^sub>r \<cdot> InrV v \<leadsto> (\<iota>\<^sub>r \<cdot> f\<^sub>r) \<cdot> v" by simp
    ultimately show ?case by (metis tev_step)
  next case (22 \<Lambda> n e v)
    hence "\<Lambda> \<turnstile> e \<cdot> v \<Down> v'" by simp
    moreover have "\<Lambda> \<turnstile> $ \<cdot> PairV (FunV e) v \<leadsto> e \<cdot> v" by simp
    ultimately show ?case by (metis tev_step)
  next case 27
    thus ?case by (simp split: if_splits)
  next case (29 \<Lambda> n f x v)
    moreover then obtain F where "var\<^sub>t_bind \<Lambda> x = Some F \<and> 
      partial_evaluation \<Lambda> n (f \<cdot> \<lparr> f \<rparr>\<^bsub>x\<^esub> \<bullet> F \<cdot> \<prec>\<^bsub>x\<^esub>) v = Some v'" by (auto split: option.splits)
    moreover hence "\<Lambda> \<turnstile> \<lparr> f \<rparr>\<^bsub>x\<^esub> \<cdot> v \<leadsto> (f \<cdot> \<lparr> f \<rparr>\<^bsub>x\<^esub> \<bullet> F \<cdot> \<prec>\<^bsub>x\<^esub>) \<cdot> v" by simp
    ultimately show ?case by (metis tev_step)
  next case (31 \<Lambda> n f x v)
    moreover then obtain F where "var\<^sub>t_bind \<Lambda> x = Some F \<and> 
      partial_evaluation \<Lambda> n (\<succ>\<^bsub>x\<^esub> \<cdot> \<lbrakk> f \<rbrakk>\<^bsub>x\<^esub> \<bullet> F \<cdot> f) v = Some v'" by (auto split: option.splits)
    moreover hence "\<Lambda> \<turnstile> \<lbrakk> f \<rbrakk>\<^bsub>x\<^esub> \<cdot> v \<leadsto> (\<succ>\<^bsub>x\<^esub> \<cdot> \<lbrakk> f \<rbrakk>\<^bsub>x\<^esub> \<bullet> F \<cdot> f) \<cdot> v" by simp
    ultimately show ?case by (metis tev_step)
  next case (34 \<Lambda> n x v)
    moreover then obtain e where E: "var\<^sub>e_bind \<Lambda> x = Some e \<and> partial_evaluation \<Lambda> n e v = Some v'" 
      by (auto split: option.splits)
    ultimately have "\<Lambda> \<turnstile> e \<cdot> v \<Down> v'" by simp
    moreover from E have "\<Lambda> \<turnstile> Var x \<cdot> v \<leadsto> e \<cdot> v" by simp
    ultimately show ?case by (metis tev_step)
  qed auto

lemma pev_larger [elim]: "partial_evaluation \<Lambda> n e v = Some v' \<Longrightarrow> n \<le> m \<Longrightarrow> 
    partial_evaluation \<Lambda> m e v = Some v'"
  proof (induction \<Lambda> n e v arbitrary: v' m rule: partial_evaluation.induct)
  case (3 \<Lambda> n f g v)
    from 3(3) obtain v\<^sub>1 where V: "partial_evaluation \<Lambda> n g v = Some v\<^sub>1 \<and> 
      partial_evaluation \<Lambda> n f v\<^sub>1 = Some v'" by (auto split: option.splits)
    with 3 have "partial_evaluation \<Lambda> m g v = Some v\<^sub>1" by blast
    moreover from 3 V have "partial_evaluation \<Lambda> m f v\<^sub>1 = Some v'" by blast
    ultimately show ?case by simp
  next case (8 \<Lambda> n f\<^sub>1 f\<^sub>2 v\<^sub>1 v\<^sub>2)
    moreover from 8(3) obtain v\<^sub>1' v\<^sub>2' where V: "partial_evaluation \<Lambda> n f\<^sub>1 v\<^sub>1 = Some v\<^sub>1' \<and> 
      partial_evaluation \<Lambda> n f\<^sub>2 v\<^sub>2 = Some v\<^sub>2' \<and> v' = PairV v\<^sub>1' v\<^sub>2'" by (auto split: option.splits)
    ultimately show ?case by simp
  next case (16 \<Lambda> n f\<^sub>l f\<^sub>r v)
    moreover from 16(2) obtain v\<^sub>1 where "partial_evaluation \<Lambda> n f\<^sub>l v = Some v\<^sub>1 \<and> 
      partial_evaluation \<Lambda> n \<iota>\<^sub>l v\<^sub>1 = Some v'" by (auto split: option.splits)
    ultimately show ?case by simp
  next case (17 \<Lambda> n f\<^sub>l f\<^sub>r v)
    moreover from 17(2) obtain v\<^sub>1 where "partial_evaluation \<Lambda> n f\<^sub>r v = Some v\<^sub>1 \<and> 
      partial_evaluation \<Lambda> n \<iota>\<^sub>r v\<^sub>1 = Some v'" by (auto split: option.splits)
    ultimately show ?case by simp
  next case (22 \<Lambda> n e v)
    thus ?case
      proof (induction m)
      case (Suc m)
        moreover from Suc(3) have "partial_evaluation \<Lambda> n e v = Some v'" by simp
        ultimately have "partial_evaluation \<Lambda> m e v = Some v'" by blast
        thus ?case by simp
      qed simp_all
  next case (29 \<Lambda> n f x v)
    thus ?case
      proof (induction m)
      case (Suc m)
        moreover from Suc(3) obtain v\<^sub>1 v\<^sub>2 F where F: "var\<^sub>t_bind \<Lambda> x = Some F \<and> 
          partial_evaluation \<Lambda> n \<prec>\<^bsub>x\<^esub> v = Some v\<^sub>1 \<and> 
            partial_evaluation \<Lambda> n (\<lparr> f \<rparr>\<^bsub>x\<^esub> \<bullet> F) v\<^sub>1 = Some v\<^sub>2 \<and> 
              partial_evaluation \<Lambda> n f v\<^sub>2 = Some v'" by (auto split: option.splits)
        moreover hence "partial_evaluation \<Lambda> n (f \<cdot> \<lparr> f \<rparr>\<^bsub>x\<^esub> \<bullet> F \<cdot> \<prec>\<^bsub>x\<^esub>) v = Some v'" by simp
        ultimately have "partial_evaluation \<Lambda> m (f \<cdot> \<lparr> f \<rparr>\<^bsub>x\<^esub> \<bullet> F \<cdot> \<prec>\<^bsub>x\<^esub>) v = Some v'" by blast
        with F show ?case by simp
      qed simp_all
  next case (31 \<Lambda> n f x v)
    thus ?case
      proof (induction m)
      case (Suc m)
        moreover from Suc(3) obtain v\<^sub>1 v\<^sub>2 F where F: "var\<^sub>t_bind \<Lambda> x = Some F \<and> 
          partial_evaluation \<Lambda> n f v = Some v\<^sub>1 \<and>
            partial_evaluation \<Lambda> n (\<lbrakk> f \<rbrakk>\<^bsub>x\<^esub> \<bullet> F) v\<^sub>1 = Some v\<^sub>2 \<and> 
              partial_evaluation \<Lambda> n \<succ>\<^bsub>x\<^esub> v\<^sub>2 = Some v'" by (auto split: option.splits)
        moreover hence "partial_evaluation \<Lambda> n (\<succ>\<^bsub>x\<^esub> \<cdot> \<lbrakk> f \<rbrakk>\<^bsub>x\<^esub> \<bullet> F \<cdot> f) v = Some v'" by simp
        ultimately have "partial_evaluation \<Lambda> m (\<succ>\<^bsub>x\<^esub> \<cdot> \<lbrakk> f \<rbrakk>\<^bsub>x\<^esub> \<bullet> F \<cdot> f) v = Some v'" by blast
        with F show ?case by simp
      qed simp_all
  next case (34 \<Lambda> n x v)
    thus ?case
      proof (induction m)
      case (Suc m)
        from Suc(3) obtain e where "var\<^sub>e_bind \<Lambda> x = Some e \<and> partial_evaluation \<Lambda> n e v = Some v'" 
          by (auto split: option.splits)
        moreover with Suc have "partial_evaluation \<Lambda> m e v = Some v'" by blast
        ultimately show ?case by simp
      qed simp_all
  qed simp_all

lemma completeness': "\<Lambda> \<turnstile> e \<cdot> v \<Down> v' \<Longrightarrow> \<exists>n. partial_evaluation \<Lambda> n e v = Some v'"
  proof (induction \<Lambda> e v v' rule: total_eval.induct)
  case (tev_step \<Lambda> e v e' v' v'')
    thus ?case
      proof (induction \<Lambda> e v e' v' arbitrary: v'' rule: evaluate.induct)
      case (ev_comp1 \<Lambda> g v g' v' f)
        moreover then obtain n v\<^sub>1 where N: "partial_evaluation \<Lambda> n g' v' = Some v\<^sub>1 \<and> 
          partial_evaluation \<Lambda> n f v\<^sub>1 = Some v''" by (auto split: option.splits)
        moreover hence "\<Lambda> \<turnstile> g' \<cdot> v' \<Down> v\<^sub>1" by (metis soundness')
        ultimately obtain m where M: "partial_evaluation \<Lambda> m g v = Some v\<^sub>1" by auto
        have "max n m \<ge> m \<and> max n m \<ge> n" by simp
        with M N have "partial_evaluation \<Lambda> (max n m) f v\<^sub>1 = Some v'' \<and> 
          partial_evaluation \<Lambda> (max n m) g v = Some v\<^sub>1" by (metis pev_larger)
        hence "partial_evaluation \<Lambda> (max n m) (f \<cdot> g) v = Some v''" by simp
        thus ?case by fastforce
      next case (ev_pair1 \<Lambda> f\<^sub>1 v\<^sub>1 f\<^sub>1' v\<^sub>1' f\<^sub>2 v\<^sub>2)
        then obtain n v\<^sub>1'' v\<^sub>2' where N: "partial_evaluation \<Lambda> n f\<^sub>1' v\<^sub>1' = Some v\<^sub>1'' \<and> 
          partial_evaluation \<Lambda> n f\<^sub>2 v\<^sub>2 = Some v\<^sub>2' \<and> v'' = PairV v\<^sub>1'' v\<^sub>2'" 
            by (auto split: option.splits) fastforce
        with ev_pair1 have "\<Lambda> \<turnstile> f\<^sub>1' \<parallel> f\<^sub>2 \<cdot> PairV v\<^sub>1' v\<^sub>2 \<Down> PairV v\<^sub>1'' v\<^sub>2'" by simp
        hence "(\<Lambda> \<turnstile> f\<^sub>1' \<cdot> v\<^sub>1' \<Down> v\<^sub>1'') \<and> \<Lambda> \<turnstile> f\<^sub>2 \<cdot> v\<^sub>2 \<Down> v\<^sub>2'" by (metis pair_big_eval)
        with ev_pair1 N obtain m where M: "partial_evaluation \<Lambda> m f\<^sub>1 v\<^sub>1 = Some v\<^sub>1''" by auto
        have "max n m \<ge> m \<and> max n m \<ge> n" by simp
        with M N have "partial_evaluation \<Lambda> (max n m) f\<^sub>1 v\<^sub>1 = Some v\<^sub>1'' \<and> 
          partial_evaluation \<Lambda> (max n m) f\<^sub>2 v\<^sub>2 = Some v\<^sub>2'" by (metis pev_larger)
        with N have "partial_evaluation \<Lambda> (max n m) (f\<^sub>1 \<parallel> f\<^sub>2) (PairV v\<^sub>1 v\<^sub>2) = Some v''" by simp
        thus ?case by fastforce
      next case (ev_pair2 \<Lambda> f\<^sub>2 v\<^sub>2 f\<^sub>2' v\<^sub>2' v\<^sub>1)
        then obtain n v\<^sub>2'' where V: "partial_evaluation \<Lambda> n f\<^sub>2' v\<^sub>2' = Some v\<^sub>2'' \<and> v'' = PairV v\<^sub>1 v\<^sub>2''" 
          by (auto split: option.splits)
        with ev_pair2 have "\<Lambda> \<turnstile> \<epsilon> \<parallel> f\<^sub>2' \<cdot> PairV v\<^sub>1 v\<^sub>2' \<Down> PairV v\<^sub>1 v\<^sub>2''" by simp
        hence "\<Lambda> \<turnstile> f\<^sub>2' \<cdot> v\<^sub>2' \<Down> v\<^sub>2''" by (metis pair_big_eval)
        with ev_pair2 V obtain m where "partial_evaluation \<Lambda> m f\<^sub>2 v\<^sub>2 = Some v\<^sub>2''" by auto
        with V have "partial_evaluation \<Lambda> m (\<epsilon> \<parallel> f\<^sub>2) (PairV v\<^sub>1 v\<^sub>2) = Some v''" by simp
        thus ?case by fastforce
      next case (ev_app \<Lambda> e v)
        then obtain n where "partial_evaluation \<Lambda> n e v = Some v''" by blast
        hence "partial_evaluation \<Lambda> (Suc n) $ (PairV (FunV e) v) = Some v''" by simp
        thus ?case by fastforce
      next case ev_outj
        thus ?case by simp
      next case (ev_cata \<Lambda> x F f v)
        moreover then obtain n where "partial_evaluation \<Lambda> n (f \<cdot> \<lparr> f \<rparr>\<^bsub>x\<^esub> \<bullet> F \<cdot> \<prec>\<^bsub>x\<^esub>) v = Some v''" 
          by blast
        ultimately have "partial_evaluation \<Lambda> (Suc n) \<lparr> f \<rparr>\<^bsub>x\<^esub> v = Some v''" by simp
        thus ?case by fastforce
      next case (ev_ana \<Lambda> x F f v)
        moreover then obtain n where "partial_evaluation \<Lambda> n (\<succ>\<^bsub>x\<^esub> \<cdot> \<lbrakk> f \<rbrakk>\<^bsub>x\<^esub> \<bullet> F \<cdot> f) v = Some v''" 
          by blast
        ultimately have "partial_evaluation \<Lambda> (Suc n) \<lbrakk> f \<rbrakk>\<^bsub>x\<^esub> v = Some v''" by simp
        thus ?case by fastforce
      next case (ev_var \<Lambda> x e v)
        moreover then obtain n where "partial_evaluation \<Lambda> n e v = Some v''" by blast
        ultimately have "partial_evaluation \<Lambda> (Suc n) (Var x) v = Some v''" by simp
        thus ?case by fastforce
      qed auto 
  qed simp_all

theorem soundness: "partial_eval_prog n \<Pi> = Some v \<Longrightarrow> \<Pi> \<Down> v"
  by (induction \<Pi>) (simp add: soundness')

theorem completeness: "\<Pi> \<Down> v \<Longrightarrow> \<exists>n. partial_eval_prog n \<Pi> = Some v"
  by (simp, induction \<Pi> v rule: total_evaluate_prog'.induct) (simp add: completeness')

end
theory PartialEvaluation
imports BananasLanguage
begin

fun exemplary_evaluation :: "nat \<Rightarrow> expr \<times> val \<Rightarrow> val option" where
  "exemplary_evaluation 0 _ = None"
| "exemplary_evaluation n (\<epsilon>, v) = Some v"
| "exemplary_evaluation n (\<kappa> v\<^sub>1, v\<^sub>2) = Some v\<^sub>1"
| "exemplary_evaluation n (f \<cdot> g, v) = (case exemplary_evaluation n (g, v) of 
      Some v' \<Rightarrow> exemplary_evaluation n (f, v')
    | None \<Rightarrow> None)"
| "exemplary_evaluation n (\<pi>\<^sub>1, PairV v\<^sub>1 v\<^sub>2) = Some v\<^sub>1"
| "exemplary_evaluation n (\<pi>\<^sub>1, _) = None"
| "exemplary_evaluation n (\<pi>\<^sub>2, PairV v\<^sub>1 v\<^sub>2) = Some v\<^sub>2"
| "exemplary_evaluation n (\<pi>\<^sub>2, _) = None"
| "exemplary_evaluation n (f\<^sub>1 \<parallel> f\<^sub>2, PairV v\<^sub>1 v\<^sub>2) = (case exemplary_evaluation n (f\<^sub>1, v\<^sub>1) of 
      Some v\<^sub>1' \<Rightarrow> (case exemplary_evaluation n (f\<^sub>2, v\<^sub>2) of 
          Some v\<^sub>2' \<Rightarrow> Some (PairV v\<^sub>1' v\<^sub>2')
        | None \<Rightarrow> None)
    | None \<Rightarrow> None)"
| "exemplary_evaluation n (f\<^sub>1 \<parallel> f\<^sub>2, _) = None"
| "exemplary_evaluation n (\<Theta>, v) = Some (PairV v v)"
| "exemplary_evaluation n (\<iota>\<^sub>l, v) = Some (InlV v)"
| "exemplary_evaluation n (\<iota>\<^sub>r, v) = Some (InrV v)"
| "exemplary_evaluation n (\<Xi>, InlV v) = Some v"
| "exemplary_evaluation n (\<Xi>, InrV v) = Some v"
| "exemplary_evaluation n (\<Xi>, _) = None"
| "exemplary_evaluation n (f\<^sub>l \<bar> f\<^sub>r, InlV v) = exemplary_evaluation n (\<iota>\<^sub>l \<cdot> f\<^sub>l, v)"
| "exemplary_evaluation n (f\<^sub>l \<bar> f\<^sub>r, InrV v) = exemplary_evaluation n (\<iota>\<^sub>r \<cdot> f\<^sub>r, v)"
| "exemplary_evaluation n (f\<^sub>l \<bar> f\<^sub>r, _) = None"
| "exemplary_evaluation n (\<rhd>, PairV (InlV v\<^sub>1) v\<^sub>2) = Some (InlV (PairV v\<^sub>1 v\<^sub>2))"
| "exemplary_evaluation n (\<rhd>, PairV (InrV v\<^sub>1) v\<^sub>2) = Some (InrV (PairV v\<^sub>1 v\<^sub>2))"
| "exemplary_evaluation n (\<rhd>, _) = None"
| "exemplary_evaluation (Suc n) ($, PairV (FunV e) v) = exemplary_evaluation n (e, v)"
| "exemplary_evaluation n ($, _) = None"
| "exemplary_evaluation n (g \<leftarrow> f, FunV e) = Some (FunV (g \<cdot> e \<cdot> f))"
| "exemplary_evaluation n (g \<leftarrow> f, _) = None"
| "exemplary_evaluation n (\<succ>\<^bsub>F\<^esub>, v) = Some (InjV F v)"
| "exemplary_evaluation n (\<prec>\<^bsub>F\<^esub>, InjV _ v) = Some v"
| "exemplary_evaluation n (\<prec>\<^bsub>F\<^esub>, _) = None"
| "exemplary_evaluation (Suc n) (\<lparr> f \<rparr>\<^bsub>F\<^esub>, v) = exemplary_evaluation n (f \<cdot> \<lparr> f \<rparr>\<^bsub>F\<^esub> \<bullet> F \<cdot> \<prec>\<^bsub>F\<^esub>, v)"
| "exemplary_evaluation (Suc n) (\<lbrakk> f \<rbrakk>\<^bsub>F\<^esub>, v) = exemplary_evaluation n (\<succ>\<^bsub>F\<^esub> \<cdot> \<lbrakk> f \<rbrakk>\<^bsub>F\<^esub> \<bullet> F \<cdot> f, v)"

abbreviation long_run :: nat where
  "long_run \<equiv> Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))"

end
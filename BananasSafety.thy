theory BananasSafety
imports BananasDynamics
begin

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

theorem progress [simp]: "\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> v : t\<^sub>1 \<Longrightarrow> \<Gamma> \<tturnstile> \<Lambda> \<Longrightarrow> e \<noteq> \<epsilon> \<Longrightarrow> 
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
      using typecheck_environment_def by fastforce
    hence "\<Lambda> \<turnstile> Var x \<cdot> v \<leadsto> e \<cdot> v" by simp
    thus ?case by fastforce
  qed simp_all

lemma [simp]: "\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> e \<bullet> F : t\<^sub>1 \<star> F \<rightarrow> t\<^sub>2 \<star> F"
  by (induction e F rule: apply_functor_expr.induct) simp_all

theorem preservation [simp]: "\<Lambda> \<turnstile> e \<cdot> v \<leadsto> e' \<cdot> v' \<Longrightarrow> \<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> 
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
      using typecheck_environment_def by fastforce 
    with ev_var show ?case by fastforce
  qed fastforce+

(* big-step evaluation *) 

inductive total_eval :: "dynamic_environment \<Rightarrow> expr \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool" 
    (infix "\<turnstile> _ \<cdot> _ \<Down>" 60) where
  tev_base [simp]: "\<Lambda> \<turnstile> \<epsilon> \<cdot> v \<Down> v"
| tev_step [simp]: "\<Lambda> \<turnstile> e \<cdot> v \<leadsto> e' \<cdot> v' \<Longrightarrow> \<Lambda> \<turnstile> e' \<cdot> v' \<Down> v'' \<Longrightarrow> \<Lambda> \<turnstile> e \<cdot> v \<Down> v''"

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

(* since we are a turing-complete language, total progress is not provable *)

theorem total_preservation [simp]: "\<Lambda> \<turnstile> e \<cdot> v \<Down> v' \<Longrightarrow> \<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> 
    \<Gamma> \<turnstile> v : t\<^sub>1 \<Longrightarrow> \<Gamma> \<tturnstile> \<Lambda> \<Longrightarrow> \<Gamma> \<turnstile> v' : t\<^sub>2"
  proof (induction \<Lambda> e v v' arbitrary: t\<^sub>1 rule: total_eval.induct)
  case (tev_step \<Lambda> e v e' v' v'')
    moreover then obtain t\<^sub>3 where "(\<Gamma> \<turnstile> e' : t\<^sub>3 \<rightarrow> t\<^sub>2) \<and> (\<Gamma> \<turnstile> v' : t\<^sub>3)" 
      by (metis preservation)
    ultimately show ?case by fastforce
  qed auto

(* environment lemmas *)



lemma [simp]: "\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> x \<notin> dom (var\<^sub>e_type \<Gamma>) \<Longrightarrow> 
    \<Gamma>\<lparr>var\<^sub>e_type := var\<^sub>e_type \<Gamma>(x \<mapsto> (tt\<^sub>1, tt\<^sub>2))\<rparr> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2"
  and [simp]: "\<Gamma> \<turnstile> v : t \<Longrightarrow> x \<notin> dom (var\<^sub>e_type \<Gamma>) \<Longrightarrow> 
    \<Gamma>\<lparr>var\<^sub>e_type := var\<^sub>e_type \<Gamma>(x \<mapsto> (tt\<^sub>1, tt\<^sub>2))\<rparr> \<turnstile> v : t"
  proof (induction \<Gamma> e t\<^sub>1 t\<^sub>2 and \<Gamma> v t rule: typecheck\<^sub>e_typecheck\<^sub>v.inducts) 
  case (tc_var \<Gamma> y t\<^sub>1 t\<^sub>2)
    hence "(var\<^sub>e_type \<Gamma>(x \<mapsto> (tt\<^sub>1, tt\<^sub>2))) y = Some (t\<^sub>1, t\<^sub>2)" by auto
    hence "\<Gamma>\<lparr>var\<^sub>e_type := var\<^sub>e_type \<Gamma>(x \<mapsto> (tt\<^sub>1, tt\<^sub>2))\<rparr> \<turnstile> Var y : t\<^sub>1 \<rightarrow> t\<^sub>2" by simp
    thus ?case by blast
  qed simp_all

lemma [simp]: "\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> x \<notin> dom (var\<^sub>v_type \<Gamma>) \<Longrightarrow> 
    \<Gamma>\<lparr>var\<^sub>v_type := var\<^sub>v_type \<Gamma>(x \<mapsto> tt)\<rparr> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2"
  and [simp]: "\<Gamma> \<turnstile> v : t \<Longrightarrow> x \<notin> dom (var\<^sub>v_type \<Gamma>) \<Longrightarrow> \<Gamma>\<lparr>var\<^sub>v_type := var\<^sub>v_type \<Gamma>(x \<mapsto> tt)\<rparr> \<turnstile> v : t"
  by (induction \<Gamma> e t\<^sub>1 t\<^sub>2 and \<Gamma> v t rule: typecheck\<^sub>e_typecheck\<^sub>v.inducts) simp_all

(*

lemma [simp]: "\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> domain\<^sub>s \<Gamma> \<inter> domain\<^sub>s \<Gamma>' = {} \<Longrightarrow> combine\<^sub>s \<Gamma> \<Gamma>' \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2"
  and [simp]: "\<Gamma> \<turnstile> v : t \<Longrightarrow> domain\<^sub>s \<Gamma> \<inter> domain\<^sub>s \<Gamma>' = {} \<Longrightarrow> combine\<^sub>s \<Gamma> \<Gamma>' \<turnstile> v : t"
  by (induction \<Gamma> e t\<^sub>1 t\<^sub>2 and \<Gamma> v t rule: typecheck\<^sub>e_typecheck\<^sub>v.inducts) simp_all

lemma [simp]: "\<And>xa t\<^sub>1' t\<^sub>2'.
       \<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow>
       var\<^sub>t_type \<Gamma> = var\<^sub>t_bind \<Lambda> \<Longrightarrow>
       dom (var\<^sub>e_type \<Gamma>) = dom (var\<^sub>e_bind \<Lambda>) \<Longrightarrow>
       var\<^sub>e_bind \<Lambda> x = None \<Longrightarrow>
       var\<^sub>v_type \<Gamma> x = None \<Longrightarrow>
       \<forall>x t\<^sub>1 t\<^sub>2. var\<^sub>e_type \<Gamma> x = Some (t\<^sub>1, t\<^sub>2) \<longrightarrow> (\<exists>e. var\<^sub>e_bind \<Lambda> x = Some e \<and> \<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2) \<Longrightarrow>
       \<forall>x t. var\<^sub>v_type \<Gamma> x = Some t \<longrightarrow> (\<exists>v. var\<^sub>v_bind \<Lambda> x = Some v \<and> \<Gamma> \<turnstile> v : t) \<Longrightarrow>
       var\<^sub>t_bind \<Lambda> x = None \<Longrightarrow>
       xa \<noteq> x \<Longrightarrow>
       var\<^sub>e_type \<Gamma> xa = Some (t\<^sub>1', t\<^sub>2') \<Longrightarrow>
       \<exists>e. var\<^sub>e_bind \<Lambda> xa = Some e \<and> \<Gamma>\<lparr>var\<^sub>e_type := var\<^sub>e_type \<Gamma>(x \<mapsto> (t\<^sub>1, t\<^sub>2))\<rparr> \<turnstile> e : t\<^sub>1' \<rightarrow> t\<^sub>2'"
  by simp

lemma [simp]: "\<And>xa t. \<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow>
            var\<^sub>t_type \<Gamma> = var\<^sub>t_bind \<Lambda> \<Longrightarrow>
            dom (var\<^sub>e_type \<Gamma>) = dom (var\<^sub>e_bind \<Lambda>) \<Longrightarrow>
            var\<^sub>e_bind \<Lambda> x = None \<Longrightarrow>
            var\<^sub>v_type \<Gamma> x = None \<Longrightarrow>
            \<forall>x t\<^sub>1 t\<^sub>2. var\<^sub>e_type \<Gamma> x = Some (t\<^sub>1, t\<^sub>2) \<longrightarrow> (\<exists>e. var\<^sub>e_bind \<Lambda> x = Some e \<and> \<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2) \<Longrightarrow>
            \<forall>x t. var\<^sub>v_type \<Gamma> x = Some t \<longrightarrow> (\<exists>v. var\<^sub>v_bind \<Lambda> x = Some v \<and> \<Gamma> \<turnstile> v : t) \<Longrightarrow>
            var\<^sub>t_bind \<Lambda> x = None \<Longrightarrow>
            var\<^sub>v_type \<Gamma> xa = Some t \<Longrightarrow> \<exists>v. var\<^sub>v_bind \<Lambda> xa = Some v \<and> \<Gamma>\<lparr>var\<^sub>e_type := var\<^sub>e_type \<Gamma>(x \<mapsto> (t\<^sub>1, t\<^sub>2))\<rparr> \<turnstile> v : t"
  by simp

lemma [simp]: "\<And>xa t\<^sub>1 t\<^sub>2.
       \<Gamma> \<turnstile> v : t \<Longrightarrow>
       var\<^sub>t_type \<Gamma> = var\<^sub>t_bind \<Lambda> \<Longrightarrow>
       dom (var\<^sub>e_type \<Gamma>) = dom (var\<^sub>e_bind \<Lambda>) \<Longrightarrow>
       var\<^sub>e_bind \<Lambda> x = None \<Longrightarrow>
       var\<^sub>v_type \<Gamma> x = None \<Longrightarrow>
       \<forall>x t\<^sub>1 t\<^sub>2. var\<^sub>e_type \<Gamma> x = Some (t\<^sub>1, t\<^sub>2) \<longrightarrow> (\<exists>e. var\<^sub>e_bind \<Lambda> x = Some e \<and> \<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2) \<Longrightarrow>
       \<forall>x t. var\<^sub>v_type \<Gamma> x = Some t \<longrightarrow> (\<exists>v. var\<^sub>v_bind \<Lambda> x = Some v \<and> \<Gamma> \<turnstile> v : t) \<Longrightarrow>
       var\<^sub>t_bind \<Lambda> x = None \<Longrightarrow>
       var\<^sub>e_type \<Gamma> xa = Some (t\<^sub>1, t\<^sub>2) \<Longrightarrow> \<exists>e. var\<^sub>e_bind \<Lambda> xa = Some e \<and> \<Gamma>\<lparr>var\<^sub>v_type := var\<^sub>v_type \<Gamma>(x \<mapsto> t)\<rparr> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2"
  by simp

lemma [simp]: "\<And>xa ta. \<Gamma> \<turnstile> v : t \<Longrightarrow>
             var\<^sub>t_type \<Gamma> = var\<^sub>t_bind \<Lambda> \<Longrightarrow>
             dom (var\<^sub>e_type \<Gamma>) = dom (var\<^sub>e_bind \<Lambda>) \<Longrightarrow>
             var\<^sub>e_bind \<Lambda> x = None \<Longrightarrow>
             var\<^sub>v_type \<Gamma> x = None \<Longrightarrow>
             \<forall>x t\<^sub>1 t\<^sub>2. var\<^sub>e_type \<Gamma> x = Some (t\<^sub>1, t\<^sub>2) \<longrightarrow> (\<exists>e. var\<^sub>e_bind \<Lambda> x = Some e \<and> \<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2) \<Longrightarrow>
             \<forall>x t. var\<^sub>v_type \<Gamma> x = Some t \<longrightarrow> (\<exists>v. var\<^sub>v_bind \<Lambda> x = Some v \<and> \<Gamma> \<turnstile> v : t) \<Longrightarrow>
             var\<^sub>t_bind \<Lambda> x = None \<Longrightarrow>
             xa \<noteq> x \<Longrightarrow> var\<^sub>v_type \<Gamma> xa = Some ta \<Longrightarrow> \<exists>v. var\<^sub>v_bind \<Lambda> xa = Some v \<and> \<Gamma>\<lparr>var\<^sub>v_type := var\<^sub>v_type \<Gamma>(x \<mapsto> t)\<rparr> \<turnstile> v : ta"
  by simp *)

lemma [simp]: "\<Gamma> \<turnstile> e : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<tturnstile> \<Lambda> \<Longrightarrow> x \<notin> domain\<^sub>s \<Gamma> \<Longrightarrow> 
    extend\<^sub>e\<^sub>s x (t\<^sub>1, t\<^sub>2) \<Gamma> \<tturnstile> extend\<^sub>e\<^sub>d x e \<Lambda>"
  by (auto simp add: typecheck_environment_def extend\<^sub>e\<^sub>s_def extend\<^sub>e\<^sub>d_def domain\<^sub>s_def)

lemma [simp]: "\<Gamma> \<turnstile> v : t \<Longrightarrow> \<Gamma> \<tturnstile> \<Lambda> \<Longrightarrow> x \<notin> domain\<^sub>s \<Gamma> \<Longrightarrow> extend\<^sub>v\<^sub>s x t \<Gamma> \<tturnstile> extend\<^sub>v\<^sub>d x v \<Lambda>"
  by (auto simp add: typecheck_environment_def extend\<^sub>v\<^sub>s_def extend\<^sub>v\<^sub>d_def domain\<^sub>s_def)

lemma typecheck_combine [simp]: "\<Gamma> \<tturnstile> \<Lambda> \<Longrightarrow> \<Gamma>' \<tturnstile> \<Lambda>' \<Longrightarrow> domain\<^sub>s \<Gamma> \<inter> domain\<^sub>s \<Gamma>' = {} \<Longrightarrow> 
    combine\<^sub>s \<Gamma> \<Gamma>' \<tturnstile> combine\<^sub>d \<Lambda> \<Lambda>'"
  by (auto simp add: typecheck_environment_def combine\<^sub>s_def combine\<^sub>d_def domain\<^sub>s_def)

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

lemma [simp]: "typecheck\<^sub>c\<^sub>e \<Gamma> F cts x = Some (t\<^sub>1, t\<^sub>2) \<Longrightarrow> \<exists>e. assemble_context\<^sub>c\<^sub>e n d cts x = Some e"
  by (induction F cts x arbitrary: d rule: typecheck\<^sub>c\<^sub>e.induct) auto

lemma [simp]: "assemble_context\<^sub>c\<^sub>e n d cts x = Some e \<Longrightarrow> \<exists>t\<^sub>1 t\<^sub>2. typecheck\<^sub>c\<^sub>e \<Gamma> F cts x = Some (t\<^sub>1, t\<^sub>2)"
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
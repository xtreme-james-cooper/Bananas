theory DerivedCombinators
imports BananasLanguage
begin

definition Bool :: type where
  "Bool = Unit \<oplus> Unit"

definition TrueV :: val where
  "TrueV = InlV UnitV"

definition FalseV :: val where
  "FalseV = InrV UnitV"

lemma [simp]: "TrueV \<turnstile> Bool"
  by (simp add: TrueV_def Bool_def)

lemma [simp]: "FalseV \<turnstile> Bool"
  by (simp add: FalseV_def Bool_def)

definition tuple_pair :: "expr \<Rightarrow> expr \<Rightarrow> expr" (infix "\<triangle>" 80) where
  "e\<^sub>1 \<triangle> e\<^sub>2 = e\<^sub>1 \<parallel> e\<^sub>2 \<cdot> \<Theta>"

definition case_strip :: "expr \<Rightarrow> expr \<Rightarrow> expr" (infix "\<nabla>" 80) where
  "e\<^sub>l \<nabla> e\<^sub>r = \<Xi> \<cdot> e\<^sub>l \<bar> e\<^sub>r"

definition predicate :: "expr \<Rightarrow> expr" ("?") where
  "? p = \<pi>\<^sub>2 \<bar> \<pi>\<^sub>2 \<cdot> \<rhd> \<cdot> p \<parallel> \<epsilon> \<cdot> \<Theta>"

definition swap :: expr ("\<bowtie>") where
  "\<bowtie> = \<pi>\<^sub>2 \<triangle> \<pi>\<^sub>1"

definition distribute_right :: expr ("\<lhd>") where
  "\<lhd> = \<bowtie> \<cdot> \<rhd> \<cdot> \<bowtie>"

lemma tc_tup_pair [simp]: "f\<^sub>1 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> f\<^sub>2 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>3 \<Longrightarrow> f\<^sub>1 \<triangle> f\<^sub>2 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<otimes> t\<^sub>3"
  proof (unfold tuple_pair_def)
    assume "f\<^sub>1 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2"
       and "f\<^sub>2 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>3"
    hence "f\<^sub>1 \<parallel> f\<^sub>2 \<turnstile> t\<^sub>1 \<otimes> t\<^sub>1 \<rightarrow> t\<^sub>2 \<otimes> t\<^sub>3" by simp
    thus "f\<^sub>1 \<parallel> f\<^sub>2 \<cdot> \<Theta> \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<otimes> t\<^sub>3" by simp
  qed

lemma tc_cse_str [simp]: "f\<^sub>l \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>3 \<Longrightarrow> f\<^sub>r \<turnstile> t\<^sub>2 \<rightarrow> t\<^sub>3 \<Longrightarrow> f\<^sub>l \<nabla> f\<^sub>r \<turnstile> t\<^sub>1 \<oplus> t\<^sub>2 \<rightarrow> t\<^sub>3"
  proof (unfold case_strip_def)
    assume "f\<^sub>l \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>3"
       and "f\<^sub>r \<turnstile> t\<^sub>2 \<rightarrow> t\<^sub>3"
    hence "f\<^sub>l \<bar> f\<^sub>r \<turnstile> t\<^sub>1 \<oplus> t\<^sub>2 \<rightarrow> t\<^sub>3 \<oplus> t\<^sub>3" by simp
    moreover have "\<Xi> \<turnstile> t\<^sub>3 \<oplus> t\<^sub>3 \<rightarrow> t\<^sub>3" by simp
    ultimately show "\<Xi> \<cdot> f\<^sub>l \<bar> f\<^sub>r \<turnstile> t\<^sub>1 \<oplus> t\<^sub>2 \<rightarrow> t\<^sub>3" by (metis tc_comp)
  qed

lemma tc_pred [simp]: "p \<turnstile> t \<rightarrow> Bool \<Longrightarrow> ? p \<turnstile> t \<rightarrow> t \<oplus> t"
  proof (unfold predicate_def)
    assume "p \<turnstile> t \<rightarrow> Bool"
    thus "\<pi>\<^sub>2 \<bar> \<pi>\<^sub>2 \<cdot> \<rhd> \<cdot> p \<parallel> \<epsilon> \<cdot> \<Theta> \<turnstile> t \<rightarrow> t \<oplus> t" by simp
  qed

lemma tc_swap [simp]: "\<bowtie> \<turnstile> t\<^sub>1 \<otimes> t\<^sub>2 \<rightarrow> t\<^sub>2 \<otimes> t\<^sub>1"
  proof (unfold swap_def)
    show "\<pi>\<^sub>2 \<triangle> \<pi>\<^sub>1 \<turnstile> t\<^sub>1 \<otimes> t\<^sub>2 \<rightarrow> t\<^sub>2 \<otimes> t\<^sub>1" by simp
  qed

lemma tc_distr [simp]: "\<lhd> \<turnstile> t\<^sub>3 \<otimes> (t\<^sub>1 \<oplus> t\<^sub>2) \<rightarrow> t\<^sub>3 \<otimes> t\<^sub>1 \<oplus> t\<^sub>3 \<otimes> t\<^sub>2"
  proof (unfold distribute_right_def)
    show "\<bowtie> \<cdot> \<rhd> \<cdot> \<bowtie> \<turnstile> t\<^sub>3 \<otimes> (t\<^sub>1 \<oplus> t\<^sub>2) \<rightarrow> t\<^sub>3 \<otimes> t\<^sub>1 \<oplus> t\<^sub>3 \<otimes> t\<^sub>2" by simp
  qed

lemma ev_tup_pair [simp]: "f\<^sub>1 \<cdot> v \<Down> v\<^sub>1 \<Longrightarrow> f\<^sub>2 \<cdot> v \<Down> v\<^sub>2 \<Longrightarrow> f\<^sub>1 \<triangle> f\<^sub>2 \<cdot> v \<Down> PairV v\<^sub>1 v\<^sub>2"
  proof (unfold tuple_pair_def)
    assume "f\<^sub>1 \<cdot> v \<Down> v\<^sub>1"
       and "f\<^sub>2 \<cdot> v \<Down> v\<^sub>2"
    moreover have "\<Theta> \<cdot> v \<Down> PairV v v" by simp
    ultimately show "(f\<^sub>1 \<parallel> f\<^sub>2 \<cdot> \<Theta>) \<cdot> v \<Down> PairV v\<^sub>1 v\<^sub>2" by fastforce
  qed

lemma ev_cse_str_l [simp]: "f\<^sub>l \<cdot> v \<Down> v' \<Longrightarrow> f\<^sub>l \<nabla> f\<^sub>r \<cdot> InlV v \<Down> v'"
  proof (unfold case_strip_def)
    assume "f\<^sub>l \<cdot> v \<Down> v'"
    hence "f\<^sub>l \<bar> f\<^sub>r \<cdot> InlV v \<Down> InlV v'" by simp
    thus "(\<Xi> \<cdot> f\<^sub>l \<bar> f\<^sub>r) \<cdot> InlV v \<Down> v'" by fastforce
  qed

lemma ev_cse_str_r [simp]: "f\<^sub>r \<cdot> v \<Down> v' \<Longrightarrow> f\<^sub>l \<nabla> f\<^sub>r \<cdot> InrV v \<Down> v'"
  proof (unfold case_strip_def)
    assume "f\<^sub>r \<cdot> v \<Down> v'"
    hence "f\<^sub>l \<bar> f\<^sub>r \<cdot> InrV v \<Down> InrV v'" by simp
    thus "(\<Xi> \<cdot> f\<^sub>l \<bar> f\<^sub>r) \<cdot> InrV v \<Down> v'" by fastforce
  qed

lemma ev_pred_t [simp]: "p \<cdot> v \<Down> TrueV \<Longrightarrow> ? p \<cdot> v \<Down> InlV v"
  proof (unfold predicate_def)
    assume "p \<cdot> v \<Down> TrueV"
    show "\<pi>\<^sub>2 \<bar> \<pi>\<^sub>2 \<cdot> \<rhd> \<cdot> p \<parallel> \<epsilon> \<cdot> \<Theta> \<cdot> v \<Down> InlV v" by simp
  qed

lemma ev_pred_f [simp]: "p \<cdot> v \<Down> FalseV \<Longrightarrow> ? p \<cdot> v \<Down> InrV v"
  proof (unfold predicate_def)
    assume "p \<cdot> v \<Down> FalseV"
    show "\<pi>\<^sub>2 \<bar> \<pi>\<^sub>2 \<cdot> \<rhd> \<cdot> p \<parallel> \<epsilon> \<cdot> \<Theta> \<cdot> v \<Down> InrV v" by simp
  qed

lemma ev_swap [simp]: "\<bowtie> \<cdot> PairV v\<^sub>1 v\<^sub>2 \<Down> PairV v\<^sub>2 v\<^sub>1"
  proof (unfold swap_def)
    show "\<pi>\<^sub>2 \<triangle> \<pi>\<^sub>1 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<Down> PairV v\<^sub>2 v\<^sub>1" by simp
  qed

lemma ev_dstrl [simp]: "\<lhd> \<cdot> PairV v\<^sub>1 (InlV v\<^sub>2) \<Down> InlV (PairV v\<^sub>1 v\<^sub>2)"
  proof (unfold distribute_right_def)
    show "\<bowtie> \<cdot> \<rhd> \<cdot> \<bowtie> \<cdot> PairV v\<^sub>1 (InlV v\<^sub>2) \<Down> InlV (PairV v\<^sub>1 v\<^sub>2)" by simp
  qed

lemma ev_dstrr [simp]: "\<lhd> \<cdot> PairV v\<^sub>1 (InrV v\<^sub>2) \<Down> InrV (PairV v\<^sub>1 v\<^sub>2)"
  proof (unfold distribute_right_def)
    show "\<bowtie> \<cdot> \<rhd> \<cdot> \<bowtie> \<cdot> PairV v\<^sub>1 (InrV v\<^sub>2) \<Down> InrV (PairV v\<^sub>1 v\<^sub>2)" by simp
  qed

end
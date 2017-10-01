theory DerivedCombinators
imports BananasLanguage
begin

(* derived types *)

definition Bool :: type where
  "Bool = \<one> \<oplus> \<one>"

definition TrueV :: val where
  "TrueV = InlV UnitV"

definition FalseV :: val where
  "FalseV = InrV UnitV"

definition Nat :: type where
  "Nat = \<mu> (K \<one> \<Oplus> Id)"

definition ZeroV :: val where
  "ZeroV = InjV (K \<one> \<Oplus> Id) (InlV UnitV)"

definition SuccV :: "val \<Rightarrow> val" where
  "SuccV v = InjV (K \<one> \<Oplus> Id) (InrV v)"

definition List :: "type \<Rightarrow> type" where
  "List t = \<mu> (K \<one> \<Oplus> K t \<Otimes> Id)"

definition NilV :: "type \<Rightarrow> val" where
  "NilV t = InjV (K \<one> \<Oplus> K t \<Otimes> Id) (InlV UnitV)"

definition ConsV :: "type \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val" where
  "ConsV t v\<^sub>1 v\<^sub>2 = InjV (K \<one> \<Oplus> K t \<Otimes> Id) (InrV (PairV v\<^sub>1 v\<^sub>2))"

lemma [simp]: "TrueV \<turnstile> Bool"
  by (simp add: TrueV_def Bool_def)

lemma [simp]: "FalseV \<turnstile> Bool"
  by (simp add: FalseV_def Bool_def)

lemma [simp]: "ZeroV \<turnstile> Nat"
  by (simp add: ZeroV_def Nat_def)

lemma [simp]: "n \<turnstile> Nat \<Longrightarrow> SuccV n \<turnstile> Nat"
  by (simp add: SuccV_def Nat_def)

lemma [simp]: "NilV t \<turnstile> List t"
  by (simp add: NilV_def List_def)

lemma [simp]: "v\<^sub>1 \<turnstile> t \<Longrightarrow> v\<^sub>2 \<turnstile> List t \<Longrightarrow> ConsV t v\<^sub>1 v\<^sub>2 \<turnstile> List t"
  by (simp add: ConsV_def List_def)

(* derived combinators *)

definition tuple_pair :: "expr \<Rightarrow> expr \<Rightarrow> expr" (infix "\<triangle>" 80) where
  "e\<^sub>1 \<triangle> e\<^sub>2 = e\<^sub>1 \<parallel> e\<^sub>2 \<cdot> \<Theta>"

definition case_strip :: "expr \<Rightarrow> expr \<Rightarrow> expr" (infix "\<nabla>" 80) where
  "e\<^sub>l \<nabla> e\<^sub>r = \<Xi> \<cdot> e\<^sub>l \<bar> e\<^sub>r"

definition predicate :: "expr \<Rightarrow> expr" ("?") where
  "? p = \<pi>\<^sub>2 \<bar> \<pi>\<^sub>2 \<cdot> \<rhd> \<cdot> p \<parallel> \<epsilon> \<cdot> \<Theta>"

definition swap :: expr ("\<bowtie>") where
  "\<bowtie> = \<pi>\<^sub>2 \<triangle> \<pi>\<^sub>1"

definition distribute_right :: expr ("\<lhd>") where
  "\<lhd> = \<bowtie> \<bar> \<bowtie> \<cdot> \<rhd> \<cdot> \<bowtie>"

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
    hence "p \<parallel> \<epsilon> \<turnstile> t \<otimes> t \<rightarrow> Bool \<otimes> t" by simp
    moreover have "\<rhd> \<turnstile> Bool \<otimes> t \<rightarrow> \<one> \<otimes> t \<oplus> \<one> \<otimes> t" by (simp add: Bool_def)
    ultimately have "\<rhd> \<cdot> p \<parallel> \<epsilon> \<cdot> \<Theta> \<turnstile> t \<rightarrow> \<one> \<otimes> t \<oplus> \<one> \<otimes> t" by simp
    moreover have "\<pi>\<^sub>2 \<bar> \<pi>\<^sub>2 \<turnstile> \<one> \<otimes> t \<oplus> \<one> \<otimes> t \<rightarrow> t \<oplus> t" by simp
    ultimately show "\<pi>\<^sub>2 \<bar> \<pi>\<^sub>2 \<cdot> \<rhd> \<cdot> p \<parallel> \<epsilon> \<cdot> \<Theta> \<turnstile> t \<rightarrow> t \<oplus> t" by (metis tc_comp)
  qed

lemma tc_swap [simp]: "\<bowtie> \<turnstile> t\<^sub>1 \<otimes> t\<^sub>2 \<rightarrow> t\<^sub>2 \<otimes> t\<^sub>1"
  by (simp add: swap_def)

lemma tc_distr [simp]: "\<lhd> \<turnstile> t\<^sub>3 \<otimes> (t\<^sub>1 \<oplus> t\<^sub>2) \<rightarrow> t\<^sub>3 \<otimes> t\<^sub>1 \<oplus> t\<^sub>3 \<otimes> t\<^sub>2"
  proof (unfold distribute_right_def)
    have "\<rhd> \<turnstile> (t\<^sub>1 \<oplus> t\<^sub>2) \<otimes> t\<^sub>3 \<rightarrow> t\<^sub>1 \<otimes> t\<^sub>3 \<oplus> t\<^sub>2 \<otimes> t\<^sub>3" by simp
    moreover have "\<bowtie> \<turnstile> t\<^sub>3 \<otimes> (t\<^sub>1 \<oplus> t\<^sub>2) \<rightarrow> (t\<^sub>1 \<oplus> t\<^sub>2) \<otimes> t\<^sub>3" by simp
    ultimately have "\<rhd> \<cdot> \<bowtie> \<turnstile> t\<^sub>3 \<otimes> (t\<^sub>1 \<oplus> t\<^sub>2) \<rightarrow> t\<^sub>1 \<otimes> t\<^sub>3 \<oplus> t\<^sub>2 \<otimes> t\<^sub>3" by (metis tc_comp)
    moreover have "\<bowtie> \<bar> \<bowtie> \<turnstile> t\<^sub>1 \<otimes> t\<^sub>3 \<oplus> t\<^sub>2 \<otimes> t\<^sub>3 \<rightarrow> t\<^sub>3 \<otimes> t\<^sub>1 \<oplus> t\<^sub>3 \<otimes> t\<^sub>2" by simp
    ultimately show "\<bowtie> \<bar> \<bowtie> \<cdot> \<rhd> \<cdot> \<bowtie> \<turnstile> t\<^sub>3 \<otimes> (t\<^sub>1 \<oplus> t\<^sub>2) \<rightarrow> t\<^sub>3 \<otimes> t\<^sub>1 \<oplus> t\<^sub>3 \<otimes> t\<^sub>2" by (metis tc_comp)
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
    have "\<Theta> \<cdot> v \<Down> PairV v v" by simp
    moreover assume "p \<cdot> v \<Down> TrueV"
    moreover hence "(p \<parallel> \<epsilon>) \<cdot> PairV v v \<Down> PairV TrueV v" by simp
    ultimately have "(p \<parallel> \<epsilon> \<cdot> \<Theta>) \<cdot> v \<Down> PairV TrueV v" by fastforce
    moreover have "\<rhd> \<cdot> PairV TrueV v \<Down> InlV (PairV UnitV v)" by (simp add: TrueV_def)
    ultimately have "(\<rhd> \<cdot> p \<parallel> \<epsilon> \<cdot> \<Theta>) \<cdot> v \<Down> InlV (PairV UnitV v)" by fastforce
    moreover have "(\<pi>\<^sub>2 \<bar> \<pi>\<^sub>2) \<cdot> InlV (PairV UnitV v) \<Down> InlV v" by simp
    ultimately show "(\<pi>\<^sub>2 \<bar> \<pi>\<^sub>2 \<cdot> \<rhd> \<cdot> p \<parallel> \<epsilon> \<cdot> \<Theta>) \<cdot> v \<Down> InlV v" by fastforce
  qed

lemma ev_pred_f [simp]: "p \<cdot> v \<Down> FalseV \<Longrightarrow> ? p \<cdot> v \<Down> InrV v"
  proof (unfold predicate_def)
    have "\<Theta> \<cdot> v \<Down> PairV v v" by simp
    moreover assume "p \<cdot> v \<Down> FalseV"
    moreover hence "(p \<parallel> \<epsilon>) \<cdot> PairV v v \<Down> PairV FalseV v" by simp
    ultimately have "(p \<parallel> \<epsilon> \<cdot> \<Theta>) \<cdot> v \<Down> PairV FalseV v" by fastforce
    moreover have "\<rhd> \<cdot> PairV FalseV v \<Down> InrV (PairV UnitV v)" by (simp add: FalseV_def)
    ultimately have "(\<rhd> \<cdot> p \<parallel> \<epsilon> \<cdot> \<Theta>) \<cdot> v \<Down> InrV (PairV UnitV v)" by fastforce
    moreover have "(\<pi>\<^sub>2 \<bar> \<pi>\<^sub>2) \<cdot> InrV (PairV UnitV v) \<Down> InrV v" by simp
    ultimately show "(\<pi>\<^sub>2 \<bar> \<pi>\<^sub>2 \<cdot> \<rhd> \<cdot> p \<parallel> \<epsilon> \<cdot> \<Theta>) \<cdot> v \<Down> InrV v" by fastforce
  qed

lemma ev_swap [simp]: "\<bowtie> \<cdot> PairV v\<^sub>1 v\<^sub>2 \<Down> PairV v\<^sub>2 v\<^sub>1"
  proof (unfold swap_def)
    show "\<pi>\<^sub>2 \<triangle> \<pi>\<^sub>1 \<cdot> PairV v\<^sub>1 v\<^sub>2 \<Down> PairV v\<^sub>2 v\<^sub>1" by simp
  qed

lemma ev_dstrl [simp]: "\<lhd> \<cdot> PairV v\<^sub>1 (InlV v\<^sub>2) \<Down> InlV (PairV v\<^sub>1 v\<^sub>2)"
  proof (unfold distribute_right_def)
    have "\<bowtie> \<cdot> PairV v\<^sub>1 (InlV v\<^sub>2) \<Down> PairV (InlV v\<^sub>2) v\<^sub>1" by simp
    moreover have "\<rhd> \<cdot> PairV (InlV v\<^sub>2) v\<^sub>1 \<Down> InlV (PairV v\<^sub>2 v\<^sub>1)" by simp
    ultimately have "(\<rhd> \<cdot> \<bowtie>) \<cdot> PairV v\<^sub>1 (InlV v\<^sub>2) \<Down> InlV (PairV v\<^sub>2 v\<^sub>1)" by fastforce
    moreover have "\<bowtie> \<bar> \<bowtie> \<cdot> InlV (PairV v\<^sub>2 v\<^sub>1) \<Down> InlV (PairV v\<^sub>1 v\<^sub>2)" by simp
    ultimately show "(\<bowtie> \<bar> \<bowtie> \<cdot> \<rhd> \<cdot> \<bowtie>) \<cdot> PairV v\<^sub>1 (InlV v\<^sub>2) \<Down> InlV (PairV v\<^sub>1 v\<^sub>2)" by fastforce
  qed

lemma ev_dstrr [simp]: "\<lhd> \<cdot> PairV v\<^sub>1 (InrV v\<^sub>2) \<Down> InrV (PairV v\<^sub>1 v\<^sub>2)"
  proof (unfold distribute_right_def)
    have "\<bowtie> \<cdot> PairV v\<^sub>1 (InrV v\<^sub>2) \<Down> PairV (InrV v\<^sub>2) v\<^sub>1" by simp
    moreover have "\<rhd> \<cdot> PairV (InrV v\<^sub>2) v\<^sub>1 \<Down> InrV (PairV v\<^sub>2 v\<^sub>1)" by simp
    ultimately have "(\<rhd> \<cdot> \<bowtie>) \<cdot> PairV v\<^sub>1 (InrV v\<^sub>2) \<Down> InrV (PairV v\<^sub>2 v\<^sub>1)" by fastforce
    moreover have "\<bowtie> \<bar> \<bowtie> \<cdot> InrV (PairV v\<^sub>2 v\<^sub>1) \<Down> InrV (PairV v\<^sub>1 v\<^sub>2)" by simp
    ultimately show "(\<bowtie> \<bar> \<bowtie> \<cdot> \<rhd> \<cdot> \<bowtie>) \<cdot> PairV v\<^sub>1 (InrV v\<^sub>2) \<Down> InrV (PairV v\<^sub>1 v\<^sub>2)" by fastforce
  qed

end
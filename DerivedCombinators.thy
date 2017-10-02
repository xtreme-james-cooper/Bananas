theory DerivedCombinators
imports BananasLanguage
begin

(* derived types *)

abbreviation Bool :: type where
  "Bool \<equiv> \<one> \<oplus> \<one>"

abbreviation TrueV :: val where
  "TrueV \<equiv> InlV UnitV"

abbreviation FalseV :: val where
  "FalseV \<equiv> InrV UnitV"

abbreviation NatF :: funct where
  "NatF \<equiv> K \<one> \<Oplus> Id"

abbreviation Nat :: type where
  "Nat \<equiv> \<mu> NatF"

abbreviation ZeroV :: val where
  "ZeroV \<equiv> InjV NatF TrueV" (* = InjV NatF (InlV UnitV), but otherwise the pun prevents collapsing *)

abbreviation SuccV :: "val \<Rightarrow> val" where
  "SuccV v \<equiv> InjV NatF (InrV v)"

abbreviation succ :: expr where
  "succ \<equiv> \<succ>\<^bsub>NatF\<^esub> \<cdot> \<iota>\<^sub>r"

abbreviation ListF :: "type \<Rightarrow> funct" where
  "ListF t \<equiv> K \<one> \<Oplus> K t \<Otimes> Id"

abbreviation List :: "type \<Rightarrow> type" where
  "List t \<equiv> \<mu> (ListF t)"

abbreviation NilV :: "type \<Rightarrow> val" where
  "NilV t \<equiv> InjV (ListF t) (InlV UnitV)"

abbreviation ConsV :: "type \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val" where
  "ConsV t v\<^sub>1 v\<^sub>2 \<equiv> InjV (ListF t) (InrV (PairV v\<^sub>1 v\<^sub>2))"

abbreviation cons :: "type \<Rightarrow> expr" ("cons\<^bsub>_\<^esub>") where
  "cons\<^bsub>t\<^esub> \<equiv> \<succ>\<^bsub>ListF t\<^esub> \<cdot> \<iota>\<^sub>r"

lemma "TrueV \<turnstile> Bool" by simp
lemma "FalseV \<turnstile> Bool" by simp
lemma "ZeroV \<turnstile> Nat" by simp
lemma "n \<turnstile> Nat \<Longrightarrow> SuccV n \<turnstile> Nat" by simp
lemma "NilV t \<turnstile> List t" by simp
lemma "v\<^sub>1 \<turnstile> t \<Longrightarrow> v\<^sub>2 \<turnstile> List t \<Longrightarrow> ConsV t v\<^sub>1 v\<^sub>2 \<turnstile> List t" by simp

lemma [simp]: "succ \<turnstile> Nat \<rightarrow> Nat"
  proof -
    have "\<succ>\<^bsub>NatF\<^esub> \<turnstile> Nat \<star> NatF \<rightarrow> Nat" by (metis tc_inj)
    thus "succ \<turnstile> Nat \<rightarrow> Nat" by simp
  qed

lemma [simp]: "cons\<^bsub>t\<^esub> \<turnstile> t \<otimes> List t \<rightarrow> List t"
  proof -
    have "\<succ>\<^bsub>ListF t\<^esub> \<turnstile> List t \<star> ListF t \<rightarrow> List t" by (metis tc_inj)
    thus "cons\<^bsub>t\<^esub> \<turnstile> t \<otimes> List t \<rightarrow> List t" by simp
  qed

(* derived combinators *)

abbreviation tuple_pair :: "expr \<Rightarrow> expr \<Rightarrow> expr" (infix "\<triangle>" 80) where
  "e\<^sub>1 \<triangle> e\<^sub>2 \<equiv> e\<^sub>1 \<parallel> e\<^sub>2 \<cdot> \<Theta>"

abbreviation case_strip :: "expr \<Rightarrow> expr \<Rightarrow> expr" (infix "\<nabla>" 80) where
  "e\<^sub>l \<nabla> e\<^sub>r \<equiv> \<Xi> \<cdot> e\<^sub>l \<bar> e\<^sub>r"

abbreviation predicate :: "expr \<Rightarrow> expr" ("_?") where
  "p? \<equiv> \<pi>\<^sub>2 \<bar> \<pi>\<^sub>2 \<cdot> \<rhd> \<cdot> p \<parallel> \<epsilon> \<cdot> \<Theta>"

abbreviation swap :: expr ("\<bowtie>") where
  "\<bowtie> \<equiv> \<pi>\<^sub>2 \<triangle> \<pi>\<^sub>1"

abbreviation distribute_right :: expr ("\<lhd>") where
  "\<lhd> \<equiv> \<bowtie> \<bar> \<bowtie> \<cdot> \<rhd> \<cdot> \<bowtie>"

abbreviation if_expr :: "expr \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr" ("IF _ THEN _ ELSE _ FI") where
  "IF p THEN e\<^sub>t ELSE e\<^sub>f FI \<equiv> e\<^sub>t \<nabla> e\<^sub>f \<cdot> (p?)" 

abbreviation not_expr :: expr ("not") where
  "not \<equiv> IF \<epsilon> THEN \<kappa> FalseV ELSE \<kappa> TrueV FI" 

lemma [simp]: "f\<^sub>1 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> f\<^sub>2 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>3 \<Longrightarrow> f\<^sub>1 \<triangle> f\<^sub>2 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<otimes> t\<^sub>3"
  proof - 
    assume "f\<^sub>1 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2"
       and "f\<^sub>2 \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>3"
    hence "f\<^sub>1 \<parallel> f\<^sub>2 \<turnstile> t\<^sub>1 \<otimes> t\<^sub>1 \<rightarrow> t\<^sub>2 \<otimes> t\<^sub>3" by simp
    thus "f\<^sub>1 \<parallel> f\<^sub>2 \<cdot> \<Theta> \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<otimes> t\<^sub>3" by simp
  qed

lemma [simp]: "f\<^sub>l \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>3 \<Longrightarrow> f\<^sub>r \<turnstile> t\<^sub>2 \<rightarrow> t\<^sub>3 \<Longrightarrow> f\<^sub>l \<nabla> f\<^sub>r \<turnstile> t\<^sub>1 \<oplus> t\<^sub>2 \<rightarrow> t\<^sub>3"
  proof -
    assume "f\<^sub>l \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>3"
       and "f\<^sub>r \<turnstile> t\<^sub>2 \<rightarrow> t\<^sub>3"
    hence "f\<^sub>l \<bar> f\<^sub>r \<turnstile> t\<^sub>1 \<oplus> t\<^sub>2 \<rightarrow> t\<^sub>3 \<oplus> t\<^sub>3" by simp
    moreover have "\<Xi> \<turnstile> t\<^sub>3 \<oplus> t\<^sub>3 \<rightarrow> t\<^sub>3" by simp
    ultimately show "\<Xi> \<cdot> f\<^sub>l \<bar> f\<^sub>r \<turnstile> t\<^sub>1 \<oplus> t\<^sub>2 \<rightarrow> t\<^sub>3" by (metis tc_comp)
  qed

lemma [simp]: "p \<turnstile> t \<rightarrow> Bool \<Longrightarrow> p? \<turnstile> t \<rightarrow> t \<oplus> t"
  proof -
    assume "p \<turnstile> t \<rightarrow> Bool"
    hence "p \<parallel> \<epsilon> \<turnstile> t \<otimes> t \<rightarrow> Bool \<otimes> t" by simp
    moreover have "\<Theta> \<turnstile> t \<rightarrow> t \<otimes> t" by simp
    moreover have "\<rhd> \<turnstile> Bool \<otimes> t \<rightarrow> \<one> \<otimes> t \<oplus> \<one> \<otimes> t" by simp
    ultimately have "\<rhd> \<cdot> p \<parallel> \<epsilon> \<cdot> \<Theta> \<turnstile> t \<rightarrow> \<one> \<otimes> t \<oplus> \<one> \<otimes> t" by (metis tc_comp)
    moreover have "\<pi>\<^sub>2 \<bar> \<pi>\<^sub>2 \<turnstile> \<one> \<otimes> t \<oplus> \<one> \<otimes> t \<rightarrow> t \<oplus> t" by simp
    ultimately show "\<pi>\<^sub>2 \<bar> \<pi>\<^sub>2 \<cdot> \<rhd> \<cdot> p \<parallel> \<epsilon> \<cdot> \<Theta> \<turnstile> t \<rightarrow> t \<oplus> t" by (metis tc_comp)
  qed

lemma [simp]: "\<bowtie> \<turnstile> t\<^sub>1 \<otimes> t\<^sub>2 \<rightarrow> t\<^sub>2 \<otimes> t\<^sub>1" 
  by simp

lemma [simp]: "\<lhd> \<turnstile> t\<^sub>3 \<otimes> (t\<^sub>1 \<oplus> t\<^sub>2) \<rightarrow> t\<^sub>3 \<otimes> t\<^sub>1 \<oplus> t\<^sub>3 \<otimes> t\<^sub>2"
  proof -
    have "\<rhd> \<turnstile> (t\<^sub>1 \<oplus> t\<^sub>2) \<otimes> t\<^sub>3 \<rightarrow> t\<^sub>1 \<otimes> t\<^sub>3 \<oplus> t\<^sub>2 \<otimes> t\<^sub>3" by simp
    moreover have "\<bowtie> \<turnstile> t\<^sub>3 \<otimes> (t\<^sub>1 \<oplus> t\<^sub>2) \<rightarrow> (t\<^sub>1 \<oplus> t\<^sub>2) \<otimes> t\<^sub>3" by simp
    ultimately have "\<rhd> \<cdot> \<bowtie> \<turnstile> t\<^sub>3 \<otimes> (t\<^sub>1 \<oplus> t\<^sub>2) \<rightarrow> t\<^sub>1 \<otimes> t\<^sub>3 \<oplus> t\<^sub>2 \<otimes> t\<^sub>3" by (metis tc_comp)
    moreover have "\<bowtie> \<bar> \<bowtie> \<turnstile> t\<^sub>1 \<otimes> t\<^sub>3 \<oplus> t\<^sub>2 \<otimes> t\<^sub>3 \<rightarrow> t\<^sub>3 \<otimes> t\<^sub>1 \<oplus> t\<^sub>3 \<otimes> t\<^sub>2" by simp
    ultimately show "\<bowtie> \<bar> \<bowtie> \<cdot> \<rhd> \<cdot> \<bowtie> \<turnstile> t\<^sub>3 \<otimes> (t\<^sub>1 \<oplus> t\<^sub>2) \<rightarrow> t\<^sub>3 \<otimes> t\<^sub>1 \<oplus> t\<^sub>3 \<otimes> t\<^sub>2" by (metis tc_comp)
  qed

lemma [simp]: "p \<turnstile> t\<^sub>1 \<rightarrow> Bool \<Longrightarrow> e\<^sub>t \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> e\<^sub>f \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> 
    IF p THEN e\<^sub>t ELSE e\<^sub>f FI \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2"
  proof -
    assume "e\<^sub>t \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2"
       and "e\<^sub>f \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2"
    hence "e\<^sub>t \<nabla> e\<^sub>f \<turnstile> t\<^sub>1 \<oplus> t\<^sub>1 \<rightarrow> t\<^sub>2" by simp
    moreover assume "p \<turnstile> t\<^sub>1 \<rightarrow> Bool"
    ultimately show "IF p THEN e\<^sub>t ELSE e\<^sub>f FI \<turnstile> t\<^sub>1 \<rightarrow> t\<^sub>2" by simp
  qed

lemma [simp]: "not \<turnstile> Bool \<rightarrow> Bool"
  by simp

lemma [simp]: "f\<^sub>1 \<cdot> v \<Down> v\<^sub>1 \<Longrightarrow> f\<^sub>2 \<cdot> v \<Down> v\<^sub>2 \<Longrightarrow> f\<^sub>1 \<triangle> f\<^sub>2 \<cdot> v \<Down> PairV v\<^sub>1 v\<^sub>2"
  proof -
    assume "f\<^sub>1 \<cdot> v \<Down> v\<^sub>1"
       and "f\<^sub>2 \<cdot> v \<Down> v\<^sub>2"
    moreover have "\<Theta> \<cdot> v \<Down> PairV v v" by simp
    ultimately show "(f\<^sub>1 \<parallel> f\<^sub>2 \<cdot> \<Theta>) \<cdot> v \<Down> PairV v\<^sub>1 v\<^sub>2" by fastforce
  qed

lemma [simp]: "f\<^sub>l \<cdot> v \<Down> v' \<Longrightarrow> f\<^sub>l \<nabla> f\<^sub>r \<cdot> InlV v \<Down> v'"
  proof -
    assume "f\<^sub>l \<cdot> v \<Down> v'"
    hence "f\<^sub>l \<bar> f\<^sub>r \<cdot> InlV v \<Down> InlV v'" by simp
    thus "(\<Xi> \<cdot> f\<^sub>l \<bar> f\<^sub>r) \<cdot> InlV v \<Down> v'" by fastforce
  qed

lemma [simp]: "f\<^sub>r \<cdot> v \<Down> v' \<Longrightarrow> f\<^sub>l \<nabla> f\<^sub>r \<cdot> InrV v \<Down> v'"
  proof -
    assume "f\<^sub>r \<cdot> v \<Down> v'"
    hence "f\<^sub>l \<bar> f\<^sub>r \<cdot> InrV v \<Down> InrV v'" by simp
    thus "(\<Xi> \<cdot> f\<^sub>l \<bar> f\<^sub>r) \<cdot> InrV v \<Down> v'" by fastforce
  qed

lemma [simp]: "p \<cdot> v \<Down> TrueV \<Longrightarrow> p? \<cdot> v \<Down> InlV v"
  proof -
    have "\<Theta> \<cdot> v \<Down> PairV v v" by simp
    moreover assume "p \<cdot> v \<Down> TrueV"
    moreover hence "(p \<parallel> \<epsilon>) \<cdot> PairV v v \<Down> PairV TrueV v" by simp
    ultimately have "(p \<parallel> \<epsilon> \<cdot> \<Theta>) \<cdot> v \<Down> PairV TrueV v" by fastforce
    moreover have "\<rhd> \<cdot> PairV TrueV v \<Down> InlV (PairV UnitV v)" by simp
    ultimately have "(\<rhd> \<cdot> p \<parallel> \<epsilon> \<cdot> \<Theta>) \<cdot> v \<Down> InlV (PairV UnitV v)" by fastforce
    moreover have "(\<pi>\<^sub>2 \<bar> \<pi>\<^sub>2) \<cdot> InlV (PairV UnitV v) \<Down> InlV v" by simp
    ultimately show "(\<pi>\<^sub>2 \<bar> \<pi>\<^sub>2 \<cdot> \<rhd> \<cdot> p \<parallel> \<epsilon> \<cdot> \<Theta>) \<cdot> v \<Down> InlV v" by fastforce
  qed

lemma [simp]: "p \<cdot> v \<Down> FalseV \<Longrightarrow> p? \<cdot> v \<Down> InrV v"
  proof -
    have "\<Theta> \<cdot> v \<Down> PairV v v" by simp
    moreover assume "p \<cdot> v \<Down> FalseV"
    moreover hence "(p \<parallel> \<epsilon>) \<cdot> PairV v v \<Down> PairV FalseV v" by simp
    ultimately have "(p \<parallel> \<epsilon> \<cdot> \<Theta>) \<cdot> v \<Down> PairV FalseV v" by fastforce
    moreover have "\<rhd> \<cdot> PairV FalseV v \<Down> InrV (PairV UnitV v)" by simp
    ultimately have "(\<rhd> \<cdot> p \<parallel> \<epsilon> \<cdot> \<Theta>) \<cdot> v \<Down> InrV (PairV UnitV v)" by fastforce
    moreover have "(\<pi>\<^sub>2 \<bar> \<pi>\<^sub>2) \<cdot> InrV (PairV UnitV v) \<Down> InrV v" by simp
    ultimately show "(\<pi>\<^sub>2 \<bar> \<pi>\<^sub>2 \<cdot> \<rhd> \<cdot> p \<parallel> \<epsilon> \<cdot> \<Theta>) \<cdot> v \<Down> InrV v" by fastforce
  qed

lemma [simp]: "\<bowtie> \<cdot> PairV v\<^sub>1 v\<^sub>2 \<Down> PairV v\<^sub>2 v\<^sub>1"
  by simp

lemma [simp]: "\<lhd> \<cdot> PairV v\<^sub>1 (InlV v\<^sub>2) \<Down> InlV (PairV v\<^sub>1 v\<^sub>2)"
  proof -
    have "\<bowtie> \<cdot> PairV v\<^sub>1 (InlV v\<^sub>2) \<Down> PairV (InlV v\<^sub>2) v\<^sub>1" by simp
    moreover have "\<rhd> \<cdot> PairV (InlV v\<^sub>2) v\<^sub>1 \<Down> InlV (PairV v\<^sub>2 v\<^sub>1)" by simp
    ultimately have "(\<rhd> \<cdot> \<bowtie>) \<cdot> PairV v\<^sub>1 (InlV v\<^sub>2) \<Down> InlV (PairV v\<^sub>2 v\<^sub>1)" by fastforce
    moreover have "\<bowtie> \<bar> \<bowtie> \<cdot> InlV (PairV v\<^sub>2 v\<^sub>1) \<Down> InlV (PairV v\<^sub>1 v\<^sub>2)" by simp
    ultimately show "(\<bowtie> \<bar> \<bowtie> \<cdot> \<rhd> \<cdot> \<bowtie>) \<cdot> PairV v\<^sub>1 (InlV v\<^sub>2) \<Down> InlV (PairV v\<^sub>1 v\<^sub>2)" by fastforce
  qed

lemma [simp]: "\<lhd> \<cdot> PairV v\<^sub>1 (InrV v\<^sub>2) \<Down> InrV (PairV v\<^sub>1 v\<^sub>2)"
  proof -
    have "\<bowtie> \<cdot> PairV v\<^sub>1 (InrV v\<^sub>2) \<Down> PairV (InrV v\<^sub>2) v\<^sub>1" by simp
    moreover have "\<rhd> \<cdot> PairV (InrV v\<^sub>2) v\<^sub>1 \<Down> InrV (PairV v\<^sub>2 v\<^sub>1)" by simp
    ultimately have "(\<rhd> \<cdot> \<bowtie>) \<cdot> PairV v\<^sub>1 (InrV v\<^sub>2) \<Down> InrV (PairV v\<^sub>2 v\<^sub>1)" by fastforce
    moreover have "\<bowtie> \<bar> \<bowtie> \<cdot> InrV (PairV v\<^sub>2 v\<^sub>1) \<Down> InrV (PairV v\<^sub>1 v\<^sub>2)" by simp
    ultimately show "(\<bowtie> \<bar> \<bowtie> \<cdot> \<rhd> \<cdot> \<bowtie>) \<cdot> PairV v\<^sub>1 (InrV v\<^sub>2) \<Down> InrV (PairV v\<^sub>1 v\<^sub>2)" by fastforce
  qed

lemma [simp]: "p \<cdot> v \<Down> TrueV \<Longrightarrow> e\<^sub>t \<cdot> v \<Down> v' \<Longrightarrow> IF p THEN e\<^sub>t ELSE e\<^sub>f FI \<cdot> v \<Down> v'"
  proof -
    assume "p \<cdot> v \<Down> TrueV" 
    hence X: "p? \<cdot> v \<Down> InlV v" by simp
    assume "e\<^sub>t \<cdot> v \<Down> v'"
    hence "e\<^sub>t \<nabla> e\<^sub>f \<cdot> InlV v \<Down> v'" by simp
    with X show "IF p THEN e\<^sub>t ELSE e\<^sub>f FI \<cdot> v \<Down> v'" by fastforce
  qed

lemma [simp]: "p \<cdot> v \<Down> FalseV \<Longrightarrow> e\<^sub>f \<cdot> v \<Down> v' \<Longrightarrow> IF p THEN e\<^sub>t ELSE e\<^sub>f FI \<cdot> v \<Down> v'"
  proof -
    assume "p \<cdot> v \<Down> FalseV" 
    hence X: "p? \<cdot> v \<Down> InrV v" by simp
    assume "e\<^sub>f \<cdot> v \<Down> v'"
    hence "e\<^sub>t \<nabla> e\<^sub>f \<cdot> InrV v \<Down> v'" by simp
    with X show "IF p THEN e\<^sub>t ELSE e\<^sub>f FI \<cdot> v \<Down> v'" by fastforce
  qed

lemma [simp]: "not \<cdot> TrueV \<Down> FalseV"
  by simp

lemma [simp]: "not \<cdot> FalseV \<Down> TrueV"
  by simp

end
theory DerivedCombinators
imports BananasExpression
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

lemma "\<Gamma> \<turnstile> TrueV : Bool" by simp
lemma "\<Gamma> \<turnstile> FalseV : Bool" by simp
lemma "\<Gamma> \<turnstile> ZeroV : Nat" by simp
lemma "\<Gamma> \<turnstile> n : Nat \<Longrightarrow> \<Gamma> \<turnstile> SuccV n : Nat" by simp
lemma "\<Gamma> \<turnstile> NilV t : List t" by simp
lemma "\<Gamma> \<turnstile> v\<^sub>1 : t \<Longrightarrow> \<Gamma> \<turnstile> v\<^sub>2 : List t \<Longrightarrow> \<Gamma> \<turnstile> ConsV t v\<^sub>1 v\<^sub>2 : List t" by simp

lemma [simp]: "\<Gamma> \<turnstile> succ : Nat \<rightarrow> Nat"
  proof -
    have "\<Gamma> \<turnstile> \<succ>\<^bsub>NatF\<^esub> : Nat \<star> NatF \<rightarrow> Nat" by (metis tc_inj)
    thus "\<Gamma> \<turnstile> succ : Nat \<rightarrow> Nat" by simp
  qed

lemma [simp]: "\<Gamma> \<turnstile> cons\<^bsub>t\<^esub> : t \<otimes> List t \<rightarrow> List t"
  proof -
    have "\<Gamma> \<turnstile> \<succ>\<^bsub>ListF t\<^esub> : List t \<star> ListF t \<rightarrow> List t" by (metis tc_inj)
    thus "\<Gamma> \<turnstile> cons\<^bsub>t\<^esub> : t \<otimes> List t \<rightarrow> List t" by simp
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

lemma [simp]: "\<Gamma> \<turnstile> f\<^sub>1 : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> f\<^sub>2 : t\<^sub>1 \<rightarrow> t\<^sub>3 \<Longrightarrow> \<Gamma> \<turnstile> f\<^sub>1 \<triangle> f\<^sub>2 : t\<^sub>1 \<rightarrow> t\<^sub>2 \<otimes> t\<^sub>3"
  proof - 
    assume "\<Gamma> \<turnstile> f\<^sub>1 : t\<^sub>1 \<rightarrow> t\<^sub>2"
       and "\<Gamma> \<turnstile> f\<^sub>2 : t\<^sub>1 \<rightarrow> t\<^sub>3"
    hence "\<Gamma> \<turnstile> f\<^sub>1 \<parallel> f\<^sub>2 : t\<^sub>1 \<otimes> t\<^sub>1 \<rightarrow> t\<^sub>2 \<otimes> t\<^sub>3" by simp
    thus "\<Gamma> \<turnstile> f\<^sub>1 \<parallel> f\<^sub>2 \<cdot> \<Theta> : t\<^sub>1 \<rightarrow> t\<^sub>2 \<otimes> t\<^sub>3" by simp
  qed

lemma [simp]: "\<Gamma> \<turnstile> f\<^sub>l : t\<^sub>1 \<rightarrow> t\<^sub>3 \<Longrightarrow> \<Gamma> \<turnstile> f\<^sub>r : t\<^sub>2 \<rightarrow> t\<^sub>3 \<Longrightarrow> \<Gamma> \<turnstile> f\<^sub>l \<nabla> f\<^sub>r : t\<^sub>1 \<oplus> t\<^sub>2 \<rightarrow> t\<^sub>3"
  proof -
    assume "\<Gamma> \<turnstile> f\<^sub>l : t\<^sub>1 \<rightarrow> t\<^sub>3"
       and "\<Gamma> \<turnstile> f\<^sub>r : t\<^sub>2 \<rightarrow> t\<^sub>3"
    hence "\<Gamma> \<turnstile> f\<^sub>l \<bar> f\<^sub>r : t\<^sub>1 \<oplus> t\<^sub>2 \<rightarrow> t\<^sub>3 \<oplus> t\<^sub>3" by simp
    moreover have "\<Gamma> \<turnstile> \<Xi> : t\<^sub>3 \<oplus> t\<^sub>3 \<rightarrow> t\<^sub>3" by simp
    ultimately show "\<Gamma> \<turnstile> \<Xi> \<cdot> f\<^sub>l \<bar> f\<^sub>r : t\<^sub>1 \<oplus> t\<^sub>2 \<rightarrow> t\<^sub>3" by (metis tc_comp)
  qed

lemma [simp]: "\<Gamma> \<turnstile> p : t \<rightarrow> Bool \<Longrightarrow> \<Gamma> \<turnstile> p? : t \<rightarrow> t \<oplus> t"
  proof -
    assume "\<Gamma> \<turnstile> p : t \<rightarrow> Bool"
    hence "\<Gamma> \<turnstile> p \<parallel> \<epsilon> : t \<otimes> t \<rightarrow> Bool \<otimes> t" by simp
    moreover have "\<Gamma> \<turnstile> \<Theta> : t \<rightarrow> t \<otimes> t" by simp
    moreover have "\<Gamma> \<turnstile> \<rhd> : Bool \<otimes> t \<rightarrow> \<one> \<otimes> t \<oplus> \<one> \<otimes> t" by simp
    ultimately have "\<Gamma> \<turnstile> \<rhd> \<cdot> p \<parallel> \<epsilon> \<cdot> \<Theta> : t \<rightarrow> \<one> \<otimes> t \<oplus> \<one> \<otimes> t" by (metis tc_comp)
    moreover have "\<Gamma> \<turnstile> \<pi>\<^sub>2 \<bar> \<pi>\<^sub>2 : \<one> \<otimes> t \<oplus> \<one> \<otimes> t \<rightarrow> t \<oplus> t" by simp
    ultimately show "\<Gamma> \<turnstile> \<pi>\<^sub>2 \<bar> \<pi>\<^sub>2 \<cdot> \<rhd> \<cdot> p \<parallel> \<epsilon> \<cdot> \<Theta> : t \<rightarrow> t \<oplus> t" by (metis tc_comp)
  qed

lemma [simp]: "\<Gamma> \<turnstile> \<bowtie> : t\<^sub>1 \<otimes> t\<^sub>2 \<rightarrow> t\<^sub>2 \<otimes> t\<^sub>1" 
  by simp

lemma [simp]: "\<Gamma> \<turnstile> \<lhd> : t\<^sub>3 \<otimes> (t\<^sub>1 \<oplus> t\<^sub>2) \<rightarrow> t\<^sub>3 \<otimes> t\<^sub>1 \<oplus> t\<^sub>3 \<otimes> t\<^sub>2"
  proof -
    have "\<Gamma> \<turnstile> \<rhd> : (t\<^sub>1 \<oplus> t\<^sub>2) \<otimes> t\<^sub>3 \<rightarrow> t\<^sub>1 \<otimes> t\<^sub>3 \<oplus> t\<^sub>2 \<otimes> t\<^sub>3" by simp
    moreover have "\<Gamma> \<turnstile> \<bowtie> : t\<^sub>3 \<otimes> (t\<^sub>1 \<oplus> t\<^sub>2) \<rightarrow> (t\<^sub>1 \<oplus> t\<^sub>2) \<otimes> t\<^sub>3" by simp
    ultimately have "\<Gamma> \<turnstile> \<rhd> \<cdot> \<bowtie> : t\<^sub>3 \<otimes> (t\<^sub>1 \<oplus> t\<^sub>2) \<rightarrow> t\<^sub>1 \<otimes> t\<^sub>3 \<oplus> t\<^sub>2 \<otimes> t\<^sub>3" by (metis tc_comp)
    moreover have "\<Gamma> \<turnstile> \<bowtie> \<bar> \<bowtie> : t\<^sub>1 \<otimes> t\<^sub>3 \<oplus> t\<^sub>2 \<otimes> t\<^sub>3 \<rightarrow> t\<^sub>3 \<otimes> t\<^sub>1 \<oplus> t\<^sub>3 \<otimes> t\<^sub>2" by simp
    ultimately show "\<Gamma> \<turnstile> \<bowtie> \<bar> \<bowtie> \<cdot> \<rhd> \<cdot> \<bowtie> : t\<^sub>3 \<otimes> (t\<^sub>1 \<oplus> t\<^sub>2) \<rightarrow> t\<^sub>3 \<otimes> t\<^sub>1 \<oplus> t\<^sub>3 \<otimes> t\<^sub>2" by (metis tc_comp)
  qed

lemma [simp]: "\<Gamma> \<turnstile> p : t\<^sub>1 \<rightarrow> Bool \<Longrightarrow> \<Gamma> \<turnstile> e\<^sub>t : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> e\<^sub>f : t\<^sub>1 \<rightarrow> t\<^sub>2 \<Longrightarrow> 
    \<Gamma> \<turnstile> IF p THEN e\<^sub>t ELSE e\<^sub>f FI : t\<^sub>1 \<rightarrow> t\<^sub>2"
  proof -
    assume "\<Gamma> \<turnstile> e\<^sub>t : t\<^sub>1 \<rightarrow> t\<^sub>2"
       and "\<Gamma> \<turnstile> e\<^sub>f : t\<^sub>1 \<rightarrow> t\<^sub>2"
    hence "\<Gamma> \<turnstile> e\<^sub>t \<nabla> e\<^sub>f : t\<^sub>1 \<oplus> t\<^sub>1 \<rightarrow> t\<^sub>2" by simp
    moreover assume "\<Gamma> \<turnstile> p : t\<^sub>1 \<rightarrow> Bool"
    ultimately show "\<Gamma> \<turnstile> IF p THEN e\<^sub>t ELSE e\<^sub>f FI : t\<^sub>1 \<rightarrow> t\<^sub>2" by simp
  qed

lemma [simp]: "\<Gamma> \<turnstile> not : Bool \<rightarrow> Bool"
  by simp

lemma [simp]: "\<Lambda> \<turnstile> f\<^sub>1 \<cdot> v \<Down> v\<^sub>1 \<Longrightarrow> \<Lambda> \<turnstile> f\<^sub>2 \<cdot> v \<Down> v\<^sub>2 \<Longrightarrow> \<Lambda> \<turnstile> f\<^sub>1 \<triangle> f\<^sub>2 \<cdot> v \<Down> PairV v\<^sub>1 v\<^sub>2"
  proof -
    assume "\<Lambda> \<turnstile> f\<^sub>1 \<cdot> v \<Down> v\<^sub>1"
       and "\<Lambda> \<turnstile> f\<^sub>2 \<cdot> v \<Down> v\<^sub>2"
    moreover have "\<Lambda> \<turnstile> \<Theta> \<cdot> v \<Down> PairV v v" by simp
    ultimately show "\<Lambda> \<turnstile> (f\<^sub>1 \<parallel> f\<^sub>2 \<cdot> \<Theta>) \<cdot> v \<Down> PairV v\<^sub>1 v\<^sub>2" by fastforce
  qed

lemma [simp]: "\<Lambda> \<turnstile> f\<^sub>l \<cdot> v \<Down> v' \<Longrightarrow> \<Lambda> \<turnstile> f\<^sub>l \<nabla> f\<^sub>r \<cdot> InlV v \<Down> v'"
  proof -
    assume "\<Lambda> \<turnstile> f\<^sub>l \<cdot> v \<Down> v'"
    hence "\<Lambda> \<turnstile> f\<^sub>l \<bar> f\<^sub>r \<cdot> InlV v \<Down> InlV v'" by simp
    thus "\<Lambda> \<turnstile> (\<Xi> \<cdot> f\<^sub>l \<bar> f\<^sub>r) \<cdot> InlV v \<Down> v'" by fastforce
  qed

lemma [simp]: "\<Lambda> \<turnstile> f\<^sub>r \<cdot> v \<Down> v' \<Longrightarrow> \<Lambda> \<turnstile> f\<^sub>l \<nabla> f\<^sub>r \<cdot> InrV v \<Down> v'"
  proof -
    assume "\<Lambda> \<turnstile> f\<^sub>r \<cdot> v \<Down> v'"
    hence "\<Lambda> \<turnstile> f\<^sub>l \<bar> f\<^sub>r \<cdot> InrV v \<Down> InrV v'" by simp
    thus "\<Lambda> \<turnstile> (\<Xi> \<cdot> f\<^sub>l \<bar> f\<^sub>r) \<cdot> InrV v \<Down> v'" by fastforce
  qed

lemma [simp]: "\<Lambda> \<turnstile> p \<cdot> v \<Down> TrueV \<Longrightarrow> \<Lambda> \<turnstile> p? \<cdot> v \<Down> InlV v"
  proof -
    have "\<Lambda> \<turnstile> \<Theta> \<cdot> v \<Down> PairV v v" by simp
    moreover assume "\<Lambda> \<turnstile> p \<cdot> v \<Down> TrueV"
    moreover hence "\<Lambda> \<turnstile> (p \<parallel> \<epsilon>) \<cdot> PairV v v \<Down> PairV TrueV v" by simp
    ultimately have "\<Lambda> \<turnstile> (p \<parallel> \<epsilon> \<cdot> \<Theta>) \<cdot> v \<Down> PairV TrueV v" by fastforce
    moreover have "\<Lambda> \<turnstile> \<rhd> \<cdot> PairV TrueV v \<Down> InlV (PairV UnitV v)" by simp
    ultimately have "\<Lambda> \<turnstile> (\<rhd> \<cdot> p \<parallel> \<epsilon> \<cdot> \<Theta>) \<cdot> v \<Down> InlV (PairV UnitV v)" by fastforce
    moreover have "\<Lambda> \<turnstile> (\<pi>\<^sub>2 \<bar> \<pi>\<^sub>2) \<cdot> InlV (PairV UnitV v) \<Down> InlV v" by simp
    ultimately show "\<Lambda> \<turnstile> (\<pi>\<^sub>2 \<bar> \<pi>\<^sub>2 \<cdot> \<rhd> \<cdot> p \<parallel> \<epsilon> \<cdot> \<Theta>) \<cdot> v \<Down> InlV v" by fastforce
  qed

lemma [simp]: "\<Lambda> \<turnstile> p \<cdot> v \<Down> FalseV \<Longrightarrow> \<Lambda> \<turnstile> p? \<cdot> v \<Down> InrV v"
  proof -
    have "\<Lambda> \<turnstile> \<Theta> \<cdot> v \<Down> PairV v v" by simp
    moreover assume "\<Lambda> \<turnstile> p \<cdot> v \<Down> FalseV"
    moreover hence "\<Lambda> \<turnstile> (p \<parallel> \<epsilon>) \<cdot> PairV v v \<Down> PairV FalseV v" by simp
    ultimately have "\<Lambda> \<turnstile> (p \<parallel> \<epsilon> \<cdot> \<Theta>) \<cdot> v \<Down> PairV FalseV v" by fastforce
    moreover have "\<Lambda> \<turnstile> \<rhd> \<cdot> PairV FalseV v \<Down> InrV (PairV UnitV v)" by simp
    ultimately have "\<Lambda> \<turnstile> (\<rhd> \<cdot> p \<parallel> \<epsilon> \<cdot> \<Theta>) \<cdot> v \<Down> InrV (PairV UnitV v)" by fastforce
    moreover have "\<Lambda> \<turnstile> (\<pi>\<^sub>2 \<bar> \<pi>\<^sub>2) \<cdot> InrV (PairV UnitV v) \<Down> InrV v" by simp
    ultimately show "\<Lambda> \<turnstile> (\<pi>\<^sub>2 \<bar> \<pi>\<^sub>2 \<cdot> \<rhd> \<cdot> p \<parallel> \<epsilon> \<cdot> \<Theta>) \<cdot> v \<Down> InrV v" by fastforce
  qed

lemma [simp]: "\<Lambda> \<turnstile> \<bowtie> \<cdot> PairV v\<^sub>1 v\<^sub>2 \<Down> PairV v\<^sub>2 v\<^sub>1"
  by simp

lemma [simp]: "\<Lambda> \<turnstile> \<lhd> \<cdot> PairV v\<^sub>1 (InlV v\<^sub>2) \<Down> InlV (PairV v\<^sub>1 v\<^sub>2)"
  proof -
    have "\<Lambda> \<turnstile> \<bowtie> \<cdot> PairV v\<^sub>1 (InlV v\<^sub>2) \<Down> PairV (InlV v\<^sub>2) v\<^sub>1" by simp
    moreover have "\<Lambda> \<turnstile> \<rhd> \<cdot> PairV (InlV v\<^sub>2) v\<^sub>1 \<Down> InlV (PairV v\<^sub>2 v\<^sub>1)" by simp
    ultimately have "\<Lambda> \<turnstile> (\<rhd> \<cdot> \<bowtie>) \<cdot> PairV v\<^sub>1 (InlV v\<^sub>2) \<Down> InlV (PairV v\<^sub>2 v\<^sub>1)" by fastforce
    moreover have "\<Lambda> \<turnstile> \<bowtie> \<bar> \<bowtie> \<cdot> InlV (PairV v\<^sub>2 v\<^sub>1) \<Down> InlV (PairV v\<^sub>1 v\<^sub>2)" by simp
    ultimately show "\<Lambda> \<turnstile> (\<bowtie> \<bar> \<bowtie> \<cdot> \<rhd> \<cdot> \<bowtie>) \<cdot> PairV v\<^sub>1 (InlV v\<^sub>2) \<Down> InlV (PairV v\<^sub>1 v\<^sub>2)" by fastforce
  qed

lemma [simp]: "\<Lambda> \<turnstile> \<lhd> \<cdot> PairV v\<^sub>1 (InrV v\<^sub>2) \<Down> InrV (PairV v\<^sub>1 v\<^sub>2)"
  proof -
    have "\<Lambda> \<turnstile> \<bowtie> \<cdot> PairV v\<^sub>1 (InrV v\<^sub>2) \<Down> PairV (InrV v\<^sub>2) v\<^sub>1" by simp
    moreover have "\<Lambda> \<turnstile> \<rhd> \<cdot> PairV (InrV v\<^sub>2) v\<^sub>1 \<Down> InrV (PairV v\<^sub>2 v\<^sub>1)" by simp
    ultimately have "\<Lambda> \<turnstile> (\<rhd> \<cdot> \<bowtie>) \<cdot> PairV v\<^sub>1 (InrV v\<^sub>2) \<Down> InrV (PairV v\<^sub>2 v\<^sub>1)" by fastforce
    moreover have "\<Lambda> \<turnstile> \<bowtie> \<bar> \<bowtie> \<cdot> InrV (PairV v\<^sub>2 v\<^sub>1) \<Down> InrV (PairV v\<^sub>1 v\<^sub>2)" by simp
    ultimately show "\<Lambda> \<turnstile> (\<bowtie> \<bar> \<bowtie> \<cdot> \<rhd> \<cdot> \<bowtie>) \<cdot> PairV v\<^sub>1 (InrV v\<^sub>2) \<Down> InrV (PairV v\<^sub>1 v\<^sub>2)" by fastforce
  qed

lemma [simp]: "\<Lambda> \<turnstile> p \<cdot> v \<Down> TrueV \<Longrightarrow> \<Lambda> \<turnstile> e\<^sub>t \<cdot> v \<Down> v' \<Longrightarrow> \<Lambda> \<turnstile> IF p THEN e\<^sub>t ELSE e\<^sub>f FI \<cdot> v \<Down> v'"
  proof -
    assume "\<Lambda> \<turnstile> p \<cdot> v \<Down> TrueV" 
    hence X: "\<Lambda> \<turnstile> p? \<cdot> v \<Down> InlV v" by simp
    assume "\<Lambda> \<turnstile> e\<^sub>t \<cdot> v \<Down> v'"
    hence "\<Lambda> \<turnstile> e\<^sub>t \<nabla> e\<^sub>f \<cdot> InlV v \<Down> v'" by simp
    with X show "\<Lambda> \<turnstile> IF p THEN e\<^sub>t ELSE e\<^sub>f FI \<cdot> v \<Down> v'" by fastforce
  qed

lemma [simp]: "\<Lambda> \<turnstile> p \<cdot> v \<Down> FalseV \<Longrightarrow> \<Lambda> \<turnstile> e\<^sub>f \<cdot> v \<Down> v' \<Longrightarrow> \<Lambda> \<turnstile> IF p THEN e\<^sub>t ELSE e\<^sub>f FI \<cdot> v \<Down> v'"
  proof -
    assume "\<Lambda> \<turnstile> p \<cdot> v \<Down> FalseV" 
    hence X: "\<Lambda> \<turnstile> p? \<cdot> v \<Down> InrV v" by simp
    assume "\<Lambda> \<turnstile> e\<^sub>f \<cdot> v \<Down> v'"
    hence "\<Lambda> \<turnstile> e\<^sub>t \<nabla> e\<^sub>f \<cdot> InrV v \<Down> v'" by simp
    with X show "\<Lambda> \<turnstile> IF p THEN e\<^sub>t ELSE e\<^sub>f FI \<cdot> v \<Down> v'" by fastforce
  qed

lemma [simp]: "\<Lambda> \<turnstile> not \<cdot> TrueV \<Down> FalseV"
  by simp

lemma [simp]: "\<Lambda> \<turnstile> not \<cdot> FalseV \<Down> TrueV"
  by simp

end
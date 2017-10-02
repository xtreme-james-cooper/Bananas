theory Examples
imports DerivedCombinators PartialEvaluation
begin

definition is_zero_expr :: expr where
  "is_zero_expr = \<epsilon> \<bar> \<kappa> UnitV \<cdot> \<prec>\<^bsub>NatF\<^esub>"

definition pred_expr :: expr where
  "pred_expr = \<kappa> ZeroV \<nabla> \<epsilon> \<cdot> \<prec>\<^bsub>NatF\<^esub>"

definition greater_than_helper :: expr where
  "greater_than_helper = 
      IF is_zero_expr \<cdot> \<pi>\<^sub>1 THEN \<iota>\<^sub>l \<cdot> \<kappa> FalseV 
      ELSE IF is_zero_expr \<cdot> \<pi>\<^sub>2 THEN \<iota>\<^sub>l \<cdot> \<kappa> TrueV 
      ELSE \<iota>\<^sub>r \<cdot> pred_expr \<parallel> pred_expr 
      FI FI"

definition greater_than_expr :: expr where
  "greater_than_expr = \<lparr> \<Xi> \<rparr>\<^bsub>K Bool \<Oplus> Id\<^esub> \<cdot> \<lbrakk> greater_than_helper \<rbrakk>\<^bsub>K Bool \<Oplus> Id\<^esub>"

definition length_expr :: "type \<Rightarrow> expr" ("length\<^bsub>_\<^esub>") where
  "length\<^bsub>t\<^esub> = \<lparr> \<kappa> ZeroV \<nabla> (succ \<cdot> \<pi>\<^sub>2) \<rparr>\<^bsub>ListF t\<^esub>"

lemma [simp]: "is_zero_expr \<turnstile> Nat \<rightarrow> Bool"
  proof (unfold is_zero_expr_def)
    have "\<prec>\<^bsub>NatF\<^esub> \<turnstile> Nat \<rightarrow> Nat \<star> NatF" by (metis tc_outj)
    hence "\<prec>\<^bsub>NatF\<^esub> \<turnstile> Nat \<rightarrow> \<one> \<oplus> Nat" by simp
    moreover have "\<epsilon> \<bar> \<kappa> UnitV \<turnstile> \<one> \<oplus> Nat \<rightarrow> Bool" by simp
    ultimately show "\<epsilon> \<bar> \<kappa> UnitV \<cdot> \<prec>\<^bsub>NatF\<^esub> \<turnstile> Nat \<rightarrow> Bool" by (metis tc_comp)
  qed

lemma [simp]: "pred_expr \<turnstile> Nat \<rightarrow> Nat"
  proof (unfold pred_expr_def)
    have "\<prec>\<^bsub>NatF\<^esub> \<turnstile> Nat \<rightarrow> Nat \<star> NatF" by (metis tc_outj)
    hence "\<prec>\<^bsub>NatF\<^esub> \<turnstile> Nat \<rightarrow> \<one> \<oplus> Nat" by simp
    moreover have "\<kappa> ZeroV \<nabla> \<epsilon> \<turnstile> \<one> \<oplus> Nat \<rightarrow> Nat" by simp
    ultimately show "\<kappa> ZeroV \<nabla> \<epsilon> \<cdot> \<prec>\<^bsub>NatF\<^esub> \<turnstile> Nat \<rightarrow> Nat" by (metis tc_comp)
  qed

lemma [simp]: "greater_than_helper \<turnstile> Nat \<otimes> Nat \<rightarrow> Bool \<oplus> Nat \<otimes> Nat"
  proof (unfold greater_than_helper_def)
    have E: "is_zero_expr \<turnstile> Nat \<rightarrow> Bool" by simp
    moreover have "\<pi>\<^sub>1 \<turnstile> Nat \<otimes> Nat \<rightarrow> Nat" by simp
    ultimately have X: "is_zero_expr \<cdot> \<pi>\<^sub>1 \<turnstile> Nat \<otimes> Nat \<rightarrow> Bool" by (metis tc_comp)
    have I: "\<iota>\<^sub>l \<turnstile> Bool \<rightarrow> Bool \<oplus> Nat \<otimes> Nat" by simp
    moreover have "\<kappa> FalseV \<turnstile> Nat \<otimes> Nat \<rightarrow> Bool" by simp
    ultimately have Y: "\<iota>\<^sub>l \<cdot> \<kappa> FalseV \<turnstile> Nat \<otimes> Nat \<rightarrow> Bool \<oplus> Nat \<otimes> Nat" by (metis tc_comp)
    have "\<pi>\<^sub>2 \<turnstile> Nat \<otimes> Nat \<rightarrow> Nat" by simp
    with E have Z: "is_zero_expr \<cdot> \<pi>\<^sub>2 \<turnstile> Nat \<otimes> Nat \<rightarrow> Bool" by (metis tc_comp)
    have "\<kappa> TrueV \<turnstile> Nat \<otimes> Nat \<rightarrow> Bool" by simp
    with I have W: "\<iota>\<^sub>l \<cdot> \<kappa> TrueV  \<turnstile> Nat \<otimes> Nat \<rightarrow> Bool \<oplus> Nat \<otimes> Nat" by (metis tc_comp)
    have "pred_expr \<parallel> pred_expr \<turnstile> Nat \<otimes> Nat \<rightarrow> Nat \<otimes> Nat" by simp
    moreover have "\<iota>\<^sub>r \<turnstile> Nat \<otimes> Nat \<rightarrow> Bool \<oplus> Nat \<otimes> Nat" by simp
    ultimately have "\<iota>\<^sub>r \<cdot> pred_expr \<parallel> pred_expr \<turnstile> Nat \<otimes> Nat \<rightarrow> Bool \<oplus> Nat \<otimes> Nat" by (metis tc_comp)
    with X Y Z W show "
      IF is_zero_expr \<cdot> \<pi>\<^sub>1 THEN \<iota>\<^sub>l \<cdot> \<kappa> FalseV 
      ELSE IF is_zero_expr \<cdot> \<pi>\<^sub>2 THEN \<iota>\<^sub>l \<cdot> \<kappa> TrueV 
      ELSE \<iota>\<^sub>r \<cdot> pred_expr \<parallel> pred_expr 
      FI FI 
        \<turnstile> Nat \<otimes> Nat \<rightarrow> Bool \<oplus> Nat \<otimes> Nat" by simp
  qed

lemma "greater_than_expr \<turnstile> Nat \<otimes> Nat \<rightarrow> Bool"
  proof (unfold greater_than_expr_def)
    have "\<lparr> \<Xi> \<rparr>\<^bsub>K Bool \<Oplus> funct.Id\<^esub> \<turnstile> \<mu> (K Bool \<Oplus> Id) \<rightarrow> Bool" by simp
    moreover have "\<lbrakk> greater_than_helper \<rbrakk>\<^bsub>K Bool \<Oplus> Id\<^esub> \<turnstile> Nat \<otimes> Nat \<rightarrow> \<mu> (K Bool \<Oplus> Id)" by simp
    ultimately show "\<lparr> \<Xi> \<rparr>\<^bsub>K Bool \<Oplus> funct.Id\<^esub> \<cdot> \<lbrakk> greater_than_helper \<rbrakk>\<^bsub>K Bool \<Oplus> Id\<^esub> 
      \<turnstile> Nat \<otimes> Nat \<rightarrow> Bool" by (metis tc_comp)
  qed

lemma "length\<^bsub>t\<^esub> \<turnstile> List t \<rightarrow> Nat"
  proof (unfold length_expr_def)
    have "succ \<turnstile> Nat \<rightarrow> Nat" by simp
    moreover have "\<pi>\<^sub>2 \<turnstile> t \<otimes> Nat \<rightarrow> Nat" by simp
    ultimately have "succ \<cdot> \<pi>\<^sub>2 \<turnstile> t \<otimes> Nat \<rightarrow> Nat" by (metis tc_comp)
    thus "\<lparr> \<kappa> ZeroV \<nabla> (succ \<cdot> \<pi>\<^sub>2) \<rparr>\<^bsub>ListF t\<^esub> \<turnstile> List t \<rightarrow> Nat" by simp
  qed

primrec nat_to_val :: "nat \<Rightarrow> val" where
  "nat_to_val 0 = ZeroV"
| "nat_to_val (Suc n) = SuccV (nat_to_val n)"

primrec list_to_val :: "type \<Rightarrow> val list \<Rightarrow> val" where
  "list_to_val t [] = NilV t"
| "list_to_val t (v # vs) = ConsV t v (list_to_val t vs)"

abbreviation long_run :: nat where
  "long_run \<equiv> Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))"

lemma "partial_evaluation long_run is_zero_expr ZeroV = Some TrueV"
  by (simp add: is_zero_expr_def)

lemma "partial_evaluation long_run is_zero_expr (SuccV ZeroV) = Some FalseV"
  by (simp add: is_zero_expr_def)

lemma "partial_evaluation long_run is_zero_expr (SuccV (SuccV ZeroV)) = Some FalseV"
  by (simp add: is_zero_expr_def)

lemma "partial_evaluation long_run pred_expr ZeroV = Some ZeroV"
  by (simp add: pred_expr_def)

lemma "partial_evaluation long_run pred_expr (SuccV ZeroV) = Some ZeroV"
  by (simp add: pred_expr_def)

lemma "partial_evaluation long_run pred_expr (SuccV (SuccV ZeroV)) = Some (SuccV ZeroV)"
  by (simp add: pred_expr_def)

lemma "partial_evaluation long_run length\<^bsub>t\<^esub> (list_to_val t [a, b, c]) = 
    Some (nat_to_val (Suc (Suc (Suc 0))))"
  by (simp add: length_expr_def)

lemma "partial_evaluation long_run greater_than_expr (PairV (SuccV (SuccV ZeroV)) (SuccV ZeroV)) = Some TrueV"
  by (simp add: greater_than_expr_def greater_than_helper_def is_zero_expr_def pred_expr_def)

lemma "partial_evaluation long_run greater_than_expr (PairV (SuccV ZeroV) (SuccV (SuccV ZeroV))) = Some FalseV"
  by (simp add: greater_than_expr_def greater_than_helper_def is_zero_expr_def pred_expr_def)

end
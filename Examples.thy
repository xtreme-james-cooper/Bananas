theory Examples
imports DerivedCombinators PartialEvaluation
begin

definition length_expr :: "type \<Rightarrow> expr" ("length\<^bsub>_\<^esub>")where
  "length\<^bsub>t\<^esub> = \<lparr> \<kappa> ZeroV \<nabla> (succ \<cdot> \<pi>\<^sub>2) \<rparr>\<^bsub>ListF t\<^esub>"

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

lemma "partial_evaluation long_run length\<^bsub>t\<^esub> (list_to_val t [a, b, c]) = 
    Some (nat_to_val (Suc (Suc (Suc 0))))"
  by (simp add: length_expr_def)

end
theory Examples
imports DerivedCombinators PartialEvaluation Typechecking
begin

definition is_zero_expr :: expr where
  "is_zero_expr = \<epsilon> \<bar> \<kappa> UnitV \<cdot> \<prec>\<^bsub>NatF\<^esub>"

definition pred_expr :: expr where
  "pred_expr = \<kappa> ZeroV \<nabla> \<epsilon> \<cdot> \<prec>\<^bsub>NatF\<^esub>"

definition greater_than_helper :: expr where
  "greater_than_helper = 
      IF (Var ''is_zero'') \<cdot> \<pi>\<^sub>1 THEN \<iota>\<^sub>l \<cdot> \<kappa> FalseV 
      ELSE IF (Var ''is_zero'') \<cdot> \<pi>\<^sub>2 THEN \<iota>\<^sub>l \<cdot> \<kappa> TrueV 
      ELSE \<iota>\<^sub>r \<cdot> (Var ''pred'') \<parallel> (Var ''pred'')
      FI FI"

definition greater_than_expr :: expr where
  "greater_than_expr = \<lparr> \<Xi> \<rparr>\<^bsub>K Bool \<Oplus> Id\<^esub> \<cdot> \<lbrakk> Var ''greater_than_helper'' \<rbrakk>\<^bsub>K Bool \<Oplus> Id\<^esub>"

definition length_expr :: "type \<Rightarrow> expr" ("length\<^bsub>_\<^esub>") where
  "length\<^bsub>t\<^esub> = \<lparr> \<kappa> ZeroV \<nabla> (succ \<cdot> \<pi>\<^sub>2) \<rparr>\<^bsub>ListF t\<^esub>"

lemma "algorithmic_typecheck\<^sub>e Map.empty is_zero_expr = Some (Nat, Bool)"
  by (simp add: is_zero_expr_def Let_def)

lemma [simp]: "algorithmic_typecheck\<^sub>e Map.empty pred_expr = Some (Nat, Nat)"
  by (simp add: pred_expr_def Let_def)

lemma [simp]: "algorithmic_typecheck\<^sub>e [''is_zero'' \<mapsto> (Nat, Bool), ''pred'' \<mapsto> (Nat, Nat)] 
    greater_than_helper = Some (Nat \<otimes> Nat, Bool \<oplus> Nat \<otimes> Nat)"
  by (simp add: greater_than_helper_def Let_def)

lemma "algorithmic_typecheck\<^sub>e [''greater_than_helper'' \<mapsto> (Nat \<otimes> Nat, Bool \<oplus> Nat \<otimes> Nat)] 
    greater_than_expr = Some (Nat \<otimes> Nat, Bool)"
  by (simp add: greater_than_expr_def Let_def)

lemma "algorithmic_typecheck\<^sub>e Map.empty length\<^bsub>t\<^esub> = Some (List t, Nat)"
  by (simp add: length_expr_def)

primrec nat_to_val :: "nat \<Rightarrow> val" where
  "nat_to_val 0 = ZeroV"
| "nat_to_val (Suc n) = SuccV (nat_to_val n)"

primrec list_to_val :: "type \<Rightarrow> val list \<Rightarrow> val" where
  "list_to_val t [] = NilV t"
| "list_to_val t (v # vs) = ConsV t v (list_to_val t vs)"

abbreviation long_run :: nat where
  "long_run \<equiv> Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))"

lemma "partial_eval_prog long_run (Prog [] is_zero_expr ZeroV) = Some TrueV"
  by (simp add: is_zero_expr_def)

lemma "partial_eval_prog long_run (Prog [] is_zero_expr (SuccV ZeroV)) = Some FalseV"
  by (simp add: is_zero_expr_def)

lemma "partial_eval_prog long_run (Prog [] is_zero_expr (SuccV (SuccV ZeroV))) = Some FalseV"
  by (simp add: is_zero_expr_def)

lemma "partial_eval_prog long_run (Prog [] pred_expr ZeroV) = Some ZeroV"
  by (simp add: pred_expr_def)

lemma "partial_eval_prog long_run (Prog [] pred_expr (SuccV ZeroV)) = Some ZeroV"
  by (simp add: pred_expr_def)

lemma "partial_eval_prog long_run (Prog [] pred_expr (SuccV (SuccV ZeroV))) = Some (SuccV ZeroV)"
  by (simp add: pred_expr_def)

lemma "partial_eval_prog long_run (Prog [] length\<^bsub>t\<^esub> (list_to_val t [a, b, c])) = 
    Some (nat_to_val (Suc (Suc (Suc 0))))"
  by (simp add: length_expr_def)

abbreviation example_env :: "decl list" where
  "example_env \<equiv> [
    ExprDecl ''pred'' pred_expr,
    ExprDecl ''is_zero'' is_zero_expr,
    ExprDecl ''greater_than_helper'' greater_than_helper]"

lemma "partial_eval_prog long_run (Prog example_env greater_than_expr (PairV (SuccV (SuccV ZeroV)) (SuccV ZeroV))) = Some TrueV"
  by (simp add: greater_than_expr_def greater_than_helper_def is_zero_expr_def pred_expr_def)

lemma "partial_eval_prog long_run (Prog example_env greater_than_expr (PairV (SuccV ZeroV) (SuccV (SuccV ZeroV)))) = Some FalseV"
  by (simp add: greater_than_expr_def greater_than_helper_def is_zero_expr_def pred_expr_def)

end
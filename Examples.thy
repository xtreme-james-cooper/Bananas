theory Examples
imports DerivedCombinators PartialEvaluation Typechecking
begin

definition base_environment :: "decl list" where
  "base_environment = [
      TypeDecl ''Nat'' [(''Zero'', []), (''Succ'', [''Nat''])],
      ExprDecl ''is_zero'' (\<epsilon> \<bar> \<kappa> UnitV \<cdot> \<prec>\<^bsub>''Nat''\<^esub>),
      ExprDecl ''pred'' (\<kappa> (VarV ''Zero'') \<nabla> \<epsilon> \<cdot> \<prec>\<^bsub>''Nat''\<^esub>),
      ExprDecl ''greater_than_helper'' IF (Var ''is_zero'') \<cdot> \<pi>\<^sub>1 THEN \<iota>\<^sub>l \<cdot> \<kappa> FalseV 
                                       ELSE IF (Var ''is_zero'') \<cdot> \<pi>\<^sub>2 THEN \<iota>\<^sub>l \<cdot> \<kappa> TrueV 
                                       ELSE \<iota>\<^sub>r \<cdot> (Var ''pred'') \<parallel> (Var ''pred'')
                                       FI FI,
      TypeDecl ''GTHelper'' [(''Success'', [''Bool'']), (''Recurse'', [''GTHelper''])],
      ExprDecl ''greater_than'' (\<lparr> \<Xi> \<rparr>\<^bsub>''GTHelper''\<^esub> \<cdot> \<lbrakk> Var ''greater_than_helper'' \<rbrakk>\<^bsub>''GTHelper''\<^esub>)]"

primrec nat_to_val :: "nat \<Rightarrow> val" where
  "nat_to_val 0 = ZeroV"
| "nat_to_val (Suc n) = SuccV (nat_to_val n)"

abbreviation long_run :: nat where
  "long_run \<equiv> Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))"

lemma "partial_eval_prog long_run (Prog base_environment (Var ''greater_than_expr'') (PairV (SuccV (SuccV ZeroV)) (SuccV ZeroV))) = Some TrueV"
  by (simp add: greater_than_expr_def greater_than_helper_def is_zero_expr_def pred_expr_def)

lemma "partial_eval_prog long_run (Prog example_env greater_than_expr (PairV (SuccV ZeroV) (SuccV (SuccV ZeroV)))) = Some FalseV"
  by (simp add: greater_than_expr_def greater_than_helper_def is_zero_expr_def pred_expr_def)

end

(*
  type Bool = True | False
  type Nat = Zero | Succ Nat
  expr is_zero = \<kappa> True \<nabla> \<kappa> False . \<prec>\<^sub>N\<^sub>a\<^sub>t
  expr pred = \<kappa> Zero \<nabla> \<pi>\<^sub>1 \<nabla> \<kappa> Zero . \<prec>\<^sub>N\<^sub>a\<^sub>t
  expr gt_help = IF is_zero . \<pi>\<^sub>1 THEN \<iota>\<^sub>l . \<kappa> False ELSE IF is_zero . \<pi>\<^sub>2 THEN \<iota>\<^sub>l . \<kappa> True ELSE \<iota>\<^sub>r . pred \<parallel> pred
  type GTHelp = Success Bool | Recurse GTHelper
  expr greater_than = \<lparr> \<Xi> \<rparr>\<^sub>G\<^sub>T\<^sub>H\<^sub>e\<^sub>l\<^sub>p . \<lbrakk> gt_help \<rbrakk>\<^sub>G\<^sub>T\<^sub>H\<^sub>e\<^sub>l\<^sub>p

  greater_than (Succ (Succ (Succ Zero)), Succ (Succ Zero))

*)

val base_environment = [
      TypeDecl("Bool", [("True", []), ("False", [])]),
      TypeDecl("Nat", [("Zero", []), ("Succ", ["Nat"])]),
      ExprDecl("aaa", [Const TrueV]) (*
      ExprDecl("is_zero", Outj "Nat" :: case_strip [Const TrueV] [Const FalseV]),
      ExprDecl("pred", Outj "Nat" :: case_strip [Const UnitV, Var "Zero"] (case_strip [Proj1] [Const UnitV, Var "Zero"])),
      ExprDecl("greater_than_helper", if_expr [Proj1, Var "is_zero"] [Const FalseV, Injl]
                                      (if_expr [Proj2, Var "is_zero"] [Const TrueV, Injl]
                                      [Pairwise([Var "pred"], [Var "pred"]), Injr])),
      TypeDecl("GTHelper", [("Success", ["Bool"]), ("Recurse", ["GTHelper"])]),
      ExprDecl("greater_than", [Ana([Var "greater_than_helper"], "GTHelper"), Cata([Strip], "GTHelper")]) *)
]

val (SOME tc1) = typecheck_def empty_static (TypeDecl("Bool", [("True", []), ("False", [])]))
val (SOME tc2) = typecheck_def tc1 (TypeDecl("Nat", [("Zero", []), ("Succ", ["Nat"])]))
val tc3 = option_bind (unify' (#1 (assemble_constraints_expr tc2 (VAR 0) (VAR 1) 2 (Const (InjV("Bool", InlV UnitV)))))) (fn phi => 
            option_bind (inflate_type (subst_sub phi 0)) (fn t1 => 
              option_bind (inflate_type (subst_sub phi 1))  (fn t2 => SOME (t1, t2))))

(* val aa = #1 (assemble_constraints_exprs tc2 (VAR 0) (VAR 1) 2 (Const TrueV :: [])) *)

(* val example2 = partial_eval_prog (Prog(base_environment, [Const TrueV], UnitV)) *)

(* val example1 = partial_eval_prog (Prog(base_environment, [Var "is_zero"], InjV("Nat", InlV UnitV))) *)


(*
  type Bool = True | False

  type Nat = Zero | Succ Nat
  expr is_zero = \<kappa> True \<nabla> \<kappa> False . \<prec>\<^sub>N\<^sub>a\<^sub>t
  expr pred = \<kappa> Zero \<nabla> \<epsilon> . \<prec>\<^sub>N\<^sub>a\<^sub>t

  type GTHelp = Success Bool | Recurse GTHelper
  expr gt_help = IF is_zero . \<pi>\<^sub>1 THEN \<iota>\<^sub>l . \<kappa> False
                 ELSE IF is_zero . \<pi>\<^sub>2 THEN \<iota>\<^sub>l . \<kappa> True
                 ELSE \<iota>\<^sub>r . pred \<parallel> pred
  expr greater_than = \<lparr> \<Xi> \<rparr>\<^sub>G\<^sub>T\<^sub>H\<^sub>e\<^sub>l\<^sub>p . \<lbrakk> gt_help \<rbrakk>\<^sub>G\<^sub>T\<^sub>H\<^sub>e\<^sub>l\<^sub>p

  greater_than (Succ (Succ (Succ Zero)), Succ (Succ Zero))

*)

val base_environment = [
      TypeDecl("Bool", [("True", []), ("False", [])]),
      TypeDecl("Nat", [("Zero", []), ("Succ", ["Nat"])]),
      ExprDecl("is_zero", Outj "Nat" :: case_strip [Const (ValDesc("True", []))] [Const (ValDesc("False", []))]),
      ExprDecl("pred", Outj "Nat" :: case_strip [Const (ValDesc("Zero", []))] []),
      TypeDecl("GTHelper", [("Success", ["Bool"]), ("Recurse", ["GTHelper"])]),
      ExprDecl("greater_than_helper", if_expr [Proj1, Var "is_zero"] [Const (ValDesc("False", [])), Injl]
                                      (if_expr [Proj2, Var "is_zero"] [Const (ValDesc("True", [])), Injl]
                                      [Pairwise([Var "pred"], [Var "pred"]), Injr])),
      ExprDecl("greater_than", [Ana([Var "greater_than_helper"], "GTHelper"), Cata([Strip], "GTHelper")])
]

val (static, dynamic) = assemble_context empty_static empty_dynamic base_environment

val zero = ValDesc("Zero", [])
val one = ValDesc("Succ", [zero])
val two = ValDesc("Succ", [one])
val three = ValDesc("Succ", [two])
val four = ValDesc("Succ", [three])

val example1 = partial_eval_prog (Prog(base_environment, [Var "is_zero"], zero))
val example2 = partial_eval_prog (Prog(base_environment, [Var "is_zero"], one)) 
val example3 = partial_eval_prog (Prog(base_environment, [Var "pred"], zero))
val example4 = partial_eval_prog (Prog(base_environment, [Var "pred"], one))
val example5 = partial_eval_prog (Prog(base_environment, [Var "pred"], two))
val example6 = partial_eval_prog (Prog(base_environment, [Var "pred", Var "is_zero"], zero))
val example7 = partial_eval_prog (Prog(base_environment, [Var "pred", Var "is_zero"], one))
val example8 = partial_eval_prog (Prog(base_environment, [Var "pred", Var "is_zero"], two))
val example9 = partial_eval_prog (Prog(base_environment, tuple_pair [Const three] [Const four] @ [Var "greater_than"], zero))
val example10 = partial_eval_prog (Prog(base_environment, tuple_pair [Const four] [Const three] @ [Var "greater_than"], zero))
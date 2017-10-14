
(* example program in real syntax:
  type Bool = True | False

  type Nat = Zero | Succ Nat
  expr is_zero = \<kappa> True \<nabla> \<kappa> False . \<prec>\<^sub>N\<^sub>a\<^sub>t
  expr pred = \<kappa> Zero \<nabla> \<epsilon> . \<prec>\<^sub>N\<^sub>a\<^sub>t

  type GTHelp = Success Bool | Recurse GTHelper
  expr gt_help = (\<iota>\<^sub>l . \<kappa> False) \<lhd> is_zero . \<pi>\<^sub>1 \<rhd> ((\<iota>\<^sub>l . \<kappa> True) \<lhd> is_zero . \<pi>\<^sub>2 \<rhd> (\<iota>\<^sub>r . pred \<parallel> pred))
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
      ExprDecl("greater_than", [Ana([Var "greater_than_helper"], "GTHelper"), Cata([Strip], "GTHelper")]),
      TypeDecl("List", [("Nil", []), ("Cons", ["Nat", "List"])]),
      TypeDecl("Tree", [("Leaf", []), ("Branch", ["Tree", "Nat", "Tree"])])
]

val (static, dynamic) = assemble_context empty_static empty_dynamic base_environment

val zero = ValDesc("Zero", [])
val one = ValDesc("Succ", [zero])
val two = ValDesc("Succ", [one])
val three = ValDesc("Succ", [two])
val four = ValDesc("Succ", [three])

val example1 = eval_prog (Prog(base_environment, tuple_pair [Const three] [Const four] @ [Var "greater_than"], zero))
val example2 = eval_prog (Prog(base_environment, tuple_pair [Const four] [Const three] @ [Var "greater_than"], zero))
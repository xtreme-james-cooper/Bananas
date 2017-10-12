
val base_environment = [
      TypeDecl("Nat", [("Zero", []), ("Succ", ["Nat"])]),
      ExprDecl("is_zero", Outj "Nat" :: case_strip [Const TrueV] [Const FalseV])
(*      ExprDecl("pred", (Comp(case_strip (Const (VarV "Zero")) Identity, Outj "Nat"))),
      ExprDecl("greater_than_helper", if_expr (Comp(Var "is_zero", Proj1)) (Comp(Injl, Const FalseV)) (
                                      if_expr (Comp(Var "is_zero", Proj2)) (Comp(Injl, Const TrueV)) (
                                      (Comp(Injr, Pairwise(Var "pred", Var "pred")))))),
      TypeDecl("GTHelper", [("Success", ["Bool"]), ("Recurse", ["GTHelper"])]),
      ExprDecl("greater_than", (Comp(Cata(Strip, "GTHelper"), Ana(Var "greater_than_helper", "GTHelper")))) *)
]

val example1 = partial_eval_prog (Prog(base_environment, [Var "is_zero"], InjV("Nat", InlV UnitV)))
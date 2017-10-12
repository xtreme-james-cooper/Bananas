
val base_environment = [
      TypeDecl("Nat", [("Zero", []), ("Succ", ["Nat"])]),
      ExprDecl("is_zero", (Comp(Case(Identity, Const UnitV), Outj "Nat")))
(*      ExprDecl("pred", (Comp(case_strip (Const (VarV "Zero")) Identity, Outj "Nat"))),
      ExprDecl("greater_than_helper", if_expr (Comp(Var "is_zero", Proj1)) (Comp(Injl, Const FalseV)) (
                                      if_expr (Comp(Var "is_zero", Proj2)) (Comp(Injl, Const TrueV)) (
                                      (Comp(Injr, Pairwise(Var "pred", Var "pred")))))),
      TypeDecl("GTHelper", [("Success", ["Bool"]), ("Recurse", ["GTHelper"])]),
      ExprDecl("greater_than", (Comp(Cata(Strip, "GTHelper"), Ana(Var "greater_than_helper", "GTHelper")))) *)
]

(*
partial_eval_prog (Prog(base_environment, Var "greater_than_expr", PairV (SuccV (SuccV ZeroV)) (SuccV ZeroV)))
partial_eval_prog (Prog base_environment (Var "greater_than_expr") (PairV (SuccV ZeroV) (SuccV (SuccV ZeroV))))
*)

val example1 = partial_eval_prog (Prog(base_environment, Var "is_zero", InjV("Nat", InlV UnitV)))
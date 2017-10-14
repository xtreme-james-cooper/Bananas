
(* example program in real syntax:
  type Bool = True | False

  type Nat = Zero | Succ Nat
  expr is_zero = \<kappa> True \<nabla> \<kappa> False . \<prec>\<^sub>N\<^sub>a\<^sub>t
  expr pred = \<kappa> Zero \<nabla> \<epsilon> . \<prec>\<^sub>N\<^sub>a\<^sub>t

  type GTHelp = Success Bool | Recurse GTHelper
  expr gt_help = (\<iota>\<^sub>l . \<kappa> False) \<lhd> is_zero . \<pi>\<^sub>1 \<rhd> ((\<iota>\<^sub>l . \<kappa> True) \<lhd> is_zero . \<pi>\<^sub>2 \<rhd> (\<iota>\<^sub>r . pred \<parallel> pred))
  expr greater_than = \<lparr> \<Xi> \<rparr>\<^sub>G\<^sub>T\<^sub>H\<^sub>e\<^sub>l\<^sub>p . \<lbrakk> gt_help \<rbrakk>\<^sub>G\<^sub>T\<^sub>H\<^sub>e\<^sub>l\<^sub>p

  val one = Succ Zero
  val two = Succ one
  val three = Succ two
  val four = Succ three

  type List = Nil | Cons Nat List

  greater_than . \<kappa> three \<triangle> \<kappa> four

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

      ValDecl("one", ValDesc("Succ", [ValDesc("Zero", [])])),
      ValDecl("two", ValDesc("Succ", [ValDesc("one", [])])),
      ValDecl("three", ValDesc("Succ", [ValDesc("two", [])])),
      ValDecl("four", ValDesc("Succ", [ValDesc("three", [])])),

      TypeDecl("List", [("Nil", []), ("Cons", ["Nat", "List"])]),

      ExprDecl("insert_helper_cons", if_expr [Pairwise([Proj1], []), Var "greater_than"] 
                                             (Pairwise(swap @ [Apply], []) :: swap @ [Var "Cons"])
                                             (assoc_left @ [Pairwise([], [Apply]), Var "Cons"])),
      ExprDecl("a", [Curry [Var "insert_helper_cons"]]),
      ExprDecl("b", [Fun (Var "Cons" :: tuple_pair [] [Const (ValDesc("Nil", []))])])
 (*
      ExprDecl("insert_helper", case_strip [Fun (Var "Cons" :: tuple_pair [] [Const (ValDesc("Nil", []))])] 
                                           [Curry [Var "insert_helper_cons"]])
      ExprDecl("insert", [Cata([Var "insert_helper"], "List")]) *)

]

val (static, dynamic) = assemble_context empty_static empty_dynamic base_environment

fun typ_to_string Void = "0"
  | typ_to_string Unit = "1"
  | typ_to_string (Poly x) = "?" ^ Int.toString x
  | typ_to_string (Prod(t1, t2)) = "(" ^ typ_to_string t1 ^ " * " ^ typ_to_string t2 ^ ")"
  | typ_to_string (Sum(t1, t2)) = "(" ^ typ_to_string t1 ^ " + " ^ typ_to_string t2 ^ ")"
  | typ_to_string (Func(t1, t2)) = "(" ^ typ_to_string t1 ^ " => " ^ typ_to_string t2 ^ ")"
  | typ_to_string (Fix F) = "Mu " ^ funct_to_string F
and funct_to_string Id = "Id"
  | funct_to_string (K t) = "K " ^ typ_to_string t
  | funct_to_string (ProdF(f1, f2)) = "(" ^ funct_to_string f1 ^ " * " ^ funct_to_string f2 ^ ")"
  | funct_to_string (SumF(f1, f2)) = "(" ^ funct_to_string f1 ^ " + " ^ funct_to_string f2 ^ ")"

val (a, b) = var_e_type static "a"
val a' = typ_to_string a
val b' = typ_to_string b

val example1 = eval_prog (Prog(base_environment, tuple_pair [Const (ValDesc("three", []))] [Const (ValDesc("four", []))] @ [Var "greater_than"], ValDesc("Zero", [])))
val example2 = eval_prog (Prog(base_environment, tuple_pair [Const (ValDesc("four", []))] [Const (ValDesc("three", []))] @ [Var "greater_than"], ValDesc("Zero", [])))
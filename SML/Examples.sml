
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

  val testlist = Cons three (Cons four (Cons two (Cons one Nil)))

  expr insert_helper_cons = (Cons . \<bowtie> . ($ . \<bowtie>) \<parallel> \<epsilon>) \<triangleleft> greater_than . \<pi>\<^sub>1 \<parallel> \<epsilon> \<triangleright> (Cons . \<epsilon> \<parallel> $ . \<supset>)
  expr insert_helper = \<langle> Cons . \<epsilon> \<triangle> \<kappa> Nil \<rangle> \<nabla> (\<sharp> insert_helper_cons)
  expr insert = $ . \<bowtie> . \<epsilon> \<parallel> \<lparr> insert_helper \<rparr>\<^sub>L\<^sub>i\<^sub>s\<^sub>t
  expr sort = \<lparr> (\<succ>\<^sub>L\<^sub>i\<^sub>s\<^sub>t . \<iota>\<^sub>l) \<nabla> insert \<rparr>\<^sub>L\<^sub>i\<^sub>s\<^sub>t

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

      ValDecl("testlist", ValDesc("Cons", [ValDesc("three", []), 
                          ValDesc("Cons", [ValDesc("four", []), 
                          ValDesc("Cons", [ValDesc("two", []), 
                          ValDesc("Cons", [ValDesc("one", []), ValDesc("Nil", [])])])])])),

      ExprDecl("insert_helper_cons", if_expr [Pairwise([Proj1], []), Var "greater_than"] 
                                             (Pairwise(swap @ [Apply], []) :: swap @ [Var "Cons"])
                                             (assoc_left @ [Pairwise([], [Apply]), Var "Cons"])),
      ExprDecl("insert_helper", case_strip [Fun (tuple_pair [] [Const (ValDesc("Nil", []))] @ [Var "Cons"])] 
                                           [Curry [Var "insert_helper_cons"]]),
      ExprDecl("insert", (Pairwise([], [Cata([Var "insert_helper"], "List")]) :: swap @ [Apply])),

      ExprDecl("sort", [Cata(case_strip [Injl, Inj "List"] [Var "insert"], "List")])
]

val (static, dynamic) = assemble_context empty_static empty_dynamic base_environment

val a = typ_to_string (#1 (var_e_type static "sort")) ^ "--->" ^ typ_to_string (#2 (var_e_type static "sort"))
val b = expr_to_string (var_e_bind dynamic) (Var "sort")

val example1 = [Const (ValDesc("testlist", [])), Var "sort"]

val c = val_to_string (var_e_bind dynamic) (eval_prog (Prog(base_environment, example1, ValDesc("Zero", []))))
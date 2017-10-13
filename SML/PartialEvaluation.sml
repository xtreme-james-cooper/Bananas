
exception CannotEval of expr * vall

type dynamic_environment = {
  var_e_bind: name -> expr list,
  var_t_bind: name -> funct
}

val empty_dynamic = { 
      var_e_bind = fn x => raise MissingExpr x, 
      var_t_bind = fn x => raise MissingType x }

fun extend_e_dynamic x e (lam: dynamic_environment) = { 
    var_e_bind = fn y => if x = y then e else #var_e_bind lam y,
    var_t_bind = #var_t_bind lam }

fun extend_t_dynamic x t (gamma: dynamic_environment) = { 
    var_e_bind = #var_e_bind gamma,
    var_t_bind = fn y => if x = y then t else #var_t_bind gamma y }

fun combine_dynamic (lam1: dynamic_environment) (lam2: dynamic_environment) = { 
    var_e_bind = fn x => 
      #var_e_bind lam1 x handle (MissingExpr _) => #var_e_bind lam2 x, 
    var_t_bind = fn x => 
      #var_t_bind lam1 x handle (MissingType _) => #var_t_bind lam2 x }

fun apply_functor_expr e Id = [e]
  | apply_functor_expr _ (K _) = []
  | apply_functor_expr e (ProdF(f1, f2)) = [Pairwise (apply_functor_expr e f1, apply_functor_expr e f2)]
  | apply_functor_expr e (SumF(f1, f2)) = [Case (apply_functor_expr e f1, apply_functor_expr e f2)]

fun partial_evaluation _ (Const v1) _ = v1
  | partial_evaluation _ Proj1 (PairV(v1, _)) = v1
  | partial_evaluation _ Proj1 v = raise CannotEval(Proj1, v)
  | partial_evaluation _ Proj2 (PairV(_, v2)) = v2
  | partial_evaluation _ Proj2 v = raise CannotEval(Proj2, v)
  | partial_evaluation lam (Pairwise(f1, f2)) (PairV(v1, v2)) = 
      PairV(partial_eval lam f1 v1, partial_eval lam f2 v2)
  | partial_evaluation _ (Pairwise(f1, f2)) v = raise CannotEval(Pairwise(f1, f2), v)
  | partial_evaluation _ Duplicate v = PairV(v, v)
  | partial_evaluation _ Injl v = InlV v
  | partial_evaluation _ Injr v = InrV v
  | partial_evaluation _ Strip (InlV v) = v
  | partial_evaluation _ Strip (InrV v) = v
  | partial_evaluation _ Strip v = raise CannotEval(Strip, v)
  | partial_evaluation lam (Case(fl, _)) (InlV v) = partial_eval lam (fl @ [Injl]) v
  | partial_evaluation lam (Case(_, fr)) (InrV v) = partial_eval lam (fr @ [Injr]) v
  | partial_evaluation _ (Case(fl, fr)) v = raise CannotEval(Case(fl, fr), v)
  | partial_evaluation _ Distribute (PairV (InlV v1, v2)) = InlV (PairV(v1, v2))
  | partial_evaluation _ Distribute (PairV (InrV v1, v2)) = InrV (PairV(v1, v2))
  | partial_evaluation _ Distribute v = raise CannotEval(Distribute, v)
  | partial_evaluation lam Apply (PairV(FunV e, v)) = partial_eval lam e v
  | partial_evaluation _ Apply v = raise CannotEval(Apply, v)
  | partial_evaluation _ (Arrow(g, f)) (FunV e) = FunV (g @ e @ f)
  | partial_evaluation _ (Arrow(g, f)) v = raise CannotEval(Arrow(g, f), v)
  | partial_evaluation _ (Inj x) v = InjV(x, v)
  | partial_evaluation _ (Outj _) (InjV(_, v)) = v
  | partial_evaluation _ (Outj n) v = raise CannotEval(Outj n, v)
  | partial_evaluation lam (Cata(f, x)) v = 
      partial_eval lam (Outj x :: apply_functor_expr (Cata(f, x)) (#var_t_bind lam x) @ f) v
  | partial_evaluation lam (Ana(f, x)) v = 
      partial_eval lam (f @ apply_functor_expr (Ana(f, x)) (#var_t_bind lam x) @ [Inj x]) v
  | partial_evaluation lam (Var x) v = partial_eval lam (#var_e_bind lam x) v 
and partial_eval _ [] v = v
  | partial_eval lam (f :: g) v = partial_eval lam g (partial_evaluation lam f v)

fun right_inject 0 = [Injl]
  | right_inject x = right_inject (x - 1) @ [Injr]

fun assemble_context_ctor_expr _ _     []              y = raise MissingExpr y
  | assemble_context_ctor_expr n depth ((x, _) :: cts) y = 
      if y = x then right_inject depth @ [Inj n]
      else assemble_context_ctor_expr n (depth + 1) cts y

fun assemble_context' gamma (TypeDecl(x, cts)) = {
      var_e_bind = assemble_context_ctor_expr x 0 cts, 
      var_t_bind = fn y => if x = y then typecheck_ctors gamma x cts else raise MissingExpr y } 
  | assemble_context' _ (ExprDecl(x, e)) = { 
      var_e_bind = fn y => if x = y then e else raise MissingExpr y, 
      var_t_bind = fn y => raise MissingType y }

fun assemble_context gam lam [] = (gam, lam)
  | assemble_context gam lam (del :: dels) = 
      assemble_context (typecheck_def gam del) (combine_dynamic (assemble_context' gam del) lam) dels

fun partial_eval_prog (Prog(lam, e, v)) = 
      partial_eval (#2 (assemble_context empty_static empty_dynamic lam)) e v

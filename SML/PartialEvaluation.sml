

type dynamic_environment = {
  var_e_bind: name -> expr option,
  var_t_bind: name -> funct option
}

val empty_dynamic = { var_e_bind = fn _ => NONE, var_t_bind = fn _ => NONE }

fun extend_e_dynamic x t (lam: dynamic_environment) = { 
    var_e_bind = fn y => if x = y then SOME t else #var_e_bind lam y,
    var_t_bind = #var_t_bind lam }

fun combine_dynamic (lam1: dynamic_environment) (lam2: dynamic_environment) = { 
    var_e_bind = fn x => 
      case #var_e_bind lam1 x of NONE => #var_e_bind lam2 x | SOME e => SOME e, 
    var_t_bind = fn x => 
      case #var_t_bind lam1 x of NONE => #var_t_bind lam2 x | SOME t => SOME t }

fun apply_functor_expr e Id = e
  | apply_functor_expr _ (K _) = Identity
  | apply_functor_expr e (ProdF(f1, f2)) = Pairwise (apply_functor_expr e f1, apply_functor_expr e f2)
  | apply_functor_expr e (SumF(f1, f2)) = Case (apply_functor_expr e f1, apply_functor_expr e f2)

fun partial_evaluation _ Identity v = SOME v
  | partial_evaluation _ (Const v1) _ = SOME v1
  | partial_evaluation lam (Comp(f, g)) v = (case partial_evaluation lam g v of 
      SOME v' => partial_evaluation lam f v'
    | NONE => NONE)
  | partial_evaluation _ Proj1 (PairV(v1, _)) = SOME v1
  | partial_evaluation _ Proj1 _ = NONE
  | partial_evaluation _ Proj2 (PairV(_, v2)) = SOME v2
  | partial_evaluation _ Proj2 _ = NONE
  | partial_evaluation lam (Pairwise(f1, f2)) (PairV(v1, v2)) = (case partial_evaluation lam f1 v1 of 
        SOME v1' => (case partial_evaluation lam f2 v2 of 
            SOME v2' => SOME (PairV(v1', v2'))
          | NONE => NONE)
      | NONE => NONE)
  | partial_evaluation _ (Pairwise(_, _)) _ = NONE
  | partial_evaluation _ Duplicate v = SOME (PairV(v, v))
  | partial_evaluation _ Injl v = SOME (InlV v)
  | partial_evaluation _ Injr v = SOME (InrV v)
  | partial_evaluation _ Strip (InlV v) = SOME v
  | partial_evaluation _ Strip (InrV v) = SOME v
  | partial_evaluation _ Strip _ = NONE
  | partial_evaluation lam (Case(fl, _)) (InlV v) = partial_evaluation lam (Comp(Injl, fl)) v
  | partial_evaluation lam (Case(_, fr)) (InrV v) = partial_evaluation lam (Comp(Injr, fr)) v
  | partial_evaluation _ (Case(_, _)) _ = NONE
  | partial_evaluation _ Distribute (PairV (InlV v1, v2)) = SOME (InlV (PairV(v1, v2)))
  | partial_evaluation _ Distribute (PairV (InrV v1, v2)) = SOME (InrV (PairV(v1, v2)))
  | partial_evaluation _ Distribute _ = NONE
  | partial_evaluation lam Apply (PairV(FunV e, v)) = partial_evaluation lam e v
  | partial_evaluation _ Apply _ = NONE
  | partial_evaluation _ (Arrow(g, f)) (FunV e) = SOME (FunV (Comp(g, Comp(e, f))))
  | partial_evaluation _ (Arrow(_, _)) _ = NONE
  | partial_evaluation _ (Inj x) v = SOME (InjV(x, v))
  | partial_evaluation _ (Outj _) (InjV(_, v)) = SOME v
  | partial_evaluation _ (Outj _) _ = NONE
  | partial_evaluation lam (Cata(f, x)) v = (case #var_t_bind lam x of 
        SOME F => partial_evaluation lam (Comp(f, Comp(apply_functor_expr (Cata(f, x)) F, Outj x))) v
      | NONE => NONE)
  | partial_evaluation lam (Ana(f, x)) v = (case #var_t_bind lam x of 
        SOME F => partial_evaluation lam (Comp(Inj x, Comp(apply_functor_expr (Ana(f, x)) F, f))) v
      | NONE => NONE)
  | partial_evaluation lam (Var x) v = (case #var_e_bind lam x of 
        SOME e => partial_evaluation lam e v 
      | NONE => NONE)

fun right_inject 0 = Injl
  | right_inject x = Comp(Injr, right_inject (x - 1))

fun assemble_context_ctor_expr _ _     []              _ = NONE
  | assemble_context_ctor_expr n depth ((x, _) :: cts) y = 
      if y = x then SOME (Comp(Inj n, right_inject depth))
      else assemble_context_ctor_expr n (depth + 1) cts y

fun assemble_context' gamma (TypeDecl(x, cts)) = {
      var_e_bind = assemble_context_ctor_expr x 0 cts, 
      var_t_bind = fn y => if x = y then typecheck_ctors gamma x cts else NONE } 
  | assemble_context' _ (ExprDecl(x, e)) = { 
      var_e_bind = fn y => if x = y then SOME e else NONE, 
      var_t_bind = fn _ => NONE }

fun assemble_context [] = (empty_static, empty_dynamic)
  | assemble_context (del :: lam) = 
      let val (gam, lam) = assemble_context lam
      in (valOf (typecheck_def gam del), combine_dynamic (assemble_context' gam del) lam)
      end

fun partial_eval_prog (Prog(lam, e, v)) = partial_evaluation (#2 (assemble_context lam)) e v

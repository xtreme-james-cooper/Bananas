
exception CannotEval of expr * vall

(* evaluate a variableDesc *)
fun eval_v (lam: dynamic_environment) (ValDesc(n, vs)) = 
      var_v_bind lam n (map (eval_v lam) vs)

(* evaluate an expr applied to a value, in a dynamic environment *)
fun eval lam (Const v1)         _                    = eval_v lam v1
  | eval _   (ConstV v)         _                    = v
  | eval _   Proj1              (PairV(v1, _))       = v1
  | eval _   Proj2              (PairV(_, v2))       = v2
  | eval lam (Pairwise(f1, f2)) (PairV(v1, v2))      = PairV(evals lam f1 v1, evals lam f2 v2)
  | eval _   Duplicate          v                    = PairV(v, v)
  | eval _   Injl               v                    = InlV v
  | eval _   Injr               v                    = InrV v
  | eval _   Strip              (InlV v)             = v
  | eval _   Strip              (InrV v)             = v
  | eval lam (Case(fl, _))      (InlV v)             = evals lam (fl @ [Injl]) v
  | eval lam (Case(_, fr))      (InrV v)             = evals lam (fr @ [Injr]) v
  | eval _   Distribute         (PairV(InlV v1, v2)) = InlV (PairV(v1, v2))
  | eval _   Distribute         (PairV(InrV v1, v2)) = InrV (PairV(v1, v2))
  | eval lam Apply              (PairV(FunV e, v))   = evals lam e v
  | eval _   (Fun f)            _                    = FunV f
  | eval _   (Arrow(g, f))      (FunV e)             = FunV (g @ e @ f)
  | eval _   (Curry f)          v                    = 
      FunV (Duplicate :: Pairwise([ConstV v], []) :: f)
  | eval lam (Uncurry f)        (PairV(v1, v2))      =
      evals lam [Pairwise([Apply], []), Apply] (PairV(PairV(FunV f, v1), v2))
  | eval _   (Inj x)            v                    = InjV(x, v)
  | eval _   (Outj _)           (InjV(_, v))         = v
  | eval lam (Cata(f, x))       v                    = 
      evals lam (Outj x :: apply_functor_expr (Cata(f, x)) (var_t_bind lam x) @ f) v
  | eval lam (Ana(f, x))        v                    = 
      evals lam (f @ apply_functor_expr (Ana(f, x)) (var_t_bind lam x) @ [Inj x]) v
  | eval lam (Var x)            v                    = evals lam (var_e_bind lam x) v 
  | eval _   e                  v                    = raise CannotEval(e, v)
and evals _   []       v = v
  | evals lam (f :: g) v = evals lam g (eval lam f v)

(* the (uninjected) expression form of a constructor 
   nothing if the last constructor
   left and right injections every time there's more than one remaining *)
fun assemble_context_ctor_expr [] = raise Empty 
  | assemble_context_ctor_expr [(x, _)] = [(x, [])]
  | assemble_context_ctor_expr ((x, _) :: cts) = 
      (x, [Injl]) :: map (fn (x, e) => (x, e @ [Injr])) (assemble_context_ctor_expr cts)

(* the (uninjected) value form of a constructor 
   nothing if the last constructor
   left and right injections every time there's more than one remaining *)
fun assemble_context_ctor_val [] = raise Empty 
  | assemble_context_ctor_val [(x, _)] = 
      [(x, fn vs => if length vs = 0 then UnitV else foldr1 PairV vs)]
  | assemble_context_ctor_val ((x, _) :: cts) = 
      (x, fn vs => InlV (if length vs = 0 then UnitV else foldr1 PairV vs)) :: 
        map (fn (x, v) => (x, InrV o v)) (assemble_context_ctor_val cts)

(* create the dynamic environment from a declaration 
    types are much more involved than expressions *)
fun assemble_context' gamma _ (TypeDecl(x, cts)) = {
      var_e_bind = map (fn (n, e) => (n, e @ [Inj x])) (assemble_context_ctor_expr cts), 
      var_v_bind = map (fn (n, v) => (n, fn vs => InjV(x, v vs))) (assemble_context_ctor_val cts),
      var_t_bind = [(x, typecheck_ctors gamma x cts)] } 
  | assemble_context' _ lam (ValDecl(x, v)) = 
      extend_v_dynamic x (fn _ => eval_v lam v) empty_dynamic
  | assemble_context' _ _ (ExprDecl(x, e)) = extend_e_dynamic x e empty_dynamic

(* create the dynamic environment from a declaration list *)
fun assemble_context gam lam [] = (gam, lam)
  | assemble_context gam lam (del :: dels) = 
      assemble_context (typecheck_def gam del) (combine_dynamic (assemble_context' gam lam del) lam) dels

(* evaluate a program *) 
fun eval_prog (Prog(del, e, v)) = 
      let val lam = #2 (assemble_context empty_static empty_dynamic del)
      in evals lam e (eval_v lam v)
      end

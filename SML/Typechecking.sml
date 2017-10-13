
exception MissingType of name
exception MissingExpr of name

type static_environment = {
  var_e_type : name -> (typ * typ),
  var_t_type : name -> funct
}

val empty_static = { 
      var_e_type = fn x => raise MissingExpr x, 
      var_t_type = fn x => raise MissingType x }

fun extend_e_static x t (gamma: static_environment) = { 
    var_e_type = fn y => if x = y then t else #var_e_type gamma y,
    var_t_type = #var_t_type gamma }

fun extend_t_static x t (gamma: static_environment) = { 
    var_e_type = #var_e_type gamma,
    var_t_type = fn y => if x = y then t else #var_t_type gamma y }

fun combine_static (gamma1: static_environment) (gamma2: static_environment) = { 
    var_e_type = fn x => 
      #var_e_type gamma1 x handle (MissingExpr _) => #var_e_type gamma2 x, 
    var_t_type = fn x => 
      #var_t_type gamma1 x handle (MissingType _) => #var_t_type gamma2 x }

fun apply_functor_type t Id = t
  | apply_functor_type _ (K t') = t'
  | apply_functor_type t (ProdF(f1, f2)) = Prod(apply_functor_type t f1, apply_functor_type t f2)
  | apply_functor_type t (SumF(f1, f2)) = Sum(apply_functor_type t f1, apply_functor_type t f2)

datatype flat_type = UNIT | VOID | TIMES | PLUS | ARROW | MU | IDF | CONSTF | TIMESF | PLUSF

fun flatten_type Unit           = CON(UNIT, []) 
  | flatten_type Void           = CON(VOID, [])
  | flatten_type (Poly n)       = VAR n
  | flatten_type (Prod(t1, t2)) = CON(TIMES, [flatten_type t1, flatten_type t2])
  | flatten_type (Sum(t1, t2))  = CON(PLUS, [flatten_type t1, flatten_type t2])
  | flatten_type (Func(t1, t2)) = CON(ARROW, [flatten_type t1, flatten_type t2])
  | flatten_type (Fix F)        = CON(MU, [flatten_funct F])

and flatten_funct Id              = CON(IDF, [])
  | flatten_funct (K t)           = CON(CONSTF, [flatten_type t])
  | flatten_funct (ProdF(f1, f2)) = CON(TIMESF, [flatten_funct f1, flatten_funct f2])
  | flatten_funct (SumF(f1, f2))  = CON(PLUSF, [flatten_funct f1, flatten_funct f2])

fun apply_functor_flat t Id              = t
  | apply_functor_flat _ (K t')          = flatten_type t'
  | apply_functor_flat t (ProdF(f1, f2)) = 
      CON(TIMES, [apply_functor_flat t f1, apply_functor_flat t f2])
  | apply_functor_flat t (SumF(f1, f2))  = 
      CON(PLUS, [apply_functor_flat t f1, apply_functor_flat t f2])

exception TypeInflationError of flat_type expression
exception UnificationError of (flat_type equation) list

fun inflate_type (VAR x) = Poly x
  | inflate_type (CON(UNIT, [])) = Unit
  | inflate_type (CON(VOID, [])) = Void
  | inflate_type (CON(MU, [F])) = Fix (inflate_funct F) 
  | inflate_type (CON(TIMES, [t1, t2])) = Prod(inflate_type t1, inflate_type t2)
  | inflate_type (CON(PLUS, [t1, t2])) = Sum(inflate_type t1, inflate_type t2)
  | inflate_type (CON(ARROW, [t1, t2])) = Func(inflate_type t1, inflate_type t2) 
  | inflate_type ft = raise TypeInflationError ft

and inflate_funct (CON(IDF, [])) = Id
  | inflate_funct (CON(CONSTF, [t])) = K (inflate_type t) 
  | inflate_funct (CON(TIMESF, [f1, f2])) = ProdF(inflate_funct f1, inflate_funct f2)
  | inflate_funct (CON(PLUSF, [f1, f2])) = SumF(inflate_funct f1, inflate_funct f2)
  | inflate_funct ft = raise TypeInflationError ft

fun assemble_constraints_expr gamma _ y free (Const v) = assemble_constraints_val gamma y free v
  | assemble_constraints_expr _ x y free Proj1 = ([(x, CON(TIMES, [y, VAR free]))], free + 1)
  | assemble_constraints_expr _ x y free Proj2 = ([(x, CON(TIMES, [VAR free, y]))], free + 1)
  | assemble_constraints_expr _ x y free Duplicate = ([(y, CON (TIMES, [x, x]))], free)
  | assemble_constraints_expr gamma x y free (Pairwise(f1, f2)) = 
      let val a = VAR free
          val b = VAR (free + 1) 
          val (cs1, free') = assemble_constraints_exprs gamma a b (free + 2) f1
          val c = VAR free'
          val d = VAR (free' + 1) 
          val (cs2, free'') = assemble_constraints_exprs gamma c d (free' + 2) f2
      in ((x, CON(TIMES, [a, c])) :: (y, CON(TIMES, [b, d])) :: cs1 @ cs2, free'') 
      end
  | assemble_constraints_expr _ x y free Injl = ([(y, CON(PLUS, [x, VAR free]))], free + 1)
  | assemble_constraints_expr _ x y free Injr = ([(y, CON(PLUS, [VAR free, x]))], free + 1)
  | assemble_constraints_expr _ x y free Strip = ([(x, CON(PLUS, [y, y]))], free)
  | assemble_constraints_expr gamma x y free (Case (f1, f2)) =
      let val a = VAR free
          val b = VAR (free + 1) 
          val (cs1, free') = assemble_constraints_exprs gamma a b (free + 2) f1
          val c = VAR free' 
          val d = VAR (free' + 1) 
          val (cs2, free'') = assemble_constraints_exprs gamma c d (free' + 2) f2
      in ((x, CON(PLUS, [a, c])) :: (y, CON(PLUS, [b, d])) :: cs1 @ cs2, free'')
      end
  | assemble_constraints_expr _ x y free Distribute = 
      let val a = VAR free
          val b = VAR (free + 1)
          val c = VAR (free + 2)
      in ([(x, CON(TIMES, [CON(PLUS, [a, b]), c])), 
           (y, CON(PLUS, [CON(TIMES, [a, c]), CON(TIMES, [b, c])]))], free + 3)
      end
  | assemble_constraints_expr _ x y free Apply = 
      ([(x, CON(TIMES, [CON(ARROW, [VAR free, y]), VAR free]))], free + 1)
  | assemble_constraints_expr gamma x y free (Arrow (f1, f2)) =
      let val a = VAR free
          val b = VAR (free + 1) 
          val (cs1, free') = assemble_constraints_exprs gamma a b (free + 1) f1
          val c = VAR free' 
          val d = VAR (free' + 1) 
          val (cs2, free'') = assemble_constraints_exprs gamma c d (free' + 2) f2
      in ((x, CON(ARROW, [b, c])) :: (y, CON(PLUS, [a, d])) :: cs1 @ cs2, free'')
      end
  | assemble_constraints_expr gamma x y free (Inj n) = 
      let val F = #var_t_type gamma n
      in ([(x, flatten_type (apply_functor_type (Fix F) F)), (y, flatten_type (Fix F))], free)
      end
  | assemble_constraints_expr gamma x y free (Outj n) = 
      let val F = #var_t_type gamma n 
      in ([(x, flatten_type (Fix F)), (y, flatten_type (apply_functor_type (Fix F) F))], free)
      end
  | assemble_constraints_expr gamma x y free (Cata(f, n)) =
      let val F = #var_t_type gamma n
          val (cs, free') = assemble_constraints_exprs gamma (apply_functor_flat y F) y free f
      in ((x, CON(MU, [flatten_funct F])) :: cs, free')
      end
  | assemble_constraints_expr gamma x y free (Ana(f, n)) =
      let val F = #var_t_type gamma n
          val (cs, free') = assemble_constraints_exprs gamma x (apply_functor_flat x F) free f
      in ((y, CON(MU, [flatten_funct F])) :: cs, free')
      end
  | assemble_constraints_expr gamma x y free (Var z) = 
      let val (t1, t2) = #var_e_type gamma z
      in ([(x, flatten_type t1), (y, flatten_type t2)], free)
      end

and assemble_constraints_exprs (_: static_environment) x y free [] = ([(x, y)], free)
  | assemble_constraints_exprs gamma x y free (f1 :: f2) =
      let val (cs1, free') = assemble_constraints_expr gamma x (VAR free) (free + 1) f1
          val (cs2, free'') = assemble_constraints_exprs gamma (VAR free) y free' f2
      in (cs1 @ cs2, free'') 
      end

and assemble_constraints_val _     x free UnitV = 
      ([(x, CON(UNIT, []))], free)
  | assemble_constraints_val gamma x free (PairV(v1, v2)) =
      let val (cs1, free') = assemble_constraints_val gamma (VAR free) (free + 1) v1
          val  (cs2, free'') = assemble_constraints_val gamma (VAR free') (free' + 1) v2
      in ((x, CON(TIMES, [VAR free, VAR free'])) :: cs1 @ cs2, free'')
      end
  | assemble_constraints_val gamma x free (InlV v) =
      let val (cs, free') = assemble_constraints_val gamma (VAR free) (free + 1) v
      in ((x, CON(PLUS, [VAR free, VAR free'])) :: cs, free' + 1)
      end
  | assemble_constraints_val gamma x free (InrV v) =
      let val (cs, free') = assemble_constraints_val gamma (VAR free) (free + 1) v
      in ((x, CON(PLUS, [VAR free', VAR free])) :: cs, free' + 1)
      end
  | assemble_constraints_val gamma x free (FunV f) =
      let val (cs, free') = assemble_constraints_exprs gamma (VAR free) (VAR (free + 1)) (free + 2) f
      in ((x, CON(ARROW, [VAR free, VAR (free + 1)])) :: cs, free')
      end
  | assemble_constraints_val gamma x free (InjV(n, v)) =
      let val F = #var_t_type gamma n
          val ff = flatten_type (apply_functor_type (Fix F) F)
          val (cs, free') = assemble_constraints_val gamma ff free v
      in ((x, flatten_type (Fix F)) :: cs, free')
      end

fun typecheck_expr gamma e = 
      let val eqns = #1 (assemble_constraints_exprs gamma (VAR 0) (VAR 1) 2 e) 
      in case unify' eqns of
          SOME phi => (inflate_type (subst_sub phi 0), inflate_type (subst_sub phi 1))
        | NONE => raise UnificationError eqns
      end
       
fun typecheck_val gamma v = 
      let val eqns = #1 (assemble_constraints_val gamma (VAR 0) 1 v) 
      in case unify' eqns of
          SOME phi => inflate_type (subst_sub phi 0)
        | NONE => raise UnificationError eqns
      end
      
fun typecheck_ctor_expr _     _ []               y = raise MissingExpr y
  | typecheck_ctor_expr gamma F ((x, ts) :: cts) y = 
      if y = x 
      then (foldr Prod Unit (map (Fix o #var_t_type gamma) ts), Fix F) 
      else typecheck_ctor_expr gamma F cts y

fun typecheck_ctor_val F (cts: (name * name list) list) x = 
      if List.exists (fn y => x = y) (map #1 cts) then Fix F else raise MissingExpr x

fun typecheck_ctor_arg gamma tn t = if t = tn then Id else K (Fix (#var_t_type gamma t))

fun ctor_funct Fs = foldr ProdF (K Unit) Fs

fun typecheck_ctor gamma tn (_, ts) = ctor_funct (map (typecheck_ctor_arg gamma tn) ts)

fun adt_type Fs = foldr SumF (K Void) Fs

fun typecheck_ctors gamma x cts = adt_type (map (typecheck_ctor gamma x) cts)

fun typecheck_typedef gamma n cts = 
      let val F = typecheck_ctors gamma n cts
      in { var_e_type = typecheck_ctor_expr (extend_t_static n F gamma) F cts, 
           var_t_type = fn x => if x = n then F else raise MissingType x }
      end

fun typecheck_def gamma (TypeDecl(x, cts)) = typecheck_typedef gamma x cts
  | typecheck_def gamma (ExprDecl(x, e)) = 
      let val (t1, t2) = typecheck_expr gamma e
      in extend_e_static x (t1, t2) gamma
      end

fun typecheck_prog (Prog(lam, e, v)) =
    let val gamma = foldl (fn (d, gamma) => typecheck_def gamma d) empty_static lam
        val (t1, t2) = typecheck_expr gamma e
        val t3 = typecheck_val gamma v
    in case unify (flatten_type t1) (flatten_type t3) of
          SOME _ => t2
        | NONE => raise UnificationError [(flatten_type t1, flatten_type t3)]
    end

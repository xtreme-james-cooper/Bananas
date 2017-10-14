
(* the actual typechecker
   it works by walking the expression, accumulating contraints, and then unifying them
   it could probably be sped up by performing simple substitutions in place
   but that'd be going afield and it's effective enough as is *)

(* constraints from a val_desc *)
fun assemble_constraints_val_desc gamma x free (ValDesc(n, vs)) =
      let val (ts, t) = var_v_type gamma n
      in foldr (fn ((t, v), (cs1, free')) => 
            let val (cs2, free'') = assemble_constraints_val_desc gamma (flatten_type t) free' v
            in (cs1 @ cs2, free'') 
            end) ([(x, flatten_type t, "val output type mismatch")], free) (ListPair.zip(ts, vs))
      end

(* constraints from an expression *)
fun assemble_constraints_expr gamma _ y free (Const v) = assemble_constraints_val_desc gamma y free v
  | assemble_constraints_expr _ x y free Proj1 = 
      ([(x, CON(TIMES, [y, VAR free]), "Proj1 type mismatch")], free + 1)
  | assemble_constraints_expr _ x y free Proj2 = 
      ([(x, CON(TIMES, [VAR free, y]), "Proj2 type mismatch")], free + 1)
  | assemble_constraints_expr _ x y free Duplicate = 
      ([(y, CON(TIMES, [x, x]), "Duplicate type mismatch")], free)
  | assemble_constraints_expr gamma x y free (Pairwise(f1, f2)) = 
      let val a = VAR free
          val b = VAR (free + 1) 
          val (cs1, free') = assemble_constraints_exprs gamma a b (free + 2) f1
          val c = VAR free'
          val d = VAR (free' + 1) 
          val (cs2, free'') = assemble_constraints_exprs gamma c d (free' + 2) f2
      in ((x, CON(TIMES, [a, c]), "Pairwise(1) type mismatch") :: 
            (y, CON(TIMES, [b, d]), "Pairwise(2) type mismatch") :: cs1 @ cs2, free'') 
      end
  | assemble_constraints_expr _ x y free Injl = ([(y, CON(PLUS, [x, VAR free]), "Injl type mismatch")], free + 1)
  | assemble_constraints_expr _ x y free Injr = ([(y, CON(PLUS, [VAR free, x]), "Injr type mismatch")], free + 1)
  | assemble_constraints_expr _ x y free Strip = ([(x, CON(PLUS, [y, y]), "Strip type mismatch")], free)
  | assemble_constraints_expr gamma x y free (Case (f1, f2)) =
      let val a = VAR free
          val b = VAR (free + 1) 
          val (cs1, free') = assemble_constraints_exprs gamma a b (free + 2) f1
          val c = VAR free' 
          val d = VAR (free' + 1) 
          val (cs2, free'') = assemble_constraints_exprs gamma c d (free' + 2) f2
      in ((x, CON(PLUS, [a, c]), "Case(1) type mismatch") :: 
            (y, CON(PLUS, [b, d]), "Case(2) type mismatch") :: cs1 @ cs2, free'')
      end
  | assemble_constraints_expr _ x y free Distribute = 
      let val a = VAR free
          val b = VAR (free + 1)
          val c = VAR (free + 2)
      in ([(x, CON(TIMES, [CON(PLUS, [a, b]), c]), "Distribute in type mismatch"), 
           (y, CON(PLUS, [CON(TIMES, [a, c]), CON(TIMES, [b, c])]), "Distribute out type mismatch")], free + 3)
      end
  | assemble_constraints_expr _ x y free Apply = 
      ([(x, CON(TIMES, [CON(ARROW, [VAR free, y]), VAR free]), "Apply type mismatch")], free + 1)
  | assemble_constraints_expr gamma x y free (Arrow (f1, f2)) =
      let val a = VAR free
          val b = VAR (free + 1) 
          val (cs1, free') = assemble_constraints_exprs gamma a b (free + 1) f1
          val c = VAR free' 
          val d = VAR (free' + 1) 
          val (cs2, free'') = assemble_constraints_exprs gamma c d (free' + 2) f2
      in ((x, CON(ARROW, [b, c]), "Arrow(1) type mismatch") :: 
            (y, CON(PLUS, [a, d]), "Arrow(2) type mismatch") :: cs1 @ cs2, free'')
      end
  | assemble_constraints_expr gamma x y free (Inj n) = 
      let val F = var_t_type gamma n
      in ([(x, flatten_type (apply_functor_type (Fix F) F), "Inj in type mismatch"), 
             (y, flatten_type (Fix F), "Inj out type mismatch")], free)
      end
  | assemble_constraints_expr gamma x y free (Outj n) = 
      let val F = var_t_type gamma n
      in ([(x, flatten_type (Fix F), "Outj in type mismatch"), 
              (y, flatten_type (apply_functor_type (Fix F) F), "Outj out type mismatch")], free)
      end
  | assemble_constraints_expr gamma x y free (Cata(f, n)) =
      let val F = var_t_type gamma n
          val (cs, free') = assemble_constraints_exprs gamma (apply_functor_flat y F) y free f
      in ((x, CON(MU, [flatten_funct F]), "Cata type mismatch") :: cs, free')
      end
  | assemble_constraints_expr gamma x y free (Ana(f, n)) =
      let val F = var_t_type gamma n
          val (cs, free') = assemble_constraints_exprs gamma x (apply_functor_flat x F) free f
      in ((y, CON(MU, [flatten_funct F]), "Ana type mismatch") :: cs, free')
      end
  | assemble_constraints_expr gamma x y free (Var z) = 
      let val (t1, t2) = var_e_type gamma z
      in ([(x, flatten_type t1, "Var in type mismatch"), (y, flatten_type t2, "Var out type mismatch")], free) 
      end (* we have a monomorphism restriction here 
             all instances of the same variable in the same expr _must_ have the same type 
             not for deep reasons - just because I'm too lazy to fix it here now *)

(* constraints from an expression list *)
and assemble_constraints_exprs (_: static_environment) x y free [] = ([(x, y, "Empty op type mismatch")], free)
  | assemble_constraints_exprs gamma x y free (f1 :: f2) =
      let val (cs1, free') = assemble_constraints_expr gamma x (VAR free) (free + 1) f1
          val (cs2, free'') = assemble_constraints_exprs gamma (VAR free) y free' f2
      in (cs1 @ cs2, free'') 
      end

(* typecheck an expr *)
fun typecheck_expr gamma e = 
      let val eqns = #1 (assemble_constraints_exprs gamma (VAR 0) (VAR 1) 2 e) 
          val phi = unify eqns 
      in (inflate_type (subst_sub phi 0), inflate_type (subst_sub phi 1))
      end
       
(* typecheck a value *)
fun typecheck_val gamma v = 
      let val eqns = #1 (assemble_constraints_val_desc gamma (VAR 0) 1 v) 
          val phi =  unify eqns
      in inflate_type (subst_sub phi 0)
      end
      
(* the expected types of a set of constructors 
   Unit -> \<mu> F if no arguments
   arg1 \<otimes> ... \<otimes> argn -> \<mu> F otherwise *)
fun typecheck_ctor_expr gamma F cts = map (fn (x, ts) => 
      (x, (if ts = [] then Unit else foldr1 Prod (map (Fix o var_t_type gamma) ts), Fix F))) cts

(* check if a name is the recursive type name
   if so, the Id functor; otherwise the constant functor of that name *)
fun typecheck_ctor_arg gamma tn t = if t = tn then Id else K (Fix (var_t_type gamma t))

(* the functor form of a constructor 
   K Unit if no arguments
   arg1 \<Otimes> ... \<Otimes> argn otherwise *)
fun typecheck_ctor _     _  (_, []) = K Unit
  | typecheck_ctor gamma tn (_, ts) = foldr1 ProdF (map (typecheck_ctor_arg gamma tn) ts)

(* the functor form of a set of constructors: ctor1 \<Oplus> ... \<Oplus> ctorn  *)
fun typecheck_ctors gamma x cts = foldr1 SumF (map (typecheck_ctor gamma x) cts)

(* expected type of a constructor-as-value: args -> \<mu> F *)
fun typecheck_ctor_val gamma F cts = 
      map (fn (x, xs) => (x, (map (Fix o var_t_type gamma) xs, Fix F))) cts

(* typecheck a type declaration *)
fun typecheck_typedef gamma n cts = 
      let val F = typecheck_ctors gamma n cts
      in { var_e_type = typecheck_ctor_expr (extend_t_static n F gamma) F cts, 
           var_v_type = typecheck_ctor_val (extend_t_static n F gamma) F cts,
           var_t_type = [(n, F)] }
      end

(* typecheck a declaration *)
fun typecheck_def gamma (TypeDecl(x, cts)) = combine_static gamma (typecheck_typedef gamma x cts)
  | typecheck_def gamma (ExprDecl(x, e)) = 
      let val (t1, t2) = typecheck_expr gamma e
      in extend_e_static x (t1, t2) gamma
      end

(* typecheck a program *)
fun typecheck_prog (Prog(lam, e, v)) =
    let val gamma = foldl (fn (d, gamma) => typecheck_def gamma d) empty_static lam
        val (t1, t2) = typecheck_expr gamma e
        val t3 = typecheck_val gamma v
        val _ = unify [(flatten_type t1, flatten_type t3, "Top level expr-val type mismatch")] 
    in t2
    end

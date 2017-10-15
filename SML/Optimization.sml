
fun cata_fusion (f: expr) (phi: expr list) (F: funct): expr list = phi @ [f]
fun ana_fusion (f: expr) (phi: expr list) (F: funct): expr list = f :: phi

fun optimize _ [] = []
  | optimize env (e :: es) = (case (e, optimize env es) of
        (Duplicate, Proj1 :: es') => es'
      | (Duplicate, Proj2 :: es') => es'
      | (Duplicate, Pairwise(e1, e2) :: es') => 
          if e1 = e2 
          then optimize env (e1 @ Duplicate :: es') 
          else Duplicate :: Pairwise(e1, e2) :: es'
      | (Pairwise(e1, _), Proj1 :: es') => optimize env (Proj1 :: e1 @ es')
      | (Pairwise(_, e2), Proj2 :: es') => optimize env (Proj2 :: e2 @ es')
      | (Pairwise(e1, e2), Pairwise(e1', e2') :: es') => Pairwise(optimize env (e1 @ e1'), optimize env (e2 @ e2')) :: es'
      | (Injl, Strip :: es') => es'
      | (Injl, Case(e1, _) :: es') => optimize env (e1 @ Injl :: es')
      | (Injr, Strip :: es') => es'
      | (Injr, Case(_, e2) :: es') => optimize env (e2 @ Injr :: es')
      | (Case(e1, e2), Strip :: es') =>
          if optimize env e1 = optimize env e2 
          then optimize env (Strip :: optimize env e1 @ es') 
          else Case(optimize env e1, optimize env e2) :: Strip :: es'
      | (Case(e1, e2), Case(e1', e2') :: es') => Case(optimize env (e1 @ e1'), optimize env (e2 @ e2')) :: es'
      | (Distribute, Strip :: es') => optimize env (Pairwise([Strip], []) :: es')
      | (Fun f, Arrow(g, h) :: es') => Fun(optimize env (h @ f @ g)) :: es'
      | (Fun f, Curry g :: es') => Fun (optimize env (Duplicate :: Pairwise([ConstV (FunV (optimize env f))], []) :: g)) :: es'
      | (Arrow(f, g), Arrow(f', g') :: es') => Arrow(optimize env (f @ f'), optimize env (g' @ g)) :: es'
      | (Inj _, Outj _ :: es') => es'
      | (Inj _, Cata(f, n) :: es') => optimize env (apply_functor_expr (Cata(f, n)) (var_t_bind env n) @ f @ es')
      | (Outj n, Inj m :: es') => if n = m then es' else Outj n :: Inj m :: es'
      | (Cata(f, n), e :: es') => optimize env (cata_fusion e f (var_t_bind env n) @ es')
      | (Ana(f, n), Outj _ :: es') => optimize env (f @ apply_functor_expr (Ana(f, n)) (var_t_bind env n) @ es')
      | (e, Ana(f, n) :: es') => optimize env (ana_fusion e f (var_t_bind env n) @ es')
      | (_, Fun f :: es') => Fun f :: es'
      | (_, Const v :: es') => Const v :: es'
      | (_, ConstV v :: es') => ConstV v :: es'
      | (Pairwise(e1, e2), es') => Pairwise(optimize env e1, optimize env e2) :: es'  
      | (Case(e1, e2), es') => Case(optimize env e1, optimize env e2) :: es'
      | (Fun f, es') => Fun (optimize env f) :: es'
      | (Arrow(f, g), es') => Arrow(optimize env f, optimize env g) :: es'
      | (Curry f, es') => Curry (optimize env f) :: es'
      | (Uncurry f, es') => Uncurry (optimize env f) :: es'
      | (Ana(f, n), e :: es') => Ana(optimize env f, n) :: e :: es'
      | (e, Cata(f, n) :: es') => e :: Cata(optimize env f, n) :: es'
      | (Var x, es') => optimize env (var_e_bind env x @ es')
      | (e, es') => e :: es')

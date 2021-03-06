
fun optimize_single env (Pairwise(f, g)) = Pairwise(optimize env f, optimize env g)
  | optimize_single env (Case(f, g)) = Case(optimize env f, optimize env g)
  | optimize_single env (Fun f) = Fun (optimize env f)
  | optimize_single env (Arrow(f, g)) = Arrow(optimize env f, optimize env g)
  | optimize_single env (Uncurry f) = Uncurry(optimize env f)
  | optimize_single env (Curry f) = Curry(optimize env f)
  | optimize_single env (Cata(f, n)) = Cata(optimize env f, n)
  | optimize_single env (Ana(f, n)) = Ana(optimize env f, n)
  | optimize_single _   e = e

and optimize _ [] = []
  | optimize env (e :: es) = (case (optimize_single env e, optimize env es) of
        (e1, []) => e1 :: []
      | (Proj1, Proj1 :: es') => optimize_single env e :: optimize env es 
      | (Proj1, Proj2 :: es') => optimize_single env e :: optimize env es
      | (Proj1, Duplicate :: es') => optimize_single env e :: optimize env es 
      | (Proj1, Pairwise(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Proj1, Injl :: es') => optimize_single env e :: optimize env es 
      | (Proj1, Injr :: es') => optimize_single env e :: optimize env es 
      | (Proj1, Strip :: es') => optimize_single env e :: optimize env es 
      | (Proj1, Case(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Proj1, Distribute :: es') => optimize_single env e :: optimize env es 
      | (Proj1, Apply :: es') => optimize_single env e :: optimize env es 
      | (Proj1, Fun f :: es') => optimize_single env e :: optimize env es 
      | (Proj1, Arrow(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Proj1, Uncurry f :: es') => optimize_single env e :: optimize env es 
      | (Proj1, Curry f :: es') => optimize_single env e :: optimize env es 
      | (Proj1, Inj n :: es') => optimize_single env e :: optimize env es 
      | (Proj1, Outj n :: es') => optimize_single env e :: optimize env es 
      | (Proj1, Cata(f, n) :: es') => optimize_single env e :: optimize env es 
      | (Proj1, Ana(f, n) :: es') => optimize_single env e :: optimize env es 
      | (Proj1, Var x :: es') => optimize_single env e :: optimize env es 
      | (Proj1, Const v :: es') => optimize_single env e :: optimize env es 
      | (Proj1, ConstV v :: es') => optimize_single env e :: optimize env es 
      | (Proj2, Proj1 :: es') => optimize_single env e :: optimize env es 
      | (Proj2, Proj2 :: es') => optimize_single env e :: optimize env es 
      | (Proj2, Duplicate :: es') => optimize_single env e :: optimize env es 
      | (Proj2, Pairwise(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Proj2, Injl :: es') => optimize_single env e :: optimize env es 
      | (Proj2, Injr :: es') => optimize_single env e :: optimize env es 
      | (Proj2, Strip :: es') => optimize_single env e :: optimize env es 
      | (Proj2, Case(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Proj2, Distribute :: es') => optimize_single env e :: optimize env es 
      | (Proj2, Apply :: es') => optimize_single env e :: optimize env es 
      | (Proj2, Fun f :: es') => optimize_single env e :: optimize env es 
      | (Proj2, Arrow(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Proj2, Uncurry f :: es') => optimize_single env e :: optimize env es 
      | (Proj2, Curry f :: es') => optimize_single env e :: optimize env es 
      | (Proj2, Inj n :: es') => optimize_single env e :: optimize env es 
      | (Proj2, Outj n :: es') => optimize_single env e :: optimize env es 
      | (Proj2, Cata(f, n) :: es') => optimize_single env e :: optimize env es 
      | (Proj2, Ana(f, n) :: es') => optimize_single env e :: optimize env es 
      | (Proj2, Var x :: es') => optimize_single env e :: optimize env es 
      | (Proj2, Const v :: es') => optimize_single env e :: optimize env es 
      | (Proj2, ConstV v :: es') => optimize_single env e :: optimize env es 
      | (Duplicate, Proj1 :: es') => optimize_single env e :: optimize env es 
      | (Duplicate, Proj2 :: es') => optimize_single env e :: optimize env es 
      | (Duplicate, Duplicate :: es') => optimize_single env e :: optimize env es 
      | (Duplicate, Pairwise(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Duplicate, Injl :: es') => optimize_single env e :: optimize env es 
      | (Duplicate, Injr :: es') => optimize_single env e :: optimize env es 
      | (Duplicate, Strip :: es') => optimize_single env e :: optimize env es 
      | (Duplicate, Case(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Duplicate, Distribute :: es') => optimize_single env e :: optimize env es 
      | (Duplicate, Apply :: es') => optimize_single env e :: optimize env es 
      | (Duplicate, Fun f :: es') => optimize_single env e :: optimize env es 
      | (Duplicate, Arrow(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Duplicate, Uncurry f :: es') => optimize_single env e :: optimize env es 
      | (Duplicate, Curry f :: es') => optimize_single env e :: optimize env es 
      | (Duplicate, Inj n :: es') => optimize_single env e :: optimize env es 
      | (Duplicate, Outj n :: es') => optimize_single env e :: optimize env es 
      | (Duplicate, Cata(f, n) :: es') => optimize_single env e :: optimize env es 
      | (Duplicate, Ana(f, n) :: es') => optimize_single env e :: optimize env es 
      | (Duplicate, Var x :: es') => optimize_single env e :: optimize env es 
      | (Duplicate, Const v :: es') => optimize_single env e :: optimize env es 
      | (Duplicate, ConstV v :: es') => optimize_single env e :: optimize env es 
      | (Pairwise(f, g), Proj1 :: es') => optimize_single env e :: optimize env es 
      | (Pairwise(f, g), Proj2 :: es') => optimize_single env e :: optimize env es 
      | (Pairwise(f, g), Duplicate :: es') => optimize_single env e :: optimize env es 
      | (Pairwise(f, g), Pairwise(f', g') :: es') => optimize_single env e :: optimize env es 
      | (Pairwise(f, g), Injl :: es') => optimize_single env e :: optimize env es 
      | (Pairwise(f, g), Injr :: es') => optimize_single env e :: optimize env es 
      | (Pairwise(f, g), Strip :: es') => optimize_single env e :: optimize env es 
      | (Pairwise(f, g), Case(f', g') :: es') => optimize_single env e :: optimize env es 
      | (Pairwise(f, g), Distribute :: es') => optimize_single env e :: optimize env es 
      | (Pairwise(f, g), Apply :: es') => optimize_single env e :: optimize env es 
      | (Pairwise(f, g), Fun h :: es') => optimize_single env e :: optimize env es 
      | (Pairwise(f, g), Arrow(f', g') :: es') => optimize_single env e :: optimize env es 
      | (Pairwise(f, g), Uncurry h :: es') => optimize_single env e :: optimize env es 
      | (Pairwise(f, g), Curry h :: es') => optimize_single env e :: optimize env es 
      | (Pairwise(f, g), Inj n :: es') => optimize_single env e :: optimize env es 
      | (Pairwise(f, g), Outj n :: es') => optimize_single env e :: optimize env es 
      | (Pairwise(f, g), Cata(h, n) :: es') => optimize_single env e :: optimize env es 
      | (Pairwise(f, g), Ana(h, n) :: es') => optimize_single env e :: optimize env es 
      | (Pairwise(f, g), Var x :: es') => optimize_single env e :: optimize env es 
      | (Pairwise(f, g), Const v :: es') => optimize_single env e :: optimize env es 
      | (Pairwise(f, g), ConstV v :: es') => optimize_single env e :: optimize env es 
      | (Injl, Proj1 :: es') => optimize_single env e :: optimize env es 
      | (Injl, Proj2 :: es') => optimize_single env e :: optimize env es 
      | (Injl, Duplicate :: es') => optimize_single env e :: optimize env es 
      | (Injl, Pairwise(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Injl, Injl :: es') => optimize_single env e :: optimize env es 
      | (Injl, Injr :: es') => optimize_single env e :: optimize env es 
      | (Injl, Strip :: es') => optimize_single env e :: optimize env es 
      | (Injl, Case(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Injl, Distribute :: es') => optimize_single env e :: optimize env es 
      | (Injl, Apply :: es') => optimize_single env e :: optimize env es 
      | (Injl, Fun f :: es') => optimize_single env e :: optimize env es 
      | (Injl, Arrow(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Injl, Uncurry f :: es') => optimize_single env e :: optimize env es 
      | (Injl, Curry f :: es') => optimize_single env e :: optimize env es 
      | (Injl, Inj n :: es') => optimize_single env e :: optimize env es 
      | (Injl, Outj n :: es') => optimize_single env e :: optimize env es 
      | (Injl, Cata(f, n) :: es') => optimize_single env e :: optimize env es 
      | (Injl, Ana(f, n) :: es') => optimize_single env e :: optimize env es 
      | (Injl, Var x :: es') => optimize_single env e :: optimize env es 
      | (Injl, Const v :: es') => optimize_single env e :: optimize env es 
      | (Injl, ConstV v :: es') => optimize_single env e :: optimize env es 
      | (Injr, Proj1 :: es') => optimize_single env e :: optimize env es 
      | (Injr, Proj2 :: es') => optimize_single env e :: optimize env es 
      | (Injr, Duplicate :: es') => optimize_single env e :: optimize env es 
      | (Injr, Pairwise(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Injr, Injl :: es') => optimize_single env e :: optimize env es 
      | (Injr, Injr :: es') => optimize_single env e :: optimize env es 
      | (Injr, Strip :: es') => optimize_single env e :: optimize env es 
      | (Injr, Case(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Injr, Distribute :: es') => optimize_single env e :: optimize env es 
      | (Injr, Apply :: es') => optimize_single env e :: optimize env es 
      | (Injr, Fun f :: es') => optimize_single env e :: optimize env es 
      | (Injr, Arrow(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Injr, Uncurry f :: es') => optimize_single env e :: optimize env es 
      | (Injr, Curry f :: es') => optimize_single env e :: optimize env es 
      | (Injr, Inj n :: es') => optimize_single env e :: optimize env es 
      | (Injr, Outj n :: es') => optimize_single env e :: optimize env es 
      | (Injr, Cata(f, n) :: es') => optimize_single env e :: optimize env es 
      | (Injr, Ana(f, n) :: es') => optimize_single env e :: optimize env es 
      | (Injr, Var x :: es') => optimize_single env e :: optimize env es 
      | (Injr, Const v :: es') => optimize_single env e :: optimize env es 
      | (Injr, ConstV v :: es') => optimize_single env e :: optimize env es 
      | (Strip, Proj1 :: es') => optimize_single env e :: optimize env es 
      | (Strip, Proj2 :: es') => optimize_single env e :: optimize env es 
      | (Strip, Duplicate :: es') => optimize_single env e :: optimize env es 
      | (Strip, Pairwise(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Strip, Injl :: es') => optimize_single env e :: optimize env es 
      | (Strip, Injr :: es') => optimize_single env e :: optimize env es 
      | (Strip, Strip :: es') => optimize_single env e :: optimize env es 
      | (Strip, Case(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Strip, Distribute :: es') => optimize_single env e :: optimize env es 
      | (Strip, Apply :: es') => optimize_single env e :: optimize env es 
      | (Strip, Fun f :: es') => optimize_single env e :: optimize env es 
      | (Strip, Arrow(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Strip, Uncurry f :: es') => optimize_single env e :: optimize env es 
      | (Strip, Curry f :: es') => optimize_single env e :: optimize env es 
      | (Strip, Inj n :: es') => optimize_single env e :: optimize env es 
      | (Strip, Outj n :: es') => optimize_single env e :: optimize env es 
      | (Strip, Cata(f, n) :: es') => optimize_single env e :: optimize env es 
      | (Strip, Ana(f, n) :: es') => optimize_single env e :: optimize env es 
      | (Strip, Var x :: es') => optimize_single env e :: optimize env es 
      | (Strip, Const v :: es') => optimize_single env e :: optimize env es 
      | (Strip, ConstV v :: es') => optimize_single env e :: optimize env es 
      | (Case(f, g), Proj1 :: es') => optimize_single env e :: optimize env es 
      | (Case(f, g), Proj2 :: es') => optimize_single env e :: optimize env es 
      | (Case(f, g), Duplicate :: es') => optimize_single env e :: optimize env es 
      | (Case(f, g), Pairwise(f', g') :: es') => optimize_single env e :: optimize env es 
      | (Case(f, g), Injl :: es') => optimize_single env e :: optimize env es 
      | (Case(f, g), Injr :: es') => optimize_single env e :: optimize env es 
      | (Case(f, g), Strip :: es') => optimize_single env e :: optimize env es 
      | (Case(f, g), Case(f', g') :: es') => optimize_single env e :: optimize env es 
      | (Case(f, g), Distribute :: es') => optimize_single env e :: optimize env es 
      | (Case(f, g), Apply :: es') => optimize_single env e :: optimize env es 
      | (Case(f, g), Fun h :: es') => optimize_single env e :: optimize env es 
      | (Case(f, g), Arrow(f', g') :: es') => optimize_single env e :: optimize env es 
      | (Case(f, g), Uncurry h :: es') => optimize_single env e :: optimize env es 
      | (Case(f, g), Curry h :: es') => optimize_single env e :: optimize env es 
      | (Case(f, g), Inj n :: es') => optimize_single env e :: optimize env es 
      | (Case(f, g), Outj n :: es') => optimize_single env e :: optimize env es 
      | (Case(f, g), Cata(h, n) :: es') => optimize_single env e :: optimize env es 
      | (Case(f, g), Ana(h, n) :: es') => optimize_single env e :: optimize env es 
      | (Case(f, g), Var x :: es') => optimize_single env e :: optimize env es 
      | (Case(f, g), Const v :: es') => optimize_single env e :: optimize env es 
      | (Case(f, g), ConstV v :: es') => optimize_single env e :: optimize env es 
      | (Distribute, Proj1 :: es') => optimize_single env e :: optimize env es 
      | (Distribute, Proj2 :: es') => optimize_single env e :: optimize env es 
      | (Distribute, Duplicate :: es') => optimize_single env e :: optimize env es 
      | (Distribute, Pairwise(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Distribute, Injl :: es') => optimize_single env e :: optimize env es 
      | (Distribute, Injr :: es') => optimize_single env e :: optimize env es 
      | (Distribute, Strip :: es') => optimize_single env e :: optimize env es 
      | (Distribute, Case(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Distribute, Distribute :: es') => optimize_single env e :: optimize env es 
      | (Distribute, Apply :: es') => optimize_single env e :: optimize env es 
      | (Distribute, Fun f :: es') => optimize_single env e :: optimize env es 
      | (Distribute, Arrow(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Distribute, Uncurry f :: es') => optimize_single env e :: optimize env es 
      | (Distribute, Curry f :: es') => optimize_single env e :: optimize env es 
      | (Distribute, Inj n :: es') => optimize_single env e :: optimize env es 
      | (Distribute, Outj n :: es') => optimize_single env e :: optimize env es 
      | (Distribute, Cata(f, n) :: es') => optimize_single env e :: optimize env es 
      | (Distribute, Ana(f, n) :: es') => optimize_single env e :: optimize env es 
      | (Distribute, Var x :: es') => optimize_single env e :: optimize env es 
      | (Distribute, Const v :: es') => optimize_single env e :: optimize env es 
      | (Distribute, ConstV v :: es') => optimize_single env e :: optimize env es 
      | (Apply, Proj1 :: es') => optimize_single env e :: optimize env es 
      | (Apply, Proj2 :: es') => optimize_single env e :: optimize env es 
      | (Apply, Duplicate :: es') => optimize_single env e :: optimize env es 
      | (Apply, Pairwise(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Apply, Injl :: es') => optimize_single env e :: optimize env es 
      | (Apply, Injr :: es') => optimize_single env e :: optimize env es 
      | (Apply, Strip :: es') => optimize_single env e :: optimize env es 
      | (Apply, Case(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Apply, Distribute :: es') => optimize_single env e :: optimize env es 
      | (Apply, Apply :: es') => optimize_single env e :: optimize env es 
      | (Apply, Fun f :: es') => optimize_single env e :: optimize env es 
      | (Apply, Arrow(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Apply, Uncurry f :: es') => optimize_single env e :: optimize env es 
      | (Apply, Curry f :: es') => optimize_single env e :: optimize env es 
      | (Apply, Inj n :: es') => optimize_single env e :: optimize env es 
      | (Apply, Outj n :: es') => optimize_single env e :: optimize env es 
      | (Apply, Cata(f, n) :: es') => optimize_single env e :: optimize env es 
      | (Apply, Ana(f, n) :: es') => optimize_single env e :: optimize env es 
      | (Apply, Var x :: es') => optimize_single env e :: optimize env es 
      | (Apply, Const v :: es') => optimize_single env e :: optimize env es 
      | (Apply, ConstV v :: es') => optimize_single env e :: optimize env es 
      | (Fun f, Proj1 :: es') => optimize_single env e :: optimize env es 
      | (Fun f, Proj2 :: es') => optimize_single env e :: optimize env es 
      | (Fun f, Duplicate :: es') => optimize_single env e :: optimize env es 
      | (Fun f, Pairwise(g, h) :: es') => optimize_single env e :: optimize env es 
      | (Fun f, Injl :: es') => optimize_single env e :: optimize env es 
      | (Fun f, Injr :: es') => optimize_single env e :: optimize env es 
      | (Fun f, Strip :: es') => optimize_single env e :: optimize env es 
      | (Fun f, Case(g, h) :: es') => optimize_single env e :: optimize env es 
      | (Fun f, Distribute :: es') => optimize_single env e :: optimize env es 
      | (Fun f, Apply :: es') => optimize_single env e :: optimize env es 
      | (Fun f, Fun f' :: es') => optimize_single env e :: optimize env es 
      | (Fun f, Arrow(g, h) :: es') => optimize_single env e :: optimize env es 
      | (Fun f, Uncurry f' :: es') => optimize_single env e :: optimize env es 
      | (Fun f, Curry f' :: es') => optimize_single env e :: optimize env es 
      | (Fun f, Inj n :: es') => optimize_single env e :: optimize env es 
      | (Fun f, Outj n :: es') => optimize_single env e :: optimize env es 
      | (Fun f, Cata(f', n) :: es') => optimize_single env e :: optimize env es 
      | (Fun f, Ana(f', n) :: es') => optimize_single env e :: optimize env es 
      | (Fun f, Var x :: es') => optimize_single env e :: optimize env es 
      | (Fun f, Const v :: es') => optimize_single env e :: optimize env es 
      | (Fun f, ConstV v :: es') => optimize_single env e :: optimize env es 
      | (Arrow(f, g), Proj1 :: es') => optimize_single env e :: optimize env es 
      | (Arrow(f, g), Proj2 :: es') => optimize_single env e :: optimize env es 
      | (Arrow(f, g), Duplicate :: es') => optimize_single env e :: optimize env es 
      | (Arrow(f, g), Pairwise(f', g') :: es') => optimize_single env e :: optimize env es 
      | (Arrow(f, g), Injl :: es') => optimize_single env e :: optimize env es 
      | (Arrow(f, g), Injr :: es') => optimize_single env e :: optimize env es 
      | (Arrow(f, g), Strip :: es') => optimize_single env e :: optimize env es 
      | (Arrow(f, g), Case(f', g') :: es') => optimize_single env e :: optimize env es 
      | (Arrow(f, g), Distribute :: es') => optimize_single env e :: optimize env es 
      | (Arrow(f, g), Apply :: es') => optimize_single env e :: optimize env es 
      | (Arrow(f, g), Fun h :: es') => optimize_single env e :: optimize env es 
      | (Arrow(f, g), Arrow(f', g') :: es') => optimize_single env e :: optimize env es 
      | (Arrow(f, g), Uncurry h :: es') => optimize_single env e :: optimize env es 
      | (Arrow(f, g), Curry h :: es') => optimize_single env e :: optimize env es 
      | (Arrow(f, g), Inj n :: es') => optimize_single env e :: optimize env es 
      | (Arrow(f, g), Outj n :: es') => optimize_single env e :: optimize env es 
      | (Arrow(f, g), Cata(h, n) :: es') => optimize_single env e :: optimize env es 
      | (Arrow(f, g), Ana(h, n) :: es') => optimize_single env e :: optimize env es 
      | (Arrow(f, g), Var x :: es') => optimize_single env e :: optimize env es 
      | (Arrow(f, g), Const v :: es') => optimize_single env e :: optimize env es 
      | (Arrow(f, g), ConstV v :: es') => optimize_single env e :: optimize env es 
      | (Uncurry f, Proj1 :: es') => optimize_single env e :: optimize env es 
      | (Uncurry f, Proj2 :: es') => optimize_single env e :: optimize env es 
      | (Uncurry f, Duplicate :: es') => optimize_single env e :: optimize env es 
      | (Uncurry f, Pairwise(g, h) :: es') => optimize_single env e :: optimize env es 
      | (Uncurry f, Injl :: es') => optimize_single env e :: optimize env es 
      | (Uncurry f, Injr :: es') => optimize_single env e :: optimize env es 
      | (Uncurry f, Strip :: es') => optimize_single env e :: optimize env es 
      | (Uncurry f, Case(g, h) :: es') => optimize_single env e :: optimize env es 
      | (Uncurry f, Distribute :: es') => optimize_single env e :: optimize env es 
      | (Uncurry f, Apply :: es') => optimize_single env e :: optimize env es 
      | (Uncurry f, Fun f' :: es') => optimize_single env e :: optimize env es 
      | (Uncurry f, Arrow(g, h) :: es') => optimize_single env e :: optimize env es 
      | (Uncurry f, Uncurry f' :: es') => optimize_single env e :: optimize env es 
      | (Uncurry f, Curry f' :: es') => optimize_single env e :: optimize env es 
      | (Uncurry f, Inj n :: es') => optimize_single env e :: optimize env es 
      | (Uncurry f, Outj n :: es') => optimize_single env e :: optimize env es 
      | (Uncurry f, Cata(f', n) :: es') => optimize_single env e :: optimize env es 
      | (Uncurry f, Ana(f', n) :: es') => optimize_single env e :: optimize env es 
      | (Uncurry f, Var x :: es') => optimize_single env e :: optimize env es 
      | (Uncurry f, Const v :: es') => optimize_single env e :: optimize env es 
      | (Uncurry f, ConstV v :: es') => optimize_single env e :: optimize env es 
      | (Curry f, Proj1 :: es') => optimize_single env e :: optimize env es 
      | (Curry f, Proj2 :: es') => optimize_single env e :: optimize env es 
      | (Curry f, Duplicate :: es') => optimize_single env e :: optimize env es 
      | (Curry f, Pairwise(g, h) :: es') => optimize_single env e :: optimize env es 
      | (Curry f, Injl :: es') => optimize_single env e :: optimize env es 
      | (Curry f, Injr :: es') => optimize_single env e :: optimize env es 
      | (Curry f, Strip :: es') => optimize_single env e :: optimize env es 
      | (Curry f, Case(g, h) :: es') => optimize_single env e :: optimize env es 
      | (Curry f, Distribute :: es') => optimize_single env e :: optimize env es 
      | (Curry f, Apply :: es') => optimize_single env e :: optimize env es 
      | (Curry f, Fun f' :: es') => optimize_single env e :: optimize env es 
      | (Curry f, Arrow(g, h) :: es') => optimize_single env e :: optimize env es 
      | (Curry f, Uncurry f' :: es') => optimize_single env e :: optimize env es 
      | (Curry f, Curry f' :: es') => optimize_single env e :: optimize env es 
      | (Curry f, Inj n :: es') => optimize_single env e :: optimize env es 
      | (Curry f, Outj n :: es') => optimize_single env e :: optimize env es 
      | (Curry f, Cata(f', n) :: es') => optimize_single env e :: optimize env es 
      | (Curry f, Ana(f', n) :: es') => optimize_single env e :: optimize env es 
      | (Curry f, Var x :: es') => optimize_single env e :: optimize env es 
      | (Curry f, Const v :: es') => optimize_single env e :: optimize env es 
      | (Curry f, ConstV v :: es') => optimize_single env e :: optimize env es 
      | (Inj n, Proj1 :: es') => optimize_single env e :: optimize env es 
      | (Inj n, Proj2 :: es') => optimize_single env e :: optimize env es 
      | (Inj n, Duplicate :: es') => optimize_single env e :: optimize env es 
      | (Inj n, Pairwise(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Inj n, Injl :: es') => optimize_single env e :: optimize env es 
      | (Inj n, Injr :: es') => optimize_single env e :: optimize env es 
      | (Inj n, Strip :: es') => optimize_single env e :: optimize env es 
      | (Inj n, Case(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Inj n, Distribute :: es') => optimize_single env e :: optimize env es 
      | (Inj n, Apply :: es') => optimize_single env e :: optimize env es 
      | (Inj n, Fun f :: es') => optimize_single env e :: optimize env es 
      | (Inj n, Arrow(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Inj n, Uncurry f :: es') => optimize_single env e :: optimize env es 
      | (Inj n, Curry f :: es') => optimize_single env e :: optimize env es 
      | (Inj n, Inj n' :: es') => optimize_single env e :: optimize env es 
      | (Inj n, Outj n' :: es') => optimize_single env e :: optimize env es 
      | (Inj n, Cata(f, n') :: es') => optimize_single env e :: optimize env es 
      | (Inj n, Ana(f, n') :: es') => optimize_single env e :: optimize env es 
      | (Inj n, Var x :: es') => optimize_single env e :: optimize env es 
      | (Inj n, Const v :: es') => optimize_single env e :: optimize env es 
      | (Inj n, ConstV v :: es') => optimize_single env e :: optimize env es 
      | (Outj n, Proj1 :: es') => optimize_single env e :: optimize env es 
      | (Outj n, Proj2 :: es') => optimize_single env e :: optimize env es 
      | (Outj n, Duplicate :: es') => optimize_single env e :: optimize env es 
      | (Outj n, Pairwise(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Outj n, Injl :: es') => optimize_single env e :: optimize env es 
      | (Outj n, Injr :: es') => optimize_single env e :: optimize env es 
      | (Outj n, Strip :: es') => optimize_single env e :: optimize env es 
      | (Outj n, Case(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Outj n, Distribute :: es') => optimize_single env e :: optimize env es 
      | (Outj n, Apply :: es') => optimize_single env e :: optimize env es 
      | (Outj n, Fun f :: es') => optimize_single env e :: optimize env es 
      | (Outj n, Arrow(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Outj n, Uncurry f :: es') => optimize_single env e :: optimize env es 
      | (Outj n, Curry f :: es') => optimize_single env e :: optimize env es 
      | (Outj n, Inj n' :: es') => optimize_single env e :: optimize env es 
      | (Outj n, Outj n' :: es') => optimize_single env e :: optimize env es 
      | (Outj n, Cata(f, n') :: es') => optimize_single env e :: optimize env es 
      | (Outj n, Ana(f, n') :: es') => optimize_single env e :: optimize env es 
      | (Outj n, Var x :: es') => optimize_single env e :: optimize env es 
      | (Outj n, Const v :: es') => optimize_single env e :: optimize env es 
      | (Outj n, ConstV v :: es') => optimize_single env e :: optimize env es 
      | (Cata(f, n), Proj1 :: es') => optimize_single env e :: optimize env es 
      | (Cata(f, n), Proj2 :: es') => optimize_single env e :: optimize env es 
      | (Cata(f, n), Duplicate :: es') => optimize_single env e :: optimize env es 
      | (Cata(f, n), Pairwise(g, h) :: es') => optimize_single env e :: optimize env es 
      | (Cata(f, n), Injl :: es') => optimize_single env e :: optimize env es 
      | (Cata(f, n), Injr :: es') => optimize_single env e :: optimize env es 
      | (Cata(f, n), Strip :: es') => optimize_single env e :: optimize env es 
      | (Cata(f, n), Case(g, h) :: es') => optimize_single env e :: optimize env es 
      | (Cata(f, n), Distribute :: es') => optimize_single env e :: optimize env es 
      | (Cata(f, n), Apply :: es') => optimize_single env e :: optimize env es 
      | (Cata(f, n), Fun f' :: es') => optimize_single env e :: optimize env es 
      | (Cata(f, n), Arrow(g, h) :: es') => optimize_single env e :: optimize env es 
      | (Cata(f, n), Uncurry f' :: es') => optimize_single env e :: optimize env es 
      | (Cata(f, n), Curry f' :: es') => optimize_single env e :: optimize env es 
      | (Cata(f, n), Inj n' :: es') => optimize_single env e :: optimize env es 
      | (Cata(f, n), Outj n' :: es') => optimize_single env e :: optimize env es 
      | (Cata(f, n), Cata(f', n') :: es') => optimize_single env e :: optimize env es 
      | (Cata(f, n), Ana(f', n') :: es') => optimize_single env e :: optimize env es 
      | (Cata(f, n), Var x :: es') => optimize_single env e :: optimize env es 
      | (Cata(f, n), Const v :: es') => optimize_single env e :: optimize env es 
      | (Cata(f, n), ConstV v :: es') => optimize_single env e :: optimize env es 
      | (Ana(f, n), Proj1 :: es') => optimize_single env e :: optimize env es 
      | (Ana(f, n), Proj2 :: es') => optimize_single env e :: optimize env es 
      | (Ana(f, n), Duplicate :: es') => optimize_single env e :: optimize env es 
      | (Ana(f, n), Pairwise(g, h) :: es') => optimize_single env e :: optimize env es 
      | (Ana(f, n), Injl :: es') => optimize_single env e :: optimize env es 
      | (Ana(f, n), Injr :: es') => optimize_single env e :: optimize env es 
      | (Ana(f, n), Strip :: es') => optimize_single env e :: optimize env es 
      | (Ana(f, n), Case(g, h) :: es') => optimize_single env e :: optimize env es 
      | (Ana(f, n), Distribute :: es') => optimize_single env e :: optimize env es 
      | (Ana(f, n), Apply :: es') => optimize_single env e :: optimize env es 
      | (Ana(f, n), Fun f' :: es') => optimize_single env e :: optimize env es 
      | (Ana(f, n), Arrow(g, h) :: es') => optimize_single env e :: optimize env es 
      | (Ana(f, n), Uncurry f' :: es') => optimize_single env e :: optimize env es 
      | (Ana(f, n), Curry f' :: es') => optimize_single env e :: optimize env es 
      | (Ana(f, n), Inj n' :: es') => optimize_single env e :: optimize env es 
      | (Ana(f, n), Outj n' :: es') => optimize_single env e :: optimize env es 
      | (Ana(f, n), Cata(f', n') :: es') => optimize_single env e :: optimize env es 
      | (Ana(f, n), Ana(f', n') :: es') => optimize_single env e :: optimize env es 
      | (Ana(f, n), Var x :: es') => optimize_single env e :: optimize env es 
      | (Ana(f, n), Const v :: es') => optimize_single env e :: optimize env es 
      | (Ana(f, n), ConstV v :: es') => optimize_single env e :: optimize env es 
      | (Var x, Proj1 :: es') => optimize_single env e :: optimize env es 
      | (Var x, Proj2 :: es') => optimize_single env e :: optimize env es 
      | (Var x, Duplicate :: es') => optimize_single env e :: optimize env es 
      | (Var x, Pairwise(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Var x, Injl :: es') => optimize_single env e :: optimize env es 
      | (Var x, Injr :: es') => optimize_single env e :: optimize env es 
      | (Var x, Strip :: es') => optimize_single env e :: optimize env es 
      | (Var x, Case(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Var x, Distribute :: es') => optimize_single env e :: optimize env es 
      | (Var x, Apply :: es') => optimize_single env e :: optimize env es 
      | (Var x, Fun f :: es') => optimize_single env e :: optimize env es 
      | (Var x, Arrow(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Var x, Uncurry f :: es') => optimize_single env e :: optimize env es 
      | (Var x, Curry f :: es') => optimize_single env e :: optimize env es 
      | (Var x, Inj n :: es') => optimize_single env e :: optimize env es 
      | (Var x, Outj n :: es') => optimize_single env e :: optimize env es 
      | (Var x, Cata(f, n) :: es') => optimize_single env e :: optimize env es 
      | (Var x, Ana(f, n) :: es') => optimize_single env e :: optimize env es 
      | (Var x, Var y :: es') => optimize_single env e :: optimize env es 
      | (Var x, Const v :: es') => optimize_single env e :: optimize env es 
      | (Var x, ConstV v :: es') => optimize_single env e :: optimize env es 
      | (Const v, Proj1 :: es') => optimize_single env e :: optimize env es 
      | (Const v, Proj2 :: es') => optimize_single env e :: optimize env es 
      | (Const v, Duplicate :: es') => optimize_single env e :: optimize env es 
      | (Const v, Pairwise(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Const v, Injl :: es') => optimize_single env e :: optimize env es 
      | (Const v, Injr :: es') => optimize_single env e :: optimize env es 
      | (Const v, Strip :: es') => optimize_single env e :: optimize env es 
      | (Const v, Case(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Const v, Distribute :: es') => optimize_single env e :: optimize env es 
      | (Const v, Apply :: es') => optimize_single env e :: optimize env es 
      | (Const v, Fun f :: es') => optimize_single env e :: optimize env es 
      | (Const v, Arrow(f, g) :: es') => optimize_single env e :: optimize env es 
      | (Const v, Uncurry f :: es') => optimize_single env e :: optimize env es 
      | (Const v, Curry f :: es') => optimize_single env e :: optimize env es 
      | (Const v, Inj n :: es') => optimize_single env e :: optimize env es 
      | (Const v, Outj n :: es') => optimize_single env e :: optimize env es 
      | (Const v, Cata(f, n) :: es') => optimize_single env e :: optimize env es 
      | (Const v, Ana(f, n) :: es') => optimize_single env e :: optimize env es 
      | (Const v, Var x :: es') => optimize_single env e :: optimize env es 
      | (Const v, Const v' :: es') => optimize_single env e :: optimize env es 
      | (Const v, ConstV v' :: es') => optimize_single env e :: optimize env es 
      | (ConstV v, Proj1 :: es') => optimize_single env e :: optimize env es 
      | (ConstV v, Proj2 :: es') => optimize_single env e :: optimize env es 
      | (ConstV v, Duplicate :: es') => optimize_single env e :: optimize env es 
      | (ConstV v, Pairwise(f, g) :: es') => optimize_single env e :: optimize env es 
      | (ConstV v, Injl :: es') => optimize_single env e :: optimize env es 
      | (ConstV v, Injr :: es') => optimize_single env e :: optimize env es 
      | (ConstV v, Strip :: es') => optimize_single env e :: optimize env es 
      | (ConstV v, Case(f, g) :: es') => optimize_single env e :: optimize env es 
      | (ConstV v, Distribute :: es') => optimize_single env e :: optimize env es 
      | (ConstV v, Apply :: es') => optimize_single env e :: optimize env es 
      | (ConstV v, Fun f :: es') => optimize_single env e :: optimize env es 
      | (ConstV v, Arrow(f, g) :: es') => optimize_single env e :: optimize env es 
      | (ConstV v, Uncurry f :: es') => optimize_single env e :: optimize env es 
      | (ConstV v, Curry f :: es') => optimize_single env e :: optimize env es 
      | (ConstV v, Inj n :: es') => optimize_single env e :: optimize env es 
      | (ConstV v, Outj n :: es') => optimize_single env e :: optimize env es 
      | (ConstV v, Cata(f, n) :: es') => optimize_single env e :: optimize env es 
      | (ConstV v, Ana(f, n) :: es') => optimize_single env e :: optimize env es 
      | (ConstV v, Var x :: es') => optimize_single env e :: optimize env es 
      | (ConstV v, Const v' :: es') => optimize_single env e :: optimize env es 
      | (ConstV v, ConstV v' :: es') => optimize_single env e :: optimize env es)


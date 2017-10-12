
type var = int

datatype 'a expression =
  VAR of var
| CON of 'a * 'a expression list

fun vars (VAR(x)) = [x]
  | vars (CON(_, es)) = List.concat (map vars es)

datatype 'a substitution = 
  EMPTY
| EXTEND of var * 'a expression * 'a substitution

fun subst_expr x e' (VAR(y))     = if x = y then e' else VAR y
  | subst_expr x e' (CON(s, es)) = CON(s, map (subst_expr x e') es)

fun subst_sub EMPTY                 x = VAR x
  | subst_sub (EXTEND(y, e, theta)) x = (if x = y then e else subst_expr y e (subst_sub theta x))

fun subst_expr_sub theta (VAR(x))     = subst_sub theta x
  | subst_expr_sub theta (CON(s, es)) = CON(s, map (subst_expr_sub theta) es)

type 'a equation = 'a expression * 'a expression

fun subst_eqn x e' (e1, e2) = (subst_expr x e' e1, subst_expr x e' e2)

fun unify' [] = SOME EMPTY
  | unify' ((CON(s, es1), CON(t, es2)) :: eqs) =
      if s = t andalso length es1 = length es2 
      then unify' (ListPair.zip (es1, es2) @ eqs) 
      else NONE
  | unify' ((CON(s, es), VAR(x)) :: eqs) = unify' ((VAR x, CON(s, es)) :: eqs)
  | unify' ((VAR x, t) :: eqs) =
      if t = VAR x then unify' eqs 
      else if List.exists (fn y => x = y) (vars t) then NONE
      else case unify' (map (subst_eqn x t) eqs) of
          NONE => NONE
        | SOME theta => SOME (EXTEND(x, subst_expr_sub theta t, theta))

fun unify e1 e2 = unify' [(e1, e2)]
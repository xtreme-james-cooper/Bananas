
(* standard unification algorithm 
   we have a restricted variable/constructor language to unify over, which makes it much simpler
   we pay for it in the actual typechecker, though *)

type var = int

exception UnificationError of string

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

type 'a equation = 'a expression * 'a expression * string (* string is the error message if unification fails *)

fun subst_eqn x e' (e1, e2, s) = (subst_expr x e' e1, subst_expr x e' e2, s)

fun unify [] = EMPTY
  | unify ((CON(s, es1), CON(t, es2), errorMessage) :: eqs) =
      if s = t andalso length es1 = length es2 
      then unify (map (fn (x, y) => (x, y, errorMessage)) (ListPair.zip (es1, es2)) @ eqs) 
      else raise UnificationError errorMessage
  | unify ((CON(s, es), VAR(x), errorMessage) :: eqs) = unify ((VAR x, CON(s, es), errorMessage) :: eqs)
  | unify ((VAR x, t, errorMessage) :: eqs) =
      if t = VAR x then unify eqs 
      else if List.exists (fn y => x = y) (vars t) then raise UnificationError ("Occurs check at: " ^ errorMessage)
      else let val theta = unify (map (subst_eqn x t) eqs)
           in EXTEND(x, subst_expr_sub theta t, theta)
           end
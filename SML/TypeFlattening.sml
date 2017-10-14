
(* in order to make our unifier work for typechecking
   we need a way to compress a type into our restricted VAR/CON language
   these functions do so, and inflate it again at the other end *)

datatype flat_type = UNIT | VOID | TIMES | PLUS | ARROW | MU | IDF | CONSTF | TIMESF | PLUSF

fun flatten_type Unit           = CON(UNIT, []) 
  | flatten_type Void           = CON(VOID, [])
  | flatten_type (Poly n)       = VAR n (* polymorphic type variables are turned into unification variables *)
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

fun inflate_type (VAR x) = Poly x (* ununified variables pop out as polymorphic type variables *)
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

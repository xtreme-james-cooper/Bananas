
(* in order to make our unifier work for typechecking
   we need a way to compress a type into our restricted VAR/CON language
   these functions do so, and inflate it again at the other end *)

datatype flat_type = UNIT | VOID | TIMES | PLUS | ARROW | MU | IDF | CONSTF | TIMESF | PLUSF

fun flatten_type free Unit           = (CON(UNIT, []), free)
  | flatten_type free Void           = (CON(VOID, []), free)
(* polymorphic type variables are turned into fresh unification variables 
   but consistently, hence our somewhat wasteful way of generating new variables from a fresh count *)
  | flatten_type free (Poly n)       = (VAR(free + n), free + n + 1) 
  | flatten_type free (Prod(t1, t2)) = 
      let val (t1', free1) = flatten_type free t1 
          val (t2', free2) = flatten_type free t2
      in (CON(TIMES, [t1', t2']), Int.max(free1, free2))
      end
  | flatten_type free (Sum(t1, t2))  = 
      let val (t1', free1) = flatten_type free t1 
          val (t2', free2) = flatten_type free t2
      in (CON(PLUS, [t1', t2']), Int.max(free1, free2))
      end
  | flatten_type free (Func(t1, t2)) = 
      let val (t1', free1) = flatten_type free t1 
          val (t2', free2) = flatten_type free t2
      in (CON(ARROW, [t1', t2']), Int.max(free1, free2))
      end
  | flatten_type free (Fix F)        = 
      let val (f', free1) = flatten_funct free F 
      in (CON(MU, [f']), free1)
      end

and flatten_funct free Id              = (CON(IDF, []), free)
  | flatten_funct free (K t)           = 
      let val (t', free1) = flatten_type free t
      in (CON(CONSTF, [t']), free1)
      end
  | flatten_funct free (ProdF(f1, f2)) = 
      let val (f1', free1) = flatten_funct free f1 
          val (f2', free2) = flatten_funct free f2
      in (CON(TIMESF, [f1', f2']), Int.max(free1, free2))
      end
  | flatten_funct free (SumF(f1, f2))  = 
      let val (f1', free1) = flatten_funct free f1 
          val (f2', free2) = flatten_funct free f2
      in (CON(PLUSF, [f1', f2']), Int.max(free1, free2))
      end

fun apply_functor_flat free t Id              = (t, free)
  | apply_functor_flat free _ (K t')          = flatten_type free t'
  | apply_functor_flat free t (ProdF(f1, f2)) = 
      let val (t1', free1) = apply_functor_flat free t f1 
          val (t2', free2) = apply_functor_flat free t f2
      in (CON(TIMES, [t1', t2']), Int.max(free1, free2))
      end
  | apply_functor_flat free t (SumF(f1, f2))  = 
      let val (t1', free1) = apply_functor_flat free t f1 
          val (t2', free2) = apply_functor_flat free t f2
      in (CON(PLUS, [t1', t2']), Int.max(free1, free2))
      end

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

fun flat_to_string UNIT = "Unit"
  | flat_to_string VOID = "Void"
  | flat_to_string MU = "Mu"
  | flat_to_string TIMES = "Times"
  | flat_to_string PLUS = "Plus"
  | flat_to_string ARROW = "Arrow"
  | flat_to_string IDF = "Id"
  | flat_to_string CONSTF = "K" 
  | flat_to_string TIMESF = "TimesF"
  | flat_to_string PLUSF = "PlusF"

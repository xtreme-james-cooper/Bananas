
type name = string

datatype typ = 
  Void
| Unit
| Poly of int
| Prod of typ * typ
| Sum of typ * typ
| Func of typ * typ
| Fix of funct
and funct =
  Id
| K of typ
| ProdF of funct * funct
| SumF of funct * funct

datatype val_description = ValDesc of name * val_description list

datatype expr = 
  Proj1 | Proj2 | Duplicate | Pairwise of expr list * expr list
| Injl | Injr | Strip | Case of expr list * expr list
| Distribute
| Apply | Arrow of expr list * expr list
| Inj of name | Outj of name
| Cata of expr list * name | Ana of expr list * name
| Var of name | Const of val_description

datatype vall = 
  UnitV
| PairV of vall * vall
| InlV of vall | InrV of vall
| FunV of expr list
| InjV of name * vall 

datatype decl = 
  TypeDecl of name * (name * name list) list
| ExprDecl of name * expr list

datatype prog = Prog of decl list * expr list * val_description

fun typ_to_string Void = "0"
  | typ_to_string Unit = "1"
  | typ_to_string (Poly x) = "?" ^ Int.toString x
  | typ_to_string (Prod(t1, t2)) = "(" ^ typ_to_string t1 ^ " * " ^ typ_to_string t2 ^ ")"
  | typ_to_string (Sum(t1, t2)) = "(" ^ typ_to_string t1 ^ " + " ^ typ_to_string t2 ^ ")"
  | typ_to_string (Func(t1, t2)) = "(" ^ typ_to_string t1 ^ " => " ^ typ_to_string t2 ^ ")"
  | typ_to_string (Fix F) = "Mu " ^ funct_to_string F
and funct_to_string Id = "Id"
  | funct_to_string (K t) = "K " ^ typ_to_string t
  | funct_to_string (ProdF(f1, f2)) = "(" ^ funct_to_string f1 ^ " * " ^ funct_to_string f2 ^ ")"
  | funct_to_string (SumF(f1, f2)) = "(" ^ funct_to_string f1 ^ " + " ^ funct_to_string f2 ^ ")"

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

datatype expr = 
  Const of vall
| Proj1 | Proj2 | Duplicate | Pairwise of expr list * expr list
| Injl | Injr | Strip | Case of expr list * expr list
| Distribute
| Apply | Arrow of expr list * expr list
| Inj of name | Outj of name
| Cata of expr list * name | Ana of expr list * name
| Var of name
and vall = 
  UnitV
| PairV of vall * vall
| InlV of vall | InrV of vall
| FunV of expr list
| InjV of name * vall 

datatype decl = 
  TypeDecl of name * (name * name list) list
| ExprDecl of name * expr list

datatype prog = Prog of decl list * expr list * vall
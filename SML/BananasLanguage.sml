
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
  Identity | Const of vall | Comp of expr * expr
| Proj1 | Proj2 | Duplicate | Pairwise of expr * expr
| Injl | Injr | Strip | Case of expr * expr
| Distribute
| Apply | Arrow of expr * expr
| Inj of name | Outj of name
| Cata of expr * name | Ana of expr * name
| Var of name
and vall = 
  UnitV
| PairV of vall * vall
| InlV of vall | InrV of vall
| FunV of expr
| InjV of name * vall 

datatype decl = 
  TypeDecl of name * (name * name list) list
| ExprDecl of name * expr

datatype prog = Prog of decl list * expr * vall

type name = string

(* types and functors *)

datatype typ = 
  Void (* \<zero> *)
| Unit (* \<one> *)
| Poly of int (* slightly garbage. Used only for typechecking purposes *)
| Prod of typ * typ (* t1 \<otimes> t2 *)
| Sum of typ * typ (* t1 \<oplus> t2 *)
| Func of typ * typ (* t1 \<rightarrow> t2 *)
| Fix of name * funct (* \<mu> F *)
and funct =
  Id
| K of typ
| ProdF of funct * funct (* f1 \<Otimes> f2 *)
| SumF of funct * funct (* f1 \<Oplus> f2 *)

(* the result of applying a functor to a type, t \<star> F 
   for example, Nat \<star> ListF = Nat \<star> (K \<one> \<Oplus> (K A \<Otimes> Id)) = \<one> \<oplus> (A \<otimes> Nat) *) 
fun apply_functor_type t Id = t
  | apply_functor_type _ (K t') = t'
  | apply_functor_type t (ProdF(f1, f2)) = Prod(apply_functor_type t f1, apply_functor_type t f2)
  | apply_functor_type t (SumF(f1, f2)) = Sum(apply_functor_type t f1, apply_functor_type t f2)

(* how we represent inputted values
   constructor names followed by a (recursive) list of value arguments *)
datatype val_description = ValDesc of name * val_description list

(* our library of basis combinators *)
datatype expr = 
  Proj1 (* \<pi>\<^sub>1 *) | Proj2 (* \<pi>\<^sub>2 *) | Duplicate (* \<Theta> *) | Pairwise of expr list * expr list (* f \<parallel> g *)
| Injl (* \<iota>\<^sub>l *) | Injr (* \<iota>\<^sub>r *) | Strip (* \<Xi> *) | Case of expr list * expr list (* f \<bar> g *)
| Distribute (* \<sqsupset> *)
| Apply (* $ *) | Fun of expr list (* \<langle> f \<rangle> *) | Arrow of expr list * expr list (* g \<leftarrow> f *) 
| Uncurry of expr list (* \<flat> f *) | Curry of expr list (* \<sharp> f *)
| Inj of name (* \<succ>\<^sub>F *) | Outj of name (* \<prec>\<^sub>F *)
| Cata of expr list * name (* \<lparr> f \<rparr>\<^sub>F *) | Ana of expr list * name (* \<lbrakk> f \<rbrakk>\<^sub>F *)
| Var of name | Const of val_description | ConstV of vall (* last not available to users! *)

(* actual values never need to be depicted to the user! They're internal only *)
and vall = 
  UnitV
| PairV of vall * vall
| InlV of vall | InrV of vall
| FunV of expr list
| InjV of name * vall 

(* the result of applying a functor to an expr, e \<star> F 
   for example, \<pi>\<^sub>1 \<star> ListF = \<pi>\<^sub>1 \<star> (K \<one> \<Oplus> (K A \<Otimes> Id)) = [] \<bar> [[] \<parallel> [\<pi>\<^sub>1]] *) 
fun apply_functor_expr e Id = [e]
  | apply_functor_expr _ (K _) = []
  | apply_functor_expr e (ProdF(f1, f2)) = [Pairwise (apply_functor_expr e f1, apply_functor_expr e f2)]
  | apply_functor_expr e (SumF(f1, f2)) = [Case (apply_functor_expr e f1, apply_functor_expr e f2)]

(* derived combinators *)

fun tuple_pair e1 e2 = [Duplicate, Pairwise(e1, e2)] (* f \<triangle> g *)
fun case_strip el er = [Case(el, er), Strip] (* f \<nabla> g *)
fun predicate p = [Duplicate, Pairwise(p @ [Outj "Bool"], []), Distribute, Case([Proj2], [Proj2])] (* p? *)
val swap = tuple_pair [Proj2] [Proj1] (* \<bowtie> *)
val distribute_right = swap @ [Distribute, Case(swap, swap)] (* \<sqsubset> *)
val assoc_left = [Duplicate, Pairwise([Proj1, Proj1], [Pairwise([Proj2], [])])] (* \<supset> *)
val assoc_right = [Duplicate, Pairwise([Pairwise([], [Proj1])], [Proj2, Proj2])] (* \<subset> *)
fun if_expr p et ef = predicate p @ case_strip et ef (* et \<triangleleft> p \<triangleright> ef *)

(* declarations for (haskell-style sum-of-products) types and combinator chain expressions *)
datatype decl = 
  TypeDecl of name * (name * name list) list
| ValDecl of name * val_description
| ExprDecl of name * expr list

(* top-level program *)
datatype prog = Prog of decl list * expr list * val_description

(* debugging utilities *)

fun typ_to_string Void = "0"
  | typ_to_string Unit = "1"
  | typ_to_string (Poly x) = "?" ^ Int.toString x
  | typ_to_string (Prod(t1, t2)) = "(" ^ typ_to_string t1 ^ " * " ^ typ_to_string t2 ^ ")"
  | typ_to_string (Sum(t1, t2)) = "(" ^ typ_to_string t1 ^ " + " ^ typ_to_string t2 ^ ")"
  | typ_to_string (Func(t1, t2)) = "(" ^ typ_to_string t1 ^ " => " ^ typ_to_string t2 ^ ")"
  | typ_to_string (Fix (n, _)) = n
and funct_to_string Id = "Id"
  | funct_to_string (K t) = "K " ^ typ_to_string t
  | funct_to_string (ProdF(f1, f2)) = "(" ^ funct_to_string f1 ^ " * " ^ funct_to_string f2 ^ ")"
  | funct_to_string (SumF(f1, f2)) = "(" ^ funct_to_string f1 ^ " + " ^ funct_to_string f2 ^ ")"

fun val_to_string UnitV = "()"
  | val_to_string (PairV(v1, v2)) = "(" ^ val_to_string v1 ^ ", " ^ val_to_string v2 ^ ")"
  | val_to_string (InlV v) = "inl " ^ val_to_string v
  | val_to_string (InrV v) = "inr " ^ val_to_string v
  | val_to_string (FunV _) = "fn"
  | val_to_string (InjV(n, v)) = "[" ^ n ^ " " ^ val_to_string v ^ "]"
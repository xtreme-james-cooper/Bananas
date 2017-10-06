theory BananasLanguage
imports Main
begin

type_synonym name = string

datatype type = 
  Void ("\<zero>")
| Unit ("\<one>")
| Poly nat
| Prod type type (infixr "\<otimes>" 85)
| Sum type type (infixr "\<oplus>" 80)
| Func type type (infixr "\<hookrightarrow>" 70)
| Fix funct ("\<mu>")
and funct =
  Id
| K type
| ProdF funct funct (infixr "\<Otimes>" 85)
| SumF funct funct (infixr "\<Oplus>" 80)

datatype expr = 
  Identity ("\<epsilon>") | Const val ("\<kappa>") | Comp expr expr (infixr "\<cdot>" 65)
| Proj1 ("\<pi>\<^sub>1") | Proj2 ("\<pi>\<^sub>2") | Duplicate ("\<Theta>") | Pairwise expr expr (infixr "\<parallel>" 85)
| Injl ("\<iota>\<^sub>l") | Injr ("\<iota>\<^sub>r") | Strip ("\<Xi>") |  Case expr expr (infixr "\<bar>" 80)
| Distribute ("\<rhd>")
| Apply ("$") | Arrow expr expr (infixl "\<leftarrow>" 70)
| Inj name ("\<succ>\<^bsub>_\<^esub>") | Outj name ("\<prec>\<^bsub>_\<^esub>")
| Cata expr name ("\<lparr> _ \<rparr>\<^bsub>_\<^esub>") | Ana expr name ("\<lbrakk> _ \<rbrakk>\<^bsub>_\<^esub>")
| Var name
and val = 
  UnitV
| PairV val val 
| InlV val | InrV val
| FunV expr
| InjV name val 

datatype decl = 
  TypeDecl name "(name \<times> name list) list"
| ValDecl name val
| ExprDecl name expr

primrec binders\<^sub>d :: "decl \<Rightarrow> name set" where
  "binders\<^sub>d (TypeDecl x cts) = insert x (fst ` set cts)"
| "binders\<^sub>d (ValDecl x v) = {x}"
| "binders\<^sub>d (ExprDecl x e) = {x}"

fun binders :: "decl list \<Rightarrow> name set" where
  "binders \<Delta> = \<Union> (binders\<^sub>d ` set \<Delta>)"

datatype prog = Prog "decl list" expr val

end
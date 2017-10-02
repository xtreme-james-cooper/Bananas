theory Typechecking
imports BananasLanguage Unification
begin

datatype flat_type = UNIT| TIMES | PLUS | ARROW | MU | IDF | CONSTF | TIMESF | PLUSF

primrec flatten_type :: "type \<Rightarrow> flat_type expression"
    and flatten_funct :: "funct \<Rightarrow> flat_type expression" where
  "flatten_type \<one> = CON UNIT []"
| "flatten_type (t\<^sub>1 \<otimes> t\<^sub>2) = CON TIMES [flatten_type t\<^sub>1, flatten_type t\<^sub>2]"
| "flatten_type (t\<^sub>1 \<oplus> t\<^sub>2) = CON PLUS [flatten_type t\<^sub>1, flatten_type t\<^sub>2]"
| "flatten_type (t\<^sub>1 \<hookrightarrow> t\<^sub>2) = CON ARROW [flatten_type t\<^sub>1, flatten_type t\<^sub>2]"
| "flatten_type (\<mu> F) = CON MU [flatten_funct F]"

| "flatten_funct Id = CON IDF []"
| "flatten_funct (K t) = CON CONSTF [flatten_type t]"
| "flatten_funct (f\<^sub>1 \<Otimes> f\<^sub>2) = CON TIMESF [flatten_funct f\<^sub>1, flatten_funct f\<^sub>2]"
| "flatten_funct (f\<^sub>1 \<Oplus> f\<^sub>2) = CON PLUSF [flatten_funct f\<^sub>1, flatten_funct f\<^sub>2]"

primrec apply_functor_flat :: "flat_type expression \<Rightarrow> funct \<Rightarrow> flat_type expression" where
  "apply_functor_flat t Id = t"
| "apply_functor_flat t (K t') = flatten_type t'"
| "apply_functor_flat t (f\<^sub>1 \<Otimes> f\<^sub>2) = CON TIMES [apply_functor_flat t f\<^sub>1, apply_functor_flat t f\<^sub>2]"
| "apply_functor_flat t (f\<^sub>1 \<Oplus> f\<^sub>2) = CON PLUS [apply_functor_flat t f\<^sub>1, apply_functor_flat t f\<^sub>2]"

fun inflate_type :: "flat_type expression \<Rightarrow> type option"
and inflate_funct :: "flat_type expression \<Rightarrow> funct option" where
  "inflate_type (VAR x) = None"
| "inflate_type (CON c []) = (if c = UNIT then Some \<one> else None)"
| "inflate_type (CON c [F]) = 
    Option.bind (inflate_funct F) (\<lambda>F'. 
      (if c = MU then Some (\<mu> F') else None))"
| "inflate_type (CON c [t\<^sub>1, t\<^sub>2]) = 
    Option.bind (inflate_type t\<^sub>1) (\<lambda>t\<^sub>1'.
      Option.bind (inflate_type t\<^sub>2) (\<lambda>t\<^sub>2'. case c of
          TIMES \<Rightarrow> Some (t\<^sub>1' \<otimes> t\<^sub>2')
        | PLUS \<Rightarrow> Some (t\<^sub>1' \<oplus> t\<^sub>2')
        | ARROW \<Rightarrow> Some (t\<^sub>1' \<hookrightarrow> t\<^sub>2')
        | _ \<Rightarrow> None))"
| "inflate_type (CON c _) = None"

| "inflate_funct (VAR x) = None"
| "inflate_funct (CON c []) = (if c = IDF then Some Id else None)"
| "inflate_funct (CON c [t]) = 
    Option.bind (inflate_type t) (\<lambda>t'. 
      if c = CONSTF then Some (K t') else None)"
| "inflate_funct (CON c [f\<^sub>1, f\<^sub>2]) = 
    Option.bind (inflate_funct f\<^sub>1) (\<lambda>f\<^sub>1'.
      Option.bind (inflate_funct f\<^sub>2) (\<lambda>f\<^sub>2'. case c of
          TIMESF \<Rightarrow> Some (f\<^sub>1' \<Otimes> f\<^sub>2')
        | PLUSF \<Rightarrow> Some (f\<^sub>1' \<Oplus> f\<^sub>2')
        | _ \<Rightarrow> None))"
| "inflate_funct (CON c _) = None"

primrec assemble_constraints\<^sub>e :: "flat_type expression \<Rightarrow> flat_type expression \<Rightarrow> var \<Rightarrow> expr \<Rightarrow> 
      flat_type equation list \<times> var" 
    and assemble_constraints\<^sub>v :: "flat_type expression \<Rightarrow> var \<Rightarrow> val \<Rightarrow> 
      flat_type equation list \<times> var" where
  "assemble_constraints\<^sub>e x y free \<epsilon> = ([(x, y)], free)"
| "assemble_constraints\<^sub>e x y free (\<kappa> v) = assemble_constraints\<^sub>v y (Suc free) v"
| "assemble_constraints\<^sub>e x y free (f\<^sub>1 \<cdot> f\<^sub>2) = (
    let (cs\<^sub>1, free') = assemble_constraints\<^sub>e x (VAR free) (Suc free) f\<^sub>1
    in let (cs\<^sub>2, free'') = assemble_constraints\<^sub>e (VAR free) y free' f\<^sub>2
    in (cs\<^sub>1 @ cs\<^sub>2, free''))"
| "assemble_constraints\<^sub>e x y free \<pi>\<^sub>1 = ([(x, CON TIMES [y, VAR free])], Suc free)"
| "assemble_constraints\<^sub>e x y free \<pi>\<^sub>2 = ([(x, CON TIMES [VAR free, y])], Suc free)"
| "assemble_constraints\<^sub>e x y free \<Theta> = ([(y, CON TIMES [x, x])], free)"
| "assemble_constraints\<^sub>e x y free (f\<^sub>1 \<parallel> f\<^sub>2) = (
    let a = VAR free in let b = VAR (Suc free) 
    in let (cs\<^sub>1, free') = assemble_constraints\<^sub>e a b (Suc (Suc free)) f\<^sub>1
    in let c = VAR free' in let d = VAR (Suc free') 
    in let (cs\<^sub>2, free'') = assemble_constraints\<^sub>e c d (Suc (Suc free')) f\<^sub>2
    in ((x, CON TIMES [a, c]) # (y, CON TIMES [b, d]) # cs\<^sub>1 @ cs\<^sub>2, free''))"
| "assemble_constraints\<^sub>e x y free \<iota>\<^sub>l = ([(y, CON PLUS [x, VAR free])], Suc free)"
| "assemble_constraints\<^sub>e x y free \<iota>\<^sub>r = ([(y, CON PLUS [VAR free, x])], Suc free)"
| "assemble_constraints\<^sub>e x y free \<Xi> = ([(x, CON PLUS [y, y])], free)"
| "assemble_constraints\<^sub>e x y free (f\<^sub>1 \<bar> f\<^sub>2) = (
    let a = VAR free in let b = VAR (Suc free) 
    in let (cs\<^sub>1, free') = assemble_constraints\<^sub>e a b (Suc (Suc free)) f\<^sub>1
    in let c = VAR free' in let d = VAR (Suc free') 
    in let (cs\<^sub>2, free'') = assemble_constraints\<^sub>e c d (Suc (Suc free')) f\<^sub>2
    in ((x, CON PLUS [a, c]) # (y, CON PLUS [b, d]) # cs\<^sub>1 @ cs\<^sub>2, free''))"
| "assemble_constraints\<^sub>e x y free \<rhd> = (
    let a = VAR free in let b = VAR (Suc free) in let c = VAR (Suc (Suc free))
    in ([(x, CON TIMES [CON PLUS [a, b], c]), (y, CON PLUS [CON TIMES [a, c], CON TIMES [b, c]])], 
        Suc (Suc (Suc free))))"
| "assemble_constraints\<^sub>e x y free $ = 
    ([(x, CON TIMES [CON ARROW [VAR free, y], VAR free])], Suc free)"
| "assemble_constraints\<^sub>e x y free (f\<^sub>1 \<leftarrow> f\<^sub>2) = (
    let a = VAR free in let b = VAR (Suc free) 
    in let (cs\<^sub>1, free') = assemble_constraints\<^sub>e a b (Suc (Suc free)) f\<^sub>1
    in let c = VAR free' in let d = VAR (Suc free') 
    in let (cs\<^sub>2, free'') = assemble_constraints\<^sub>e c d (Suc (Suc free')) f\<^sub>2
    in ((x, CON ARROW [b, c]) # (y, CON PLUS [a, d]) # cs\<^sub>1 @ cs\<^sub>2, free''))"
| "assemble_constraints\<^sub>e x y free \<succ>\<^bsub>F\<^esub> = 
    ([(x, flatten_type (\<mu> F \<star> F)), (y, flatten_type (\<mu> F))], free)"
| "assemble_constraints\<^sub>e x y free \<prec>\<^bsub>F\<^esub> = 
    ([(x, flatten_type (\<mu> F)), (x, flatten_type (\<mu> F \<star> F))], free)"
| "assemble_constraints\<^sub>e x y free \<lparr> f \<rparr>\<^bsub>F\<^esub> = (
    let (cs, free') = assemble_constraints\<^sub>e (apply_functor_flat y F) y free f
    in ((x, CON MU [flatten_funct F]) # cs, free'))"
| "assemble_constraints\<^sub>e x y free \<lbrakk> f \<rbrakk>\<^bsub>F\<^esub> = (
    let (cs, free') = assemble_constraints\<^sub>e x (apply_functor_flat x F) free f
    in ((y, CON MU [flatten_funct F]) # cs, free'))"

| "assemble_constraints\<^sub>v x free UnitV = ([(x, CON UNIT [])], free)"
| "assemble_constraints\<^sub>v x free (PairV v\<^sub>1 v\<^sub>2) = (
    let (cs\<^sub>1, free') = assemble_constraints\<^sub>v (VAR free) (Suc free) v\<^sub>1
    in let (cs\<^sub>2, free'') = assemble_constraints\<^sub>v (VAR free') (Suc free') v\<^sub>2
    in ((x, CON TIMES [VAR free, VAR free']) # cs\<^sub>1 @ cs\<^sub>2, free''))"
| "assemble_constraints\<^sub>v x free (InlV v) = (
    let (cs, free') = assemble_constraints\<^sub>v (VAR free) (Suc free) v
    in ((x, CON PLUS [VAR free, VAR free']) # cs, Suc free'))"
| "assemble_constraints\<^sub>v x free (InrV v) = (
    let (cs, free') = assemble_constraints\<^sub>v (VAR free) (Suc free) v
    in ((x, CON PLUS [VAR free', VAR free]) # cs, Suc free'))"
| "assemble_constraints\<^sub>v x free (FunV f) = (
    let (cs, free') = assemble_constraints\<^sub>e (VAR free) (VAR (Suc free)) (Suc (Suc free)) f
    in ((x, CON ARROW [VAR free, VAR (Suc free)]) # cs, free'))"
| "assemble_constraints\<^sub>v x free (InjV F v) = (
    let (cs, free') = assemble_constraints\<^sub>v (flatten_type (\<mu> F \<star> F)) free v
    in ((x, flatten_type (\<mu> F)) # cs, free'))"

fun typecheck :: "expr \<Rightarrow> (type \<times> type) option" where
  "typecheck e = 
    Option.bind (unify' (fst (assemble_constraints\<^sub>e (VAR 0) (VAR 1) 2 e))) (\<lambda>\<phi>. 
      Option.bind (inflate_type (\<phi> 0)) (\<lambda>t\<^sub>1. 
        Option.bind (inflate_type (\<phi> 1)) (\<lambda>t\<^sub>2. 
          Some (t\<^sub>1, t\<^sub>2))))"

end
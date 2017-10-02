theory Typechecking
imports BananasLanguage Unification
begin

fun typechecker\<^sub>e' :: "var \<Rightarrow> expr \<Rightarrow> flat_type expression \<Rightarrow> (flat_type expression \<times> var) option" 
and typechecker\<^sub>v' :: "var \<Rightarrow> val \<Rightarrow> (flat_type expression \<times> var) option" where
  "typechecker\<^sub>e' x \<epsilon> t = Some (t, x)"
| "typechecker\<^sub>e' x (\<kappa> v) t = typechecker\<^sub>v v"
| "typechecker\<^sub>e' x (f \<cdot> g) t = undefined"
| "typechecker\<^sub>e' x \<pi>\<^sub>1 (CON TIMES [t\<^sub>1, t\<^sub>2]) = Some t\<^sub>1"
| "typechecker\<^sub>e' x \<pi>\<^sub>1 _ = None"
| "typechecker\<^sub>e' x \<pi>\<^sub>2 (CON TIMES [t\<^sub>1, t\<^sub>2]) = Some t\<^sub>2"
| "typechecker\<^sub>e' x \<pi>\<^sub>2 _ = None"
| "typechecker\<^sub>e' x \<Theta> t = Some (CON TIMES [t, t])"
| "typechecker\<^sub>e' x (f\<^sub>1 \<parallel> f\<^sub>2) (CON PLUS [t\<^sub>1, t\<^sub>2]) = undefined"
| "typechecker\<^sub>e' x (f\<^sub>1 \<parallel> f\<^sub>2) _ = None"
| "typechecker\<^sub>e' x \<iota>\<^sub>l t = Some (CON PLUS [t, VAR x])"
| "typechecker\<^sub>e' x \<iota>\<^sub>r t = Some (CON PLUS [VAR x, t])"
| "typechecker\<^sub>e' x \<Xi> (CON PLUS [t\<^sub>1, t\<^sub>2]) = (if t\<^sub>1 = t\<^sub>2 then Some (Base t\<^sub>1) else None)"
| "typechecker\<^sub>e' x \<Xi> _ = None"
| "typechecker\<^sub>e' x (f\<^sub>1 \<bar> f\<^sub>2) (CON PLUS [t\<^sub>1, t\<^sub>2]) = undefined"
| "typechecker\<^sub>e' x (f\<^sub>1 \<bar> f\<^sub>2) _ = None"
| "typechecker\<^sub>e' x \<rhd> (CON TIMES [CON PLUS [t\<^sub>1, t\<^sub>2], t\<^sub>3]) = Some (Base (t\<^sub>1 \<otimes> t\<^sub>3 \<oplus> t\<^sub>2 \<otimes> t\<^sub>3))"
| "typechecker\<^sub>e' x \<rhd> _ = None"
| "typechecker\<^sub>e' x $ ((t\<^sub>1 \<hookrightarrow> t\<^sub>2) \<otimes> t\<^sub>3) = (if t\<^sub>1 = t\<^sub>3 then Some (Base t\<^sub>2) else None)"
| "typechecker\<^sub>e' x $ _ = None"
| "typechecker\<^sub>e' x (f\<^sub>1 \<leftarrow> f\<^sub>2) (t\<^sub>2 \<hookrightarrow> t\<^sub>3) = undefined"
| "typechecker\<^sub>e' x (f\<^sub>1 \<leftarrow> f\<^sub>2) _ = None"
| "typechecker\<^sub>e' x \<succ>\<^bsub>F\<^esub> t = (if t = \<mu> F \<star> F then Some (Base (\<mu> F)) else None)"
| "typechecker\<^sub>e' x \<prec>\<^bsub>F\<^esub> t = (if t = \<mu> F then Some (Base (\<mu> F \<star> F)) else None)"
| "typechecker\<^sub>e' x \<lparr> f \<rparr>\<^bsub>F\<^esub> t = (if t = \<mu> F then typechecker\<^sub>e f (t \<star> F) else None)"
| "typechecker\<^sub>e' x \<lbrakk> f \<rbrakk>\<^bsub>F\<^esub> t = Option.bind (typechecker\<^sub>e f t) (\<lambda>tt. if tt = Base (t \<star> F) then Some (Base (\<mu> F)) else None)"

| "typechecker\<^sub>v' x UnitV = Some (CON UNIT [], x)"
| "typechecker\<^sub>v' x (PairV v\<^sub>1 v\<^sub>2) = 
    Option.bind (typechecker\<^sub>v v\<^sub>1) (\<lambda>t\<^sub>1. 
      Option.bind (typechecker\<^sub>v v\<^sub>2) (\<lambda>t\<^sub>2. 
        undefined))"
| "typechecker\<^sub>v' x (InlV v) = 
    Option.bind (typechecker\<^sub>v' x v) (\<lambda>(t, x'). Some (CON PLUS [t, VAR x'], Suc x'))"
| "typechecker\<^sub>v' x (InrV v) = 
    Option.bind (typechecker\<^sub>v' x v) (\<lambda>(t, x'). Some (CON PLUS [VAR x', t], Suc x'))"
| "typechecker\<^sub>v' x (FunV f) = undefined"
| "typechecker\<^sub>v' x (InjV F v) = 
    Option.bind (typechecker\<^sub>v' x v) (\<lambda>(t, x'). 
      if t = (\<mu> F \<star> F) then Some (Base (\<mu> F)) else None)"

end
theory Typechecking
imports BananasLanguage
begin

fun typechecker\<^sub>e :: "expr \<Rightarrow> type \<Rightarrow> type option" 
and typechecker\<^sub>v :: "val \<Rightarrow> type option" where
  "typechecker\<^sub>e \<epsilon> t = Some (Base t)"
| "typechecker\<^sub>e (\<kappa> v) t = typechecker\<^sub>v v"
| "typechecker\<^sub>e (f \<cdot> g) t = undefined"
| "typechecker\<^sub>e \<pi>\<^sub>1 (t\<^sub>1 \<otimes> t\<^sub>2) = Some (Base t\<^sub>1)"
| "typechecker\<^sub>e \<pi>\<^sub>1 _ = None"
| "typechecker\<^sub>e \<pi>\<^sub>2 (t\<^sub>1 \<otimes> t\<^sub>2) = Some (Base t\<^sub>2)"
| "typechecker\<^sub>e \<pi>\<^sub>2 _ = None"
| "typechecker\<^sub>e \<Theta> t = Some (Base (t \<otimes> t))"
| "typechecker\<^sub>e (f\<^sub>1 \<parallel> f\<^sub>2) (t\<^sub>1 \<otimes> t\<^sub>2) = undefined"
| "typechecker\<^sub>e (f\<^sub>1 \<parallel> f\<^sub>2) _ = None"
| "typechecker\<^sub>e \<iota>\<^sub>l t = Some (Missing (\<lambda>tt. Base (t \<oplus> tt)))"
| "typechecker\<^sub>e \<iota>\<^sub>r t = Some (Missing (\<lambda>tt. Base (tt \<oplus> t)))"
| "typechecker\<^sub>e \<Xi> (t\<^sub>1 \<oplus> t\<^sub>2) = (if t\<^sub>1 = t\<^sub>2 then Some (Base t\<^sub>1) else None)"
| "typechecker\<^sub>e \<Xi> _ = None"
| "typechecker\<^sub>e \<rhd> ((t\<^sub>1 \<oplus> t\<^sub>2) \<otimes> t\<^sub>3) = Some (Base (t\<^sub>1 \<otimes> t\<^sub>3 \<oplus> t\<^sub>2 \<otimes> t\<^sub>3))"
| "typechecker\<^sub>e \<rhd> _ = None"
| "typechecker\<^sub>e $ ((t\<^sub>1 \<hookrightarrow> t\<^sub>2) \<otimes> t\<^sub>3) = (if t\<^sub>1 = t\<^sub>3 then Some (Base t\<^sub>2) else None)"
| "typechecker\<^sub>e $ _ = None"
| "typechecker\<^sub>e (f\<^sub>1 \<bar> f\<^sub>2) (t\<^sub>1 \<oplus> t\<^sub>2) = undefined"
| "typechecker\<^sub>e (f\<^sub>1 \<bar> f\<^sub>2) _ = None"
| "typechecker\<^sub>e (f\<^sub>1 \<leftarrow> f\<^sub>2) (t\<^sub>2 \<hookrightarrow> t\<^sub>3) = undefined"
| "typechecker\<^sub>e (f\<^sub>1 \<leftarrow> f\<^sub>2) _ = None"
| "typechecker\<^sub>e \<succ>\<^bsub>F\<^esub> t = (if t = \<mu> F \<star> F then Some (Base (\<mu> F)) else None)"
| "typechecker\<^sub>e \<prec>\<^bsub>F\<^esub> t = (if t = \<mu> F then Some (Base (\<mu> F \<star> F)) else None)"
| "typechecker\<^sub>e \<lparr> f \<rparr>\<^bsub>F\<^esub> t = (if t = \<mu> F then typechecker\<^sub>e f (t \<star> F) else None)"
| "typechecker\<^sub>e \<lbrakk> f \<rbrakk>\<^bsub>F\<^esub> t = Option.bind (typechecker\<^sub>e f t) (\<lambda>tt. if tt = Base (t \<star> F) then Some (Base (\<mu> F)) else None)"

| "typechecker\<^sub>v UnitV = Some (Base \<one>)"
| "typechecker\<^sub>v (PairV v\<^sub>1 v\<^sub>2) = 
    Option.bind (typechecker\<^sub>v v\<^sub>1) (\<lambda>t\<^sub>1. 
      Option.bind (typechecker\<^sub>v v\<^sub>2) (\<lambda>t\<^sub>2. 
        undefined))"
| "typechecker\<^sub>v (InlV v) = Option.bind (typechecker\<^sub>v v) (\<lambda>t. undefined)"
| "typechecker\<^sub>v (InrV v) = Option.bind (typechecker\<^sub>v v) (\<lambda>t. undefined)"
| "typechecker\<^sub>v (FunV f) = undefined"
| "typechecker\<^sub>v (InjV F v) = 
    Option.bind (typechecker\<^sub>v v) (\<lambda>t. 
      if t = Base (\<mu> F \<star> F) then Some (Base (\<mu> F)) else None)"

end
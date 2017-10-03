theory Unification
imports Main
begin

type_synonym var = nat

datatype 'a expression =
  VAR var
| CON 'a "'a expression list" 

fun vars :: "'a expression \<Rightarrow> var set" where
  "vars (VAR x) = {x}"
| "vars (CON s es) = \<Union> (vars ` set es)"

datatype 'a substitution = 
  EMPTY
| EXTEND var "'a expression" "'a substitution"

primrec subst\<^sub>e :: "var \<Rightarrow> 'a expression \<Rightarrow> 'a expression \<Rightarrow> 'a expression"  where
  "subst\<^sub>e x e' (VAR y) = (if x = y then e' else VAR y)"
| "subst\<^sub>e x e' (CON s es) = CON s (map (subst\<^sub>e x e') es)"

primrec subst\<^sub>\<Theta> :: "'a substitution \<Rightarrow> var \<Rightarrow> 'a expression" where
  "subst\<^sub>\<Theta> EMPTY x = VAR x"
| "subst\<^sub>\<Theta> (EXTEND y e \<Theta>) x = (if x = y then e else subst\<^sub>e y e (subst\<^sub>\<Theta> \<Theta> x))"

primrec subst\<^sub>e\<^sub>\<Theta> :: "'a substitution \<Rightarrow> 'a expression \<Rightarrow> 'a expression" where
  "subst\<^sub>e\<^sub>\<Theta> \<Theta> (VAR x) = subst\<^sub>\<Theta> \<Theta> x"
| "subst\<^sub>e\<^sub>\<Theta> \<Theta> (CON s es) = CON s (map (subst\<^sub>e\<^sub>\<Theta> \<Theta>) es)"

type_synonym 'a equation = "'a expression \<times> 'a expression"

primrec subst\<^sub>e\<^sub>q\<^sub>n :: "var \<Rightarrow> 'a expression \<Rightarrow> 'a equation \<Rightarrow> 'a equation" where
  "subst\<^sub>e\<^sub>q\<^sub>n x e' (e\<^sub>1, e\<^sub>2) = (subst\<^sub>e x e' e\<^sub>1, subst\<^sub>e x e' e\<^sub>2)"

primrec subst\<^sub>e\<^sub>q\<^sub>n\<^sub>s :: "var \<Rightarrow> 'a expression \<Rightarrow> 'a equation list \<Rightarrow> 'a equation list" where
  "subst\<^sub>e\<^sub>q\<^sub>n\<^sub>s x e' [] = []"
| "subst\<^sub>e\<^sub>q\<^sub>n\<^sub>s x e' (eq # eqs) = subst\<^sub>e\<^sub>q\<^sub>n x e' eq # subst\<^sub>e\<^sub>q\<^sub>n\<^sub>s x e' eqs"

function unify' :: "'a equation list \<Rightarrow> 'a substitution option" where
  "unify' [] = Some EMPTY"
| "unify' ((CON s es\<^sub>1, CON t es\<^sub>2) # eqs) = (
    if s = t \<and> length es\<^sub>1 = length es\<^sub>2 then unify' (zip es\<^sub>1 es\<^sub>2 @ eqs) 
    else None)"
| "unify' ((CON s es, VAR x) # eqs) = unify' ((VAR x, CON s es) # eqs)"
| "unify' ((VAR x, t) # eqs) = (
    if t = VAR x then unify' eqs 
    else if x \<in> vars t then None
    else case unify' (subst\<^sub>e\<^sub>q\<^sub>n\<^sub>s x t eqs) of
        None \<Rightarrow> None
      | Some \<Theta> \<Rightarrow> Some (EXTEND x (subst\<^sub>e\<^sub>\<Theta> \<Theta> t) \<Theta>))"
  by pat_completeness auto

definition unify :: "'a expression \<Rightarrow> 'a expression \<Rightarrow> 'a substitution option" where
  "unify e\<^sub>1 e\<^sub>2 = unify' [(e\<^sub>1, e\<^sub>2)]"

(* unification termination *)

(* useless function, useful induction pattern: expression_complete.induct *)
fun expression_complete :: "'a expression \<Rightarrow> bool" where
  "expression_complete (VAR y) = True" 
| "expression_complete (CON s []) = True" 
| "expression_complete (CON s (e # es)) = (expression_complete e \<and> expression_complete (CON s es))" 

(* useless function, useful induction pattern: two_lists.induct *)
fun two_lists :: "'a list \<Rightarrow> 'b list \<Rightarrow> bool" where
  "two_lists [] [] = True"
| "two_lists [] (b # bs) = True"
| "two_lists (a # as) [] = True"
| "two_lists (a # as) (b # bs) = two_lists as bs"

fun vars_first :: "'a equation list \<Rightarrow> nat" where
  "vars_first [] = 0"
| "vars_first ((VAR x, t) # eqs) = 1"
| "vars_first ((CON s es, t) # eqs) = 2"

primrec cons :: "'a expression \<Rightarrow> nat"
    and conss :: "'a expression list \<Rightarrow> nat" where
  "cons (VAR x) = 0"
| "cons (CON s es) = Suc (conss es)"
| "conss [] = 0"
| "conss (e # es) = cons e + conss es"

primrec vars\<^sub>e\<^sub>q\<^sub>n :: "'a equation \<Rightarrow> var set" where
  "vars\<^sub>e\<^sub>q\<^sub>n (e\<^sub>1, e\<^sub>2) = vars e\<^sub>1 \<union> vars e\<^sub>2"

primrec vars\<^sub>e\<^sub>q\<^sub>n\<^sub>s :: "'a equation list \<Rightarrow> var set" where
  "vars\<^sub>e\<^sub>q\<^sub>n\<^sub>s [] = {}"
| "vars\<^sub>e\<^sub>q\<^sub>n\<^sub>s (eq # eqs) = vars\<^sub>e\<^sub>q\<^sub>n eq \<union> vars\<^sub>e\<^sub>q\<^sub>n\<^sub>s eqs"

primrec cons\<^sub>e\<^sub>q\<^sub>n :: "'a equation \<Rightarrow> nat" where
  "cons\<^sub>e\<^sub>q\<^sub>n (e\<^sub>1, e\<^sub>2) = cons e\<^sub>1 + cons e\<^sub>2"

primrec cons\<^sub>e\<^sub>q\<^sub>n\<^sub>s :: "'a equation list \<Rightarrow> nat" where
  "cons\<^sub>e\<^sub>q\<^sub>n\<^sub>s [] = 0"
| "cons\<^sub>e\<^sub>q\<^sub>n\<^sub>s (eq # eqs) = cons\<^sub>e\<^sub>q\<^sub>n eq + cons\<^sub>e\<^sub>q\<^sub>n\<^sub>s eqs"

lemma [simp]: "finite (vars t)"
  by (induction t rule: expression_complete.induct) simp_all

lemma [simp]: "x \<notin> vars t \<Longrightarrow> vars (subst\<^sub>e x t e) = 
    (if x \<in> vars e then vars e - {x} \<union> vars t else vars e - {x})"
  by (induction e rule: expression_complete.induct) auto

lemma [simp]: "x \<notin> vars e \<Longrightarrow> subst\<^sub>e x t e = e"
  by (induction e rule: expression_complete.induct) simp_all

lemma [simp]: "vars\<^sub>e\<^sub>q\<^sub>n\<^sub>s (eqs @ eqs') = vars\<^sub>e\<^sub>q\<^sub>n\<^sub>s eqs \<union> vars\<^sub>e\<^sub>q\<^sub>n\<^sub>s eqs'"
  by (induction eqs arbitrary: eqs') auto

lemma [simp]: "length es1 = length es2 \<Longrightarrow> vars\<^sub>e\<^sub>q\<^sub>n\<^sub>s (zip es1 es2) = \<Union> (vars ` set (es1 @ es2))"
  by (induction es1 es2 rule: two_lists.induct) auto

lemma [simp]: "cons\<^sub>e\<^sub>q\<^sub>n\<^sub>s (eqs @ eqs') = cons\<^sub>e\<^sub>q\<^sub>n\<^sub>s eqs + cons\<^sub>e\<^sub>q\<^sub>n\<^sub>s eqs'"
  by (induction eqs arbitrary: eqs') auto

lemma [simp]: "length es1 = length es2 \<Longrightarrow> cons\<^sub>e\<^sub>q\<^sub>n\<^sub>s (zip es1 es2) = conss es1 + conss es2"
  by (induction es1 es2 rule: two_lists.induct) auto

lemma [simp]: "finite (vars\<^sub>e\<^sub>q\<^sub>n eq)"
  by (induction eq) simp_all

lemma [simp]: "finite (vars\<^sub>e\<^sub>q\<^sub>n\<^sub>s eqs)"
  by (induction eqs) simp_all

lemma [simp]: "x \<notin> vars t \<Longrightarrow> vars\<^sub>e\<^sub>q\<^sub>n (subst\<^sub>e\<^sub>q\<^sub>n x t eq) = 
    (if x \<in> vars\<^sub>e\<^sub>q\<^sub>n eq then vars\<^sub>e\<^sub>q\<^sub>n eq - {x} \<union> vars t else vars\<^sub>e\<^sub>q\<^sub>n eq - {x})"
  by (induction eq) auto

lemma unfold_vars_subst\<^sub>e\<^sub>q\<^sub>n\<^sub>s: "x \<notin> vars t \<Longrightarrow> vars\<^sub>e\<^sub>q\<^sub>n\<^sub>s (subst\<^sub>e\<^sub>q\<^sub>n\<^sub>s x t eqs) = 
    (if x \<in> vars\<^sub>e\<^sub>q\<^sub>n\<^sub>s eqs then vars\<^sub>e\<^sub>q\<^sub>n\<^sub>s eqs - {x} \<union> vars t else vars\<^sub>e\<^sub>q\<^sub>n\<^sub>s eqs - {x})"
  by (induction eqs) auto

lemma [simp]: "x \<notin> vars t \<Longrightarrow> vars\<^sub>e\<^sub>q\<^sub>n\<^sub>s (subst\<^sub>e\<^sub>q\<^sub>n\<^sub>s x t eqs) \<subset> insert x (vars t \<union> vars\<^sub>e\<^sub>q\<^sub>n\<^sub>s eqs)"
  by (auto simp add: unfold_vars_subst\<^sub>e\<^sub>q\<^sub>n\<^sub>s)

lemma [simp]: "x \<notin> vars t \<Longrightarrow> 
    card (vars\<^sub>e\<^sub>q\<^sub>n\<^sub>s (subst\<^sub>e\<^sub>q\<^sub>n\<^sub>s x t eqs)) < card (insert x (vars t \<union> vars\<^sub>e\<^sub>q\<^sub>n\<^sub>s eqs))"
  by (simp add: psubset_card_mono)

lemma [simp]: "card (vars\<^sub>e\<^sub>q\<^sub>n\<^sub>s eqs) < card (insert x (vars\<^sub>e\<^sub>q\<^sub>n\<^sub>s eqs)) \<or> 
    card (vars\<^sub>e\<^sub>q\<^sub>n\<^sub>s eqs) = card (insert x (vars\<^sub>e\<^sub>q\<^sub>n\<^sub>s eqs))"
  by (cases "x \<in> vars\<^sub>e\<^sub>q\<^sub>n\<^sub>s eqs") (simp_all add: insert_absorb)

termination unify'
  by (relation "measures [card o vars\<^sub>e\<^sub>q\<^sub>n\<^sub>s, cons\<^sub>e\<^sub>q\<^sub>n\<^sub>s, length, vars_first]") simp_all

end
theory CombinatorLaws
imports BananasLanguage
begin

(* kludged in order to deal with mismatching domains - particularly \<epsilon>*)
definition expression_equality :: "expr \<Rightarrow> expr \<Rightarrow> bool" (infix "\<simeq>" 50) where
  "e\<^sub>1 \<simeq> e\<^sub>2 = ((\<forall>v v'. (v ~ e\<^sub>1 \<leadsto> v') \<longrightarrow> (v ~ e\<^sub>2 \<leadsto> v')) \<or> (\<forall>v v'. (v ~ e\<^sub>2 \<leadsto> v') \<longrightarrow> (v ~ e\<^sub>1 \<leadsto> v')))"

(* helper lemmas *)

lemma [elim]: "v ~ (e\<^sub>1 \<cdot> e\<^sub>2) \<cdot> e\<^sub>3 \<leadsto> v' \<Longrightarrow> v ~ e\<^sub>1 \<cdot> e\<^sub>2 \<cdot> e\<^sub>3 \<leadsto> v'"
  proof (induction v "(e\<^sub>1 \<cdot> e\<^sub>2) \<cdot> e\<^sub>3" v' rule: evaluate.induct)
  case (ev_comp v v' v'')
    with ev_comp(3) show ?case 
      by (induction v' "e\<^sub>1 \<cdot> e\<^sub>2" v'' rule: evaluate.induct) (metis evaluate.ev_comp)
  qed

lemma [elim]: "v ~ \<epsilon> \<leadsto> v' \<Longrightarrow> v = v'"
  by (induction v \<epsilon> v' rule: evaluate.induct) simp_all

lemma [elim]: "PairV v\<^sub>1 v\<^sub>2 ~ \<pi>\<^sub>1 \<leadsto> v \<Longrightarrow> v\<^sub>1 = v"
  by (induction "PairV v\<^sub>1 v\<^sub>2" \<pi>\<^sub>1 v rule: evaluate.induct) simp_all

lemma [elim]: "PairV v\<^sub>1 v\<^sub>2 ~ \<pi>\<^sub>2 \<leadsto> v \<Longrightarrow> v\<^sub>2 = v"
  by (induction "PairV v\<^sub>1 v\<^sub>2" \<pi>\<^sub>2 v rule: evaluate.induct) simp_all

lemma [elim]: "v ~ \<iota>\<^sub>l \<leadsto> v' \<Longrightarrow> v' = InlV v"
  by (induction v \<iota>\<^sub>l v' rule: evaluate.induct) simp_all

lemma [elim]: "v ~ \<iota>\<^sub>l \<leadsto> InlV v' \<Longrightarrow> v' = v"
  by (induction v \<iota>\<^sub>l "InlV v'" rule: evaluate.induct) simp_all

lemma [elim]: "v ~ \<iota>\<^sub>l \<leadsto> InrV v' \<Longrightarrow> False"
  by (induction v \<iota>\<^sub>l "InrV v'" rule: evaluate.induct)

lemma [elim]: "v ~ \<iota>\<^sub>r \<leadsto> v' \<Longrightarrow> v' = InrV v"
  by (induction v \<iota>\<^sub>r v' rule: evaluate.induct) simp_all

lemma [elim]: "v ~ \<iota>\<^sub>r \<leadsto> InrV v' \<Longrightarrow> v' = v"
  by (induction v \<iota>\<^sub>r "InrV v'" rule: evaluate.induct) simp_all

lemma [elim]: "v ~ \<iota>\<^sub>r \<leadsto> InlV v' \<Longrightarrow> False"
  by (induction v \<iota>\<^sub>r "InlV v'" rule: evaluate.induct)

lemma [elim]: "v ~ \<epsilon> \<cdot> e \<leadsto> v' \<Longrightarrow> v ~ e \<leadsto> v'"
  proof (induction v "\<epsilon> \<cdot> e" v' rule: evaluate.induct)
  case (ev_comp v v' v'')
    moreover hence "v' = v''" by auto
    ultimately show ?case by simp
  qed

lemma [elim]: "v ~ e \<cdot> \<epsilon> \<leadsto> v' \<Longrightarrow> v ~ e \<leadsto> v'"
  proof (induction v "e \<cdot> \<epsilon>" v' rule: evaluate.induct)
  case (ev_comp v v' v'')
    moreover hence "v = v'" by auto
    ultimately show ?case by simp
  qed

lemma [elim]: "v ~ \<pi>\<^sub>1 \<leadsto> v\<^sub>1 \<Longrightarrow> v ~ \<pi>\<^sub>2 \<leadsto> v\<^sub>2 \<Longrightarrow> v = PairV v\<^sub>1 v\<^sub>2"
  proof (induction v \<pi>\<^sub>1 v\<^sub>1 rule: evaluate.induct)
  case (ev_fst v\<^sub>1 v\<^sub>2')
    thus ?case by (induction "PairV v\<^sub>1 v\<^sub>2'" \<pi>\<^sub>2 v\<^sub>2 rule: evaluate.induct) simp_all
  qed

lemma [simp]: "v ~ \<pi>\<^sub>1 \<triangle> \<pi>\<^sub>2 \<leadsto> v' \<Longrightarrow> v ~ \<epsilon> \<leadsto> v'"
  proof (induction v "\<pi>\<^sub>1 \<triangle> \<pi>\<^sub>2" v' rule: evaluate.induct)
  case (ev_tup v v\<^sub>1 v\<^sub>2)
    hence "v = PairV v\<^sub>1 v\<^sub>2" by auto
    thus ?case by simp
  qed

lemma [simp]: "v ~ e\<^sub>1 \<triangle> e\<^sub>2 \<cdot> e\<^sub>3 \<leadsto> v' \<Longrightarrow> v ~ (e\<^sub>1 \<cdot> e\<^sub>3) \<triangle> (e\<^sub>2 \<cdot> e\<^sub>3) \<leadsto> v'"
  proof (induction v "e\<^sub>1 \<triangle> e\<^sub>2 \<cdot> e\<^sub>3" v' rule: evaluate.induct)
  case (ev_comp v v' v'')
    with ev_comp(3) show ?case by (induction v' "e\<^sub>1 \<triangle> e\<^sub>2" v'' rule: evaluate.induct) simp_all
  qed

lemma [elim]: "v ~ \<pi>\<^sub>1 \<cdot> e\<^sub>1 \<triangle> e\<^sub>2 \<leadsto> v' \<Longrightarrow> v ~ e\<^sub>1 \<leadsto> v'"
  proof (induction v "\<pi>\<^sub>1 \<cdot> e\<^sub>1 \<triangle> e\<^sub>2" v' rule: evaluate.induct)
  case (ev_comp v v' v'')
    thus ?case 
      proof (induction v "e\<^sub>1 \<triangle> e\<^sub>2" v' rule: evaluate.induct)
      case (ev_tup v v\<^sub>1 v\<^sub>2)
        moreover hence "v\<^sub>1 = v''" by auto
        ultimately show ?case by simp
      qed
  qed

lemma [elim]: "v ~ \<pi>\<^sub>2 \<cdot> e\<^sub>1 \<triangle> e\<^sub>2 \<leadsto> v' \<Longrightarrow> v ~ e\<^sub>2 \<leadsto> v'"
  proof (induction v "\<pi>\<^sub>2 \<cdot> e\<^sub>1 \<triangle> e\<^sub>2" v' rule: evaluate.induct)
  case (ev_comp v v' v'')
    thus ?case 
      proof (induction v "e\<^sub>1 \<triangle> e\<^sub>2" v' rule: evaluate.induct)
      case (ev_tup v v\<^sub>1 v\<^sub>2)
        moreover hence "v\<^sub>2 = v''" by auto
        ultimately show ?case by simp
      qed
  qed

lemma [simp]: "v ~ \<iota>\<^sub>l \<nabla> \<iota>\<^sub>r \<leadsto> v' \<Longrightarrow> v ~ \<epsilon> \<leadsto> v'"
  proof (induction v "\<iota>\<^sub>l \<nabla> \<iota>\<^sub>r" v' rule: evaluate.induct)
  case (ev_csl v v')
    hence "v' = InlV v" by auto
    thus ?case by simp
  next case (ev_csr v v')
    hence "v' = InrV v" by auto
    thus ?case by simp
  qed

lemma [simp]: "v ~ e\<^sub>3 \<cdot> e\<^sub>1 \<nabla> e\<^sub>2 \<leadsto> v' \<Longrightarrow> v ~ (e\<^sub>3 \<cdot> e\<^sub>1) \<nabla> (e\<^sub>3 \<cdot> e\<^sub>2) \<leadsto> v'"
  proof (induction v "e\<^sub>3 \<cdot> e\<^sub>1 \<nabla> e\<^sub>2" v' rule: evaluate.induct)
  case (ev_comp v v' v'')
    thus ?case by (induction v "e\<^sub>1 \<nabla> e\<^sub>2" v' rule: evaluate.induct) simp_all
  qed

lemma [elim]: "v ~ e\<^sub>1 \<nabla> e\<^sub>2 \<cdot> \<iota>\<^sub>l \<leadsto> v' \<Longrightarrow> v ~ e\<^sub>1 \<leadsto> v'"
  proof (induction v "e\<^sub>1 \<nabla> e\<^sub>2 \<cdot> \<iota>\<^sub>l" v' rule: evaluate.induct)
  case (ev_comp v v' v'')
    with ev_comp(2) show ?case
      proof (induction v' "e\<^sub>1 \<nabla> e\<^sub>2" v'' rule: evaluate.induct)
      case (ev_csl v' v'')
        moreover hence "v' = v" by auto
        ultimately show ?case by simp
      next case (ev_csr v' v'')
        hence False by auto
        thus ?case by simp
      qed
  qed

lemma [elim]: "v ~ e\<^sub>1 \<nabla> e\<^sub>2 \<cdot> \<iota>\<^sub>r \<leadsto> v' \<Longrightarrow> v ~ e\<^sub>2 \<leadsto> v'"
  proof (induction v "e\<^sub>1 \<nabla> e\<^sub>2 \<cdot> \<iota>\<^sub>r" v' rule: evaluate.induct)
  case (ev_comp v v' v'')
    with ev_comp(2) show ?case
      proof (induction v' "e\<^sub>1 \<nabla> e\<^sub>2" v'' rule: evaluate.induct)
      case (ev_csl v' v'')
        hence False by auto
        thus ?case by blast
      next case (ev_csr v' v'')
        moreover hence "v' = v" by auto
        ultimately show ?case by blast
      qed
  qed

(* in terms of the actual expression equality *)

lemma equiv_refl [simp]: "e\<^sub>1 \<simeq> e\<^sub>1"
  by (auto simp add: expression_equality_def)

lemma equiv_sym [sym]: "e\<^sub>1 \<simeq> e\<^sub>2 \<Longrightarrow> e\<^sub>2 \<simeq> e\<^sub>1"
  by (auto simp add: expression_equality_def)

lemma equiv_trans [simp, trans]: "e\<^sub>1 \<simeq> e\<^sub>2 \<Longrightarrow> e\<^sub>2 \<simeq> e\<^sub>3 \<Longrightarrow> e\<^sub>1 \<simeq> e\<^sub>3"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>1 \<simeq> e\<^sub>2 \<Longrightarrow> e\<^sub>3 \<simeq> e\<^sub>4 \<Longrightarrow> e\<^sub>1 \<cdot> e\<^sub>3 \<simeq> e\<^sub>2 \<cdot> e\<^sub>4"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>1 \<simeq> e\<^sub>2 \<Longrightarrow> e\<^sub>3 \<simeq> e\<^sub>4 \<Longrightarrow>  e\<^sub>1 \<triangle> e\<^sub>3 \<simeq> e\<^sub>2 \<triangle> e\<^sub>4"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>1 \<simeq> e\<^sub>2 \<Longrightarrow> e\<^sub>3 \<simeq> e\<^sub>4 \<Longrightarrow>  e\<^sub>1 \<nabla> e\<^sub>3 \<simeq> e\<^sub>2 \<nabla> e\<^sub>4"
  by (auto simp add: expression_equality_def)

lemma [simp]: "(e\<^sub>1 \<cdot> e\<^sub>2) \<cdot> e\<^sub>3 \<simeq> e\<^sub>1 \<cdot> e\<^sub>2 \<cdot> e\<^sub>3"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<epsilon> \<cdot> e \<simeq> e"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e \<cdot> \<epsilon> \<simeq> e"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<pi>\<^sub>1 \<triangle> \<pi>\<^sub>2 \<simeq> \<epsilon>"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>1 \<triangle> e\<^sub>2 \<cdot> e\<^sub>3 \<simeq> (e\<^sub>1 \<cdot> e\<^sub>3) \<triangle> (e\<^sub>2 \<cdot> e\<^sub>3)"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<pi>\<^sub>1 \<cdot> e\<^sub>1 \<triangle> e\<^sub>2 \<simeq> e\<^sub>1"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<pi>\<^sub>2 \<cdot> e\<^sub>1 \<triangle> e\<^sub>2 \<simeq> e\<^sub>2"
  by (auto simp add: expression_equality_def)

lemma [simp]: "\<iota>\<^sub>l \<nabla> \<iota>\<^sub>r \<simeq> \<epsilon>"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>3 \<cdot> e\<^sub>1 \<nabla> e\<^sub>2 \<simeq> (e\<^sub>3 \<cdot> e\<^sub>1) \<nabla> (e\<^sub>3 \<cdot> e\<^sub>2)"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>1 \<nabla> e\<^sub>2 \<cdot> \<iota>\<^sub>l \<simeq> e\<^sub>1"
  by (auto simp add: expression_equality_def)

lemma [simp]: "e\<^sub>1 \<nabla> e\<^sub>2 \<cdot> \<iota>\<^sub>r \<simeq> e\<^sub>2"
  by (auto simp add: expression_equality_def)

end
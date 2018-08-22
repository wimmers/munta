theory TA_Impl_Misc2
  imports
    TA_Impl.TA_Impl_Misc
    "HOL-Library.Sublist"
    "List-Index.List_Index"
    Automatic_Refinement.Misc
begin

lemma mem_nth:
  "x \<in> set xs \<Longrightarrow> \<exists> i < length xs. xs ! i = x"
  by (metis index_less_size_conv nth_index)

lemma union_subsetI:
  "A \<union> B \<subseteq> C \<union> D" if "A \<subseteq> C" "B \<subseteq> D"
  using that by blast

lemma map_eq_imageD:
  "f ` set xs = set ys" if "map f xs = ys"
  using that by auto

lemma if_contract:
  "(if a then x else if b then x else y) = (if a \<or> b then x else y)" for a x b y
  by (rule SMT.z3_rule)

paragraph \<open>More intros\<close>

named_theorems more_intros
named_theorems more_elims
lemmas [more_intros] =
  image_eqI[rotated] CollectI subsetI

lemmas [more_elims] =
  CollectE

paragraph \<open>Finiteness\<close>

lemma finite_prodI:
  "finite {(a,b). P a \<and> Q b}" if "finite {a. P a}" "finite {a. Q a}"
  using that by simp

lemma finite_prodI3:
  "finite {(a,b,c). P a \<and> Q b \<and> Q1 c}"
  if "finite {a. P a}" "finite {a. Q a}" "finite {a. Q1 a}"
  using that by simp

lemma finite_prodI4:
  "finite {(a,b,c,d). P a \<and> Q b \<and> Q1 c \<and> Q2 d}"
  if "finite {a. P a}" "finite {a. Q a}" "finite {a. Q1 a}" "finite {a. Q2 a}"
  using that by simp

named_theorems finite_intros
named_theorems more_finite_intros

lemmas [finite_intros] =
  finite_UnI finite_Union finite_imageI
  finite_lists_length_eq finite_lists_length_le
  distinct_finite_subset distinct_finite_set

lemmas [more_finite_intros] =
  finite_prodI finite_prodI3 finite_prodI4

paragraph \<open>Lists\<close>

(* XXX Merge with the variants from TA_Impl_Misc *)
lemma fold_evD2:
  assumes
    "P y (fold f xs acc)" "\<not> P y acc"
    "\<And> acc x. \<not> P y acc \<Longrightarrow> Q acc \<Longrightarrow> P y (f x acc) \<Longrightarrow> x \<in> set xs \<Longrightarrow> x = y"
    "Q acc" "\<And> acc x. Q acc \<Longrightarrow> Q (f x acc)"
    "\<And> acc x. \<not> P y acc \<Longrightarrow> Q acc \<Longrightarrow> P y (f x acc) \<Longrightarrow> R y"
  shows "\<exists> ys zs. xs = ys @ y # zs \<and> \<not> P y (fold f ys acc) \<and> P y (f y (fold f ys acc)) \<and> R y"
proof -
  from fold_evD'[OF assms(2,1)] obtain x ys zs where *:
    "xs = ys @ x # zs" "\<not> P y (fold f ys acc)" "P y (f x (fold f ys acc))"
    by auto
  moreover from assms(4-) have "Q (fold f ys acc)" by (auto intro: fold_acc_preserv)
  moreover from \<open>xs = _\<close> have "x \<in> set xs"
    by auto
  ultimately show ?thesis using assms(3,6) by auto
qed

lemmas fold_evD2' = fold_evD2[where R = "\<lambda> _. True", simplified]

lemma filter_map_map_filter:
  "filter P (map f xs) = List.map_filter (\<lambda> x. let y = f x in if P y then Some y else None) xs"
  by (induction xs; simp add: Let_def List.map_filter_simps)

lemma distinct_map_filterI:
  "distinct (List.map_filter f xs)"
  if "\<forall>x \<in> set xs. \<forall>y \<in> set xs. \<forall>a. f x = Some a \<and> f y = Some a \<longrightarrow> x = y" "distinct xs"
  using that by (induction xs) (auto simp: map_filter_simps set_map_filter split: option.split)

lemma filter_eqI:
  assumes
    "subseq ys xs" "\<forall>x \<in> set ys. P x"
    "\<forall>zs. subseq zs xs \<and> length zs > length ys \<longrightarrow> (\<exists> x \<in> set zs. \<not> P x)"
  shows "filter P xs = ys"
  using assms
proof (induction xs arbitrary: ys rule: list.induct)
  case Nil
  then show ?case
    by - (cases ys; simp)
next
  case (Cons x xs)
  show ?case
  proof (cases "P x")
    case True
    show ?thesis
    proof (cases ys)
      case Nil
      have "subseq [x] (x # xs)"
        by auto
      with Cons.prems Nil \<open>P x\<close> show ?thesis
        by fastforce
    next
      case (Cons y ys')
      have "x = y"
      proof (rule ccontr)
        assume "x \<noteq> y"
        with \<open>subseq ys (x # xs)\<close> \<open>ys = _\<close> have "subseq (x # ys) (x # xs)"
          by simp
        with Cons.prems(2-) \<open>P x\<close> show False
          by fastforce
      qed
      have "\<exists>x\<in>set zs. \<not> P x" if "subseq zs xs" and "length ys' < length zs" for zs
      proof -
        from \<open>subseq zs xs\<close> have "subseq (x # zs) (x # xs)"
          by simp
        with \<open>length ys' < length zs\<close> Cons.prems(3) \<open>ys = _\<close> have "\<exists>x\<in>set (x # zs). \<not> P x"
          by (intro Cons.prems(3)[rule_format]; simp)
        with \<open>P x\<close> show ?thesis
          by auto
      qed
      with Cons.prems \<open>P x\<close> \<open>ys = _\<close> \<open>x = y\<close> show ?thesis
        by (auto intro!: Cons.IH)
    qed
  next
    case False
    with Cons.prems show ?thesis
      by (cases ys) (auto split: if_split_asm intro!: Cons.IH)
  qed
qed

lemma filter_greatest_subseqD:
  "\<exists> x \<in> set zs. \<not> P x" if "subseq zs xs" "length zs > length (filter P xs)"
  using that by (metis filter_id_conv not_subseq_length subseq_filter)

lemma filter_eq_iff_greatest_subseq:
  "filter P xs = ys \<longleftrightarrow>
  subseq ys xs \<and> (\<forall>x \<in> set ys. P x) \<and>
  (\<forall>zs. subseq zs xs \<and> length zs > length ys \<longrightarrow> (\<exists> x \<in> set zs. \<not> P x))"
  using filter_greatest_subseqD filter_eqI by auto

lemma subseq_subsetD:
  "set xs \<subseteq> set ys" if "subseq xs ys"
  using that
  by (intro subsetI) (unfold subseq_singleton_left[symmetric], erule subseq_order.order.trans)

lemma subseq_distinct:
  "distinct xs" if "distinct ys" "subseq xs ys"
  using subseqs_distinctD that by simp

(* XXX Move *)
lemma filter_distinct_eqI:
  assumes
    "subseq ys xs" "\<forall>x \<in> set ys. P x" "\<forall>x \<in> set xs. x \<notin> set ys \<longrightarrow> \<not> P x" "distinct xs"
  shows "filter P xs = ys"
proof (intro filter_eqI, safe)
  fix zs assume prems: "subseq zs xs" "length ys < length zs"
  obtain x where "x \<in> set zs" "x \<notin> set ys"
  proof (atomize_elim, rule ccontr)
    assume "\<nexists>x. x \<in> set zs \<and> x \<notin> set ys"
    then have "set zs \<subseteq> set ys"
      by auto
    moreover from prems assms have "distinct zs" "distinct ys"
      by (blast intro: subseq_distinct)+
    ultimately show False
      using \<open>length ys < length zs\<close>
      by (auto dest: card_mono[rotated] simp: distinct_card[symmetric])
  qed
  with prems assms show "\<exists>x\<in>set zs. \<not> P x"
    by (auto 4 3 dest: subseq_subsetD)
qed (use assms in blast)+

lemma subseq_sorted_wrt:
  "sorted_wrt R xs" if "sorted_wrt R ys" "subseq xs ys"
  using that
  by (induction xs arbitrary: ys)
     (auto 0 4 dest: subseq_subsetD list_emb_ConsD subseq_Cons' simp: sorted_wrt_append)

lemma subseq_sorted:
  "sorted xs" if "sorted ys" "subseq xs ys"
  using that unfolding sorted_sorted_wrt by (rule subseq_sorted_wrt)

lemma sorted_distinct_subset_subseqI:
  assumes "sorted xs" "distinct xs" "sorted ys" "set xs \<subseteq> set ys"
  shows "subseq xs ys"
  using assms
proof (induction ys arbitrary: xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons y ys xs)
  from Cons.prems show ?case
    by (cases xs; simp) (safe; rule Cons.IH; auto 4 4)
qed

lemma sorted_distinct_subseq_iff:
  assumes "sorted ys" "distinct ys"
  shows "subseq xs ys \<longleftrightarrow> (sorted xs \<and> distinct xs \<and> set xs \<subseteq> set ys)"
  using assms
  by safe
     (erule
       subseq_subsetD[THEN subsetD] sorted_distinct_subset_subseqI subseq_distinct subseq_sorted;
       assumption
     )+

lemma list_all2_map_fst_aux:
  assumes "list_all2 (\<lambda>x y. x \<in> Pair y ` (zs y)) xs ys"
  shows "list_all2 (=) (map fst xs) ys"
  using assms by (smt fstI imageE list.rel_mono_strong list_all2_map1)

end
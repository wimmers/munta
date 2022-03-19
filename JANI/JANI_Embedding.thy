theory JANI_Embedding
  imports
    Simple_Networks.Generalized_Network_Language_Impl_Refine
    JANI
begin

subsection \<open>Embedding Into the Core Network Language\<close>

subsubsection \<open>Misc\<close>

lemma properties_for_sort_key':
  assumes "mset ys = mset xs"
    and "\<And>k. k \<in> set ys \<Longrightarrow> filter (\<lambda>x. f x = f k) ys = filter (\<lambda>x. f x = f k) xs"
    and "sorted (map f ys)"
  shows "sort_key f xs = ys"
proof -
  have *: "(\<lambda>x. k = f x) = (\<lambda>x. f x = k)" for k
    by auto
  from assms show ?thesis
    unfolding *[symmetric] by (rule properties_for_sort_key)
qed

lemma double_sort_key_append_right:
  "sort_key key (xs @ ys) = sort_key key (xs @ sort_key key ys)"
  by (rule properties_for_sort_key'; simp add: sort_key_stable)

lemma double_sort_key_append_left:
  "sort_key key (xs @ ys) = sort_key key (sort_key key xs @ ys)"
  by (rule properties_for_sort_key'; simp add: sort_key_stable)

lemma double_sort_key_append:
  "sort_key key (xs @ ys) = sort_key key (sort_key key xs @ sort_key key ys)"
  by (rule properties_for_sort_key'; simp add: sort_key_stable)

lemma sort_key_append_split:
  assumes "\<forall>x \<in> set xs. \<forall>y \<in> set ys. key x \<le> key y"
  shows "sort_key key (xs @ ys) = sort_key key xs @ sort_key key ys"
  using assms by (auto simp: sorted_append sort_key_stable intro!: properties_for_sort_key')

lemma sort_key_append_split_swap:
  assumes "\<forall>x \<in> set xs. \<forall>y \<in> set ys. key x > key y"
  shows "sort_key key (xs @ ys) = sort_key key ys @ sort_key key xs"
proof -
  have [simp]: "filter (\<lambda>x. key x = key k) xs = []" if "k \<in> set ys" for k
    using assms that by (intro filter_False) force
  have [simp]: "filter (\<lambda>x. key x = key k) ys = []" if "k \<in> set xs" for k
    using assms that by (intro filter_False) force
  show ?thesis
    using assms by (auto 4 4 simp: sorted_append sort_key_stable intro!: properties_for_sort_key')
qed

lemma sort_key_concat_map_split:
  assumes "\<forall>x \<in> set xs. \<forall>y \<in> set xs. \<forall>a \<in> set (f x). \<forall>b \<in> set (g y). key a < key b"
  shows
  "sort_key key (concat_map (\<lambda>x. f x @ g x) xs) =
   sort_key key (concat_map f xs) @ sort_key key (concat_map g xs)"
  using assms
proof (induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  have filter_g_empty: "filter (\<lambda>x. key x = key k) (g b) = []"
    if "k \<in> set (f a)" "a \<in> set (x # xs)" "b \<in> set (x # xs)" for a b k
    using Cons.prems that by (intro filter_False) force
  have filter_f_empty: "filter (\<lambda>x. key x = key k) (concat_map f xs) = []"
    if "k \<in> set (g a)" "a \<in> set (x # xs)" for a k
    using Cons.prems that by (intro filter_False) force
  have "sort_key key (f x @ g x @ concat_map (\<lambda>x. f x @ g x) xs)
    = sort_key key (f x @ g x @ sort_key key (concat_map (\<lambda>x. f x @ g x) xs))"
    by (metis (no_types) double_sort_key_append_right)
  also have
    "\<dots> = sort_key key (f x @ g x @ sort_key key (concat_map f xs) @ sort_key key (concat_map g xs))"
    using Cons by simp
  also have "\<dots> = sort_key key (f x @ sort_key key (g x @ concat_map f xs) @ concat_map g xs)"
    by (metis (no_types) append.assoc double_sort_key_append_left double_sort_key_append_right)
  also have
    "\<dots> = sort_key key (f x @ sort_key key (concat_map f xs) @ sort_key key (g x) @ concat_map g xs)"
    using Cons.prems by (simp add: sort_key_append_split_swap)
  also have
    "\<dots> = sort_key key (f x @ concat_map f xs @ g x @ concat_map g xs)"
    by (metis (no_types) double_sort_key_append_left double_sort_key_append_right)
  also have "\<dots> = sort_key key (f x @ concat_map f xs) @ sort_key key (g x @ concat_map g xs)"
    using Cons.prems by (subst sort_key_append_split[symmetric]; force)
  finally show ?case
    by simp
qed

lemma insort_key_key_cong:
  "insort_key key x xs = insort_key key' x xs" if "\<forall>x \<in> set (x # xs). key x = key' x"
  using that by (induction xs) auto

lemma sort_key_key_cong:
  "sort_key key xs = sort_key key' xs" if "\<forall>x \<in> set xs. key x = key' x"
  using that by (induction xs) (auto simp: insort_key_key_cong)

lemma sort_key_same:
  "sort_key key xs = xs" if "\<forall>x \<in> set xs. key x = c"
proof -
  from that have "sort_key key xs = sort_key (\<lambda>_. c) xs"
    by (rule sort_key_key_cong)
  also have "\<dots> = xs"
    by (rule sort_key_const)
  finally show ?thesis .
qed

lemma subseq_Suc_upt:
  "subseq [Suc i..<j] [i..<j]"
  by (metis Suc_lessD list_emb.simps subseq_order.dual_order.eq_iff upt_rec)


lemma const_upd_fold_remove_one:
  assumes "(x, const c) \<in> set upds" "\<forall>(x, e) \<in> set upds. \<exists>c. e = const c"
  shows
  "fold (\<lambda>(x, const c) \<Rightarrow> \<lambda>s. s(x:=Some c)) upds (s(x := Some c))
 = fold (\<lambda>(x, const c) \<Rightarrow> \<lambda>s. s(x:=Some c)) upds s"
  using assms
  by (induction upds arbitrary: s; simp)
     (smt (z3) case_prod_conv exp.simps(26) fun_upd_twist fun_upd_upd surj_pair)

lemma const_upd_fold_remove_many:
  assumes "\<forall>(x, e) \<in> set upds. \<exists>c. e = const c" "set upds' \<subseteq> set upds"
  shows
  "fold (\<lambda>(x, const c) \<Rightarrow> \<lambda>s. s(x:=Some c)) (upds' @ upds) s
 = fold (\<lambda>(x, const c) \<Rightarrow> \<lambda>s. s(x:=Some c)) upds s"
  using assms
  by (induction upds' arbitrary: s; simp)
     (smt (z3) case_prodE exp.simps(26) const_upd_fold_remove_one split_conv)

lemma is_upds_const_is_fold:
  assumes "\<forall>(x, e) \<in> set upds. \<exists>c. e = const c"
  shows "is_upds s upds s' \<longleftrightarrow> s' = fold (\<lambda>(x, const c) \<Rightarrow> \<lambda>s. s(x:=Some c)) upds s"
proof -
  have "mk_upds s upds = fold (\<lambda>(x, const c) \<Rightarrow> \<lambda>s. s(x:=Some c)) upds s"
    unfolding mk_upds_def mk_upd_def comp_def using assms by (intro fold_cong) auto
  from is_upds_make_updsI[of upds s] assms have "is_upds s upds (mk_upds s upds)"
    by force
  then have "is_upds s upds s' \<longleftrightarrow> s' = mk_upds s upds"
    by (auto simp: is_upds_determ)
  then show ?thesis
    unfolding \<open>mk_upds s upds = _\<close> .
qed

lemma is_upds_const_remove_many:
  assumes "\<forall>(x, e) \<in> set upds. \<exists>c. e = const c" "set upds' \<subseteq> set upds"
  shows "is_upds s (upds' @ upds) s' \<longleftrightarrow> is_upds s upds s'"
  using assms
  apply (subst is_upds_const_is_fold, (auto; fail))
  apply (subst is_upds_const_is_fold, (auto; fail))
  apply (subst const_upd_fold_remove_many; auto)
  done


subsubsection \<open>Construction\<close>

locale JANI_Embed_Defs = JANI +
  fixes get_cconstr :: "condition \<Rightarrow> (identifier, int) cconstraint"
    and get_cond  :: "condition \<Rightarrow> (identifier, int) bexp"
begin

definition mk_sync where
  "mk_sync sync \<equiv>
    List.map_filter id (map_index (\<lambda>p. map_option (\<lambda>a. (p, a, \<not> is_weak p a))) sync)"

definition syncsG where
  "syncsG \<equiv> List.map (mk_sync o synchronise) (syncs (system model))"

definition get_destination where
  "get_destination e \<equiv> List.hd (destinations e)"

definition mk_action where
  "mk_action a \<equiv> case a of None \<Rightarrow> Sil '''' | Some a \<Rightarrow> Com a"

definition mk_label where
  "mk_label a \<equiv> case a of
    Del \<Rightarrow> Generalized_Network_Language.Del
  | Internal \<Rightarrow> Generalized_Network_Language.Internal ''''
  | Sync sync \<Rightarrow> Generalized_Network_Language.Sync (mk_sync (synchronise sync))"

definition
  "idxs_of_edge e \<equiv> (\<Union>d \<in> set (destinations e). index ` set (assignments d))"

definition
  "max_idx \<equiv> Max (\<Union> p \<in> {0..<n_ps}. \<Union> e \<in> set (edges (N p)). idxs_of_edge e) + 1"

definition
  "mk_transient_resets \<equiv> map (\<lambda>upd. (upd, max_idx)) transient_vars_upds"

definition
  "mk_edge e \<equiv> (
    location e,
    get_cond (guard e),
    get_cconstr (guard e),
    mk_action (action e),
    get_upds (get_destination e) @ mk_transient_resets,
    get_resets (get_destination e),
    destination.location (get_destination e)
  )"

definition
  "mk_automaton p A \<equiv>
    ({},
     {},
     set (map mk_edge (edges A)),
     \<lambda>l. get_cconstr (inv p l)
    )"

definition
  "N_G \<equiv> map (\<lambda>p. mk_automaton p (N p)) [0..<n_ps]"

definition
  "B_G x \<equiv> case type_of x of
    Some (TBounded b) \<Rightarrow> Some (lower_bound b, upper_bound b) | _ \<Rightarrow> None"

abbreviation
  "systemG \<equiv> (
    set syncsG,
    N_G,
    B_G
  )
"

definition is_splittable where
  "is_splittable bexp \<equiv> \<forall>s u. is_bval s u bexp True
    \<longleftrightarrow> u \<turnstile> conv_cc (get_cconstr bexp) \<and> check_bexp s (get_cond bexp) True"

definition states where
  "states \<equiv>
    {L. length L = n_ps \<and> (\<forall>p < n_ps. \<exists>l \<in> set (locations (N p)). location.name l = L ! p)}"

definition vars where
  "vars \<equiv> {variable_declaration.name decl | decl. \<exists>bounds.
    variable_declaration.type decl = TBounded bounds \<and> decl \<in> set (variables model)}"

end

no_notation Generalized_Network_Language.step_u ("_ \<turnstile> \<langle>_, _, _\<rangle> \<rightarrow>\<^bsub>_\<^esub> \<langle>_, _, _\<rangle>" [61,61,61,61,61] 61)

notation Generalized_Network_Language.step_u ("_ \<turnstile>\<^sub>t \<langle>_, _, _\<rangle> \<rightarrow>\<^bsub>_\<^esub> \<langle>_, _, _\<rangle>" [61,61,61,61,61] 61)

abbreviation conv_A where "conv_A \<equiv> Generalized_Network_Language.conv_A"


subsubsection \<open>Embedding Proofs\<close>

locale JANI_Embed = JANI_Embed_Defs +
  \<comment> \<open>Computable\<close>
  assumes variable_declarations_names_distinct:
    "distinct (map variable_declaration.name (variables model))"
  assumes all_variables_initialized:
    "x \<in> set (model.variables model) \<Longrightarrow> \<exists>c. initial_value x = Some (exp.const c)"
  assumes transient_bounds_declared:
    "decl \<in> set (model.variables model) \<Longrightarrow> transient decl \<Longrightarrow>
     \<exists>bounds. variable_declaration.type decl = TBounded bounds"
  assumes locations_distinct[rule_format]:
    "\<forall>p<n_ps. distinct (map location.name (locations (N p)))"
  assumes destinations_length:
    "\<forall>p<n_ps. \<forall>e \<in> set (edges (N p)). length (destinations e) = 1"
  assumes transient_vars_upds_empty_or_no_weak_only_syncs:
    "transient_vars_upds = [] \<or>
     (\<forall>sync\<in>set (syncs (system model)). \<exists>p<n_ps. \<exists>a. synchronise sync ! p = Some a \<and> \<not> is_weak p a)"
  assumes length_synchronise[rule_format]:
    "\<forall>sync \<in> set (syncs (system model)). length (synchronise sync) = n_ps"
  assumes destinations_preconds: "\<forall>p<n_ps. \<forall>e\<in>set (edges (N p)). \<forall>destination\<in>set (destinations e).
    (\<forall>((x, e), i) \<in> set (get_upds destination). x \<in> vars) \<and>
    (\<exists>l\<in>set (locations (N p)). location.name l = destination.location destination)"
  \<comment> \<open>Not directly computable\<close>
  assumes invs_splittable:
    "\<forall>p<n_ps. \<forall>l \<in> set (locations (N p)). case time_progress l of
      Some cc \<Rightarrow> is_splittable cc | _ \<Rightarrow> True"
  assumes guards_splittable:
    "\<forall>p<n_ps. \<forall>e \<in> set (edges (N p)). is_splittable (guard e)"
  assumes get_cond_time_progress[rule_format]:
    "\<forall>p<n_ps. \<forall>l \<in> set (locations (N p)). \<forall>g. time_progress l = Some g \<longrightarrow> get_cond g = bexp.true"
  assumes get_cconstr_true:
    "get_cconstr bexp.true = []"
begin

lemma destinations_unique:
  "\<forall>p<n_ps. \<forall>e \<in> set (edges (N p)). \<exists>d. destinations e = [d]"
  using destinations_length list_decomp_1 by blast

lemma destinations_var_set:
  assumes "p < n_ps" "destinations e = [destination]" "e \<in> set (edges (N p))"
  shows "\<forall>((x, e), i) \<in> set (get_upds destination). x \<in> vars"
  using assms destinations_preconds by auto

lemma location_destinations_closed:
  assumes \<open>p < n_ps\<close> \<open>destinations e = [destination]\<close> \<open>e \<in> set (edges (N p))\<close>
  shows \<open>\<exists>l\<in>set (locations (N p)). location.name l = destination.location destination\<close>
  using assms destinations_preconds by auto

lemma dom_B_G:
  "dom B_G = vars"
  unfolding B_G_def vars_def dom_def type_of_def
  by (auto split: option.splits JANI.type.splits simp: find_Some_iff, metis nth_mem type.exhaust)
     (force dest: mem_nth distinct_idx[OF variable_declarations_names_distinct, rotated 2])+

lemma conv_systemG0:
  "conv systemG = (set syncsG, map conv_A N_G, B_G)"
  unfolding conv_def by (simp split: prod.split)

lemma length_N_G[simp]:
  "length N_G = n_ps"
  unfolding N_G_def by simp

definition N' where
  "N' p \<equiv> conv_A (mk_automaton p (N p))"

lemma N'_alt_def:
  "N' p = conv_A (N_G ! p)" if "p < n_ps"
  using that unfolding N'_def N_G_def by simp

lemma conv_systemG:
  "conv systemG = (set syncsG, map N' [0..<n_ps], B_G)"
  unfolding conv_systemG0 unfolding N'_def N_G_def by simp

lemmas N'_unfolds =
  N'_def
  mk_automaton_def
  Generalized_Network_Language.conv_A_def

lemma inv_N'_eq:
  "Generalized_Network_Language.inv (N' p) l = conv_cc (get_cconstr (inv p l))"
  unfolding N'_unfolds Generalized_Network_Language.inv_def by simp

lemma find_location:
  assumes "p < n_ps" "l \<in> set (locations (N p))"
  shows "find (\<lambda>loc. location.name loc = location.name l) (locations (N p)) = Some l"
  using assms locations_distinct unfolding find_Some_iff
  by (smt (verit, best) Suc_le_eq distinct_idx le_trans nat_less_le mem_nth)

lemma is_bval_inv_equiv0:
  assumes "p < n_ps" "l \<in> set (locations (N p))"
  shows
    "is_bval s u (inv p (location.name l)) True
  \<longleftrightarrow> u \<turnstile> conv_cc (get_cconstr (inv p (location.name l)))"
  using invs_splittable assms
  by (fastforce split: option.split_asm
       simp: find_location inv_def is_splittable_def get_cond_time_progress get_cconstr_true
       intro: is_bval_is_eval.intros(1) check_bexp_is_val.intros(1))

lemma is_bval_inv_equiv:
  assumes "p < n_ps" "L \<in> states"
  shows
    "is_bval s u (inv p (L ! p)) True \<longleftrightarrow> u \<turnstile> conv_cc (get_cconstr (inv p (L ! p)))"
  using assms is_bval_inv_equiv0 unfolding states_def by fastforce

lemma is_bval_edge_split:
  assumes "p < n_ps" "e \<in> set (edges (N p))"
  shows "is_bval s u (guard e) True
    \<longleftrightarrow> check_bexp s (get_cond (guard e)) True \<and> u \<turnstile> conv_cc (get_cconstr (guard e))"
  using guards_splittable assms unfolding is_splittable_def by auto

lemma urgent_simp[simp]:
  "urgent (N' p) = {}"
  unfolding urgent_def N'_unfolds by simp

lemma committed_N'[simp]:
  "committed (N' p) = {}"
  unfolding committed_def N'_unfolds by simp

lemma vars_type_ofE:
  assumes \<open>x \<in> vars\<close>
  obtains bounds where \<open>type_of x = Some (TBounded bounds)\<close>
  using assms
  unfolding vars_def
  by (simp add: type_of_def)
     (smt (verit, ccfv_SIG) distinct_map_eq find_None_iff find_SomeD
       not_Some_eq variable_declarations_names_distinct)

lemma bounded_B_G_iff:
  \<open>Simple_Network_Language.bounded B_G s \<longleftrightarrow> bounded s \<and> dom s = vars\<close>
  unfolding bounded_def dom_B_G Simple_Network_Language.bounded_def B_G_def
  by (metis (no_types, lifting) vars_type_ofE fstI option.sel option.simps(5) snd_conv type.simps(4))

lemma trans_N'I:
  assumes "e \<in> set (edges (N p))"
  shows "Generalized_Network_Language.conv_t (mk_edge e) \<in> trans (N' p)"
  using assms unfolding N'_unfolds trans_def by simp

lemma trans_N'_iff:
  "Generalized_Network_Language.conv_t (mk_edge e) \<in> trans (N' p) \<longleftrightarrow> e \<in> set (edges (N p))"
  unfolding N'_unfolds trans_def apply (auto simp:)
  apply (frule injD[OF inj_conv_t])
  apply simp \<comment> \<open>would need injectivity of @{term mk_edge}\<close>
  oops

lemma trans_N'E:
  assumes "t \<in> trans (N' p)"
  obtains e where "e \<in> set (edges (N p))" "t = Generalized_Network_Language.conv_t (mk_edge e)"
  using assms unfolding N'_unfolds trans_def by auto

lemma get_destination_simp:
  assumes "destinations e = [destination]"
  shows "get_destination e = destination"
  using assms unfolding get_destination_def by simp

lemma states_preservation_updI:
  assumes
    \<open>L \<in> states\<close> and
    \<open>destinations e = [destination]\<close> and
    \<open>e \<in> set (edges (N p))\<close>
  shows \<open>L[p := destination.location destination] \<in> states\<close>
  using assms location_destinations_closed unfolding states_def by (auto simp: nth_list_update')

lemma states_preservation_updsI:
  assumes
    \<open>L \<in> states\<close>
    \<open>set ps \<subseteq> {0..<n_ps}\<close>
    \<open>\<forall>p\<in>set ps. es p \<in> set (edges (N p))\<close> and
    \<open>\<forall>p\<in>set ps. destination.location (ds p) = ls' p\<close> and
    \<open>\<forall>p\<in>set ps. destinations (es p) = [ds p]\<close>
  shows \<open>fold (\<lambda>p L. L[p := ls' p]) ps L \<in> states\<close>
proof -
  have \<open>\<forall>p \<in> set ps. \<exists>l \<in> set (locations (N p)). location.name l = ls' p\<close>
    using assms location_destinations_closed unfolding subset_code(1) by fastforce
  with \<open>L \<in> states\<close> show ?thesis
    by (induction ps arbitrary: L) (auto simp: states_def nth_list_update')
qed

lemma set_mk_sync [simp]:
  "set (mk_sync sync_vec) = {(i,z,\<not> is_weak i z) | i z. i<length sync_vec \<and> sync_vec ! i = Some z}"
  by (auto simp add: mk_sync_def set_map_filter)

lemma sorted_mk_sync:
  "sorted (map fst (mk_sync xs))"
proof -
  have "sorted (map fst (List.map_filter id (map_index' i (\<lambda>p. map_option (\<lambda>a. (p, f p a))) xs)))"
    for f :: "nat \<Rightarrow> char list \<Rightarrow> 'a" and i
  by (induction xs arbitrary: i)
     (auto simp: set_map_filter map_filter_simps split: option.split)
  then show ?thesis
    unfolding mk_sync_def by fast
qed

lemma subseq_indices_mk_sync:
  "subseq (map fst (mk_sync xs)) [0..<length xs]"
proof -
  have "
    subseq
      (map fst
        (List.map_filter id (map_index' i (\<lambda>p. map_option (\<lambda>a. (p, f p a))) xs))) [i..<length xs+i]"
    for f :: "nat \<Rightarrow> char list \<Rightarrow> 'a" and i
    supply [simp] = map_filter_simps and [simp del] = upt_Suc
    apply (induction xs arbitrary: i)
      apply (simp; fail)
    apply (clarsimp split: option.split, safe)
     apply (rule list_emb_trans[rotated], rprems; simp add: subseq_Suc_upt)
    apply (subst upt_rec, simp flip: add_Suc_right)
    done
  from this[of 0] show ?thesis
    unfolding mk_sync_def by force
qed

lemma max_idx_is_max: "i < max_idx" if
  "((x, e), i) \<in> set (get_upds destination)"
  "edge \<in> set (edges (N p))" "p < n_ps" "destination \<in> set (destinations edge)"
  using that unfolding max_idx_def idxs_of_edge_def get_upds_def
  by (force intro: Max_ge le_imp_less_Suc)

lemma sort_upds_transient_resets_split:
  assumes "edge \<in> set (edges (N p))" "p < n_ps" "destination \<in> set (destinations edge)"
  shows
  "Generalized_Network_Language.sort_upds (get_upds destination @ mk_transient_resets)
 = Generalized_Network_Language.sort_upds (get_upds destination) @ transient_vars_upds"
proof -
  have "sort_key snd (get_upds destination  @ map (\<lambda>upd. (upd, max_idx)) transient_vars_upds)
      = sort_key snd (get_upds destination) @ map (\<lambda>upd. (upd, max_idx)) transient_vars_upds"
    by (subst sort_key_append_split)
       (auto dest: max_idx_is_max[OF _ assms] simp: sort_key_same[where c = max_idx])
  then show ?thesis
    unfolding Generalized_Network_Language.sort_upds_def mk_transient_resets_def
    by (simp add: comp_def)
qed

lemma transient_vars_upds_dom:
  "\<forall>(x, e)\<in>set transient_vars_upds. x \<in> vars"
  unfolding transient_vars_upds_def vars_def
  by (auto dest: transient_bounds_declared simp: set_map_filter)

lemma sort_upds_transient_resets_split2:
  assumes "\<forall>p \<in> set ps. es p \<in> set (edges (N p))" "\<forall>p \<in> set ps. ds p \<in> set (destinations (es p))"
    "set ps \<subseteq> {0..<n_ps}"
  shows
  "Generalized_Network_Language.sort_upds
     (concat_map (\<lambda>p. get_upds (ds p) @ mk_transient_resets) ps)
 = Generalized_Network_Language.sort_upds
     (concat_map (\<lambda>p. get_upds (ds p)) ps) @ concat_map (\<lambda>p. transient_vars_upds) ps"
  unfolding sort_upds_def using assms
  by (subst sort_key_concat_map_split)
     (auto 4 3 simp: mk_transient_resets_def sort_key_same[where c = max_idx] map_concat comp_def
               elim!: max_idx_is_max)

lemma is_upds_transient_vars_upds_dedup:
  "is_upds s (concat_map (\<lambda>p. transient_vars_upds) ps) s'
\<longleftrightarrow> is_upds s (if ps = [] then [] else transient_vars_upds) s'"
proof (induction ps)
  case Nil
  then show ?case
    by simp
next
  case (Cons a ps)
  then show ?case
    apply (simp split: if_split_asm)
    apply (subst is_upds_const_remove_many)
    apply (auto simp: transient_vars_upds_def set_map_filter dest: all_variables_initialized)
    done
qed

lemma step_embedI:
  notes [simp] = get_destination_simp
  assumes step: \<open>\<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>\<close> and \<open>L \<in> states\<close> and
    [tag \<open>''bounded''\<close>]: \<open>bounded s\<close> \<open>dom s = vars\<close>
  shows \<open>conv systemG \<turnstile>\<^sub>t \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>mk_label a\<^esub> \<langle>L', s', u'\<rangle>\<close>
using step proof cases
  case [tagged,untagged]: (step_t d)
  have "mk_label a = Generalized_Network_Language.Del"
    unfolding mk_label_def \<open>a = _\<close> by simp
  with \<open>L \<in> states\<close> show ?thesis
    apply (simp add: conv_systemG step_t(1-4))
    apply (rule step_u.intros)
    preferT \<open>''target invariant''\<close> apply (tag, simp add: inv_N'_eq is_bval_inv_equiv)
    preferT \<open>''bounded''\<close> apply (tag, simp add: bounded_B_G_iff)
    apply (tag; auto)+
    done
next
  case [tagged,untagged]: (step_int e p destination s1)
  from \<open>p < length L\<close> \<open>L \<in> states\<close> have "p < n_ps"
    unfolding states_def by simp
  then have "N' p = map N' [0..<n_ps] ! p"
    by simp
  from \<open>L \<in> states\<close> have \<open>L' \<in> states\<close>
    usingT \<open>''new loc''\<close> \<open>''destination''\<close> \<open>TRANS ''edge''\<close> by (simp,intro states_preservation_updI)
  have [simp]: "get_destination e = destination"
    usingT \<open>''destination''\<close> by simp
  have \<open>mk_label a = Generalized_Network_Language.Internal ''''\<close>
    unfolding mk_label_def \<open>a = _\<close> by simp
  with \<open>L \<in> states\<close> \<open>p < n_ps\<close> show ?thesis
    apply (simp add: conv_systemG step_int(1))
    apply (rule step_u.intros)
    preferT \<open>TRANS ''silent''\<close>
      apply (tag \<open>TRANS _\<close>, simp)
      apply (frule trans_N'I,
        simp add: mk_edge_def Generalized_Network_Language.conv_t_def mk_action_def,
        subst \<open>N' p = _\<close>[symmetric], assumption; fail)
    preferT \<open>''bexp''\<close> apply (tag \<open>''guard''\<close> \<open>TRANS _\<close>, simp add: is_bval_edge_split; fail)
    preferT \<open>''guard''\<close> apply (tag \<open>TRANS _\<close>, simp add: is_bval_edge_split; fail)
    preferT \<open>''target invariant''\<close>
      apply (tag, insert \<open>L' \<in> states\<close>, simp add: is_bval_inv_equiv inv_N'_eq; fail)
    preferT \<open>''is_upd''\<close>
      apply (tag \<open>''transients''\<close> \<open>''destination''\<close> \<open>TRANS ''edge''\<close>,
             simp add: is_upd_idxs_def sort_upds_transient_resets_split,
             simp add: sort_upds_def, erule (1) is_upds_appendI; fail)
    preferT \<open>''bounded''\<close>
         apply (tag \<open>''is_upd''\<close> \<open>''destination''\<close> \<open>TRANS ''edge''\<close> \<open>''transients''\<close>)
         apply (drule is_upds_dom, drule (2) destinations_var_set, (auto; fail)) \<comment> \<open>updates\<close>
         \<comment> \<open>reset transients\<close>
         apply (drule is_upds_dom; simp add: bounded_B_G_iff transient_vars_upds_dom; fail)
    apply (tag, simp; fail)+
    done
next
  case [tagged,untagged]: (step_sync sync ps as es gs ds ls' s1)
  have \<open>mk_label a = Generalized_Network_Language.label.Sync (mk_sync (synchronise sync))\<close>
    unfolding mk_label_def \<open>a = _\<close> by simp
  have [simp]: "length (synchronise sync) = n_ps"
    usingT \<open>''sync''\<close> by (rule length_synchronise)
  have N'_eq: "N' p = map N' [0..<n_ps] ! p" if "p \<in> set ps" for p
    usingT \<open>SEL ''range''\<close> using that by auto
  have \<open>L' \<in> states\<close>
    using \<open>L \<in> states\<close> usingT \<open>SEL ''range''\<close> \<open>''new loc''\<close>
      \<open>TRANS ''edges''\<close> \<open>TRANS ''new locs''\<close> \<open>TRANS ''destinations''\<close>
    by (simp only:, intro states_preservation_updsI)
  have subseqI: "subseq ps (map fst (mk_sync (synchronise sync)))" if "subseq ps [0..<n_ps]"
  proof (rule sorted_distinct_subset_subseqI)
    show \<open>sorted ps\<close>
      using that sorted_upt subseq_sorted unfolding mk_sync_def by blast
  next
    show \<open>distinct ps\<close>
      using that distinct_upt subseq_distinct unfolding mk_sync_def by blast
  next
    show \<open>sorted (map fst (mk_sync (synchronise sync)))\<close>
      by (rule sorted_mk_sync)
  next
    show \<open>set ps \<subseteq> set (map fst (mk_sync (synchronise sync)))\<close>
      unfolding mk_sync_def usingT \<open>''only syncs''\<close> \<open>SEL ''range''\<close>
      apply (clarsimp simp add: set_map_filter)
      subgoal for p
        by (cases "synchronise sync ! p"; force)
      done
  qed
  have transients_cond: "transient_vars_upds = [] \<or> ps \<noteq> []"
    using transient_vars_upds_empty_or_no_weak_only_syncs usingT \<open>''enabled''\<close> \<open>''sync''\<close> by auto
  from \<open>L \<in> states\<close> show ?thesis
    apply (simp add: conv_systemG \<open>mk_label a = _\<close>)
    apply (rule step_u.step_sync[where ps = ps])
    preferT \<open>''sync''\<close>
      apply (tag, simp add: syncsG_def; fail)

    preferT \<open>''enabled''\<close>
      apply (tag, simp; fail)

    preferT \<open>''only syncs''\<close>
      apply (tag, auto; fail)

    preferT \<open>''actions''\<close>
      apply (tag, auto; fail)

    preferT \<open>TRANS ''sync''\<close>
      apply (tag \<open>TRANS _\<close>)
      apply (simp add: N'_eq[symmetric])
      apply intros
      apply (drule (1) bspec)+
      apply (frule trans_N'I,
        simp add: mk_edge_def Generalized_Network_Language.conv_t_def mk_action_def; fail)

    preferT \<open>''committed''\<close>
      apply (tag, simp; fail)

    preferT \<open>''bexp''\<close>
      apply (tag \<open>''guards''\<close> \<open>TRANS _\<close> \<open>SEL ''range''\<close>, simp add: subset_code(1),
        metis is_bval_edge_split)

    preferT \<open>''guard''\<close>
      apply (tag \<open>''guards''\<close> \<open>TRANS _\<close> \<open>SEL ''range''\<close>, simp add: subset_code(1),
        metis is_bval_edge_split)

    preferT \<open>''maximal''\<close>
      apply (tag \<open>''actions''\<close>,
        auto elim!: trans_N'E simp: mk_edge_def Generalized_Network_Language.conv_t_def
               mk_action_def is_bval_edge_split split: option.split_asm; fail)

    preferT \<open>''target invariant''\<close>
      apply (tag, insert \<open>L' \<in> states\<close>, simp add: is_bval_inv_equiv inv_N'_eq; fail)

    preferT \<open>SEL ''range''\<close>
      apply (tag, simp; fail)

    preferT \<open>SEL ''sublist''\<close>
      apply (tag, erule subseqI; fail)

    preferT \<open>''new loc''\<close>
      apply (tag, assumption)

    preferT \<open>''new valuation''\<close>
      apply (tag, simp add: comp_def; fail)

    preferT \<open>''upds''\<close>
      apply (tag \<open>''transients''\<close> \<open>SEL ''range''\<close> \<open>TRANS _\<close>, insert transients_cond)
      apply (simp add: is_upds_idxs_def sort_upds_transient_resets_split2)
      apply (rule is_upds_appendI;
             auto simp: sort_upds_def comp_def is_upds_transient_vars_upds_dedup; fail)

    preferT \<open>''bounded''\<close>
      apply (tag \<open>''upds''\<close> \<open>TRANS _\<close> \<open>SEL ''range''\<close> \<open>''transients''\<close>, simp add: bounded_B_G_iff)
      apply (drule is_upds_dom, fastforce dest: destinations_var_set)
      apply (drule is_upds_dom; simp add: transient_vars_upds_dom; fail)
    done
qed


lemma states_lengthI [simp]:
  assumes "L \<in> states"
  shows "length L = n_ps"
  using assms unfolding states_def by simp

lemma destinations_eq:
  assumes "p < n_ps" "e \<in> set (edges (N p))"
  shows "destinations e = [get_destination e]"
  using assms destinations_unique unfolding get_destination_def by force

lemma step_embedE:
  assumes step: \<open>conv systemG \<turnstile>\<^sub>t \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>\<close> and [simp,intro]: \<open>L \<in> states\<close> and
    [tag \<open>''bounded''\<close>]: \<open>bounded s\<close> \<open>dom s = vars\<close>
  obtains a' where \<open>a = mk_label a'\<close> \<open>\<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a'\<^esub> \<langle>L', s', u'\<rangle>\<close>
proof -
  note thesisI = that
  have "conv systemG = (set syncsG, map N' [0..<n_ps], B_G)"
    by (rule conv_systemG)
  from step[unfolded conv_systemG] show ?thesis
  proof cases
    case [tagged, untagged]: (step_t d)
    from \<open>a = _\<close> have "a = mk_label Del"
      unfolding mk_label_def by simp
    from \<open>a = mk_label Del\<close> show ?thesis
      by (rule that, unfold step_t)
         (rule step.intros; tag; simp add: inv_N'_eq is_bval_inv_equiv)
  next
    case [tagged, untagged]: (step_int l b g a' f r l' p)
    have [simp]: "p < n_ps"
      usingT \<open>''range''\<close> by simp
    obtain e where
      edge [tag \<open>TRANS ''edge''\<close>]: "e \<in> set (edges (N p))" and
      "(l, b, g, Sil a', f, r, l') = Generalized_Network_Language.conv_t (mk_edge e)"
      usingT \<open>TRANS ''silent''\<close> by - (simp, erule trans_N'E)
    from this(2) have
      [tag \<open>''loc''\<close>]: \<open>l = edge.location e\<close> and
      [tag \<open>''bexp''\<close>]: \<open>b = get_cond (guard e)\<close> and
      [tag \<open>''guard''\<close>]: \<open>g = map conv_ac (get_cconstr (guard e))\<close> and
      [tag \<open>TRANS ''silent''\<close>]: \<open>action e = None\<close> \<open>a' = []\<close> and
      [tag \<open>''is_upd''\<close>]: \<open>f = get_upds (get_destination e) @ mk_transient_resets\<close> and
      [tag \<open>''new valuation''\<close>]: \<open>r = get_resets (get_destination e)\<close> and
      [tag \<open>''new loc''\<close>]: \<open>l' = destination.location (get_destination e)\<close>
      unfolding mk_edge_def Generalized_Network_Language.conv_t_def mk_action_def
      by (simp_all split: option.split_asm)
    have [tag \<open>''destination''\<close>]: "destinations e = [get_destination e]"
      using \<open>p < n_ps\<close> edge by (rule destinations_eq)
    from \<open>L \<in> states\<close> have [simp]: \<open>L' \<in> states\<close>
      usingT- \<open>''new loc''\<close> \<open>''destination''\<close> \<open>TRANS ''edge''\<close>
      by (simp only:, intro states_preservation_updI)
    obtain s1 where s1:
      "is_upds s (Generalized_Network_Language.sort_upds (get_upds (get_destination e))) s1"
      "is_upds s1 transient_vars_upds s'"
      usingT- \<open>''is_upd''\<close> \<open>TRANS _\<close> \<open>''destination''\<close> unfolding is_upd_idxs_def
      by (simp add: sort_upds_transient_resets_split) (erule is_upds_appendE)
    from \<open>a = _\<close> \<open>a' = []\<close> have "a = mk_label Internal"
      unfolding mk_label_def by simp
    then show ?thesis
      apply (rule thesisI)
      apply (rule step.intros)
      preferT \<open>TRANS ''edge''\<close>
        apply (tag, assumption)

      preferT \<open>TRANS ''silent''\<close>
        apply (tag, assumption)
      
      preferT \<open>''guard''\<close>
        apply (tag \<open>TRANS _\<close> \<open>''bexp''\<close>, subst is_bval_edge_split; simp; fail)
      
      preferT \<open>''target invariant''\<close>
        apply (tag, simp add: is_bval_inv_equiv inv_N'_eq; fail)
      
      preferT \<open>''destination''\<close>
        apply (tag, assumption)
      
      preferT \<open>''loc''\<close>
        apply (tag, simp; fail)
      
      preferT \<open>''range''\<close>
        apply (tag, assumption)
      
      preferT \<open>''new loc''\<close>
        apply (tag, simp; fail)
      
      preferT \<open>''new valuation''\<close>
        apply (tag, simp; fail)

      preferT \<open>''is_upd''\<close>
        apply (tag, use s1 in \<open>simp add: sort_upds_def\<close>; fail)

      preferT \<open>''transients''\<close>
        apply (tag, use s1 in \<open>simp add: sort_upds_def\<close>; fail)

      preferT \<open>''bounded''\<close>
        apply (tag, metis bounded_B_G_iff)
      done
  next
    case [tagged, untagged]: (step_sync sync ps as bs gs fs rs ls')
    obtain sync' where [tag \<open>''sync''\<close>]: "sync' \<in> set (syncs (system model))" and
      [tag \<open>''enabled''\<close>, simp]: "sync = mk_sync (synchronise sync')"
      usingT \<open>''sync''\<close> unfolding syncsG_def by auto
    have [simp]: "length (synchronise sync') = n_ps"
      usingT- \<open>''sync''\<close> by (intro length_synchronise)
    define es :: "nat \<Rightarrow> edge" where "es \<equiv> \<lambda>p. SOME e. e \<in> set (edges (N p))
      \<and> Generalized_Network_Language.conv_t (mk_edge e)
      = (L ! p, bs p, gs p, Com (as p), fs p, rs p, ls' p)"
    have [intro, simp]: "es p \<in> set (edges (N p))" and es_eq:
      "Generalized_Network_Language.conv_t (mk_edge (es p))
     = (L ! p, bs p, gs p, Com (as p), fs p, rs p, ls' p)" if "p\<in>set ps" for p
      unfolding atomize_conj es_def usingT \<open>TRANS ''sync''\<close> \<open>SEL ''range''\<close> using \<open>p \<in> set ps\<close>
      by - (rule someI_ex, force elim: trans_N'E)
    have
      \<open>edge.location (es p) = L ! p\<close> and
      \<open>get_cond (guard (es p)) = bs p\<close> and
      \<open>map conv_ac (get_cconstr (guard (es p))) = gs p\<close> and
      \<open>mk_action (action (es p)) = Com (as p)\<close> and
      \<open>action (es p) = Some (as p)\<close> and
      \<open>get_upds (get_destination (es p)) @ mk_transient_resets = fs p\<close> and
      \<open>get_resets (get_destination (es p)) = rs p\<close> and
      \<open>destination.location (get_destination (es p)) = ls' p\<close> if "p \<in> set ps" for p
      using that[THEN es_eq]
      by (simp add: Generalized_Network_Language.conv_t_def mk_edge_def mk_action_def
               split: option.split_asm)+
    note es_eqs[simp] = this
    have [tag \<open>TRANS ''destinations''\<close>]: "\<forall>p\<in>set ps. destinations (es p) = [get_destination (es p)]"
      usingT \<open>SEL ''range''\<close> by (simp add: subset_code(1)) (blast intro: destinations_eq)
    let ?gs = "\<lambda>p. guard (es p)" and ?ds = "\<lambda>p. get_destination (es p)"
    have [simp]: \<open>L' \<in> states\<close>
      usingT \<open>''new loc''\<close> \<open>SEL ''range''\<close> \<open>TRANS ''destinations''\<close>
      by - (simp only:, rule states_preservation_updsI[where es = es and ds = ?ds]; simp)
    have "subseq (map fst sync) [0..<n_ps]"
      unfolding \<open>sync = _\<close> \<open>length (synchronise sync') = n_ps\<close>[symmetric]
      by (rule subseq_indices_mk_sync)
    then have [tag \<open>SEL ''sublist''\<close>]: "subseq ps [0..<n_ps]"
      usingT \<open>SEL ''sublist''\<close> using subseq_order.trans by blast
    obtain s1 where s1:
      "is_upds s
        (Generalized_Network_Language.sort_upds (
          concat_map (\<lambda>p. get_upds (get_destination (es p))) ps)) s1"
      "is_upds s1 (concat_map (\<lambda>p. transient_vars_upds) ps) s'"
      usingT- \<open>''upds''\<close> \<open>TRANS _\<close> \<open>SEL ''range''\<close> unfolding is_upds_idxs_def
      by (simp flip: es_eqs(6) cong: map_cong add: sort_upds_transient_resets_split2)
         (subst (asm) sort_upds_transient_resets_split2, auto elim: is_upds_appendE)
    have transients_cond: "transient_vars_upds = [] \<or> ps \<noteq> []"
      using transient_vars_upds_empty_or_no_weak_only_syncs usingT- \<open>''enabled''\<close> \<open>''sync''\<close> by auto
    from \<open>sync = _\<close> \<open>a = _\<close> have "a = mk_label (Sync sync')"
      unfolding mk_label_def by simp
    then show ?thesis
      apply (rule thesisI)
      apply (rule step.step_sync[where
              ps = ps and as = as and es = es and gs = ?gs and ds = ?ds and ls' = ls' and s' = s1])
      preferT \<open>''sync''\<close>
        apply (tag, assumption)

      preferT \<open>''enabled''\<close>
        apply (tag, simp; fail)
      
      preferT \<open>''only syncs''\<close>
        apply (tag; auto; fail)
      
      preferT \<open>''actions''\<close>
        apply (tag, simp; fail)
      
      preferT \<open>TRANS ''edges''\<close>
        apply (tag, simp; fail)
      
      preferT \<open>TRANS ''actions''\<close>
        apply (tag, simp; fail)
      
      preferT \<open>TRANS ''guards''\<close>
        apply (tag, simp; fail)
      
      preferT \<open>TRANS ''locs''\<close>
        apply (tag, simp; fail)
      
      preferT \<open>TRANS ''destinations''\<close>
        apply (tag, assumption)
      
      preferT \<open>TRANS ''new locs''\<close>
        apply (tag, simp; fail)
      
      preferT \<open>''guards''\<close>
        apply (tag \<open>''guard''\<close> \<open>''bexp''\<close> \<open>SEL ''range''\<close>, use is_bval_edge_split in fastforce)
      
      preferT \<open>''maximal''\<close>
        apply (tag \<open>''actions''\<close>,
               clarsimp dest!: trans_N'I simp: mk_edge_def Generalized_Network_Language.conv_t_def
                 mk_action_def is_bval_edge_split,
               fastforce)
      
      preferT \<open>''target invariant''\<close>
        apply (tag, simp add: is_bval_inv_equiv inv_N'_eq; fail)
      
      preferT \<open>SEL ''range''\<close>
        apply (tag, simp; fail)
      
      preferT \<open>SEL ''sublist''\<close>
        apply (tag, assumption)
      
      preferT \<open>''new loc''\<close>
        apply (tag, assumption)
      
      preferT \<open>''new valuation''\<close>
        apply (tag, simp add: comp_def cong: map_cong; fail)
      
      preferT \<open>''upds''\<close>
        apply (tag, use s1 in \<open>simp add: is_upds_idxs_def sort_upds_def comp_def\<close>; fail)
      
      preferT \<open>''transients''\<close>
       apply (tag, use s1 transients_cond in
                   \<open>simp add: is_upds_transient_vars_upds_dedup split: if_split_asm\<close>; fail)
      
      preferT \<open>''bounded''\<close>
        apply (tag, simp add: bounded_B_G_iff; fail)
      done
  qed
qed

theorem step_embed_iff:
  assumes \<open>L \<in> states\<close> \<open>bounded s\<close> \<open>dom s = vars\<close>
  shows \<open>(\<exists>a. conv systemG \<turnstile>\<^sub>t \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>) \<longleftrightarrow> (\<exists>a. \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>)\<close>
  using step_embedI step_embedE assms by metis

end

end
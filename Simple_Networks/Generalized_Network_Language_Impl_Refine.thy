theory Generalized_Network_Language_Impl_Refine
  imports Simple_Network_Language_Impl_Refine Generalized_Network_Language_Impl
begin

unbundle no_library_syntax
notation fun_rel_syn (infixr "\<rightarrow>" 60)

paragraph \<open>Expression evaluation\<close>

definition mk_upd_idxs where
  "mk_upd_idxs s upds_idxs \<equiv> mk_upds s (sort_upds upds_idxs)"

definition mk_upds_idxs where
  "mk_upds_idxs s upds_idxs \<equiv> mk_upds s (sort_upds (concat upds_idxs))"

lemma dom_mk_upds_aux:
  "dom s \<subseteq> dom (fold (\<lambda>(x, upd) s'. s'(x \<mapsto> f upd)) xs s)"
  by (induction xs arbitrary: s) (auto simp: dom_def Collect_mono_iff)

lemma dom_mk_upds:
  "dom s \<subseteq> dom (mk_upds s upds)"
  unfolding mk_upds_def
  by (induction upds arbitrary: s; simp) (rule subset_trans[rotated], assumption, rule dom_mk_upd)

lemma is_upd_idxs_mk_upd_idxsI:
  "is_upd_idxs s upds (mk_upd_idxs s upds)"
  if "\<forall> ((_, e), _) \<in> set upds. \<forall>x \<in> vars_of_exp e. x \<in> dom s"
  unfolding mk_upd_idxs_def is_upd_idxs_def sort_upds_def
  using that by (intro is_upds_make_updsI) force

lemma is_upds_idxs_mk_upds_idxsI:
  "is_upds_idxs s upds (mk_upds_idxs s upds)"
  if "\<forall>upd \<in> set upds. \<forall> ((_, e), _) \<in> set upd. \<forall>x \<in> vars_of_exp e. x \<in> dom s"
  unfolding mk_upds_idxs_def is_upds_idxs_def sort_upds_def
  using that by (intro is_upds_make_updsI) force


paragraph \<open>Implementation auxiliaries\<close>

lemma union_map_of_alt_def:
  "union_map_of xs x = (let
    ys = rev (map snd (filter (\<lambda> (x', y). x' = x) xs))
   in if ys = [] then None else Some ys)"
proof -
  have "fold (\<lambda> (x, y) m. case m x of None \<Rightarrow> m(x \<mapsto> [y]) | Some ys \<Rightarrow> m(x \<mapsto> y # ys)) xs m x
  = (let
      ys = rev (map snd (filter (\<lambda> (x', y). x' = x) xs))
    in
    case m x of None \<Rightarrow> if ys = [] then None else Some ys | Some zs \<Rightarrow> Some (ys @ zs))" for x m
    by (induction xs arbitrary: m; clarsimp split: option.split)
  then show ?thesis
    unfolding union_map_of_def by simp
qed

lemma in_union_map_ofI:
  "\<exists> ys. union_map_of xs x = Some ys \<and> y \<in> set ys" if "(x, y) \<in> set xs"
  unfolding union_map_of_alt_def Let_def
  using that apply auto
  using set_filter[of "\<lambda>(x', y). x' = x" xs] apply auto
  done

lemma in_union_map_ofD:
  "(x, y) \<in> set xs" if "union_map_of xs x = Some ys" "y \<in> set ys"
  using that unfolding union_map_of_alt_def by (auto split: if_split_asm)


paragraph \<open>Implementation of state set\<close>

context Generalized_Network_Impl_nat_defs
begin

definition
  "states_i i = (\<Union>(l, e, g, a, r, u, l')\<in>set (fst (snd (snd (automata ! i)))). {l, l'})"

lemma states_mem_compute[code]:
  "L \<in> states \<longleftrightarrow> length L = n_ps \<and> (\<forall>i<n_ps. L ! i \<in> states_i i)"
  unfolding states_def states_i_def by simp (metis mem_trans_N_iff)

lemma states_mem_compute':
  "L \<in> states \<longleftrightarrow> length L = n_ps \<and> (\<forall>i<n_ps. L ! i \<in> map states_i [0..<n_ps] ! i)"
  unfolding states_mem_compute by simp

end


context Generalized_Network_Impl_nat
begin

paragraph \<open>Fundamentals\<close>

lemma mem_trans_N_iff:
  \<open>t \<in> trans (N i) \<longleftrightarrow> t \<in> set (fst (snd (snd (automata ! i))))\<close>
  if "i < n_ps"
  unfolding N_def fst_conv snd_conv
  unfolding automaton_of_def
  unfolding trans_def
  using that by (cases "automata ! i") (auto simp: length_automata_eq_n_ps)

lemma L_i_len:
  \<open>L ! i < num_states i\<close> if "i < n_ps" "L \<in> states"
  using trans_num_states that
  unfolding states_def by (auto 4 4 simp: mem_trans_N_iff)

lemma L_i_simp:
  \<open>[0..<num_states i] ! (L ! i) = L ! i\<close>
  if "i < n_ps" "L \<in> states"
  using L_i_len[OF that] by simp

lemma action_setD:
  \<open>pred_act (\<lambda>a'. a' < num_actions) a\<close>
  if \<open>(l, b, g, a, f, r, l') \<in> trans (N p)\<close> \<open>p < n_ps\<close>
  using that action_set
  by (cases "automata ! p")
    (subst (asm) mem_trans_N_iff; force dest!: nth_mem simp flip: length_automata_eq_n_ps)

paragraph \<open>More precise state sets\<close>

definition
  "states' \<equiv> {(L, s). L \<in> states \<and> dom s = {0..<n_vs} \<and> bounded bounds s}"

lemma states'_states[intro, dest]:
  "L \<in> states" if "(L, s) \<in> states'"
  using that unfolding states'_def by auto

lemma states'_dom[intro, dest]:
  "dom s = {0..<n_vs}" if "(L, s) \<in> states'"
  using that unfolding states'_def by auto

lemma states'_bounded[intro, dest]:
  "bounded bounds s" if "(L, s) \<in> states'"
  using that unfolding states'_def by auto

paragraph \<open>Implementation of invariants\<close>

definition (in Generalized_Network_Impl_nat_defs)
  "invs i \<equiv> let m = default_map_of [] (snd (snd (snd (automata ! i))));
    m' = map (\<lambda> j. m j) [0..<num_states i]
  in m'"

definition (in Generalized_Network_Impl_nat_defs)
  "invs1 \<equiv> map (\<lambda> i. let m = default_map_of [] (snd (snd (snd (automata ! i))));
    m' = map (\<lambda> j. m j) [0..<num_states i]
  in m') [0..<n_ps]"

definition (in Generalized_Network_Impl_nat_defs)
  "invs2 \<equiv> IArray (map (\<lambda> i. let m = default_map_of [] (snd (snd (snd (automata ! i))));
    m' = IArray (map (\<lambda> j. m j) [0..<num_states i])
  in m') [0..<n_ps])"

lemma refine_invs2:
  "invs2 !! i !! j = invs1 ! i ! j" if "i < n_ps"
  using that unfolding invs2_def invs1_def by simp

definition (in Generalized_Network_Impl_nat_defs)
  "inv_fun \<equiv> \<lambda>(L, _).
    concat (map (\<lambda>i. invs1 ! i ! (L ! i)) [0..<n_ps])"

lemma refine_invs1:
  \<open>invs1 ! i = invs i\<close> if \<open>i < n_ps\<close>
  using that unfolding invs_def invs1_def by simp

lemma invs_simp:
  "invs1 ! i ! (L ! i) = inv (N i) (L ! i)"
  if "i < n_ps" "L \<in> states"
  using that unfolding refine_invs1[OF \<open>i < _\<close>] invs_def N_def fst_conv snd_conv
  unfolding inv_def
  by (subst nth_map;
      clarsimp split: prod.split simp: automaton_of_def length_automata_eq_n_ps L_i_len)

lemma inv_fun_inv_of':
  "(inv_fun, inv_of prod_ta) \<in> inv_rel R states'" if "R \<subseteq> Id \<times>\<^sub>r S"
  using that
  unfolding inv_rel_def
  unfolding inv_fun_def
  unfolding inv_of_prod prod_inv_def
  apply (clarsimp simp: states'_def)
  apply (rule arg_cong[where f = concat])
  apply (auto simp add: invs_simp cong: map_cong)
  done

lemma inv_fun_alt_def:
  "inv_fun = (\<lambda>(L, _). concat (map (\<lambda>i. invs2 !! i !! (L ! i)) [0..<n_ps]))"
  unfolding inv_fun_def
  apply (intro ext)
  apply (clarsimp simp del: IArray.sub_def)
  apply (fo_rule arg_cong)
  apply (simp add: refine_invs2 del: IArray.sub_def)
  done

end (* Simple Network Impl nat *)

paragraph \<open>Implementation of transitions\<close>

context Generalized_Network_Impl_nat_defs
begin

definition
  "bounds_map \<equiv> the o map_of bounds'"

definition
  "check_bounded s =
    (\<forall>x \<in> dom s. fst (bounds_map x) \<le> the (s x) \<and> the (s x) \<le> snd (bounds_map x))"

text \<open>Compute pairs of processes with committed initial locations from location vector.\<close>
definition
  "get_committed L =
    List.map_filter (\<lambda>p.
    let l = L ! p in
    if l \<in> set (fst (automata ! p)) then Some (p, l) else None) [0..<n_ps]"

text \<open>Given a process and a location, return the corresponding transitions.\<close>
definition
  "trans_map i \<equiv>
    let m = union_map_of (fst (snd (snd (automata ! i)))) in (\<lambda>j.
      case m j of None \<Rightarrow> [] | Some xs \<Rightarrow> xs)"

text \<open>Filter for internal transitions.\<close>
definition
  "trans_i_map i j \<equiv>
    List.map_filter
      (\<lambda> (b, g, a, m, l'). case a of Sil a \<Rightarrow> Some (b, g, a, m, l') | _ \<Rightarrow> None)
    (trans_map i j)"

text \<open>Compute valid internal successors given:
  \<^item> a process \<open>p\<close>,
  \<^item> initial location \<open>l\<close>,
  \<^item> location vector \<open>L\<close>,
  \<^item> and initial state \<open>s\<close>.
\<close>
definition
  "int_trans_from_loc p l L s \<equiv>
    let trans = trans_i_map p l
    in
    List.map_filter (\<lambda> (b, g, a, f, r, l').
      let s' = mk_upd_idxs s f in
        if bval (the o s) b \<and> check_bounded s' then Some (g, Internal a, r, (L[p := l'], s'))
        else None
    ) trans"


definition
  "int_trans_from_vec pairs L s \<equiv>
    concat (map (\<lambda>(p, l). int_trans_from_loc p l L s) pairs)"

definition
  "int_trans_from_all L s \<equiv>
    concat (map (\<lambda>p. int_trans_from_loc p (L ! p) L s) [0..<n_ps])"

definition
  "int_trans_from \<equiv> \<lambda> (L, s).
    let pairs = get_committed L in
    if pairs = []
    then int_trans_from_all L s
    else int_trans_from_vec pairs L s
  "

definition
  "actions_by_state i \<equiv>
   fold (\<lambda> t acc. acc[fst (snd (snd t)) := (i, t) # (acc ! fst (snd (snd t)))])"

definition
  "all_actions_by_state t L \<equiv>
    fold (\<lambda> i. actions_by_state i (t i (L ! i))) [0..<n_ps] (repeat [] num_actions)"

definition
  "all_actions_from_vec t vec \<equiv>
    fold (\<lambda>(p, l). actions_by_state p (t p l)) vec (repeat [] num_actions)"


definition
  "trans_sil_map i j \<equiv>
    List.map_filter
      (\<lambda> (b, g, a, m, l'). case a of Sil a \<Rightarrow> Some (b, g, a, m, l') | _ \<Rightarrow> None)
    (trans_map i j)"

definition
  "trans_com_map i j \<equiv>
    List.map_filter
      (\<lambda> (b, g, a, m, l'). case a of Com a \<Rightarrow> Some (b, g, a, m, l') | _ \<Rightarrow> None)
    (trans_map i j)"

\<comment> \<open>Sort transitions by action\<close>
definition
  "actions_by_state' xs \<equiv>
    fold (\<lambda> t acc. acc[fst (snd (snd t)) := t # (acc ! fst (snd (snd t)))])
      xs (repeat [] num_actions)"

definition
  "trans_com_grouped i j \<equiv> actions_by_state' (trans_com_map i j)"

definition
  "pair_by_action OUT IN \<equiv>
  concat (
    map (\<lambda>(g1, a, r1, (L, s)).
      List.map (\<lambda>(q, g2, a2, f2, r2, l2).
          (g1 @ g2, a, r1 @ r2, (L[q := l2], mk_upds s f2))
    ) OUT) IN)
  "

definition make_combs where
  "make_combs p a xs \<equiv>
    let
      ys = List.map_filter
        (\<lambda>i.
          if i = p then None
          else if xs ! i ! a = [] then None
          else Some (map (\<lambda>t. (i, t)) (xs ! i ! a))
        )
        [0..<n_ps]
    in if ys = [] then [] else product_lists ys
  "

definition make_combs_from_pairs where
  "make_combs_from_pairs p a pairs xs \<equiv>
    let
      ys = List.map_filter
        (\<lambda>i.
          if i = p then None
          else if xs ! i ! a = [] then None
          else Some (map (\<lambda>t. (i, t)) (xs ! i ! a))
        )
        [0..<n_ps]
    in if ys = [] then [] else product_lists ys
  "

definition select_trans_from_sync where
  "select_trans_from_sync sync xs \<equiv>
    List.map_filter
      (\<lambda>(i, a, strong).
          if xs ! i ! a = [] then None
          else Some (map (\<lambda>t. (i, t)) (xs ! i ! a))
      )
    sync"

definition make_combs_from_sync where
  "make_combs_from_sync sync xs \<equiv>
    let selected = select_trans_from_sync sync xs
    in if selected = [] then [] else product_lists selected"

definition is_sync_enabled where
  "is_sync_enabled sync xs \<equiv>
    list_all
      (\<lambda>(i, a, strong). \<not> (strong \<and> xs ! i ! a = [])) sync"

\<^cancel>\<open>definition make_trans_from_combs where "
  make_trans_from_combs sync \<equiv> \<lambda>(L, s) combs. List.map_filter (\<lambda>comb.
    let (g, a, r, L', s) =
      fold
        (\<lambda>(q, _, g2, _, f2, r2, l2) (g1, a, r1, (L, s)).
          (g1 @ g2, a, r1 @ r2, (L[q := l2], mk_upd_idxs s f2))
        )
        comb
        ([], Sync sync, [], (L, s))
    in if check_bounded s then Some (g, a, r, L', s) else None
  ) combs
  "\<close>

definition make_trans_from_combs where "
  make_trans_from_combs sync \<equiv> \<lambda>(L, s) combs. List.map_filter (\<lambda>comb.
    let
      g = concat_map (\<lambda>(q, _, g, _, f, r, l). g) comb;
      r = concat_map (\<lambda>(q, _, g, _, f, r, l). r) comb;
      a = Sync sync;
      s' = mk_upds_idxs s (map (\<lambda>(q, _, g, _, f, r, l). f) comb);
      L' = fold (\<lambda>(q, _, g, _, f, r, l) L. L[q := l]) comb L
    in if check_bounded s' then Some (g, a, r, L', s') else None
  ) combs
  "

definition is_sync_enabled_committed where
  "is_sync_enabled_committed sync xs comm \<equiv>
    is_sync_enabled sync xs \<and>
    list_ex (\<lambda>(i, a, strong). xs ! i ! a \<noteq> [] \<and> i \<in> fst ` set comm) sync
  "

definition
  "sync_trans_from \<equiv> \<lambda>(L, s).
    let
      commited = get_committed L;
      Com = map (\<lambda>p. trans_com_grouped p (L ! p)) [0..<n_ps];
      Com = map (map (filter (\<lambda> (b, _). bval (the o s) b))) Com
    in
    if commited = [] then
      concat (map (\<lambda>sync.
        let
          combs = make_combs_from_sync sync Com;
          is_enabled = is_sync_enabled sync Com
        in
          if is_enabled then make_trans_from_combs sync (L, s) combs else []
        )
        syncs
      )
    else
      concat (map (\<lambda>sync.
        let
          combs = make_combs_from_sync sync Com;
          is_enabled = is_sync_enabled_committed sync Com commited
        in
          if is_enabled then make_trans_from_combs sync (L, s) combs else []
        )
        syncs
      )
    "

end (* Simple Network Impl nat defs *)

(* XXX Move *)
lemma product_lists_empty: "product_lists xss = [] \<longleftrightarrow> (\<exists>xs \<in> set xss. xs = [])" for xss
  by (induction xss) auto

context Generalized_Network_Impl_nat
begin

paragraph \<open>Correctness for implementations of primitives\<close>

lemma dom_bounds_eq:
  "dom bounds = {0..<n_vs}"
  using bounds unfolding bounds_def
  apply simp
  unfolding n_vs_def dom_map_of_conv_image_fst
  apply safe
   apply (force dest: mem_nth; fail)
  apply (force dest: nth_mem; fail)
  done

lemma check_bounded_iff:
  "bounded bounds s \<longleftrightarrow> check_bounded s" if "dom s = {0..<n_vs}"
  using that
  unfolding dom_bounds_eq[symmetric]
  unfolding check_bounded_def bounded_def bounds_map_def bounds_def
  by auto

lemma get_committed_mem_iff:
  "(p, l) \<in> set (get_committed L) \<longleftrightarrow> (l = L ! p \<and> l \<in> committed (N p) \<and> p < n_ps)"
  unfolding get_committed_def
  unfolding set_map_filter Let_def
  apply clarsimp
  unfolding N_def fst_conv snd_conv
  unfolding committed_def
  by safe
    ((subst nth_map | subst (asm) nth_map);
      auto split: prod.splits simp: automaton_of_def length_automata_eq_n_ps
      )+

lemma get_committed_empty_iff:
  "(\<forall>p < n_ps. L ! p \<notin> committed (N p)) \<longleftrightarrow> get_committed L = []"
  apply safe
  subgoal
  proof (rule ccontr)
    assume prems:
      "\<forall>p<n_ps. L ! p \<notin> committed (N p)" and
      "get_committed L \<noteq> []"
    then obtain p l where "(p, l) \<in> set (get_committed L)"
      by (metis length_greater_0_conv nth_mem old.prod.exhaust)
    from this[unfolded get_committed_mem_iff] prems(1)
    show "False"
      by auto
  qed
  subgoal for p
    using get_committed_mem_iff[of p "L ! p" L] by auto
  done

lemma get_committed_distinct: "distinct (get_committed L)"
  unfolding get_committed_def by (rule distinct_map_filterI) (auto simp: Let_def)

lemma is_upd_make_updI2:
  "is_upd_idxs s upds (mk_upd_idxs s upds)"
  if "(l, b, g, a, upds, r, l') \<in> trans (N p)" "p < n_ps" "dom s = {0..<n_vs}"
  using that var_set
  by - (intro is_upd_idxs_mk_upd_idxsI, subst (asm) mem_trans_N_iff;
        clarsimp simp flip: length_automata_eq_n_ps dest!: nth_mem; fastforce)

lemma var_setD:
  "\<forall>((x, upd), _)\<in>set f. x < n_vs \<and> (\<forall>i\<in>vars_of_exp upd. i < n_vs)"
  if "(l, b, g, a, f, r, l') \<in> trans (N p)" "p < n_ps"
  using var_set that
  by (force dest: nth_mem simp flip: length_automata_eq_n_ps simp: mem_trans_N_iff)

lemma var_setD2:
  "\<forall>i\<in>vars_of_bexp b. i < n_vs"
  if "(l, b, g, a, f, r, l') \<in> trans (N p)" "p < n_ps"
  using var_set that
  by (force dest: nth_mem simp flip: length_automata_eq_n_ps simp: mem_trans_N_iff)

lemma sort_upds_set:
  "set (sort_upds xs) = fst ` set xs"
  unfolding sort_upds_def by simp

lemma is_upd_dom2:
  "dom s' = {0..<n_vs}" if "is_upd_idxs s f s'"
  "(l, b, g, a, f, r, l') \<in> trans (N p)" "p < n_ps"
  "dom s = {0..<n_vs}"
  unfolding that(4)[symmetric] using that unfolding is_upd_idxs_def sort_upds_set
  by - (drule (1) var_setD, erule is_upds_dom, auto simp: sort_upds_set)

lemma is_updD:
  "s' = mk_upd_idxs s f" if "is_upd_idxs s f s'"
  "(l, b, g, a, f, r, l') \<in> trans (N p)" "p < n_ps"
  "dom s = {0..<n_vs}"
proof -
  from is_upd_make_updI2[OF that(2-)] have "is_upd_idxs s f (mk_upd_idxs s f)" .
  with that(1)[unfolded is_upd_idxs_def] show ?thesis
    unfolding is_upd_idxs_def by (rule is_upds_determ)
qed

lemma is_upds_make_updsI2:
  "is_upds_idxs s upds (mk_upds_idxs s upds)"
  if "dom s = {0..<n_vs}" 
    "\<forall>upd \<in> set upds. \<exists>p < n_ps. \<exists>l b g a r l'.
        (l, b, g, a, upd, r, l') \<in> trans (N p)"
  apply (rule is_upds_idxs_mk_upds_idxsI)
  using that using var_set
  apply intros
  apply (drule bspec)
  apply assumption
  apply elims
  apply (clarsimp simp flip: length_automata_eq_n_ps simp add: mem_trans_N_iff dest!: nth_mem)
  apply fastforce
  done

lemma is_upds_dom2:
  assumes "is_upds_idxs s upds s'"
    and "\<forall>f \<in> set upds. \<exists> p < n_ps. \<exists> l b g a r l'.
      (l, b, g, a, f, r, l') \<in> trans (N p)"
    and "dom s = {0..<n_vs}"
  shows "dom s' = dom s"
  using assms var_setD unfolding is_upds_idxs_def
  by (elim is_upds_dom, clarsimp) (fastforce simp: sort_upds_set)

lemma is_upds_dom3:
  assumes "is_upds_idxs s (map fs ps) s'"
    and "\<forall>p\<in>set ps. (L ! p, bs p, gs p, as p, fs p, rs p, ls' p) \<in> trans (N p)"
    and "set ps \<subseteq> {0..<n_ps}"
    and "dom s = {0..<n_vs}"
  shows "dom s' = dom s"
  using assms by (elim is_upds_dom2; force)

lemma is_upds_make_updsI3:
  "is_upds_idxs s (map fs ps) (mk_upds_idxs s (map fs ps))"
  if "dom s = {0..<n_vs}" 
    and "\<forall>p\<in>set ps. (L ! p, bs p, gs p, as p, fs p, rs p, ls' p) \<in> trans (N p)"
    and "set ps \<subseteq> {0..<n_ps}"
  for s :: "nat \<Rightarrow> int option"
  using that by (elim is_upds_make_updsI2) force

lemma is_updsD:
  assumes 
    "dom s = {0..<n_vs}" and
    "\<forall>p\<in>set ps.
        (ls p, bs p, gs p, as p, fs p, rs p, ls' p)
        \<in> trans (N p)" and
    "set ps \<subseteq> {0..<n_ps}" and
    "is_upds_idxs s (map fs ps) s'"
  shows "s' = mk_upds_idxs s (map fs ps)"
proof -
  have "is_upds_idxs s (map fs ps) (mk_upds_idxs s (map fs ps))"
    using assms(1-3) by (intro is_upds_make_updsI2; force)
  with assms(4) show ?thesis
    unfolding is_upds_idxs_def by (rule is_upds_determ)
qed



context
  notes [simp] = length_automata_eq_n_ps
begin

lemma trans_mapI:
  assumes
    "(L ! p, g, a, f, r, l') \<in> trans (N p)"
    "p < n_ps"
  shows
    "(g, a, f, r, l') \<in> set (trans_map p (L ! p))"
  using assms unfolding trans_map_def N_def fst_conv snd_conv trans_def
  by (subst (asm) nth_map) (auto dest: in_union_map_ofI split: prod.split_asm simp: automaton_of_def)

lemma trans_i_mapI:
  assumes
    "(L ! p, b, g, Sil a', f, r, l') \<in> trans (N p)"
    "p < n_ps"
  shows
    "(b, g, a', f, r, l') \<in> set (trans_i_map p (L ! p))"
  using assms unfolding trans_i_map_def set_map_filter by (fastforce dest: trans_mapI)

lemma trans_mapI':
  assumes
    "(l, b, g, a, f, r, l') \<in> trans (N p)"
    "p < n_ps"
  shows
    "(b, g, a, f, r, l') \<in> set (trans_map p l)"
  using assms unfolding trans_map_def N_def fst_conv snd_conv trans_def
  by (subst (asm) nth_map) (auto dest: in_union_map_ofI split: prod.split_asm simp: automaton_of_def)

lemma trans_mapD:
  assumes
    "(b, g, a, f, r, l') \<in> set (trans_map p l)"
    "p < n_ps"
  shows
    "(l, b, g, a, f, r, l') \<in> trans (N p)"
  using assms unfolding trans_map_def N_def fst_conv snd_conv trans_def
  by (subst nth_map) (auto split: prod.split elim: in_union_map_ofD[rotated] simp: automaton_of_def)

lemma trans_map_iff:
  assumes
    "p < n_ps"
  shows
    "(b, g, a, f, r, l') \<in> set (trans_map p l)
 \<longleftrightarrow> (l, b, g, a, f, r, l') \<in> trans (N p)"
  using trans_mapD trans_mapI' \<open>p < n_ps\<close> by auto

lemma trans_i_mapD:
  assumes
    "(b, g, a', f, r, l') \<in> set (trans_i_map p (L ! p))"
    "p < n_ps"
  shows
    "(L ! p, b, g, Sil a', f, r, l') \<in> trans (N p)"
  using assms unfolding trans_i_map_def set_map_filter
  by (force split: act.split_asm intro: trans_mapD)

paragraph \<open>An additional brute force method for forward-chaining of facts\<close>

method frules_all =
  repeat_rotate \<open>frules\<close>, dedup_prems

paragraph \<open>Internal transitions\<close>

lemma get_committed_memI:
  "(p, L ! p) \<in> set (get_committed L)" if "L ! p  \<in> committed (N p)" "p < n_ps"
  using that unfolding get_committed_mem_iff by simp

lemma check_bexp_bvalI:
  "bval (the o s) b" if "check_bexp s b True"
  "(l, b, g, a, f, r, l') \<in> trans (N p)" "p < n_ps"
  "dom s = {0..<n_vs}"
proof -
  from var_setD2[OF that(2,3)] \<open>dom s = {0..<n_vs}\<close> have "check_bexp s b (bval (the o s) b)"
    by (intro check_bexp_bval, simp)
  with check_bexp_determ that(1) show ?thesis
    by auto
qed

lemma check_bexp_bvalD:
  "check_bexp s b True" if "bval (the o s) b"
  "(l, b, g, a, f, r, l') \<in> trans (N p)" "p < n_ps"
  "dom s = {0..<n_vs}"
proof -
  from var_setD2[OF that(2,3)] \<open>dom s = {0..<n_vs}\<close> have "check_bexp s b (bval (the o s) b)"
    by (intro check_bexp_bval, simp)
  with check_bexp_determ that(1) show ?thesis
    by auto
qed

lemmas [forward2] =
  trans_i_mapD
  trans_i_mapI
  get_committed_memI
lemmas [forward3] =
  is_upd_make_updI2
lemmas [forward4] =
  is_updD
  is_upd_dom2
  check_bexp_bvalI
  check_bexp_bvalD

lemma int_trans_from_correct:
  "(int_trans_from, trans_int) \<in> transition_rel states'"
  unfolding transition_rel_def
proof clarsimp
  note [more_elims] = allE
  fix L s g a r L' s' assume "(L, s) \<in> states'"
  then have "L \<in> states" "dom s = {0..<n_vs}" "bounded bounds s"
    by auto
  then have [simp]: "length L = n_ps" "check_bounded s"
    by (auto simp: check_bounded_iff)
  show "(((L, s), g, a, r, L', s') \<in> trans_int)
    \<longleftrightarrow> ((g, a, r, L', s') \<in> set (int_trans_from (L, s)))"
  proof (cases "get_committed L = []")
    case True
    then have *: "((L, s), g, a, r, L', s') \<in> trans_int \<longleftrightarrow>
      ((L, s), g, a, r, L', s') \<in> {((L, s), g, Internal a, r, (L', s')) | L s l b g f p a r l' L' s'.
        (l, b, g, Sil a, f, r, l') \<in> trans (N p) \<and>
        (\<forall>p < n_ps. L ! p \<notin> committed (N p)) \<and>
        check_bexp s b True \<and>
        L!p = l \<and> p < length L \<and> L' = L[p := l'] \<and> is_upd_idxs s f s' \<and>
        L \<in> states \<and> bounded bounds s \<and> bounded bounds s'
      }"
      unfolding get_committed_empty_iff[symmetric] trans_int_def by blast
    from True have **: "int_trans_from (L, s) = int_trans_from_all L s"
      unfolding int_trans_from_def by simp
    from \<open>dom s = _\<close> show ?thesis
      unfolding * ** int_trans_from_all_def
      apply clarsimp
      unfolding int_trans_from_loc_def Let_def set_map_filter
      apply clarsimp
      apply safe
      subgoal for b f p a' l'
        apply frules
        unfolding check_bounded_iff by (intros; solve_triv)
      subgoal for p _ a' upds l'
        apply simp
        apply frules
        using \<open>L \<in> states\<close> \<open>check_bounded s\<close> True[folded get_committed_empty_iff]
        unfolding check_bounded_iff by (intros; solve_triv)
      done
  next
    case False
    then have *: "((L, s), g, a, r, L', s') \<in> trans_int \<longleftrightarrow>
      ((L, s), g, a, r, L', s') \<in> {((L, s), g, Internal a, r, (L', s')) | L s l b g f p a r l' L' s'.
        (l, b, g, Sil a, f, r, l') \<in> trans (N p) \<and>
        l \<in> committed (N p) \<and>
        L!p = l \<and> p < length L \<and> check_bexp s b True \<and> L' = L[p := l'] \<and> is_upd_idxs s f s' \<and>
        L \<in> states \<and> bounded bounds s \<and> bounded bounds s'
      }"
      unfolding get_committed_empty_iff[symmetric] trans_int_def by blast
    from False have **: "int_trans_from (L, s) = int_trans_from_vec (get_committed L) L s"
      unfolding int_trans_from_def by simp
    from \<open>dom s = _\<close> \<open>L \<in> states\<close> show ?thesis
      unfolding * ** int_trans_from_vec_def
      apply clarsimp
      unfolding int_trans_from_loc_def Let_def set_map_filter
      apply clarsimp
      apply safe
      subgoal for f p a' l'
        apply frules
        unfolding check_bounded_iff by (intros; solve_triv)
      subgoal for p _ a' upds l'
        unfolding get_committed_mem_iff
        apply (elims; simp)
        apply frules
        unfolding check_bounded_iff by (intros; solve_triv)
      done
  qed
qed


paragraph \<open>Mostly copied\<close>

lemma in_actions_by_stateI:
  assumes
    "(b1, g1, a, r1) \<in> set xs" "a < length acc"
  shows
    "(q, b1, g1, a, r1) \<in> set (actions_by_state q xs acc ! a)
    \<and> a < length (actions_by_state q xs acc)"
  using assms unfolding actions_by_state_def
  apply (induction xs arbitrary: acc)
   apply (simp; fail)
  apply simp
  apply (erule disjE)
   apply (rule fold_acc_preserv
      [where P = "\<lambda> acc. (q, b1, g1, a, r1) \<in> set (acc ! a) \<and> a < length acc"]
      )
    apply (subst list_update_nth_split; auto)
  by auto

lemma in_actions_by_state'I:
  assumes
    "(b1, g1, a, r1) \<in> set xs" "a < num_actions"
  shows
    "(b1, g1, a, r1) \<in> set (actions_by_state' xs ! a)
    \<and> a < length (actions_by_state' xs)"
proof -
  let ?f = "(\<lambda>t acc. acc[fst (snd (snd t)) := t # acc ! fst (snd (snd t))])"
  have "(b1, g1, a, r1) \<in> set (fold ?f xs acc ! a)
    \<and> a < length (fold ?f xs acc)" if "a < length acc" for acc
    using assms(1) that
    apply (induction xs arbitrary: acc)
     apply (simp; fail)
    apply simp
    apply (erule disjE)
     apply (rule fold_acc_preserv
        [where P = "\<lambda> acc. (b1, g1, a, r1) \<in> set (acc ! a) \<and> a < length acc"]
        )
      apply (subst list_update_nth_split; auto)
    by auto
  with \<open>a < _\<close> show ?thesis
    unfolding actions_by_state'_def by simp
qed

lemma in_actions_by_state_preserv:
  assumes
    "(q, b1, g1, a, r1) \<in> set (acc ! a)" "a < length acc"
  shows
    "(q, b1, g1, a, r1) \<in> set (actions_by_state y xs acc ! a)
    \<and> a < length (actions_by_state y xs acc)"
  using assms unfolding actions_by_state_def
  apply -
  apply (rule fold_acc_preserv
      [where P = "\<lambda> acc. (q, b1, g1, a, r1) \<in> set (acc ! a) \<and> a < length acc"]
      )
   apply (subst list_update_nth_split; auto)
  by auto

lemma length_actions_by_state_preserv[simp]:
  shows "length (actions_by_state y xs acc) = length acc"
  unfolding actions_by_state_def by (auto intro: fold_acc_preserv simp: list_update_nth_split)

lemma in_all_actions_by_stateI:
  assumes
    "a < num_actions" "q < n_ps" "(b1, g1, a, r1) \<in> set (M q (L ! q))"
  shows
    "(q, b1, g1, a, r1) \<in> set (all_actions_by_state M L ! a)"
  unfolding all_actions_by_state_def
  apply (rule fold_acc_ev_preserv
      [where P = "\<lambda> acc. (q, b1, g1, a, r1) \<in> set (acc ! a)" and Q = "\<lambda> acc. a < length acc",
        THEN conjunct1]
      )
      apply (rule in_actions_by_state_preserv[THEN conjunct1])
  using assms by (auto intro: in_actions_by_stateI[THEN conjunct1])

lemma in_all_actions_from_vecI:
  assumes
    "a < num_actions" "(b1, g1, a, r1) \<in> set (M q l)" "(q, l) \<in> set pairs"
  shows
    "(q, b1, g1, a, r1) \<in> set (all_actions_from_vec M pairs ! a)"
  unfolding all_actions_from_vec_def using assms
  by (intro fold_acc_ev_preserv
      [where P = "\<lambda> acc. (q, b1, g1, a, r1) \<in> set (acc ! a)" and Q = "\<lambda> acc. a < length acc",
        THEN conjunct1])
    (auto intro: in_actions_by_stateI[THEN conjunct1] in_actions_by_state_preserv[THEN conjunct1])

lemma actions_by_state_inj:
  assumes "j < length acc"
  shows "\<forall> (q, a) \<in> set (actions_by_state i xs acc ! j). (q, a) \<notin> set (acc ! j) \<longrightarrow> i = q"
  unfolding actions_by_state_def
  apply (rule fold_acc_preserv
      [where P =
        "\<lambda> acc'. (\<forall> (q, a) \<in> set (acc' ! j). (q, a) \<notin> set (acc ! j) \<longrightarrow> i = q) \<and> j < length acc'",
        THEN conjunct1])
  subgoal for x acc
    by (cases "fst (snd (snd x)) = j"; simp)
  using assms by auto

lemma actions_by_state_inj':
  assumes "j < length acc" "(q, a) \<notin> set (acc ! j)" "(q, a) \<in> set (actions_by_state i xs acc ! j)"
  shows "i = q"
  using actions_by_state_inj[OF assms(1)] assms(2-) by fast

lemma in_actions_by_stateD:
  assumes
    "(q, b, g, a, t) \<in> set (actions_by_state i xs acc ! j)" "(q, b, g, a, t) \<notin> set (acc ! j)"
    "j < length acc"
  shows
    "(b, g, a, t) \<in> set xs \<and> j = a"
  using assms unfolding actions_by_state_def
  apply -
  apply (drule fold_evD
      [where y = "(b, g, a, t)" and Q = "\<lambda> acc'. length acc' = length acc"
        and R = "\<lambda> (_, _, a', t). a' = j"]
      )
       apply assumption
    (* XXX Define asm split rule *)
      apply (subst (asm) list_update_nth_split[of j]; force)
     apply simp+
   apply (subst (asm) list_update_nth_split[of j]; force)
  by auto

lemma in_actions_by_state'D:
  assumes
    "(b, g, a, r) \<in> set (actions_by_state' xs ! a')" "a' < num_actions"
  shows
    "(b, g, a, r) \<in> set xs \<and> a' = a"
proof -
  let ?f = "(\<lambda>t acc. acc[fst (snd (snd t)) := t # acc ! fst (snd (snd t))])"
  have "(b, g, a, r) \<in> set xs \<and> a' = a"
    if "(b, g, a, r) \<in> set (fold ?f xs acc ! a')" "(b, g, a, r) \<notin> set (acc ! a')" "a' < length acc"
    for acc
    using that
    apply -
    apply (drule fold_evD
        [where y = "(b, g, a, r)" and Q = "\<lambda> acc'. length acc' = length acc"
          and R = "\<lambda> (_, _, a, t). a = a'"]
        )
         apply ((subst (asm) list_update_nth_split[where j = a'])?; auto; fail)+
    done
  with assms show ?thesis
    unfolding actions_by_state'_def by auto
qed

lemma in_all_actions_by_stateD:
  assumes
    "(q, b1, g1, a, r1) \<in> set (all_actions_by_state M L ! a')" "a' < num_actions"
  shows
    "(b1, g1, a, r1) \<in> set (M q (L ! q)) \<and> q < n_ps \<and> a' = a"
  using assms
  unfolding all_actions_by_state_def
  apply -
  apply (drule fold_evD''[where y = q and Q = "\<lambda> acc. length acc = num_actions"])
      apply (simp; fail)
     apply (drule actions_by_state_inj'[rotated])
       apply (simp; fail)+
  apply safe
    apply (drule in_actions_by_stateD)
      apply assumption
     apply (rule fold_acc_preserv)
      apply (simp; fail)+
  subgoal premises prems
  proof -
    from prems(2) have "q \<in> set [0..<n_ps]" by auto
    then show ?thesis by simp
  qed
  by (auto intro: fold_acc_preserv dest!: in_actions_by_stateD)

lemma length_all_actions_by_state_preserv:
  "length (all_actions_by_state M L) = num_actions"
  unfolding all_actions_by_state_def by (auto intro: fold_acc_preserv)

lemma length_actions_by_state'_preserv:
  "length (actions_by_state' xs) = num_actions"
  unfolding actions_by_state'_def by (rule fold_acc_preserv; simp)

lemma all_actions_from_vecD:
  assumes
    "(q, b1, g1, a, r1) \<in> set (all_actions_from_vec M pairs ! a')" "a' < num_actions"
    "distinct (map fst pairs)"
  shows
    "\<exists> l. (q, l) \<in> set pairs \<and> (b1, g1, a, r1) \<in> set (M q l) \<and> a' = a"
  using assms(1,2)
  unfolding all_actions_from_vec_def
  apply -
  apply (drule fold_evD2'[where
        y = "(q, SOME l. (q, l) \<in> set pairs)"
        and Q = "\<lambda> acc. length acc = num_actions"])
      apply (clarsimp; fail)
     apply clarsimp
     apply (drule actions_by_state_inj'[rotated])
       apply assumption
      apply assumption
     apply simp
  subgoal
    using assms(3) by (meson distinct_map_fstD someI_ex)
    apply (auto intro: fold_acc_preserv dest!: in_actions_by_stateD)
  subgoal premises prems for ys zs
    using prems(4) by (subst \<open>pairs = _\<close>) auto
  done

lemma all_actions_from_vecD2:
  assumes
    "(q, b1, g1, a, r1) \<in> set (all_actions_from_vec M pairs ! a')" "a' < num_actions"
    "(q, l) \<in> set pairs" "distinct (map fst pairs)"
  shows
    "(b1, g1, a, r1) \<in> set (M q l) \<and> a' = a"
  using assms(1,2,3)
  unfolding all_actions_from_vec_def
  apply -
  apply (drule fold_evD2'[where y = "(q, l)" and Q = "\<lambda> acc. length acc = num_actions"])
      apply (clarsimp; fail)
     apply clarsimp
     apply (drule actions_by_state_inj'[rotated])
       apply assumption
      apply assumption
     apply simp
  subgoal
    using assms(4) by (meson distinct_map_fstD)
  by (auto intro: fold_acc_preserv dest!: in_actions_by_stateD)

paragraph \<open>Synchronising transitions\<close>

lemma select_trans_from_sync_alt_def:
  "select_trans_from_sync sync xs \<equiv>
    map (\<lambda>(i, a, strong). map (\<lambda>t. (i, t)) (xs ! i ! a))
      (filter
        (\<lambda>(i, a, strong).
           xs ! i ! a \<noteq> []
        )
        sync
      )"
  apply (rule eq_reflection)
  unfolding select_trans_from_sync_def
  apply (simp add: map_filter_def comp_def split: prod.split)
  apply (fo_rule map_cong arg_cong2, auto)+
  done

lemma empty_not_in_select_trans_from_sync: "[] \<notin> set (select_trans_from_sync sync xs)"
  unfolding select_trans_from_sync_alt_def by auto

lemma make_combs_from_sync_emptyD: "select_trans_from_sync sync COM' = []"
  if "make_combs_from_sync sync COM' = []" for sync :: "(nat \<times> nat \<times> bool) list"
  using that empty_not_in_select_trans_from_sync unfolding make_combs_from_sync_def
  by (auto split: if_split_asm simp: Let_def product_lists_empty)

definition is_select_basic where
  "is_select_basic L s sync ps bs gs as fs rs ls' \<equiv>
  ''sync'' \<bbar> sync \<in> set syncs \<and>
  ''enabled'' \<bbar> (\<forall>(p, a, b) \<in> set sync. b \<longrightarrow> p \<in> set ps) \<and>
  ''only syncs'' \<bbar> (\<forall>p < n_ps. p \<notin> fst ` set sync \<longrightarrow> p \<notin> set ps) \<and>
  ''actions'' \<bbar> (\<forall>(p, a, _) \<in> set sync. as p = a) \<and>
  TRANS ''sync'' \<bbar>
    (\<forall>p \<in> set ps. (L ! p, bs p, gs p, Com (as p), fs p, rs p, ls' p) \<in> trans (N p)) \<and>
  ''bexp''    \<bbar> (\<forall>p \<in> set ps. check_bexp s (bs p) True) \<and>
  SEL ''range''      \<bbar> set ps \<subseteq> {0..<n_ps} \<and>
  SEL ''sublist'' \<bbar> subseq ps (map fst sync)"

definition is_select_maximal where
  "is_select_maximal L s sync ps \<equiv> ''maximal'' \<bar> \<forall>q < n_ps. q \<notin> set ps \<longrightarrow>
        (\<forall>a b g f r l'.
          (L!q, b, g, Com a, f, r, l') \<in> trans (N q) \<and> (q, a, False) \<in> set sync
          \<longrightarrow> \<not> check_bexp s b True)"

definition is_sync_result where
  "is_sync_result L s sync ps as fs ls' L' s'  \<equiv>
    ''new loc'' \<bbar> L' = fold (\<lambda>p L . L[p := ls' p]) ps L \<and>
    ''upds''    \<bbar> is_upds_idxs s (map fs ps) s'"

definition is_select_committed where
  "is_select_committed L ps \<equiv>
    ''committed'' \<bar> (\<exists>p\<in>set ps. L ! p \<in> committed (N p)) \<or> (\<forall>p<n_ps. L ! p \<notin> committed (N p))"

lemma sync_trans_from_correct:
  "(sync_trans_from, trans_sync) \<in> transition_rel states'"
  unfolding transition_rel_def
proof clarsimp
  fix L s g a r L' s' assume "(L, s) \<in> states'"
  then have "L \<in> states" "dom s = {0..<n_vs}" and [tag \<open>''bounded''\<close>]: "bounded bounds s"
    by auto
  then have [simp]: "length L = n_ps"
    by auto
  define COM  where "COM  = map (\<lambda>p. trans_com_grouped p (L ! p)) [0..<n_ps]"
  define COM' where "COM' = map (map (filter (\<lambda> (b, _). bval (the o s) b))) COM"
  have COM_I:
    "(b, g, a', f, r, l') \<in> set (COM ! p ! a')"
    if "(L ! p, b, g, Com a', f, r, l') \<in> trans (N p)"
      "p < n_ps" "a' < num_actions"
    for p b g a' f r l'
  proof -
    from trans_mapI[OF that(1,2)] have
      "(b, g, a', f, r, l') \<in> set (trans_com_map p (L ! p))"
      unfolding trans_com_map_def set_map_filter by fastforce
    with \<open>a' < _\<close> have "(b, g, a', f, r, l') \<in> set (trans_com_grouped p (L ! p) ! a')"
      unfolding trans_com_grouped_def by (auto dest: in_actions_by_state'I)
    with \<open>p < _\<close> show ?thesis
      unfolding COM_def by auto
  qed
  have COM_D:
    "(L ! p, b, g, Com a', f, r, l') \<in> trans (N p) \<and> a' = a1"
    if "(b, g, a', f, r, l') \<in> set (COM ! p ! a1)" "a1 < num_actions" "p < n_ps"
    for p b g a' f r l' a1
    using that unfolding COM_def trans_com_grouped_def trans_com_map_def
    by (auto split: option.split_asm simp: set_map_filter dest!: in_actions_by_state'D)
       (auto split: act.split_asm if_split_asm dest: trans_mapD)
  have [simp]: "length COM = n_ps"
    unfolding COM_def by simp
  have [simp]: "length (COM ! p) = num_actions" if "p < n_ps" for p
    using that by (simp add: length_actions_by_state'_preserv trans_com_grouped_def COM_def)
  have COM'_I:
    "(b, g, a', f, r, l') \<in> set (COM' ! p ! a')"
    if "(b, g, a', f, r, l') \<in> set (COM ! p ! a')" "p < n_ps" "a' < num_actions"
       "check_bexp s b True" for p b g a' f r l'
    using that \<open>dom s = {0..<n_vs}\<close> unfolding COM'_def
    by (auto dest!: COM_D[THEN conjunct1] elim: check_bexp_bvalI)
  have COM'_D:
    "(L ! p, b, g, Com a', f, r, l') \<in> trans (N p)
     \<and> a' = a1 \<and> check_bexp s b True"
    if "(b, g, a', f, r, l') \<in> set (COM' ! p ! a1)" "a1 < num_actions" "p < n_ps"
    for p b g a' f r l' a1
    using that \<open>dom s = {0..<n_vs}\<close> unfolding COM'_def by (auto dest!: COM_D elim: check_bexp_bvalD)

  define make_trans where
    "make_trans sync \<equiv>
    let
      commited = get_committed L
    in
    if commited = [] then
        let
          combs = make_combs_from_sync sync COM';
          is_enabled = is_sync_enabled sync COM'
        in
          if is_enabled then make_trans_from_combs sync (L, s) combs else []
    else
        let
          combs = make_combs_from_sync sync COM';
          is_enabled = is_sync_enabled_committed sync COM' commited
        in
          if is_enabled then make_trans_from_combs sync (L, s) combs else []
    " for sync
  have sync_trans_from_make_trans:
    "sync_trans_from (L, s) = concat (map (\<lambda>sync. make_trans sync) syncs)"
    unfolding make_trans_def Let_def sync_trans_from_def Let_def if_contract case_prod_conv
    unfolding COM'_def[symmetric] COM_def[symmetric] by simp
  {
    fix sync :: "(nat \<times> nat \<times> bool) list" and ps bs gs as fs rs ls'
    assume
      A: "is_select_basic L s sync ps bs gs as fs rs ls'" "is_select_maximal L s sync ps"
    define selected where "selected = select_trans_from_sync sync COM'"
    from A have
      "sync \<in> set syncs" and
      [tag \<open>''enabled''\<close>]: "(\<forall>(p, a, b) \<in> set sync. b \<longrightarrow> p \<in> set ps)" and
      [tag \<open>''only syncs''\<close>]: "(\<forall>p < n_ps. p \<notin> fst ` set sync \<longrightarrow> p \<notin> set ps)" and
      [tag \<open>''actions''\<close>]: "\<forall>(p, a, _) \<in> set sync. as p = a" and
      trans [tag \<open>TRANS ''sync''\<close>]: "\<forall>p\<in>set ps.
          (L ! p, bs p, gs p, Com (as p), fs p, rs p, ls' p) \<in> trans (N p)" and
      [tag \<open>''maximal''\<close>]: "\<forall>q < n_ps. q \<notin> set ps \<longrightarrow>
        (\<forall>a b g f r l'.
          (L!q, b, g, Com a, f, r, l') \<in> trans (N q) \<and> (q, a, False) \<in> set sync
          \<longrightarrow> \<not> check_bexp s b True)" and
      range [tag \<open>SEL ''range''\<close>]: "set ps \<subseteq> {0..<n_ps}" and
      [tag \<open>SEL ''sublist''\<close>]: "subseq ps (map fst sync)" and
      [tag \<open>''bexp''\<close>]: "\<forall>p \<in> set ps. check_bexp s (bs p) True"
      unfolding is_select_basic_def is_select_maximal_def by - (elim conjE, untag, assumption)+
    obtain ps' where ps': "subseq ps' sync" "map fst ps' = ps"
      using \<open>subseq ps _\<close> by (rule subseq_mapE)
    have ps'_subs_sync [intro]: "(p, a, b) \<in> set sync" if "(p, a, b) \<in> set ps'" for p a b
      using that \<open>subseq ps' _\<close> by (auto elim: list_emb_set)
    have "distinct (map fst sync)"
      using action_set(3) \<open>sync \<in> _\<close> by auto
    have action_boundedI: "as p < num_actions" if "(p, a, b) \<in> set sync" for p a b
      usingT \<open>''actions''\<close> using action_set(1) \<open>sync \<in> _\<close> \<open>_ \<in> set sync\<close>
      by (auto split: prod.split_asm) metis
    have COM'_I1: "(bs p, gs p, as p, fs p, rs p, ls' p) \<in> set (COM' ! p ! as p) \<and> as p = a"
      if "(p, a, b) \<in> set sync" "p \<in> set ps" for p a b
    proof -
      from \<open>p \<in> _\<close> trans have
        "(L ! p, bs p, gs p, Com (as p), fs p, rs p, ls' p) \<in> trans (N p)"
        by auto
      moreover from \<open>p \<in> _\<close> range have "p < n_ps"
        by auto
      moreover have "as p < num_actions"
        using \<open>_ \<in> set sync\<close> by (rule action_boundedI)
      ultimately have "(bs p, gs p, as p, fs p, rs p, ls' p) \<in> set (COM ! p ! as p)"
        by (rule COM_I)
      moreover have "check_bexp s (bs p) True"
        usingT \<open>''bexp''\<close> using \<open>p \<in> _\<close> by blast
      ultimately have "(bs p, gs p, as p, fs p, rs p, ls' p) \<in> set (COM' ! p ! as p)"
        using \<open>p < _\<close> \<open>as p < _\<close> by (intro COM'_I)
      moreover have "as p = a"
        using \<open>_ \<in> set sync\<close> usingT \<open>''actions''\<close> by auto
      ultimately show ?thesis
        by auto
    qed
    have COM'_I2: "(bs p, gs p, as p, fs p, rs p, ls' p) \<in> set (COM' ! p ! as p) \<and> as p = a"
      if "(p, a, b) \<in> set ps'" for p a b
      using that ps'(2) by (intro COM'_I1) auto
    { fix p assume "p \<in> set ps"
      consider b where
        "(p, as p, b) \<in> set ps'" "(bs p, gs p, as p, fs p, rs p, ls' p) \<in> set (COM' ! p ! as p)"
      proof -
        from \<open>p \<in> _\<close> ps' obtain a' b where "(p, a', b) \<in> set ps'"
          by (force elim: list_emb_set)
        from this COM'_I2[OF this] show ?thesis
          using that by auto
      qed
    } note 01 = this
    have "COM' ! p ! a \<noteq> []" if "(p, a, b) \<in> set ps'" for p a b
      using COM'_I2[OF that] by auto
    moreover have False
      if "(p, a, b) \<notin> set ps'" "COM' ! p ! a \<noteq> []" "(p, a, b) \<in> set sync" for p a b
    proof -
      from \<open>_ \<in> set sync\<close> have "p < n_ps"
        using action_set(1) \<open>sync \<in> set syncs\<close> unfolding n_ps_def by auto
      have "p \<notin> set ps"
        using that(1,3) \<open>_ = ps\<close> \<open>distinct _\<close>
        by clarsimp (metis (full_types) distinct_map_fstD ps'_subs_sync)
      with \<open>_ \<in> set sync\<close> have "b = False"
        usingT \<open>''enabled''\<close> by auto
      have "as p < num_actions"
        using \<open>_ \<in> set sync\<close> by (rule action_boundedI)
      moreover have "as p = a"
        using \<open>_ \<in> set sync\<close> usingT \<open>''actions''\<close> by auto
      ultimately have "a < num_actions"
        by auto
      from COM'_D[OF _ \<open>a < _\<close> \<open>p < _\<close>] that(2) obtain b' g f r l where
        "(L ! p, b', g, Com a, f, r, l) \<in> trans (N p)" "check_bexp s b' True"
        by - (frule list.set_sel, cases "hd (COM' ! p ! a)", fastforce)
      then show ?thesis
        usingT \<open>''maximal''\<close> using \<open>p < _\<close> \<open>p \<notin> set ps\<close> \<open>_ \<in> set sync\<close> \<open>as p = a\<close> \<open>b = _\<close> by force
    qed
    ultimately have ps'_eq: "filter (\<lambda>(i, a, strong). COM' ! i ! a \<noteq> []) sync = ps'"
      using \<open>distinct _\<close> ps' by (intro filter_distinct_eqI) (auto intro: distinct_mapI)
    then have "map fst (filter (\<lambda>(i, a, strong). COM' ! i ! a \<noteq> []) sync) = ps"
      using ps' by simp
    from \<open>_ = ps'\<close> have "length selected = length ps'"
      unfolding selected_def select_trans_from_sync_alt_def by simp
    then have "length selected = length ps"
      using ps' by auto
    have non_empty: "selected \<noteq> []" if "ps' \<noteq> []"
      using \<open>_ = ps'\<close> \<open>ps' \<noteq> []\<close> unfolding selected_def select_trans_from_sync_alt_def by simp
    have make_combsD:
      "map (\<lambda>p. (p, bs p, gs p, as p, fs p, rs p, ls' p)) ps \<in> set (make_combs_from_sync sync COM')"
      if "ps \<noteq> []"
    proof -
      have
        "let p = ps ! i in (p, bs p, gs p, as p, fs p, rs p, ls' p) \<in> set (selected ! i)"
        if "i<length ps" for i
      proof -
        define p where "p = ps ! i"
        from \<open>i < _\<close> ps' have [simp]: "i < length ps'"
          by auto
        have *: "as (fst (ps' ! i)) = fst (snd (ps' ! i))"
          usingT \<open>''actions''\<close>
          by (smt (z3) \<open>length selected = length ps'\<close> \<open>length selected = length ps\<close>
                all_set_conv_nth case_prod_beta' list_emb_set ps'(1) that)
        from \<open>i < length ps\<close> have "p \<in> set ps"
          unfolding p_def by auto
        from 01[OF this] ps'(2) show ?thesis
          unfolding p_def Let_def selected_def select_trans_from_sync_alt_def
          apply (subst (2) map_cong)
          apply (rule HOL.refl)
          apply (simp; fail)
          apply (clarsimp simp add: \<open>_ = ps'\<close> split: prod.split)
          apply (inst_existentials "snd (snd (ps' ! i))" "fst (snd (ps' ! i))" "fst (ps' ! i)")
          apply (auto simp: *)
          done
      qed
      moreover from non_empty ps'(2) \<open>ps \<noteq> []\<close> have "selected \<noteq> []"
        by auto
      ultimately show ?thesis
        using \<open>length selected = length ps'\<close> ps'(2)
        unfolding make_combs_def selected_def Let_def make_combs_from_sync_def
        by (auto simp: product_lists_set intro:list_all2_all_nthI)
    qed
    have make_combs_empty:
      "make_combs_from_sync sync COM' = [] \<longleftrightarrow> ps = []"
    proof (cases "ps = []")
      case True
      then show ?thesis
        using \<open>length _ = length ps\<close>
        unfolding make_combs_def selected_def make_combs_from_sync_def by auto
    next
      case False
      then show ?thesis
        using make_combsD by auto
    qed
    have is_sync_enabled: "is_sync_enabled sync COM'"
      unfolding is_sync_enabled_def list_all_iff using COM'_I1 usingT \<open>''enabled''\<close> by fastforce
    have "is_sync_enabled_committed sync COM' (get_committed L)" if "get_committed L \<noteq> []"
      "is_select_committed L ps"
    proof -
      from that obtain p where "p\<in>set ps" "L ! p \<in> committed (N p)"
        unfolding is_select_committed_def by untag (auto simp: get_committed_empty_iff)
      then have "(p, L ! p) \<in> set (get_committed L)"
        using \<open>p \<in> _\<close> range by - (erule get_committed_memI, auto)
      from 01[OF \<open>p \<in> _\<close>] obtain b where
        "(p, as p, b) \<in> set ps'"
        "(bs p, gs p, as p, fs p, rs p, ls' p) \<in> set (COM' ! p ! as p)"
        .
      with \<open>_ \<in> set (get_committed L)\<close> show ?thesis
        unfolding is_sync_enabled_committed_def
        using is_sync_enabled \<open>subseq ps' sync\<close> by (force simp: list_ex_iff list_all_iff)
    qed
    note make_combsD make_combs_empty is_sync_enabled this
  } note make_combsD = this(1) and make_combs_empty = this(2)
     and make_combs_sync_enabled = this(3) and make_combs_sync_enabled_committed = this(4)
  { fix sync xs
    assume "xs \<in> set (make_combs_from_sync sync COM')" and [tag \<open>''sync''\<close>]: "sync \<in> set syncs"
       and "is_sync_enabled sync COM'"
       and committed: "get_committed L = [] \<or> is_sync_enabled_committed sync COM' (get_committed L)"
    define ps bs gs as fs rs ls' where defs:
      "ps  = map fst xs"
      "bs  = (\<lambda>i. case the (map_of xs i) of (b, g, a, f, r, l') \<Rightarrow> b)"
      "gs  = (\<lambda>i. case the (map_of xs i) of (b, g, a, f, r, l') \<Rightarrow> g)"
      "as  = (\<lambda>i. case map_of xs i of Some (b, g, a, f, r, l') \<Rightarrow> a
        | None \<Rightarrow> SOME a. \<exists>strong. (i, a, strong) \<in> set sync
      )"
      "fs  = (\<lambda>i. case the (map_of xs i) of (b, g, a, f, r, l') \<Rightarrow> f)"
      "rs  = (\<lambda>i. case the (map_of xs i) of (b, g, a, f, r, l') \<Rightarrow> r)"
      "ls' = (\<lambda>i. case the (map_of xs i) of (b, g, a, f, r, l') \<Rightarrow> l')"
    let ?selected = "select_trans_from_sync sync COM'"
    let ?filtered = "filter (\<lambda>(i, a, strong). COM' ! i ! a \<noteq> []) sync"
    from \<open>xs \<in> _\<close> have "list_all2 (\<lambda>x ys. x \<in> set ys) xs ?selected"
      by (auto simp: make_combs_from_sync_def Let_def product_lists_set split: if_split_asm)
    then have xs_filtered:
      "list_all2 (\<lambda>(i, t) (i', a, strong). i = i' \<and> t \<in> set (COM' ! i ! a)) xs ?filtered"
      unfolding select_trans_from_sync_alt_def
      by (auto simp: list_all2_map2 split: if_split_asm elim: list_all2_mono)
    then have fst_eq: "list_all2 (\<lambda>x y. fst x = fst y) xs ?filtered"
      by (rule list_all2_mono, simp split: prod.split_asm)
    then have "map fst ?filtered = ps"
      unfolding \<open>ps = _\<close> using list.rel_map(2) list_all2_fst_aux by - (rule sym, blast)
    have "distinct ps"
      using action_set(3) \<open>sync \<in> _\<close> \<open>_ = ps\<close> distinct_map_filter by blast
    then have to_map: "map_of xs q = Some (b, g, a, r, f, l')"
      if "(q, b, g, a, r, f, l') \<in> set xs" for b q g a r f l'
      using that
      by (subst (asm) map_of_eq_Some_iff[of xs q, symmetric]) (auto simp: \<open>ps = map fst xs\<close>)
    have boundsD[intro]: "a < num_actions" "p < n_ps" if "(p, a, strong) \<in> set sync" for p a strong
      using action_set(1) that \<open>sync \<in> _\<close> unfolding n_ps_def by auto
    have subseq: "subseq (map fst xs) (map fst sync)"
    proof -
      from fst_eq have "map fst xs = map fst ?filtered"
        unfolding list_all2_map_eq_iff .
      then have "subseq (map fst xs) (map fst ?filtered)"
        by simp
      moreover have "subseq (map fst ?filtered) (map fst sync)"
        using subseq_filter_left subseq_map by blast
      ultimately show ?thesis
        by (rule subseq_order.trans)
    qed
    have actions: "as p = a" if "(p, a, strong) \<in> set sync" for p a strong
    proof -
      from that have "distinct (map fst sync)"
        using action_set(3) \<open>sync \<in> _\<close> by auto
      show ?thesis
      proof (cases "map_of xs p")
        case None
        then show ?thesis
          using \<open>distinct (map fst sync)\<close> that unfolding defs
          by (simp, intro some_equality) (auto dest: eq_key_imp_eq_value)
      next
        case (Some r)
        then obtain b g a1 f r l' where *: "map_of xs p = Some (b, g, a1, f, r, l')"
          by (cases r) auto
        from \<open>distinct (map fst sync)\<close> subseq have \<open>distinct (map fst xs)\<close>
          by (rule subseq_distinct)
        with xs_filtered * obtain a2 strong2 where
          "(b, g, a1, f, r, l') \<in> set (COM' ! p ! a2)" "(p, a2, strong2) \<in> set sync"
          by (subst (asm) map_of_eq_Some_iff; fastforce split: prod.splits dest!: list_all2_set1)
        with COM'_D have "a1 = a2"
          using action_set(1) \<open>sync \<in> _\<close> by fastforce
        moreover from \<open>distinct (map fst sync)\<close> \<open>(p, a2, _) \<in> _\<close> \<open>(p, a, _) \<in> _\<close> have "a2 = a"
          using eq_key_imp_eq_value by fastforce
        ultimately show ?thesis
          using * unfolding defs by simp
      qed
    qed
    then have [tag \<open>''actions''\<close>]: "\<forall>(p, a, _) \<in> set sync. as p = a"
      by auto
    { fix p assume "p \<in> set ps"
      consider strong where
        "(p, as p, strong) \<in> set sync"
        "(bs p, gs p, as p, fs p, rs p, ls' p) \<in> set (COM' ! p ! as p)"
      proof -
        from \<open>p \<in> _\<close> \<open>ps = map _ _\<close> obtain b g a r f l' where "(p, b, g, a, r, f, l') \<in> set xs"
          by auto
        with xs_filtered obtain a' strong where
          "(b, g, a, r, f, l') \<in> set (COM' ! p ! a')" "(p, a', strong) \<in> set sync"
          by (fastforce split: prod.splits dest!: list_all2_set1)
        then have "(bs p, gs p, as p, fs p, rs p, ls' p) \<in> set (COM' ! p ! a')"
          using \<open>_ \<in> set xs\<close>[THEN to_map] unfolding defs by simp
        with \<open>_ \<in> set xs\<close> \<open>_ \<in> set sync\<close> show ?thesis
          by (auto simp: actions intro: that)
      qed
    } note selectedE = this
    from \<open>sync \<in> _\<close> have *\<^cancel>\<open>[tag \<open>TRANS ''sync''\<close>]\<close> \<comment> \<open>XXX: Tags not working w/ assumptions\<close>:
      "(L ! p, bs p, gs p, Com (as p), fs p, rs p, ls' p) \<in> trans (N p)" if "p\<in>set ps" for p
      using that by (auto 4 3 intro: COM'_D[THEN conjunct1] elim: selectedE)
    from \<open>sync \<in> _\<close> \<open>_ = ps\<close> have "ps \<noteq> []"
      apply auto
      \<comment> \<open>See problem description below\<close>
      sorry
    with \<open>_ = ps\<close> have "?filtered \<noteq> []"
      by auto
    with \<open>sync \<in> _\<close> \<open>_ = ps\<close> have maximal [tag \<open>''maximal''\<close>]: "\<forall>q < n_ps. q \<notin> set ps \<longrightarrow>
        (\<forall>a b g f r l'.
          (L!q, b, g, Com a, f, r, l') \<in> trans (N q) \<and> (q, a, False) \<in> set sync
          \<longrightarrow> \<not> check_bexp s b True)"
      by (auto 4 3 dest!: COM_I COM'_I simp: set_map_filter product_lists_set split: if_split_asm)
    have "xs = map (\<lambda>p. (p, bs p, gs p, as p, fs p, rs p, ls' p)) ps"
      apply (intro nth_equalityI)
       apply (simp add: defs; fail)
      subgoal for i
        by (cases "xs ! i") (auto 4 4 simp: defs dest: to_map nth_mem)
      done
    have range[tag \<open>SEL ''range''\<close>]: \<open>set ps \<subseteq> {0..<n_ps}\<close>
      by (auto elim!: selectedE)
    have [tag \<open>SEL ''sublist''\<close>]: "subseq ps (map fst sync)"
      using \<open>map fst (filter (\<lambda>(i, a, strong). COM' ! i ! a \<noteq> []) sync) = ps\<close>
        subseq_filter_left subseq_map by blast
    have [tag \<open>''bexp''\<close>]: "\<forall>p\<in>set ps. check_bexp s (bs p) True"
    proof
      fix q assume "q \<in> set ps"
      then have "(bs q, gs q, as q, fs q, rs q, ls' q) \<in> set (COM' ! q ! as q)"
        by (rule selectedE)
      moreover have \<open>as q < num_actions\<close>
        using \<open>q \<in> _\<close> by (auto elim: selectedE)
     ultimately show "check_bexp s (bs q) True"
        using COM'_D  \<open>set ps \<subseteq> _\<close> \<open>q \<in> set ps\<close> by auto
    qed
    have [tag \<open>''only syncs''\<close>]: "\<forall>p<n_ps. p \<notin> fst ` set sync \<longrightarrow> p \<notin> set ps"
      by (meson img_fst selectedE)
    from \<open>is_sync_enabled _ _\<close> have [tag \<open>''enabled''\<close>]: "\<forall>(p, a, b)\<in>set sync. b \<longrightarrow> p \<in> set ps"
      unfolding is_sync_enabled_def list_all_iff using \<open>_ = ps\<close> by (auto 4 3)
    from * have "is_select_basic L s sync ps bs gs as fs rs ls'"
      unfolding is_select_basic_def by safe (tag; (assumption | simp))+
    moreover have "is_select_maximal L s sync ps"
      unfolding is_select_maximal_def by tag
    moreover from committed have "is_select_committed L ps"
    proof
      show "is_select_committed L ps" if "get_committed L = []"
        using that unfolding is_select_committed_def get_committed_empty_iff by (untag, blast)
      show "is_select_committed L ps" if
        "is_sync_enabled_committed sync COM' (get_committed L)"
      proof -
        from that obtain a b p where
          \<open>(p, a, b) \<in> set sync\<close> \<open>COM' ! p ! a \<noteq> []\<close> \<open>L ! p \<in> committed (N p)\<close> \<open>p < n_ps\<close>
          unfolding is_sync_enabled_committed_def list_ex_iff by (auto simp: get_committed_mem_iff)
        with \<open>_ = ps\<close> show ?thesis
          unfolding is_select_committed_def by (untag, force)
      qed
    qed
    moreover have "is_upds_idxs s (map fs ps) (mk_upds_idxs s (map fs ps))"
      using \<open>dom s = _\<close> range * by (elim is_upds_make_updsI3) auto
    moreover have "dom (mk_upds_idxs s (map fs ps)) = {0..<n_vs}"
      using \<open>is_upds_idxs s _ _\<close> * range \<open>dom s = _\<close> by (subst is_upds_dom3; (assumption | force))
    moreover have
      "map (\<lambda>(q, _, g, _, f, r, l). g) xs = map gs ps"
      "map (\<lambda>(q, _, g, _, f, r, l). f) xs = map fs ps"
      "map (\<lambda>(q, _, g, _, f, r, l). r) xs = map rs ps"
      unfolding defs by (auto simp: to_map)
    moreover have
      "fold (\<lambda>(q, _, g, _, f, r, l) L. L[q := l]) xs L = fold (\<lambda>p L. L[p := ls' p]) ps L"
      unfolding defs by (auto simp: fold_map to_map intro: fold_cong)
    ultimately consider ps bs gs as fs rs ls' where
      "is_select_basic L s sync ps bs gs as fs rs ls'" "is_select_maximal L s sync ps"
      "is_upds_idxs s (map fs ps) (mk_upds_idxs s (map fs ps))"
      "is_select_committed L ps"
      "map (\<lambda>(q, _, g, _, f, r, l). g) xs = map gs ps"
      "map (\<lambda>(q, _, g, _, f, r, l). f) xs = map fs ps"
      "map (\<lambda>(q, _, g, _, f, r, l). r) xs = map rs ps"
      "fold (\<lambda>(q, _, g, _, f, r, l) L. L[q := l]) xs L = fold (\<lambda>p L. L[p := ls' p]) ps L"
      "dom (mk_upds_idxs s (map fs ps)) = {0..<n_vs}"
      by blast
  } note make_combsI = this
  have make_transI:
    "(concat (map gs ps), Sync sync, concat (map rs ps), (L', s')) \<in> set (make_trans sync)"
    if assms: "is_sync_result L s sync ps as fs ls' L' s'"
    "is_select_basic L s sync ps bs gs as fs rs ls'" "is_select_maximal L s sync ps"
    "is_select_committed L ps"
    "bounded bounds s'"
    for sync ps bs gs as fs rs ls'
  proof -
    have "is_sync_enabled sync COM'"
      using assms by (intro make_combs_sync_enabled)
    moreover have
      "(concat (map gs ps), Sync sync, concat (map rs ps), L', s') \<in>
        set (make_trans_from_combs sync (L, s) (make_combs_from_sync sync COM'))"
      using assms \<open>dom s = _\<close>
      apply -
      apply (frule (1) make_combsD)
      subgoal non_empty_selection
        using make_combs_empty \<comment> \<open>Does not seem helpful, probably can be deleted\<close>
        \<comment> \<open>Basically, the question is what about syncs that only contain weak constraints?\<close>
        \<comment> \<open>Either make this a special case loop transition (in @{term make_trans}}\<close>
        \<comment> \<open>Or simply disallow it: a) via static constraints b) in the semantics\<close>
        \<comment> \<open>Tending towards b) now, but what do other tools do?\<close>
        sorry
      apply (clarsimp simp: make_trans_from_combs_def set_map_filter Let_def split: prod.split)
      unfolding is_sync_result_def is_select_basic_def apply (elim conjE)
      apply (tag- \<open>TRANS _\<close> \<open>SEL ''range''\<close> \<open>''upds''\<close> \<open>''new loc''\<close>)
      supply [forward4] = is_upds_dom3 is_updsD[rotated 3]
      apply frules_all
      apply intros
      apply (auto simp:  check_bounded_iff[symmetric] comp_def fold_map)
      done
    moreover have "is_sync_enabled_committed sync COM' (get_committed L)" if "get_committed L \<noteq> []"
      using assms that by (intro make_combs_sync_enabled_committed)
    ultimately show ?thesis
      unfolding make_trans_def by (simp add: set_map_filter Let_def split: prod.split)
  qed
  have make_transD:
    "\<exists>bs gs as fs rs ls' ps.
         is_select_basic L s sync ps bs gs as fs rs ls' \<and> is_select_maximal L s sync ps \<and>
         is_sync_result L s sync ps as fs ls' L' s' \<and> is_select_committed L ps \<and>
         g = concat (map gs ps) \<and>
         a = Sync sync \<and>
         r = concat (map rs ps) \<and>
         L' = fold (\<lambda>p L. L[p := ls' p]) ps L \<and>
         bounded bounds s'"
    if "sync \<in> set syncs" "(g, a, r, L', s') \<in> set (make_trans sync)"
    for sync g a r L' s'
    using that(1,2)
    unfolding make_trans_def make_trans_from_combs_def
    unfolding is_sync_result_def
    apply untag
    apply (clarsimp simp: Let_def set_map_filter split: if_split_asm)
     apply (erule (2) make_combsI, (simp; fail))
     apply (subst check_bounded_iff, simp split: if_split_asm)
     apply (intros; (assumption | simp); fail)
    apply (erule (1) make_combsI, (simp add: is_sync_enabled_committed_def; fail), (simp; fail))
    apply (subst check_bounded_iff, simp split: if_split_asm)
    apply (intros; (assumption | simp); fail)
    done

  show "(((L, s), g, a, r, L', s') \<in> trans_sync) =
        ((g, a, r, L', s') \<in> set (sync_trans_from (L, s)))"
    unfolding sync_trans_from_make_trans
    apply (clarsimp, safe)
    subgoal \<comment> \<open>\<open>\<longrightarrow>\<close>\<close>
      unfolding trans_sync_tagged_def
      apply clarsimp
      apply intros
       apply (tag- \<open>''sync''\<close>, simp add: syncs_def; fail)
      apply (rule make_transI)
      unfolding is_select_basic_def is_select_maximal_def is_sync_result_def is_select_committed_def
      apply safe
      preferT "''sync''" apply (tag, simp add: syncs_def; fail)
      preferT "''maximal''" apply (tag, fast)
      apply (tag, assumption)+
      apply (tag- \<open>''bounded''\<close>, assumption; fail)
      done
    subgoal \<comment> \<open>\<open>\<longleftarrow>\<close>\<close>
      apply (frule (1) make_transD)
      unfolding trans_sync_tagged_def
      apply clarsimp
      unfolding is_select_basic_def is_select_maximal_def is_sync_result_def is_select_committed_def
      apply (elims, intros)
      apply (rule HOL.refl, rule HOL.refl)
      preferT "''sync''" apply (tag, simp add: syncs_def; fail)
        apply (all \<open>(tag, assumption)?\<close>)
      preferT "''maximal''" subgoal premises prems[tagged] for bs gs as fs rs ls' ps
        by (tag, fast)
      subgoal "\<open>L \<in> states\<close>"
        using \<open>L \<in> states\<close> .
      preferT "''bounded''"
        by (tag, rule HOL.TrueI)
      done
qed


paragraph \<open>Refinement of the State Implementation\<close>

definition state_rel :: "(nat \<rightharpoonup> int) \<Rightarrow> int list \<Rightarrow> bool"
  where
  "state_rel s xs \<equiv> length xs = n_vs \<and> dom s = {0..<n_vs} \<and> (\<forall>i < n_vs. xs ! i = the (s i))"

definition loc_rel where
  "loc_rel \<equiv> {((L', s'), (L, s)) | L s L' s'. L' = L \<and> length L = n_ps \<and> state_rel s s'}"

lemma state_impl_abstract:
  "\<exists>L s. ((Li, si), (L, s)) \<in> loc_rel" if "length Li = n_ps" "length si = n_vs"
  using that unfolding loc_rel_def state_rel_def
  by (inst_existentials Li "\<lambda>i. if i < n_vs then Some (si ! i) else None")(auto split: if_split_asm)

lemma state_rel_left_unique:
  "l \<in> states' \<Longrightarrow> (li, l) \<in> loc_rel \<Longrightarrow> (li', l) \<in> loc_rel \<Longrightarrow> li' = li"
  unfolding loc_rel_def state_rel_def by (auto intro: nth_equalityI)

lemma state_rel_right_unique:
  "l \<in> states' \<Longrightarrow> l' \<in> states' \<Longrightarrow> (li, l) \<in> loc_rel \<Longrightarrow> (li, l') \<in> loc_rel \<Longrightarrow> l' = l"
  unfolding loc_rel_def state_rel_def
  apply clarsimp
  apply (rule ext)
  subgoal premises prems for L s s'1 s'2 x
  proof -
    show "s'1 x = s x"
    proof (cases "x < n_vs")
      case True
      then have "x \<in> dom s'1" "x \<in> dom s"
        using prems by auto
      with \<open>x < n_vs\<close> show ?thesis
        using prems(9) by auto
    next
      case False
      then have "x \<notin> dom s'1" "x \<notin> dom s"
        using prems by auto
      then show ?thesis
        by (auto simp: dom_def)
    qed
  qed
  done

end (* Anonymous context for simp setup *)

end (* Simple Network Impl nat *)

definition mk_upd_idxsi where
  "mk_upd_idxsi s upds_idxs \<equiv> mk_updsi s (sort_upds upds_idxs)"

definition mk_upds_idxsi where
  "mk_upds_idxsi s upds_idxs \<equiv> mk_updsi s (sort_upds (concat upds_idxs))"

context Generalized_Network_Impl_nat_defs
begin

definition
  "check_boundedi s =
    (\<forall>x < length s. fst (bounds_map x) \<le> s ! x \<and> s ! x \<le> snd (bounds_map x))"

definition
  "states'_memi \<equiv> \<lambda>(L, s). L \<in> states \<and> length s = n_vs \<and> check_boundedi s"

definition
  "int_trans_from_loc_impl p l L s \<equiv>
    let trans = trans_i_map p l
    in
    List.map_filter (\<lambda>(b, g, a, f, r, l').
      let s' = mk_upd_idxsi s f in
        if bvali s b \<and> check_boundedi s' then Some (g, Internal a, r, (L[p := l'], s'))
        else None
    ) trans"

definition
  "int_trans_from_vec_impl pairs L s \<equiv>
    concat (map (\<lambda>(p, l). int_trans_from_loc_impl p l L s) pairs)"

definition
  "int_trans_from_all_impl L s \<equiv>
    concat (map (\<lambda>p. int_trans_from_loc_impl p (L ! p) L s) [0..<n_ps])"

definition
  "int_trans_impl \<equiv> \<lambda> (L, s).
    let pairs = get_committed L in
    if pairs = []
    then int_trans_from_all_impl L s
    else int_trans_from_vec_impl pairs L s
  "

definition
  "make_trans_from_combs_impl sync \<equiv> \<lambda>(L, s) combs. List.map_filter (\<lambda>comb.
    let
      g = concat_map (\<lambda>(q, _, g, _, f, r, l). g) comb;
      r = concat_map (\<lambda>(q, _, g, _, f, r, l). r) comb;
      a = Sync sync;
      s' = mk_upds_idxsi s (map (\<lambda>(q, _, g, _, f, r, l). f) comb);
      L' = fold (\<lambda>(q, _, g, _, f, r, l) L. L[q := l]) comb L
    in if check_boundedi s' then Some (g, a, r, L', s') else None
  ) combs"

definition trans_from where
  "trans_from st = int_trans_from st @ sync_trans_from st"

definition
  "sync_trans_from_impl \<equiv> \<lambda>(L, s).
    let
      commited = get_committed L;
      Com = map (\<lambda>p. trans_com_grouped p (L ! p)) [0..<n_ps];
      Com = map (map (filter (\<lambda>(b, _). bvali s b))) Com
    in
    if commited = [] then
      concat (map (\<lambda>sync.
        let
          combs = make_combs_from_sync sync Com;
          is_enabled = is_sync_enabled sync Com
        in
          if is_enabled then make_trans_from_combs_impl sync (L, s) combs else []
        )
        syncs
      )
    else
      concat (map (\<lambda>sync.
        let
          combs = make_combs_from_sync sync Com;
          is_enabled = is_sync_enabled_committed sync Com commited
        in
          if is_enabled then make_trans_from_combs_impl sync (L, s) combs else []
        )
        syncs
      )
    "

definition trans_impl where
  "trans_impl st = int_trans_impl st @ sync_trans_from_impl st"

end (* Simple Network Impl nat defs *)


context Generalized_Network_Impl_nat
begin

lemma bval_bvali:
  "state_rel s si \<Longrightarrow> \<forall>x \<in> vars_of_bexp b. x \<in> dom s \<Longrightarrow> bval (the o s) b = bvali si b"
and eval_evali:
  "state_rel s si \<Longrightarrow> \<forall>x \<in> vars_of_exp e. x \<in> dom s \<Longrightarrow> eval (the o s) e = evali si e"
  by (induction b and e) (auto simp: state_rel_def)

lemma mk_upds_mk_updsi:
  "state_rel (mk_upds s upds) (mk_updsi si upds)"
  if assms: "state_rel s si" "\<forall> (_, e) \<in> set upds. \<forall>x \<in> vars_of_exp e. x < n_vs"
    "\<forall> (x, e) \<in> set upds. x < n_vs"
proof -
  have upd_stepI: "state_rel (mk_upd (x, e) s') (si'[x := evali si' e])"
    if "state_rel s' si'" "\<forall>x \<in> vars_of_exp e. x < n_vs" "x < n_vs"
    for s' si' x e
    using that assms unfolding mk_upd_def state_rel_def by (auto simp: state_rel_def eval_evali)
  from assms show ?thesis
  proof (induction upds arbitrary: s si)
    case Nil
    then show ?case
      by (simp add: mk_upds_def mk_updsi_def)
  next
    case (Cons upd upds)
    then show ?case
      by (simp add: mk_upds_def mk_updsi_def split: prod.splits) (rprem, auto intro!: upd_stepI)
  qed
qed

lemma check_bounded_check_boundedi:
  "check_bounded s = check_boundedi si" if "state_rel s si"
  using that unfolding check_bounded_def check_boundedi_def state_rel_def by auto

definition
  "valid_upd \<equiv> \<lambda>(x, e). x < n_vs \<and> (\<forall>x \<in> vars_of_exp e. x < n_vs)"

definition
  "valid_check b \<equiv> (\<forall>x \<in> vars_of_bexp b. x < n_vs)"

context includes lifting_syntax begin
notation rel_prod (infixr "\<times>\<^sub>R" 56)

abbreviation
  "valid_upd_idx \<equiv> \<lambda>(upd, idx). valid_upd upd"

(* XXX Move *)
definition is_at_least_equality where
  "is_at_least_equality R \<equiv> \<forall>x y. R x y \<longrightarrow> x = y" for R

named_theorems is_at_least_equality

lemma [is_at_least_equality]:
  "is_at_least_equality (=)"
  by (simp add: is_at_least_equality_def)

lemma [is_at_least_equality]:
  "is_at_least_equality R" if "is_equality R" for R
  using that by (simp add: is_at_least_equality_def is_equality_def)

lemma [is_at_least_equality]:
  "is_at_least_equality (eq_onp P)"
  by (simp add: is_at_least_equality_def eq_onp_def)

lemma is_at_least_equality_list_all2[is_at_least_equality]:
  "is_at_least_equality (list_all2 R)" if "is_at_least_equality R" for R
  using that unfolding is_at_least_equality_def
  by (auto simp: list.rel_eq dest: list_all2_mono[where Q = "(=)"])

lemma is_at_least_equality_rel_prod[is_at_least_equality]:
  "is_at_least_equality (R1 \<times>\<^sub>R R2)"
  if "is_at_least_equality R1" "is_at_least_equality R2" for R1 R2
  using that unfolding is_at_least_equality_def by auto

lemma is_at_least_equality_cong1:
  "(S1 ===> (=)) f f" if "is_at_least_equality S1" "is_at_least_equality S2" for S1 f
  using that unfolding is_at_least_equality_def by (intro rel_funI) auto

lemma is_at_least_equality_cong2:
  "(S1 ===> S2 ===> (=)) f f" if "is_at_least_equality S1" "is_at_least_equality S2" for S1 S2 f
  using that unfolding is_at_least_equality_def by (intro rel_funI) auto

lemma is_at_least_equality_cong3:
  "(S1 ===> S2 ===> S3 ===> (=)) f f"
  if "is_at_least_equality S1" "is_at_least_equality S2" "is_at_least_equality S3" for S1 S2 S3 f
  using that unfolding is_at_least_equality_def by (intro rel_funI) force

lemma is_at_least_equality_Let:
  "(S ===> ((=) ===> R) ===> R) Let Let" if "is_at_least_equality S" for R
  using that unfolding is_at_least_equality_def
  by (intro rel_funI) (erule Let_transfer[THEN rel_funD, THEN rel_funD, rotated], auto)

lemma map_transfer_length:
  fixes R S n
  shows
    "((R ===> S)
      ===> (\<lambda>x y. list_all2 R x y \<and> length x = n)
      ===> (\<lambda>x y. list_all2 S x y \<and> length x = n))
    map map"
  apply (intro rel_funI conjI)
  apply (erule list.map_transfer[THEN rel_funD, THEN rel_funD], erule conjunct1)
  apply simp
  done

lemma upt_0_transfer:
  "(eq_onp (\<lambda>x. x = 0) ===> eq_onp (\<lambda>x. x = n) ===> list_all2 (eq_onp (\<lambda>x. x < n))) upt upt" for n
  apply (intro rel_funI upt_transfer_upper_bound[THEN rel_funD, THEN rel_funD])
   apply (assumption | erule eq_onp_to_eq)+
  done

lemma upt_length_transfer:
  "(eq_onp (\<lambda>x. x = 0) ===> eq_onp (\<lambda>x. x = n)
    ===> (\<lambda> x y. list_all2 (eq_onp (\<lambda>x. x < n)) x y \<and> length x = n)) upt upt" for n
  apply (intro rel_funI conjI upt_0_transfer[THEN rel_funD, THEN rel_funD], assumption+)
  apply (simp add: eq_onp_def)
  done

lemma case_prod_transfer_strong:
  fixes A B C
  assumes "\<And> x y. A1 x y \<Longrightarrow> A x y" "\<And> x y. B1 x y \<Longrightarrow> B x y"
  shows "((A ===> B ===> C) ===> A1 \<times>\<^sub>R B1 ===> C) case_prod case_prod"
  apply (intro rel_funI)
  apply clarsimp
  apply (drule assms)+
  apply (drule (1) rel_funD)+
  apply assumption
  done

lemma concat_transfer_strong:
  fixes A B C
  assumes "\<And>x y. A x y \<Longrightarrow> B x y" "\<And> x y. C x y \<Longrightarrow> list_all2 (list_all2 A) x y"
  shows "(C ===> list_all2 B) concat concat"
  apply (intro rel_funI concat_transfer[THEN rel_funD])
  apply (drule assms)
  apply (erule list_all2_mono)
  apply (erule list_all2_mono)
  apply (erule assms)
  done

lemma map_transfer_strong:
  fixes A B C
  assumes "\<And>xs ys. C xs ys \<Longrightarrow> list_all2 A xs ys"
  shows "((A ===> B) ===> C ===> list_all2 B) map map"
  apply (intro rel_funI)
  apply (erule list.map_transfer[THEN rel_funD, THEN rel_funD])
  apply (erule assms)
  done

lemma list_update_transfer':
  fixes A :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  shows "(list_all2 A ===> eq_onp (\<lambda>i. i<n_ps) ===> A ===> list_all2 A) list_update list_update"
  apply (intro rel_funI)
  apply (rule list_update_transfer[THEN rel_funD, THEN rel_funD, THEN rel_funD])
    apply (auto simp: eq_onp_def)
  done

lemma list_update_transfer'':
  fixes A :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and n
  shows "((\<lambda> x y. list_all2 A x y \<and> length x = n) ===> eq_onp (\<lambda>i. i<n) ===> A
    ===> (\<lambda> x y. list_all2 A x y \<and> length x = n)) list_update list_update"
  apply (intro rel_funI conjI)
  subgoal
    apply (erule conjE)
    apply (rule List.list_update_transfer[THEN rel_funD, THEN rel_funD, THEN rel_funD])
    apply (assumption | elim eq_onp_to_eq)+
    done
  apply simp
  done

lemma list_update_transfer''':
  fixes A :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and n
  shows "((\<lambda> x y. list_all2 A x y \<and> length x = n) ===> (=) ===> A
    ===> (\<lambda> x y. list_all2 A x y \<and> length x = n)) list_update list_update"
  apply (intro rel_funI conjI)
  subgoal
    apply (erule conjE)
    apply (rule List.list_update_transfer[THEN rel_funD, THEN rel_funD, THEN rel_funD])
    apply (assumption | elim eq_onp_to_eq)+
    done
  apply simp
  done

lemma fold_transfer_strong:
  fixes A B
  assumes "\<And>x y. A1 x y \<Longrightarrow> A x y" "\<And>x y. B1 x y \<Longrightarrow> B x y" "\<And>x y. B x y \<Longrightarrow> B2 x y"
    "\<And>x y. B x y \<Longrightarrow> B3 x y"
  shows "((A ===> B2 ===> B1) ===> list_all2 A1 ===> B ===> B3) fold fold"
  apply (intro rel_funI, rule assms)
  apply (rule fold_transfer[THEN rel_funD, THEN rel_funD, THEN rel_funD])
    apply (intro rel_funI)
    apply (drule rel_funD, erule assms)
    apply (drule rel_funD, erule assms, erule assms)
   apply assumption+
  done

lemma bval_bvali_transfer[transfer_rule]:
  "(state_rel ===> eq_onp valid_check ===> (=)) (\<lambda> s. bval (the o s)) bvali"
  by (intro rel_funI) (auto simp: eq_onp_def valid_check_def state_rel_def intro!: bval_bvali)

lemma mk_upds_mk_updsi_transfer[transfer_rule]:
  "(state_rel ===> list_all2 (eq_onp valid_upd) ===> state_rel) mk_upds mk_updsi"
  apply (intro rel_funI)
  subgoal for x y upds upds'
    apply (subgoal_tac "upds' = upds")
     apply auto
     apply (rule mk_upds_mk_updsi)
       apply assumption
    subgoal
      by (smt case_prodI2 case_prod_conv eq_onp_def list_all2_same valid_upd_def)
    subgoal
      by (smt case_prodE case_prod_conv eq_onp_def list_all2_same valid_upd_def)
    subgoal
      by (metis eq_onp_to_eq list.rel_eq_onp)
    done
  done

\<comment> \<open>XXX: move\<close>
lemma insort_key_transfer[transfer_rule]:
  "((R ===> (=)) ===> R ===> list_all2 R ===> list_all2 R) insort_key insort_key"
  proof (intro rel_funI)
  fix f :: "'a \<Rightarrow> 'b" and g :: "'c \<Rightarrow> 'b" and x :: 'a and y :: 'c and xs ys
  assume
    rel[THEN rel_funD]: "(R ===> (=)) f g" and
    "R x y" and "list_all2 R xs ys"
  from this(3,2) show "list_all2 R (insort_key f x xs) (insort_key g y ys)"
  proof (induction arbitrary: x y)
    case Nil
    then show ?case
      by simp
  next
    case (Cons x' xs y' ys)
    then show ?case
      by (auto dest!: rel)
  qed
qed

\<comment> \<open>XXX: move\<close>
lemma sort_key_transfer[transfer_rule]:
  "((R ===> (=)) ===> list_all2 R ===> list_all2 R) sort_key sort_key"
  unfolding sort_key_def by transfer_prover

lemma valid_upd_idx_snd_transfer:
  "(eq_onp valid_upd_idx ===> (=)) snd snd"
  by (intro rel_funI) (auto simp: eq_onp_def)

lemma valid_upd_idx_fst_transfer:
  "(eq_onp valid_upd_idx ===> eq_onp valid_upd) fst fst"
  by (intro rel_funI) (auto simp: eq_onp_def)

lemma sort_upds_transfer:
  "(list_all2 (eq_onp valid_upd_idx) ===> list_all2 (eq_onp valid_upd))
    sort_upds sort_upds"
  supply [transfer_rule] = valid_upd_idx_fst_transfer valid_upd_idx_snd_transfer
  unfolding sort_upds_def by transfer_prover

lemma mk_upd_idxs_mk_upds_idxsi_transfer[transfer_rule]:
  "(state_rel ===> list_all2 (eq_onp valid_upd_idx) ===> state_rel)
    mk_upd_idxs mk_upd_idxsi"
  supply [transfer_rule] = sort_upds_transfer
  unfolding mk_upd_idxs_def mk_upd_idxsi_def by transfer_prover

lemma mk_upds_idxs_mk_upds_idxsi_transfer[transfer_rule]:
  "(state_rel ===> list_all2 (list_all2 (eq_onp valid_upd_idx)) ===> state_rel)
    mk_upds_idxs mk_upds_idxsi"
  supply [transfer_rule] = sort_upds_transfer
  unfolding mk_upds_idxs_def mk_upds_idxsi_def by transfer_prover

lemma check_bounded_transfer[transfer_rule]:
  "(state_rel ===> (=)) check_bounded check_boundedi"
  by (simp add: check_bounded_check_boundedi rel_funI)

lemma trans_map_transfer:
  "(eq_onp (\<lambda>i. i<n_ps) ===> (=) ===>
    list_all2 (
      eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (pred_act (\<lambda>x. x < num_actions))
      \<times>\<^sub>R list_all2 (eq_onp valid_upd_idx) \<times>\<^sub>R (=)
   )) trans_map trans_map"
  apply (intro rel_funI, simp add: eq_onp_def, intro list.rel_refl_strong)
  apply clarsimp
  apply (auto 4 4 dest!: trans_mapD dest: action_setD var_setD var_setD2 intro: list.rel_refl_strong
                  simp: valid_upd_def valid_check_def
        )
  done

lemma trans_map_transfer':
  "(eq_onp (\<lambda>i. i<n_ps) ===> (=) ===>
    list_all2 (eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R list_all2 (eq_onp valid_upd_idx) \<times>\<^sub>R (=))
  ) trans_map trans_map"
  apply (intro rel_funI, simp add: eq_onp_def, intro list.rel_refl_strong)
  apply clarsimp
  apply (intro conjI list.rel_refl_strong)
    apply (auto 4 4 dest: var_setD trans_mapD var_setD2 simp: valid_upd_def valid_check_def)
  done

\<comment> \<open>XXX: move\<close>
lemma map_filter_transfer[transfer_rule]:
  "((S ===> rel_option R) ===> list_all2 S ===> list_all2 R) List.map_filter List.map_filter"
  unfolding map_filter_def
  apply (intro rel_funI)
  subgoal for f g xs ys
    apply (rule list.map_transfer[THEN rel_funD, THEN rel_funD, of "\<lambda> x y. f x \<noteq> None \<and> S x y"])
    apply (rule rel_funI)
    subgoal for a b
      by (cases "f a") (auto simp: option_rel_Some1 option_rel_Some2 dest!: rel_funD)
    subgoal premises prems
      using prems(2,1) by (induction rule: list_all2_induct) (auto dest: rel_funD)
    done
  done

lemma trans_i_map_transfer[transfer_rule]:
  "(eq_onp (\<lambda>i. i<n_ps) ===> (=) ===>
    list_all2 (eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R list_all2 (eq_onp valid_upd_idx) \<times>\<^sub>R (=))
   ) trans_i_map trans_i_map"
  supply [transfer_rule] = trans_map_transfer'
  unfolding trans_i_map_def by transfer_prover

lemma int_trans_from_loc_transfer[transfer_rule]:
  "(eq_onp (\<lambda>i. i<n_ps) ===> (=) ===> (\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) ===> state_rel
    ===> list_all2((=) \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R (\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel))
  int_trans_from_loc int_trans_from_loc_impl"
  supply [transfer_rule] = list_update_transfer''
  unfolding int_trans_from_loc_def int_trans_from_loc_impl_def Let_def by transfer_prover

lemma n_ps_transfer:
  "eq_onp (\<lambda>x. x = n_ps) n_ps n_ps"
  by (simp add: eq_onp_def)

lemma zero_nat_transfer:
  "(=) 0 (0::nat)"
  ..

lemma int_trans_from_all_transfer[transfer_rule]:
  "((\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) ===> state_rel
    ===> list_all2((=) \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R (\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel))
  int_trans_from_all int_trans_from_all_impl"
  supply [transfer_rule] = zero_nat_transfer n_ps_transfer
  unfolding int_trans_from_all_def int_trans_from_all_impl_def Let_def
  by transfer_prover

lemma int_trans_from_vec_transfer[transfer_rule]:
  "(list_all2 (eq_onp (\<lambda>x. x < n_ps) \<times>\<^sub>R (=)) ===> (\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps)
    ===> state_rel
    ===> list_all2((=) \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R (\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel))
  int_trans_from_vec int_trans_from_vec_impl"
  unfolding int_trans_from_vec_def int_trans_from_vec_impl_def Let_def
  by transfer_prover

private definition R where "R \<equiv> (\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps)"

lemma get_committed_transfer[transfer_rule]:
  "((\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) ===> list_all2 (eq_onp (\<lambda>x. x < n_ps) \<times>\<^sub>R (=)))
    get_committed get_committed"
proof -
  have [transfer_rule]:
    "R automata automata"
    unfolding R_def by (simp add: n_ps_def list.rel_eq)
  show ?thesis
  supply [transfer_rule] = zero_nat_transfer n_ps_transfer
  unfolding get_committed_def
  unfolding Let_def
  apply transfer_prover_start
  using [[goals_limit=15]]
  prefer 8
  apply transfer_step
                prefer 8
  unfolding R_def
       apply transfer_step+
  apply transfer_prover
  done
qed

lemma eq_transfer:
  "(list_all2 (eq_onp (\<lambda>x. x < n_ps) \<times>\<^sub>R (=)) ===> list_all2 (=) ===> (=)) (=) (=)"
  unfolding eq_onp_def
  apply (intro rel_funI)
  apply (drule list_all2_mono[where Q = "(=)"])
   apply (auto simp add: list.rel_eq rel_prod.simps)
  done

lemma int_trans_from_transfer:
  "((\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel
  ===> list_all2 ((=) \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R ((\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel)))
  int_trans_from int_trans_impl"
  supply [transfer_rule] = eq_transfer
  unfolding int_trans_impl_def int_trans_from_def Let_def
  by transfer_prover

lemmas rel_elims =
  rel_prod.cases
  rel_funD

lemmas rel_intros =
  rel_funI


lemma trans_com_map_transfer[transfer_rule]:
  "(eq_onp (\<lambda>i. i<n_ps) ===> (=)
    ===> list_all2 (
      eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>a. a < num_actions)
      \<times>\<^sub>R list_all2 (eq_onp valid_upd_idx) \<times>\<^sub>R (=))
   ) trans_com_map trans_com_map"
  supply [transfer_rule] = trans_map_transfer[folded act.rel_eq_onp]
  unfolding trans_com_map_def by transfer_prover

lemma actions_by_state_transfer[transfer_rule]:
  "(eq_onp (\<lambda>i. i < n_ps) ===>
    list_all2 ((=) \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>i. i < n) \<times>\<^sub>R (=)) ===>
    (\<lambda> x y. list_all2 (list_all2 (
      eq_onp (\<lambda>i. i<n_ps) \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>x. x < n) \<times>\<^sub>R (=))) x y \<and> length x = n) ===>
    (\<lambda> x y. list_all2 (list_all2
      (eq_onp (\<lambda>i. i<n_ps) \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>x. x < n) \<times>\<^sub>R (=))) x y \<and> length x = n)
  )
  actions_by_state actions_by_state" for n
  supply [transfer_rule] = list_update_transfer''
  unfolding actions_by_state_def by transfer_prover

lemma actions_by_state_transfer'[transfer_rule]:
  "(
    eq_onp (\<lambda>i. i < n_ps) ===>
    list_all2 (
      eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>i. i < n) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=)) ===>
    (\<lambda> x y. list_all2 (list_all2 (
        eq_onp (\<lambda>i. i<n_ps) \<times>\<^sub>R eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>x. x < n)
        \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=))) x y \<and> length x = n) ===>
    (\<lambda> x y. list_all2 (list_all2 (
        eq_onp (\<lambda>i. i<n_ps) \<times>\<^sub>R eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>x. x < n)
        \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=))) x y \<and> length x = n)
  )
  actions_by_state actions_by_state"
  for n
  supply [transfer_rule] = list_update_transfer''
  unfolding actions_by_state_def by transfer_prover

lemma transfer_consts:
  "(eq_onp (\<lambda>x. x = num_actions)) num_actions num_actions" "(eq_onp (\<lambda>x. x = 0)) (0::nat) 0"
  "(eq_onp (\<lambda>x. x = n_ps)) n_ps n_ps" 
  by (auto simp: eq_onp_def)

lemma all_actions_by_state_transfer[transfer_rule]:
  "
  (
    (eq_onp (\<lambda>i. i<n_ps) ===> (=) ===>
      list_all2 (
        eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>i. i < num_actions)
        \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=)))
    ===>
    (\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps)
    ===>
    (\<lambda> x y. list_all2 (list_all2 (
      eq_onp (\<lambda>i. i<n_ps) \<times>\<^sub>R eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>i. i<num_actions)
      \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=))) x y \<and> length x = num_actions)
  )
  all_actions_by_state all_actions_by_state"
  supply [transfer_rule] = map_transfer_length upt_0_transfer upt_length_transfer transfer_consts
    n_ps_transfer
  unfolding all_actions_by_state_def by transfer_prover

lemma all_actions_from_vec_transfer[transfer_rule]:
  "
  (
    (eq_onp (\<lambda>i. i<n_ps) ===> (=) ===> list_all2 (eq_onp valid_check \<times>\<^sub>R (=) 
      \<times>\<^sub>R eq_onp (\<lambda>i. i < num_actions) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=)))
    ===>
    list_all2 (eq_onp (\<lambda>i. i < n_ps) \<times>\<^sub>R (=))
    ===>
    (\<lambda> x y. list_all2 (list_all2 (eq_onp (\<lambda>i. i<n_ps) \<times>\<^sub>R eq_onp valid_check \<times>\<^sub>R (=)
      \<times>\<^sub>R eq_onp (\<lambda>i. i<num_actions) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=))) x y
      \<and> length x = num_actions)
  )
  all_actions_from_vec all_actions_from_vec"
  supply [transfer_rule] = map_transfer_length upt_length_transfer transfer_consts
  unfolding all_actions_from_vec_def all_actions_from_vec_def by transfer_prover

lemma Let_transfer_bin_aux:
  "((\<lambda>x y. list_all2 (list_all2
    (eq_onp (\<lambda>i. i < n_ps) \<times>\<^sub>R eq_onp valid_check \<times>\<^sub>R list_all2 (rel_acconstraint (=) (=)) \<times>\<^sub>R
         eq_onp (\<lambda>i. i < num_actions) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R list_all2 (=) \<times>\<^sub>R (=))) x y
    \<and> length x = num_actions) ===>
   ((\<lambda>x y. list_all2 (list_all2
    ((=) \<times>\<^sub>R eq_onp valid_check \<times>\<^sub>R list_all2 (rel_acconstraint (=) (=)) \<times>\<^sub>R
         (=) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R list_all2 (=) \<times>\<^sub>R (=))) x y
    \<and> length x = num_actions) ===>
   list_all2
    (list_all2 (rel_acconstraint (=) (=)) \<times>\<^sub>R rel_label (=) \<times>\<^sub>R
     list_all2 (=) \<times>\<^sub>R (\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel)) ===>
  list_all2
    (list_all2 (rel_acconstraint (=) (=)) \<times>\<^sub>R rel_label (=) \<times>\<^sub>R
     list_all2 (=) \<times>\<^sub>R (\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel))
  Let Let"
  unfolding Let_def
  by (intro rel_funI, drule rel_funD)
     (auto simp: eq_onp_def elim!: list_all2_mono prod.rel_mono_strong)

abbreviation
  "state'_rel n \<equiv> (\<lambda>x y. list_all2 (=) x y \<and> length x = n) \<times>\<^sub>R state_rel"

abbreviation
  "sync_rel \<equiv> list_all2 (eq_onp (\<lambda>x. x < n_ps) \<times>\<^sub>R eq_onp (\<lambda>x. x < num_actions) \<times>\<^sub>R (=))"

lemma make_trans_from_combs_transfer:
  "(list_all2 ((=) \<times>\<^sub>R (=) \<times>\<^sub>R (=)) ===> state'_rel n
  ===> list_all2 (list_all2
        ((=) \<times>\<^sub>R eq_onp valid_check \<times>\<^sub>R list_all2 (=) \<times>\<^sub>R (=) \<times>\<^sub>R list_all2 (eq_onp valid_upd_idx)
        \<times>\<^sub>R list_all2 (=) \<times>\<^sub>R (=))) ===>
  list_all2 (
    list_all2 (=) \<times>\<^sub>R (=) \<times>\<^sub>R list_all2 (=) \<times>\<^sub>R (\<lambda>x y. list_all2 (=) x y \<and> length x = n) \<times>\<^sub>R state_rel
  )) make_trans_from_combs make_trans_from_combs_impl"
  supply [transfer_rule] = list_update_transfer'''
  unfolding make_trans_from_combs_def make_trans_from_combs_impl_def by transfer_prover


text \<open>We are using the ``equality version'' of parametricty for @{term "(!)"} here.\<close>
lemma actions_by_state'_transfer[transfer_rule]:
  "(list_all2 (
    eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>x. x < num_actions)
    \<times>\<^sub>R list_all2 (eq_onp valid_upd_idx) \<times>\<^sub>R (=))
  ===> (\<lambda> x y. list_all2 (
    list_all2 (
      eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>x. x < num_actions)
      \<times>\<^sub>R list_all2 (eq_onp valid_upd_idx) \<times>\<^sub>R (=))) x y
    \<and> length x = num_actions
  ))
  actions_by_state' actions_by_state'"
  supply [transfer_rule] = transfer_consts
    upt_length_transfer
    map_transfer_length
    list_update_transfer''
  unfolding actions_by_state'_def by transfer_prover

lemma trans_com_grouped_transfer[transfer_rule]:
  "(eq_onp (\<lambda>i. i<n_ps) ===> (=)
  ===> (\<lambda> x y. list_all2 (
    list_all2 (
      eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>x. x < num_actions)
      \<times>\<^sub>R list_all2 (eq_onp valid_upd_idx) \<times>\<^sub>R (=))) x y
    \<and> length x = num_actions
  )) trans_com_grouped trans_com_grouped"
  unfolding trans_com_grouped_def by transfer_prover

lemma make_combs_transfer:
  fixes R
  assumes "\<And>x y. R x y \<Longrightarrow> x = y"
  shows
    "(eq_onp (\<lambda>x. x < n_ps)
  ===> eq_onp (\<lambda>x. x < num_actions)
  ===> (\<lambda>x y. list_all2 (\<lambda>x y. list_all2 (list_all2 R) x y \<and> length x = num_actions) x y
        \<and> length x = n_ps)
  ===> list_all2 (list_all2 (eq_onp (\<lambda>x. x < n_ps) \<times>\<^sub>R R)))
  make_combs make_combs"
proof -
  have [transfer_rule]:
    "(eq_onp (\<lambda>x. x < n_ps) ===> eq_onp (\<lambda>x. x < n_ps) ===> (=)) (=) (=)"
    "(list_all2 R ===> list_all2 R ===> (=)) (=) (=)"
    "(list_all2 (list_all2 (eq_onp (\<lambda>x. x < n_ps) \<times>\<^sub>R R))
      ===> list_all2 (list_all2 (eq_onp (\<lambda>x. x < n_ps) \<times>\<^sub>R R)) ===> (=)) (=) (=)"
      apply (auto simp: eq_onp_def)
    subgoal
      by (smt assms list.rel_eq list_all2_mono rel_funI)
    subgoal
      by (smt assms fun.rel_eq list_all2_eq list_all2_mono rel_fun_mono rel_prod.cases)
    done
  show ?thesis
    supply [transfer_rule] = upt_0_transfer transfer_consts
    unfolding make_combs_def by transfer_prover
qed

lemma make_combs_from_sync_transfer:
  fixes R
  assumes "\<And>x y. R x y \<Longrightarrow> x = y"
  shows
    "(sync_rel
  ===> (\<lambda>x y. list_all2 (\<lambda>x y. list_all2 (list_all2 R) x y \<and> length x = num_actions) x y
        \<and> length x = n_ps)
  ===> list_all2 (list_all2 (eq_onp (\<lambda>x. x < n_ps) \<times>\<^sub>R R)))
  make_combs_from_sync make_combs_from_sync"
  unfolding make_combs_from_sync_def select_trans_from_sync_def List.null_def[symmetric]
  by transfer_prover

lemma concat_length_transfer:
  "((\<lambda> x y. list_all2 (list_all2 A) x y \<and> length x = n) ===> list_all2 A) concat concat" for A n
  by (intro rel_funI concat_transfer[THEN rel_funD], elim conjunct1)

definition is_in_fst_set where "is_in_fst_set x xs \<equiv> x \<in> fst ` set xs" for x xs

lemma is_in_fst_set_transfer [transfer_rule]:
  fixes R
  assumes [transfer_rule]: "bi_unique R"
  shows "(R ===> list_all2 (R \<times>\<^sub>R S) ===> (=)) is_in_fst_set is_in_fst_set"
  unfolding is_in_fst_set_def by transfer_prover

lemma eq_onp_bi_unique[transfer_rule]: "bi_unique (eq_onp R)" for R
  unfolding bi_unique_def eq_onp_def by auto

lemma syncs_transfer[transfer_rule]:
  "(list_all2 sync_rel) syncs syncs"
  using action_set(1) by (intro list.rel_refl_strong) (auto 4 3 simp: eq_onp_def n_ps_def)

lemma sync_trans_from_transfer:
  "((\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel
  ===> list_all2 ((=) \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R ((\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel)))
  sync_trans_from sync_trans_from_impl"
proof -

  have make_trans_from_combs_impl_transfer[transfer_rule]: "
    (sync_rel ===> state'_rel n_ps ===>
      list_all2
       (list_all2
         (eq_onp (\<lambda>x. x < n_ps) \<times>\<^sub>R
          eq_onp valid_check \<times>\<^sub>R
          list_all2 (rel_acconstraint (=) (=)) \<times>\<^sub>R
          eq_onp (\<lambda>x. x < num_actions) \<times>\<^sub>R
          list_all2 (eq_onp valid_upd_idx) \<times>\<^sub>R list_all2 (=) \<times>\<^sub>R (=))) ===>
      list_all2
       (list_all2 (=) \<times>\<^sub>R
        (=) \<times>\<^sub>R
        list_all2 (=) \<times>\<^sub>R (\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel))
     make_trans_from_combs make_trans_from_combs_impl"
    apply (intro rel_funI)
    apply (rule make_trans_from_combs_transfer[THEN rel_funD, THEN rel_funD, THEN rel_funD])
      apply (elim rel_prod.cases)
    subgoal
      apply (elim list_all2_mono rel_prod.cases)
      apply (simp only:)
      apply (intro rel_prod.intros)
        apply (assumption | simp add: eq_onp_def acconstraint.rel_eq)+
      done
     apply assumption
    subgoal
      apply (elim list_all2_mono rel_prod.cases)
      apply (simp only:)
      apply (intro rel_prod.intros)
            apply (assumption | simp add: eq_onp_def acconstraint.rel_eq)+
      done
    done

  have is_sync_enabled_transfer[transfer_rule]: "
    (sync_rel ===>
        (\<lambda>x y. list_all2 (\<lambda>x y. list_all2 (list_all2
          (eq_onp valid_check \<times>\<^sub>R list_all2 (rel_acconstraint (=) (=)) \<times>\<^sub>R
           eq_onp (\<lambda>x. x < num_actions) \<times>\<^sub>R
           list_all2 (eq_onp valid_upd_idx) \<times>\<^sub>R list_all2 (=) \<times>\<^sub>R (=)))
          x y \<and> length x = num_actions) x y \<and> length x = n_ps) ===>
        (=)
    ) is_sync_enabled is_sync_enabled"
    unfolding is_sync_enabled_def List.null_def[symmetric] by transfer_prover

  have is_sync_enabled_committed_transfer[transfer_rule]: "
    (sync_rel ===>
        (\<lambda>x y. list_all2 (\<lambda>x y. list_all2 (list_all2
          (eq_onp valid_check \<times>\<^sub>R list_all2 (rel_acconstraint (=) (=))
          \<times>\<^sub>R eq_onp (\<lambda>x. x < num_actions) \<times>\<^sub>R list_all2 (eq_onp valid_upd_idx)
          \<times>\<^sub>R list_all2 (=) \<times>\<^sub>R (=)))
          x y \<and> length x = num_actions) x y \<and> length x = n_ps) ===>
        list_all2 (eq_onp (\<lambda>x. x < n_ps) \<times>\<^sub>R (=)) ===>
        (=)
    ) is_sync_enabled_committed is_sync_enabled_committed"
    unfolding is_sync_enabled_committed_def List.null_def[symmetric] is_in_fst_set_def[symmetric]
    by transfer_prover

  have make_combs_from_sync_transfer: "
    (sync_rel ===>
        (\<lambda>x y. list_all2 (\<lambda>x y. list_all2 (list_all2
          (eq_onp valid_check \<times>\<^sub>R list_all2 (rel_acconstraint (=) (=))
          \<times>\<^sub>R eq_onp (\<lambda>x. x < num_actions) \<times>\<^sub>R list_all2 (eq_onp valid_upd_idx)
          \<times>\<^sub>R list_all2 (=) \<times>\<^sub>R (=)))
          x y \<and> length x = num_actions) x y \<and> length x = n_ps) ===>
        list_all2 (list_all2 (eq_onp (\<lambda>x. x < n_ps) \<times>\<^sub>R
          eq_onp valid_check \<times>\<^sub>R list_all2 (rel_acconstraint (=) (=))
          \<times>\<^sub>R eq_onp (\<lambda>x. x < num_actions) \<times>\<^sub>R list_all2 (eq_onp valid_upd_idx)
          \<times>\<^sub>R list_all2 (=) \<times>\<^sub>R (=))
        )
    ) make_combs_from_sync make_combs_from_sync"
    apply (intro rel_funI)
    apply (rule make_combs_from_sync_transfer[THEN rel_funD, THEN rel_funD])
    apply (clarsimp simp add: acconstraint.rel_eq list.rel_eq eq_onp_def)
    using list.rel_mono_strong list_all2_eq apply blast
     apply assumption+
    done

  show ?thesis
    supply [transfer_rule] =
      transfer_consts
      map_transfer_length
      upt_length_transfer
      make_combs_from_sync_transfer
    unfolding sync_trans_from_def sync_trans_from_impl_def Let_def by transfer_prover
qed

lemma trans_from_transfer:
  "((\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel
  ===> list_all2 ((=) \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R ((\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel)))
  trans_from trans_impl"
  supply [transfer_rule] = int_trans_from_transfer sync_trans_from_transfer
  unfolding trans_from_def trans_impl_def by transfer_prover

lemma list_all2_swap:
  "list_all2 S ys xs" if "list_all2 R xs ys" "S = (\<lambda>x y. R y x)" for R S
  using list_all2_swap that by blast

lemma swap_rel_prod: "(\<lambda> x y. (R \<times>\<^sub>R S) y x) = (\<lambda>x y. R y x) \<times>\<^sub>R (\<lambda>x y. S y x)" for R S
  by (intro ext) auto

lemma swap_eq:
  "(\<lambda>x y. y = x) = (=)"
  by auto

lemma trans_from_refine:
  "(trans_impl, trans_from) \<in> fun_rel_syn loc_rel (list_rel (Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r loc_rel))"
proof -
  have [rel2p]:
    "rel2p loc_rel = (\<lambda> x y. ((\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel) y x)"
    unfolding loc_rel_def rel2p_def by (intro ext) (auto simp: list.rel_eq)
  have "rel2p (fun_rel_syn
      {((L', s'), L, s) |L s L' s'. L' = L \<and> length L = n_ps \<and> state_rel s s'}
      (\<langle>Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r loc_rel\<rangle>list_rel))
    trans_impl trans_from"
    unfolding rel2p rel2p_def state_rel_def
    by (intro rel_funI trans_from_transfer[THEN rel_funD, THEN list_all2_swap])
       (auto simp: list.rel_eq state_rel_def swap_rel_prod swap_eq)
  then show ?thesis
    unfolding rel2p_def relAPP_def loc_rel_def .
qed

lemma trans_from_correct:
  "(trans_from, trans_prod) \<in> transition_rel states'"
  using int_trans_from_correct sync_trans_from_correct
  unfolding trans_from_def trans_prod_def transition_rel_def by auto

lemma states'_alt_def:
  "states' = {(L, s). L \<in> states \<and> bounded bounds s}"
  unfolding states'_def bounded_def dom_bounds_eq by auto

lemma states'_alt_def2:
  "states' = {(L, s). L \<in> states \<and> dom s = {0..<n_vs} \<and> check_bounded s}"
proof -
  have "states' = {(L, s). L \<in> states \<and> dom s = {0..<n_vs} \<and> bounded bounds s}"
    unfolding states'_def bounded_def dom_bounds_eq by auto
  then show ?thesis
    by (auto simp: check_bounded_iff)
qed

lemma trans_prod_states'_inv:
  "l' \<in> states'" if "(l, g, a, r, l') \<in> trans_prod" "l \<in> states'"
  using that unfolding states'_alt_def
  by (cases l') (auto dest: trans_prod_bounded_inv trans_prod_states_inv)

lemma prod_ta_states'_inv:
  "l' \<in> states'" if "prod_ta \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" "l \<in> states'"
  using that by simp (rule trans_prod_states'_inv)

lemma dom_eq_transfer [transfer_rule]:
  "(state_rel ===> (=)) (\<lambda>s. dom s = {0..<n_vs}) (\<lambda>s. length s = n_vs)"
  by (rule rel_funI) (auto simp: state_rel_def)

lemma states'_memi_correct:
  "(states'_memi, (\<lambda>l. l \<in> states')) \<in> loc_rel \<rightarrow> bool_rel"
proof -
  define t where "t s \<equiv> dom s = {0..<n_vs}" for s :: "nat \<rightharpoonup> int"
  define ti where "ti s \<equiv> length s = n_vs" for s :: "int list"
  let ?R = "\<lambda>x y. (eq_onp (\<lambda>L. length L = n_ps) \<times>\<^sub>R state_rel) y x"
  note [transfer_rule] = dom_eq_transfer[folded t_def ti_def]
  have [p2rel]: "p2rel ((\<lambda>x y. (eq_onp (\<lambda>L. length L = n_ps) \<times>\<^sub>R state_rel) y x)) = loc_rel"
    by (auto simp: eq_onp_def p2rel_def loc_rel_def)
  have *: "(\<lambda>(L, s). L \<in> states \<and> dom s = {0..<n_vs} \<and> check_bounded s) = (\<lambda>l. l \<in> states')"
    by (intro ext) (auto simp: states'_alt_def2)
  have "(((=) \<times>\<^sub>R state_rel) ===> (=))
      (\<lambda>(L, s). L \<in> states \<and> t s \<and> check_bounded s) (\<lambda>(L, s). L \<in> states \<and> ti s \<and> check_boundedi s)"
    by transfer_prover
  then have
    "(((=) \<times>\<^sub>R state_rel) ===> (=))
    (\<lambda>(L, s). L \<in> states \<and> dom s = {0..<n_vs} \<and> check_bounded s)
    states'_memi"
    unfolding t_def ti_def states'_memi_def .
  then have [p2rel]: "(?R ===> (=)) states'_memi (\<lambda>l. l \<in> states')"
    unfolding * by (intro rel_funI) (auto simp: eq_onp_def elim!: rel_funE)
  then have "(states'_memi, (\<lambda>l. l \<in> states')) \<in> p2rel (?R ===> (=))"
    unfolding p2rel_def by simp
  then show ?thesis
    unfolding p2rel .
qed

end (* Lfiting Syntax *)

end (* Simple Network Impl nat *)

end (* Theory *)
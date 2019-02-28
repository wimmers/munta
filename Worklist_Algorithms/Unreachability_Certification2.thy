theory Unreachability_Certification2
  imports Unreachability_Certification
begin

hide_const (open) list_set_rel

lemma monadic_list_all_mono:
  "monadic_list_all P xs \<le> monadic_list_all Q ys" if "list_all2 (\<lambda> x y. P x \<le> Q y) xs ys"
proof -
  have "nfoldli xs id (\<lambda>x _. P x) a \<le> nfoldli ys id (\<lambda>x _. Q x) a" for a
    using that by (induction xs ys arbitrary: a; clarsimp; refine_mono)
  then show ?thesis
    unfolding monadic_list_all_def .
qed

lemma monadic_list_all_mono':
  "monadic_list_all P xs \<le> monadic_list_all Q ys"
  if "(xs, ys) \<in> \<langle>R\<rangle>list_rel" "\<And> x y. (x, y) \<in> R \<Longrightarrow> P x \<le> Q y"
   using that by (intro monadic_list_all_mono) (auto simp: list_all2_iff list_rel_def)

lemma monadic_list_ex_mono:
  "monadic_list_ex P xs \<le> monadic_list_ex Q ys" if "list_all2 (\<lambda> x y. P x \<le> Q y) xs ys"
proof -
  have "nfoldli xs Not (\<lambda>x _. P x) a \<le> nfoldli ys Not (\<lambda>x _. Q x) a" for a
    using that by (induction xs ys arbitrary: a; clarsimp; refine_mono)
  then show ?thesis
    unfolding monadic_list_ex_def .
qed

lemma monadic_list_ex_mono':
  "monadic_list_ex P xs \<le> monadic_list_ex Q ys"
  if "(xs, ys) \<in> \<langle>R\<rangle>list_rel" "\<And> x y. (x, y) \<in> R \<Longrightarrow> P x \<le> Q y"
  using that by (intro monadic_list_ex_mono) (auto simp: list_all2_iff list_rel_def)

definition list_set_rel where list_set_rel_def_internal:
  "list_set_rel R = \<langle>R\<rangle>list_rel O {(xs, S). set xs = S}"

lemma list_set_rel_def:
  "\<langle>R\<rangle>list_set_rel = \<langle>R\<rangle>list_rel O {(xs, S). set xs = S}"
  unfolding list_set_rel_def_internal relAPP_def ..

lemma list_set_relE:
  assumes "(xs, zs) \<in> \<langle>R\<rangle>list_set_rel"
  obtains ys where "(xs, ys) \<in> \<langle>R\<rangle>list_rel" "set ys = zs"
  using assms unfolding list_set_rel_def by auto

lemma list_set_rel_Nil[simp, intro]:
  "([], {}) \<in> \<langle>Id\<rangle>list_set_rel"
  unfolding list_set_rel_def by auto

lemma specify_right:
  "c \<le> SPEC P \<bind> c'" if "P x" "c \<le> c' x"
  using that by (auto intro: SUP_upper2[where i = x] simp: bind_RES)

lemma list_rel_setE1:
  assumes "x \<in> set xs" "(xs, ys) \<in> \<langle>R\<rangle>list_rel"
  obtains y where "y \<in> set ys" "(x, y) \<in> R"
  using assms unfolding list_rel_def by (auto dest!: list_all2_set1)

lemma list_rel_setE2:
  assumes "y \<in> set ys" "(xs, ys) \<in> \<langle>R\<rangle>list_rel"
  obtains x where "x \<in> set xs" "(x, y) \<in> R"
  using assms unfolding list_rel_def by (auto dest!: list_all2_set2)

locale Reachability_Impl_pure = Reachability_Impl_pre +
  fixes get_succs and loc_rel and state_rel and Mi and Li and lei
  assumes loc_rel_right_unique: "single_valued loc_rel"
  assumes loc_rel_left_unique:  "single_valued (loc_rel\<inverse>)"
  assumes Li_L: "(Li, L) \<in> \<langle>loc_rel\<rangle>list_set_rel"
  assumes Mi_M[param]: "(Mi, M) \<in> loc_rel \<rightarrow> \<langle>state_rel\<rangle>list_set_rel"
  assumes lei_less_eq: "(lei, less_eq) \<in> state_rel \<rightarrow> state_rel \<rightarrow> bool_rel"
  assumes get_succs_succs[param]:
    "(get_succs, succs) \<in>
    loc_rel \<rightarrow> \<langle>state_rel\<rangle>list_set_rel \<rightarrow> \<langle>loc_rel \<times>\<^sub>r \<langle>state_rel\<rangle>list_set_rel\<rangle>list_rel"
begin

definition "check_invariant1 L' \<equiv>
do {
  monadic_list_all (\<lambda>l.
  do {
    let as = Mi l;
    let succs = get_succs l as;
    monadic_list_all (\<lambda>(l', xs).
    do {
      if xs = [] then RETURN True else do {
        b1 \<leftarrow> RETURN (l' \<in> set Li);
        let ys = Mi l';
        b2 \<leftarrow> monadic_list_all (\<lambda>x.
          monadic_list_ex (\<lambda>y. RETURN (lei x y)) ys
        ) xs;
        RETURN (b1 \<and> b2)
      }
    }
    ) succs
  }
  ) L'
}
"

lemma check_invariant1_refine:
  "(check_invariant1, check_invariant) \<in> \<langle>loc_rel\<rangle>list_rel \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  unfolding check_invariant1_def check_invariant_def Let_def
  apply (refine_rcg monadic_list_all_mono' refine_IdI)
    apply assumption
   apply parametricity
  apply (clarsimp; safe)
  subgoal for _ _ _ _ li _ l
    by (elim list_set_relE specify_right) auto
  subgoal premises prems for _ _ _ _ li _ l
  proof -
    have [refine_mono]: \<open>RETURN (lei a b) \<le> RETURN (a' \<preceq> b')\<close>
      if  \<open>(a, a') \<in> state_rel\<close> \<open>(b, b') \<in> state_rel\<close> for a a' b b'
      using that using lei_less_eq by simp (metis pair_in_Id_conv tagged_fun_relD_both)
    have *: \<open>li \<in> set Li \<longleftrightarrow> l \<in> L\<close> if \<open>(li, l) \<in> loc_rel\<close>
      using that using Li_L loc_rel_left_unique loc_rel_right_unique
      by (auto dest: single_valuedD elim: list_rel_setE1 list_rel_setE2 elim!: list_set_relE)
    from prems have "(Mi li, M l) \<in> \<langle>state_rel\<rangle>list_set_rel"
      by parametricity
    then obtain xs where "(Mi li, xs) \<in> \<langle>state_rel\<rangle>list_rel" "set xs = M l"
      by (elim list_set_relE)
    with prems show ?thesis
      apply (elim list_set_relE, elim specify_right)
      apply (clarsimp, safe)
       apply (auto; fail)
      apply (elim specify_right[where x = xs])
      supply [refine_mono] = monadic_list_all_mono' monadic_list_ex_mono'
      apply refine_mono
      subgoal
        using * by simp
      done
  qed
  done

end (* Reachability_Impl_pure *)

context Reachability_Impl
begin

context
  fixes to_state :: "'b \<Rightarrow> 'bi Heap" and from_state :: "'bi \<Rightarrow> 'b Heap"
    and to_loc :: "'k \<Rightarrow> 'ki" and from_loc :: "'ki \<Rightarrow> 'k"
  fixes L_list :: "'ki list" and Li :: "'k list"
  assumes Li: "(L_list, Li) \<in> \<langle>the_pure K\<rangle>list_rel" "set Li = L"
  fixes Mi :: "'k \<Rightarrow> 'b list option"
  assumes Mi_M: "(Mi, M) \<in> Id \<rightarrow> \<langle>\<langle>Id\<rangle>list_set_rel\<rangle>option_rel"
  assumes to_state_ht: "<emp> to_state s <\<lambda>si. A s si>"
  assumes from_state_ht: "<A s si> from_state is <\<lambda>s'. \<up>(s = s')>\<^sub>t"
  assumes from_loc: "(li, l) \<in> the_pure K \<Longrightarrow> from_loc li = l"
  assumes to_loc: "(to_loc l, l) \<in> the_pure K"
begin

definition
  "get_succs l xs \<equiv>
    do {
      let li = to_loc l;
      xsi \<leftarrow> Heap_Monad.fold_map to_state xs;
      r \<leftarrow> succsi li xsi;
      Heap_Monad.fold_map
        (\<lambda>(li, xsi). do {xs \<leftarrow> Heap_Monad.fold_map from_state xsi; return (from_loc li, xs)}) r
    }"

lemma get_succs:
  "(run_heap oo get_succs, succs) \<in> Id \<rightarrow> \<langle>Id\<rangle>list_set_rel \<rightarrow> \<langle>Id \<times>\<^sub>r \<langle>Id\<rangle>list_set_rel\<rangle>list_rel"
proof (refine_rcg, clarsimp, rule hoare_triple_run_heapD)
  fix l :: \<open>'k\<close> and xs :: \<open>'b list\<close> and S :: \<open>'b set\<close>
  assume \<open>(xs, S) \<in> \<langle>Id\<rangle>list_set_rel\<close>
  then obtain ys where ys: "(xs, ys) \<in> \<langle>Id\<rangle>list_rel" "set ys = S"
    by (elim list_set_relE)
  have 1: "K = pure (the_pure K)"
    using pure_K by auto
  let ?li = "to_loc l"
  show "<emp> get_succs l xs <\<lambda>r. \<up>((r, succs l S) \<in> \<langle>Id \<times>\<^sub>r \<langle>Id\<rangle>list_set_rel\<rangle>list_rel)>\<^sub>t"
    unfolding get_succs_def
    apply sep_auto
      (* fold_map to_state *)
     apply (rule Hoare_Triple.cons_pre_rule[rotated])
      apply (rule fold_map_ht3[where A = true and R = id_assn and Q = A and xs = xs])
      apply (sep_auto heap: to_state_ht simp: pure_def; fail)
     apply (unfold list_assn_pure_conv, sep_auto simp: pure_def; fail)
    apply sep_auto
      (* succsi *)
     apply (rule Hoare_Triple.cons_pre_rule[rotated], rule frame_rule[where R = true])
      apply (rule succsi[to_hnr, unfolded hn_refine_def hn_ctxt_def, simplified, of S _ l ?li])
    subgoal
      using ys(1) unfolding lso_assn_def hr_comp_def br_def \<open>set ys = _\<close>[symmetric]
      by (subst 1) (sep_auto simp: pure_def to_loc)
        (* nested fold_map *)
    apply (sep_auto simp: invalid_assn_def)
    apply (rule cons_rule[rotated 2])
      apply (rule frame_rule)
      apply (rule fold_map_ht1[where
          A = true and R = "(K \<times>\<^sub>a lso_assn A)" and xs = "succs l S" and
          Q = "\<lambda>x xi. (xi, x) \<in> Id \<times>\<^sub>r \<langle>Id\<rangle>list_set_rel"
          ])
    subgoal
      unfolding lso_assn_def
      apply (subst 1, subst pure_def)
      apply (sep_auto simp: prod_assn_def hr_comp_def br_def split: prod.splits)
        (* inner fold_map *)
       apply (rule Hoare_Triple.cons_pre_rule[rotated])
        apply (rule fold_map_ht1[where A = true and R = A and Q = "(=)"])
        apply (rule cons_rule[rotated 2], rule frame_rule, rule from_state_ht)
         apply frame_inference
        apply (sep_auto; fail)
       apply solve_entails
        (* return *)
      apply (sep_auto simp: list.rel_eq list_set_rel_def from_loc)
      done
     apply solve_entails
    using list_all2_swap by (sep_auto simp: list_rel_def)
qed

interpretation pure:
  Reachability_Impl_pure
  where 
    M = "\<lambda>x. case M x of None \<Rightarrow> {} | Some S \<Rightarrow> S" and
    Mi = "\<lambda>x. case Mi x of None \<Rightarrow> [] | Some S \<Rightarrow> S" and
    get_succs = "run_heap oo get_succs" and
    loc_rel = Id and
    state_rel = Id and
    lei = less_eq
  apply standard
  subgoal
    by simp
  subgoal
    by simp
  subgoal
    using Li unfolding list_set_rel_def by auto
  subgoal
    using Mi_M by parametricity simp
  subgoal
    by simp
  subgoal
    using get_succs .
  done

end

end
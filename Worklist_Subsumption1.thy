(* Authors: Lammich, Wimmer *)
theory Worklist_Subsumption1
  imports Worklist_Subsumption_Multiset DRAT_Misc
begin

subsection \<open>From Multisets to Lists\<close>

subsubsection \<open>Utilities\<close>

definition take_from_list where
  "take_from_list s = ASSERT (s \<noteq> []) \<then> SPEC (\<lambda> (x, s'). s = x # s')"

lemma take_from_list_correct:
  assumes "s \<noteq> []"
  shows "take_from_list s \<le> SPEC (\<lambda> (x, s'). s = x # s')"
using assms unfolding take_from_list_def by simp

lemmas [refine_vcg] = take_from_list_correct[THEN order.trans]


context Search_Space'_Defs
begin

  definition "worklist_inv_frontier_list passed wait =
    (\<forall> a \<in> passed. \<forall> a'. E a a' \<and> \<not> empty a' \<longrightarrow> (\<exists> b' \<in> passed \<union> set wait. a' \<preceq> b'))"

  definition "start_subsumed_list passed wait = (\<exists> a \<in> passed \<union> set wait. a\<^sub>0 \<preceq> a)"

  definition "worklist_inv_list \<equiv> \<lambda> (passed, wait, brk).
    passed \<subseteq> Collect reachable \<and>
    (brk \<longrightarrow> (\<exists> f. reachable f \<and> F f)) \<and>
    (\<not> brk \<longrightarrow>
      worklist_inv_frontier_list passed wait
    \<and> (\<forall> a \<in> passed \<union> set wait. \<not> F a)
    \<and> start_subsumed_list passed wait
    \<and> set wait \<subseteq> Collect reachable)
    \<and> (\<forall> a \<in> passed. \<not> empty a) \<and> (\<forall> a \<in> set wait. \<not> empty a)
    "

  definition "add_succ_spec_list wait a \<equiv> SPEC (\<lambda>(wait',brk).
    (
    if \<exists>a'. E a a' \<and> F a' then
      brk
    else
      \<not>brk \<and> set wait' \<subseteq> set wait \<union> {a' . E a a'} \<and>
      (\<forall> s \<in> set wait \<union> {a' . E a a' \<and> \<not> empty a'}. \<exists> s' \<in> set wait'. s \<preceq> s')
    ) \<and> (\<forall> s \<in> set wait'. \<not> empty s)
  )"

  definition worklist_algo_list where
    "worklist_algo_list = do
      {
        if F a\<^sub>0 then RETURN True
        else do {
          let passed = {};
          let wait = [a\<^sub>0];
          (passed, wait, brk) \<leftarrow> WHILEIT worklist_inv_list (\<lambda> (passed, wait, brk). \<not> brk \<and> wait \<noteq> [])
            (\<lambda> (passed, wait, brk). do
              {
                (a, wait) \<leftarrow> take_from_list wait;
                ASSERT (reachable a);
                if (\<exists> a' \<in> passed. a \<unlhd> a') then RETURN (passed, wait, brk) else
                do
                  {
                    (wait,brk) \<leftarrow> add_succ_spec_list wait a;
                    let passed = insert a passed;
                    RETURN (passed, wait, brk)
                  }
              }
            )
            (passed, wait, False);
            RETURN brk
        }
      }
    "

end -- \<open>Search Space Defs\<close>

context Search_Space'
begin

  lemma worklist_algo_list_inv_ref:
    fixes x x'
    assumes
      "\<not> F a\<^sub>0" "\<not> F a\<^sub>0"
      "(x, x') \<in> {((passed,wait,brk), (passed',wait',brk')). passed = passed' \<and> mset wait = wait' \<and> brk = brk' }"
      "worklist_inv' x'"
    shows "worklist_inv_list x"
    using assms
    unfolding worklist_inv'_def worklist_inv_def worklist_inv_list_def
    unfolding worklist_inv_frontier_def worklist_inv_frontier_list_def
    unfolding start_subsumed_def start_subsumed_list_def
    by auto

  lemma take_from_list_take_from_mset_ref[refine]:
    "take_from_list xs \<le> \<Down> {((x, xs),(y, m)). x = y \<and> mset xs = m} (take_from_mset m)"
    if "mset xs = m"
    using that unfolding take_from_list_def take_from_mset_def
    by (clarsimp simp: pw_le_iff refine_pw_simps)

  lemma add_succ_spec_list_add_succ_spec_ref[refine]:
    "add_succ_spec_list xs b \<le> \<Down> {((xs, b), (m, b')). mset xs = m \<and> b = b'} (add_succ_spec' m b')"
    if "mset xs = m" "b = b'"
    using that unfolding add_succ_spec_list_def add_succ_spec'_def
    by (clarsimp simp: pw_le_iff refine_pw_simps)

  lemma worklist_algo_list_ref[refine]: "worklist_algo_list \<le> \<Down>Id worklist_algo'"
    unfolding worklist_algo_list_def worklist_algo'_def
    apply (refine_rcg)
               apply blast
              prefer 2
              apply (rule worklist_algo_list_inv_ref; assumption)
    by auto

end -- \<open>Search Space\<close>


subsection \<open>Towards an Implementation\<close>
locale Worklist1_Defs = Search_Space_Defs +
  fixes succs :: "'a \<Rightarrow> 'a list"

locale Worklist1 = Worklist1_Defs + Search_Space' +
  assumes succs_correct: "reachable a \<Longrightarrow> set (succs a) = Collect (E a)"
begin

  definition
    "add_succ1 wait a \<equiv>
     nfoldli (succs a) (\<lambda>(_,brk). \<not>brk)
      (\<lambda>a (wait,brk).
        do {
        ASSERT (\<forall> x \<in> set wait. \<not> empty x);
        if F a then RETURN (wait,True) else RETURN (
          if (\<exists> x \<in> set wait. a \<preceq> x \<and> \<not> x \<preceq> a) \<or> empty a
          then [x \<leftarrow> wait. \<not> x \<preceq> a]
          else a # [x \<leftarrow> wait. \<not> x \<preceq> a],False)
        }
      )
      (wait,False)"

  definition
    "add_succ1' wait a \<equiv>
     nfoldli (succs a) (\<lambda>(_,brk). \<not>brk)
      (\<lambda>a (wait,brk).
        if F a then RETURN (wait,True) else RETURN (
          if empty a
          then wait
          else if \<exists> x \<in> set wait. a \<unlhd> x \<and> \<not> x \<unlhd> a
          then [x \<leftarrow> wait. \<not> x \<unlhd> a]
          else a # [x \<leftarrow> wait. \<not> x \<unlhd> a],False)
      )
      (wait,False)"

  lemma add_succ1_ref[refine]:
    "add_succ1 wait a \<le> \<Down>(Id \<times>\<^sub>r bool_rel) (add_succ_spec_list wait' a')"
    if "(wait,wait')\<in>Id" "(a,a')\<in>b_rel Id reachable" "\<forall> x \<in> set wait'. \<not> empty x"
    using that
    apply simp
    unfolding add_succ_spec_list_def add_succ1_def
    apply (refine_vcg nfoldli_rule[where I =
          "\<lambda>l1 _ (wait',brk).
            (if brk then \<exists>a'. E a a' \<and> F a'
            else set wait' \<subseteq> set wait \<union> set l1 \<and> set l1 \<inter> Collect F = {}
              \<and> (\<forall> x \<in> set wait \<union> set l1. \<not> empty x \<longrightarrow> (\<exists> x' \<in> set wait'. x \<preceq> x')))
            \<and> (\<forall> x \<in> set wait'. \<not> empty x)"]
          )
              apply (auto; fail)
             apply (auto; fail)
    using succs_correct[of a] apply (auto; fail)
    using succs_correct apply fastforce
          apply (auto; fail)
    subgoal
      apply (clarsimp split: if_split_asm)
       apply rule
        apply blast
       apply rule
        apply blast
       apply (meson empty_mono local.trans)
      apply rule
       apply blast
      apply (meson empty_mono local.trans)
      done
        apply (auto split: if_split_asm; fail)
       apply (auto; fail)
      apply (auto; fail)
    using succs_correct[of a] apply (auto; fail)
    apply (auto; fail)
    done

  lemma add_succ1'_ref[refine]:
    "add_succ1' wait a \<le> \<Down>(Id \<times>\<^sub>r bool_rel) (add_succ1 wait' a')"
    if "(wait,wait')\<in>Id" "(a,a')\<in>b_rel Id reachable" "\<forall> x \<in> set wait'. \<not> empty x"
    unfolding add_succ1'_def add_succ1_def
    using that
    apply (refine_vcg nfoldli_refine)
         apply refine_dref_type
         apply (auto simp: empty_subsumes' cong: filter_cong)
    by (metis empty_mono empty_subsumes' filter_True)+


  lemma add_succ1'_ref'[refine]:
    "add_succ1' wait a \<le> \<Down>(Id \<times>\<^sub>r bool_rel) (add_succ_spec_list wait' a')"
    if "(wait,wait')\<in>Id" "(a,a')\<in>b_rel Id reachable" "\<forall> x \<in> set wait'. \<not> empty x"
    using that
  proof -
    note add_succ1'_ref
    also note add_succ1_ref
    finally show ?thesis
      using that by - auto
  qed

  definition worklist_algo1' where
    "worklist_algo1' = do
      {
        if F a\<^sub>0 then RETURN True
        else do {
          let passed = {};
          let wait = [a\<^sub>0];
          (passed, wait, brk) \<leftarrow> WHILEIT worklist_inv_list (\<lambda> (passed, wait, brk). \<not> brk \<and> wait \<noteq> [])
            (\<lambda> (passed, wait, brk). do
              {
                (a, wait) \<leftarrow> take_from_list wait;
                if (\<exists> a' \<in> passed. a \<unlhd> a') then RETURN (passed, wait, brk) else
                do
                  {
                    (wait,brk) \<leftarrow> add_succ1' wait a;
                    let passed = insert a passed;
                    RETURN (passed, wait, brk)
                  }
              }
            )
            (passed, wait, False);
            RETURN brk
        }
      }
    "

  lemma take_from_list_ref[refine]:
    "take_from_list wait \<le>
     \<Down> {((x, wait), (y, wait')). x = y \<and> wait = wait' \<and> \<not> empty x \<and> (\<forall> a \<in> set wait. \<not> empty a)}
       (take_from_list wait')"
    if "wait = wait'" "\<forall> a \<in> set wait. \<not> empty a" "wait \<noteq> []"
    using that
    by (auto 4 4 simp: pw_le_iff refine_pw_simps dest!: take_from_list_correct)

  lemma worklist_algo1_list_ref[refine]: "worklist_algo1' \<le> \<Down>Id worklist_algo_list"
    unfolding worklist_algo1'_def worklist_algo_list_def
    apply (refine_rcg)
    apply refine_dref_type
    unfolding worklist_inv_list_def
    by auto

  definition worklist_algo1 where
    "worklist_algo1 \<equiv> if empty a\<^sub>0 then RETURN False else worklist_algo1'"

  lemma worklist_algo1_ref[refine]: "worklist_algo1 \<le> \<Down>Id worklist_algo''"
    unfolding worklist_algo1_def worklist_algo''_def
  proof clarsimp
    assume "\<not> empty a\<^sub>0"
    note worklist_algo1_list_ref
    also note worklist_algo_list_ref
    finally show "worklist_algo1' \<le> worklist_algo'" by simp
  qed

end -- \<open>Worklist1\<close>

locale Worklist2_Defs = Worklist1_Defs +
  fixes F' :: "'a \<Rightarrow> bool"

locale Worklist2 = Worklist2_Defs + Worklist1 +
  assumes F_split: "F a \<longleftrightarrow> \<not> empty a \<and> F' a"
begin

  definition
    "add_succ2 wait a \<equiv>
     nfoldli (succs a) (\<lambda>(_,brk). \<not>brk)
      (\<lambda>a (wait,brk).
        if empty a then RETURN (wait, False)
        else if F' a then RETURN (wait,True)
        else RETURN (
          if \<exists> x \<in> set wait. a \<unlhd> x \<and> \<not> x \<unlhd> a
          then [x \<leftarrow> wait. \<not> x \<unlhd> a]
          else a # [x \<leftarrow> wait. \<not> x \<unlhd> a],False)
      )
      (wait,False)"

  definition
    "filter_insert_wait wait a \<equiv>
     if \<exists> x \<in> set wait. a \<unlhd> x \<and> \<not> x \<unlhd> a
     then [x \<leftarrow> wait. \<not> x \<unlhd> a]
     else a # [x \<leftarrow> wait. \<not> x \<unlhd> a]"

  lemma filter_insert_wait_alt_def:
    "filter_insert_wait wait a = (
      let
         (f, xs) =
           fold (\<lambda> x (f, xs). if x \<unlhd> a then (f, xs) else (f \<or> a \<unlhd> x, x # xs)) wait (False, [])
       in
         if f then rev xs else a # rev xs
    )
    "
  proof -
    have
      "fold (\<lambda> x (f, xs). if x \<unlhd> a then (f, xs) else (f \<or> a \<unlhd> x, x # xs)) wait (f, xs)
     = (f \<or> (\<exists> x \<in> set wait. a \<unlhd> x \<and> \<not> x \<unlhd> a), rev [x \<leftarrow> wait. \<not> x \<unlhd> a] @ xs)" for f xs
      by (induction wait arbitrary: f xs; simp)
    then show ?thesis unfolding filter_insert_wait_def by auto
  qed

  lemma add_succ2_alt_def:
    "add_succ2 wait a \<equiv>
     nfoldli (succs a) (\<lambda>(_,brk). \<not>brk)
      (\<lambda>a (wait,brk).
        if empty a then RETURN (wait, False)
        else if F' a then RETURN (wait, True)
        else RETURN (filter_insert_wait wait a, False)
      )
      (wait,False)"
    unfolding add_succ2_def filter_insert_wait_def by (intro HOL.eq_reflection HOL.refl)

  lemma add_succ2_ref[refine]:
    "add_succ2 wait a \<le> \<Down>(Id \<times>\<^sub>r bool_rel) (add_succ1' wait' a')"
    if "(wait,wait')\<in>Id" "(a,a')\<in>Id"
    unfolding add_succ2_def add_succ1'_def
    apply (rule nfoldli_refine)
       apply refine_dref_type
    using that by (auto simp: F_split)

  definition worklist_algo2' where
    "worklist_algo2' = do
      {
        if F' a\<^sub>0 then RETURN True
        else do {
          let passed = {};
          let wait = [a\<^sub>0];
          (passed, wait, brk) \<leftarrow> WHILEIT worklist_inv_list (\<lambda> (passed, wait, brk). \<not> brk \<and> wait \<noteq> [])
            (\<lambda> (passed, wait, brk). do
              {
                (a, wait) \<leftarrow> take_from_list wait;
                if (\<exists> a' \<in> passed. a \<unlhd> a') then RETURN (passed, wait, brk) else
                do
                  {
                    (wait,brk) \<leftarrow> add_succ2 wait a;
                    let passed = insert a passed;
                    RETURN (passed, wait, brk)
                  }
              }
            )
            (passed, wait, False);
            RETURN brk
        }
      }
    "

  lemma worklist_algo2'_ref[refine]: "worklist_algo2' \<le> \<Down>Id worklist_algo1'" if "\<not> empty a\<^sub>0"
    unfolding worklist_algo2'_def worklist_algo1'_def
    using that
    supply take_from_list_ref [refine del]
    apply refine_rcg
              apply refine_dref_type
    by (auto simp: F_split)

  definition worklist_algo2 where
    "worklist_algo2 \<equiv> if empty a\<^sub>0 then RETURN False else worklist_algo2'"

  lemma worklist_algo2_ref[refine]: "worklist_algo2 \<le> \<Down>Id worklist_algo''"
  proof -
    have "worklist_algo2 \<le> \<Down>Id worklist_algo1"
      unfolding worklist_algo2_def worklist_algo1_def
      by refine_rcg standard
    also note worklist_algo1_ref
    finally show ?thesis .
  qed

end -- \<open>Worklist2\<close>

locale Search_Space_Key_Defs =
  Search_Space'_Defs E for E :: "'v \<Rightarrow> 'v \<Rightarrow> bool" +
  fixes key :: "'v \<Rightarrow> 'k"


locale Search_Space_Key =
  Search_Space_Key_Defs + Search_Space' +
  assumes subsumes_key[intro, simp]: "a \<preceq> b \<Longrightarrow> key a = key b"

locale Worklist_Map =
  Search_Space_Key + Worklist1
begin

definition
  "map_list_rel =
    {(m, l). (\<Union> x \<in> ran m. set x) = set l \<and> (\<forall> k. \<forall> xs. m k = Some xs \<longrightarrow> (\<forall> v \<in> set xs. key v = k))}"

lemma map_list_rel_alt_def:
  "map_list_rel =
    {(m, l). set l = (\<Union> x \<in> ran m. set x) \<and> (\<forall> k. \<forall> xs. m k = Some xs \<longrightarrow> (\<forall> v \<in> set xs. key v = k))}"
  unfolding map_list_rel_def
  by auto

definition
  "wait_rel = {((ml, m), l). (m, l) \<in> map_list_rel \<and> key ` set l \<subseteq> set ml}"

lemma ran_upd_cases:
  "(x \<in> ran m) \<or> (x = y)" if "x \<in> ran (m(a \<mapsto> y))"
  using that unfolding ran_def by (auto split: if_split_asm)

lemma ran_upd_cases2:
  "(\<exists> k. m k = Some x \<and> k \<noteq> a) \<or> (x = y)" if "x \<in> ran (m(a \<mapsto> y))"
  using that unfolding ran_def by (auto split: if_split_asm)

definition
  "add_succ1_map wait a \<equiv>
   nfoldli (succs a) (\<lambda>(_,brk). \<not>brk)
    (\<lambda>a ((waitl, wait), brk).
      do {
      ASSERT (\<forall> wait \<in> ran wait. \<forall> x \<in> set wait. \<not> empty x);
      if F a then RETURN ((waitl, wait), True) else RETURN ((
        let k = key a; wait' = (case wait k of Some wait' \<Rightarrow> wait' | None \<Rightarrow> [])
        in
          if (\<exists> x \<in> set wait'. a \<preceq> x \<and> \<not> x \<preceq> a) \<or> empty a
          then (waitl, wait(k \<mapsto> [x \<leftarrow> wait'. \<not> x \<preceq> a]))
          else (k # waitl, wait(k \<mapsto> (a # [x \<leftarrow> wait'. \<not> x \<preceq> a])))),False)
      }
    )
    (wait,False)"

lemma add_succ1_map_ref[refine]:
  "add_succ1_map wait a \<le> \<Down>(wait_rel \<times>\<^sub>r Id) (add_succ1 wait' a')"
  if "(wait, wait') \<in> wait_rel" "(a, a') \<in> Id"
  unfolding add_succ1_map_def add_succ1_def
  apply refine_rcg
        apply refine_dref_type
  using that apply (auto; fail)+
  subgoal unfolding map_list_rel_def wait_rel_def by auto
    apply (auto; fail)
   apply (auto; fail)
  subgoal premises assms for a' a _ _ wait f _ waitl wait' f'
  proof -
    from assms have [simp]: "a' = a" "f = f'" by simp+
    from assms have rel: "(wait', wait) \<in> map_list_rel" unfolding wait_rel_def by simp
    then have union: "set wait = (\<Union>x\<in>ran wait'. set x)"
      unfolding map_list_rel_def by auto
    from assms have rel': "key ` set wait \<subseteq> set waitl" unfolding wait_rel_def by simp
    from rel have keys[simp]: "key v = k" if "wait' k = Some xs" "v\<in>set xs" for k xs v
      using that unfolding map_list_rel_def by auto
    define k where "k \<equiv> key a"
    define xs where "xs \<equiv> case wait' k of None \<Rightarrow> [] | Some wait' \<Rightarrow> wait'"
    have *:
      "(\<exists>x\<in>set xs. a' \<preceq> x \<and> \<not> x \<preceq> a') \<or> empty a' \<longleftrightarrow> (\<exists>x\<in>set wait. a \<preceq> x \<and> \<not> x \<preceq> a) \<or> empty a"
    proof (simp, safe, goal_cases)
      case (1 x)
      with rel show ?case
        unfolding xs_def union by (auto intro: ranI[OF sym])
    next
      case (2 x)
      with rel show ?case unfolding xs_def union ran_def k_def by auto
    qed
    have "(\<Union>x\<in>ran (wait'(k \<mapsto> [x\<leftarrow>xs . \<not> x \<preceq> a'])). set x) = set [x\<leftarrow>wait . \<not> x \<preceq> a]"
    proof (safe, goal_cases)
      case prems: (1 x xs')
      from ran_upd_cases2[OF prems(1)] show ?case
      proof (safe, goal_cases)
        case (1 k')
        with \<open>x \<in> _\<close> have "\<not> x \<preceq> a" unfolding k_def by (auto dest: keys)
        with 1 \<open>x \<in> _\<close> show ?case by (auto intro: ranI simp: union)
      next
        case 2
        with \<open>x \<in> _\<close> have "\<not> x \<preceq> a" by auto
        with 2 \<open>x \<in> _\<close> show ?case
          unfolding xs_def by (auto simp: union split: option.split_asm intro: ranI)
      qed
    next
      case (2 x)
      then have "\<not> x \<preceq> a" "x \<in> set wait"
        by auto
      from this(2) obtain k' xs' where k': "wait' k' = Some xs'" "x \<in> set xs'"
        unfolding union ran_def by auto
      show ?case
      proof (cases "k' = k")
        case True
        with k' \<open>\<not> x \<preceq> a\<close> have "x \<in> set [x\<leftarrow>xs . \<not> x \<preceq> a']"
          unfolding xs_def by auto
        then show ?thesis unfolding ran_def by auto
      next
        case False
        with k' show ?thesis by (auto intro!: ranI)
      qed
    qed
    then have **: "(wait'(k \<mapsto> [x\<leftarrow>xs . \<not> x \<preceq> a']), [x\<leftarrow>wait . \<not> x \<preceq> a]) \<in> map_list_rel"
      unfolding map_list_rel_def xs_def by (auto intro: keys[OF sym])
    have ***: "(wait'(k \<mapsto> a' # [x\<leftarrow>xs . \<not> x \<preceq> a']), a # [x\<leftarrow>wait . \<not> x \<preceq> a]) \<in> map_list_rel"
      unfolding map_list_rel_def
      apply safe
      subgoal for x xs'
        using ** unfolding map_list_rel_alt_def by (fastforce simp: ran_def dest!: ran_upd_cases2)
      subgoal premises prems' for x
      proof -
        show ?thesis
        proof (cases "x = a")
          case True
          then show ?thesis by (force intro: ranI)
        next
          case False
          with prems' ** have "x \<in> (\<Union>x\<in>ran (wait'(k \<mapsto> [x\<leftarrow>xs . \<not> x \<preceq> a'])). set x)"
            unfolding map_list_rel_alt_def by auto
          with False show ?thesis by (fastforce dest!: ran_upd_cases2 simp: ran_def)
        qed
      qed
      subgoal
        using **
        apply (auto split: if_split_asm)
        unfolding map_list_rel_alt_def
         apply auto
        unfolding k_def by fastforce
      done
    have unfold:
      "(let k = key a'; xs = case wait' k of None \<Rightarrow> [] | Some wait' \<Rightarrow> wait'
          in if (\<exists>x\<in>set xs. a' \<preceq> x \<and> \<not> x \<preceq> a') \<or> empty a'
             then (waitl, wait'(k \<mapsto> [x\<leftarrow>xs . \<not> x \<preceq> a']))
             else (k # waitl, wait'(k \<mapsto> a' # [x\<leftarrow>xs . \<not> x \<preceq> a'])))
       = (if (\<exists>x\<in>set xs. a' \<preceq> x \<and> \<not> x \<preceq> a') \<or> empty a'
          then (waitl, wait'(k \<mapsto> [x\<leftarrow>xs . \<not> x \<preceq> a']))
          else (k # waitl, wait'(k \<mapsto> a' # [x\<leftarrow>xs . \<not> x \<preceq> a'])))"
      unfolding xs_def k_def by (simp add: Let_def)
    have
      "((let k = key a'; xs = case wait' k of None \<Rightarrow> [] | Some wait' \<Rightarrow> wait'
           in if (\<exists>x\<in>set xs. a' \<preceq> x \<and> \<not> x \<preceq> a') \<or> empty a'
              then (waitl, wait'(k \<mapsto> [x\<leftarrow>xs . \<not> x \<preceq> a']))
              else (k # waitl, wait'(k \<mapsto> a' # [x\<leftarrow>xs . \<not> x \<preceq> a']))),
           if (\<exists>x\<in>set wait. a \<preceq> x \<and> \<not> x \<preceq> a) \<or> empty a then [x\<leftarrow>wait . \<not> x \<preceq> a]
           else a # [x\<leftarrow>wait . \<not> x \<preceq> a]) \<in> wait_rel"
      using ** *** rel' unfolding *[symmetric] unfold wait_rel_def k_def by auto
    then show ?thesis by auto
  qed
  done

(*
definition
  "add_succ1_map wait a \<equiv>
   nfoldli (succs a) (\<lambda>(_,brk). \<not>brk)
    (\<lambda>a (wait,brk).
      do {
      ASSERT (\<forall> wait \<in> ran wait. \<forall> x \<in> set wait. \<not> empty x);
      if F a then RETURN (wait,True) else RETURN ((
        let k = key a; wait' = (case wait k of Some wait' \<Rightarrow> wait' | None \<Rightarrow> [])
        in
          if (\<exists> x \<in> set wait'. a \<preceq> x \<and> \<not> x \<preceq> a) \<or> empty a
          then wait(k \<mapsto> [x \<leftarrow> wait'. \<not> x \<preceq> a])
          else wait(k \<mapsto> (a # [x \<leftarrow> wait'. \<not> x \<preceq> a]))),False)
      }
    )
    (wait,False)"

lemma add_succ1_map_ref[refine]:
  "add_succ1_map wait a \<le> \<Down>(map_list_rel \<times>\<^sub>r Id) (add_succ1 wait' a')"
  if "(wait, wait') \<in> map_list_rel" "(a, a') \<in> Id"
  unfolding add_succ1_map_def add_succ1_def
  apply refine_rcg
        apply refine_dref_type
  using that apply (auto; fail)+
  subgoal unfolding map_list_rel_def by auto
    apply (auto; fail)
   apply (auto; fail)
  subgoal premises assms for a' a _ _ wait f wait' f'
  proof -
    from assms have [simp]: "a' = a" "f = f'" by simp+
    from assms have rel: "(wait', wait) \<in> map_list_rel" by simp
    then have union: "set wait = (\<Union>x\<in>ran wait'. set x)"
      unfolding map_list_rel_def by auto
    from rel have keys[simp]: "key v = k" if "wait' k = Some xs" "v\<in>set xs" for k xs v
      using that unfolding map_list_rel_def by auto
    define k where "k \<equiv> key a"
    define xs where "xs \<equiv> case wait' k of None \<Rightarrow> [] | Some wait' \<Rightarrow> wait'"
    have *:
      "(\<exists>x\<in>set xs. a' \<preceq> x \<and> \<not> x \<preceq> a') \<or> empty a' \<longleftrightarrow> (\<exists>x\<in>set wait. a \<preceq> x \<and> \<not> x \<preceq> a) \<or> empty a"
    proof (simp, safe, goal_cases)
      case (1 x)
      with rel show ?case
        unfolding xs_def union by (auto intro: ranI[OF sym])
    next
      case (2 x)
      with rel show ?case unfolding xs_def union ran_def k_def by auto
    qed
    have "(\<Union>x\<in>ran (wait'(k \<mapsto> [x\<leftarrow>xs . \<not> x \<preceq> a'])). set x) = set [x\<leftarrow>wait . \<not> x \<preceq> a]"
    proof (safe, goal_cases)
      case prems: (1 x xs')
      from ran_upd_cases2[OF prems(1)] show ?case
      proof (safe, goal_cases)
        case (1 k')
        with \<open>x \<in> _\<close> have "\<not> x \<preceq> a" unfolding k_def by (auto dest: keys)
        with 1 \<open>x \<in> _\<close> show ?case by (auto intro: ranI simp: union)
      next
        case 2
        with \<open>x \<in> _\<close> have "\<not> x \<preceq> a" by auto
        with 2 \<open>x \<in> _\<close> show ?case
          unfolding xs_def by (auto simp: union split: option.split_asm intro: ranI)
      qed
    next
      case (2 x)
      then have "\<not> x \<preceq> a" "x \<in> set wait"
        by auto
      from this(2) obtain k' xs' where k': "wait' k' = Some xs'" "x \<in> set xs'"
        unfolding union ran_def by auto
      show ?case
      proof (cases "k' = k")
        case True
        with k' \<open>\<not> x \<preceq> a\<close> have "x \<in> set [x\<leftarrow>xs . \<not> x \<preceq> a']"
          unfolding xs_def by auto
        then show ?thesis unfolding ran_def by auto
      next
        case False
        with k' show ?thesis by (auto intro!: ranI)
      qed
    qed
    then have **: "(wait'(k \<mapsto> [x\<leftarrow>xs . \<not> x \<preceq> a']), [x\<leftarrow>wait . \<not> x \<preceq> a]) \<in> map_list_rel"
      unfolding map_list_rel_def xs_def by (auto intro: keys[OF sym])
    have ***: "(wait'(k \<mapsto> a' # [x\<leftarrow>xs . \<not> x \<preceq> a']), a # [x\<leftarrow>wait . \<not> x \<preceq> a]) \<in> map_list_rel"
      unfolding map_list_rel_def
      apply safe
      subgoal for x xs'
        using ** unfolding map_list_rel_alt_def by (fastforce simp: ran_def dest!: ran_upd_cases2)
      subgoal premises prems' for x
      proof -
        show ?thesis
        proof (cases "x = a")
          case True
          then show ?thesis by (force intro: ranI)
        next
          case False
          with prems' ** have "x \<in> (\<Union>x\<in>ran (wait'(k \<mapsto> [x\<leftarrow>xs . \<not> x \<preceq> a'])). set x)"
            unfolding map_list_rel_alt_def by auto
          with False show ?thesis by (fastforce dest!: ran_upd_cases2 simp: ran_def)
        qed
      qed
      subgoal
        using **
        apply (auto split: if_split_asm)
        unfolding map_list_rel_alt_def
         apply auto
        unfolding k_def by fastforce
      done
    have unfold:
      "(let k = key a'; xs = case wait' k of None \<Rightarrow> [] | Some wait' \<Rightarrow> wait'
          in if (\<exists>x\<in>set xs. a' \<preceq> x \<and> \<not> x \<preceq> a') \<or> empty a' then wait'(k \<mapsto> [x\<leftarrow>xs . \<not> x \<preceq> a'])
             else wait'(k \<mapsto> a' # [x\<leftarrow>xs . \<not> x \<preceq> a']))
       = (if (\<exists>x\<in>set xs. a' \<preceq> x \<and> \<not> x \<preceq> a') \<or> empty a' then wait'(k \<mapsto> [x\<leftarrow>xs . \<not> x \<preceq> a'])
          else wait'(k \<mapsto> a' # [x\<leftarrow>xs . \<not> x \<preceq> a']))"
      unfolding xs_def k_def by (simp add: Let_def)
    have
      "((let k = key a'; xs = case wait' k of None \<Rightarrow> [] | Some wait' \<Rightarrow> wait'
           in if (\<exists>x\<in>set xs. a' \<preceq> x \<and> \<not> x \<preceq> a') \<or> empty a' then wait'(k \<mapsto> [x\<leftarrow>xs . \<not> x \<preceq> a'])
              else wait'(k \<mapsto> a' # [x\<leftarrow>xs . \<not> x \<preceq> a'])),
           if (\<exists>x\<in>set wait. a \<preceq> x \<and> \<not> x \<preceq> a) \<or> empty a then [x\<leftarrow>wait . \<not> x \<preceq> a]
           else a # [x\<leftarrow>wait . \<not> x \<preceq> a]) \<in> map_list_rel"
      unfolding *[symmetric] unfold using ** *** by auto
    then show ?thesis by auto
  qed
  done
*)

term ASSERT

term take_from_list

definition take_from_wait :: "_ \<Rightarrow> _ \<Rightarrow> _ nres" where
  "take_from_wait wait wait_map = do {
    ASSERT (wait \<noteq> []);
    (k, wait) \<leftarrow> take_from_list wait;
    let v = wait_map k;
    case v of
      None \<Rightarrow> RETURN (None, wait, wait_map) |
      Some wait' \<Rightarrow>
        case wait' of
          [] \<Rightarrow> RETURN (None, wait, wait_map) |
          (n # wait') \<Rightarrow> RETURN (Some n, wait, wait_map(k \<mapsto> wait'))
  }
  "

(*
lemma take_from_list_correct:
  assumes "s \<noteq> []"
  shows "take_from_list s \<le> SPEC (\<lambda> (x, s'). s = x # s')"
using assms unfolding take_from_list_def by simp

lemmas [refine_vcg] = take_from_list_correct[THEN order.trans]
*)

abbreviation "ran' m \<equiv> (\<Union> x \<in> ran m. set x)"

definition "worklist_inv_frontier_map passed wait_map =
    (\<forall> a \<in> passed. \<forall> a'. E a a' \<and> \<not> empty a' \<longrightarrow> (\<exists> b' \<in> passed \<union> ran' wait_map. a' \<preceq> b'))"

definition "start_subsumed_map passed wait_map = (\<exists> a \<in> passed \<union> ran' wait_map. a\<^sub>0 \<preceq> a)"

definition "worklist_inv_map \<equiv> \<lambda> (passed, (wait, wait_map), brk).
    passed \<subseteq> Collect reachable \<and>
    (brk \<longrightarrow> (\<exists> f. reachable f \<and> F f)) \<and>
    (\<not> brk \<longrightarrow>
      worklist_inv_frontier_map passed wait_map
    \<and> (\<forall> a \<in> passed \<union> ran' wait_map. \<not> F a)
    \<and> start_subsumed_map passed wait_map
    \<and> ran' wait_map \<subseteq> Collect reachable)
    \<and> (\<forall> a \<in> passed. \<not> empty a) \<and> (\<forall> wait \<in> ran wait_map. \<forall> x \<in> set wait. \<not> empty x)
    \<and> key ` ran' wait_map \<subseteq> set wait
    "

definition worklist_algo_map' where
    "worklist_algo_map' = do
      {
        if F a\<^sub>0 then RETURN True
        else do {
          let passed = {};
          let w_wm = ([key a\<^sub>0], \<lambda> x. if x = key a\<^sub>0 then Some [a\<^sub>0] else None);
          (passed, (wait, wait_map), brk) \<leftarrow> WHILEIT worklist_inv_map (\<lambda> (passed, (wait, wait_map), brk). \<not> brk \<and> ran' wait_map \<noteq> {})
            (\<lambda> (passed, (wait, wait_map), brk). do
              {
                (a, wait, wait_map) \<leftarrow> take_from_wait wait wait_map;
                case a of
                  None \<Rightarrow> RETURN (passed, (wait, wait_map), brk) |
                  Some a \<Rightarrow>
                    if (\<exists> a' \<in> passed. a \<unlhd> a') then RETURN (passed, (wait, wait_map), brk) else
                    do
                      {
                        ((wait,wait_map),brk) \<leftarrow> add_succ1_map (wait,wait_map) a;
                        let passed = insert a passed;
                        RETURN (passed, (wait, wait_map), brk)
                      }
              }
            )
            (passed, w_wm, False);
            RETURN brk
        }
      }
    "

lemma worklist_inv_map_list:
  "worklist_inv_map x" if
  "(x, x') \<in> Id \<times>\<^sub>r wait_rel \<times>\<^sub>r Id" "worklist_inv_list x'"
  using that
  unfolding worklist_inv_list_def worklist_inv_map_def
  apply safe
    sorry

lemma take_from_list_ref[refine]:
    "take_from_list wait \<le>
     \<Down> {((x, wait), (y, wait')). x = y \<and> wait = wait' \<and> \<not> empty x \<and> (\<forall> a \<in> set wait. \<not> empty a)}
       (take_from_list wait')"
    if "wait = wait'" "\<forall> a \<in> set wait. \<not> empty a" "wait \<noteq> []"
    using that
    by (auto 4 4 simp: pw_le_iff refine_pw_simps dest!: take_from_list_correct)

  lemma worklist_algo_map'_ref[refine]: "worklist_algo_map' \<le> \<Down>Id worklist_algo1'"
    unfolding worklist_algo_map'_def worklist_algo1'_def
    apply (refine_rcg)
          prefer 3
          apply (rule worklist_inv_map_list, assumption, assumption)
         apply simp
        apply (simp add: wait_rel_def map_list_rel_def)
       apply auto[]
        apply (auto simp: wait_rel_def map_list_rel_def)[]
       apply (auto simp: wait_rel_def map_list_rel_def)[]
    subgoal
      sorry
    prefer 3
      apply (simp; fail)
        apply (auto simp: worklist_inv_map_def)[]

    apply refine_dref_type
    unfolding worklist_inv_list_def
    by aut

end

locale Search_Space_Pair =
  Search_Space_Pair_Defs + Search_Space' +
  assumes "(a1, b1) \<preceq> (a2, b2) \<Longrightarrow> a1 = a2"

locale Search_Space_Pair_Defs =
  Search_Space'_Defs E a\<^sub>0 F subsumes empty subsumes'
    for E :: "'a * 'b \<Rightarrow> 'a * 'b \<Rightarrow> bool"
    and a\<^sub>0 :: "'a * 'b"
    and F :: "'a * 'b \<Rightarrow> bool"
    and subsumes :: "'a * 'b \<Rightarrow> 'a * 'b \<Rightarrow> bool" (infix "\<preceq>" 50)
    and empty :: "'a * 'b \<Rightarrow> bool"
    and subsumes' :: "'a * 'b \<Rightarrow> 'a * 'b \<Rightarrow> bool" (infix "\<unlhd>" 50)
begin

term "x \<unlhd> y"

end

locale Search_Space_Pair =
  Search_Space_Pair_Defs + Search_Space' +
  assumes "(a1, b1) \<preceq> (a2, b2) \<Longrightarrow> a1 = a2"



end -- \<open>Theory\<close>

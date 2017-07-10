theory Worklist_Scratch
  imports Worklist_Subsumption1
begin

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

lemma take_from_wait_ref:
  "take_from_wait wait wait_map \<le> \<Down>{((a, w_wm), (a', l)). wait_rel w_wm l \<and> a \<in> ran' wait \<and> a' \<in> set wait \<and> set l} take_from_list wait'"
  if "((wait, wait_map), wait') \<in> wait_rel"
  oops

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

end --\<open>End of Theory\<close>
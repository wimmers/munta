theory Deadlock_Impl
  imports Deadlock
begin

subsection \<open>Functional Refinement\<close>

definition
  "free_upd1 n M c =
  (let
    M1 = fold (\<lambda>i M. if i \<noteq> c then (M((i, c) := op_mtx_get M (i, 0))) else M) [0..<Suc n] M;
    M2 = fold (\<lambda>i M. if i \<noteq> c then M((c,i) := \<infinity>)         else M) [0..<Suc n] M1
  in
    M2
  )
  "

definition
  "pre_reset_upd1 n M x \<equiv> free_upd1 n (restrict_zero_upd n M x) x"

definition
  "pre_reset_list_upd1 n M r \<equiv> fold (\<lambda> x M. pre_reset_upd1 n M x) r M"

definition
  "upd_pairs xs = fold (\<lambda>(p,q) f. f(p:=q)) xs"

lemma upd_pairs_Nil:
  "upd_pairs [] f = f"
  unfolding upd_pairs_def by simp

lemma upd_pairs_Cons:
  "upd_pairs ((p, q) # xs) f = upd_pairs xs (f(p:=q))"
  unfolding upd_pairs_def by simp

lemma upd_pairs_no_upd:
  assumes "p \<notin> fst ` set xs"
  shows "upd_pairs xs f p = f p"
  using assms by (induction xs arbitrary: f) (auto simp: upd_pairs_Nil upd_pairs_Cons)

lemma upd_pairs_upd:
  assumes "(p, y) \<in> set xs" "distinct (map fst xs)"
  shows "upd_pairs xs f p = y"
  using assms proof (induction xs arbitrary: f)
  case Nil
  then show ?case
    by (simp add: upd_pairs_Nil)
next
  case (Cons x xs)
  then show ?case
    by (cases x) (auto simp add: upd_pairs_Cons upd_pairs_no_upd)
qed

lemma upd_pairs_append:
  "upd_pairs (xs @ ys) = upd_pairs ys o upd_pairs xs"
  unfolding upd_pairs_def fold_append ..

lemma upd_pairs_commute_single:
  "upd_pairs xs (f(a := b)) = (upd_pairs xs f)(a := b)" if "a \<notin> fst ` set xs"
  using that by (induction xs arbitrary: f) (auto simp: upd_pairs_Nil upd_pairs_Cons fun_upd_twist)

lemma upd_pairs_append':
  "upd_pairs (xs @ ys) = upd_pairs xs o upd_pairs ys" if "fst ` set xs \<inter> fst ` set ys = {}"
  using that
proof (induction xs)
  case Nil
  then show ?case
    by (simp add: upd_pairs_Nil)
next
  case (Cons a xs)
  then show ?case
    by (cases a) (auto simp add: upd_pairs_Nil upd_pairs_Cons upd_pairs_commute_single)
qed

definition
  "upd_pairs' xs = fold (\<lambda>(p,q) f. f(p:=f q)) xs"

lemma upd_pairs'_Nil:
  "upd_pairs' [] f = f"
  unfolding upd_pairs'_def by simp

lemma upd_pairs'_Cons:
  "upd_pairs' ((p, q) # xs) f = upd_pairs' xs (f(p:=f q))"
  unfolding upd_pairs'_def by simp

lemma upd_pairs'_upd_pairs:
  assumes "fst ` set xs \<inter> snd ` set xs = {}"
  shows   "upd_pairs' xs f = upd_pairs (map (\<lambda>(p, q). (p, f q)) xs) f"
  using assms
proof (induction xs arbitrary: f)
  case Nil
  then show ?case
    by (simp add: upd_pairs_Nil upd_pairs'_Nil)
next
  case (Cons x xs)
  obtain a b where [simp]: "x = (a, b)"
    by (cases x)
  from Cons.prems have *:
    "map (\<lambda>(p, q). (p, if q = a then f b else f q)) xs = map (\<lambda>(p, q). (p, f q)) xs"
    by auto
  from Cons show ?case
    by (auto simp add: upd_pairs_Cons upd_pairs'_Cons *)
qed

lemma atLeastLessThan_alt_def:
  "{a..<b} = {k. a \<le> k \<and> k < b}"
  by auto

lemma atLeastLessThan_Suc_alt_def:
  "{a..<Suc b} = {k. a \<le> k \<and> k \<le> b}"
  by auto

lemma upd_pairs_map:
  "upd_pairs (map f xs) = fold (\<lambda>pq g. let (p,q) = f pq in g(p:=q)) xs"
  unfolding upd_pairs_def fold_map
  by (intro arg_cong2[where f = fold] ext) (auto simp: comp_def split: prod.split)

lemma down_upd_alt_def:
  "down_upd n M =
  upd_pairs ([((0, j), fold min [M (k, j). k \<leftarrow> [1..<Suc n]] (Le 0)). j \<leftarrow> [1..<Suc n]]) M"
proof -
  define xs where
    "xs = [((0::nat, j), Min ({Le 0} \<union> {M (k, j) | k. 1 \<le> k \<and> k \<le> n})). j \<leftarrow> [1..<Suc n]]"
  have "distinct (map fst xs)"
    unfolding xs_def by (auto simp add: map_concat comp_def distinct_map)
  have *: "fold min [M (k, j). k\<leftarrow>[1..<Suc n]] (Le 0) = Min ({Le 0} \<union> {M (k, j) |k. 1 \<le> k \<and> k \<le> n})"
    for j
    by (subst Min.set_eq_fold[symmetric])
       (auto simp: atLeastLessThan_Suc_alt_def simp del: upt_Suc intro: arg_cong[where f = Min])
  show ?thesis
    unfolding * xs_def[symmetric]
  by (intro ext, auto simp add: down_upd_def)
     (subst upd_pairs_upd[OF _ \<open>distinct _\<close>] upd_pairs_no_upd, auto simp: image_def xs_def; fail)+
qed

lemma down_upd_alt_def1:
  "down_upd n M =
  fold (\<lambda>j M. let (p,q) = ((0, j), fold min [M (k, j). k \<leftarrow> [1..<Suc n]] (Le 0)) in M(p:=q))
  [1..<Suc n] M"
proof -
  have *: "
    fold (\<lambda>j M.  let (p,q) = ((0,j), fold min [M (k, j). k \<leftarrow> [1..<Suc n]] (Le 0)) in M(p:=q))  xs M
  = fold (\<lambda>j M'. let (p,q) = ((0,j), fold min [M (k, j). k \<leftarrow> [1..<Suc n]] (Le 0)) in M'(p:=q)) xs M
  " for xs
  proof (induction xs arbitrary: M)
    case Nil
    then show ?case
      by simp
  next
    case (Cons x xs)
    then show ?case
      by (auto 4 7 intro: arg_cong2[where f = min] fold_cong)
  qed
  then show ?thesis
    unfolding down_upd_alt_def upd_pairs_map ..
qed

lemma
  "free_upd n M c =
  upd_pairs ([((c,i), \<infinity>). i \<leftarrow> [0..<Suc n], i \<noteq> c] @ [((i,c), M(i,0)). i \<leftarrow> [0..<Suc n], i \<noteq> c]) M"
  if "c \<le> n"
proof -
  let ?xs1 = "\<lambda>n. [((c,i), \<infinity>). i \<leftarrow> [0..<Suc n], i \<noteq> c]"
  let ?xs2 = "\<lambda>n. [((i,c), M(i,0)). i \<leftarrow> [0..<Suc n], i \<noteq> c]"
  define xs where "xs = ?xs1 n @ ?xs2 n"
  have "distinct (map fst xs)"
    unfolding xs_def
    apply (auto simp del: upt_Suc simp add: map_concat comp_def if_distrib split: if_split)
     apply (auto split: if_split_asm simp: distinct_map inj_on_def intro!: distinct_concat)
    done
  from \<open>c \<le> n\<close> show ?thesis
    unfolding xs_def[symmetric]
  by (intro ext, auto simp: free_upd_def)
     (subst upd_pairs_upd[OF _ \<open>distinct (map fst xs)\<close>] upd_pairs_no_upd, auto simp: xs_def; fail)+
qed

lemma free_upd_alt_def1:
  "free_upd n M c = (let
    M1 = upd_pairs' ([((i,c), (i,0)). i \<leftarrow> [0..<Suc n], i \<noteq> c]) M;
    M2 = upd_pairs ([((c,i), \<infinity>). i \<leftarrow> [0..<Suc n], i \<noteq> c]) M1
  in
    M2
  )" (is "_ = ?r")
  if "0 < c" "c \<le> n"
proof -
  let ?xs1 = "\<lambda>n. [((c,i), \<infinity>). i \<leftarrow> [0..<Suc n], i \<noteq> c]"
  let ?xs2 = "\<lambda>n. [((i,c), M(i,0)). i \<leftarrow> [0..<Suc n], i \<noteq> c]"
  define xs where "xs = ?xs1 n @ ?xs2 n"
  let ?t = "upd_pairs xs M"
  have "distinct (map fst xs)"
    unfolding xs_def
    apply (auto simp del: upt_Suc simp add: map_concat comp_def if_distrib split: if_split)
     apply (auto split: if_split_asm simp: distinct_map inj_on_def intro!: distinct_concat)
    done
  from \<open>c \<le> n\<close> have "free_upd n M c = ?t"
    by (intro ext, auto simp: free_upd_def)
      (subst upd_pairs_upd[OF _ \<open>distinct _\<close>] upd_pairs_no_upd, auto simp: xs_def; fail)+
  also have "\<dots> = ?r"
    unfolding xs_def
    apply (subst upd_pairs_append')
    subgoal
      by auto
    apply (subst upd_pairs'_upd_pairs)
    subgoal
      using \<open>c > 0\<close> by auto
    apply (simp del: upt_Suc add: map_concat)
    apply (intro arg_cong2[where f = upd_pairs] arg_cong[where f = concat])
    by (simp del: upt_Suc)+
  finally show ?thesis .
qed

lemma free_upd_free_upd1:
  "free_upd n M c = free_upd1 n M c" if "c > 0" "c \<le> n"
proof -
  let ?x1 = "\<lambda>xs. upd_pairs' ([((i,c), (i,0)). i \<leftarrow> xs, i \<noteq> c]) M"
  let ?x2 = "\<lambda>xs. fold (\<lambda>i M. if i \<noteq> c then (M((i, c) := M(i, 0))) else M) xs M"
  have *: "?x1 xs = ?x2 xs" for xs
    by (induction xs arbitrary: M) (auto simp: upd_pairs'_Nil upd_pairs'_Cons)
  let ?y1 = "\<lambda>xs. upd_pairs ([((c,i), \<infinity>). i \<leftarrow> xs, i \<noteq> c])"
  let ?y2 = "fold (\<lambda>i M. if i \<noteq> c then M((c,i) := \<infinity>) else M)"
  have **: "?y1 xs M = ?y2 xs M" for xs M
    by (induction xs arbitrary: M) (auto simp: upd_pairs_Nil upd_pairs_Cons)
  show ?thesis
    unfolding free_upd_alt_def1[OF that] free_upd1_def op_mtx_get_def * ** ..
qed

lemma free_upd_alt_def:
  "free_upd n M c =
    fold (\<lambda>i M. if i \<noteq> c then (M((c,i) := \<infinity>, (i, c) := M(i, 0))) else M) [0..<Suc n] M"
  if "c \<le> n"
  oops

lemma pre_reset_upd_pre_reset_upd1:
  "pre_reset_upd n M c = pre_reset_upd1 n M c" if "c > 0" "c \<le> n"
  unfolding pre_reset_upd_def pre_reset_upd1_def free_upd_free_upd1[OF that] ..

lemma pre_reset_list_upd_pre_reset_list_upd1:
  "pre_reset_list_upd n M cs = pre_reset_list_upd1 n M cs" if "\<forall>c \<in> set cs. 0 < c \<and> c \<le> n"
  unfolding pre_reset_list_upd_def pre_reset_list_upd1_def
  using that by (intro fold_cong; simp add: pre_reset_upd_pre_reset_upd1)

lemma pre_reset_list_transfer'[transfer_rule]:
  includes lifting_syntax shows
  "(eq_onp (\<lambda>x. x = n) ===> RI2 n ===> list_all2 (eq_onp (\<lambda>x. 0 < x \<and> x < Suc n)) ===> RI2 n)
    pre_reset_list pre_reset_list_upd1"
  unfolding rel_fun_def
  apply safe
  apply (subst pre_reset_list_upd_pre_reset_list_upd1[symmetric])
  subgoal
    unfolding list.rel_eq_onp by (auto simp: eq_onp_def list_all_iff)
  by (rule pre_reset_list_transfer[unfolded rel_fun_def, rule_format])
     (auto simp: eq_onp_def list_all2_iff)







subsection \<open>Abstract Implementation\<close>

context Reachability_Problem_Impl
begin

definition
  "check_deadlock_dbm l M = dbm_subset_fed_upd n M (
   [down_upd n (abstr_FW_upd n (inv_fun l) (abstr_FW_upd n g
      (pre_reset_list_upd1 n (abstr_FW_upd n (inv_fun l') (V_dbm' n)) r)
    )). (g, a, r, l') \<leftarrow> trans_fun l
   ]
  )"

abbreviation zone_of ("\<lbrakk>_\<rbrakk>") where "zone_of M \<equiv> [curry (conv_M M)]\<^bsub>v,n\<^esub>"

theorem check_deadlock_dbm_correct:
  "TA.check_deadlock l \<lbrakk>M\<rbrakk> = check_deadlock_dbm l M" if
  "\<lbrakk>M\<rbrakk> \<subseteq> V" "l \<in> states" "Deadlock.canonical' n (curry (conv_M M))"
proof -
  text \<open>0. Setup \<open>&\<close> auxiliary facts\<close>
  include lifting_syntax
  note [simp del] = And.simps abstr.simps (* TODO: make definitions *)
  have inv_of_simp: "inv_of (conv_A A) l = conv_cc (inv_fun l)" if \<open>l \<in> states\<close> for l
    using inv_fun \<open>l \<in> states\<close> unfolding inv_rel_def b_rel_def fun_rel_def
    by (force split: prod.split simp: inv_of_def)
  have inv_of_simp2: "inv_of A l = inv_fun l" if \<open>l \<in> states\<close> for l
    using inv_fun \<open>l \<in> states\<close> unfolding inv_rel_def b_rel_def fun_rel_def by force

  have trans_funD: "l' \<in> states"
    "collect_clks (inv_fun l) \<subseteq> clk_set A" "collect_clks (inv_fun l') \<subseteq> clk_set A"
    "collect_clks g \<subseteq> clk_set A" "set r \<subseteq> clk_set A"
    if "(g, a, r, l') \<in> set(trans_fun l)" for g a r l'
    subgoal
      using \<open>l \<in> states\<close> \<open>(g, a, r, l') \<in> _\<close> trans_fun_states by auto
    subgoal
      by (metis \<open>l \<in> states\<close> collect_clks_inv_clk_set inv_of_simp2)
    subgoal
      by (metis \<open>l' \<in> states\<close> collect_clks_inv_clk_set inv_of_simp2)
    subgoal
      using trans_fun_trans_of[OF that \<open>l \<in> _\<close>] by (rule collect_clocks_clk_set)
    subgoal
      using trans_fun_trans_of[OF that \<open>l \<in> _\<close>] by (rule reset_clk_set)
    done

  text \<open>1. Transfer to most abstract DBM operations\<close>
  have [transfer_rule]:
    "(eq_onp (\<lambda> (g, a, r, l'). (g, a, r, l') \<in> set (trans_fun l)) ===> RI2 n)
      (\<lambda>(g, a, r, l'). down n
          (abstr_FW n (conv_cc (inv_fun l))
            (abstr_FW n (conv_cc g)
              (pre_reset_list n (abstr_FW n (conv_cc (inv_fun l')) V_dbm v) r) v) v))
      (\<lambda>(g, a, r, l'). down_upd n
          (abstr_FW_upd n (inv_fun l)
            (abstr_FW_upd n g (pre_reset_list_upd1 n (abstr_FW_upd n (inv_fun l') (V_dbm' n)) r))
          ))
    " (is "(_ ===> RI2 n) (\<lambda> (g, a, r, l'). ?f g a r l') (\<lambda> (g, a, r, l'). ?g g a r l')")
  proof (intro rel_funI, clarsimp simp: eq_onp_def)
    fix g a r l' assume "(g, a, r, l') \<in> set (trans_fun l)"
    have *: "rel_acconstraint (eq_onp (\<lambda>x. 0 < x \<and> x < Suc n)) ri (conv_ac ac) ac"
      if "constraint_clk ac > 0" "constraint_clk ac \<le> n" for ac
      using that by (cases ac) (auto simp: eq_onp_def ri_def)
    have *: "list_all2 (rel_acconstraint (eq_onp (\<lambda>x. 0 < x \<and> x < Suc n)) ri) (conv_cc g) g"
      if "collect_clks g \<subseteq> clk_set A" for g
      unfolding list_all2_map1 using that clock_range
      by (auto simp: collect_clks_def intro!: * list.rel_refl_strong)
    have [transfer_rule]:
      "list_all2 (rel_acconstraint (eq_onp (\<lambda>x. 0 < x \<and> x < Suc n)) ri) (conv_cc g) g"
      "list_all2 (rel_acconstraint (eq_onp (\<lambda>x. 0 < x \<and> x < Suc n)) ri)
        (conv_cc (inv_fun l)) (inv_fun l)"
      "list_all2 (rel_acconstraint (eq_onp (\<lambda>x. 0 < x \<and> x < Suc n)) ri)
        (conv_cc (inv_fun l')) (inv_fun l')"
      by (intro * trans_funD[OF \<open>(g, a, r, l') \<in> set (trans_fun l)\<close>])+
    have [transfer_rule]:
      "list_all2 (eq_onp (\<lambda>x. 0 < x \<and> x < Suc n)) r r"
      using trans_funD(5)[OF \<open>(g, a, r, l') \<in> set (trans_fun l)\<close>] clock_range
      by (auto 4 3 dest: bspec subsetD simp: eq_onp_def list_all2_same)
    show "RI2 n (?f g a r l') (?g g a r l')"
      by transfer_prover
  qed
  have [transfer_rule]:
    "(eq_onp (\<lambda>l'. l' = l) ===> list_all2 (eq_onp (\<lambda>(g,a,r,l'). (g,a,r,l') \<in> set (trans_fun l))))
      trans_fun trans_fun
    "
    unfolding rel_fun_def eq_onp_def by (auto intro: list.rel_refl_strong)
  note [transfer_rule] = dbm_subset_fed_transfer
  have [transfer_rule]: "eq_onp (\<lambda>l'. l' = l) l l" "(eq_onp (\<lambda>x. x < Suc n)) n n"
    by (auto simp: eq_onp_def)
  have *: "
    (dbm_subset_fed n (curry (conv_M M))
         (map (\<lambda>(g, a, r, l').
                  down n
          (abstr_FW n (conv_cc (inv_fun l))
            (abstr_FW n (conv_cc g)
              (pre_reset_list n (abstr_FW n (conv_cc (inv_fun l')) V_dbm v) r) v) v))
           (trans_fun l))) =
    (dbm_subset_fed_upd n M
         (map (\<lambda>(g, a, r, l').
                  down_upd n
          (abstr_FW_upd n (inv_fun l)
            (abstr_FW_upd n g (pre_reset_list_upd1 n (abstr_FW_upd n (inv_fun l') (V_dbm' n)) r))
          ))
         (trans_fun l)))
    "
    by transfer_prover

  text \<open>2. Semantic argument establishing equivalences between zones and DBMs\<close>
  have **:
    "[down n (abstr_FW n (conv_cc (inv_fun l)) (abstr_FW n (conv_cc g)
          (pre_reset_list n (abstr_FW n (conv_cc (inv_fun l')) V_dbm v) r) v) v)]\<^bsub>v,n\<^esub>
  = (zone_set_pre ({u. u \<turnstile> inv_of (conv_A A) l'} \<inter> V) r \<inter> {u. \<forall> x \<in> set r. u x \<ge> 0}
       \<inter> {u. u \<turnstile> conv_cc g} \<inter> {u. u \<turnstile> inv_of (conv_A A) l})\<^sup>\<down> \<inter> V"
    if "(g, a, r, l') \<in> set(trans_fun l)" for g a r l'
  proof -
    from trans_funD[OF \<open>(g, a, r, l') \<in> set (trans_fun l)\<close>] have clock_conditions:
      "\<forall>c\<in>collect_clks (conv_cc (inv_fun l)). 0 < c \<and> c \<le> n"
      "\<forall>c\<in>collect_clks (conv_cc (inv_fun l')). 0 < c \<and> c \<le> n"
      "\<forall>c\<in>collect_clks (conv_cc g). 0 < c \<and> c \<le> n"
      "\<forall>c\<in>set r. 0 < c \<and> c \<le> n"
      using \<open>l \<in> states\<close> clock_range
      by (auto simp: constraint_clk_conv_cc inv_of_simp2[symmetric])
    have structural_conditions:
      "abstr_FW n (conv_cc (inv_fun l')) V_dbm v 0 0 \<le> 0"
      "\<forall>x\<in>set r. abstr_FW n (map conv_ac (inv_fun l')) V_dbm v 0 x \<le> 0"
      subgoal
        using abstr_FW_diag_preservation[of n V_dbm "conv_cc (inv_fun l')" v]
        by (simp add: V_dbm_def)
      subgoal
        using \<open>\<forall>c\<in>set r. 0 < c \<and> c \<le> n\<close>
        by (auto 4 3 simp: V_dbm_def intro: abstr_FW_mono order.trans)
      done
    note side_conditions = clock_conditions structural_conditions
      abstr_FW_canonical[unfolded canonical'_def] abstr_FW_canonical
    show ?thesis
      apply (subst dbm.down_correct, rule side_conditions)
      apply (subst dbm.abstr_FW_correct, rule side_conditions)
      apply (subst dbm.abstr_FW_correct, rule side_conditions)
      apply (subst dbm.pre_reset_list_correct, (rule side_conditions)+)
      apply (subst dbm.abstr_FW_correct, (rule side_conditions)+)
      by (simp add: inv_of_simp[OF \<open>l \<in> states\<close>] inv_of_simp[OF \<open>l' \<in> states\<close>] dbm.V_dbm_correct
          atLeastLessThanSuc_atLeastAtMost Int_commute)
  qed
  have **:
    "(\<Union>x\<in>set (trans_fun l).
              dbm.zone_of
               (case x of (g, a, r, l') \<Rightarrow>
                  down n
        (abstr_FW n (conv_cc (inv_fun l))
          (abstr_FW n (conv_cc g)
            (pre_reset_list n (abstr_FW n (conv_cc (inv_fun l')) V_dbm v) r) v) v)))
    = (\<Union>(g,a,r,l')\<in>set (trans_fun l).
    ((zone_set_pre ({u. u \<turnstile> inv_of (conv_A A) l'} \<inter> V) r \<inter> {u. \<forall> x \<in> set r. u x \<ge> 0}
           \<inter> {u. u \<turnstile> conv_cc g} \<inter> {u. u \<turnstile> inv_of (conv_A A) l})\<^sup>\<down> \<inter> V)
    )
    "
    by (auto simp: **)

  text \<open>3. Putting it all together\<close>
  have transD: "\<exists> g'. (g', a, r, l') \<in> set (trans_fun l) \<and> g = conv_cc g'"
    if "conv_A A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" for g a r l'
    using trans_of_trans_fun that \<open>l \<in> states\<close>
    unfolding trans_of_def by (auto 6 0 split: prod.split_asm)
  have transD2:
    "conv_A A \<turnstile> l \<longrightarrow>\<^bsup>conv_cc g,a,r\<^esup> l'" if "(g, a, r, l') \<in> set (trans_fun l)" for g a r l'
    using trans_fun_trans_of[OF that \<open>l \<in> states\<close>]
    unfolding trans_of_def by (auto 4 3 split: prod.split)
  show ?thesis
    unfolding TA.check_deadlock_alt_def[OF \<open>\<lbrakk>M\<rbrakk> \<subseteq> V\<close>] check_deadlock_dbm_def *[symmetric]
    apply (subst dbm.dbm_subset_fed_correct[symmetric, OF that(3)])
    apply (simp add: **)
    apply safe
    subgoal for x
      by (auto 4 5 elim!: transD[elim_format] dest: subsetD)
    subgoal for x
      apply (drule subsetD, assumption)
      apply clarsimp
      subgoal for g a r l'
        apply (inst_existentials "
          (zone_set_pre ({u. u \<turnstile> inv_of (conv_A A) l'} \<inter> V) r \<inter> {u. \<forall>x\<in>set r. 0 \<le> u x}
           \<inter> {u. u \<turnstile> conv_cc g} \<inter> {u. u \<turnstile> inv_of (conv_A A) l})\<^sup>\<down> \<inter> V" "conv_cc g" a r l')
        apply (auto dest: transD2)
        done
      done
    done
qed

subsection \<open>Imperative Refinement\<close>

paragraph \<open>Implementation of the invariant precondition check\<close>

  definition
    "V_dbm'' = V_dbm' n"

  lemma V_dbm'_alt_def:
    "V_dbm' n = op_amtx_new (Suc n) (Suc n) (V_dbm'')"
    unfolding V_dbm''_def by simp

  text \<open>We need the custom rule here because V\_dbm is a higher-order constant\<close>
  lemma [sepref_fr_rules]:
    "(uncurry0 (return V_dbm''), uncurry0 (RETURN (PR_CONST (V_dbm''))))
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a pure (nat_rel \<times>\<^sub>r nat_rel \<rightarrow> Id)"
    by sepref_to_hoare sep_auto

  (* sepref_register "V_dbm' :: nat \<times> nat \<Rightarrow> int DBMEntry" :: "'b DBMEntry i_mtx" *)
  sepref_register "V_dbm'' :: nat \<times> nat \<Rightarrow> _ DBMEntry"

  text \<open>Necessary to solve side conditions of @{term op_amtx_new}\<close>
  lemma V_dbm''_bounded:
    "mtx_nonzero V_dbm'' \<subseteq> {0..<Suc n} \<times> {0..<Suc n}"
    unfolding mtx_nonzero_def V_dbm''_def V_dbm'_def neutral by auto

  text \<open>We need to pre-process the lemmas due to a failure of \<open>TRADE\<close>\<close>
  lemma V_dbm''_bounded_1:
    "(a, b) \<in> mtx_nonzero V_dbm'' \<Longrightarrow> a < Suc n"
    using V_dbm''_bounded by auto

  lemma V_dbm''_bounded_2:
    "(a, b) \<in> mtx_nonzero V_dbm'' \<Longrightarrow> b < Suc n"
    using V_dbm''_bounded by auto

  context
    notes [id_rules] = itypeI[of "PR_CONST n" "TYPE (nat)"]
      and [sepref_import_param] = IdI[of n]
  begin

  sepref_definition V_dbm_impl is
    "uncurry0 (RETURN (PR_CONST (V_dbm' n)))" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a mtx_assn n"
    supply V_dbm''_bounded_1[simp] V_dbm''_bounded_2[simp]
    using V_dbm''_bounded
    apply (subst V_dbm'_alt_def)
    unfolding PR_CONST_def by sepref

  end (* End sepref setup *)

context
  notes [map_type_eqs] = map_type_eqI[of "TYPE(nat * nat \<Rightarrow> 'e)" "TYPE('e i_mtx)"]
  notes [map_type_eqs] = map_type_eqI[of "TYPE((nat * nat \<Rightarrow> 'e) list)" "TYPE(('e i_mtx) list)"]
begin

sepref_definition abstr_FW_impl is
  "uncurry (RETURN oo PR_CONST (abstr_FW_upd n))" ::
  "(list_assn (acconstraint_assn (clock_assn n) id_assn))\<^sup>k *\<^sub>a (mtx_assn n)\<^sup>d \<rightarrow>\<^sub>a mtx_assn n"
  unfolding abstr_FW_upd_def FW''_def[symmetric] PR_CONST_def by sepref

sepref_definition free_impl is
  "uncurry (RETURN oo PR_CONST (free_upd1 n))" ::
  "[\<lambda>(_, i). i\<le>n]\<^sub>a (mtx_assn n)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> mtx_assn n"
  unfolding free_upd1_def op_mtx_set_def[symmetric] PR_CONST_def by sepref

sepref_definition and_entry_impl is
  "uncurry2 (uncurry (\<lambda>x. RETURN ooo and_entry_upd x))" ::
  "[\<lambda>(((i, j),_),_). i\<le>n \<and> j \<le> n]\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k *\<^sub>a (mtx_assn n)\<^sup>d \<rightarrow> mtx_assn n"
  unfolding and_entry_upd_def by sepref

sepref_register and_entry_upd

lemmas [sepref_fr_rules] = and_entry_impl.refine

sepref_definition restrict_zero_impl is
  "uncurry (RETURN oo PR_CONST (restrict_zero_upd n))" ::
  "[\<lambda>(_, i). i\<le>n]\<^sub>a (mtx_assn n)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> mtx_assn n"
  unfolding restrict_zero_upd_def PR_CONST_def by sepref

sepref_register "restrict_zero_upd n" "free_upd1 n"

lemmas [sepref_fr_rules] = free_impl.refine restrict_zero_impl.refine

sepref_definition pre_reset_impl is
  "uncurry (RETURN oo PR_CONST (pre_reset_upd1 n))" ::
  "[\<lambda>(_, i). i\<le>n]\<^sub>a (mtx_assn n)\<^sup>d *\<^sub>a (clock_assn n)\<^sup>k \<rightarrow> mtx_assn n"
  unfolding pre_reset_upd1_def PR_CONST_def by sepref

sepref_register "pre_reset_upd1 n"

lemmas [sepref_fr_rules] = pre_reset_impl.refine

sepref_definition pre_reset_list_impl is
  "uncurry (RETURN oo PR_CONST (pre_reset_list_upd1 n))" ::
  "(mtx_assn n)\<^sup>d *\<^sub>a (list_assn (clock_assn n))\<^sup>k \<rightarrow>\<^sub>a mtx_assn n"
  unfolding pre_reset_list_upd1_def PR_CONST_def by sepref

definition "inner_loop M i = fold min (map (\<lambda>k. M (k, i :: nat)) [1..<Suc n]) (Le 0)"

sepref_register inner_loop :: "('e :: {zero,linorder}) DBMEntry i_mtx \<Rightarrow> nat \<Rightarrow> 'e DBMEntry"

lemma inner_loop_alt_def:
  "inner_loop M i = fold (\<lambda>k a. min (M (k, i)) a) [1..<Suc n] (Le 0)"
  unfolding inner_loop_def fold_map comp_def ..

sepref_thm inner_loop is
  "uncurry (RETURN oo PR_CONST inner_loop)" ::
  "[\<lambda>(_, i). i\<le>n]\<^sub>a (mtx_assn n)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> id_assn"
  unfolding inner_loop_alt_def PR_CONST_def by sepref

lemmas [sepref_fr_rules] = inner_loop.refine_raw

sepref_definition down_impl is
  "RETURN o PR_CONST (down_upd n)" ::
  "(mtx_assn n)\<^sup>d \<rightarrow>\<^sub>a mtx_assn n"
  unfolding down_upd_alt_def1 upd_pairs_map PR_CONST_def
  unfolding Let_def prod.case
  unfolding fold_map comp_def
  (* unfolding inner_loop_def[symmetric] *)
  by sepref

sepref_definition and_entry_repair_impl is
  "uncurry2 (uncurry (\<lambda>x. RETURN ooo PR_CONST (and_entry_repair_upd n) x))" ::
  "[\<lambda>(((i, j),_),_). i\<le>n \<and> j \<le> n]\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k *\<^sub>a (mtx_assn n)\<^sup>d \<rightarrow> mtx_assn n"
  unfolding and_entry_repair_upd_def PR_CONST_def by sepref

definition make_clock :: "nat \<Rightarrow> nat" where [code_unfold]:
  "make_clock = (\<lambda> x. x)"

lemma make_clock[sepref_import_param]:
  "(make_clock, make_clock) \<in> [\<lambda>i. i \<le> n]\<^sub>f nat_rel \<rightarrow> clock_rel"
  unfolding make_clock_def
  apply (rule frefI)
  apply auto
  done

definition "get_entries m =
  [(make_clock i, make_clock j). i\<leftarrow>[0..<Suc n], j\<leftarrow>[0..<Suc n], (i > 0 \<or> j > 0) \<and> i \<le> n \<and> j \<le> n \<and> m (i, j) \<noteq> \<infinity>]"

lemma dbm_minus_canonical_upd_alt_def:
  "dbm_minus_canonical_upd n xs m =
  concat (map (\<lambda>ij. map (\<lambda> M. and_entry_repair_upd n (snd ij) (fst ij) (neg_dbm_entry (m (fst ij, snd ij))) (op_mtx_copy M)) (xs))
    (get_entries m))"
  unfolding dbm_minus_canonical_upd_def op_mtx_copy_def COPY_def get_entries_def split_beta make_clock_def
  by simp

definition
  "upd_entry i j M m = and_entry_repair_upd n j i (neg_dbm_entry (m (i, j))) (op_mtx_copy M)"

definition
  "upd_entries i j m = map (\<lambda> M. upd_entry i j M m)"

sepref_register "and_entry_repair_upd n"

lemma [sepref_import_param]: "(neg_dbm_entry,neg_dbm_entry) \<in> Id\<rightarrow>Id" by simp

lemmas [sepref_fr_rules] = and_entry_repair_impl.refine

sepref_definition upd_entry_impl is
  "uncurry2 (uncurry (\<lambda>x. RETURN ooo PR_CONST upd_entry x))" ::
  "[\<lambda>(((i, j),_),_). i\<le>n \<and> j \<le> n]\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (mtx_assn n)\<^sup>k *\<^sub>a (mtx_assn n)\<^sup>k \<rightarrow> mtx_assn n"
  unfolding upd_entry_def PR_CONST_def by sepref

sepref_register upd_entry upd_entries get_entries

lemma [intf_of_assn]:
  "intf_of_assn AA TYPE('aa) \<Longrightarrow> intf_of_assn (list_assn(AA)) TYPE('aa list)"
  by simp

lemma map_conv_rev_fold:
  "map f xs = rev (fold (\<lambda> a xs. f a # xs) xs [])"
proof -
  have "fold (\<lambda> a xs. f a # xs) xs ys = rev (map f xs) @ ys" for ys
    by (induction xs arbitrary: ys) auto
  then show ?thesis
    by simp
qed

lemma rev_map_conv_fold:
  "rev (map f xs) = fold (\<lambda> a xs. f a # xs) xs []"
  using map_conv_rev_fold[of f xs] by simp

lemmas [sepref_fr_rules] = upd_entry_impl.refine

sepref_definition upd_entries_impl is
  "uncurry2 (uncurry (\<lambda>x. RETURN ooo PR_CONST upd_entries x))" ::
  "[\<lambda>(((i, j),_),_). i\<le>n \<and> j \<le> n]\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (mtx_assn n)\<^sup>k *\<^sub>a (list_assn (mtx_assn n))\<^sup>k \<rightarrow> list_assn (mtx_assn n)"
  unfolding upd_entries_def PR_CONST_def
  unfolding map_conv_rev_fold rev_conv_fold
  supply [sepref_fr_rules] = HOL_list_empty_hnr_aux
  by sepref

lemma [sepref_import_param]: "((=), (=)) \<in> Id\<rightarrow>Id\<rightarrow>Id" by simp

lemma concat_map_conv_rev_fold:
  "concat (map f xs) = rev (fold (\<lambda> xs ys. rev (f xs) @ ys) xs [])"
proof -
  have "rev (fold (\<lambda> xs ys. rev (f xs) @ ys) xs ys) = rev ys @ List.maps f xs" for ys
    by (induction xs arbitrary: ys) (auto simp: maps_simps)
  then show ?thesis
    by (simp add: concat_map_maps)
qed

lemma concat_conv_fold_rev:
  "concat xss = fold (@) (rev xss) []"
  using fold_append_concat_rev[of "rev xss"] by simp

sepref_definition get_entries_impl is
  "RETURN o PR_CONST get_entries" ::
  "(mtx_assn n)\<^sup>k \<rightarrow>\<^sub>a list_assn ((clock_assn n) \<times>\<^sub>a (clock_assn n))"
  unfolding get_entries_def PR_CONST_def
  unfolding map_conv_rev_fold
  unfolding concat_conv_fold_rev
  supply [sepref_fr_rules] = HOL_list_empty_hnr_aux
  by sepref

lemmas [sepref_fr_rules] = upd_entries_impl.refine get_entries_impl.refine

sepref_definition dbm_minus_canonical_impl is
  "uncurry (RETURN oo PR_CONST (dbm_minus_canonical_upd n))" ::
  "(list_assn (mtx_assn n))\<^sup>k *\<^sub>a (mtx_assn n)\<^sup>k \<rightarrow>\<^sub>a list_assn (mtx_assn n)"
  unfolding dbm_minus_canonical_upd_alt_def PR_CONST_def
  unfolding upd_entry_def[symmetric] upd_entries_def[symmetric]
  unfolding concat_map_conv_rev_fold rev_conv_fold
  supply [sepref_fr_rules] = HOL_list_empty_hnr_aux
  by sepref

sepref_register "dbm_minus_canonical_upd n"

lemmas [sepref_fr_rules] = dbm_minus_canonical_impl.refine

lemma filter_conv_rev_fold:
  "filter P xs = rev (fold (\<lambda>x xs. if P x then x # xs else xs) xs [])"
proof -
  have "rev ys @ filter P xs = rev (fold (\<lambda>x xs. if P x then x # xs else xs) xs ys)" for ys
    by (induction xs arbitrary: ys) (auto, metis revg.simps(2) revg_fun)
  from this[symmetric] show ?thesis
    by simp
qed

sepref_definition dbm_subset_fed_impl is
  "uncurry (RETURN oo PR_CONST (dbm_subset_fed_upd n))" ::
  "(mtx_assn n)\<^sup>d *\<^sub>a (list_assn (mtx_assn n))\<^sup>d \<rightarrow>\<^sub>a bool_assn"
  unfolding dbm_subset_fed_upd_def PR_CONST_def
  unfolding list_all_foldli filter_conv_rev_fold
  supply [sepref_fr_rules] = HOL_list_empty_hnr_aux
  by sepref

sepref_register
  "dbm_subset_fed_upd n" "abstr_FW_upd n" "pre_reset_list_upd1 n" "V_dbm' n" "down_upd n"

sepref_register inv_fun

lemma check_deadlock_dbm_alt_def:
  "check_deadlock_dbm l M = dbm_subset_fed_upd n M (
   [down_upd n (abstr_FW_upd n (inv_of_A l) (abstr_FW_upd n g
      (pre_reset_list_upd1 n (abstr_FW_upd n (inv_of_A l') (V_dbm' n)) r)
    )). (g, a, r, l') \<leftarrow> trans_fun l
   ]
  )"
  sorry

lemmas [sepref_fr_rules] =
  V_dbm_impl.refine abstr_FW_impl.refine pre_reset_list_impl.refine
  down_impl.refine dbm_subset_fed_impl.refine

sepref_definition check_deadlock_impl is
  "uncurry (RETURN oo check_deadlock_dbm)" ::
  "location_assn\<^sup>k *\<^sub>a (mtx_assn n)\<^sup>d \<rightarrow>\<^sub>a bool_assn"
  unfolding check_deadlock_dbm_alt_def
  unfolding case_prod_beta
  unfolding map_conv_rev_fold
apply (rewrite "HOL_list.fold_custom_empty")
  by sepref

end
end

end
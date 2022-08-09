theory Unreachability_Abstract
  imports Unreachability_Misc
begin

paragraph \<open>Abstract \<open>nres\<close> algorithms for certification.\<close>

text \<open>We introduce some locales that correspond to the ones we have already have
for simulation graphs, but without requiring an order to facilitate reuse.\<close>
locale Paired_Graph =
  fixes E :: "('l \<times> 's) \<Rightarrow> ('l \<times> 's) \<Rightarrow> bool"

\<comment> \<open>For documentation, the proper sublocale instantiations happen in \<open>Unreachbility_Misc\<close>.\<close>
\<^cancel>\<open>sublocale Reachability_Invariant_paired_pre_defs \<subseteq> Paired_Graph .\<close>

locale Paired_Graph_Set =
  Paired_Graph where E = E for E :: "('l \<times> 's) \<Rightarrow> ('l \<times> 's) \<Rightarrow> bool" +
  fixes M :: "'l \<Rightarrow> 's set"
    and L :: "'l set"

\<^cancel>\<open>sublocale Reachability_Invariant_paired_defs \<subseteq> Paired_Graph_Set .\<close>

locale Paired_Graph_Invariant =
  Paired_Graph where E = E
    for E :: "('l \<times> 's) \<Rightarrow> ('l \<times> 's) \<Rightarrow> bool"+
  fixes P :: "('l \<times> 's) \<Rightarrow> bool"

\<^cancel>\<open>sublocale Unreachability_Invariant_paired_pre_defs \<subseteq> Paired_Graph_Invariant .\<close>

locale Paired_Graph_Set_Invariant =
  Paired_Graph_Invariant where E = E and P = P +
  Paired_Graph_Set where E = E and M = M and L = L
    for E :: "('l \<times> 's) \<Rightarrow> ('l \<times> 's) \<Rightarrow> bool"
    and M :: "'l \<Rightarrow> 's set"
    and L :: "'l set"
    and P :: "('l \<times> 's) \<Rightarrow> bool"

\<^cancel>\<open>sublocale Unreachability_Invariant_paired_defs \<subseteq> Paired_Graph_Set_Invariant .\<close>

context Paired_Graph_Set
begin

context
  fixes P :: "('l \<times> 's) \<Rightarrow> bool"
begin

definition "check_prop \<equiv>
do {
  xs \<leftarrow> SPEC (\<lambda>xs. set xs = PR_CONST L);
  monadic_list_all (\<lambda>l. do {
    xs \<leftarrow> SPEC (\<lambda>xs. set xs = PR_CONST M l);
    monadic_list_all (\<lambda>s. RETURN (PR_CONST P (l, s))) xs
  }
  ) xs
}"

lemma check_prop_correct:
  "check_prop \<le> SPEC (\<lambda>r. r \<longleftrightarrow> (\<forall>l \<in> L. \<forall>s \<in> M l. P (l, s)))"
  unfolding check_prop_def by (refine_vcg monadic_list_all_rule monadic_list_ex_rule) auto

end

end

locale Reachability_Impl_base_defs =
  Paired_Graph where E = E for E :: "'l \<times> 's \<Rightarrow> _" +
  fixes succs :: "'l \<Rightarrow> 's set \<Rightarrow> ('l \<times> 's set) list"

locale Reachability_Impl_base =
  Reachability_Impl_base_defs +
  fixes P
  assumes succs_correct:
    "\<And>l. \<forall>s \<in> xs. P (l, s)
  \<Longrightarrow> {(l', s')| l' ys s'. (l', ys) \<in> set (succs l xs) \<and> s' \<in> ys}
    = (\<Union> s \<in> xs. Collect (E (l, s)))"

locale Reachability_Impl_invariant_defs =
  Reachability_Impl_base_defs where E = E +
  Paired_Graph_Set where E = E for E :: "'l \<times> 's \<Rightarrow> _" +
  fixes R :: "'l \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool"
  fixes R_impl :: "'l \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool nres"

locale Reachability_Impl_invariant =
  Reachability_Impl_base +
  Reachability_Impl_invariant_defs +
  assumes R_impl_correct[unfolded RETURN_SPEC_conv]: "\<And>l s xs. R_impl l s xs \<le> RETURN (R l s xs)"

context Reachability_Impl_invariant_defs
begin

definition "check_invariant L' \<equiv>
do {
  monadic_list_all (\<lambda>l.
  do {
    let as = M l;
    let succs = succs l as;
    monadic_list_all (\<lambda>(l', xs).
    do {
      xs \<leftarrow> SPEC (\<lambda>xs'. set xs' = xs);
      if xs = [] then RETURN True else do {
        b1 \<leftarrow> RETURN (l' \<in> L);
        b2 \<leftarrow> monadic_list_all (\<lambda>x.
          R_impl l' x (M l')
        ) xs;
        RETURN (b1 \<and> b2)
      }
    }
    ) succs
  }
  ) L'
}
"

definition
  "check_invariant_spec L' \<equiv>
  \<forall>l \<in> L'. \<forall>s \<in> M l. \<forall>l' s'. E (l, s) (l', s') \<longrightarrow> l' \<in> L \<and> R l' s' (M l')"

definition
  "check_invariant_spec_pre L' \<equiv>
  \<forall>l \<in> set L'. \<forall>(l',xs) \<in> set (succs l (M l)). \<^cancel>\<open>\<forall>pair \<in> set (succs l (M l)). case pair of (l',xs) \<Rightarrow>\<close>
    (\<forall>s' \<in> xs. l' \<in> L \<and> R l' s' (M l'))"

end

context Reachability_Impl_invariant
begin

lemma check_invariant_correct_pre:
  "check_invariant L' \<le> RETURN (check_invariant_spec_pre L')"
  unfolding check_invariant_def check_invariant_spec_pre_def
  by (refine_vcg monadic_list_all_rule R_impl_correct) auto

context
  fixes L'
  assumes pre: "\<forall>l \<in> L. \<forall>s \<in> M l. P (l, s)" "set L' \<subseteq> L"
begin

lemma check_invariant_spec_pre_eq_check_invariant_spec:
  "check_invariant_spec_pre L' = check_invariant_spec (set L')"
proof -
  have *: "(\<forall>x\<in>set (succs l xs). case x of (l', xs) \<Rightarrow> \<forall>s'\<in>xs. l' \<in> L \<and> R l' s' (M l')) =
           (\<forall>s\<in>xs. \<forall>l' s'. E (l, s) (l', s') \<longrightarrow> l' \<in> L \<and> R l' s' (M l'))"
    if "xs = M l" "l \<in> L" for l xs
    using succs_correct[of xs l] pre(1) that by fastforce
  then show ?thesis
    unfolding check_invariant_spec_def check_invariant_spec_pre_def
    by (simp add: * pre(2)[THEN subsetD])
qed

lemma check_invariant_correct_strong:
  "check_invariant L' \<le> RETURN (check_invariant_spec (set L'))"
  using check_invariant_correct_pre
  unfolding check_invariant_spec_pre_eq_check_invariant_spec[symmetric] .

lemma check_invariant_correct:
  "check_invariant L' \<le> SPEC (\<lambda>r. r \<longrightarrow> check_invariant_spec (set L'))"
  using check_invariant_correct_strong by (rule Orderings.order.trans) simp

end

end (* Reachability Impl Invariant *)


locale Reachability_Problem_defs =
  Reachability_Impl_invariant_defs where E = E
  for E :: "'l \<times> 's \<Rightarrow> _" +
  fixes P' F :: "'l \<times> 's \<Rightarrow> bool"

locale Reachability_Problem_no_subsumption_defs =
  fixes succs :: "'l \<Rightarrow> 's set \<Rightarrow> ('l \<times> 's set) list"
    and M :: "'l \<Rightarrow> 's set"
    and L :: "'l set"
    and E :: "'l \<times> 's \<Rightarrow> 'l \<times> 's \<Rightarrow> bool"
    and P' :: "'l \<times> 's \<Rightarrow> bool"
    and F :: "'l \<times> 's \<Rightarrow> bool"
begin

sublocale Reachability_Impl_base_defs .

sublocale Paired_Graph_Set .

definition
  "check_final \<equiv> do {
  l \<leftarrow> SPEC (\<lambda>xs. set xs = L);
  monadic_list_all (\<lambda>l. do {
    xs \<leftarrow> SPEC (\<lambda>xs. set xs = M l);
    monadic_list_all (\<lambda>s.
      RETURN (\<not> F (l, s))
    ) xs
    }
  ) l
  }
"

definition
  "check_final_spec = (\<forall>s'\<in>{(l, s) |l s. l \<in> L \<and> s \<in> M l}. \<not> F s')"

lemma check_final_correct:
  "check_final \<le> SPEC (\<lambda>r. r \<longleftrightarrow> check_final_spec)"
  unfolding check_final_def check_final_spec_def by (refine_vcg monadic_list_all_rule) auto

lemma check_final_nofail:
  "nofail check_final"
  by (metis check_final_correct nofail_simps(2) pwD1)

end

context Reachability_Problem_defs
begin

sublocale Reachability_Problem_no_subsumption_defs .

definition
  "check_init l\<^sub>0 s\<^sub>0 \<equiv> do {
  b1 \<leftarrow> RETURN (l\<^sub>0 \<in> L);
  b2 \<leftarrow> RETURN (P' (l\<^sub>0, s\<^sub>0));
  b3 \<leftarrow> R_impl l\<^sub>0 s\<^sub>0 (M l\<^sub>0);
  RETURN (b1 \<and> b2 \<and> b3)
  }"

definition check_all_pre_alt_def:
  "check_all_pre l\<^sub>0 s\<^sub>0 \<equiv> do {
  b1 \<leftarrow> check_init l\<^sub>0 s\<^sub>0;
  b2 \<leftarrow> check_prop P';
  RETURN (b1 \<and> b2)
  }"

lemma check_all_pre_def:
  "check_all_pre l\<^sub>0 s\<^sub>0 = do {
  b1 \<leftarrow> RETURN (l\<^sub>0 \<in> L);
  b2 \<leftarrow> RETURN (P' (l\<^sub>0, s\<^sub>0));
  b3 \<leftarrow> R_impl l\<^sub>0 s\<^sub>0 (M l\<^sub>0);
  b4 \<leftarrow> check_prop P';
  RETURN (b1 \<and> b2 \<and> b3 \<and> b4)
  }"
  unfolding check_all_pre_alt_def check_init_def by simp

definition
  "check_init_spec l\<^sub>0 s\<^sub>0 \<equiv> l\<^sub>0 \<in> L \<and> (R l\<^sub>0 s\<^sub>0 (M l\<^sub>0)) \<and> P' (l\<^sub>0, s\<^sub>0)"

definition
  "check_all_pre_spec l\<^sub>0 s\<^sub>0 \<equiv>
  (\<forall>l \<in> L. \<forall>s \<in> M l. P' (l, s)) \<and> l\<^sub>0 \<in> L \<and> (R l\<^sub>0 s\<^sub>0 (M l\<^sub>0)) \<and> P' (l\<^sub>0, s\<^sub>0)"

end

locale Reachability_Problem_Start_defs =
  Reachability_Problem_defs where E = E
  for E :: "'l \<times> 's \<Rightarrow> _" +
  fixes l\<^sub>0 :: 'l and s\<^sub>0 :: 's

locale Reachability_Impl_defs =
  Reachability_Impl_invariant_defs +
  Reachability_Problem_Start_defs

locale Reachability_Impl_New =
  Reachability_Problem_defs +
  Reachability_Impl_invariant

locale Reachability_Impl_New_start =
  Reachability_Impl_defs +
  Reachability_Impl_New

context Reachability_Impl_New
begin

lemma check_all_pre_correct:
  "check_all_pre l\<^sub>0 s\<^sub>0 \<le> RETURN (check_all_pre_spec l\<^sub>0 s\<^sub>0)"
  unfolding check_all_pre_def check_all_pre_spec_def
  by (refine_vcg check_prop_correct R_impl_correct; auto simp: list_ex_iff)

lemma check_init_correct:
  "check_init l\<^sub>0 s\<^sub>0 \<le> RETURN (check_init_spec l\<^sub>0 s\<^sub>0)"
  unfolding check_init_def check_init_spec_def
  by (refine_vcg R_impl_correct; auto simp: list_ex_iff)

end

context Reachability_Impl_defs
begin

definition
  "check_all \<equiv> do {
  b \<leftarrow> check_all_pre l\<^sub>0 s\<^sub>0;
  if b then SPEC (\<lambda>r. r \<longrightarrow> check_invariant_spec L) else RETURN False
  }"

definition
  "certify_unreachable = do {
    b1 \<leftarrow> check_all;
    b2 \<leftarrow> check_final;
    RETURN (b1 \<and> b2)
  }"

lemma certify_unreachable_alt_def:
  "certify_unreachable = do {
    b1 \<leftarrow> check_all_pre l\<^sub>0 s\<^sub>0;
    b2 \<leftarrow> SPEC (\<lambda>r. r \<longrightarrow> check_invariant_spec L);
    b3 \<leftarrow> check_final;
    RETURN (b1 \<and> b2 \<and> b3)
  }"
  unfolding certify_unreachable_def check_all_def
  apply simp
  apply (fo_rule arg_cong2, auto)
  apply (rule ext)
  apply auto
  by (metis RETURN_rule Refine_Basic.bind_mono(1) dual_order.eq_iff
      let_to_bind_conv lhs_step_bind nofail_simps(2))

end

context Reachability_Impl_New_start
begin

definition
  "check_all_spec \<equiv> check_all_pre_spec l\<^sub>0 s\<^sub>0 \<and> check_invariant_spec L"

lemma check_all_correct:
  "check_all \<le> SPEC (\<lambda>r. r \<longrightarrow> check_all_spec)"
  unfolding check_all_def check_all_spec_def check_all_pre_def check_all_pre_spec_def
  by (refine_vcg check_prop_correct check_invariant_correct monadic_list_ex_rule R_impl_correct)
     auto

end

locale Reachability_Impl_correct_base =
  Reachability_Impl_base where E = E +
  Reachability_Impl_base_defs where E = E
    for E :: "'l \<times> 's \<Rightarrow> _" +
  fixes P' F :: "'l \<times> 's \<Rightarrow> bool"
  assumes P'_P: "\<And> l s. P' (l, s) \<Longrightarrow> P (l, s)"


locale Buechi_Impl_invariant =
  Reachability_Impl_base where E = E for E :: "'l \<times> 's \<Rightarrow> _" +
  fixes L :: "'l set" and M :: "'l \<Rightarrow> ('s \<times> nat) set"
begin

definition "check_invariant_buechi R L' \<equiv>
  monadic_list_all (\<lambda>l.
    do {
      let as = M l;
      as \<leftarrow> SPEC (\<lambda>xs'. set xs' = as);
      monadic_list_all (\<lambda>(x, i). do {
        let succs = succs l {x};
        monadic_list_all (\<lambda>(l', xs). do {
          xs \<leftarrow> SPEC (\<lambda>xs'. set xs' = xs);
          b1 \<leftarrow> RETURN (l' \<in> L);
          if xs = [] then RETURN True else do {
              ys \<leftarrow> SPEC (\<lambda>xs. set xs = M l');
              b2 \<leftarrow> monadic_list_all (\<lambda>y.
                monadic_list_ex (\<lambda>(z, j). RETURN (R l l' i j x y z)) ys
              ) xs;
              RETURN (b1 \<and> b2)
            }
          }) succs
      }) as
    }) L'"

definition
  "check_invariant_buechi_spec R L' \<equiv>
  \<forall>l \<in> L'. \<forall>(s, i) \<in> M l. \<forall>l' s'.
    E (l, s) (l', s') \<longrightarrow> l' \<in> L \<and> (\<exists>(s'', j) \<in> M l'. R l l' i j s s' s'')"

lemma check_invariant_buechi_correct:
  "check_invariant_buechi R L' \<le> SPEC (\<lambda>r. r \<longrightarrow> check_invariant_buechi_spec R (set L'))"
  (is "_ \<le> ?rhs")
  if assms: "\<forall>l \<in> L. \<forall>(s, _) \<in> M l. P (l, s)" "set L' \<subseteq> L"
proof -
  have *: "
    (case x of (s, i) \<Rightarrow> \<forall>x\<in>set (succs l {s}). case x of (l', ys) \<Rightarrow>
                  \<forall>s' \<in> ys. l' \<in> L \<and> (\<exists>(s'', j) \<in> M l'. R l l' i j s s' s'')) =
    (case x of (s, i) \<Rightarrow>
       \<forall>l' s'. E (l, s) (l', s') \<longrightarrow> l' \<in> L \<and> (\<exists>(s'', j) \<in> M l'. R l l' i j s s' s''))"
    if "x \<in> M l" "l \<in> L" for x l using succs_correct[of "{fst x}" l] assms(1) that by fastforce
  let ?R = "\<lambda>l s i l' s'. (\<exists>(s'', j) \<in> M l'. R l l' i j s s' s'')"
  let ?Q = "\<lambda>l s i. \<lambda>(l',ys). (\<forall>s' \<in> ys. l' \<in> L \<and> ?R l s i l' s')"
  let ?P = "\<lambda>l (s, i). \<forall>(l',ys) \<in> set (succs l {s}). ?Q l s i (l', ys)"
  have "check_invariant_buechi R L' \<le> SPEC (\<lambda>r. r \<longleftrightarrow>
    (\<forall>l \<in> set L'. \<forall>(s, i) \<in> M l. \<forall>(l',ys) \<in> set (succs l {s}). (\<forall>s' \<in> ys. l' \<in> L \<and>
      (\<exists>(s'', j) \<in> M l'. R l l' i j s s' s''))))"
    unfolding check_invariant_buechi_def
    apply (rule monadic_list_all_rule)
    apply refine_vcg
    subgoal for l xs
      apply (refine_vcg monadic_list_all_rule[where P = "?P l"])
      subgoal for _ s i
        apply (refine_vcg monadic_list_all_rule[where P = "?Q l s i"])
          apply (auto; fail)
        subgoal for _ l'
          apply (refine_vcg monadic_list_all_rule[where P = "?R l s i l'"])
          subgoal for s'
            apply (refine_vcg monadic_list_ex_rule)
            by auto
          by auto
        by auto
      by auto
    done
  also have "\<dots> \<le> ?rhs"
    unfolding check_invariant_buechi_spec_def by (auto simp: * assms(2)[THEN subsetD])
  finally show ?thesis .
qed

end


locale Reachability_Impl_common_defs =
  Reachability_Problem_no_subsumption_defs where M = "\<lambda>x. case M x of None \<Rightarrow> {} | Some S \<Rightarrow> S"
  for M :: "'k \<Rightarrow> 'b set option"
begin

definition
  "check_final' L' M' = do {
  l \<leftarrow> SPEC (\<lambda>xs. set xs = L');
  monadic_list_all (\<lambda>l. do {
    let S = op_map_lookup l M';
    case S of None \<Rightarrow> RETURN True | Some S \<Rightarrow> do {
      xs \<leftarrow> SPEC (\<lambda>xs. set xs = S);
      monadic_list_all (\<lambda>s.
        RETURN (\<not> PR_CONST F (l, s))
      ) xs
    }
    }
  ) l
  }"

lemma check_final_alt_def:
  "check_final' L M = check_final"
  unfolding check_final'_def check_final_def
  by (fo_rule arg_cong2, simp, fo_rule arg_cong) (auto split: option.split simp: bind_RES)

definition check_prop' where
  "check_prop' L' M' = do {
  l \<leftarrow> SPEC (\<lambda>xs. set xs = L');
  monadic_list_all (\<lambda>l. do {
    let S = op_map_lookup l M';
    case S of None \<Rightarrow> RETURN True | Some S \<Rightarrow> do {
      xs \<leftarrow> SPEC (\<lambda>xs. set xs = S);
      r \<leftarrow> monadic_list_all (\<lambda>s.
        RETURN (PR_CONST P' (l, s))
      ) xs;
      RETURN r
    }
    }
  ) l
  }"

lemma check_prop_alt_def:
  "check_prop' L M = check_prop P'"
  unfolding check_prop_def check_prop'_def
  by (fo_rule arg_cong2, simp, fo_rule arg_cong) (auto split: option.split simp: bind_RES)

lemma check_prop'_alt_def:
  "check_prop' L' M' = do {
  l \<leftarrow> SPEC (\<lambda>xs. set xs = L');
  monadic_list_all (\<lambda>l. do {
    let (S, M) = op_map_extract l M';
    case S of None \<Rightarrow> RETURN True | Some S \<Rightarrow> do {
      xs \<leftarrow> SPEC (\<lambda>xs. set xs = S);
      r \<leftarrow> monadic_list_all (\<lambda>s.
        RETURN (PR_CONST P' (l, s))
      ) xs;
      RETURN r
    }
    }
  ) l
  }"
  unfolding check_prop'_def
  by (fo_rule arg_cong2, simp, fo_rule arg_cong) (auto split: option.split simp: bind_RES)

end

locale Reachability_Impl_common =
  Reachability_Impl_common_defs +
  assumes L_finite: "finite L"
      and M_ran_finite: "\<forall>S \<in> ran M. finite S"
      and succs_finite: "\<forall>l S. \<forall>(l', S') \<in> set (succs l S). finite S \<longrightarrow> finite S'"
      and succs_empty: "\<And>l. succs l {} = []"
      \<comment> \<open>NB: This could be weakened to state that \<open>succs l {}\<close> only contains empty sets\<close>
begin

\<comment> \<open>Note that these three lemmas do not use @{thm succs_finite} and @{thm succs_empty}.\<close>

lemma M_listD:
  assumes "M l = Some S"
  shows "\<exists> xs. set xs = S"
  using M_ran_finite assms unfolding ran_def by (auto intro: finite_list)

lemma L_listD:
  shows "\<exists> xs. set xs = L"
  using L_finite by (rule finite_list)

lemma check_prop_gt_SUCCEED:
  "check_prop P' > SUCCEED"
  unfolding check_prop_def using L_listD
  by (fastforce split: option.split dest: M_listD
        intro: monadic_list_all_gt_SUCCEED bind_RES_gt_SUCCEED_I
     )

end


locale Certification_Impl_correct_base =
  Reachability_Impl_correct_base where E = E
    for E :: "'k \<times> 's \<Rightarrow> _" +
  fixes A :: "'s \<Rightarrow> ('si :: heap) \<Rightarrow> assn"
    and K :: "'k \<Rightarrow> ('ki :: {hashable,heap}) \<Rightarrow> assn"
    and Fi and keyi and Pi and copyi \<^cancel>\<open>and Lei\<close> and succsi
  assumes [sepref_fr_rules]: "(keyi,RETURN o PR_CONST fst) \<in> (prod_assn K A)\<^sup>k \<rightarrow>\<^sub>a K"
  assumes copyi[sepref_fr_rules]: "(copyi, RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A"
  assumes Pi_P'[sepref_fr_rules]: "(Pi,RETURN o PR_CONST P') \<in> (prod_assn K A)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  assumes Fi_F[sepref_fr_rules]: "(Fi,RETURN o PR_CONST F) \<in> (prod_assn K A)\<^sup>d \<rightarrow>\<^sub>a bool_assn"
  assumes succsi[sepref_fr_rules]:
    "(uncurry succsi,uncurry (RETURN oo PR_CONST succs))
    \<in> K\<^sup>k *\<^sub>a (lso_assn A)\<^sup>d \<rightarrow>\<^sub>a list_assn (K \<times>\<^sub>a lso_assn A)"
  assumes pure_K: "is_pure K"
  assumes left_unique_K: "IS_LEFT_UNIQUE (the_pure K)"
  assumes right_unique_K: "IS_RIGHT_UNIQUE (the_pure K)"

locale Certification_Impl =
  Reachability_Impl_common where M = M +
  Certification_Impl_correct_base where K = K and A = A
  for M :: "'k \<Rightarrow> 'a set option"
  and K :: "'k \<Rightarrow> 'ki :: {hashable,heap} \<Rightarrow> assn" and A :: "'a \<Rightarrow> 'ai :: heap \<Rightarrow> assn" +
  fixes l\<^sub>0 :: 'k and s\<^sub>0 :: 'a fixes l\<^sub>0i :: "'ki Heap" and s\<^sub>0i :: "'ai Heap"
  assumes l\<^sub>0i_l\<^sub>0[sepref_fr_rules]:
    "(uncurry0 l\<^sub>0i, uncurry0 (RETURN (PR_CONST l\<^sub>0))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a K"
  assumes s\<^sub>0i_s\<^sub>0[sepref_fr_rules]:
    "(uncurry0 s\<^sub>0i, uncurry0 (RETURN (PR_CONST s\<^sub>0))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a A"

end
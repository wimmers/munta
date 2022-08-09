theory Unreachability_Common
  imports
    Simulation_Graphs_Certification
    Unreachability_Abstract
begin

paragraph \<open>Instantiating Abstract Certification for Simulation Graphs.\<close>

sublocale Reachability_Invariant_paired_pre_defs \<subseteq> Paired_Graph .

sublocale Reachability_Invariant_paired_defs \<subseteq> Paired_Graph_Set .

sublocale Unreachability_Invariant_paired_pre_defs \<subseteq> Paired_Graph_Invariant .

sublocale Unreachability_Invariant_paired_defs \<subseteq> Paired_Graph_Set_Invariant .

locale Reachability_Impl_base2 =
  Reachability_Impl_base where E = E +
  Unreachability_Invariant_paired_pre_defs where E = E
  for E :: "'l \<times> 's \<Rightarrow> _" +
  fixes P' and F
  assumes P'_P: "\<And> l s. P' (l, s) \<Longrightarrow> P (l, s)"
  assumes F_mono: "\<And>a b. P a \<Longrightarrow> F a \<Longrightarrow> (\<lambda>(l, s) (l', s'). l' = l \<and> s \<preceq> s') a b \<Longrightarrow> P b \<Longrightarrow> F b"

locale Reachability_Impl_pre =
  Reachability_Impl_base where E = E +
  Reachability_Impl_base2 where E = E +
  Paired_Graph_Set where E = E for E :: "'l \<times> 's \<Rightarrow> _"
begin

sublocale Reachability_Impl_New
  where R = "\<lambda>l s xs. Bex xs (\<lambda>s'. s \<preceq> s')"
    and R_impl =
      "\<lambda>l s xs. do {xs \<leftarrow> SPEC (\<lambda>ys. set ys = xs); monadic_list_ex (\<lambda>s'. RETURN (s \<preceq> s')) xs}"
  by standard (refine_vcg monadic_list_ex_rule, auto)

end

locale Reachability_Impl_pre_start =
  Reachability_Impl_pre where E = E for E :: "'l \<times> 's \<Rightarrow> _" +
  fixes l\<^sub>0 :: 'l and s\<^sub>0 :: 's
begin

sublocale Reachability_Impl_New_start
  where R = "\<lambda>l s xs. Bex xs (\<lambda>s'. s \<preceq> s')"
    and R_impl =
      "\<lambda>l s xs. do {xs \<leftarrow> SPEC (\<lambda>ys. set ys = xs); monadic_list_ex (\<lambda>s'. RETURN (s \<preceq> s')) xs}"
  ..

end

lemma (in Reachability_Impl_New_start) certify_unreachable_correct:
  "certify_unreachable \<le> SPEC (\<lambda>r. r \<longrightarrow> check_all_spec \<and> check_final_spec)"
  unfolding certify_unreachable_def by (refine_vcg check_all_correct check_final_correct; fast)

locale Reachability_Impl_correct =
  Reachability_Impl_pre_start where E = E +
  Unreachability_Invariant_paired_pre where E = E for E :: "'l \<times> 's \<Rightarrow> _"
begin

lemma Unreachability_Invariant_pairedI[rule_format]:
  "check_all_spec
  \<longrightarrow> Unreachability_Invariant_paired (\<preceq>) (\<prec>) M L E P l\<^sub>0 s\<^sub>0 (\<lambda>(l, u) (l', u'). l' = l \<and> u \<preceq> u')"
  unfolding check_all_spec_def check_all_pre_spec_def check_invariant_spec_def
  by clarsimp (standard, auto dest: P'_P)

lemma check_all_correct':
  "check_all \<le> SPEC (\<lambda>r. r \<longrightarrow>
    Unreachability_Invariant_paired (\<preceq>) (\<prec>) M L E P l\<^sub>0 s\<^sub>0 (\<lambda>(l, u) (l', u'). l' = l \<and> u \<preceq> u'))"
  by (refine_vcg Unreachability_Invariant_pairedI check_all_correct) fast

lemma certify_unreachableI:
  "check_all_spec \<and> check_final_spec \<longrightarrow> (\<nexists>s'. E\<^sup>*\<^sup>* (l\<^sub>0, s\<^sub>0) s' \<and> F s')"
  by (rule impI Unreachability_Invariant_paired.final_unreachable Unreachability_Invariant_pairedI)+
     (auto intro: F_mono simp: check_final_spec_def)

lemma certify_unreachable_correct':
  "certify_unreachable \<le> SPEC (\<lambda>r. r \<longrightarrow> (\<nexists>s'. E\<^sup>*\<^sup>* (l\<^sub>0, s\<^sub>0) s' \<and> F s'))"
  by (refine_vcg certify_unreachableI[rule_format] certify_unreachable_correct; fast)

definition "check_invariant0 L' \<equiv>
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
        ys \<leftarrow> SPEC (\<lambda>xs. set xs = M l');
        b2 \<leftarrow> monadic_list_all (\<lambda>x.
          monadic_list_ex (\<lambda>y. RETURN (x \<preceq> y)) ys
        ) xs;
        RETURN (b1 \<and> b2)
      }
    }
    ) succs
  }
  ) L'
}
"

lemma check_invariant0_refine:
  "check_invariant0 L' \<le> check_invariant L'"
  unfolding check_invariant0_def check_invariant_def
  unfolding PR_CONST_def Let_def
  apply refine_mono
  apply (rule ballI)
  apply refine_mono
  apply clarsimp
  subgoal for l _ l'
    apply refine_mono
    apply (rule specify_left)
     apply refine_mono
    subgoal for xs1 in_L xs2
      apply (rule bind_gt_SUCCEED_I'[where r = "in_L \<and> (\<forall>x \<in> set xs1. \<exists>y \<in> set xs2. x \<preceq> y)"])
          apply (refine_vcg monadic_list_all_rule monadic_list_ex_rule)
           apply auto
       apply (refine_vcg monadic_list_all_rule monadic_list_ex_rule)
         apply (auto intro: succeed_rules)
      done
    done
  done

end

locale Buechi_Impl_pre =
  Buechi_Impl_invariant where M = M +
  Reachability_Impl_base2 for M :: "'l \<Rightarrow> ('s \<times> nat) set" +
  assumes finite: "finite L" "\<forall>l \<in> L. finite (M l)"
begin

definition
  "buechi_prop l l' i j s s' s'' \<equiv> l' \<in> L \<and> s' \<preceq> s'' \<and>
    (if F (l, s) then i < j else i \<le> j)"

text \<open>
Old alternative definition.
Slightly easier to work with but subsumptions are not deterministic.\<close>
\<comment> \<open>definition
  "SE \<equiv> \<lambda>(l, s) (l', s').
    l' = l \<and> (\<exists>j. is_arg_max (\<lambda>(s, i). i) (\<lambda>(s', j). s \<preceq> s' \<and> (s', j) \<in> M l) (s', j))"\<close>

definition
  "has_SE \<equiv> \<lambda>s l. \<exists>s' j. s \<preceq> s' \<and> (s', j) \<in> M l"

definition
  "SE \<equiv> \<lambda>(l, s) (l', s'). l' = l \<and> l \<in> L \<and> has_SE s l \<and>
    (\<exists>j. (s', j) = arg_max (\<lambda>(s, i). i) (\<lambda>(s', j). s \<preceq> s' \<and> (s', j) \<in> M l))"

lemma
  assumes "SE (l, s) (l', s')"
  shows SE_same_loc: "l' = l" and SE_subsumes: "s \<preceq> s'"
    and SE_is_arg_max: "\<exists>j. is_arg_max (\<lambda>(s, i). i) (\<lambda>(s', j). s \<preceq> s' \<and> (s', j) \<in> M l) (s', j)"
    (is "\<exists>j. is_arg_max ?f ?P (s', j)")
proof -
  from assms have "has_SE s l'" "l' \<in> L" and [simp]: "l' = l"
    unfolding SE_def by auto
  then obtain s1 j where "?P (s1, j)"
    unfolding has_SE_def by auto
  moreover have "finite (Collect ?P)"
    using finite \<open>l' \<in> L\<close> by (auto intro: finite_subset)
  moreover note arg_max_rule = arg_max_nat_lemma2[of ?P, OF calculation, of "\<lambda>(s, i). i"]
  then show "l' = l" "s \<preceq> s'" "\<exists>j. is_arg_max ?f ?P (s', j)"
    using assms unfolding is_arg_max_linorder SE_def is_arg_max_linorder by auto
qed

lemma SE_deterministic:
  assumes "\<And>s. s1 \<preceq> s \<longleftrightarrow> s2 \<preceq> s"
  assumes "SE (l, s1) (l', s1')" "SE (l, s2) (l', s2')"
  shows "s2' = s1'"
  using assms(2,3) unfolding SE_def by (clarsimp simp: assms(1)) (metis prod.inject)

lemma SE_I:
  assumes "(s'', j) \<in> M l'" "buechi_prop l l' i j s s' s''"
  shows "\<exists>(s'', j) \<in> M l'. SE (l', s') (l', s'')"
proof -
  let ?P = "\<lambda>(s1, j). s' \<preceq> s1 \<and> (s1, j) \<in> M l'"
  let ?f = "\<lambda>(s, i). i"
  from assms have "?P (s'', j)" "l' \<in> L"
    unfolding buechi_prop_def by auto
  have "finite (Collect ?P)"
    using finite \<open>l' \<in> L\<close> by (auto intro: finite_subset)
  from arg_max_nat_lemma2[OF \<open>?P (s'', j) \<close> this, of ?f] \<open>l' \<in> L\<close> show ?thesis
    unfolding has_SE_def SE_def is_arg_max_linorder by (auto 4 3)
qed

definition
  "check_all_pre_spec1 inits \<equiv>
  (\<forall>l \<in> L. \<forall>s \<in> fst ` M l. P' (l, s)) \<and>
  (\<forall>(l\<^sub>0, s\<^sub>0) \<in> inits. l\<^sub>0 \<in> L \<and> (\<exists> (s', _) \<in> M l\<^sub>0. s\<^sub>0 \<preceq> s') \<and> P' (l\<^sub>0, s\<^sub>0))"

definition
  "check_buechi inits \<equiv> do {
  b \<leftarrow> SPEC (\<lambda>r. r \<longrightarrow> check_all_pre_spec1 inits);
  if b then do {
    ASSERT (check_all_pre_spec1 inits);
    SPEC (\<lambda>r. r \<longrightarrow> check_invariant_buechi_spec (buechi_prop ) L)
  } else RETURN False
  }"

definition
  "check_buechi_spec inits \<equiv>
  check_all_pre_spec1 inits
  \<and> (\<forall>l \<in> L. \<forall>(s, i) \<in> M l. \<forall>l' s'. E (l, s) (l', s')
    \<longrightarrow> (\<exists>(s'', j) \<in> M l'. buechi_prop l l' i j s s' s''))"

definition
  "check_buechi_spec' inits \<equiv>
  (\<forall>(l\<^sub>0, s\<^sub>0) \<in> inits. Unreachability_Invariant_paired (\<preceq>) (\<prec>) (\<lambda>l. fst ` M l) L E P l\<^sub>0 s\<^sub>0 SE)
  \<and> (\<forall>l \<in> L. \<forall>(s, i) \<in> M l. \<forall>l' s'. E (l, s) (l', s')
    \<longrightarrow> (\<exists>(s'', j) \<in> M l'. buechi_prop l l' i j s s' s''))"

lemma check_buechi_correct:
  "check_buechi inits \<le> SPEC (\<lambda>r. r \<longrightarrow> check_buechi_spec inits)"
  unfolding check_buechi_def check_invariant_buechi_spec_def check_buechi_spec_def
  by (refine_vcg; blast)

end


locale Buechi_Impl_correct =
  Buechi_Impl_pre where M = M and E = E+
  Unreachability_Invariant_paired_pre where E = E for E and M :: "'l \<Rightarrow> ('s \<times> nat) set"
begin

lemma check_buechi_correct':
  "check_buechi inits \<le> SPEC (\<lambda>r. r \<longrightarrow> check_buechi_spec' inits)"
proof -
  have "Unreachability_Invariant_paired (\<preceq>) (\<prec>) (\<lambda>l. fst ` M l) L E P l\<^sub>0 s\<^sub>0 SE"
    if "(l\<^sub>0, s\<^sub>0) \<in> inits" "check_all_pre_spec1 inits" "check_invariant_buechi_spec (buechi_prop ) L"
    for l\<^sub>0 s\<^sub>0
    using that unfolding check_invariant_buechi_spec_def check_all_pre_spec1_def
    apply -
    apply standard
         apply (use SE_I SE_same_loc SE_subsumes in
          \<open>auto 4 3 dest!: P'_P simp: list_ex_iff Ball_def_raw Bex_def_raw\<close>)
    apply (smt case_prodE fst_conv)
    done
  then show ?thesis
    unfolding check_buechi_def check_invariant_buechi_spec_def check_buechi_spec'_def
    by (refine_vcg; blast)
qed

definition f where
  "f \<equiv> \<lambda>(l, s). Max {i. (s, i) \<in> M l}"

lemma
  assumes "l \<in> L" "(s, i) \<in> M l"
  shows f_in: "(s, f (l, s)) \<in> M l" (is "?P1")
    and f_ge: "\<forall>j. (s, j) \<in> M l \<longrightarrow> j \<le> f (l, s)" (is "?P2")
proof -
  have "finite {i. (s, i) \<in> M l}"
    using finite \<open>l \<in> L\<close> [[simproc add: finite_Collect]] by auto
  with assms(2) show ?P1 ?P2
    unfolding f_def by (auto intro: Max_ge dest: Max_in)
qed

lemma f_topo:
  fixes l :: \<open>'l\<close> and s :: \<open>'s\<close> and l1 :: \<open>'l\<close> and s1 :: \<open>'s\<close> and l2 :: \<open>'l\<close> and s2 :: \<open>'s\<close>
  assumes 
    "check_buechi_spec' inits"
    \<open>l \<in> L\<close> and
    \<open>s \<in> fst ` M l\<close> and
    \<open>l2 \<in> L\<close> and
    \<open>s2 \<in> fst ` M l2\<close> and
    \<open>E (l, s) (l1, s1)\<close> and
    \<open>SE (l1, s1) (l2, s2)\<close>
  shows \<open>if F (l, s) then f (l, s) < f (l2, s2) else f (l, s) \<le> f (l2, s2)\<close>
proof -
  let ?P = "\<lambda>s l' (s', j). s \<preceq> s' \<and> (s', j) \<in> M l'"
  let ?f = "\<lambda>(s, i). i"
  let ?le = "\<lambda>l s i j. if F(l, s) then i < j else i \<le> j"
  from \<open>SE _ _\<close> obtain j where "(s2, j) \<in> M l2" and [simp]: "l2 = l1"
    and is_max: "is_arg_max ?f (?P s1 l1) (s2, j)"
    using SE_is_arg_max SE_same_loc SE_subsumes
    by atomize_elim (fastforce simp: Lattices_Big.ord_class.is_arg_max_def)
  from f_in assms have "(s, f (l, s)) \<in> M l"
    by auto
  with assms obtain s' i where "(s', i) \<in> M l2" "buechi_prop l l2 (f (l, s)) i s s1 s'"
    unfolding check_buechi_spec'_def by fastforce
  then have "(s', i) \<in> M l2" "s1 \<preceq> s'" "?le l s (f (l, s)) i"
    unfolding buechi_prop_def by auto
  from is_max \<open>(s', i) \<in> _\<close> \<open>s1 \<preceq> s'\<close> have "i \<le> j"
    unfolding is_arg_max_linorder by simp
  also from f_ge \<open>(s2, j) \<in> M l2\<close> have "j \<le> f (l2, s2)"
    using assms by auto
  finally show ?thesis
    using \<open>?le l s _ _\<close> by auto
qed

lemma no_buechi_run:
  assumes check: "check_buechi_spec' inits"
  assumes accepting_run:
    "(l\<^sub>0, s\<^sub>0) \<in> inits" "Graph_Defs.run E ((l\<^sub>0, s\<^sub>0) ## xs)" "alw (ev (holds F)) ((l\<^sub>0, s\<^sub>0) ## xs)"
  shows False
proof -
  interpret Unreachability_Invariant_paired "(\<preceq>)" "(\<prec>)" "\<lambda>l. fst ` M l" L E P l\<^sub>0 s\<^sub>0 SE
    using check \<open>_ \<in> inits\<close> unfolding check_buechi_spec'_def by blast
  show ?thesis
    apply (rule no_buechi_run[where F = F and f = f])
         apply (rule F_mono; assumption)
    using finite apply blast+
      apply (rule f_topo, rule check, assumption+)
     apply (rule accepting_run)+
    done
qed

end (* Buechi Impl pre *)


locale Reachability_Impl =
  Certification_Impl where M = M and K = K and A = A +
  Reachability_Impl_correct where M = "\<lambda>x. case M x of None \<Rightarrow> {} | Some S \<Rightarrow> S"
    for M :: "'k \<Rightarrow> 'a set option"
    and K :: "'k \<Rightarrow> 'ki :: {hashable,heap} \<Rightarrow> assn"
    and A :: "'a \<Rightarrow> 'ai :: heap \<Rightarrow> assn" +
  fixes Lei
  assumes Lei[sepref_fr_rules]:
    "(uncurry Lei,uncurry (RETURN oo PR_CONST less_eq)) \<in> A\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a bool_assn"

end
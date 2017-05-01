theory Normalized_Zone_Semantics_Impl_Semantic_Refinement
  imports TA_Impl_Misc Floyd_Warshall
    FW_More
    Normalized_Zone_Semantics_Impl
begin

no_notation Ref.update ("_ := _" 62)

hide_const D

hide_fact upd_def

lemma fold_acc_preserv':
  assumes "\<And> x acc. x \<in> set xs \<Longrightarrow> P acc \<Longrightarrow> P (f x acc)" "P acc"
  shows "P (fold f xs acc)"
  using assms by (induction xs arbitrary: acc) auto

lemma
  "\<one> = 0"
  oops

lemma
  fixes x :: "'a :: linordered_ab_monoid_add"
  assumes "x \<ge> \<one>"
  shows "y \<le> y + x"
    oops

lemma reset_canonical_canonical:
  "canonical (reset_canonical M k (d :: 'c :: linordered_ab_group_add)) n"
  if "\<forall> i \<le> n. M i i = \<one>" "canonical M n" "k > 0" for k n :: nat
proof -
  have add_mono_neutr': "a \<le> a + b" if "b \<ge> Le (0 :: 'c)" for a b
    using that unfolding neutral[symmetric] by (rule add_mono_neutr)
  have add_mono_neutl': "a \<le> b + a" if "b \<ge> Le (0 :: 'c)" for a b
    using that unfolding neutral[symmetric] by (rule add_mono_neutl)
  show ?thesis
    using that
    unfolding reset_canonical_def neutral
    apply (clarsimp split: if_splits)
    apply safe
                     apply (simp add: add_mono_neutr'; fail)
                    apply (simp add: comm; fail)
                   apply (simp add: add_mono_neutl'; fail)
                  apply (simp add: comm; fail)
                 apply (simp add: add_mono_neutl'; fail)
                apply (simp add: add_mono_neutl'; fail)
               apply (simp add: add_mono_neutl'; fail)
              apply (simp add: add_mono_neutl' add_mono_neutr'; fail)
             apply (simp add: assoc[symmetric] add_mono_neutl' add_mono_neutr'; fail)
            apply (simp add: assoc[symmetric] add_mono_neutl' add_mono_neutr' comm; fail)
           apply (simp add: assoc[symmetric] add_mono_neutl' add_mono_neutr'; fail)
    subgoal premises prems for i j k
    proof -
      from prems have "M i k \<le> M i 0 + M 0 k"
        by auto
      also have "\<dots> \<le> Le (- d) + M i 0 + (Le d + M 0 k)"
        apply (simp add: assoc[symmetric], simp add: comm, simp add: assoc[symmetric])
        by (metis le_less linordered_ab_monoid_add_class.neutr neutral)
      finally show ?thesis .
    qed
    subgoal premises prems for i j k
    proof -
      from prems have "Le 0 \<le> M 0 j + M j 0"
        by force
      also have "\<dots> \<le> Le d + M 0 j + (Le (- d) + M j 0)"
        apply (simp add: assoc[symmetric], simp add: comm, simp add: assoc[symmetric])
        by (metis le_less linordered_ab_monoid_add_class.neutr neutral comm)
      finally show ?thesis .
    qed
    subgoal premises prems for i j k
    proof -
      from prems have "Le 0 \<le> M 0 j + M j 0"
        by force
      then show ?thesis
        by (simp add: add.assoc add_mono_neutr')
    qed
    subgoal premises prems for i j k
    proof -
      from prems have "M 0 k \<le> M 0 j + M j k"
        by force
      then show ?thesis
        by (simp add: add_left_mono assoc)
    qed
    subgoal premises prems for i j
    proof -
      from prems have "M i 0 \<le> M i j + M j 0"
        by force
      then show ?thesis
        by (simp add: ab_semigroup_add_class.add.left_commute add_mono_right)
    qed
    subgoal premises prems for i j
    proof -
      from prems have "Le 0 \<le> M 0 j + M j 0"
        by force
      then show ?thesis
        by (simp add: ab_semigroup_add_class.add.left_commute add_mono_neutr')
    qed
    subgoal premises prems for i j
    proof -
      from prems have "M i 0 \<le> M i j + M j 0"
        by force
      then show ?thesis
        by (simp add: ab_semigroup_add_class.add.left_commute add_mono_right)
    qed
    done
qed

lemma reset_canonical_upd_canonical:
  "canonical (curry (reset_canonical_upd M n k (d :: 'c :: {linordered_ab_group_add,uminus}))) n"
  if "\<forall> i \<le> n. M (i, i) = \<one>" "canonical (curry M) n" "k > 0" for k n :: nat
  using reset_canonical_canonical[of n "curry M" k] that
  by (auto simp: reset_canonical_upd_reset_canonical')


(* XXX Move? *)
lemma fwi_characteristic:
  "canonical_subs n (I \<union> {k::nat}) (FWI M n k) \<or> (\<exists> i \<le> n. FWI M n k i i < \<one>)" if
  "canonical_subs n I M" "I \<subseteq> {0..n}" "k \<le> n"
proof (cases "\<one> \<le> M k k")
  case True
  from fwi_canonical_extend[OF that(1,2) this \<open>k \<le> n\<close>] show ?thesis unfolding FWI_def ..
next
  case False
  with \<open>k \<le> n\<close> fwi_mono[OF \<open>k \<le> n\<close> \<open>k \<le> n\<close>, of M k n n] show ?thesis
    unfolding FWI_def by fastforce
qed

definition canonical_set :: "(nat \<times> nat \<times> nat) set \<Rightarrow> _ DBM \<Rightarrow> bool" where
  "canonical_set I M \<equiv> \<forall> (k, i, j) \<in> I. M i j \<le> M i k + M k j"

definition canonical_sets :: "nat set \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> _ DBM \<Rightarrow> bool" where
  "canonical_sets K I J M \<equiv> \<forall> k \<in> K. \<forall> i \<in> I. \<forall> j \<in> J. M i j \<le> M i k + M k j"

lemma canonical_canonical_subs:
  "canonical M n \<longleftrightarrow> canonical_subs n {0..<n+1} M"
  unfolding canonical_subs_def by auto

lemma canonical_subs_upd:
  "canonical_subs n (I - {x, y}) (upd M x y e)" if "canonical_subs n I M" "e \<le> M x y"
  using that unfolding canonical_subs_def upd_def by (auto 4 4)

lemma fw_upd_id:
  "fw_upd M k i j i' j' = M i' j'" if "j' \<in> J" "i' \<in> I" "k \<in> K" "canonical_sets K I J M"
  using that
  unfolding fw_upd_def upd_def
  unfolding canonical_sets_def
  by auto

lemma fw_upd_id1[simp]:
  "fw_upd M k i j i' j' = M i' j'" if "i' \<noteq> i"
  using that unfolding fw_upd_def upd_def by simp

lemma fw_upd_id2[simp]:
  "fw_upd M k i j i' j' = M i' j'" if "j' \<noteq> j"
  using that unfolding fw_upd_def upd_def by simp

abbreviation "fw_order \<equiv> less_than <*lex*> less_than <*lex*> less_than"

context Reachability_Problem
  begin

abbreviation
  "canonical' D \<equiv> canonical (curry D) n"

abbreviation
  "canonical_diag' D \<equiv> canonical' D \<or> check_diag n D"

abbreviation
  "canonical_diag D \<equiv> canonical' (conv_M D) \<or> check_diag n D"

lemma canonical_diagI:
  "canonical_diag D"  if "canonical_diag' D"
  using that canonical_conv by auto

lemma canonical'_up_canonical_upd:
  assumes "canonical' M"
  shows "canonical' (up_canonical_upd M n)"
  using
    up_canonical_preservation[OF assms] up_canonical_eq_up[OF assms]
    up_canonical_upd_up_canonical'[of M n]
  unfolding curry_def n_eq_def by auto

lemma check_diag_up_canonical_upd:
  "check_diag n (up_canonical_upd M n)" if "check_diag n M"
  unfolding up_canonical_upd_def
  apply (rule fold_acc_preserv'[where P = "check_diag n"])
  using that by (auto simp: check_diag_def)

lemma canonical_diag'_up_canonical_upd:
  "canonical_diag' (up_canonical_upd M n)" if "canonical_diag' M"
  using that by (blast dest: canonical'_up_canonical_upd check_diag_up_canonical_upd)

abbreviation "canonical_subs' I M \<equiv> canonical_subs n I (curry M)"

lemma canonical_subs'_upd:
  "canonical_subs' (I - {a, b}) (M((a, b) := c))" if "canonical_subs' I M" "c \<le> M (a, b)"
  using that unfolding canonical_subs_def by (auto 4 4)

lemma FWI'_characteristic:
  "canonical_subs' (I \<union> {a::nat}) (FWI' M n a) \<or> check_diag n (FWI' M n a)" if
  "canonical_subs' I M" "I \<subseteq> {0..n}" "a \<le> n"
  using fwi_characteristic[of n I "curry M", OF that]
  unfolding check_diag_def neutral FWI'_def by simp

lemma FWI'_check_diag_preservation:
  "check_diag n (FWI' M n a)" if "check_diag n M"
  using that fwi_mono[of _ n _ "curry M" a n n] unfolding check_diag_def FWI'_def FWI_def by force

definition "repair_pair M a b = FWI' (FWI' M n b) n a"
lemmas FWI_zone_equiv_spec = FWI_zone_equiv[OF surj_numbering]

lemma curry_conv_M_swap:
  "(map_DBMEntry real_of_int \<circ>\<circ>\<circ> curry) M = curry (conv_M M)"
  by (intro ext; simp)

lemma repair_pair_equiv:
  "M \<simeq> repair_pair M a b" if "a \<le> n" "b \<le> n"
  unfolding dbm_equiv_def repair_pair_def FWI'_def
  apply (subst FWI_zone_equiv_spec[of b], rule that)
  apply (subst FWI_zone_equiv_spec[of a], rule that)
  by (simp add: FWI_def fwi_conv_M' fwi_conv_M'' curry_conv_M_swap)

lemma canonical'_conv_M_iff:
  "canonical' (conv_M D) \<longleftrightarrow> canonical' D"
  by (metis canonical_conv canonical_conv_rev)

lemma repair_pair_canonical_diag_1:
  "canonical_diag (repair_pair M a b)" if "canonical_subs' ({0..n} - {a, b}) M" "a \<le> n" "b \<le> n"
  using that
  unfolding canonical'_conv_M_iff
  unfolding repair_pair_def
  apply -
  apply (drule FWI'_characteristic[where a = b], force, assumption)
  apply (erule disjE)
   apply (drule FWI'_characteristic[where a = a], force, assumption)
  unfolding canonical_alt_def
  subgoal premises prems
  proof -
    have *: "{0..n} - {a, b} \<union> {b} \<union> {a} = {0..n}"
      using that(2,3) by fastforce
    with prems(3) show ?thesis by (simp only: *)
  qed
  by (auto intro: FWI'_check_diag_preservation)

lemma repair_pair_canonical_diag_2:
  "canonical_diag (repair_pair M a b)" if "check_diag n M"
  unfolding repair_pair_def using that by (auto intro: FWI'_check_diag_preservation)

lemma diag_conv_M:
  "\<forall>i\<le>n. conv_M D (i, i) \<le> \<one>" if "\<forall>i\<le>n. D (i, i) \<le> \<one>"
  using that by auto (metis DBMEntry.simps(15) conv_dbm_entry_mono neutral of_int_0)

lemma conv_M_diag:
  "\<forall>i\<le>n. D (i, i) \<le> \<one>" if "\<forall>i\<le>n. conv_M D (i, i) \<le> \<one>"
  using that by (simp add: conv_dbm_entry_mono_rev neutral)

lemma wf_dbm_altD:
  "canonical' D \<or> check_diag n D"
  "\<forall>i\<le>n. D (i, i) \<le> \<one>"
  "[curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> V"
  if "wf_dbm D"
  using that
    apply -
    apply (drule wf_dbm_D, simp only: canonical'_conv_M_iff; fail)
   apply (drule wf_dbm_D, auto intro!: conv_M_diag; fail)
  apply (drule wf_dbm_D, erule valid_dbm.cases, simp; fail)
  done

lemmas valid_dbm_convI = valid_dbm.intros[OF _ dbm_int_conv]
thm diag_conv
lemmas wf_dbm_altI = wf_dbm_I[OF _ diag_conv_M valid_dbm_convI]
(* XXX Why do we have two notions here? *)
thm valid_dbm_def

lemma wf_dbm_rule:
  assumes "wf_dbm D"
  assumes canonical:
    "canonical' D \<Longrightarrow> \<forall>i\<le>n. D (i, i) \<le> \<one> \<Longrightarrow> \<forall>i\<le>n. D (i, i) = \<one> \<Longrightarrow> [curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> V
    \<Longrightarrow> canonical' (f D) \<or> check_diag n (f D)
    "
  assumes diag:
    "check_diag n D \<Longrightarrow> \<forall>i\<le>n. D (i, i) \<le> \<one> \<Longrightarrow> [curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> V
    \<Longrightarrow> check_diag n (f D)
    "
  assumes diag_le:
    "canonical' D \<or> check_diag n D \<Longrightarrow> \<forall>i\<le>n. D (i, i) \<le> \<one> \<Longrightarrow> [curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> V
    \<Longrightarrow> \<forall>i\<le>n. f D (i, i) \<le> \<one>
    "
  assumes V:
    "canonical' D \<Longrightarrow> \<forall>i\<le>n. D (i, i) \<le> \<one> \<Longrightarrow> [curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> V
    \<Longrightarrow> [curry (conv_M (f D))]\<^bsub>v,n\<^esub> \<subseteq> V
    "
  shows "wf_dbm (f D)"
proof -
  from wf_dbm_altD[OF assms(1)] have facts:
    "canonical' D \<or> check_diag n D" "\<forall>i\<le>n. D (i, i) \<le> \<one>" "[curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> V"
    .
  from this(1) consider "canonical' D \<and> \<not> check_diag n D" | "check_diag n D"
    by auto
  then show ?thesis
  proof cases
    assume A: "canonical' D \<and> \<not> check_diag n D"
    with facts(2) have "\<forall>i\<le>n. D (i, i) = \<one>"
      unfolding check_diag_def neutral[symmetric] by fastforce
    with A[THEN conjunct1] show ?thesis
      by (intro wf_dbm_altI[unfolded canonical'_conv_M_iff] canonical diag_le V facts)
  next
    assume "check_diag n D"
    then have "check_diag n (f D)" by (intro disjI2 diag facts)
    then have "[curry (conv_M (f D))]\<^bsub>v,n\<^esub> = {}" by (intro check_diag_conv_M check_diag_empty_spec)
    with \<open>check_diag n (f D)\<close> show ?thesis
      by - (rule wf_dbm_altI[unfolded canonical'_conv_M_iff];
           (intro diag_le diag facts; fail | blast)+)
  qed
qed

definition
  "abstra_repair ac M = repair_pair (abstra_upd ac M) 0 (constraint_clk ac)"

(* XXX Move *)
lemma canonical_subs'_subset:
  "canonical_subs' I' M" if "canonical_subs' I M" "I' \<subseteq> I"
  using that unfolding canonical_subs_def by auto

lemma canonical_subs'_abstra_upd:
  "canonical_subs' (I - {0, constraint_clk ac}) (abstra_upd ac M)" if
  "canonical_subs' I M" "constraint_clk ac > 0"
  using that
  apply (cases ac)
  subgoal for c d
    by (force
        dest: canonical_subs'_upd[of I M "Lt d" c 0] simp: insert_commute min_def
        intro: canonical_subs'_subset
        )
  subgoal for c d
    by (force
        dest: canonical_subs'_upd[of I M "Le d" c 0] simp: insert_commute min_def
        intro: canonical_subs'_subset
        )
    defer
  subgoal for c d
    by (force
        dest: canonical_subs'_upd[of I M "Lt (-d)" 0 c] simp: insert_commute min_def
        intro: canonical_subs'_subset
        )
  subgoal for c d
    by (force
        dest: canonical_subs'_upd[of I M "Le (-d)" 0 c] simp: insert_commute min_def
        intro: canonical_subs'_subset
        )
  subgoal for c d
    apply (auto simp: min_def Let_def)
       apply (force
        dest: canonical_subs'_upd[of I M "Le (-d)" 0 c] simp: insert_commute min_def
        intro: canonical_subs'_subset
        )
      apply (force
        dest: canonical_subs'_upd[of I M "Le d" c 0] simp: insert_commute min_def
        intro: canonical_subs'_subset
        )
    subgoal
      apply (drule canonical_subs'_upd[of I M "Le (-d)" 0 c])
      by simp (metis fun_upd_apply fun_upd_triv gr_implies_not_zero old.prod.inject)
    subgoal
      by (drule canonical_subs'_upd[of I M "Le (-d)" 0 c];
          force dest: canonical_subs'_upd[of _ _ "Le d" c 0])
    done
  done

lemma repair_pair_diag_le:
  "\<forall>i\<le>n. repair_pair M 0 c (i, i) \<le> \<one>" if "\<forall>i\<le>n. M (i, i) \<le> \<one>"
  using that
  unfolding repair_pair_def FWI'_def
  apply clarsimp
  apply (rule order.trans[OF FWI_mono], assumption, assumption)
  apply (rule order.trans[OF FWI_mono], assumption, assumption)
  by simp

lemma wf_dbm_abstra_repair:
  assumes "wf_dbm M" "constraint_clk ac > 0" "constraint_clk ac \<le> n"
  shows "wf_dbm (abstra_repair ac M)"
proof -
  note facts = wf_dbm_altD[OF assms(1)]
  let ?M = "abstra_upd ac M"
  let ?MM = "abstra_repair ac M"
  from assms(2) facts(2) have "\<forall>i\<le>n. ?M (i, i) \<le> \<one>"
    by (auto simp: abstra_upd_diag_preservation)
  then have diag: "\<forall>i\<le>n. ?MM (i, i) \<le> \<one>" unfolding abstra_repair_def by (rule repair_pair_diag_le)
  from assms(2) facts(3) have "[curry (conv_M ?M)]\<^bsub>v,n\<^esub> \<subseteq> V" sorry
  with repair_pair_equiv[of 0 "constraint_clk ac" ?M] assms(3) have V:
    "[curry (conv_M ?MM)]\<^bsub>v,n\<^esub> \<subseteq> V"
    unfolding dbm_equiv_def abstra_repair_def by simp
  from facts(1) have "canonical_diag ?MM"
  proof
    assume "canonical' M"
    from canonical_subs'_abstra_upd[OF this[unfolded canonical_alt_def] assms(2)] show
      "canonical_diag ?MM"
      unfolding abstra_repair_def by (intro repair_pair_canonical_diag_1 assms; simp)
  next
    assume "check_diag n M"
    then have "check_diag n ?M"
      unfolding check_diag_def using assms(2) by (auto simp: abstra_upd_diag_preservation)
    then show "canonical_diag ?MM"
      unfolding abstra_repair_def by (rule repair_pair_canonical_diag_2)
  qed
  with diag V show ?thesis by (intro wf_dbm_altI)
qed

lemma wf_dbm_abstra_repair_equiv:
  assumes "constraint_clk ac \<le> n"
  shows "abstra_repair ac M \<simeq> abstra_upd ac M"
  by (simp add: abstra_repair_def assms dbm_equiv_sym repair_pair_equiv)

lemma abstra_upd_equiv:
  assumes "constraint_clk ac > 0" "constraint_clk ac \<le> n" "M \<simeq> M'"
  shows "abstra_upd ac M \<simeq> abstra_upd ac M'"
    sorry

lemma wf_dbm_abstra_repair_equiv':
  assumes "constraint_clk ac > 0" "constraint_clk ac \<le> n" "M \<simeq> M'"
  shows "abstra_repair ac M \<simeq> abstra_upd ac M'"
  using wf_dbm_abstra_repair_equiv[OF assms(2)] abstra_upd_equiv[OF assms] by blast

definition abstr_repair where
  "abstr_repair = fold (\<lambda> ac M. abstra_repair ac M)"

lemma wf_dbm_abstr_repair_equiv:
  assumes "\<forall> c \<in> constraint_clk ` set cc. c > 0 \<and> c \<le> n" "M \<simeq> M'"
  shows "abstr_repair cc M \<simeq> abstr_upd cc M'"
  using assms unfolding abstr_repair_def abstr_upd_def
  by (induction cc arbitrary: M M') (auto dest!: wf_dbm_abstra_repair_equiv')

lemma wf_dbm_abstr_repair:
  assumes "wf_dbm M" "\<forall> c \<in> constraint_clk ` set cc. c > 0 \<and> c \<le> n"
  shows "wf_dbm (abstr_repair cc M)"
  using assms unfolding abstr_repair_def
  by (induction cc arbitrary: M) (auto intro: wf_dbm_abstra_repair)

lemma wf_dbm_FW'_abstr_upd:
  "wf_dbm (FW' (abstr_upd cc M) n)" if "wf_dbm M" "\<forall> c \<in> constraint_clk ` set cc. c > 0 \<and> c \<le> n"
  apply (rule wf_dbm_rule[OF that(1)])
  subgoal
    unfolding check_diag_def neutral[symmetric] by (rule FW'_canonical)
  subgoal
    unfolding check_diag_def neutral[symmetric]
    using that(2)
    apply safe
    apply (subst (asm) (2) abstr_upd_diag_preservation[symmetric, where M = M and cc = cc])
    by (auto dest: FW'_neg_diag_preservation simp: collect_clks_def)
  subgoal
    apply (drule abstr_upd_diag_preservation'[where cc = cc])
    by (simp add: FW'_diag_preservation collect_clks_def that(2))+
  subgoal
    apply (subst FW'_zone_equiv)
    sorry
  done


lemma n_eq_equiv:
  "[M1]\<^bsub>v,n\<^esub> = [M2]\<^bsub>v,n\<^esub>" if "M1 =\<^sub>n M2"
  using that unfolding DBM_zone_repr_def n_eq_def DBM_val_bounded_def by auto

schematic_goal "[curry (conv_M (up_canonical_upd M1 n))]\<^bsub>v,n\<^esub> = [?M]\<^bsub>v,n\<^esub>"
  thm n_eq_equiv[OF up_canonical_upd_up_canonical']
    oops

lemma up_canonical_upd_V:
  "[curry (up_canonical_upd M n)]\<^bsub>v,n\<^esub> \<subseteq> V" if "canonical' M" "[curry M]\<^bsub>v,n\<^esub> \<subseteq> V"
  apply (subst n_eq_equiv[OF up_canonical_upd_up_canonical'])
  apply (subst up_canonical_equiv_up[OF that(1)])
  apply (subst up_correct)
   apply (rule clock_numbering(1))
    by (rule up_V[OF that(2)])
  thm n_eq_equiv[OF up_canonical_upd_up_canonical']

abbreviation "conv_M' M \<equiv> curry (conv_M M)"

lemma n_eq_transfer[transfer_rule]: "eq_onp (\<lambda>x. x = n) n n"
  by (simp add: eq_onp_def)

lemma RI_up_canonical_upd:
  "RI n (up_canonical_upd Mr n) (up_canonical_upd Mi n)" if "RI n Mr Mi"
  supply [transfer_rule] = that
  by transfer_prover

lemma wf_dbm_up_canonical_upd:
  "wf_dbm (up_canonical_upd M n)" if "wf_dbm M"
  apply (rule wf_dbm_rule[OF that])
  subgoal
    by (intro canonical_diag'_up_canonical_upd disjI1)
  subgoal
    by (simp add: check_diag_def up_canonical_upd_diag_preservation)
  subgoal
    by (simp add: up_canonical_upd_diag_preservation)
  subgoal
    unfolding canonical'_conv_M_iff[symmetric]
    apply (drule up_canonical_upd_V, assumption)
    by (subst (asm) RI_zone_equiv[OF RI_up_canonical_upd[OF RI_conv_M]])
  done

lemma reset_resets_spec:
  "[reset M n i d]\<^bsub>v,n\<^esub> = {u(i := d) |u. u \<in> [M]\<^bsub>v,n\<^esub>}" if "i > 0" "i \<le> n" "0 \<le> d"
proof -
  from that have v_i[simp]: "v i = i" sorry
  show ?thesis
    apply (subst reset_resets[OF _ clock_numbering(1), of i, unfolded v_i])
    using clock_numbering(2) that by fastforce+
qed

lemma reset_V:
  "[reset M n i d]\<^bsub>v,n\<^esub> \<subseteq> V" if "[M]\<^bsub>v,n\<^esub> \<subseteq> V" "i > 0" "i \<le> n" "0 \<le> d"
  apply (subst reset_resets_spec)
  using that unfolding V_def by auto

lemma reset_canonical_n_eq_reset_canonical_upd:
  "reset_canonical (curry M) i d =\<^sub>n curry (reset_canonical_upd M n i d)" if "i > 0"
  using that unfolding n_eq_def by (auto simp: reset_canonical_upd_reset_canonical')

lemma RI_reset_canonical_upd:
  "RI n (reset_canonical_upd Mr n i (real_of_int d)) (reset_canonical_upd Mi n i d)" if
  "RI n Mr Mi" "i \<le> n"
proof -
  have [transfer_rule]: "ri (real_of_int d) d"
    by (simp only: ri_def)
  from that have [transfer_rule]: "eq_onp (\<lambda>x. x < Suc n) i i" by (simp add: eq_onp_def)
  note [transfer_rule] = that(1)
  show ?thesis by transfer_prover
qed

lemma reset_canonical_upd_correct:
  "[curry (reset_canonical_upd D n i d)]\<^bsub>v,n\<^esub> = {u(i := d) |u. u \<in> [curry D]\<^bsub>v,n\<^esub>}" if
  "canonical' D" "i > 0" "i \<le> n" "0 \<le> d"
  apply (subst n_eq_equiv[OF reset_canonical_n_eq_reset_canonical_upd, symmetric])
  defer
   apply (subst reset_reset_canonical[symmetric])
      prefer 5
      apply (subst reset_resets_spec)
  using that clock_numbering(1) by auto

lemma reset_canonical_upd_correct_conv_M:
  "[curry ((map_DBMEntry real_of_int \<circ>\<circ>\<circ> reset_canonical_upd M n) i d)]\<^bsub>v,n\<^esub> =
    {u(i := real_of_int d) |u. u \<in> [curry (conv_M M)]\<^bsub>v,n\<^esub>}"
  if "i > 0" "i \<le> n" "0 \<le> d" "canonical' M"
  apply (subst RI_zone_equiv[OF RI_reset_canonical_upd[OF RI_conv_M], symmetric], rule that)
  apply (subst reset_canonical_upd_correct)
  unfolding canonical'_conv_M_iff using that by auto

lemma wf_dbm_reset_canonical_upd:
  "wf_dbm (reset_canonical_upd M n i d)" if "wf_dbm M" "i > 0" "i \<le> n" "0 \<le> d"
  apply (rule wf_dbm_rule[OF that(1)])
  subgoal
    by (intro reset_canonical_upd_canonical disjI1 that)
  subgoal
    by (metis check_diag_def reset_canonical_upd_diag_preservation that(2))
  subgoal
    by (simp add: reset_canonical_upd_diag_preservation that(2))
  subgoal
    unfolding canonical'_conv_M_iff[symmetric]
    apply (subst RI_zone_equiv[OF RI_reset_canonical_upd[OF RI_conv_M], symmetric], rule that)
    apply (subst reset_canonical_upd_correct)
    using that unfolding V_def by auto
  done

lemma reset_canonical_upd_equiv':
  "reset_canonical_upd D n i d \<simeq> reset_canonical_upd M n i d" if
  "D \<simeq> M" "i > 0" "i \<le> n" "0 \<le> d" "canonical' D" "canonical' M"
  using that unfolding dbm_equiv_def
  apply (subst reset_canonical_upd_correct_conv_M)
      prefer 5
      apply (subst reset_canonical_upd_correct_conv_M)
  by auto

lemma canonical_check_diag_empty_iff:
  "[curry (conv_M D)]\<^bsub>v,n\<^esub> = {} \<longleftrightarrow> check_diag n D" if "canonical_diag' D"
  apply standard
  subgoal
    apply (rule canonical_empty_check_diag)
    using canonical_diagI[OF that] unfolding check_diag_def neutral by auto
  by (intro check_diag_empty_spec check_diag_conv_M)

lemma reset_canonical_upd_equiv:
  "reset_canonical_upd D n i d \<simeq> reset_canonical_upd M n i d" if
  "D \<simeq> M" "i > 0" "i \<le> n" "0 \<le> d" "canonical_diag' D" "canonical_diag' M"
proof -
  have *: "check_diag n D \<longleftrightarrow> check_diag n M"
    using that unfolding dbm_equiv_def
      apply -
    apply (subst canonical_check_diag_empty_iff[symmetric], assumption)
    apply (subst canonical_check_diag_empty_iff[symmetric], assumption)
      by simp
  from that(5) consider "canonical' D" "\<not> check_diag n D" | "check_diag n D"
    by auto
  then show ?thesis
  proof cases
    case 1
    with * that(6) have "canonical' D" "canonical' M"
      by auto
    with that show ?thesis
      by (auto intro: reset_canonical_upd_equiv')
  next
    case 2
    then have "check_diag n D" "check_diag n M" unfolding * by assumption+
    then have
      "check_diag n (reset_canonical_upd D n i d)" "check_diag n (reset_canonical_upd M n i d)"
      by (metis check_diag_def reset_canonical_upd_diag_preservation that(2))+
    then show ?thesis by (auto dest!: check_diag_empty_spec check_diag_conv_M simp: dbm_equiv_def)
  qed
qed

lemma wf_dbm_reset'_upd:
  "wf_dbm (reset'_upd M n cs d)" if "wf_dbm M" "\<forall> i \<in> set cs. i > 0 \<and> i \<le> n" "0 \<le> d"
  using that unfolding reset'_upd_def
  by (induction cs arbitrary: M) (auto intro: wf_dbm_reset_canonical_upd)

lemma reset'_upd_equiv:
  "reset'_upd D n cs d \<simeq> reset'_upd M n cs d" if
  "D \<simeq> M" "\<forall> i \<in> set cs. i > 0 \<and> i \<le> n" "0 \<le> d" "wf_dbm M" "wf_dbm D"
  using that unfolding reset'_upd_def
  apply (induction cs arbitrary: D M)
   apply (simp; fail)
  subgoal premises prems for c cs D M
    apply simp
    apply (rule prems(1))
        apply (rule reset_canonical_upd_equiv)
    using prems(2-)
    by (auto intro: wf_dbm_reset_canonical_upd dest: wf_dbm_altD)
  done


lemma FW'_dbm_equiv':
  "FW' M n \<simeq> M" if "canonical_diag' M"
  by (simp add: FW'_zone_equiv dbm_equiv_def)

lemma FW'_dbm_equiv:
  "FW' M n \<simeq> M" if "wf_dbm M"
  using wf_dbm_altD[OF that] by (intro FW'_dbm_equiv')

definition
  "E_op l r g l' M \<equiv>
    let
      M' = FW' (abstr_upd (inv_of A l) (up_canonical_upd M n)) n;
      M'' = FW' (abstr_upd (inv_of A l') (reset'_upd (FW' (abstr_upd g M') n) n r 0)) n;
      M''' = FW' (norm_upd M'' (k' l') n) n
    in M'''"

lemma E_E_op: "E = (\<lambda> (l, M) (l', M'''). \<exists> g a r. A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<and> M''' = E_op l r g l' M)"
  unfolding E_op_def E_alt_def by simp

context
  fixes f
  assumes op_bisim:
    "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<Longrightarrow> wf_dbm M \<Longrightarrow> f l r g l' M \<simeq> E_op l r g l' M"
    and op_wf:
    "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<Longrightarrow> wf_dbm M \<Longrightarrow> wf_dbm (f l r g l' M)"
begin

definition "E_from_op = (\<lambda> (l, M) (l', M'''). \<exists> g a r. A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<and> M''' = f l r g l' M)"

lemma E_E_from_op_step:
  "E a b \<Longrightarrow> wf_state a \<Longrightarrow> (\<exists> c. E_from_op a c \<and> b \<sim> c)"
  unfolding E_E_op E_from_op_def wf_state_def state_equiv_def
  by (blast intro: op_bisim dbm_equiv_sym)

lemma E_from_op_E_step:
  "E_from_op a b \<Longrightarrow> wf_state a \<Longrightarrow> (\<exists> c. E a c \<and> b \<sim> c)"
  unfolding E_E_op E_from_op_def wf_state_def state_equiv_def by (blast intro: op_bisim)

lemma E_from_op_wf_state:
  "wf_state a \<Longrightarrow> E_from_op a b \<Longrightarrow> wf_state b"
  unfolding E_E_op E_from_op_def wf_state_def state_equiv_def by (blast intro: op_wf)

lemma E_E_from_op_steps_equiv:
  "(\<exists>l' M'. E\<^sup>*\<^sup>* a\<^sub>0 (l', M') \<and> [curry (conv_M M')]\<^bsub>v,n\<^esub> = {}) \<longleftrightarrow>
   (\<exists>l' M'. E_from_op\<^sup>*\<^sup>* a\<^sub>0 (l', M') \<and> [curry (conv_M M')]\<^bsub>v,n\<^esub> = {})"
  by (rule E_E\<^sub>1_steps_equiv[OF E_E_from_op_step E_from_op_E_step E_from_op_wf_state])

end

definition
  "E_op' l r g l' M \<equiv>
    let
      M' = abstr_repair (inv_of A l) (up_canonical_upd M n);
      M'' = abstr_repair (inv_of A l') (reset'_upd (abstr_repair g M') n r 0);
      M''' = FW' (norm_upd M'' (k' l') n) n
    in M'''"

lemma norm_step_dbm_equiv:
  "FW' (norm_upd D (k' l') n) n \<simeq> FW' (norm_upd M (k' l') n) n" if "D \<simeq> M" "wf_dbm D" "wf_dbm M"
  unfolding dbm_equiv_def
  apply (subst norm_step_correct'[OF that(2,3,1)])
  apply (subst norm_step_correct'[OF that(3,3)])
  by auto

lemma E_op'_wf: "wf_dbm (E_op' l r g l' M)" if "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" "wf_dbm M"
proof -
  have "\<forall>c\<in>constraint_clk ` set (inv_of A l). 0 < c \<and> c \<le> n"
    using clock_range collect_clks_inv_clk_set[of A l] unfolding collect_clks_def by blast
  moreover have "\<forall>c\<in>constraint_clk ` set (inv_of A l'). 0 < c \<and> c \<le> n"
    using clock_range collect_clks_inv_clk_set[of A l'] unfolding collect_clks_def by blast
  moreover have "\<forall>c\<in>constraint_clk ` set g. 0 < c \<and> c \<le> n"
    using clock_range collect_clocks_clk_set[OF that(1)] unfolding collect_clks_def by blast
  moreover have "\<forall>i\<in>set r. 0 < i \<and> i \<le> n"
    using clock_range reset_clk_set[OF that(1)] unfolding collect_clks_def by blast
  moreover note side_conds = calculation that(2)
  note wf_intros = norm_step_wf_dbm wf_dbm_abstr_repair wf_dbm_reset'_upd wf_dbm_up_canonical_upd
  show ?thesis unfolding E_op'_def by simp (intro wf_intros side_conds order.refl)
qed

lemma wf_dbm_abstr_repair_equiv_FW:
  assumes "\<forall> c \<in> constraint_clk ` set cc. c > 0 \<and> c \<le> n" "M \<simeq> M'"
  shows "abstr_repair cc M \<simeq> FW' (abstr_upd cc M') n"
  using wf_dbm_abstr_repair_equiv[OF assms] by (simp add: dbm_equiv_def FW'_zone_equiv)

lemma E_op'_bisim:
  "E_op' l r g l' M \<simeq> E_op l r g l' M" if "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" "wf_dbm M"
proof -
  note intros =
    norm_step_dbm_equiv wf_dbm_abstr_repair_equiv_FW[rotated] reset'_upd_equiv dbm_equiv_refl
  have "\<forall>c\<in>constraint_clk ` set (inv_of A l). 0 < c \<and> c \<le> n"
    using clock_range collect_clks_inv_clk_set[of A l] unfolding collect_clks_def by blast
  moreover have "\<forall>c\<in>constraint_clk ` set (inv_of A l'). 0 < c \<and> c \<le> n"
    using clock_range collect_clks_inv_clk_set[of A l'] unfolding collect_clks_def by blast
  moreover have "\<forall>c\<in>constraint_clk ` set g. 0 < c \<and> c \<le> n"
    using clock_range collect_clocks_clk_set[OF that(1)] unfolding collect_clks_def by blast
  moreover have "\<forall>i\<in>set r. 0 < i \<and> i \<le> n"
    using clock_range reset_clk_set[OF that(1)] unfolding collect_clks_def by blast
  moreover note side_conds = calculation that(2)
  note wf_intros =
    norm_step_wf_dbm wf_dbm_abstr_repair wf_dbm_reset'_upd wf_dbm_up_canonical_upd
    wf_dbm_FW'_abstr_upd
  show ?thesis unfolding E_op'_def E_op_def by simp (intro intros wf_intros side_conds order.refl)
qed

lemma E_E_from_op'_steps_equiv:
  "(\<exists>l' M'. E\<^sup>*\<^sup>* a\<^sub>0 (l', M') \<and> [curry (conv_M M')]\<^bsub>v,n\<^esub> = {}) \<longleftrightarrow>
   (\<exists>l' M'. (E_from_op E_op')\<^sup>*\<^sup>* a\<^sub>0 (l', M') \<and> [curry (conv_M M')]\<^bsub>v,n\<^esub> = {})"
  by (intro E_E_from_op_steps_equiv E_op'_wf E_op'_bisim)

end (* End of context for reachability problem*)


text \<open>Graveyard\<close>

context linordered_ab_monoid_add
begin

definition (in -) reorder_mat :: "_ \<Rightarrow> _ mat \<Rightarrow> _ mat" where
  "reorder_mat f M i j = M (inv f i) (inv f j)"

(* XXX Duplication *)
thm FW_canonical_id fw_canonical_id
lemma fw_upd_canonical_subs_id:
  "canonical_subs n {0..k} M \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> k \<le> n \<Longrightarrow> fw_upd M k i j = M"
proof (auto simp: fw_upd_def upd_def less_eq[symmetric] min.coboundedI2 canonical_subs_def, goal_cases)
  case 1
  then have "M i j \<le> M i k + M k j" by auto
  then have "min (M i j) (M i k + M k j) = M i j" by (simp split: split_min)
  thus ?case by force
qed

lemma (in -) fwi_canonical_subs_id:
  "canonical_subs n {0..k} M \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> k \<le> n \<Longrightarrow> fwi M n k i j = M"
  by (rule fwi_canonical_id; auto simp: canonical_subs_def)

thm the_inv_f_f inv_f_f

context
  fixes I :: "nat set" and n :: nat and n' :: nat and M :: "'a mat" and x :: nat
  assumes finite_I: "finite I"
  and canonical: "canonical_subs n I M"
  and n'_def: "n' = card I"
  and n'_le_n: "n' \<le> n"
  and n'_gt_0: "n' > 0"
begin

term bij_betw

lemma bij:
  "\<exists> f. bij_betw f I {0..<n'}"
  sorry

private abbreviation "the_f \<equiv> (SOME f. bij_betw f I {0..<n'})"

thm someI

lemma the_f_bij:
  "bij_betw the_f I {0..<n'}"
  using bij by (auto elim: someI[where P = "\<lambda> f. bij_betw f I {0..<n'}"])

private abbreviation "the_f' \<equiv> \<lambda>i. if i \<in> I then the_f i else i"

term fw_line

lemma f_bound:
  "inv local.the_f' i \<le> n" if "i \<le> n"
  using the_f_bij n'_le_n that unfolding bij_betw_def apply auto
  sorry

lemma f_I:
  "inv local.the_f' i \<in> I" if "i < n'"
  sorry

lemma n'_upt_simp:
  "{0..<n'} = {0..n'-1}"
  using n'_gt_0 by auto

lemma canonical_reordered:
  "canonical_subs n {0..<n'} (reorder_mat the_f' M)"
  unfolding canonical_subs_def
  unfolding reorder_mat_def
  by (auto intro: canonical[unfolded canonical_subs_def, rule_format] dest: f_bound f_I)

lemma aux:
  "fw (reorder_mat local.the_f' M) n (n' - 1) n n = reorder_mat local.the_f' M"
  using canonical_reordered n'_le_n by (auto simp: n'_upt_simp fw_canonical_subs_id)

lemma
  "canonical_subs n {0..n'} (fw_inner n (reorder_mat the_f' M) n')"
  sorry

lemma f_bound':
  "\<exists> i'. inv local.the_f' i' = i \<and> i' \<le> n" if "i \<le> n"
  sorry

lemma f_I':
  "\<exists> i'. inv the_f' i' = i \<and> i' \<in> {0..n'}" if "i \<in> I"
  sorry

lemma x_n':
  "the_f' x = n'"
  sorry

lemma x_n'_inv:
  "inv the_f' n' = x"
  sorry


end (* End of anonymous context for fixed index set *)

end (* End of class context *)

end (* End of theory *)
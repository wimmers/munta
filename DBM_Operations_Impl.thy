theory DBM_Operations_Impl
  imports DBM_Operations Normalized_Zone_Semantics
          "IICF/IICF"

begin

section \<open>Misc\<close>

lemma fold_last:
  "fold f (xs @ [x]) a = f x (fold f xs a)"
by simp

section \<open>Reset\<close>

definition
  "reset_canonical M k d =
    (\<lambda> i j. if i = k \<and> j = 0 then Le d
        else if i = 0 \<and> j = k then Le (-d)
        else if i = k \<and> j \<noteq> k then Le d + M 0 j
        else if i \<noteq> k \<and> j = k then Le (-d) + M i 0
        else M i j
    )"

(* XXX However, DBM entries are NOT a member of this typeclass *)
lemma canonical_is_cyc_free:
  fixes M :: "nat \<Rightarrow> nat \<Rightarrow> ('b :: {linordered_cancel_ab_semigroup_add, linordered_ab_monoid_add})"
  assumes "canonical M n"
  shows "cyc_free M n"
proof (cases "\<forall> i \<le> n. 0 \<le> M i i")
  case True
  with assms show ?thesis by (rule canonical_cyc_free)
next
  case False
  then obtain i where "i \<le> n" "M i i < 0" by auto
  then have "M i i + M i i < M i i" using add_strict_left_mono by fastforce
  with \<open>i \<le> n\<close> assms show ?thesis by fastforce
qed

lemma dbm_neg_add:
  fixes a :: "('t :: time) DBMEntry"
  assumes "a < 0"
  shows "a + a < 0"
using assms unfolding neutral add less
by (cases a) auto

instance linordered_ab_group_add \<subseteq> linordered_cancel_ab_monoid_add by standard auto

lemma Le_cancel_1[simp]:
  fixes d :: "'c :: linordered_ab_group_add"
  shows "Le d + Le (-d) = Le 0"
unfolding add by simp

lemma Le_cancel_2[simp]:
  fixes d :: "'c :: linordered_ab_group_add"
  shows "Le (-d) + Le d = Le 0"
unfolding add by simp

lemma reset_canonical_canonical':
  "canonical (reset_canonical M k (d :: 'c :: linordered_ab_group_add)) n"
  if "M 0 0 = 0" "M k k = 0" "canonical M n" "k > 0" for k n :: nat
proof -
  have add_mono_neutr': "a \<le> a + b" if "b \<ge> Le (0 :: 'c)" for a b
    using that unfolding neutral[symmetric] by (simp add: add_increasing2)
  have add_mono_neutl': "a \<le> b + a" if "b \<ge> Le (0 :: 'c)" for a b
    using that unfolding neutral[symmetric] by (simp add: add_increasing)
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
             apply (simp add: add.assoc[symmetric] add_mono_neutl' add_mono_neutr'; fail)
            apply (simp add: add.assoc[symmetric] add_mono_neutl' add_mono_neutr' comm; fail)
           apply (simp add: add.assoc[symmetric] add_mono_neutl' add_mono_neutr'; fail)
    subgoal premises prems for i j k
    proof -
      from prems have "M i k \<le> M i 0 + M 0 k"
        by auto
      also have "\<dots> \<le> Le (- d) + M i 0 + (Le d + M 0 k)"
        apply (simp add: add.assoc[symmetric], simp add: comm, simp add: add.assoc[symmetric])
        using prems(1) that(1) by auto
      finally show ?thesis .
    qed
    subgoal premises prems for i j k
    proof -
      from prems have "Le 0 \<le> M 0 j + M j 0"
        by force
      also have "\<dots> \<le> Le d + M 0 j + (Le (- d) + M j 0)"
        apply (simp add: add.assoc[symmetric], simp add: comm, simp add: add.assoc[symmetric])
        using prems(1) that(1) by (auto simp: add.commute)
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
        by (simp add: add_left_mono add.assoc)
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

lemma reset_canonical_canonical:
  "canonical (reset_canonical M k (d :: 'c :: linordered_ab_group_add)) n"
  if "\<forall> i \<le> n. M i i = 0" "canonical M n" "k > 0" for k n :: nat
proof -
  have add_mono_neutr': "a \<le> a + b" if "b \<ge> Le (0 :: 'c)" for a b
    using that unfolding neutral[symmetric] by (simp add: add_increasing2)
  have add_mono_neutl': "a \<le> b + a" if "b \<ge> Le (0 :: 'c)" for a b
    using that unfolding neutral[symmetric] by (simp add: add_increasing)
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
             apply (simp add: add.assoc[symmetric] add_mono_neutl' add_mono_neutr'; fail)
            apply (simp add: add.assoc[symmetric] add_mono_neutl' add_mono_neutr' comm; fail)
           apply (simp add: add.assoc[symmetric] add_mono_neutl' add_mono_neutr'; fail)
    subgoal premises prems for i j k
    proof -
      from prems have "M i k \<le> M i 0 + M 0 k"
        by auto
      also have "\<dots> \<le> Le (- d) + M i 0 + (Le d + M 0 k)"
        apply (simp add: add.assoc[symmetric], simp add: comm, simp add: add.assoc[symmetric])
        using prems(1) that(1) by (auto simp: add.commute)
      finally show ?thesis .
    qed
    subgoal premises prems for i j k
    proof -
      from prems have "Le 0 \<le> M 0 j + M j 0"
        by force
      also have "\<dots> \<le> Le d + M 0 j + (Le (- d) + M j 0)"
        apply (simp add: add.assoc[symmetric], simp add: comm, simp add: add.assoc[symmetric])
        using prems(1) that(1) by (auto simp: add.commute)
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
        by (simp add: add_left_mono add.assoc)
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


lemma canonicalD[simp]:
  assumes "canonical M n" "i \<le> n" "j \<le> n" "k \<le> n"
  shows "min (dbm_add (M i k) (M k j)) (M i j) = M i j"
using assms unfolding add[symmetric] min_def by fastforce

lemma reset_reset_canonical:
  assumes "canonical M n" "k > 0" "k \<le> n" "clock_numbering v"
  shows "[reset M n k d]\<^bsub>v,n\<^esub> = [reset_canonical M k d]\<^bsub>v,n\<^esub>"
proof safe
  fix u assume "u \<in> [reset M n k d]\<^bsub>v,n\<^esub>"
  show "u \<in> [reset_canonical M k d]\<^bsub>v,n\<^esub>"
  unfolding DBM_zone_repr_def DBM_val_bounded_def
  proof (safe, goal_cases)
    case 1
    with \<open>u \<in> _\<close> have
      "Le 0 \<le> reset M n k d 0 0"
    unfolding DBM_zone_repr_def DBM_val_bounded_def less_eq by auto
    also have "\<dots> = M 0 0" unfolding reset_def using assms by auto
    finally show ?case unfolding less_eq reset_canonical_def using \<open>k > 0\<close> by auto
  next
    case (2 c)
    from \<open>clock_numbering _\<close> have "v c > 0" by auto
    show ?case
    proof (cases "v c = k")
      case True
      with \<open>v c > 0\<close> \<open>u \<in> _\<close> \<open>v c \<le> n\<close> show ?thesis
      unfolding reset_canonical_def DBM_zone_repr_def DBM_val_bounded_def reset_def by auto
    next
      case False
      show ?thesis
      proof (cases "v c = k")
        case True
        with \<open>v c > 0\<close> \<open>u \<in> _\<close> \<open>v c \<le> n\<close> \<open>k > 0\<close> show ?thesis
        unfolding reset_canonical_def DBM_zone_repr_def DBM_val_bounded_def reset_def
        by auto
      next
        case False
        with \<open>v c > 0\<close> \<open>k > 0\<close> \<open>v c \<le> n\<close> \<open>k \<le> n\<close> \<open>canonical _ _\<close> \<open>u \<in> _\<close> have
          "dbm_entry_val u None (Some c) (M 0 (v c))"
        unfolding DBM_zone_repr_def DBM_val_bounded_def reset_def by auto
        with False \<open>k > 0\<close> show ?thesis unfolding reset_canonical_def by auto
      qed
    qed
  next
    case (3 c)
    from \<open>clock_numbering _\<close> have "v c > 0" by auto
    show ?case
    proof (cases "v c = k")
      case True
      with \<open>v c > 0\<close> \<open>u \<in> _\<close> \<open>v c \<le> n\<close> show ?thesis
      unfolding reset_canonical_def DBM_zone_repr_def DBM_val_bounded_def reset_def by auto
    next
      case False
      show ?thesis
      proof (cases "v c = k")
        case True
        with \<open>v c > 0\<close> \<open>u \<in> _\<close> \<open>v c \<le> n\<close> \<open>k > 0\<close> show ?thesis
        unfolding reset_canonical_def DBM_zone_repr_def DBM_val_bounded_def reset_def
        by auto
      next
        case False
        with \<open>v c > 0\<close> \<open>k > 0\<close> \<open>v c \<le> n\<close> \<open>k \<le> n\<close> \<open>canonical _ _\<close> \<open>u \<in> _\<close> have
          "dbm_entry_val u (Some c) None (M (v c) 0)"
        unfolding DBM_zone_repr_def DBM_val_bounded_def reset_def by auto
        with False \<open>k > 0\<close> show ?thesis unfolding reset_canonical_def by auto
      qed
    qed
  next
    case (4 c1 c2)
    from \<open>clock_numbering _\<close> have "v c1 > 0" "v c2 > 0" by auto
    show ?case
    proof (cases "v c1 = k")
      case True
      show ?thesis
      proof (cases "v c2 = k")
        case True
        with \<open>v c1 = k\<close> \<open>v c1 > 0\<close> \<open>v c2 > 0\<close> \<open>u \<in> _\<close> \<open>v c1 \<le> n\<close> \<open>v c2 \<le> n\<close> \<open>canonical _ _\<close>
        have "reset_canonical M k d (v c1) (v c2) = M k k"
        unfolding reset_canonical_def by auto
        moreover from True \<open>v c1 = k\<close> \<open>v c1 > 0\<close> \<open>v c2 > 0\<close> \<open>v c1 \<le> n\<close> \<open>v c2 \<le> n\<close>
        have "reset M n k d (v c1) (v c2) = M k k" unfolding reset_def by auto
        moreover from \<open>u \<in> _\<close> \<open>v c1 = k\<close> \<open>v c2 = k\<close> \<open>k \<le> n\<close> have
          "dbm_entry_val u (Some c1) (Some c2) (reset M n k d k k)"
        unfolding DBM_zone_repr_def DBM_val_bounded_def by auto metis
        ultimately show ?thesis using \<open>v c1 = k\<close> \<open>v c2 = k\<close> by auto
      next
        case False
        with \<open>v c1 = k\<close> \<open>v c1 > 0\<close> \<open>k > 0\<close> \<open>v c1 \<le> n\<close> \<open>k \<le> n\<close> \<open>canonical _ _\<close> \<open>u \<in> _\<close> have
          "dbm_entry_val u (Some c1) None (Le d)"
        unfolding DBM_zone_repr_def DBM_val_bounded_def reset_def by auto
        moreover from \<open>v c2 \<noteq> k\<close> \<open>k > 0\<close> \<open>v c2 \<le> n\<close> \<open>k \<le> n\<close> \<open>canonical _ _\<close> \<open>u \<in> _\<close> have
          "dbm_entry_val u None (Some c2) (M 0 (v c2))"
        unfolding DBM_zone_repr_def DBM_val_bounded_def reset_def by auto
        ultimately show ?thesis using False \<open>k > 0\<close> \<open>v c1 = k\<close> \<open>v c2 > 0\<close>
        unfolding reset_canonical_def add by (auto intro: dbm_entry_val_add_4)
      qed
    next
      case False
      show ?thesis
      proof (cases "v c2 = k")
        case True
        from \<open>v c1 \<noteq> k\<close> \<open>v c1 > 0\<close> \<open>k > 0\<close> \<open>v c1 \<le> n\<close> \<open>k \<le> n\<close> \<open>canonical _ _\<close> \<open>u \<in> _\<close> have
          "dbm_entry_val u (Some c1) None (M (v c1) 0)"
        unfolding DBM_zone_repr_def DBM_val_bounded_def reset_def by auto
        moreover from \<open>v c2 = k\<close> \<open>k > 0\<close> \<open>v c2 \<le> n\<close> \<open>k \<le> n\<close> \<open>canonical _ _\<close> \<open>u \<in> _\<close> have
          "dbm_entry_val u None (Some c2) (Le (-d))"
        unfolding DBM_zone_repr_def DBM_val_bounded_def reset_def by auto
        ultimately show ?thesis using False \<open>k > 0\<close> \<open>v c2 = k\<close> \<open>v c1 > 0\<close> \<open>v c2 > 0\<close>
        unfolding reset_canonical_def
          apply simp
          apply (subst add.commute)
        by (auto intro: dbm_entry_val_add_4[folded add])
      next
        case False
        from \<open>u \<in> _\<close> \<open>v c1 \<le> n\<close> \<open>v c2 \<le> n\<close> have
          "dbm_entry_val u (Some c1) (Some c2) (reset M n k d (v c1) (v c2))"
        unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
        with \<open>v c1 \<noteq> k\<close> \<open>v c2 \<noteq> k\<close> \<open>v c1 \<le> n\<close> \<open>v c2 \<le> n\<close> \<open>k \<le> n\<close> \<open>canonical _ _\<close> have
          "dbm_entry_val u (Some c1) (Some c2) (M (v c1) (v c2))"
        unfolding DBM_zone_repr_def DBM_val_bounded_def reset_def by auto
        with \<open>v c1 \<noteq> k\<close> \<open>v c2 \<noteq> k\<close> show ?thesis unfolding reset_canonical_def by auto
      qed
    qed
  qed
next
  fix u assume "u \<in> [reset_canonical M k d]\<^bsub>v,n\<^esub>"
  note unfolds = DBM_zone_repr_def DBM_val_bounded_def reset_canonical_def
  show "u \<in> [reset M n k d]\<^bsub>v,n\<^esub>"
  unfolding DBM_zone_repr_def DBM_val_bounded_def
  proof (safe, goal_cases)
    case 1
    with \<open>u \<in> _\<close> have
      "Le 0 \<le> reset_canonical M k d 0 0"
    unfolding DBM_zone_repr_def DBM_val_bounded_def less_eq by auto
    also have "\<dots> = M 0 0" unfolding reset_canonical_def using assms by auto
    finally show ?case unfolding less_eq reset_def using \<open>k > 0\<close> \<open>k \<le> n\<close> \<open>canonical _ _\<close> by auto
  next
    case (2 c)
    with assms have "v c > 0" by auto
    note A = this assms(1-3) \<open>v c \<le> n\<close>
    show ?case
    proof (cases "v c = k")
      case True
      with A \<open>u \<in> _\<close> show ?thesis unfolding reset_def unfolds by auto
    next
      case False
      with A \<open>u \<in> _\<close> show ?thesis unfolding unfolds reset_def by auto
    qed
  next
    case (3 c)
    with assms have "v c > 0" by auto
    note A = this assms(1-3) \<open>v c \<le> n\<close>
    show ?case
    proof (cases "v c = k")
      case True
      with A \<open>u \<in> _\<close> show ?thesis unfolding reset_def unfolds by auto
    next
      case False
      with A \<open>u \<in> _\<close> show ?thesis unfolding unfolds reset_def by auto
    qed
  next
    case (4 c1 c2)
    with assms have "v c1 > 0" "v c2 > 0" by auto
    note A = this assms(1-3) \<open>v c1 \<le> n\<close> \<open>v c2 \<le> n\<close>
    show ?case
    proof (cases "v c1 = k")
      case True
      show ?thesis
      proof (cases "v c2 = k")
        case True
        with \<open>u \<in> _\<close> A \<open>v c1 = k\<close> have
          "dbm_entry_val u (Some c1) (Some c2) (reset_canonical M k d k k)"
        unfolding DBM_zone_repr_def DBM_val_bounded_def by auto metis
        with A \<open>v c1 = k\<close> have
          "dbm_entry_val u (Some c1) (Some c2) (M k k)"
        unfolding reset_canonical_def by auto
        with A \<open>v c1 = k\<close> show ?thesis unfolding reset_def unfolds by auto
      next
        case False
        with A \<open>v c1 = k\<close> show ?thesis unfolding reset_def unfolds by auto
      qed
    next
      case False
      show ?thesis
      proof (cases "v c2 = k")
        case False
        with \<open>u \<in> _\<close> A \<open>v c1 \<noteq> k\<close> have
          "dbm_entry_val u (Some c1) (Some c2) (reset_canonical M k d (v c1) (v c2))"
        unfolding DBM_zone_repr_def DBM_val_bounded_def by auto
        with A \<open>v c1 \<noteq> k\<close> \<open>v c2 \<noteq> k\<close> have
          "dbm_entry_val u (Some c1) (Some c2) (M (v c1) (v c2))"
        unfolding reset_canonical_def by auto
        with A \<open>v c1 \<noteq> k\<close> show ?thesis unfolding reset_def unfolds by auto
      next
        case True
        with A \<open>v c1 \<noteq> k\<close> show ?thesis unfolding reset_def unfolds by auto
      qed
    qed
  qed
qed

lemma reset_canonical_diag_preservation:
  fixes k :: nat
  assumes "k > 0"
  shows "\<forall> i \<le> n. (reset_canonical M k d) i i = M i i"
using assms unfolding reset_canonical_def by auto

definition reset'' where
  "reset'' M n cs v d = fold (\<lambda> c M. reset_canonical M (v c) d) cs M"

lemma reset''_diag_preservation:
  assumes "clock_numbering v"
  shows "\<forall> i \<le> n. (reset'' M n cs v d) i i = M i i"
using assms
 apply (induction cs arbitrary: M)
 unfolding reset''_def apply auto
using reset_canonical_diag_preservation by blast

lemma reset_resets:
  assumes "\<forall>k\<le>n. k > 0 \<longrightarrow> (\<exists>c. v c = k)" "clock_numbering' v n" "v c \<le> n"
  shows "[reset M n (v c) d]\<^bsub>v,n\<^esub> = {u(c := d) | u. u \<in> [M]\<^bsub>v,n\<^esub>}"
proof safe
  fix u assume u: "u \<in> [reset M n (v c) d]\<^bsub>v,n\<^esub>"
  with assms have
    "u c = d"
  by (auto intro: DBM_reset_sound2[OF _ DBM_reset_reset] simp: DBM_zone_repr_def)
  moreover from DBM_reset_sound[OF assms u] obtain d' where
    "u(c := d') \<in> [M]\<^bsub>v,n\<^esub>" (is "?u \<in> _")
  by auto
  ultimately have "u = ?u(c := d)" by auto
  with \<open>?u \<in> _\<close> show "\<exists>u'. u = u'(c := d) \<and> u' \<in> [M]\<^bsub>v,n\<^esub>" by blast
next
  fix u assume u: "u \<in> [M]\<^bsub>v,n\<^esub>"
  with DBM_reset_complete[OF assms(2,3) DBM_reset_reset] assms
  show "u(c := d) \<in> [reset M n (v c) d]\<^bsub>v,n\<^esub>" unfolding DBM_zone_repr_def by auto
qed

lemma reset_eq':
  assumes prems: "\<forall>k\<le>n. k > 0 \<longrightarrow> (\<exists>c. v c = k)" "clock_numbering' v n" "v c \<le> n"
      and eq: "[M]\<^bsub>v,n\<^esub> = [M']\<^bsub>v,n\<^esub>"
  shows "[reset M n (v c) d]\<^bsub>v,n\<^esub> = [reset M' n (v c) d]\<^bsub>v,n\<^esub>"
using reset_resets[OF prems] eq by blast

lemma reset_eq:
  assumes prems: "\<forall>k\<le>n. k > 0 \<longrightarrow> (\<exists>c. v c = k)" "clock_numbering' v n"
      and k:  "k > 0" "k \<le> n"
      and eq: "[M]\<^bsub>v,n\<^esub> = [M']\<^bsub>v,n\<^esub>"
  shows "[reset M n k d]\<^bsub>v,n\<^esub> = [reset M' n k d]\<^bsub>v,n\<^esub>"
using reset_eq'[OF prems _ eq] prems(1) k by blast

lemma FW_reset_commute:
  assumes prems: "\<forall>k\<le>n. k > 0 \<longrightarrow> (\<exists>c. v c = k)" "clock_numbering' v n" "k > 0" "k \<le> n"
  shows "[FW (reset M n k d) n]\<^bsub>v,n\<^esub> = [reset (FW M n) n k d]\<^bsub>v,n\<^esub>"
using reset_eq[OF prems] FW_zone_equiv[OF prems(1)] by blast

lemma reset_canonical_diag_presv:
  fixes k :: nat
  assumes "M i i = Le 0" "k > 0"
  shows "(reset_canonical M k d) i i = Le 0"
unfolding reset_canonical_def using assms by auto

lemma reset_cycle_free:
  fixes M :: "('t :: time) DBM"
  assumes "cycle_free M n"
      and prems: "\<forall>k\<le>n. k > 0 \<longrightarrow> (\<exists>c. v c = k)" "clock_numbering' v n" "k > 0" "k \<le> n"
  shows "cycle_free (reset M n k d) n"
proof -
  from assms cyc_free_not_empty cycle_free_diag_equiv have "[M]\<^bsub>v,n\<^esub> \<noteq> {}" by metis
  with reset_resets[OF prems(1,2)] prems(1,3,4) have "[reset M n k d]\<^bsub>v,n\<^esub> \<noteq> {}" by fast
  with not_empty_cyc_free[OF prems(1)] cycle_free_diag_equiv show ?thesis by metis
qed

lemma reset'_reset''_equiv:
  assumes "canonical M n" "d \<ge> 0" "\<forall>i \<le> n. M i i = 0"
          "clock_numbering' v n" "\<forall> c \<in> set cs. v c \<le> n"
      and surj: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
  shows "[reset' M n cs v d]\<^bsub>v,n\<^esub> = [reset'' M n cs v d]\<^bsub>v,n\<^esub>"
proof -
  from assms(3,4,5) surj have
    "\<forall>i \<le> n. M i i \<ge> 0" "M 0 0 = Le 0" "\<forall> c \<in> set cs. M (v c) (v c) = Le 0"
  unfolding neutral by auto
  note assms = assms(1,2) this assms(4-)
  from \<open>clock_numbering' v n\<close> have "clock_numbering v" by auto
  from canonical_cyc_free assms(1,3) cycle_free_diag_equiv have "cycle_free M n" by metis
  have "reset' M n cs v d = foldr (\<lambda> c M. reset M n (v c) d) cs M" by (induction cs) auto
  then have
    "[FW (reset' M n cs v d) n]\<^bsub>v,n\<^esub> = [FW (foldr (\<lambda> c M. reset M n (v c) d) cs M) n]\<^bsub>v,n\<^esub>"
  by simp
  also have "\<dots> = [foldr (\<lambda>c M. reset_canonical M (v c) d) cs M]\<^bsub>v,n\<^esub>"
  using assms
   apply (induction cs)
   apply (simp add: FW_canonical_id; fail)
   apply simp
   subgoal premises prems for a cs
   proof -
     let ?l = "FW (reset (foldr (\<lambda>c M. reset M n (v c) d) cs M) n (v a) d) n"
     let ?m = "reset (foldr (\<lambda>c M. reset_canonical M (v c) d) cs M) n (v a) d"
     let ?r = "reset_canonical (foldr (\<lambda>c M. reset_canonical M (v c) d) cs M) (v a) d"
     have "foldr (\<lambda>c M. reset_canonical M (v c) d) cs M 0 0 = Le 0"
       apply (induction cs)
       using prems by (force intro: reset_canonical_diag_presv)+
     from prems(6) have "canonical (foldr (\<lambda>c M. reset_canonical M (v c) d) cs M) n"
       apply (induction cs)
       using \<open>canonical M n\<close> apply simp
       apply simp
       apply (rule reset_canonical_canonical'[unfolded neutral])
       using assms apply simp
       subgoal premises - for a cs
         apply (induction cs)
         using assms(4) \<open>clock_numbering v\<close> by (force intro: reset_canonical_diag_presv)+
       subgoal premises prems for a cs
         apply (induction cs)
         using prems \<open>clock_numbering v\<close> by (force intro: reset_canonical_diag_presv)+
        apply (simp; fail)
       using \<open>clock_numbering v\<close> by metis
     have "[FW (reset (foldr (\<lambda>c M. reset M n (v c) d) cs M) n (v a) d) n]\<^bsub>v,n\<^esub>
     = [reset (FW (foldr (\<lambda>c M. reset M n (v c) d) cs M) n) n (v a) d]\<^bsub>v,n\<^esub>"
       using assms(8-) prems(7-) by - (rule FW_reset_commute; auto)
     also from prems have "\<dots> = [?m]\<^bsub>v,n\<^esub>" by - (rule reset_eq; auto)
     also from \<open>canonical (foldr _ _ _) n\<close> prems have
       "\<dots> = [?r]\<^bsub>v,n\<^esub>"
       by - (rule reset_reset_canonical; simp)
     finally show ?thesis .
   qed
  done
  also have "\<dots> = [reset'' M n cs v d]\<^bsub>v,n\<^esub>" unfolding reset''_def thm arg_cong
   apply (rule arg_cong[where f = "\<lambda> M. [M]\<^bsub>v,n\<^esub>"])
   apply (rule fun_cong[where x = M])
   apply (rule foldr_fold)
   apply (rule ext)
   apply simp
   subgoal for x y M
   proof -
     from \<open>clock_numbering v\<close> have "v x > 0" "v y > 0" by auto
     show ?thesis
     proof (cases "v x = v y")
       case True
       then show ?thesis unfolding reset_canonical_def by force
     next
       case False
       with \<open>v x > 0\<close> \<open>v y > 0\<close> show ?thesis unfolding reset_canonical_def by fastforce
     qed
   qed
  done
  finally show ?thesis using FW_zone_equiv[OF surj] by metis
qed

text \<open>Eliminating the clock_numbering\<close>

definition reset''' where
  "reset''' M n cs d = fold (\<lambda> c M. reset_canonical M c d) cs M"

lemma reset''_reset''':
  assumes "\<forall> c \<in> set cs. v c = c"
  shows "reset'' M n cs v d = reset''' M n cs d"
using assms
 apply (induction cs arbitrary: M)
unfolding reset''_def reset'''_def by simp+

type_synonym 'a DBM' = "nat \<times> nat \<Rightarrow> 'a DBMEntry"

definition
  "reset_canonical_upd
    (M :: ('a :: {linordered_cancel_ab_monoid_add,uminus}) DBM') (n:: nat) (k:: nat) d =
      fold (\<lambda> i M. if i = k then M else M((k, i) := Le d + M(0,i), (i, k) := Le (-d) + M(i, 0)))
        (* [1..<n+1] *) (map nat [1..n])
        (M((k, 0) := Le d, (0, k) := Le (-d)))
  "

lemma one_upto_Suc:
  "[1..<Suc i + 1] = [1..<i+1] @ [Suc i]"
by (simp add: )

lemma one_upto_Suc':
  "[1..Suc i] = [1..i] @ [Suc i]"
by (simp add: upto_rec2)

lemma one_upto_Suc'':
  "[1..1 + int i] = [1..i] @ [Suc i]"
by (simp add: upto_rec2)

lemma reset_canonical_upd_diag_id:
  fixes k n :: nat
  assumes "k > 0"
  shows "(reset_canonical_upd M n k d) (k, k) = M (k, k)"
unfolding reset_canonical_upd_def using assms by (induction n) (auto simp: upto_rec2)

lemma reset_canonical_upd_out_of_bounds_id1:
  fixes i j k n :: nat
  assumes "i \<noteq> k" "i > n"
  shows "(reset_canonical_upd M n k d) (i, j) = M (i, j)"
using assms by (induction n) (auto simp add: reset_canonical_upd_def upto_rec2)

lemma reset_canonical_upd_out_of_bounds_id2:
  fixes i j k n :: nat
  assumes "j \<noteq> k" "j > n"
  shows "(reset_canonical_upd M n k d) (i, j) = M (i, j)"
using assms by (induction n) (auto simp add: reset_canonical_upd_def upto_rec2)

lemma reset_canonical_upd_out_of_bounds1:
  fixes i j k n :: nat
  assumes "k \<le> n" "i > n"
  shows "(reset_canonical_upd M n k d) (i, j) = M (i, j)"
using assms reset_canonical_upd_out_of_bounds_id1 by (metis not_le)

lemma reset_canonical_upd_out_of_bounds2:
  fixes i j k n :: nat
  assumes "k \<le> n" "j > n"
  shows "(reset_canonical_upd M n k d) (i, j) = M (i, j)"
using assms reset_canonical_upd_out_of_bounds_id2 by (metis not_le)

lemma reset_canonical_upd_id1:
  fixes k n :: nat
  assumes "k > 0" "i > 0" "i \<le> n" "i \<noteq> k"
  shows "(reset_canonical_upd M n k d) (i, k) = Le (-d) + M(i,0)"
using assms apply (induction n)
apply (simp add: reset_canonical_upd_def; fail)
subgoal for n
  apply (simp add: reset_canonical_upd_def)
  apply (subst one_upto_Suc'')
  using reset_canonical_upd_out_of_bounds_id1[unfolded reset_canonical_upd_def, where j = 0 and M = M]
by fastforce
done

lemma reset_canonical_upd_id2:
  fixes k n :: nat
  assumes "k > 0" "i > 0" "i \<le> n" "i \<noteq> k"
  shows "(reset_canonical_upd M n k d) (k, i) = Le d + M(0,i)"
unfolding reset_canonical_upd_def using assms apply (induction n)
apply (simp add: upto_rec2; fail)
subgoal for n
  apply (simp add: one_upto_Suc'')
  using reset_canonical_upd_out_of_bounds_id2[unfolded reset_canonical_upd_def, where i = 0 and M = M]
by fastforce
done

lemma reset_canonical_updid_0_1:
  fixes n :: nat
  assumes "k > 0"
  shows "(reset_canonical_upd M n k d) (0, k) = Le (-d)"
using assms by (induction n) (auto simp add: reset_canonical_upd_def upto_rec2)

lemma reset_canonical_updid_0_2:
  fixes n :: nat
  assumes "k > 0"
  shows "(reset_canonical_upd M n k d) (k, 0) = Le d"
using assms by (induction n) (auto simp add: reset_canonical_upd_def upto_rec2)

lemma reset_canonical_upd_id:
  fixes n :: nat
  assumes "i \<noteq> k" "j \<noteq> k"
  shows "(reset_canonical_upd M n k d) (i,j) = M (i,j)"
using assms by (induction n; simp add: reset_canonical_upd_def upto_rec2)

lemma reset_canonical_upd_reset_canonical:
  fixes i j k n :: nat and M :: "nat \<times> nat \<Rightarrow> ('a :: {linordered_cancel_ab_monoid_add,uminus}) DBMEntry"
  assumes "k > 0" "i \<le> n" "j \<le> n" "\<forall> i \<le> n. \<forall> j \<le> n. M (i, j) = M' i j"
  shows "(reset_canonical_upd M n k d)(i,j) = (reset_canonical M' k d) i j" (is "?M(i,j) = _")
proof (cases "i = k")
  case True
  show ?thesis
  proof (cases "j = k")
    case True
    with \<open>i = k\<close> assms reset_canonical_upd_diag_id[where M = M] show ?thesis
    by (auto simp: reset_canonical_def)
  next
    case False
    show ?thesis
    proof (cases "j = 0")
      case False
      with \<open>i = k\<close> \<open>j \<noteq> k\<close> assms have
        "?M (i,j) = Le d + M(0,j)"
      using reset_canonical_upd_id2[where M = M] by fastforce
      with \<open>i = k\<close> \<open>j \<noteq> k\<close> \<open>j \<noteq> 0\<close> assms show ?thesis unfolding reset_canonical_def by auto
    next
      case True
      with \<open>i = k\<close> \<open>k > 0\<close> show ?thesis by (simp add: reset_canonical_updid_0_2 reset_canonical_def)
    qed
  qed
next
  case False
  show ?thesis
  proof (cases "j = k")
    case True
    show ?thesis
    proof (cases "i = 0")
      case False
      with \<open>j = k\<close> \<open>i \<noteq> k\<close>assms have
        "?M (i,j) = Le (-d) + M(i,0)"
      using reset_canonical_upd_id1[where M = M] by fastforce
      with \<open>j = k\<close> \<open>i \<noteq> k\<close> \<open>i \<noteq> 0\<close> assms show ?thesis unfolding reset_canonical_def by force
    next
      case True
      with \<open>j = k\<close> \<open>k > 0\<close> show ?thesis by (simp add: reset_canonical_updid_0_1 reset_canonical_def)
    qed
  next
    case False
    with \<open>i \<noteq> k\<close> assms show ?thesis by (simp add: reset_canonical_upd_id reset_canonical_def)
  qed
qed

lemma reset_canonical_upd_reset_canonical':
  fixes i j k n :: nat
  assumes "k > 0" "i \<le> n" "j \<le> n"
  shows "(reset_canonical_upd M n k d)(i,j) = (reset_canonical (curry M) k d) i j" (is "?M(i,j) = _")
proof (cases "i = k")
  case True
  show ?thesis
  proof (cases "j = k")
    case True
    with \<open>i = k\<close> assms reset_canonical_upd_diag_id show ?thesis by (auto simp add: reset_canonical_def)
  next
    case False
    show ?thesis
    proof (cases "j = 0")
      case False
      with \<open>i = k\<close> \<open>j \<noteq> k\<close> assms have
        "?M (i,j) = Le d + M(0,j)"
      using reset_canonical_upd_id2[where M = M] by fastforce
      with \<open>i = k\<close> \<open>j \<noteq> k\<close> \<open>j \<noteq> 0\<close> show ?thesis unfolding reset_canonical_def by simp
    next
      case True
      with \<open>i = k\<close> \<open>k > 0\<close> show ?thesis by (simp add: reset_canonical_updid_0_2 reset_canonical_def)
    qed
  qed
next
  case False
  show ?thesis
  proof (cases "j = k")
    case True
    show ?thesis
    proof (cases "i = 0")
      case False
      with \<open>j = k\<close> \<open>i \<noteq> k\<close>assms have
        "?M (i,j) = Le (-d) + M(i,0)"
      using reset_canonical_upd_id1[where M = M] by fastforce
      with \<open>j = k\<close> \<open>i \<noteq> k\<close> \<open>i \<noteq> 0\<close> show ?thesis unfolding reset_canonical_def by simp
    next
      case True
      with \<open>j = k\<close> \<open>k > 0\<close> show ?thesis by (simp add: reset_canonical_updid_0_1 reset_canonical_def)
    qed
  next
    case False
    with \<open>i \<noteq> k\<close> show ?thesis by (simp add: reset_canonical_upd_id reset_canonical_def)
  qed
qed

lemma reset_canonical_upd_canonical:
  "canonical (curry (reset_canonical_upd M n k (d :: 'c :: {linordered_ab_group_add,uminus}))) n"
  if "\<forall> i \<le> n. M (i, i) = 0" "canonical (curry M) n" "k > 0" for k n :: nat
  using reset_canonical_canonical[of n "curry M" k] that
  by (auto simp: reset_canonical_upd_reset_canonical')

definition reset'_upd where
  "reset'_upd M n cs d = fold (\<lambda> c M. reset_canonical_upd M n c d) cs M"

lemma reset'''_reset'_upd:
  fixes n:: nat and cs :: "nat list"
  assumes "\<forall> c \<in> set cs. c \<noteq> 0" "i \<le> n" "j \<le> n" "\<forall> i \<le> n. \<forall> j \<le> n. M (i, j) = M' i j"
  shows "(reset'_upd M n cs d) (i, j) = (reset''' M' n cs d) i j"
using assms
 apply (induction cs arbitrary: M M')
 unfolding reset'_upd_def reset'''_def
 apply (simp; fail)
 subgoal for c cs M M'
 using reset_canonical_upd_reset_canonical[where M = M] by auto
done

lemma reset'''_reset'_upd':
  fixes n:: nat and cs :: "nat list" and M :: "('a :: {linordered_cancel_ab_monoid_add,uminus}) DBM'"
  assumes "\<forall> c \<in> set cs. c \<noteq> 0" "i \<le> n" "j \<le> n"
  shows "(reset'_upd M n cs d) (i, j) = (reset''' (curry M) n cs d) i j"
using reset'''_reset'_upd[where M = M and M' = "curry M", OF assms] by simp

lemma reset'_upd_out_of_bounds1:
  fixes i j k n :: nat
  assumes "\<forall> c \<in> set cs. c \<le> n" "i > n"
  shows "(reset'_upd M n cs d) (i, j) = M (i, j)"
using assms
by (induction cs arbitrary: M, auto simp: reset'_upd_def intro: reset_canonical_upd_out_of_bounds_id1)

lemma reset'_upd_out_of_bounds2:
  fixes i j k n :: nat
  assumes "\<forall> c \<in> set cs. c \<le> n" "j > n"
  shows "(reset'_upd M n cs d) (i, j) = M (i, j)"
using assms
by (induction cs arbitrary: M, auto simp: reset'_upd_def intro: reset_canonical_upd_out_of_bounds_id2)

lemma reset_canonical_int_preservation:
  fixes n :: nat
  assumes "dbm_int M n" "d \<in> \<int>"
  shows "dbm_int (reset_canonical M k d) n"
using assms unfolding reset_canonical_def  by (auto dest: sum_not_inf_dest)

lemma reset_canonical_upd_int_preservation:
  assumes "dbm_int (curry M) n" "d \<in> \<int>" "k > 0"
  shows "dbm_int (curry (reset_canonical_upd M n k d)) n"
using reset_canonical_int_preservation[OF assms(1,2)] reset_canonical_upd_reset_canonical'
by (metis assms(3) curry_conv)

lemma reset'_upd_int_preservation:
  assumes "dbm_int (curry M) n" "d \<in> \<int>" "\<forall> c \<in> set cs. c \<noteq> 0"
  shows "dbm_int (curry (reset'_upd M n cs d)) n"
using assms
 apply (induction cs arbitrary: M)
 unfolding reset'_upd_def
 apply (simp; fail)
 apply (drule reset_canonical_upd_int_preservation; auto)
done

lemma reset_canonical_upd_diag_preservation:
  fixes i :: nat
  assumes "k > 0"
  shows "\<forall> i \<le> n. (reset_canonical_upd M n k d) (i, i) = M (i, i)"
using reset_canonical_diag_preservation reset_canonical_upd_reset_canonical' assms
by (metis curry_conv)

lemma reset'_upd_diag_preservation:
  assumes "\<forall> c \<in> set cs. c > 0" "i \<le> n"
  shows "(reset'_upd M n cs d) (i, i) = M (i, i)"
using assms
by (induction cs arbitrary: M; simp add: reset'_upd_def reset_canonical_upd_diag_preservation)

(* XXX Move *)
lemma upto_from_1_upt:
  fixes n :: nat
  shows "map nat [1..int n] = [1..<n+1]"
by (induction n) (auto simp: one_upto_Suc'')

(* Version to be made executable *)
lemma reset_canonical_upd_alt_def:
  "reset_canonical_upd (M :: ('a :: {linordered_cancel_ab_monoid_add,uminus}) DBM') ( n:: nat) (k :: nat) d =
    fold
      (\<lambda> i M.
        if i = k then
          M
        else do {
          let m0i = op_mtx_get M(0,i);
          let mi0 = op_mtx_get M(i, 0);
          M((k, i) := Le d + m0i, (i, k) := Le (-d) + mi0)
        }
      )
      [1..<n+1]
      (M((k, 0) := Le d, (0, k) := Le (-d)))
  "
unfolding reset_canonical_upd_def by (simp add: upto_from_1_upt cong: if_cong)


section \<open>Delay\<close>

(* XXX Move *)
named_theorems dbm_entry_simps

lemma [dbm_entry_simps]:
  "a + \<infinity> = \<infinity>"
unfolding add by (cases a) auto

lemma [dbm_entry_simps]:
  "\<infinity> + b = \<infinity>"
unfolding add by (cases b) auto

lemmas any_le_inf[dbm_entry_simps]

lemma up_canonical_preservation:
  assumes "canonical M n"
  shows "canonical (up M) n"
unfolding up_def using assms by (simp add: dbm_entry_simps)

definition up_canonical :: "'t DBM \<Rightarrow> 't DBM" where
  "up_canonical M = (\<lambda> i j. if i > 0 \<and> j = 0 then \<infinity> else M i j)"

lemma up_canonical_eq_up:
  assumes "canonical M n" "i \<le> n" "j \<le> n"
  shows "up_canonical M i j = up M i j"
unfolding up_canonical_def up_def using assms by simp

lemma DBM_up_to_equiv:
  assumes "\<forall> i \<le> n. \<forall> j \<le> n. M i j = M' i j"
  shows "[M]\<^bsub>v,n\<^esub> = [M']\<^bsub>v,n\<^esub>"
 apply safe
 apply (rule DBM_le_subset)
using assms by (auto simp: add[symmetric] intro: DBM_le_subset)

lemma up_canonical_equiv_up:
  assumes "canonical M n"
  shows "[up_canonical M]\<^bsub>v,n\<^esub> = [up M]\<^bsub>v,n\<^esub>"
 apply (rule DBM_up_to_equiv)
unfolding up_canonical_def up_def using assms by simp

lemma up_canonical_diag_preservation:
  assumes "\<forall> i \<le> n. M i i = 0"
  shows "\<forall> i \<le> n. (up_canonical M) i i = 0"
unfolding up_canonical_def using assms by auto

(* XXX Move *)
no_notation Ref.update ("_ := _" 62)

definition up_canonical_upd :: "'t DBM' \<Rightarrow> nat \<Rightarrow> 't DBM'" where
  "up_canonical_upd M n = fold (\<lambda> i M. M((i,0) := \<infinity>)) [1..<n+1] M"

lemma up_canonical_upd_rec:
  "up_canonical_upd M (Suc n) = (up_canonical_upd M n) ((Suc n, 0) := \<infinity>)"
unfolding up_canonical_upd_def by auto

lemma up_canonical_out_of_bounds1:
  fixes i :: nat
  assumes "i > n"
  shows "up_canonical_upd M n (i, j) = M(i,j)"
using assms by (induction n) (auto simp: up_canonical_upd_def)

lemma up_canonical_out_of_bounds2:
  fixes j :: nat
  assumes "j > 0"
  shows "up_canonical_upd M n (i, j) = M(i,j)"
using assms by (induction n) (auto simp: up_canonical_upd_def)

lemma up_canonical_upd_up_canonical:
  assumes "i \<le> n" "j \<le> n" "\<forall> i \<le> n. \<forall> j \<le> n. M (i, j) = M' i j"
  shows "(up_canonical_upd M n) (i, j) = (up_canonical M') i j"
using assms
proof (induction n)
  case 0
  then show ?case by (simp add: up_canonical_upd_def up_canonical_def; fail)
next
  case (Suc n)
  show ?case
  proof (cases "j = Suc n")
    case True
    with Suc.prems show ?thesis by (simp add: up_canonical_out_of_bounds2 up_canonical_def)
  next
    case False
    show ?thesis
    proof (cases "i = Suc n")
      case True
      with Suc.prems \<open>j \<noteq> _\<close> show ?thesis
      by (simp add: up_canonical_out_of_bounds1 up_canonical_def up_canonical_upd_rec)
    next
      case False
      with Suc \<open>j \<noteq> _\<close> show ?thesis by (auto simp: up_canonical_upd_rec)
    qed
  qed
qed

lemma up_canonical_int_preservation:
  assumes "dbm_int M n"
  shows "dbm_int (up_canonical M) n"
using assms unfolding up_canonical_def by auto

lemma up_canonical_upd_int_preservation:
  assumes "dbm_int (curry M) n"
  shows "dbm_int (curry (up_canonical_upd M n)) n"
using up_canonical_int_preservation[OF assms] up_canonical_upd_up_canonical[where M' = "curry M"]
by (auto simp: curry_def)

lemma up_canonical_diag_preservation':
  "(up_canonical M) i i = M i i"
unfolding up_canonical_def by auto

lemma up_canonical_upd_diag_preservation:
  "(up_canonical_upd M n) (i, i) = M (i, i)"
unfolding up_canonical_upd_def by (induction n) auto

section \<open>Inclusion\<close>

definition pointwise_cmp where
  "pointwise_cmp P n M M' = (\<forall> i \<le> n. \<forall> j \<le> n. P (M i j) (M' i j))"

lemma subset_eq_pointwise_le:
  fixes M :: "real DBM"
  assumes "canonical M n" "\<forall> i \<le> n. M i i = 0" "\<forall> i \<le> n. M' i i = 0"
      and prems: "clock_numbering' v n" "\<forall>k\<le>n. 0 < k \<longrightarrow> (\<exists>c. v c = k)"
  shows "[M]\<^bsub>v,n\<^esub> \<subseteq> [M']\<^bsub>v,n\<^esub> \<longleftrightarrow> pointwise_cmp (op \<le>) n M M'"
unfolding pointwise_cmp_def
apply safe
 subgoal for i j
  apply (cases "i = j")
   using assms apply (simp; fail)
  apply (rule DBM_canonical_subset_le)
 using assms(1-3) prems by (auto simp: cyc_free_not_empty[OF canonical_cyc_free])
by (auto simp: less_eq intro: DBM_le_subset)

definition check_diag :: "nat \<Rightarrow> ('t :: {linorder, zero}) DBM' \<Rightarrow> bool" where
  "check_diag n M \<equiv> \<exists> i \<le> n. M (i, i) < Le 0"

lemma check_diag_empty:
  fixes n :: nat and v
  assumes surj: "\<forall> k\<le>n. 0 < k \<longrightarrow> (\<exists>c. v c = k)"
  assumes "check_diag n M"
  shows "[curry M]\<^bsub>v,n\<^esub> = {}"
using assms neg_diag_empty[OF surj, where M = "curry M"] unfolding check_diag_def neutral by auto

lemma check_diag_alt_def:
  "check_diag n M = list_ex (\<lambda> i. op_mtx_get M (i, i) < Le 0) [0..<Suc n]"
unfolding check_diag_def list_ex_iff by fastforce

definition dbm_subset :: "nat \<Rightarrow> ('t :: {linorder, zero}) DBM' \<Rightarrow> 't DBM' \<Rightarrow> bool" where
  "dbm_subset n M M' \<equiv> check_diag n M \<or> pointwise_cmp (op \<le>) n (curry M) (curry M')"

lemma dbm_subset_refl:
  "dbm_subset n M M"
unfolding dbm_subset_def pointwise_cmp_def by simp

lemma dbm_subset_trans:
  assumes "dbm_subset n M1 M2" "dbm_subset n M2 M3"
  shows "dbm_subset n M1 M3"
using assms unfolding dbm_subset_def pointwise_cmp_def check_diag_def by fastforce

lemma canonical_nonneg_diag_non_empty:
  assumes "canonical M n" "\<forall>i\<le>n. 0 \<le> M i i" "\<forall>c. v c \<le> n \<longrightarrow> 0 < v c"
  shows "[M]\<^bsub>v,n\<^esub> \<noteq> {}"
 apply (rule cyc_free_not_empty)
 apply (rule canonical_cyc_free)
using assms by auto

text \<open>
  The type constraint in this lemma is due to @{thm DBM_canonical_subset_le}.
  Proving it for a more general class of types is possible but also tricky due to a missing
  setup for arithmetic.
\<close>
lemma subset_eq_dbm_subset:
  fixes M :: "real DBM'"
  assumes "canonical (curry M) n \<or> check_diag n M" "\<forall> i \<le> n. M (i, i) \<le> 0" "\<forall> i \<le> n. M' (i, i) \<le> 0"
      and cn: "clock_numbering' v n" and surj: "\<forall> k\<le>n. 0 < k \<longrightarrow> (\<exists>c. v c = k)"
  shows "[curry M]\<^bsub>v,n\<^esub> \<subseteq> [curry M']\<^bsub>v,n\<^esub> \<longleftrightarrow> dbm_subset n M M'"
proof (cases "check_diag n M")
  case True
  with check_diag_empty[OF surj] show ?thesis unfolding dbm_subset_def by auto
next
  case F: False
  with assms(1) have canonical: "canonical (curry M) n" by fast
  show ?thesis
  proof (cases "check_diag n M'")
    case True
    from F cn have
      "[curry M]\<^bsub>v,n\<^esub> \<noteq> {}"
     apply -
     apply (rule canonical_nonneg_diag_non_empty[OF canonical])
    unfolding check_diag_def neutral[symmetric] by auto
    moreover from F True have
      "\<not> dbm_subset n M M'"
    unfolding dbm_subset_def pointwise_cmp_def check_diag_def by fastforce
    ultimately show ?thesis using check_diag_empty[OF surj True] by auto
  next
    case False
    with F assms(2,3) have
      "\<forall> i \<le> n. M (i, i) = 0" "\<forall> i \<le> n. M' (i, i) = 0"
    unfolding check_diag_def neutral[symmetric] by fastforce+
    with F False show ?thesis unfolding dbm_subset_def
    by (subst subset_eq_pointwise_le[OF canonical _ _ cn surj]; auto)
  qed
qed

lemma pointwise_cmp_alt_def:
  "pointwise_cmp P n M M' =
    list_all (\<lambda> i. list_all (\<lambda> j. P (M i j) (M' i j)) [0..<Suc n]) [0..<Suc n]"
unfolding pointwise_cmp_def by (fastforce simp: list_all_iff)

lemma dbm_subset_alt_def[code]:
  "dbm_subset n M M' =
    (list_ex (\<lambda> i. op_mtx_get M (i, i) < Le 0) [0..<Suc n] \<or>
    list_all (\<lambda> i. list_all (\<lambda> j. (op_mtx_get M (i, j) \<le> op_mtx_get M' (i, j))) [0..<Suc n]) [0..<Suc n])"
by (simp add: dbm_subset_def check_diag_alt_def pointwise_cmp_alt_def)

(* XXX Unused *)
definition pointwise_cmp_alt_def where
  "pointwise_cmp_alt_def P n M M' = fold (\<lambda> i b. fold (\<lambda> j b. P (M i j) (M' i j) \<and> b) [1..<Suc n] b) [1..<Suc n] True"

lemma list_all_foldli:
  "list_all P xs = foldli xs (\<lambda>x. x = True) (\<lambda> x _. P x) True"
 apply (induction xs)
 apply (simp; fail)
 subgoal for x xs
  apply simp
  apply (induction xs)
 by auto
 done

lemma list_ex_foldli:
  "list_ex P xs = foldli xs Not (\<lambda> x y. P x \<or> y) False"
 apply (induction xs)
 apply (simp; fail)
 subgoal for x xs
  apply simp
  apply (induction xs)
 by auto
 done

section \<open>Constraints\<close>

(*
fun abstra' :: "(nat, 't::time) acconstraint \<Rightarrow> 't DBM \<Rightarrow> 't DBM"
where
  "abstra' (EQ c d) M =
    (\<lambda> i j . if i = 0 \<and> j = c then min (M i j) (Le (-d)) else if i = c \<and> j = 0 then min (M i j) (Le d) else M i j)" |
  "abstra' (LT c d) M =
    (\<lambda> i j . if i = c \<and> j = 0 then min (M i j) (Lt d) else M i j)" |
  "abstra' (LE c d) M =
    (\<lambda> i j . if i = c \<and> j = 0 then min (M i j) (Le d) else M i j)" |
  "abstra' (GT c d) M =
    (\<lambda> i j. if i = 0 \<and> j = c then min (M i j) (Lt (- d)) else M i j)" |
  "abstra' (GE c d) M =
    (\<lambda> i j. if i = 0 \<and> j = c then min (M i j) (Le (- d)) else M i j)"
*)

definition "abstra' ac M = abstra ac M id"

lemma abstra_abstra':
  assumes "v (constraint_clk ac) = constraint_clk ac"
  shows "abstra ac M v = abstra' ac M"
unfolding abstra'_def using assms by (cases ac; fastforce)

definition "abstr' cc M = abstr cc M id"

lemma abstr_abstr':
  assumes "\<forall> c \<in> collect_clks cc. v c = c"
  shows "abstr cc M v = abstr' cc M"
unfolding abstr'_def using assms
by (auto simp: collect_clks_def intro: fold_cong abstra_abstra'[unfolded abstra'_def])

(* XXX Move? *)
lemma And_abstr:
  assumes "clock_numbering' v n" "\<forall> c \<in> collect_clks cc. v c \<le> n"
  shows "[And M (abstr cc (\<lambda> i j. \<infinity>) v)]\<^bsub>v,n\<^esub> = [abstr cc M v]\<^bsub>v,n\<^esub>"
using And_correct dbm_abstr_zone_eq[OF assms] dbm_abstr_zone_eq2[OF assms] by blast

(* XXX Move *)
lemma min_inf_r:
  "min a \<infinity> = a"
by (cases a) (auto split: split_min simp: less_eq dbm_le_def)

lemma min_inf_l:
  "min \<infinity> b = b"
by (cases b) (auto split: split_min simp: less_eq dbm_le_def)

lemma And_abstra_commute:
  assumes "clock_numbering' v n" "\<forall> c \<in> collect_clks cc. v c \<le> n"
  shows "And M (abstra ac (\<lambda> i j. \<infinity>) v) = abstra ac M v"
by (cases ac) (auto simp: min_inf_l min_inf_r any_le_inf intro!: ext)

(* Could be proven by using the facts that abstra commutes with itself and And*)
lemma
  assumes "clock_numbering' v n" "\<forall> c \<in> collect_clks cc. v c \<le> n"
  shows "And M (abstr cc (\<lambda> i j. \<infinity>) v) = abstr cc M v"
apply (induction cc)
apply simp
apply (simp add: min_inf_r)
oops

lemma abstra_canonical_diag_preservation:
  assumes "clock_numbering v"
  shows "(abstra ac M v) i i = M i i"
using assms by (cases ac) (auto dest: clock_numberingD)

lemma abstr_canonical_diag_preservation:
  assumes "clock_numbering v"
  shows "(abstr cc M v) i i = M i i"
using assms
apply (induction cc arbitrary: M)
apply (simp; fail)
 subgoal for ac cc M
 using abstra_canonical_diag_preservation[where v = v and ac = ac] by auto
done

fun abstra_upd :: "(nat, 't::{linorder,uminus}) acconstraint \<Rightarrow> 't DBM' \<Rightarrow> 't DBM'"
where
  "abstra_upd (EQ c d) M =
    (let m0c = op_mtx_get M (0, c); mc0 = op_mtx_get M(c, 0) in M((0, c) := min m0c (Le (-d)), (c, 0) := min mc0 (Le d)))" |
  "abstra_upd (LT c d) M =
    M((c, 0) := min (op_mtx_get M (c, 0)) (Lt d))" |
  "abstra_upd (LE c d) M =
    M((c, 0) := min (op_mtx_get M (c, 0)) (Le d))" |
  "abstra_upd (GT c d) M =
    M((0, c) := min (op_mtx_get M ((0, c))) (Lt (- d)))" |
  "abstra_upd (GE c d) M =
    M((0, c) := min (op_mtx_get M (0, c)) (Le (- d)))"

term case_acconstraint

lemma abstra_upd_alt_def:
  "abstra_upd ac M = case_acconstraint
    (\<lambda> c d. M((c, 0) := min (op_mtx_get M (c, 0)) (Lt d)))
    (\<lambda> c d. M((c, 0) := min (op_mtx_get M (c, 0)) (Le d)))
    (\<lambda> c d. let m0c = op_mtx_get M (0, c); mc0 = op_mtx_get M(c, 0) in M((0, c) := min m0c (Le (-d)), (c, 0) := min mc0 (Le d)))
    (\<lambda> c d. M((0, c) := min (op_mtx_get M ((0, c))) (Lt (- d))))
    (\<lambda> c d. M((0, c) := min (op_mtx_get M (0, c)) (Le (- d))))
    ac"
by (cases ac) auto

lemma abstra_upd_eq_abstra':
  assumes "constraint_clk ac > 0"
  shows "curry (abstra_upd ac M) = abstra' ac (curry M)"
unfolding abstra'_def using assms by (cases ac; fastforce)

lemma abstra_upd_int_preservation:
  assumes "snd (constraint_pair ac) \<in> \<int>" "dbm_int (curry M) n"
  shows "dbm_int (curry (abstra_upd ac M)) n"
using assms by (cases ac; simp split: split_min)

definition abstr_upd where
  "abstr_upd = fold (\<lambda> ac M. abstra_upd ac M)"

lemma abstr_upd_alt_def:
  "RETURN oo abstr_upd = (\<lambda> cc M. nfoldli cc (\<lambda> _. True) (\<lambda> ac M. RETURN (abstra_upd ac M)) M)"
by (intro ext, simp add: abstr_upd_def fold_eq_nfoldli)


lemma abstr_upd_abstr':
  assumes "\<forall> c \<in> collect_clks cc. c > 0"
  shows "curry (abstr_upd cc M) = abstr' cc (curry M)"
unfolding abstr_upd_def abstr'_def using assms
by (induction cc arbitrary: M) (auto simp: abstra_abstra' abstra_upd_eq_abstra')

lemma abstra_upd_out_of_bounds1:
  assumes "constraint_clk ac \<le> n" "i > n"
  shows "(abstra_upd ac M) (i, j) = M (i, j)"
using assms by (cases ac) auto

lemma abstra_upd_out_of_bounds2:
  assumes "constraint_clk ac \<le> n" "j > n"
  shows "(abstra_upd ac M) (i, j) = M (i, j)"
using assms by (cases ac) auto

lemma abstr_upd_out_of_bounds1:
  assumes "\<forall> c \<in> collect_clks cc. c \<le> n" "i > n"
  shows "(abstr_upd cc M) (i, j) = M (i, j)"
using assms by (induction cc arbitrary: M) (auto simp: abstr_upd_def abstra_upd_out_of_bounds1)

lemma abstr_upd_out_of_bounds2:
  assumes "\<forall> c \<in> collect_clks cc. c \<le> n" "j > n"
  shows "(abstr_upd cc M) (i, j) = M (i, j)"
using assms by (induction cc arbitrary: M) (auto simp: abstr_upd_def abstra_upd_out_of_bounds2)

lemma abstr_upd_int_preservation:
  assumes "\<forall> (_,d) \<in> collect_clock_pairs cc. d \<in> \<int>" "dbm_int (curry M) n"
  shows "dbm_int (curry (abstr_upd cc M)) n"
unfolding abstr_upd_def using assms
proof (induction cc arbitrary: M)
  case Nil then show ?case by simp
next
  case (Cons c cc)
  show ?case
   apply simp
   apply (rule Cons.IH[simplified])
   defer
   apply (rule abstra_upd_int_preservation[simplified])
  using Cons.prems unfolding collect_clock_pairs_def by auto
qed

(*
fun abstra_upd :: "('c, 't::time) acconstraint \<Rightarrow> 't DBM' \<Rightarrow> ('c \<Rightarrow> nat) \<Rightarrow> 't DBM'"
where
  "abstra_upd (EQ c d) M v =
    (let m0c = op_mtx_get M (0, v c); mc0 = op_mtx_get M(v c, 0) in M((0, v c) := min m0c (Le (-d)), (v c, 0) := min mc0 (Le d)))" |
  "abstra_upd (LT c d) M v =
    M((v c, 0) := min (op_mtx_get M (v c, 0)) (Lt d))" |
  "abstra_upd (LE c d) M v =
    M((v c, 0) := min (op_mtx_get M (v c, 0)) (Le d))" |
  "abstra_upd (GT c d) M v =
    M((0, v c) := min (op_mtx_get M ((0, v c))) (Lt (- d)))" |
  "abstra_upd (GE c d) M v =
    M((0, v c) := min (op_mtx_get M (0, v c)) (Le (- d)))"

lemma abstra_upd_eq_abstra:
  assumes "clock_numbering v"
  shows "curry (abstra_upd ac M v) = abstra ac (curry M) v"
using assms by (cases ac; fastforce dest: clock_numberingD)
*)

section \<open>Normalization\<close>

(* XXX Possible to optimize norm_lower/norm_upper combinations? *)
definition norm_upd_line :: "('t::{linordered_ab_group_add}) DBM' \<Rightarrow> 't list \<Rightarrow> 't \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 't DBM'"
where
  "norm_upd_line M k ub i n =
    fold
      (\<lambda> j M. M((i, j) := norm_lower (norm_upper (M (i, j)) ub) (- (op_list_get k j))))
      [1..<Suc n]
      (M((i, 0) := norm_lower (norm_upper (M (i, 0)) ub) 0))"

(* XXX Unused remove? *)
lemma norm_upd_line_Suc_unfold:
  "norm_upd_line M k ub i (Suc n) =
  (norm_upd_line M k ub i n) ((i, Suc n) :=
    norm_lower (norm_upper (norm_upd_line M k ub i n (i, Suc n)) ub) (- (op_list_get k (Suc n))))"
unfolding norm_upd_line_def by (simp del: norm_lower.simps norm_upper.simps)

lemma norm_upd_line_out_of_bounds:
  assumes "j > n"
  shows "norm_upd_line M k ub i n (i', j) = M (i', j)"
using assms by (induction n) (auto simp: norm_upd_line_def)

(* XXX Unused remove? *)
lemma norm_upd_line_rec:
  assumes "j < Suc n"
  shows "norm_upd_line M k ub i (Suc n) (i', j) = norm_upd_line M k ub i n (i', j)"
using assms by (simp add: norm_upd_line_Suc_unfold)

lemma norm_upd_line_alt_def:
  assumes "j \<le> n"
  shows
  "norm_upd_line M k ub i n (i', j) = (
    let lb = if j > 0 then (- op_list_get k j) else 0 in
    if i' = i \<and> j \<le> n then norm_lower (norm_upper (M (i, j)) ub) lb else M (i', j)
   )"
 apply (clarsimp simp del: norm_lower.simps norm_upper.simps)
 apply safe
by ((induction n, simp add: norm_upd_line_def,
     simp del: norm_lower.simps norm_upper.simps add: norm_upd_line_out_of_bounds norm_upd_line_Suc_unfold)
    ; fail)+

definition norm_upd :: "('t :: linordered_ab_group_add) DBM' \<Rightarrow> 't list \<Rightarrow> nat \<Rightarrow> 't DBM'"
where
  "norm_upd M k n \<equiv>
    fold (\<lambda> i M. norm_upd_line M k (op_list_get k i) i n) [1..<Suc n] (norm_upd_line M k 0 0 n)
  "

lemma norm_upd_out_of_bounds_aux1:
  assumes "i > n" "j \<le> m"
  shows "
    fold (\<lambda> i M. norm_upd_line M k (k ! i) i m)
      [Suc 0..<Suc n]
      (norm_upd_line M k 0 0 m)
    (i, j) = M (i, j)"
using assms
 apply (induction n)
 apply (simp add: norm_upd_line_alt_def del: upt_Suc norm_lower.simps norm_upper.simps; fail)
 apply (subst upt_Suc_append; simp add: norm_upd_line_alt_def del: upt_Suc)
done

(* XXX Unused remove? *)
lemma norm_upd_out_of_bounds_aux2:
  assumes "j > m"
  shows "
    fold (\<lambda> i M. norm_upd_line M k (op_list_get k i) i m)
      [1..<Suc n]
      (norm_upd_line M k 0 0 m)
    (i, j) = M (i, j)"
using assms by (induction n; simp add: norm_upd_line_out_of_bounds)

(* XXX Unused remove? *)
lemma norm_upd_out_of_bounds_aux:
  assumes "i > n"
  shows
  "fold (\<lambda> i M. norm_upd_line M k (op_list_get k i) i n) [1..<Suc n] (norm_upd_line M k 0 0 n) (i, j)
  = M (i, j)"
using assms
apply (induction n)
apply (simp add: norm_upd_line_def; fail)

apply (case_tac "j \<le> Suc n")

 apply (subst upt_Suc_append)
  apply (simp; fail)
 apply (simp del: upt_Suc)
 apply (subst norm_upd_line_alt_def)
  apply (simp; fail)
 apply (simp del: upt_Suc norm_lower.simps norm_upper.simps)
 apply (subst norm_upd_out_of_bounds_aux1[unfolded op_list_get_def One_nat_def])
   apply (simp; fail)
  apply (simp; fail)
 apply (simp; fail)

 apply (subst norm_upd_out_of_bounds_aux2; simp)
done

lemma norm_upd_out_of_bounds1:
  assumes "i > n"
  shows "(norm_upd M k n) (i, j) = M (i, j)"
using norm_upd_out_of_bounds_aux[OF assms] unfolding norm_upd_def .

lemma norm_upd_out_of_bounds2:
  assumes "j > n"
  shows "(norm_upd M k n) (i, j) = M (i, j)"
using norm_upd_out_of_bounds_aux2[OF assms] unfolding norm_upd_def .


definition norm_entry where
  "norm_entry x k i j = (let ub = if i > 0 then (k ! i) else 0 in
    let lb = if j > 0 then (- k ! j) else 0 in
    norm_lower (norm_upper x ub) lb)"

lemma norm_upd_norm_aux:
  assumes "i \<le> n" "j \<le> m"
  shows "fold (\<lambda>i M. norm_upd_line M k (op_list_get k i) i m) [1..<Suc n] (norm_upd_line M k 0 0 m) (i, j) =
    norm_entry (M (i, j)) k i j"
using assms
apply (induction n)
apply (simp add: norm_entry_def norm_upd_line_alt_def del: upt_Suc norm_lower.simps norm_upper.simps; fail)

subgoal for n
apply (cases "i = Suc n")

 apply (subst upt_Suc_append)
  apply (simp; fail)
 apply (simp del: upt_Suc)
 apply (subst norm_upd_line_alt_def)
  apply (simp; fail)
 apply (simp del: upt_Suc norm_lower.simps norm_upper.simps)
 apply (subst norm_upd_out_of_bounds_aux1)
   apply (simp; fail)
  apply (simp; fail)
 apply (subst norm_upd_out_of_bounds_aux1)
   apply (simp; fail)
  apply (simp; fail)
 apply (simp add: norm_entry_def; fail)

 apply (subst upt_Suc_append)
  apply (simp; fail)
 apply (simp del: upt_Suc)
 apply (simp add: norm_upd_line_alt_def; fail)
done
done

lemma norm_upd_norm_aux':
  assumes "i \<le> n" "j \<le> n"
  shows "(norm_upd M k n) (i, j) = (norm (curry M) (\<lambda> i. k ! i) n) i j"
using assms unfolding norm_upd_def
 apply (subst norm_upd_norm_aux[OF assms])
by (simp add: norm_entry_def norm_def del: norm_upper.simps norm_lower.simps)

lemma norm_upd_norm:
  "norm_upd M k n (i, j) = norm (curry M) (\<lambda> i. k ! i) n i j"
 apply (cases "i > n")
 apply (simp add: norm_upd_out_of_bounds1 norm_def; fail)
 apply (cases "j > n"; simp add: norm_upd_out_of_bounds2 norm_def norm_upd_norm_aux')
done

lemma norm_upd_norm':
  "curry (norm_upd M k n) = norm (curry M) (\<lambda> i. k ! i) n"
by (simp add: curry_def norm_upd_norm)

(* XXX Copy from Regions Beta, original should be moved *)
lemma norm_int_preservation:
  assumes "dbm_int M n" "\<forall> c \<le> n. k c \<in> \<int>"
  shows "dbm_int (norm M k n) n"
using assms unfolding norm_def by (auto simp: Let_def)

lemma norm_upd_int_preservation:
  fixes M :: "('t :: {linordered_ab_group_add, ring_1}) DBM'"
  assumes "dbm_int (curry M) n" "\<forall> c \<in> set k. c \<in> \<int>" "length k = Suc n"
  shows "dbm_int (curry (norm_upd M k n)) n"
proof -
  let ?k = "(\<lambda> i. k ! i)"
  from norm_int_preservation[OF assms(1), where k = ?k] assms(2,3) have
    "dbm_int (norm (curry M) ?k n) n"
  by fastforce
  with norm_upd_norm[where M = M] show ?thesis by auto
qed

end (* End of theory *)
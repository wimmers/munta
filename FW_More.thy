theory FW_More
  imports TA.DBM_Basics TA.FW_Code
begin

thm FW_zone_equiv
thm fw_shortest_path_up_to thm fwi_step'

lemma fwi_len_distinct:
  "\<exists> ys. set ys \<subseteq> {k} \<and> fwi m n k n n i j = len m i j ys \<and> i \<notin> set ys \<and> j \<notin> set ys \<and> distinct ys"
  if "i \<le> n" "j \<le> n" "k \<le> n" "m k k \<ge> 0"
  using fwi_step'[of m, OF that(4), of n n n i j] that
  apply (clarsimp split: if_splits simp: min_def)
  by (rule exI[where x = "[]"] exI[where x = "[k]"]; auto simp: add_increasing add_increasing2; fail)+

lemma FWI_mono:
  "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> FWI M n k i j \<le> M i j"
  using fwi_mono[of _ n _ M k n n, folded FWI_def, rule_format] .

lemma FWI_zone_equiv:
  "[M]\<^bsub>v,n\<^esub> = [FWI M n k]\<^bsub>v,n\<^esub>" if surj_on: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)" and "k \<le> n"
proof safe
  fix u assume A: "u \<in> [FWI M n k]\<^bsub>v,n\<^esub>"
  { fix i j assume "i \<le> n" "j \<le> n"
    then have "FWI M n k i j \<le> M i j" by (rule FWI_mono)
    hence "FWI M n k i j \<preceq> M i j" by (simp add: less_eq)
  }
  with DBM_le_subset[of n "FWI M n k" M] A show "u \<in> [M]\<^bsub>v,n\<^esub>" by auto
next
  fix u assume u:"u \<in> [M]\<^bsub>v,n\<^esub>"
  hence *:"DBM_val_bounded v u M n" by (simp add: DBM_zone_repr_def)
  note ** = DBM_val_bounded_neg_cycle[OF this _ _ _ surj_on]
  have cyc_free: "cyc_free M n" using ** by fastforce
  from cyc_free_diag[OF this] \<open>k \<le> n\<close> have "M k k \<ge> 0" by auto

  have "DBM_val_bounded v u (FWI M n k) n" unfolding DBM_val_bounded_def
  proof (safe, goal_cases)
    case 1
    with \<open>k \<le> n\<close> \<open>M k k \<ge> 0\<close> cyc_free show ?case
      unfolding FWI_def neutral[symmetric] less_eq[symmetric]
      by - (rule fwi_cyc_free_diag[where I = "{0..n}"]; auto)
  next
    case (2 c)
    with \<open>k \<le> n\<close> \<open>M k k \<ge> 0\<close> fwi_len_distinct[of 0 n "v c" k M] obtain xs where xs:
      "FWI M n k 0 (v c) = len M 0 (v c) xs" "set xs \<subseteq> {0..n}" "0 \<notin> set xs"
      unfolding FWI_def by force
    with surj_on \<open>v c \<le> n\<close> show ?case unfolding xs(1)
      by - (rule DBM_val_bounded_len'2[OF *]; auto)
  next
    case (3 c)
    with \<open>k \<le> n\<close> \<open>M k k \<ge> 0\<close> fwi_len_distinct[of "v c" n 0 k M] obtain xs where xs:
      "FWI M n k (v c) 0 = len M (v c) 0 xs" "set xs \<subseteq> {0..n}"
      "0 \<notin> set xs" "v c \<notin> set xs"
      unfolding FWI_def by force
    with surj_on \<open>v c \<le> n\<close> show ?case unfolding xs(1)
      by - (rule DBM_val_bounded_len'1[OF *]; auto)
  next
    case (4 c1 c2)
    with \<open>k \<le> n\<close> \<open>M k k \<ge> 0\<close> fwi_len_distinct[of "v c1" n "v c2" k M] obtain xs where xs:
      "FWI M n k (v c1) (v c2) = len M (v c1) (v c2) xs" "set xs \<subseteq> {0..n}"
      "v c1 \<notin> set xs" "v c2 \<notin> set xs" "distinct xs"
      unfolding FWI_def by force
    with surj_on \<open>v c1 \<le> n\<close> \<open>v c2 \<le> n\<close> show ?case
      unfolding xs(1) by - (rule DBM_val_bounded_len'3[OF *]; auto dest: distinct_cnt[of _ 0])
  qed
  then show "u \<in> [FWI M n k]\<^bsub>v,n\<^esub>" unfolding DBM_zone_repr_def by simp
qed

end

theory Deadlock
  imports
    TA.Timed_Automata TA.CTL TA.DBM_Operations TA.Normalized_Zone_Semantics
begin

section \<open>Deadlock Checking\<close>

subsection \<open>Notes\<close>

text \<open>
If we want to run the deadlock checker together with a reachability check for property \<open>P\<close>, we can:
  \<^item> run a reachability check with \<open>\<not> check_deadlock\<close> first; if we find a deadlock, we are done;
    else we can check whether any of the reachable states satisfies \<open>P\<close>;
  \<^item> or run a reachability check with \<open>P\<close> first, which might give us earlier termination;
    if we find that \<open>P\<close> is satisfied, can we directly report that the original formula is satisfied?

Generally, it seems advantageous to compute \<open>\<not> check_deadlock\<close> on the final set of states, and
not intermediate subsumed ones, as the operation is expensive.
\<close>


subsection \<open>Abstract Reachability Checking\<close>

definition zone_time_pre :: "('c, ('t::time)) zone \<Rightarrow> ('c, 't) zone"
("_\<^sup>\<down>" [71] 71)
where
  "Z\<^sup>\<down> = {u | u d. (u \<oplus> d) \<in> Z \<and> d \<ge> (0::'t)}"

definition zone_set_pre :: "('c, 't::time) zone \<Rightarrow> 'c list \<Rightarrow> ('c, 't) zone"
where
  "zone_set_pre Z r = {u . ([r \<rightarrow> (0::'t)]u) \<in> Z}"

definition zone_pre :: "('c, 't::time) zone \<Rightarrow> 'c list \<Rightarrow> ('c, 't) zone"
  where
  "zone_pre Z r = (zone_set_pre Z r)\<^sup>\<down>"


context Regions_TA
begin

definition
  "check_deadlock l Z \<equiv> Z \<subseteq>
    \<Union> {(zone_set_pre {u. u \<turnstile> inv_of A l'} r \<inter> {u. u \<turnstile> g} \<inter> {u. u \<turnstile> inv_of A l})\<^sup>\<down> | g a r l'.
        A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'}"

lemma step_trans1:
  assumes "A \<turnstile>\<^sub>t \<langle>l, u\<rangle> \<rightarrow>\<^bsub>(g,a,r)\<^esub> \<langle>l', u'\<rangle>"
  shows "u \<in> zone_set_pre {u. u \<turnstile> inv_of A l'} r \<inter> {u. u \<turnstile> g}" "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"
  using assms by (auto elim!: step_trans.cases simp: zone_set_pre_def)

lemma step_trans2:
  assumes "u \<in> zone_set_pre {u. u \<turnstile> inv_of A l'} r \<inter> {u. u \<turnstile> g}" "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"
  shows "\<exists> u'. A \<turnstile>\<^sub>t \<langle>l, u\<rangle> \<rightarrow>\<^bsub>(g,a,r)\<^esub> \<langle>l', u'\<rangle>"
  using assms unfolding zone_set_pre_def by auto

lemma time_pre_zone:
  "u \<in> (Z \<inter> {u. u \<turnstile> inv_of A l})\<^sup>\<down>" if "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l', u'\<rangle>" "u' \<in> Z"
  using that by (auto elim!: step_t.cases simp: zone_time_pre_def)

lemma time_pre_zone':
  "\<exists> d u'. u' \<in> Z \<and> A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l, u'\<rangle>" if "u \<in> (Z \<inter> {u. u \<turnstile> inv_of A l})\<^sup>\<down>"
  using that unfolding zone_time_pre_def by auto

lemma step_trans3:
  assumes "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>\<^bsup>(g,a,r)\<^esup> \<langle>l', u'\<rangle>"
  shows "u \<in> (zone_set_pre {u. u \<turnstile> inv_of A l'} r \<inter> {u. u \<turnstile> g} \<inter> {u. u \<turnstile> inv_of A l})\<^sup>\<down>"
        "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"
  using assms by (auto dest: step_trans1 time_pre_zone step_delay_loc elim: step_trans'.cases)

lemma step_trans4:
  assumes "u \<in> (zone_set_pre {u. u \<turnstile> inv_of A l'} r \<inter> {u. u \<turnstile> g} \<inter> {u. u \<turnstile> inv_of A l})\<^sup>\<down>"
          "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"
    shows "\<exists> u'. A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>\<^bsup>(g,a,r)\<^esup> \<langle>l', u'\<rangle>"
  using assms by (fast dest: time_pre_zone' step_trans2[rotated])

lemma check_deadlock_correct:
  "check_deadlock l Z \<longleftrightarrow> (\<forall>u \<in> Z. \<exists>l' u' g a r. A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>\<^bsup>(g,a,r)\<^esup> \<langle>l', u'\<rangle>)"
  unfolding check_deadlock_def
  apply safe
  subgoal for x
    using step_trans4 by blast
  subgoal for x
    using step_trans3 by fast
  done

lemma step'_step_trans'_iff:
  "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle> \<longleftrightarrow> (\<exists>g a r. A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>\<^bsup>(g,a,r)\<^esup> \<langle>l', u'\<rangle>)"
  by (metis prod_cases3 step'.cases step'.intros step_a.cases step_a.simps step_trans'.cases
            step_trans'.intros step_trans.cases step_trans.simps
     )

lemma check_deadlock_correct_step':
  "check_deadlock l Z \<longleftrightarrow> (\<forall>u \<in> Z. \<exists>l' u'. A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)"
  using check_deadlock_correct step'_step_trans'_iff by simp

paragraph \<open>Unused\<close>

lemma delay_step_zone:
  "u' \<in> Z\<^sup>\<up> \<inter> {u. u \<turnstile> inv_of A l}" if "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l, u'\<rangle>" "u \<in> Z"
  using that by (auto elim!: step_t.cases simp: zone_delay_def)

lemma delay_step_zone':
  "\<exists> d u. u \<in> Z \<and> A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l, u'\<rangle>" if "u' \<in> Z\<^sup>\<up> \<inter> {u. u \<turnstile> inv_of A l}"
  using that by (auto simp: zone_delay_def)

lemma delay_step_zone'':
  "(\<exists> d u. u \<in> Z \<and> A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l, u'\<rangle>) \<longleftrightarrow> u' \<in> Z\<^sup>\<up> \<inter> {u. u \<turnstile> inv_of A l}"
  using delay_step_zone delay_step_zone' by blast

lemma delay_step_zone''':
  "{u' | u' d u. u \<in> Z \<and> A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l, u'\<rangle>} = Z\<^sup>\<up> \<inter> {u. u \<turnstile> inv_of A l}"
  using delay_step_zone'' by auto

end (* Regions TA *)


context Regions_TA_Start_State
begin

lemma check_deadlock_deadlocked:
  "\<not> check_deadlock l Z \<longleftrightarrow> (\<exists>u\<in>Z. sim.sim.deadlocked (l, u))"
  unfolding check_deadlock_correct_step' sim.sim.deadlocked_def by simp

lemma deadlock_check':
  "(\<exists>x\<^sub>0\<in>a\<^sub>0. \<exists>l u. sim.sim.reaches x\<^sub>0 (l, u) \<and> sim.sim.deadlocked (l, u)) \<longleftrightarrow>
   (\<exists>l Z. reaches (l\<^sub>0, Z\<^sub>0) (l, Z) \<and> \<not> check_deadlock l Z)"
  apply (subst ta_reaches_ex_iff)
  subgoal for l u u' R
    by (rule sim_complete_bisim'.P1_deadlocked_compatible[where a = "from_R l R"])
       (auto intro: sim_complete_bisim'.P1_P1')
  using check_deadlock_deadlocked by auto

lemma deadlock_check:
  "(\<exists>x\<^sub>0\<in>a\<^sub>0. sim.sim.deadlock x\<^sub>0) \<longleftrightarrow> (\<exists>l Z. reaches (l\<^sub>0, Z\<^sub>0) (l, Z) \<and> \<not> check_deadlock l Z)"
  unfolding deadlock_check'[symmetric] sim.sim.deadlock_def by simp

end (* Regions TA Start State *)


subsection \<open>Operations\<close>

subsubsection \<open>Subset inclusion check for federations on DBMs\<close>

lemma
  "S \<subseteq> R \<longleftrightarrow> S \<inter> -R = {}"
  by auto

lemma
  "A \<subseteq> B \<union> C \<longleftrightarrow> A \<inter> -B \<inter> -C = {}"
  by auto

lemma
  "(A \<union> B) \<inter> (C \<union> D) = A \<inter> C \<union> A \<inter> D \<union> B \<inter> C \<union> B \<inter> D"
  by auto

(* XXX *)
lemma Le_le_inf[intro]:
  "Le (x :: _ :: linordered_cancel_ab_monoid_add) \<preceq> \<infinity>"
  by (auto intro: linordered_monoid.order.strict_implies_order)

(* XXX Move *)
lemma dbm_entry_val_mono:
  "dbm_entry_val u a b e'" if "dbm_entry_val u a b e" "e \<le> e'"
using that
  by cases
  (auto simp: DBM.less_eq intro: dbm_entry_val_mono_1 dbm_entry_val_mono_2 dbm_entry_val_mono_3
    | simp add: DBM.less_eq dbm_entry_val.simps dbm_le_def
  )+

locale Default_Nat_Clock_Numbering =
  fixes n :: nat and v :: "nat \<Rightarrow> nat"
  assumes v_is_id: "\<forall> c. c > 0 \<and> c \<le> n \<longrightarrow> v c = c" "\<forall> c. c > n \<longrightarrow> v c = n + 1" "v 0 = n + 1"
begin

lemma v_id:
  "v c = c" if "v c \<le> n"
  using v_is_id that
  apply (cases "c = 0")
  apply (simp; fail)
  apply (cases "c \<le> n"; auto)
  done

lemma le_n:
  "c \<le> n" if "v c \<le> n"
  using that v_is_id by auto

lemma gt_0:
  "c > 0" if "v c \<le> n"
  using that v_is_id by auto

lemma le_n_iff:
  "v c \<le> n \<longleftrightarrow> c \<le> n \<and> c > 0"
  using v_is_id by auto

lemma v_0:
  "v c = 0 \<longleftrightarrow> False"
  using v_is_id by (cases "c > 0"; simp; cases "c > n"; simp)

abbreviation zone_of ("\<lbrakk>_\<rbrakk>") where "zone_of M \<equiv> [M]\<^bsub>v,n\<^esub>"

abbreviation
  "dbm_fed S \<equiv> \<Union> m \<in> S. \<lbrakk>m\<rbrakk>"

abbreviation
  "dbm_list xs \<equiv> dbm_fed (set xs)"

lemma dbm_fed_singleton:
  "dbm_fed {m} = [m]\<^bsub>v,n\<^esub>"
  by auto

lemma dbm_list_single:
  "dbm_list xs = [m]\<^bsub>v,n\<^esub>" if "set xs = {m}"
  using that by auto

lemma dbm_fed_superset_fold:
  "S \<subseteq> dbm_list xs \<longleftrightarrow> fold (\<lambda>m S. S \<inter> - ([m]\<^bsub>v,n\<^esub>)) xs S = {}"
proof (induction xs arbitrary: S)
  case Nil
  then show ?case
    by auto
next
  case (Cons m xs)
  have "S \<subseteq> dbm_list (m # xs) \<longleftrightarrow> S \<inter> - ([m]\<^bsub>v,n\<^esub>) \<subseteq> dbm_list xs"
    by auto
  moreover have "\<dots> \<longleftrightarrow> fold (\<lambda>m S. S \<inter> - ([m]\<^bsub>v,n\<^esub>)) xs (S \<inter> - ([m]\<^bsub>v,n\<^esub>)) = {}"
    by fact
  ultimately show ?case
    by simp
qed

lemma dbm_fed_superset_fold':
  "dbm_fed S \<subseteq> dbm_list xs \<longleftrightarrow> dbm_fed (fold f xs S) = {}" if
  "\<And> m S. m \<in> set xs \<Longrightarrow> dbm_fed (f m S) = dbm_fed S \<inter> - ([m]\<^bsub>v,n\<^esub>)"
proof -
  from that have "fold (\<lambda>m S. S \<inter> - ([m]\<^bsub>v,n\<^esub>)) xs (dbm_fed S) = dbm_fed (fold f xs S)"
  proof (induction xs arbitrary: S)
    case Nil
    then show ?case
      by simp
  next
    case (Cons a xs)
    from Cons.prems have
      "dbm_fed (fold f xs (f a S)) = fold (\<lambda>m S. S \<inter> - ([m]\<^bsub>v,n\<^esub>)) xs (dbm_fed (f a S))"
      by - (rule sym, rule Cons.IH, auto)
    then show ?case
      by (simp add: Cons.prems)
  qed
  then show ?thesis
    by (simp add: dbm_fed_superset_fold)
qed

lemma dbm_fed_superset_fold'':
  "dbm_list S \<subseteq> dbm_list xs \<longleftrightarrow> dbm_list (fold f xs S) = {}" if
  "\<And> m S. m \<in> set xs \<Longrightarrow> dbm_list (f m S) = dbm_list S \<inter> - ([m]\<^bsub>v,n\<^esub>)"
proof -
  from that have "fold (\<lambda>m S. S \<inter> - ([m]\<^bsub>v,n\<^esub>)) xs (dbm_list S) = dbm_list (fold f xs S)"
  proof (induction xs arbitrary: S)
    case Nil
    then show ?case
      by simp
  next
    case (Cons a xs)
    from Cons.prems have
      "dbm_list (fold f xs (f a S)) = fold (\<lambda>m S. S \<inter> - ([m]\<^bsub>v,n\<^esub>)) xs (dbm_list (f a S))"
      by - (rule sym, rule Cons.IH, auto)
    then show ?case
      by (simp add: Cons.prems)
  qed
  then show ?thesis
    by (simp add: dbm_fed_superset_fold)
qed

lemma neg_inf:
  "{u. \<not> dbm_entry_val u a b e} = {}" if "e = (\<infinity> :: _ DBMEntry)"
  using that by auto

fun neg_dbm_entry where
  "neg_dbm_entry (Le a) = Lt (-a)" |
  "neg_dbm_entry (Lt a) = Le (-a)"

lemma neg_entry:
  "{u. \<not> dbm_entry_val u a b e} = {u. dbm_entry_val u b a (neg_dbm_entry e)}"
  if "e \<noteq> (\<infinity> :: _ DBMEntry)" "a \<noteq> None \<or> b \<noteq> None"
  using that by (cases e; cases a; cases b; auto 4 3 simp: le_minus_iff less_minus_iff)

definition and_entry ::
  "nat \<Rightarrow> nat \<Rightarrow> ('t::{linordered_cancel_ab_monoid_add,uminus}) DBMEntry \<Rightarrow> 't DBM \<Rightarrow> 't DBM" where
  "and_entry a b e M = (\<lambda>i j. if i = a \<and> j = b then min (M i j) e else M i j)"

abbreviation "clock_to_option a \<equiv> (if a > 0 then Some a else None)"

definition
  "dbm_entry_val' u a b e \<equiv> dbm_entry_val u (clock_to_option a) (clock_to_option b) e"

lemma dbm_entry_val'_diff_shift:
  "dbm_entry_val' (u \<oplus> d) c1 c2 (M c1 c2)" if "dbm_entry_val' u c1 c2 (M c1 c2)" "0 < c1" "0 < c2"
  using that unfolding dbm_entry_val'_def cval_add_def
  by (auto elim!: dbm_entry_val.cases intro!: dbm_entry_val.intros)

lemma dbm_entry_val_iff_bounded_Le1:
  "dbm_entry_val u (Some c1) None e \<longleftrightarrow> Le (u c1) \<le> e"
  by (cases e) (auto simp: any_le_inf)

lemma dbm_entry_val_iff_bounded_Le2:
  "dbm_entry_val u None (Some c2) e \<longleftrightarrow> Le (- u c2) \<le> e"
  by (cases e) (auto simp: any_le_inf)

lemma dbm_entry_val_iff_bounded_Le3:
  "dbm_entry_val u (Some c1) (Some c2) e \<longleftrightarrow> Le (u c1 - u c2) \<le> e"
  by (cases e) (auto simp: any_le_inf)

context
  notes [simp] = dbm_entry_val'_def
begin

lemma neg_entry':
  "{u. \<not> dbm_entry_val' u a b e} = {u. dbm_entry_val' u b a (neg_dbm_entry e)}"
  if "e \<noteq> (\<infinity> :: _ DBMEntry)" "a > 0 \<or> b > 0"
  (* using that by (auto simp: neg_entry) *)
  using that by (cases e; cases "a > 0"; cases "b > 0"; auto 4 3 simp: le_minus_iff less_minus_iff)

lemma neg_unbounded:
  "{u. \<not> dbm_entry_val' u i j e} = {}" if "e = (\<infinity> :: _ DBMEntry)"
  using that by auto

lemma and_entry_sound:
  "\<lbrakk>dbm_entry_val' u a b e; u \<turnstile>\<^bsub>v,n\<^esub> M\<rbrakk> \<Longrightarrow> u \<turnstile>\<^bsub>v,n\<^esub> and_entry a b e M"
  unfolding DBM_val_bounded_def
  by (cases a; cases b; auto simp: le_n_iff v_is_id(1) min_def v_0 and_entry_def)

lemma and_entry_mono:
  "and_entry a b e M i j \<le> M i j"
  by (auto simp: and_entry_def)

(* XXX Move *)
lemma DBM_val_bounded_mono:
  "u \<turnstile>\<^bsub>v,n\<^esub> M" if "u \<turnstile>\<^bsub>v,n\<^esub> M'" "\<forall> i \<le> n. \<forall> j \<le> n. M' i j \<le> M i j"
  using that unfolding DBM_val_bounded_def
  apply (safe; clarsimp simp: le_n_iff v_is_id(1) DBM.less_eq[symmetric])
     apply force
    apply (blast intro: dbm_entry_val_mono)+
  done

lemma and_entry_entry:
  "dbm_entry_val' u a b e" if "u \<turnstile>\<^bsub>v,n\<^esub> and_entry a b e M" "a \<le> n" "b \<le> n" "a > 0 \<or> b > 0"
proof -
  from that have "dbm_entry_val' u a b (min (M a b) e)"
    unfolding DBM_val_bounded_def by (fastforce simp: le_n_iff v_is_id(1) and_entry_def)
  then show ?thesis
    by (auto intro: dbm_entry_val_mono)
qed

lemma and_entry_correct:
  "[and_entry a b e M]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub> \<inter> {u. dbm_entry_val' u a b e}"
  if "a \<le> n" "b \<le> n" "a > 0 \<or> b > 0"
  unfolding DBM_zone_repr_def using that
  by (blast intro: and_entry_entry and_entry_sound DBM_val_bounded_mono and_entry_mono)

lemma dbm_list_Int_entry_iff_map:
  "dbm_list xs \<inter> {u. dbm_entry_val' u i j e} = dbm_list (map (\<lambda> m. and_entry i j e m) xs)"
  if "i \<le> n" "j \<le> n" "i > 0 \<or> j > 0"
  unfolding dbm_entry_val'_def
  by (induction xs;
      simp add: and_entry_correct[OF that, symmetric, unfolded dbm_entry_val'_def] Int_Un_distrib2
     )

context
  fixes m :: "nat \<Rightarrow> nat \<Rightarrow> ('a :: {time}) DBMEntry"
  assumes "Le 0 \<preceq> m 0 0"
begin

private lemma A:
  "- ([m]\<^bsub>v,n\<^esub>) =
  (\<Union> (i, j) \<in> {(i, j). i > 0 \<and> j > 0 \<and> i \<le> n \<and> j \<le> n}.
    {u. \<not> dbm_entry_val u (Some i) (Some j) (m i j)})
  \<union> (\<Union> i \<in> {i. i > 0 \<and> i \<le> n}. {u. \<not> dbm_entry_val u (Some i) None (m i 0)})
  \<union> (\<Union> j \<in> {i. i > 0 \<and> i \<le> n}. {u. \<not> dbm_entry_val u None (Some j) (m 0 j)})"
  unfolding DBM_zone_repr_def
  apply auto
  subgoal for u
    unfolding DBM_val_bounded_def
    apply (intro conjI impI allI)
    subgoal
      by (rule \<open>Le 0 \<preceq> m 0 0\<close>)
    subgoal for c
      by (auto simp: le_n_iff v_is_id(1))
    subgoal for c
      by (auto simp: le_n_iff v_is_id(1))
    subgoal for c1 c2
      by (auto elim: allE[where x = c1] simp: le_n_iff v_is_id(1))
    done
  unfolding DBM_val_bounded_def by (simp add: le_n_iff v_is_id(1))+

private lemma B:
  "S \<inter> - ([m]\<^bsub>v,n\<^esub>) =
  (\<Union> (i, j) \<in> {(i, j). i > 0 \<and> j > 0 \<and> i \<le> n \<and> j \<le> n}.
    S \<inter> {u. \<not> dbm_entry_val u (Some i) (Some j) (m i j)})
  \<union> (\<Union> i \<in> {i. i > 0 \<and> i \<le> n}. S \<inter> {u. \<not> dbm_entry_val u (Some i) None (m i 0)})
  \<union> (\<Union> j \<in> {i. i > 0 \<and> i \<le> n}. S \<inter> {u. \<not> dbm_entry_val u None (Some j) (m 0 j)})"
  by (subst A) auto

private lemma UNION_cong:
  "(\<Union> x \<in> S. f x) = (\<Union> x \<in> T. g x)" if "S = T" "\<And> x. x \<in> T \<Longrightarrow> f x = g x"
  by (simp add: that)

private lemma 1:
  "S \<inter> - ([m]\<^bsub>v,n\<^esub>) =
  (\<Union> (i, j) \<in> {(i, j). (i > 0 \<or> j > 0) \<and> i \<le> n \<and> j \<le> n}. S \<inter> {u. \<not> dbm_entry_val' u i j (m i j)})
  "
proof -
  have *: "{(i, j). (0 < i \<or> 0 < j) \<and> i \<le> n \<and> j \<le> n}
  = {(i, j). 0 < i \<and> 0 < j \<and> i \<le> n \<and> j \<le> n}
  \<union> {(i, j). 0 < i \<and> 0 = j \<and> i \<le> n \<and> j \<le> n}
  \<union> {(i, j). 0 = i \<and> 0 < j \<and> i \<le> n \<and> j \<le> n}"
    by auto
  show ?thesis
    by (simp only: B UN_Un *) (intro arg_cong2[where f = "op \<union>"] UNION_cong; force)
qed

private lemma UNION_remove:
  "(\<Union> x \<in> S. f x) = (\<Union> x \<in> T. g x)"
  if "T \<subseteq> S" "\<And> x. x \<in> T \<Longrightarrow> f x = g x" "\<And> x. x \<in> S - T \<Longrightarrow> f x = {}"
  using that by fastforce

private lemma 2:
  "(\<Union>(i, j)\<in>{(i, j).(i > 0 \<or> j > 0) \<and> i \<le> n \<and> j \<le> n}. S \<inter> {u. \<not> dbm_entry_val' u i j (m i j)})
 = (\<Union>(i, j)\<in>{(i, j).(i > 0 \<or> j > 0) \<and> i \<le> n \<and> j \<le> n \<and> m i j \<noteq> \<infinity>}.
    S \<inter> {u. dbm_entry_val' u j i (neg_dbm_entry (m i j))})"
  apply (rule UNION_remove)
    apply force
  subgoal for x
    by (cases x; simp add: neg_entry'[simplified])
  by auto

lemma dbm_list_subtract:
  "dbm_list xs \<inter> - ([m]\<^bsub>v,n\<^esub>) =
  dbm_list (concat (map (\<lambda>(i, j). map (\<lambda> M. and_entry j i (neg_dbm_entry (m i j)) M) xs)
  [(i, j). i\<leftarrow>[0..<Suc n], j\<leftarrow>[0..<Suc n], (i > 0 \<or> j > 0) \<and> i \<le> n \<and> j \<le> n \<and> m i j \<noteq> \<infinity>]))"
proof -
  have *:
    "set [(i, j). i\<leftarrow>[0..<Suc n], j\<leftarrow>[0..<Suc n], (i > 0 \<or> j > 0) \<and> i \<le> n \<and> j \<le> n \<and> m i j \<noteq> \<infinity>]
  = {(i, j).(i > 0 \<or> j > 0) \<and> i \<le> n \<and> j \<le> n \<and> m i j \<noteq> \<infinity>}"
    by (auto simp del: upt.upt_Suc)
  show ?thesis
    apply (subst set_concat)
    apply (subst set_map)
    apply (subst *)
    apply (subst 1, subst 2)
    apply (subst UN_UN_flatten)
    apply (subst UN_simps)
    apply (rule UNION_cong[OF HOL.refl])
    apply (simp split del: if_split split: prod.splits)
    apply (subst dbm_list_Int_entry_iff_map[simplified])
       apply auto
    done
qed

end -- \<open>Context for fixed DBM\<close>

end -- \<open>Simplifier setup\<close>

lemma dbm_list_empty_check:
  "dbm_list xs = {} \<longleftrightarrow> list_all (\<lambda>m. [m]\<^bsub>v,n\<^esub> = {}) xs"
  unfolding list_all_iff by auto

lemmas dbm_list_superset_op =
  dbm_fed_superset_fold''[OF dbm_list_subtract[symmetric], unfolded dbm_list_empty_check]

end (* Trivial clock numbering *)

subsubsection \<open>Down Operation\<close>

paragraph \<open>Auxiliary\<close>

lemma dbm_entry_le_iff:
  "Le a \<le> Le b \<longleftrightarrow> a \<le> b"
  "Le a \<le> Lt b \<longleftrightarrow> a < b"
  "Lt a \<le> Le b \<longleftrightarrow> a \<le> b"
  "Lt a \<le> Lt b \<longleftrightarrow> a \<le> b"
  "0 \<le> Le a \<longleftrightarrow> 0 \<le> a"
  "0 \<le> Lt a \<longleftrightarrow> 0 < a"
  "Le a \<le> 0 \<longleftrightarrow> a \<le> 0"
  "Lt a \<le> 0 \<longleftrightarrow> a \<le> 0"
  "x \<le> \<infinity> \<longleftrightarrow> True"
  "\<infinity> \<le> x \<longleftrightarrow> x = \<infinity>"
proof -
  show "\<infinity> \<le> x \<longleftrightarrow> x = \<infinity>"
    by (cases x; auto)
qed (auto simp: any_le_inf DBM.neutral)

lemma Le_le_sum_iff:
  "Le (y :: _ :: time) \<le> e \<longleftrightarrow> 0 \<le> e + Le (- y)"
  by (cases e) (auto simp: DBM.add dbm_entry_le_iff)

lemma dense':
  "\<exists>c\<ge>a. c \<le> b" if "a \<le> b" for a :: "_ :: time"
  using dense \<open>a \<le> b\<close> by auto

(* XXX Move/rename/private *)
lemma aux1:
  "- c \<le> (a :: _ :: time)" if "a \<ge> 0" "c \<ge> 0"
  using that using dual_order.trans neg_le_0_iff_le by blast

thm sum_gt_neutral_dest sum_gt_neutral_dest'

lemma dbm_entries_dense:
  "\<exists>d\<ge>0. Le (- d) \<le> l \<and> Le (d :: _ :: time) \<le> r" if "0 \<le> l" "l \<le> r"
  using that by (cases l; cases r; auto simp: dbm_entry_le_iff intro: aux1)

lemma dbm_entries_dense'_aux:
  "\<exists>d\<ge>0. l + Le d \<ge> 0 \<and> 0 \<le> r + Le (- d :: _ :: time)" if "l \<le> 0" "l + r \<ge> 0" "r \<ge> 0"
proof ((cases l; cases r), goal_cases)
  case (2 x1 x2)
  have "\<exists>d\<ge>0. 0 \<le> x + d \<and> d < y" if "x \<le> 0" "0 < x + y" "0 < y" for x y :: 'a
    using that by (metis add.right_inverse add_le_cancel_left leD leI linear)
  with 2 that show ?case
    by (auto simp: dbm_entry_le_iff DBM.add)
next
  case (3 x1)
  have "\<exists>d\<ge>0. 0 \<le> x + d" if "x \<le> 0" for x :: 'a
    using that by (metis add.right_inverse eq_iff neg_0_le_iff_le)
  with that 3 show ?case 
    by (auto simp: dbm_entry_le_iff DBM.add)
next
  case (5 a b)
  have "\<exists>d\<ge>0. 0 < x + d \<and> d < y" if "x \<le> 0" "0 < x + y" for x y :: 'a
    using that by (smt add.right_inverse add_less_cancel_left leD le_less_trans linear neg_0_le_iff_le time_class.dense)
  with 5 that show ?case 
    by (auto simp: dbm_entry_le_iff DBM.add)
next
  case (6 x2)
  have "\<exists>d\<ge>0. 0 < x + d" if "x \<le> 0" for x :: 'a
    by (metis add.inverse_neutral add_minus_cancel add_strict_increasing2 eq_iff less_le less_minus_iff non_trivial_neg not_less_iff_gr_or_eq)
  with that 6 show ?case 
    by (auto simp: dbm_entry_le_iff DBM.add)
qed (use that in \<open>auto simp: dbm_entry_le_iff DBM.add\<close>)

lemma dbm_entries_dense':
  "\<exists>d\<ge>0. l + Le d \<ge> 0 \<and> 0 \<le> r + Le (- d :: _ :: time)" if "l \<le> 0" "l + r \<ge> 0"
proof -
  from that have "r \<ge> 0"
    by (meson add_decreasing order_refl order_trans)
  with that show ?thesis
    by (rule dbm_entries_dense'_aux)
qed

lemma le_minus_iff:
  "- x \<le> (y :: _ :: time) \<longleftrightarrow> 0 \<le> y + x"
  by (metis add.commute add.right_inverse add_le_cancel_left)

lemma lt_minus_iff:
  "- x < (y :: _ :: time) \<longleftrightarrow> 0 < y + x"
  by (metis add.commute add_less_cancel_right neg_eq_iff_add_eq_0)

context Default_Nat_Clock_Numbering
begin

lemma DBM_val_bounded_alt_def1:
  "u \<turnstile>\<^bsub>v,n\<^esub> m \<equiv>
     Le 0 \<preceq> m 0 0 \<and>
     (\<forall>c. c > 0 \<and> c \<le> n \<longrightarrow>
          dbm_entry_val u None (Some c) (m 0 c) \<and>
          dbm_entry_val u (Some c) None (m c 0)) \<and>
     (\<forall>c1 c2. c1 > 0 \<and> c1 \<le> n \<and> c2 > 0 \<and> c2 \<le> n \<longrightarrow> dbm_entry_val u (Some c1) (Some c2) (m c1 c2))"
  unfolding DBM_val_bounded_def by (rule eq_reflection) (auto simp: v_id le_n_iff)

lemma DBM_val_bounded_alt_def2:
  "u \<turnstile>\<^bsub>v,n\<^esub> m \<equiv>
     Le 0 \<preceq> m 0 0 \<and>
     (\<forall>c1 c2. (c1 \<noteq> 0 \<or> c2 \<noteq> 0) \<and> c1 \<le> n \<and> c2 \<le> n \<longrightarrow> dbm_entry_val' u c1 c2 (m c1 c2))"
  unfolding DBM_val_bounded_alt_def1 dbm_entry_val'_def
  by (rule eq_reflection; clarsimp; safe; blast)

lemma DBM_val_bounded_altI:
  assumes
    "Le 0 \<preceq> m 0 0"
    "\<And> c1 c2. (c1 \<noteq> 0 \<or> c2 \<noteq> 0) \<and> c1 \<le> n \<and> c2 \<le> n \<Longrightarrow> dbm_entry_val' u c1 c2 (m c1 c2)"
  shows
    "u \<in> \<lbrakk>m\<rbrakk>"
  unfolding DBM_zone_repr_def DBM_val_bounded_alt_def2 using assms by auto

lemma dbm_entry_val'_delay1:
  "dbm_entry_val' u c1 c2 (m c1 c2)" if "dbm_entry_val' (u \<oplus> d) c1 c2 (m c1 c2)" "d \<ge> 0" "c1 > 0"
  using that unfolding dbm_entry_val'_def
  by (cases "m c1 c2")
     (auto 0 2
        dest: add_strict_increasing2 add_increasing intro!: dbm_entry_val.intros
        simp: cval_add_def
     )

lemma dbm_entry_val'_delay2:
  "dbm_entry_val' u (0 :: nat) c2 (m c1 c2)" if
  "dbm_entry_val' (u \<oplus> d) c1 c2 (m c1 c2)" "d \<ge> 0"
  "c1 > 0" "c2 > 0" "c1 \<le> n" "c2 \<le> n"
  "\<forall> c \<le> n. u c \<ge> 0"
  using that  unfolding dbm_entry_val'_def
  apply (auto elim!: dbm_entry_val.cases intro!: dbm_entry_val.intros simp: cval_add_def)
   apply (auto simp: algebra_simps le_minus_iff lt_minus_iff intro: dual_order.trans dual_order.strict_trans2)
  done

lemma dbm_entry_val'_nonneg_bound:
  "dbm_entry_val' u (0 :: nat) c (Le 0)" if "u c \<ge> 0" "c > 0"
  using that unfolding dbm_entry_val'_def by auto

end (* Default Clock Numbering *)

paragraph \<open>Definition\<close>

definition
  down :: "nat \<Rightarrow> ('t::linordered_cancel_ab_monoid_add) DBM \<Rightarrow> 't DBM"
where
  "down n M \<equiv>
    \<lambda> i j. if i = 0 \<and> j > 0 then Min ({Le 0} \<union> {M k j | k. 1 \<le> k \<and> k \<le> n}) else M i j"


paragraph \<open>Correctness\<close>

context Default_Nat_Clock_Numbering
begin

context
  fixes M :: "('t::time) DBM"
  assumes canonical: "canonical M n"
begin

lemma down_complete: "u \<in> \<lbrakk>down n M\<rbrakk>" if "u \<in> \<lbrakk>M\<rbrakk>\<^sup>\<down>" "\<forall> c \<le> n. u c \<ge> 0"
proof (rule DBM_val_bounded_altI, goal_cases)
  case 1
  with \<open>u \<in> _\<close> show ?case
    unfolding down_def DBM_zone_repr_def DBM_val_bounded_alt_def2 zone_time_pre_def by auto
next
  case prems: (2 c1 c2)
  then consider "c1 > 0" | "c1 = 0" "c2 > 0"
    by auto
  then show ?case
  proof cases
    case 1
    with prems \<open>u \<in> _\<close> show ?thesis
      unfolding down_def DBM_zone_repr_def DBM_val_bounded_alt_def2 zone_time_pre_def
      by (auto intro: dbm_entry_val'_delay1 split: if_split_asm)
  next
    case 2
    from \<open>u \<in> \<lbrakk>M\<rbrakk>\<^sup>\<down>\<close> obtain d where d: "0 \<le> d"
      "(\<forall>c1 c2. (c1 \<noteq> 0 \<or> c2 \<noteq> 0) \<and> c1 \<le> n \<and> c2 \<le> n \<longrightarrow> dbm_entry_val' (u \<oplus> d) c1 c2 (M c1 c2))"
      unfolding zone_time_pre_def DBM_zone_repr_def DBM_val_bounded_alt_def2 by auto
    let ?e = "Min ({Le 0} \<union> {M k c2 |k. 1 \<le> k \<and> k \<le> n})"
    have "?e \<in> {Le 0} \<union> {M k c2 |k. 1 \<le> k \<and> k \<le> n}"
      by (intro Min_in) auto
    then consider "?e = Le 0" | k where "?e = M k c2" "k > 0" "k \<le> n"
      by auto
    then show ?thesis
      using prems that(2) d 2
      by cases (auto intro: dbm_entry_val'_delay2 dbm_entry_val'_nonneg_bound simp: down_def)
  qed
qed

lemma down_sound: "u \<in> \<lbrakk>M\<rbrakk>\<^sup>\<down>" if "u \<in> \<lbrakk>down n M\<rbrakk>"
proof -
  from \<open>u \<in> _\<close> have "Le 0 \<preceq> M 0 0"
    unfolding down_def DBM_zone_repr_def DBM_val_bounded_alt_def2 by auto
  from \<open>u \<in> _\<close> have *:
    "(\<forall>c1 c2. (c1 \<noteq> 0 \<or> c2 \<noteq> 0) \<and> c1 \<le> n \<and> c2 \<le> n \<longrightarrow> dbm_entry_val' u c1 c2 (down n M c1 c2))"
    unfolding zone_time_pre_def DBM_zone_repr_def DBM_val_bounded_alt_def2 by auto
  define l where "l = Min ({M 0 c + Le (u c)   | c. 0 < c \<and> c \<le> n} \<union> {Le 0})"
    -- \<open>maximum current violation of the future bounds\<close>
  define r where "r = Min ({M c 0 + Le (- u c) | c. 0 < c \<and> c \<le> n} \<union> {\<infinity>})"
    -- \<open>slack for shifting upwards\<close>
  have "0 \<le> l + r" "l \<le> 0"
  proof -
    have
      "l \<in> {M 0 c + Le (u c)   | c. 0 < c \<and> c \<le> n} \<union> {Le 0}"
      "r \<in> {M c 0 + Le (- u c) | c. 0 < c \<and> c \<le> n} \<union> {\<infinity>}"
      unfolding l_def r_def by (intro Min_in; simp)+
    from \<open>l \<in> _\<close> show "l \<le> 0"
      unfolding l_def by (auto intro: Min_le simp: DBM.neutral)
    from \<open>l \<in> _\<close> \<open>r \<in> _\<close> show "0 \<le> l + r"
    proof (auto simp: algebra_simps, goal_cases)
      case 1
      then show ?case
        by (simp add: any_le_inf)
    next
      case (2 c)
      with \<open>u \<in> _\<close> have "Le (u c) \<le> M c 0"
        unfolding dbm_entry_val_iff_bounded_Le1 down_def DBM_zone_repr_def DBM_val_bounded_alt_def1
        by auto
      then show ?case
        by (auto simp: DBM.add Le_le_sum_iff)
    next
      case (3 c)
      then show ?case
        by (simp add: any_le_inf)
    next
      case (4 c1 c2)
      with \<open>canonical M n\<close> have "M c2 0 + M 0 c1 \<ge> M c2 c1"
        by auto
      have "Le (u c1) + (M c2 0 + (M 0 c1 + Le (- u c2))) =
      Le (u c1) + Le (- u c2) + (M c2 0 + M 0 c1)"
        by (simp add: algebra_simps)
      from 4 \<open>u \<in> _\<close> have "Le (u c2 - u c1) \<le> M c2 c1"
        unfolding dbm_entry_val_iff_bounded_Le3 down_def DBM_zone_repr_def DBM_val_bounded_alt_def1
        by auto
      with \<open>M c2 c1 \<le> _\<close> have "Le (u c2 - u c1) \<le> M c2 0 + M 0 c1"
        by auto
      then have "0 \<le> M c2 0 + M 0 c1 + (Le (u c1) + Le (- u c2))"
        by (simp add: DBM.add Le_le_sum_iff)
      then show ?case
        by (simp add: algebra_simps)
    qed
  qed
  from dbm_entries_dense'[OF this(2,1)] obtain d where
    "d \<ge> 0" "0 \<le> l + Le d" "0 \<le> r + Le (- d)"
    by auto
  have "u \<oplus> d \<in> \<lbrakk>M\<rbrakk>"
  proof (rule DBM_val_bounded_altI, goal_cases)
    case 1
    from \<open>Le 0 \<preceq> M 0 0\<close> show ?case .
  next
    case (2 c1 c2)
    with * have **: "dbm_entry_val' u c1 c2 (down n M c1 c2)"
      by auto
    from 2 consider
      "c1 \<le> n" "c2 \<le> n" "c1 > 0" "c2 > 0"
      | "c1 = 0" "c2 \<le> n" "c2 > 0" | "c2 = 0" "c1 \<le> n" "c1 > 0"
      by auto
    then show ?case
    proof cases
      case 1
      then show ?thesis
        using ** unfolding down_def by (auto intro: dbm_entry_val'_diff_shift)
    next
      case 2
      then have "l \<le> (M 0 c2 + Le (u c2))"
        unfolding l_def by (auto intro: Min_le)
      with \<open>0 \<le> l + Le d\<close> have "0 \<le> M 0 c2 + Le (u c2) + Le d"
        by (metis add.commute add_left_mono dual_order.trans) (* XXX Recurring proof pattern *)
      with 2 show ?thesis
        unfolding down_def dbm_entry_val'_def
        by (cases "M 0 c2")
           (auto 4 3 simp: cval_add_def DBM.add dbm_entry_le_iff
            algebra_simps lt_minus_iff le_minus_iff
           )
    next
      case 3
      then have "r \<le> M c1 0 + Le (- u c1)"
        unfolding r_def by (auto intro: Min_le)
      with \<open>0 \<le> r + Le (- d)\<close> have "0 \<le> M c1 0 + Le (- u c1) + Le ( -d)"
        by (metis add.commute add_left_mono dual_order.trans)
      with 3 ** show ?thesis
        unfolding down_def dbm_entry_val'_def
        apply (auto elim!: dbm_entry_val.cases intro!: dbm_entry_val.intros simp: cval_add_def)
         apply (auto simp: algebra_simps DBM.add dbm_entry_le_iff)
        done
    qed
  qed
  with \<open>d \<ge> 0\<close> show ?thesis
    unfolding zone_time_pre_def cval_add_def by auto
qed

end (* Fixed DBM w/ Canonicality *)

end (* Default Clock Numbering *)
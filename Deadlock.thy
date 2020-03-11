theory Deadlock
  imports
    TA.Timed_Automata TA_Library.CTL TA.DBM_Operations TA.Normalized_Zone_Semantics
    TA_Impl.Normalized_Zone_Semantics_Impl
    TA_Impl.Normalized_Zone_Semantics_Impl_Refine
    TA_Impl.FW_More
begin

no_notation Ref.update ("_ := _" 62)
(* hide_const D *) (* XXX *)
no_notation Relators.fun_rel_syn (infixr "\<rightarrow>" 60)
no_notation Extended_Nat.infinity ("\<infinity>")

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

lemma zone_time_pre_mono:
  "A\<^sup>\<down> \<subseteq> B\<^sup>\<down>" if "A \<subseteq> B"
  using that unfolding zone_time_pre_def by auto

lemma clock_set_split:
  "P (([r \<rightarrow> 0]u) x) \<longleftrightarrow> (x \<notin> set r \<longrightarrow> P (u x)) \<and> (x \<in> set r \<longrightarrow> P 0)"
  by (cases "x \<in> set r") auto






context Regions_TA
begin

definition
  "check_deadlock l Z \<equiv> Z \<subseteq>
    \<Union> {(zone_set_pre {u. u \<turnstile> inv_of A l'} r \<inter> {u. u \<turnstile> g} \<inter> {u. u \<turnstile> inv_of A l})\<^sup>\<down> | g a r l'.
        A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'}"

lemma V_zone_time_pre:
  "x \<in> (Z \<inter> V)\<^sup>\<down>" if "x \<in> Z\<^sup>\<down>" "x \<in> V"
  using that unfolding zone_time_pre_def by (auto simp: V_def cval_add_def)

lemma check_deadlock_alt_def:
  "check_deadlock l Z = (Z \<subseteq> \<Union> {
    (zone_set_pre ({u. u \<turnstile> inv_of A l'} \<inter> V) r \<inter> {u. \<forall> x \<in> set r. u x \<ge> 0}
       \<inter> {u. u \<turnstile> g} \<inter> {u. u \<turnstile> inv_of A l})\<^sup>\<down> \<inter> V
    | g a r l'. A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'})" (is "_ = (?L \<subseteq> ?R)") if "Z \<subseteq> V"
proof -
  { fix g a r l' x
    assume t: "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"
    assume x: "x \<in> (zone_set_pre {u. u \<turnstile> inv_of A l'} r \<inter> {u. u \<turnstile> g} \<inter> {u. u \<turnstile> inv_of A l})\<^sup>\<down>"
    assume "x \<in> V"
    let ?A = "zone_set_pre {u. u \<turnstile> inv_of A l'} r \<inter> {u. u \<turnstile> g} \<inter> {u. u \<turnstile> inv_of A l}"
    let ?B = "zone_set_pre ({u. u \<turnstile> inv_of A l'} \<inter> V) r \<inter> {u. \<forall> x \<in> set r. u x \<ge> 0}
              \<inter> {u. u \<turnstile> g} \<inter> {u. u \<turnstile> inv_of A l}"
    from valid_abstraction have "collect_clkvt (trans_of A) \<subseteq> X"
      by (auto elim: valid_abstraction.cases)
    have *: "0 \<le> u c" if "c \<in> set r" "u \<in> V" for c u
    proof -
      from t \<open>c \<in> set r\<close> have "c \<in> collect_clkvt (trans_of A)"
        unfolding collect_clkvt_def by force
      with \<open>_ \<subseteq> X\<close> have "c \<in> X"
        by auto
      with \<open>u \<in> V\<close> show ?thesis
        by (auto simp: V_def)
    qed
    have **: "u \<in> zone_set_pre ({u. u \<turnstile> inv_of A l'} \<inter> V) r"
      if "u \<in> zone_set_pre {u. u \<turnstile> inv_of A l'} r" "u \<in> V" for u
      using that unfolding zone_set_pre_def V_def by (auto split: clock_set_split)
    from x \<open>x \<in> V\<close> have "x \<in> (?A \<inter> V)\<^sup>\<down>"
      by (rule V_zone_time_pre)
    moreover have "y \<in> ?B" if "y \<in> ?A \<inter> V" for y
      using that by (auto intro: * **)
    ultimately have "x \<in> ?B\<^sup>\<down>"
      unfolding zone_time_pre_def by auto
  } note * = this
  have "zone_set_pre (Z \<inter> V) r \<subseteq> zone_set_pre Z r" for Z r
    unfolding zone_set_pre_def by auto
  with \<open>Z \<subseteq> V\<close> show ?thesis
    unfolding check_deadlock_def
    apply safe
    subgoal for x
      apply rotate_tac
      apply (drule subsetD, assumption)
      apply (drule subsetD, assumption)
      apply clarsimp
      apply (frule *, assumption+)
      subgoal for g a r l'
        by (inst_existentials
            "(zone_set_pre ({u. u \<turnstile> inv_of A l'} \<inter> V) r \<inter> {u. \<forall>x\<in>set r. 0 \<le> u x} \<inter> {u. u \<turnstile> g} \<inter>
             {u. u \<turnstile> inv_of A l})\<^sup>\<down> \<inter> V") auto
      done
    apply (drule subsetD, assumption)+
    apply safe
    subgoal for x X g a r l'
      by (drule
          subsetD[OF zone_time_pre_mono,
            where B1 = "zone_set_pre {u. u \<turnstile> inv_of A l'} r \<inter> {u. u \<turnstile> g} \<inter> {u. u \<turnstile> inv_of A l}",
              rotated]; force)
    done
qed

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
    by (rule sim_complete_bisim'.P1_deadlocked_compatible[where a = "from_R l R"];
       (rule sim_complete_bisim'.P1_P1')?) (auto intro: sim_complete_bisim'.P1_P1')
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

definition and_entry ::
  "nat \<Rightarrow> nat \<Rightarrow> ('t::{linordered_cancel_ab_monoid_add,uminus}) DBMEntry \<Rightarrow> 't DBM \<Rightarrow> 't DBM" where
  "and_entry a b e M = (\<lambda>i j. if i = a \<and> j = b then min (M i j) e else M i j)"

lemma and_entry_mono:
  "and_entry a b e M i j \<le> M i j"
  by (auto simp: and_entry_def)

abbreviation "clock_to_option a \<equiv> (if a > 0 then Some a else None)"

definition
  "dbm_entry_val' u a b e \<equiv> dbm_entry_val u (clock_to_option a) (clock_to_option b) e"

definition
  "dbm_minus n xs m = concat (map (\<lambda>(i, j). map (\<lambda> M. and_entry j i (neg_dbm_entry (m i j)) M) xs)
  [(i, j). i\<leftarrow>[0..<Suc n], j\<leftarrow>[0..<Suc n], (i > 0 \<or> j > 0) \<and> i \<le> n \<and> j \<le> n \<and> m i j \<noteq> \<infinity>])"

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

lemma surj_on: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
  using v_is_id by blast

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

lemma dbm_entry_val'_iff_bounded:
  "dbm_entry_val' u c1 c2 e \<longleftrightarrow> Le((if c1 > 0 then u c1 else 0) - (if c2 > 0 then u c2 else 0)) \<le> e"
  if "c1 > 0 \<or> c2 > 0"
  using that unfolding dbm_entry_val'_def
  by (auto simp:
      dbm_entry_val_iff_bounded_Le1 dbm_entry_val_iff_bounded_Le2 dbm_entry_val_iff_bounded_Le3
     )

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
  "u \<turnstile>\<^bsub>v,n\<^esub> and_entry a b e M" if "dbm_entry_val' u a b e" "u \<turnstile>\<^bsub>v,n\<^esub> M"
  using that unfolding DBM_val_bounded_def
  by (cases a; cases b; auto simp: le_n_iff v_is_id(1) min_def v_0 and_entry_def)

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
    by (simp only: B UN_Un *) (intro arg_cong2[where f = "(\<union>)"] UNION_cong; force)
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
  "dbm_list xs \<inter> - ([m]\<^bsub>v,n\<^esub>) = dbm_list (dbm_minus n xs m)"
proof -
  have *:
    "set [(i, j). i\<leftarrow>[0..<Suc n], j\<leftarrow>[0..<Suc n], (i > 0 \<or> j > 0) \<and> i \<le> n \<and> j \<le> n \<and> m i j \<noteq> \<infinity>]
  = {(i, j).(i > 0 \<or> j > 0) \<and> i \<le> n \<and> j \<le> n \<and> m i j \<noteq> \<infinity>}"
    by (auto simp del: upt.upt_Suc)
  show ?thesis
    unfolding dbm_minus_def
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

end \<comment> \<open>Context for fixed DBM\<close>

end \<comment> \<open>Simplifier setup\<close>

lemma dbm_list_empty_check:
  "dbm_list xs = {} \<longleftrightarrow> list_all (\<lambda>m. [m]\<^bsub>v,n\<^esub> = {}) xs"
  unfolding list_all_iff by auto

lemmas dbm_list_superset_op =
  dbm_fed_superset_fold''[OF dbm_list_subtract[symmetric], unfolded dbm_list_empty_check]

end (* Trivial clock numbering *)

context TA_Start_No_Ceiling
begin

sublocale dbm: Default_Nat_Clock_Numbering n v
  by unfold_locales (auto simp: v_def)

end


subsubsection \<open>Down\<close>

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
  "\<infinity> \<le> x \<longleftrightarrow> x = \<infinity>"
  "x \<le> \<infinity> \<longleftrightarrow> True"
proof -
  show "\<infinity> \<le> x \<longleftrightarrow> x = \<infinity>"
    by (cases x; auto)
qed (auto simp: any_le_inf DBM.neutral)

lemma dbm_entry_lt_iff:
  "Le a < Le b \<longleftrightarrow> a < b"
  "Le a < Lt b \<longleftrightarrow> a < b"
  "Lt a < Le b \<longleftrightarrow> a \<le> b"
  "Lt a < Lt b \<longleftrightarrow> a < b"
  "0 < Le a \<longleftrightarrow> 0 < a"
  "0 < Lt a \<longleftrightarrow> 0 < a"
  "Le a < 0 \<longleftrightarrow> a < 0"
  "Lt a < 0 \<longleftrightarrow> a \<le> 0"
  "x < \<infinity> \<longleftrightarrow> x \<noteq> \<infinity>"
  "\<infinity> < x \<longleftrightarrow> False"
  by (auto simp: any_le_inf DBM.neutral DBM.less)

lemmas [dbm_entry_simps] = dbm_entry_le_iff(1-9) dbm_entry_lt_iff(1-9)

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

lemma (in time) non_trivial_pos: "\<exists> x. x > 0"
  by (meson leD le_less_linear neg_le_0_iff_le non_trivial_neg)

lemma dbm_entries_dense_pos:
  "\<exists>d>0. Le (d :: _ :: time) \<le> e" if "e > 0"
  (* XXX Clean duplicate rewrite rule *)
  using dbm_entry_simps[simp]
proof (cases e)
case (Le d)
  with that show ?thesis
    by auto
next
  case prems: (Lt d)
  with that have "d > 0"
    by auto
  from dense[OF this] obtain z where "z > 0" "z < d"
    by auto
  then show ?thesis
    by (auto simp: prems)
next
  case prems: INF
  obtain d :: 'a where "d > 0"
    by atomize_elim (rule non_trivial_pos)
  then show ?thesis
    by (auto simp: prems)
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
     Le 0 \<le> m 0 0 \<and>
     (\<forall>c1 c2. (c1 \<noteq> 0 \<or> c2 \<noteq> 0) \<and> c1 \<le> n \<and> c2 \<le> n \<longrightarrow> dbm_entry_val' u c1 c2 (m c1 c2))"
  unfolding DBM_val_bounded_alt_def1 dbm_entry_val'_def DBM.less_eq
  by (rule eq_reflection; clarsimp; safe; blast)

lemma DBM_val_bounded_altI:
  assumes
    "Le 0 \<le> m 0 0"
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
  "\<forall> c \<le> n. c > 0 \<longrightarrow> u c \<ge> 0"
  using that  unfolding dbm_entry_val'_def
  apply (auto elim!: dbm_entry_val.cases intro!: dbm_entry_val.intros simp: cval_add_def)
   apply (auto simp: algebra_simps le_minus_iff lt_minus_iff intro: dual_order.trans dual_order.strict_trans2)
  done

lemma dbm_entry_val'_nonneg_bound:
  "dbm_entry_val' u (0 :: nat) c (Le 0)" if "u c \<ge> 0" "c > 0"
  using that unfolding dbm_entry_val'_def by auto

lemma neg_diag_empty_spec:
  "\<lbrakk>M\<rbrakk> = {}" if "i \<le> n" "M i i < 0"
  using that by (meson neg_diag_empty v_is_id(1))

lemma in_DBM_D:
  "dbm_entry_val' u c1 c2 (M c1 c2)" if "u \<in> \<lbrakk>M\<rbrakk>" "c1 \<noteq> 0 \<or> c2 \<noteq> 0" "c1 \<le> n" "c2 \<le> n"
  using that unfolding zone_time_pre_def DBM_zone_repr_def DBM_val_bounded_alt_def2 by auto

context
  fixes M :: "('t::time) DBM"
  assumes "\<lbrakk>M\<rbrakk> \<noteq> {}"
begin

lemma non_empty_diag_0_0: "M 0 0 \<ge> 0"
  using \<open>\<lbrakk>M\<rbrakk> \<noteq> {}\<close> neg_diag_empty_spec[of 0 M] leI by auto

lemma M_k_0: "M k 0 \<ge> 0" if "\<forall> u \<in> \<lbrakk>M\<rbrakk>. \<forall> c \<le> n. c > 0 \<longrightarrow> u c \<ge> 0" "k \<le> n"
proof (cases "k = 0")
  case True with non_empty_diag_0_0 show ?thesis
    by auto
next
  case False
  from \<open>\<lbrakk>M\<rbrakk> \<noteq> {}\<close> obtain u where "u \<in> \<lbrakk>M\<rbrakk>"
    by auto
  with False that(1) \<open>k \<le> n\<close> have "u k \<ge> 0"
    by auto
  from \<open>u \<in> _\<close> \<open>k \<noteq> 0\<close> \<open>k \<le> n\<close> have "dbm_entry_val' u k 0 (M k 0)"
    unfolding DBM_zone_repr_def DBM_val_bounded_alt_def2 by auto
  with \<open>k \<noteq> 0\<close> have "Le (u k) \<le> M k 0"
    by (simp add: dbm_entry_val'_iff_bounded)
  with \<open>u k \<ge> 0\<close> show "M k 0 \<ge> 0"
    by (cases "M k 0") (auto simp: dbm_entry_le_iff)
qed

lemma non_empty_cycle_free:
  "cycle_free M n"
  using \<open>\<lbrakk>M\<rbrakk> \<noteq> {}\<close> non_empty_cycle_free v_is_id(1) by blast

lemma canonical_saturated_2:
  assumes "Le r \<le> M 0 c"
    and "Le (- r) \<le> M c 0"
    and "cycle_free M n"
    and "canonical M n"
    and "c \<le> n"
    and "c > 0"
  obtains u where "u \<in> \<lbrakk>M\<rbrakk>" "u c = - r"
  using assms v_0 by (auto simp: v_is_id intro: canonical_saturated_2[of r M v c n])

lemma M_0_k: "M 0 k \<le> 0"
  if "canonical M n" "M 0 0 \<le> 0" "\<forall> u \<in> \<lbrakk>M\<rbrakk>. \<forall> c \<le> n. c > 0 \<longrightarrow> u c \<ge> 0" "k \<le> n"
proof (cases "k = 0")
  case True
  with \<open>M 0 0 \<le> 0\<close> show ?thesis
    by auto
next
  case False
  show ?thesis
  proof (rule ccontr)
    assume "\<not> M 0 k \<le> 0"
    then have "M 0 k > 0"
      by auto
    from that(3) \<open>k \<le> n\<close> have "M k 0 \<ge> 0"
      by (rule M_k_0)
    from \<open>M 0 k > 0\<close> obtain d where
      "Le d \<le> M 0 k" "d > 0"
      by (rule dbm_entries_dense_pos[elim_format]) auto
    with \<open>M k 0 \<ge> 0\<close> have "Le (-d) \<le> M k 0"
      by (auto simp: dbm_entry_le_iff intro: order.trans[rotated])
    with \<open>canonical M n\<close> \<open>Le d \<le> M 0 k\<close> obtain u where
      "u \<in> \<lbrakk>M\<rbrakk>" "u k = -d"
      using v_0 False \<open>k \<le> n\<close>
      by - (rule canonical_saturated_2[of d], auto simp: non_empty_cycle_free)
    with \<open>d > 0\<close> that(3) False \<open>k \<le> n\<close> show False
      by fastforce
  qed
qed

end (* Fixed non-empty DBM *)

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

sublocale Alpha_defs "{1..n}" .

context
  fixes M :: "('t::time) DBM"
begin

lemma down_complete: "u \<in> \<lbrakk>down n M\<rbrakk>" if "u \<in> \<lbrakk>M\<rbrakk>\<^sup>\<down>" "\<forall> c \<le> n. c > 0 \<longrightarrow> u c \<ge> 0"
proof (rule DBM_val_bounded_altI, goal_cases)
  case 1
  with \<open>u \<in> _\<close> show ?case
    unfolding down_def zone_time_pre_def by (auto intro: non_empty_diag_0_0 simp: neutral[symmetric])
next
  case prems: (2 c1 c2)
  then consider "c1 > 0" | "c1 = 0" "c2 > 0"
    by auto
  then show ?case
  proof cases
    case 1
    with prems \<open>u \<in> _\<close> show ?thesis
      unfolding zone_time_pre_def down_def by (auto intro: dbm_entry_val'_delay1 dest: in_DBM_D)
  next
    case 2
    from \<open>u \<in> \<lbrakk>M\<rbrakk>\<^sup>\<down>\<close> obtain d where d: "0 \<le> d" "u \<oplus> d \<in> \<lbrakk>M\<rbrakk>"
      unfolding zone_time_pre_def by auto
    let ?e = "Min ({Le 0} \<union> {M k c2 |k. 1 \<le> k \<and> k \<le> n})"
    have "?e \<in> {Le 0} \<union> {M k c2 |k. 1 \<le> k \<and> k \<le> n}"
      by (intro Min_in) auto
    then consider "?e = Le 0" | k where "?e = M k c2" "k > 0" "k \<le> n"
      by auto
    then show ?thesis
      using prems that(2) d 2 unfolding down_def
      by cases (auto intro: dbm_entry_val'_delay2 dbm_entry_val'_nonneg_bound in_DBM_D)
  qed
qed

lemma down_sound: "u \<in> \<lbrakk>M\<rbrakk>\<^sup>\<down>" if "u \<in> \<lbrakk>down n M\<rbrakk>" "canonical M n"
proof -
  note [simp] = dbm_entry_simps and [intro] = order.trans add_right_mono
  from \<open>u \<in> _\<close> non_empty_diag_0_0[of "down n M"] have "Le 0 \<le> M 0 0"
    by (auto simp: down_def neutral)
  note * = in_DBM_D[OF \<open>u \<in> _\<close>]
  define l where "l = Min ({M 0 c + Le (u c)   | c. 0 < c \<and> c \<le> n} \<union> {Le 0})"
    \<comment> \<open>maximum current violation of the future bounds\<close>
  define r where "r = Min ({M c 0 + Le (- u c) | c. 0 < c \<and> c \<le> n} \<union> {\<infinity>})"
    \<comment> \<open>slack for shifting upwards\<close>
  have "0 \<le> l + r" "l \<le> 0"
  proof -
    have
      "l \<in> {M 0 c + Le (u c)   | c. 0 < c \<and> c \<le> n} \<union> {Le 0}"
      "r \<in> {M c 0 + Le (- u c) | c. 0 < c \<and> c \<le> n} \<union> {\<infinity>}"
      unfolding l_def r_def by (intro Min_in; simp)+
    from \<open>l \<in> _\<close> show "l \<le> 0"
      unfolding l_def by (auto intro: Min_le simp: DBM.neutral)
    from \<open>l \<in> _\<close> \<open>r \<in> _\<close> show "0 \<le> l + r"
    proof (safe, goal_cases)
      case prems: (1 c1 c2)
      with \<open>u \<in> _\<close> have "Le (u c2 - u c1) \<le> M c2 c1"
        by (auto 0 2 dest: in_DBM_D simp: dbm_entry_val'_iff_bounded down_def)
      also from prems \<open>canonical M n\<close> have "M c2 0 + M 0 c1 \<ge> M c2 c1"
        by auto
      finally have "0 \<le> M c2 0 + M 0 c1 + (Le (u c1) + Le (- u c2))"
        by (simp add: DBM.add Le_le_sum_iff)
      then show ?case
        by (simp add: algebra_simps)
    next
      case (3 c)
      with \<open>u \<in> _\<close> have "Le (u c) \<le> M c 0"
        by (auto 0 2 dest: in_DBM_D simp: dbm_entry_val'_iff_bounded down_def)
      then show ?case
        by (auto simp: DBM.add Le_le_sum_iff)
    qed auto
  qed
  from dbm_entries_dense'[OF this(2,1)] obtain d where
    "d \<ge> 0" "0 \<le> l + Le d" "0 \<le> r + Le (- d)"
    by auto
  have "u \<oplus> d \<in> \<lbrakk>M\<rbrakk>"
  proof (rule DBM_val_bounded_altI, goal_cases)
    case 1
    from \<open>Le 0 \<le> M 0 0\<close> show ?case .
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
        by auto
      with 2 show ?thesis
        unfolding down_def dbm_entry_val'_def
        by (cases "M 0 c2")
           (auto 4 3 simp: cval_add_def DBM.add algebra_simps lt_minus_iff le_minus_iff)
    next
      case 3
      then have "r \<le> M c1 0 + Le (- u c1)"
        unfolding r_def by (auto intro: Min_le)
      with \<open>0 \<le> r + Le (- d)\<close> have "0 \<le> M c1 0 + Le (- u c1) + Le ( -d)"
        by auto
      with 3 ** show ?thesis
        unfolding down_def dbm_entry_val'_def
        by (auto elim!: dbm_entry_val.cases simp: cval_add_def algebra_simps DBM.add)
    qed
  qed
  with \<open>d \<ge> 0\<close> show ?thesis
    unfolding zone_time_pre_def cval_add_def by auto
qed

lemma down_canonical:
  "canonical (down n M) n"
  if assms: "canonical M n" "\<lbrakk>M\<rbrakk> \<noteq> {}" "\<forall> u \<in> \<lbrakk>M\<rbrakk>. \<forall> c \<le> n. c > 0 \<longrightarrow> u c \<ge> 0" "M 0 0 \<le> 0"
proof -
  from non_empty_diag_0_0[OF \<open>\<lbrakk>M\<rbrakk> \<noteq> {}\<close>] have "M 0 0 \<ge> 0" .
  with \<open>M 0 0 \<le> 0\<close> have "M 0 0 = 0"
    by auto
  note M_0_k = M_0_k[OF that(2,1,4,3)] and M_k_0 = M_k_0[OF that(2,3)]
  have Suc_0_le_iff: "Suc 0 \<le> x \<longleftrightarrow> 0 < x" for x
    by auto
  define S where "S j = Min ({Le 0} \<union> {M k j |k. 1 \<le> k \<and> k \<le> n})" for j
  { fix j :: nat
    consider (0) "S j = 0" "\<forall> i. 1 \<le> i \<and> i \<le> n \<longrightarrow> M i j \<ge> 0"
      | (entry) i where
        "S j = M i j" "0 < i" "i \<le> n" "M i j \<le> 0" "\<forall> k. 1 \<le> k \<and> k \<le> n \<longrightarrow> M i j \<le> M k j"
      unfolding S_def neutral
      using Min_in[of "{Le 0} \<union> {M k j |k. 1 \<le> k \<and> k \<le> n}"]
      apply auto
      using Min_le[of "{Le 0} \<union> {M k j |k. 1 \<le> k \<and> k \<le> n}"]
       apply auto
      done
  } note S_cases = this
  show ?thesis
    apply (intro allI impI; elim conjE)
    unfolding down_def S_def[symmetric]
    apply clarsimp
    apply safe
  proof goal_cases
    case (1 i j k)
    from \<open>M 0 0 \<ge> 0\<close> show ?case
      by (blast intro: add_increasing)
  next
    case (2 i j k)
    with \<open>canonical M n\<close> show ?case
      by (cases rule: S_cases[of k]; cases rule: S_cases[of j])
         (auto intro: order.trans simp: Suc_0_le_iff)
  next
    case prems: (3 i j k)
    then have "M 0 k \<le> S k"
      apply (cases rule: S_cases[of k])
      subgoal
        using M_0_k[of k] by auto
      subgoal for i'
        using M_0_k \<open>canonical M n\<close> by (metis add.left_neutral add_right_mono dual_order.trans)
      done
    from \<open>canonical M n\<close> prems have "M i k \<le> M i 0 + M 0 k"
      by auto
    also from \<open>_ \<le> S k\<close> have "\<dots> \<le> M i 0 + S k"
      by (simp add: add_left_mono)
    finally show ?case .
  next
    case (6 i j k)
    with \<open>canonical M n\<close> \<open>M 0 0 \<le> 0\<close> show ?case
      by (smt M_k_0 S_cases add_increasing order.trans)
  qed (use \<open>canonical M n\<close> in simp_all)
qed

end (* Fixed DBM *)

end (* Default Clock Numbering *)

subsubsection \<open>Free\<close>

paragraph \<open>Definition\<close>

definition
  free :: "nat \<Rightarrow> ('t::linordered_cancel_ab_monoid_add) DBM \<Rightarrow> nat \<Rightarrow> 't DBM"
where
  "free n M x \<equiv>
    \<lambda> i j. if i = x \<and> j \<noteq> x then \<infinity> else if i \<noteq> x \<and> j = x then M i 0 else M i j"

definition repair_pair where
  "repair_pair n M a b = FWI (FWI M n b) n a"

definition
  "and_entry_repair n a b e M \<equiv> repair_pair n (and_entry a b e M) a b"

definition
  "restrict_zero n M x \<equiv>
    let
      M1 = and_entry x 0 (Le 0) M;
      M2 = and_entry 0 x (Le 0) M1
    in repair_pair n M2 x 0"

definition
  "pre_reset n M x \<equiv> free n (restrict_zero n M x) x"

definition
  "pre_reset_list n M r \<equiv> fold (\<lambda> x M. pre_reset n M x) r M"

paragraph \<open>Auxiliary\<close>

lemma repair_pair_characteristic:
  assumes "canonical_subs n I M"
    and "I \<subseteq> {0..n}"
    and "a \<le> n" "b \<le> n"
  shows "canonical_subs n (I \<union> {a,b}) (repair_pair n M a b) \<or> (\<exists>i\<le>n. repair_pair n M a b i i < 0)"
proof -
  from fwi_characteristic[OF assms(1,2,4)] have
    "canonical_subs n (I \<union> {b}) (FWI M n b) \<or> (\<exists>i\<le>n. FWI M n b i i < 0)"
    by auto
  then show ?thesis
  proof
    assume "canonical_subs n (I \<union> {b}) (FWI M n b)"
    from fwi_characteristic[OF this _ \<open>a \<le> n\<close>] assms(2) \<open>b \<le> n\<close> show ?thesis
      unfolding repair_pair_def by simp
  next
    assume "\<exists>i\<le>n. FWI M n b i i < 0"
    then have "\<exists>i\<le>n. repair_pair n M a b i i < 0"
      unfolding repair_pair_def
      apply safe
      subgoal for i
        apply (inst_existentials i)
         apply assumption
        apply (frule FWI_mono[where M = "FWI M n b" and k = a])
         apply auto
        done
      done
    then show ?thesis ..
  qed
qed

lemma repair_pair_mono:
  assumes "i \<le> n"
      and "j \<le> n"
    shows "repair_pair n M a b i j \<le> M i j"
  unfolding repair_pair_def by (auto intro: FWI_mono assms order.trans)

context Default_Nat_Clock_Numbering
begin

lemmas FWI_zone_equiv = FWI_zone_equiv[OF surj_on, symmetric]

lemma repair_pair_zone_equiv:
  "\<lbrakk>repair_pair n M a b\<rbrakk> = \<lbrakk>M\<rbrakk>" if "a \<le> n" "b \<le> n"
  using that unfolding repair_pair_def by (simp add: FWI_zone_equiv)

context
  fixes c1 c2 c x :: nat
  notes [simp] = dbm_entry_val'_iff_bounded dbm_entry_simps DBM.add algebra_simps
begin

lemma dbm_entry_val'_diag_iff: "dbm_entry_val' u c c e \<longleftrightarrow> e \<ge> 0" if "c > 0"
  using that by (cases e) auto

lemma dbm_entry_val'_inf: "dbm_entry_val' u c1 c2 \<infinity> \<longleftrightarrow> True"
  unfolding dbm_entry_val'_def by auto

lemma dbm_entry_val'_reset_1:
  "dbm_entry_val' (u(x := d)) x c e \<longleftrightarrow> dbm_entry_val' u 0 c (e + Le (-d))"
  if "d \<ge> 0" "c \<noteq> x" "c > 0" "x > 0"
  using that \<open>d \<ge> 0\<close> by (cases e) auto

lemma dbm_entry_val'_reset_2:
  "dbm_entry_val' (u(x := d)) c x e \<longleftrightarrow> dbm_entry_val' u c (0 :: nat) (e + Le d)"
  if "d \<ge> 0" "c \<noteq> x" "c > 0" "x > 0"
  using that \<open>d \<ge> 0\<close> by (cases e) auto

lemma dbm_entry_val'_reset_2':
  "dbm_entry_val' (u(x := d)) 0 x e \<longleftrightarrow> Le (- d) \<le> e" if "d \<ge> 0" "x > 0"
  using that \<open>d \<ge> 0\<close> by (cases e) auto

lemma dbm_entry_val'_reset_3:
  "dbm_entry_val' (u(x := d)) c1 c2 e \<longleftrightarrow> dbm_entry_val' u c1 c2 e" if "c1 \<noteq> x" "c2 \<noteq> x" for e
  using that unfolding dbm_entry_val'_def by (cases e) auto

end (* Simplifier setup *)


paragraph \<open>Correctness\<close>

context
  fixes M :: "('t::time) DBM"
begin

lemma free_complete: "u(x := d) \<in> \<lbrakk>free n M x\<rbrakk>"
  if assms: "u \<in> \<lbrakk>M\<rbrakk>" "d \<ge> 0" "x > 0" "\<forall>c \<le> n. M c c \<ge> 0"
proof (rule DBM_val_bounded_altI, goal_cases)
  case 1
  with \<open>_ \<in> \<lbrakk>M\<rbrakk>\<close> show ?case
    unfolding free_def by (auto simp: neutral[symmetric] intro: non_empty_diag_0_0)
next
  case prems: (2 c1 c2)
  then have "c1 \<le> n" "c2 \<le> n"
    by auto
  note [simp] = dbm_entry_simps
  have *: "Le (u c1) \<le> M c1 0 + Le d" if "c1 > 0"
  proof -
    from \<open>_ \<in> \<lbrakk>M\<rbrakk>\<close> \<open>c1 > 0\<close> \<open>c1 \<le> n\<close> have "Le (u c1) \<le> M c1 0"
      by (auto 0 2 simp: dbm_entry_val'_iff_bounded dest: in_DBM_D)
    with \<open>d \<ge> 0\<close> show ?thesis
      by (simp add: algebra_simps add_increasing)
  qed
  have "dbm_entry_val' (u(x := d)) c1 x (M c1 0)" if "c1 \<noteq> x"
  proof (cases "c1 = 0")
    case True
    with that show ?thesis
      using assms(4) \<open>d \<ge> 0\<close> by (auto intro: order.trans[rotated] simp: dbm_entry_val'_reset_2')
  next
    case False
    with that \<open>x > 0\<close> show ?thesis
      by (subst dbm_entry_val'_reset_2[OF \<open>d \<ge> 0\<close>]) (auto simp: dbm_entry_val'_iff_bounded *)
  qed
  with prems in_DBM_D[OF \<open>_ \<in> \<lbrakk>M\<rbrakk>\<close>] that(4) show ?case
    by (auto simp: free_def dbm_entry_val'_diag_iff dbm_entry_val'_inf dbm_entry_val'_reset_3)
qed

lemma free_sound: "\<exists>d \<ge> 0. u(x := d) \<in> \<lbrakk>M\<rbrakk>" "u x \<ge> 0"
  if assms: "u \<in> \<lbrakk>free n M x\<rbrakk>" "x > 0" "x \<le> n" "canonical M n" "M 0 x \<le> 0" "M 0 0 \<le> 0"
proof -
  define l where "l = Min ({M c x + Le (- u c) | c. 0 < c \<and> c \<le> n \<and> c \<noteq> x} \<union> {M 0 x})"
  define r where "r = Min ({M x c + Le (u c)   | c. 0 < c \<and> c \<le> n \<and> c \<noteq> x} \<union> {M x 0})"
  from non_empty_diag_0_0 \<open>u \<in> _\<close> \<open>x > 0\<close> have "0 \<le> M 0 0"
    unfolding free_def by fastforce
  note [simp]  = dbm_entry_simps and [intro] = order.trans add_right_mono
  have "0 \<le> l + r" "l \<le> 0"
  proof -
    have
      "l \<in> {M c x + Le (- u c)   | c. 0 < c \<and> c \<le> n \<and> c \<noteq> x} \<union> {M 0 x}"
      "r \<in> {M x c + Le (u c)     | c. 0 < c \<and> c \<le> n \<and> c \<noteq> x} \<union> {M x 0}"
      unfolding l_def r_def by (intro Min_in; simp)+
    from \<open>l \<in> _\<close> \<open>M 0 x \<le> 0\<close> show "l \<le> 0"
      unfolding l_def by - (rule order.trans[rotated], auto intro: Min_le simp: DBM.neutral)
    from \<open>l \<in> _\<close> \<open>r \<in> _\<close> show "0 \<le> l + r"
    proof (safe, goal_cases)
      case prems: (1 c1 c2)
      with \<open>canonical M n\<close> \<open>x \<le> n\<close> have "M c1 x + M x c2 \<ge> M c1 c2"
        by auto
      from prems \<open>u \<in> _\<close> have "Le (u c1 - u c2) \<le> M c1 c2"
        unfolding free_def by (auto 0 2 simp: dbm_entry_val'_iff_bounded dest: in_DBM_D)
      with \<open>M c1 c2 \<le> M c1 x + M x c2\<close> have "Le (u c1 - u c2) \<le> M c1 x + M x c2"
        by auto
      then have "0 \<le> M c1 x + M x c2 + (Le (u c2) + Le (- u c1))"
        by (simp add: DBM.add Le_le_sum_iff)
      then show ?case
        by (simp add: algebra_simps)
    next
      case prems: (2 c)
      from prems \<open>u \<in> _\<close> have "Le (u c) \<le> M c 0"
        unfolding free_def by (auto 0 2 simp: dbm_entry_val'_iff_bounded dest: in_DBM_D)
      also from prems \<open>canonical M n\<close> \<open>x \<le> n\<close> have "\<dots> \<le> M c x + M x 0"
        by auto
      finally show ?case
        by (simp add: algebra_simps Le_le_sum_iff)
    next
      case prems: (3 c)
      with \<open>u \<in> _\<close> \<open>x > 0\<close> have "Le (- u c) \<le> M 0 c"
        unfolding free_def by (auto simp: dbm_entry_val'_iff_bounded dest: in_DBM_D[of _ _ 0 c])
      also from prems \<open>canonical M n\<close> \<open>x \<le> n\<close> have "\<dots> \<le> M 0 x + M x c"
        by auto
      finally show ?case
        by (simp add: algebra_simps Le_le_sum_iff)
    next
      case 4
      from \<open>0 \<le> M 0 0\<close> \<open>canonical M n\<close> \<open>x \<le> n\<close> show ?case
        by auto
    qed
  qed
  from dbm_entries_dense'[OF this(2,1)] obtain d where
    "d \<ge> 0" "0 \<le> l + Le d" "0 \<le> r + Le (- d)"
    by auto
  have "u(x := d) \<in> \<lbrakk>M\<rbrakk>"
  proof (rule DBM_val_bounded_altI, goal_cases)
    case 1
    from \<open>0 \<le> M 0 0\<close> show ?case unfolding DBM.neutral .
  next
    case prems: (2 c1 c2)
    then have **: "dbm_entry_val' u c1 c2 (free n M x c1 c2)"
      by (auto intro: in_DBM_D[OF \<open>u \<in> _\<close>])
    with prems \<open>x > 0\<close> show ?case
    proof (auto simp: dbm_entry_val'_iff_bounded free_def split: if_split_asm, goal_cases)
      case prems: 1
      then have "r \<le> M x c2 + Le (u c2)"
        unfolding r_def by (intro Min_le) auto
      with \<open>0 \<le> r + _\<close> have "0 \<le> M x c2 + Le (u c2) + Le (- d)"
        by auto
      moreover have "Le (d - u c2) \<le> M x c2 \<longleftrightarrow> 0 \<le> M x c2 + Le (u c2) + Le (- d)"
        by (cases "M x c2") (auto simp: DBM.add algebra_simps)
      ultimately show "Le (d - u c2) \<le> M x c2"
        by simp
    next
      case prems: 2
      from \<open>0 \<le> r + _\<close> have "Le d \<le> r"
        by (simp add: Le_le_sum_iff)
      also have "r \<le> M x 0"
        unfolding r_def by auto
      finally show "Le d \<le> M x 0" .
    next
      case prems: 3
      then have "l \<le> M c1 x + Le (- u c1)"
        unfolding l_def by (intro Min_le) auto
      with \<open>0 \<le> l + Le d\<close> have "0 \<le> M c1 x + Le (- u c1) + Le d"
        by auto
      moreover have "Le (u c1 - d) \<le> M c1 x \<longleftrightarrow> 0 \<le> M c1 x + Le (- u c1) + Le d"
        by (cases "M c1 x") (auto simp: DBM.add algebra_simps)
      ultimately show "Le (u c1 - d) \<le> M c1 x"
        by simp
    next
      case prems: 4
      from \<open>0 \<le> l + Le d\<close> have "Le (- d) \<le> l"
        by (simp add: Le_le_sum_iff)
      also have "l \<le> M 0 x"
        unfolding l_def by auto
      finally show "Le (- d) \<le> M 0 x" .
    qed
  qed
  with \<open>d \<ge> 0\<close> show "\<exists>d\<ge>0. u(x := d) \<in> \<lbrakk>M\<rbrakk>"
    by auto
  from \<open>x > 0\<close> \<open>x \<le> n\<close> have "dbm_entry_val' u 0 x (free n M x 0 x)"
    by (auto intro: in_DBM_D[OF \<open>u \<in> _\<close>])
  with \<open>0 < x\<close> have "Le (- u x) \<le> M 0 0"
    by (auto simp: free_def dbm_entry_val'_iff_bounded)
  with \<open>M 0 0 \<le> 0\<close> have "Le (- u x) \<le> 0"
    by blast
  then show "0 \<le> u x"
    by auto
qed

lemma free_correct:
  "\<lbrakk>free n M x\<rbrakk> = {u(x := d) | u d. u \<in> \<lbrakk>M\<rbrakk> \<and> d \<ge> 0}"
  if "x > 0" "x \<le> n" "\<forall>c \<le> n. M c c \<ge> 0" "\<forall> u \<in> \<lbrakk>M\<rbrakk>. u x \<ge> 0" "canonical M n"
    "M 0 x \<le> 0" "M 0 0 \<le> 0"
  using that
  apply safe
  subgoal for u'
    apply (frule free_sound, assumption+)
    apply (frule free_sound(2), assumption+)
    apply (erule exE)
    subgoal for d
      by (inst_existentials "u'(x := d)" "u' x"; simp)
    done
  subgoal for u d
    by (auto intro: free_complete)
  done

lemma pre_reset_correct_aux:
  "{u. (u(x := (0::'t))) \<in> \<lbrakk>M\<rbrakk>} \<inter> {u. u x \<ge> 0} = {u(x := d) | u d. u \<in> \<lbrakk>M\<rbrakk> \<and> u x = 0 \<and> d \<ge> 0}"
  apply auto
  subgoal for u
    by (inst_existentials "u(x := (0::'t))" "u x") auto
  subgoal for u d
    by (subgoal_tac "u = u(x := 0)") auto
  done

lemma restrict_zero_correct:
  "\<lbrakk>restrict_zero n M x\<rbrakk> = {u. u \<in> \<lbrakk>M\<rbrakk> \<and> u x = 0}" if "0 < x" "x \<le> n"
  using that unfolding restrict_zero_def
  by (auto simp: repair_pair_zone_equiv and_entry_correct dbm_entry_val'_iff_bounded dbm_entry_simps)

lemma restrict_zero_canonical:
  "canonical (restrict_zero n M x) n \<or> check_diag n (uncurry (restrict_zero n M x))"
  if "canonical M n" "x \<le> n"
proof -
  from \<open>x \<le> n\<close> have *: "{0..n} - {0, x} \<union> {x, 0} = {0..n}"
    by auto
  define M1 and M2 where "M1 = and_entry x 0 (Le 0) M" "M2 = and_entry 0 x (Le 0) M1"
  from \<open>canonical M n\<close> have "canonical_subs n {0..n} M"
    unfolding canonical_alt_def .
  with * have "canonical_subs n ({0..n} - {0, x}) M2"
    unfolding and_entry_def M1_M2_def canonical_subs_def by (auto simp: min.coboundedI1)
  from repair_pair_characteristic[OF this, of x 0] \<open>x \<le> n\<close> have
    "canonical (repair_pair n M2 x 0) n \<or> check_diag n (uncurry (repair_pair n M2 x 0))"
    unfolding canonical_alt_def check_diag_def * neutral by auto
  then show ?thesis
    unfolding restrict_zero_def M1_M2_def Let_def .
qed

end (* Fixed DBM *)

subsection \<open>Structural Properties\<close>

lemma free_canonical:
  "canonical (free n M x) n" if "canonical M n" "M x x \<ge> 0"
  unfolding free_def using that by (auto simp: add_increasing2 any_le_inf)

lemma free_diag:
  "free n M x i i = M i i"
  unfolding free_def by auto

lemma check_diag_free:
  "check_diag n (uncurry (free n M x))" if "check_diag n (uncurry M)"
  using that unfolding check_diag_def by (auto simp: free_diag)

lemma
  "\<forall>i\<le>n. (free n M x) i i \<le> 0" if "\<forall>i\<le>n. M i i \<le> 0"
  using that by (auto simp: free_diag)

lemma canonical_nonneg_diag_non_empty:
  assumes "canonical M n" "\<forall>i\<le>n. 0 \<le> M i i"
  shows "[M]\<^bsub>v,n\<^esub> \<noteq> {}"
  using v_0 by (intro canonical_nonneg_diag_non_empty[OF assms]) force

lemma V_structuralI:
  "\<lbrakk>M\<rbrakk> \<subseteq> V" if "\<forall> i \<le> n. i > 0 \<longrightarrow> M 0 i \<le> 0"
  using that
  unfolding V_def
proof clarsimp
  fix u i assume "u \<in> \<lbrakk>M\<rbrakk>" "Suc 0 \<le> i" "i \<le> n"
  from in_DBM_D[OF \<open>u \<in> _\<close>, of 0 i] \<open>_ \<le> i\<close> \<open>i \<le> n\<close> have "dbm_entry_val' u 0 i (M 0 i)"
    by auto
  with \<open>_ \<le> i\<close> \<open>i \<le> n\<close> have "Le (- u i) \<le> M 0 i"
    by (auto simp: dbm_entry_val'_iff_bounded)
  also from that \<open>_ \<le> i\<close> \<open>i \<le> n\<close> have "\<dots> \<le> 0"
    by simp
  finally show "0 \<le> u i"
    by (auto simp: dbm_entry_simps)
qed

lemma canonical_V_non_empty_iff:
  assumes "canonical M n" "M 0 0 \<le> 0"
  shows "\<lbrakk>M\<rbrakk> \<subseteq> V \<and> \<lbrakk>M\<rbrakk> \<noteq> {} \<longleftrightarrow> (\<forall> i \<le> n. i > 0 \<longrightarrow> M 0 i \<le> 0) \<and> (\<forall> i \<le> n. M i i \<ge> 0)"
proof (safe, goal_cases)
  case (1 u i)
  with \<open>M 0 0 \<le> 0\<close> show ?case
    unfolding V_def by - (rule M_0_k[OF _ \<open>canonical M n\<close>], auto)
next
  case (2 x i)
  then show ?case
    using neg_diag_empty_spec[of i M] by fastforce
next
  case prems: (3 u)
  then show ?case
    by (auto dest: subsetD[OF V_structuralI])
next
  case 4
  with canonical_nonneg_diag_non_empty[OF \<open>canonical M n\<close>] show ?case
    by simp
qed

lemma
  assumes "(\<forall> i \<le> n. i > 0 \<longrightarrow> M 0 i \<le> 0) \<and> (\<forall> i \<le> n. M i i \<ge> 0)" "M 0 0 \<le> 0" "x > 0"
  shows "(\<forall> i \<le> n. i > 0 \<longrightarrow> free n M x 0 i \<le> 0) \<and> (\<forall> i \<le> n. free n M x i i \<ge> 0)"
  using assms by (auto simp: free_def)

lemma
  assumes "(\<forall> i \<le> n. i > 0 \<longrightarrow> M 0 i \<le> 0) \<and> (\<forall> i \<le> n. M i i \<ge> 0) \<Longrightarrow>
           (\<forall> i \<le> n. i > 0 \<longrightarrow> f M 0 i \<le> 0) \<and> (\<forall> i \<le> n. f M i i \<ge> 0)"
  assumes "canonical M n" "canonical (f M) n"
  assumes "M 0 0 \<le> 0" "f M 0 0 \<le> 0"
  assumes check_diag: "check_diag n (uncurry M) \<Longrightarrow> check_diag n (uncurry (f M))"
  assumes "\<lbrakk>M\<rbrakk> \<subseteq> V"
  shows "\<lbrakk>f M\<rbrakk> \<subseteq> V"
proof (cases "\<lbrakk>M\<rbrakk> = {}")
  case True
  then have "check_diag n (uncurry M)"
  using canonical_nonneg_diag_non_empty[OF \<open>canonical M n\<close>] by (force simp: neutral check_diag_def)
  then have "check_diag n (uncurry (f M))"
    by (rule check_diag)
  then have "\<lbrakk>f M\<rbrakk> = {}"
    by (auto dest: neg_diag_empty_spec simp: check_diag_def neutral)
  then show ?thesis
    by auto
next
  case False
  with \<open>\<lbrakk>M\<rbrakk> \<subseteq> V\<close> canonical_V_non_empty_iff[OF \<open>canonical M n\<close> \<open>M 0 0 \<le> 0\<close>] have
    "(\<forall>i\<le>n. 0 < i \<longrightarrow> M 0 i \<le> 0) \<and> (\<forall>i\<le>n. 0 \<le> M i i)"
    by auto
  then have "(\<forall> i \<le> n. i > 0 \<longrightarrow> f M 0 i \<le> 0) \<and> (\<forall> i \<le> n. f M i i \<ge> 0)"
    by (rule assms(1))
  with \<open>canonical (f M) n\<close> have "\<lbrakk>f M\<rbrakk> \<subseteq> V \<and> \<lbrakk>f M\<rbrakk> \<noteq> {}"
    using \<open>f M 0 0 \<le> 0\<close> by (subst canonical_V_non_empty_iff) (auto simp: free_diag)
  then show ?thesis ..
qed

lemma
  "\<lbrakk>free n M x\<rbrakk> \<subseteq> V" if assms: "x > 0" "canonical M n" "M 0 0 \<le> 0" "0 \<le> M x x" "\<lbrakk>M\<rbrakk> \<subseteq> V"
proof (cases "\<lbrakk>M\<rbrakk> = {}")
  case True
  then obtain i where "M i i < 0" "i \<le> n"
    using canonical_nonneg_diag_non_empty[OF \<open>canonical M n\<close>] by atomize_elim force
  then have "free n M x i i < 0"
    by (auto simp: free_diag)
  with \<open>i \<le> n\<close> have "\<lbrakk>free n M x\<rbrakk> = {}"
    by (intro neg_diag_empty_spec)
  then show ?thesis
    by auto
next
  case False
  with \<open>\<lbrakk>M\<rbrakk> \<subseteq> V\<close> canonical_V_non_empty_iff[OF that(2,3)] have
    "(\<forall>i\<le>n. 0 < i \<longrightarrow> M 0 i \<le> 0) \<and> (\<forall>i\<le>n. 0 \<le> M i i)"
    by auto
  with that have "(\<forall> i \<le> n. i > 0 \<longrightarrow> free n M x 0 i \<le> 0) \<and> (\<forall> i \<le> n. free n M x i i \<ge> 0)"
    by (auto simp: free_def)
  moreover have "canonical (free n M x) n"
    apply (rule free_canonical)
     apply fact
    apply fact
    done
  ultimately have "\<lbrakk>free n M x\<rbrakk> \<subseteq> V \<and> \<lbrakk>free n M x\<rbrakk> \<noteq> {}"
    using \<open>M 0 0 \<le> 0\<close> by (subst canonical_V_non_empty_iff) (auto simp: free_diag)
  then show ?thesis ..
qed

lemma
  "down n M i i = M i i"
  unfolding down_def by auto

lemma
  assumes "(\<forall> i \<le> n. i > 0 \<longrightarrow> M 0 i \<le> 0) \<and> (\<forall> i \<le> n. M i i \<ge> 0)" "M 0 0 \<le> 0" "x > 0"
  shows "(\<forall> i \<le> n. i > 0 \<longrightarrow> down n M 0 i \<le> 0) \<and> (\<forall> i \<le> n. down n M i i \<ge> 0)"
  using assms by (auto simp: down_def neutral)

lemma check_diag_empty:
  "\<lbrakk>M\<rbrakk> = {}" if "check_diag n (uncurry M)"
  using check_diag_empty[of n v "uncurry M"] that v_is_id by auto

lemma restrict_zero_mono:
  "restrict_zero n M x i j \<le> M i j" if "i \<le> n" "j \<le> n"
  unfolding restrict_zero_def
  by simp (rule \<open>i \<le> n\<close> \<open>j \<le> n\<close> repair_pair_mono and_entry_mono order.trans)+

lemma restrict_zero_diag:
  "check_diag n (uncurry (restrict_zero n M x))" if "check_diag n (uncurry M)"
  using that unfolding check_diag_def neutral[symmetric]
  by (elim exE conjE) (frule restrict_zero_mono[where M = M and x = x], auto)

lemma pre_reset_correct:
  "\<lbrakk>pre_reset n M x\<rbrakk> = {u. (u(x := (0::'t::time))) \<in> \<lbrakk>M\<rbrakk>} \<inter> {u. u x \<ge> 0}"
  if "x > 0" "x \<le> n" "canonical M n \<or> check_diag n (uncurry M)" "M 0 x \<le> 0" "M 0 0 \<le> 0"
proof -
  have check_diag: ?thesis if A: "check_diag n (uncurry (restrict_zero n M x))"
  proof -
    from A have "check_diag n (uncurry (pre_reset n M x))"
      unfolding pre_reset_def by (rule check_diag_free)
    then have "\<lbrakk>pre_reset n M x\<rbrakk> = {}"
      by (rule check_diag_empty)
    from A have "\<lbrakk>restrict_zero n M x\<rbrakk> = {}"
      by (rule check_diag_empty)
    then have "{u. (u(x := (0::'t::time))) \<in> \<lbrakk>M\<rbrakk>} \<inter> {u. u x \<ge> 0} = {}"
      using \<open>0 < x\<close> \<open>x \<le> n\<close> by (auto simp: restrict_zero_correct)
    with \<open>\<lbrakk>pre_reset n M x\<rbrakk> = {}\<close> show ?thesis
      by simp
  qed
  from that(3) show ?thesis
  proof
    assume "canonical M n"
    from restrict_zero_canonical[OF \<open>canonical M n\<close> \<open>x \<le> n\<close>] have
      "canonical (restrict_zero n M x) n \<or> check_diag n (uncurry (restrict_zero n M x))"
      (is "?A \<or> ?B") .
    then consider ?A "\<not> ?B" | ?B
      by blast
    then show ?thesis
    proof cases
      case 1
      assume ?A "\<not> ?B"
      moreover from \<open>\<not> ?B\<close> have "\<forall>c\<le>n. 0 \<le> restrict_zero n M x c c"
        unfolding check_diag_def by (auto simp: DBM.neutral)
      moreover have "\<forall>u\<in>\<lbrakk>restrict_zero n M x\<rbrakk>. 0 \<le> u x"
        by (simp add: restrict_zero_correct that)
      moreover from \<open>x \<le> n\<close> \<open>M 0 x \<le> 0\<close> have "restrict_zero n M x 0 x \<le> 0"
        by (blast intro: order.trans restrict_zero_mono)
      moreover from \<open>x \<le> n\<close> \<open>M 0 0 \<le> 0\<close> have "restrict_zero n M x 0 0 \<le> 0"
        by (blast intro: order.trans restrict_zero_mono)
      ultimately show ?thesis
        using that
        by (auto simp: pre_reset_correct_aux restrict_zero_correct free_correct pre_reset_def)
    next
      assume ?B then show ?thesis
        by (rule check_diag)
    qed
  next
    assume "check_diag n (uncurry M)"
    then have "check_diag n (uncurry (restrict_zero n M x))"
      by (rule restrict_zero_diag)
    then show ?thesis
      by (rule check_diag)
  qed
qed

lemma zone_set_pre_Cons:
  "zone_set_pre \<lbrakk>M\<rbrakk> (x # r) = zone_set_pre {u. (u(x := (0::'t::time))) \<in> \<lbrakk>M\<rbrakk>} r"
  unfolding zone_set_pre_def by auto

lemma pre_reset_list_Cons:
  "pre_reset_list n M (x # r) = pre_reset_list n (pre_reset n M x) r"
  unfolding pre_reset_list_def by simp

lemma pre_reset_diag:
  "check_diag n (uncurry (pre_reset n M x))" if "check_diag n (uncurry M)"
  using that unfolding pre_reset_def by (intro check_diag_free restrict_zero_diag)

lemma free_canonical':
  "canonical (free n (M :: (_ :: time) DBM) x) n \<or> check_diag n (uncurry (free n M x))"
  if "canonical M n \<or> check_diag n (uncurry M)" "x \<le> n"
  by (smt check_diag_def check_diag_free dbm_entry_le_iff(5) free_canonical leI
          order_mono_setup.refl order_trans that uncurry_apply
     )

lemma pre_reset_canonical':
  "canonical (pre_reset n (M :: (_ :: time) DBM) x) n \<or> check_diag n (uncurry (pre_reset n M x))"
  if "canonical M n \<or> check_diag n (uncurry M)" "x \<le> n"
  using that(1)
proof standard
  assume "canonical M n"
  with \<open>x \<le> n\<close> have
    "canonical (restrict_zero n M x) n \<or> check_diag n (uncurry (restrict_zero n M x))"
    by (intro restrict_zero_canonical)
  with \<open>x \<le> n\<close> show ?thesis
    unfolding pre_reset_def by (intro free_canonical')
next
  assume "check_diag n (uncurry M)"
  from pre_reset_diag[OF this] show ?thesis ..
qed

lemma pre_reset_list_correct:
  "\<lbrakk>pre_reset_list n M r\<rbrakk> = zone_set_pre \<lbrakk>M\<rbrakk> r \<inter> {u. \<forall> x \<in> set r. u x \<ge> 0}"
  if "\<forall> x \<in> set r. x > 0 \<and> x \<le> n"
    "canonical M n \<or> check_diag n (uncurry M)" "\<forall> x \<in> set r. M 0 x \<le> 0" "M 0 0 \<le> 0"
  using that
  apply (induction r arbitrary: M)
   apply (simp add: zone_set_pre_def pre_reset_list_def)
  subgoal premises prems for x r M
    apply (subst zone_set_pre_Cons)
    apply (subst pre_reset_list_Cons)
    apply (subst prems)
        prefer 5
        apply (subst pre_reset_correct)
             prefer 6
    subgoal
      unfolding zone_set_pre_def by (cases "x \<in> set r") auto
    using prems(2-) apply (auto; fail)+
    subgoal
      using prems(2-) by (intro pre_reset_canonical'; auto)
    subgoal
      unfolding pre_reset_def free_def using prems(2-)
      by (auto 4 3 intro: order.trans restrict_zero_mono)
    subgoal
      unfolding pre_reset_def free_def using prems(2-)
      by (auto 4 3 intro: order.trans restrict_zero_mono)
    done
  done

end (* Default Clock Numbering *)

text \<open>
Computes \<open>dbm_list xs - \<lbrakk>M\<rbrakk> = dbm_list xs \<inter> (- \<lbrakk>M\<rbrakk>)\<close> by negating each entry of \<open>M\<close>
and intersecting it with each member of \<open>xs\<close>.
\<close>
definition
  "dbm_minus_canonical n xs M =
   [and_entry_repair n j i (neg_dbm_entry (M i j)) M'.
     (i, j) \<leftarrow> [(i, j).
        i\<leftarrow>[0..<Suc n], j\<leftarrow>[0..<Suc n], (i > 0 \<or> j > 0) \<and> i \<le> n \<and> j \<le> n \<and> M i j \<noteq> \<infinity>],
     M'     \<leftarrow> xs
   ]"

text \<open>
Same as @{text dbm_minus_canonical} but filters out empty DBMs.
\<close>
definition
  "dbm_minus_canonical_check n xs M =
  filter (\<lambda>M. \<not> check_diag n (uncurry M)) (dbm_minus_canonical n xs M)"

text \<open>Checks whether \<open>\<lbrakk>M\<rbrakk> - dbm_list xs = {}\<close>.\<close>
definition
  "dbm_subset_fed n M xs \<equiv>
    let xs = filter (\<lambda>M. \<not> check_diag n (uncurry M)) xs in
    list_all (\<lambda> M. check_diag n (uncurry M)) (fold (\<lambda>m S. dbm_minus_canonical n S m) xs [M])"

definition
  "dbm_subset_fed_check n M xs \<equiv>
    let
      xs = filter (\<lambda>M. \<not> check_diag n (uncurry M)) xs;
      is_direct_subset = list_ex (\<lambda> M'. dbm_subset' n (uncurry M) (uncurry M')) xs
    in is_direct_subset \<or>
       list_all (\<lambda>M. check_diag n (uncurry M)) (fold (\<lambda>m S. dbm_minus_canonical_check n S m) xs [M])"

definition "canonical' n M \<equiv> canonical M n \<or> check_diag n (uncurry M)"

lemma canonical'I:
  "canonical' n (f M)" if
  "canonical' n M"
  "canonical M n \<Longrightarrow> canonical' n (f M)" "check_diag n (uncurry M) \<Longrightarrow> check_diag n (uncurry (f M))"
  using that unfolding canonical'_def by metis

lemma check_diag_repair_pair:
  assumes "check_diag n (uncurry M)"
  shows "check_diag n (uncurry (repair_pair n M i j))"
  using assms repair_pair_mono[where M = M and a = i and b = j] unfolding check_diag_def by force

lemma check_diag_and_entry:
  assumes "check_diag n (uncurry M)"
  shows "check_diag n (uncurry (and_entry a b e M))"
  using assms unfolding check_diag_def
  apply (elim exE)
  subgoal for i
    using and_entry_mono[where M = M and a = a and b = b and e = e, of i i] by auto
  done

lemma canonical'_and_entry_repair:
  "canonical' n (and_entry_repair n i j e M)" if "canonical' n M" "i \<le> n" "j \<le> n"
  using that(1)
proof (rule canonical'I)
  assume "canonical M n"
  from \<open>i \<le> n\<close> \<open>j \<le> n\<close> have *: "{0..n} - {i, j} \<union> {i, j} = {0..n}"
    by auto
  define M1 where "M1 = and_entry i j e M"
  from \<open>canonical M n\<close> have "canonical_subs n {0..n} M"
    unfolding canonical_alt_def .
  with * have "canonical_subs n ({0..n} - {i, j}) M1"
    unfolding and_entry_def M1_def canonical_subs_def by (auto simp: min.coboundedI1)
  from repair_pair_characteristic[OF this, of i j] \<open>i \<le> n\<close> \<open>j \<le> n\<close> have
    "canonical' n (repair_pair n M1 i j)"
    unfolding canonical'_def
    unfolding canonical_alt_def check_diag_def * neutral by auto
  then show ?thesis
    unfolding and_entry_repair_def M1_def Let_def .
next
  assume "check_diag n (uncurry M)"
  then show "check_diag n (uncurry (and_entry_repair n i j e M))"
    unfolding and_entry_repair_def by (intro check_diag_repair_pair check_diag_and_entry)
qed

lemma dbm_minus_canonical_canonical':
  "\<forall>M \<in> set (dbm_minus_canonical n xs m). canonical' n M" if "\<forall>M \<in> set xs. canonical' n M"
  using that unfolding dbm_minus_canonical_def
  by (auto split: if_split_asm intro: canonical'_and_entry_repair)

lemma dbm_minus_canonical_check_canonical':
  "\<forall>M \<in> set (dbm_minus_canonical_check n xs m). canonical' n M" if "\<forall>M \<in> set xs. canonical' n M"
  using dbm_minus_canonical_canonical'[OF that] unfolding dbm_minus_canonical_check_def by auto

subsection \<open>Correctness of @{term dbm_subset_fed}\<close>

paragraph \<open>Misc\<close>

lemma list_all_iffI:
  assumes "\<forall> x \<in> set xs. \<exists> y \<in> set ys. P x \<longleftrightarrow> Q y"
      and "\<forall> y \<in> set ys. \<exists> x \<in> set xs. P x \<longleftrightarrow> Q y"
    shows "list_all P xs \<longleftrightarrow> list_all Q ys"
  using assms unfolding list_all_def by blast

lemma list_all_iff_list_all2I:
  assumes "list_all2 (\<lambda> x y. P x \<longleftrightarrow> Q y) xs ys"
  shows "list_all P xs \<longleftrightarrow> list_all Q ys"
  using assms by (intro list_all_iffI list_all2_set1 list_all2_set2)

lemma list_all2_mapI:
  assumes "list_all2 (\<lambda> x y. P (f x) (g y)) xs ys"
  shows "list_all2 P (map f xs) (map g ys)"
  using assms by (simp only: list.rel_map)

context Default_Nat_Clock_Numbering
begin

lemma canonical_empty_zone:
  "[M]\<^bsub>v,n\<^esub> = {} \<longleftrightarrow> (\<exists>i\<le>n. M i i < 0)" if "canonical M n"
  using v_0 that surj_on by (intro canonical_empty_zone) auto

lemma check_diag_iff_empty:
  "check_diag n (uncurry M) \<longleftrightarrow> \<lbrakk>M\<rbrakk> = {}" if "canonical' n M"
proof (auto dest: check_diag_empty, goal_cases)
  case 1
  show ?case
  proof -
    from that
    show ?thesis
      unfolding canonical'_def
    proof
      assume "canonical M n"
      from canonical_empty_zone[OF this] \<open>\<lbrakk>M\<rbrakk> = {}\<close> have
        "\<exists>i\<le>n. M i i < 0"
        by auto
      then show ?thesis unfolding check_diag_def neutral
        by auto
    next
      assume "check_diag n (uncurry M)"
      then show ?thesis unfolding check_diag_def neutral by auto
    qed
  qed
qed

lemma and_entry_repair_zone_equiv:
  "\<lbrakk>and_entry_repair n a b e M\<rbrakk> = \<lbrakk>and_entry a b e M\<rbrakk>" if "a \<le> n" "b \<le> n"
  unfolding and_entry_repair_def using that by (rule repair_pair_zone_equiv)

lemma dbm_minus_rel:
  assumes "list_all2 (\<lambda>x y. \<lbrakk>x\<rbrakk> = \<lbrakk>y\<rbrakk>) ms ms'"
  shows "list_all2 (\<lambda>x y. \<lbrakk>x\<rbrakk> = \<lbrakk>y\<rbrakk>) (dbm_minus n ms m) (dbm_minus_canonical n ms' m)"
  unfolding dbm_minus_def dbm_minus_canonical_def
  apply (rule concat_transfer[unfolded rel_fun_def, rule_format])
  apply (rule list_all2_mapI)
  apply (rule list.rel_refl_strong)
  apply (auto 4 3
      intro: list_all2_mapI list_all2_mono[OF assms]
      simp: and_entry_repair_zone_equiv and_entry_correct split: if_split_asm
      )
  done

lemma dbm_minus_canonical_fold_canonical':
  "\<forall>M \<in> set (fold (\<lambda>m S. dbm_minus_canonical n S m) xs ms). canonical' n M"
  if "\<forall>M \<in> set ms. canonical' n M" for ms and xs :: "('t ::time) DBM list"
  using that by (induction xs arbitrary: ms) (auto dest: dbm_minus_canonical_canonical')

(* XXX Move? *)
lemma not_check_diag_nonnegD:
  "M i i \<ge> 0" if "\<not> check_diag n (uncurry M)" "i \<le> n"
  using that unfolding check_diag_def by (auto simp: DBM.less_eq[symmetric] neutral)

theorem dbm_subset_fed_correct:
  fixes xs :: "(nat \<Rightarrow> nat \<Rightarrow> ('t ::time) DBMEntry) list"
    and S :: "(nat \<Rightarrow> nat \<Rightarrow> 't DBMEntry) list"
  assumes "canonical' n M"
  shows "\<lbrakk>M\<rbrakk> \<subseteq> (\<Union>m\<in>set xs. \<lbrakk>m\<rbrakk>) \<longleftrightarrow> dbm_subset_fed n M xs"
proof -
  have *: "list_all2 (\<lambda>x y. \<lbrakk>x\<rbrakk> = \<lbrakk>y\<rbrakk>)
     (fold (\<lambda>m S. dbm_minus n S m) xs ms)
     (fold (\<lambda>m S. dbm_minus_canonical n S m) xs ms')"
    if "list_all2 (\<lambda>x y. \<lbrakk>x\<rbrakk> = \<lbrakk>y\<rbrakk>) ms ms'" for ms ms' and xs :: "'t DBM list"
    using that
  proof (induction xs arbitrary: ms ms')
    case Nil
    then show ?case
      by simp
  next
    case prems: (Cons a xs)
    from this(2) show ?case
      by simp (intro prems(1) dbm_minus_rel)
  qed
  let ?xs = "filter (\<lambda>M. \<not> check_diag n (uncurry M)) xs"
  have *: "list_all2 (\<lambda>x y. \<lbrakk>x\<rbrakk> = \<lbrakk>y\<rbrakk>)
     (fold (\<lambda>m S. dbm_minus n S m) ?xs [M])
     (fold (\<lambda>m S. dbm_minus_canonical n S m) ?xs [M])"
    by (rule *) simp
  have **:"(\<Union>m\<in>set xs. \<lbrakk>m\<rbrakk>) = (\<Union>m\<in>set (filter (\<lambda>M. \<not> check_diag n (uncurry M)) xs). \<lbrakk>m\<rbrakk>)"
    by (auto simp: check_diag_empty)
  show ?thesis
    apply (subst **)
    apply (subst dbm_list_superset_op[where S = "[M]", simplified])
    subgoal
      by (auto dest: not_check_diag_nonnegD simp: neutral[symmetric] DBM.less_eq)
    subgoal
      unfolding dbm_subset_fed_def Let_def
      using dbm_minus_canonical_fold_canonical'[of "[M]"] \<open>canonical' n M\<close>
      by (intro list_all_iff_list_all2I list.rel_mono_strong[OF *])(auto dest: check_diag_iff_empty)
    done
qed

lemma dbm_minus_canonical_check_fed_equiv:
  "dbm_list (dbm_minus_canonical_check n S m) = dbm_list (dbm_minus_canonical n S m)"
  unfolding dbm_minus_canonical_check_def by (auto simp: check_diag_empty)

lemma dbm_minus_canonical_dbm_minus:
  "dbm_list (dbm_minus_canonical n xs m) = dbm_list (dbm_minus n xs m)"
  using dbm_minus_rel[of xs xs m] unfolding list_all2_same
  by (force dest: list_all2_set1 list_all2_set2)

lemma dbm_minus_canonical_fed_equiv:
  "dbm_list (dbm_minus_canonical n xs m) = dbm_list (dbm_minus_canonical n xs' m)"
  if "dbm_list xs = dbm_list xs'" "0 \<le> m 0 0"
  unfolding dbm_minus_canonical_dbm_minus
  using that by (auto simp: neutral dbm_list_subtract[symmetric] DBM.less_eq)

theorem dbm_subset_fed_correct':
  fixes xs :: "(nat \<Rightarrow> nat \<Rightarrow> ('t ::time) DBMEntry) list"
    and S :: "(nat \<Rightarrow> nat \<Rightarrow> 't DBMEntry) list"
  assumes "canonical' n M"
  shows "\<lbrakk>M\<rbrakk> \<subseteq> (\<Union>m\<in>set xs. \<lbrakk>m\<rbrakk>) \<longleftrightarrow> (
    let xs = filter (\<lambda>M. \<not> check_diag n (uncurry M)) xs in
    list_all (\<lambda> M. check_diag n (uncurry M)) (fold (\<lambda>m S. dbm_minus_canonical_check n S m) xs [M]))"
proof -
  have canonical: "\<forall>M \<in> set (fold (\<lambda>m S. dbm_minus_canonical_check n S m) xs ms). canonical' n M"
    if "\<forall>M \<in> set ms. canonical' n M" for ms and xs :: "'t DBM list"
    using that by (induction xs arbitrary: ms) (auto dest: dbm_minus_canonical_check_canonical')
  have *: "dbm_list (fold (\<lambda>m S. dbm_minus_canonical_check n S m) xs ms) =
    dbm_list (fold (\<lambda>m S. dbm_minus_canonical n S m) xs ms')"
    if "dbm_list ms = dbm_list ms'" "\<forall>m \<in> set xs. m 0 0 \<ge> 0" for ms ms' and xs :: "'t DBM list"
    using that
  proof (induction xs arbitrary: ms ms')
    case Nil
    then show ?case
      by simp
  next
    case (Cons a xs)
    from Cons.prems show ?case
      by - (simp, rule Cons.IH,
          auto intro!: dbm_minus_canonical_fed_equiv simp add: dbm_minus_canonical_check_fed_equiv
          )
  qed
  define xs' where "xs' = filter (\<lambda>M. \<not> check_diag n (uncurry M)) xs"
  have *: "dbm_list (fold (\<lambda>m S. dbm_minus_canonical_check n S m) xs' [M]) =
        dbm_list (fold (\<lambda>m S. dbm_minus_canonical n S m) xs' [M])"
    by (auto intro!: * dest: not_check_diag_nonnegD simp: xs'_def)
  have **: "list_all (\<lambda> M. check_diag n (uncurry M)) xs \<longleftrightarrow> dbm_list xs = {}"
    if "\<forall>M \<in> set xs. canonical' n M" for xs :: "'t DBM list"
    using that by (metis (mono_tags, lifting) Ball_set SUP_bot_conv(2) check_diag_iff_empty)
  show ?thesis
    unfolding 
      dbm_subset_fed_correct[OF \<open>canonical' _ _\<close>] dbm_subset_fed_def
      xs'_def[symmetric] Let_def
    apply (subst **)
     defer
     apply (subst **)
    using assms by (auto intro!: dbm_minus_canonical_fold_canonical' canonical simp: *)
qed

(* XXX Move *)
lemma subset_if_pointwise_le:
  "\<lbrakk>M\<rbrakk> \<subseteq> \<lbrakk>M'\<rbrakk>" if "pointwise_cmp (\<le>) n M M'"
  using that by (simp add: DBM.less_eq DBM_le_subset pointwise_cmp_def subsetI)

theorem dbm_subset_fed_check_correct:
  fixes xs :: "(nat \<Rightarrow> nat \<Rightarrow> ('t ::time) DBMEntry) list"
    and S :: "(nat \<Rightarrow> nat \<Rightarrow> 't DBMEntry) list"
  assumes "canonical' n M"
  shows "\<lbrakk>M\<rbrakk> \<subseteq> (\<Union>m\<in>set xs. \<lbrakk>m\<rbrakk>) \<longleftrightarrow> dbm_subset_fed_check n M xs"
proof -
  define xs' where "xs' = filter (\<lambda>M. \<not> check_diag n (uncurry M)) xs"
  define is_direct_subset where
    "is_direct_subset = list_ex (\<lambda> M'. dbm_subset' n (uncurry M) (uncurry M')) xs'"
  have "\<lbrakk>M\<rbrakk> \<subseteq> (\<Union>m\<in>set xs. \<lbrakk>m\<rbrakk>)" if is_direct_subset
  proof -
    from that have "\<exists>m \<in> set xs'. \<lbrakk>M\<rbrakk> \<subseteq> \<lbrakk>m\<rbrakk>"
      unfolding is_direct_subset_def list_ex_iff dbm_subset'_def
      by (auto intro!: subset_if_pointwise_le)
    then show ?thesis
      unfolding xs'_def by auto
  qed
  then show ?thesis
    apply (cases is_direct_subset; simp add:
        dbm_subset_fed_check_def is_direct_subset_def dbm_subset_fed_def xs'_def[symmetric]
        )
    unfolding dbm_subset_fed_correct[
        OF \<open>canonical' n M\<close>, of xs, unfolded Let_def dbm_subset_fed_def, folded xs'_def, symmetric
        ]
    unfolding dbm_subset_fed_correct'[
        OF \<open>canonical' n M\<close>, of xs, folded xs'_def, unfolded Let_def, symmetric
        ]
    ..
qed

end (* Default Clock Numbering *)


subsection \<open>Refined DBM operations\<close>

(* This is the odd one out *)
definition
  "V_dbm = (\<lambda> i j. if i = j then 0 else if i = 0 \<and> j > 0 then 0 else \<infinity>)"

definition and_entry_upd ::
  "nat \<Rightarrow> nat \<Rightarrow> int DBMEntry \<Rightarrow> int DBM' \<Rightarrow> int DBM'" where
  "and_entry_upd a b e M = M((a,b) := min (M (a, b)) e)"

definition
  "and_entry_repair_upd n a b e M \<equiv>
   Normalized_Zone_Semantics_Impl_Semantic_Refinement.repair_pair n (and_entry_upd a b e M) a b"

definition
  "dbm_minus_canonical_upd n xs m =
  concat (map (\<lambda>(i, j). map (\<lambda> M. and_entry_repair_upd n j i (neg_dbm_entry (m (i, j))) M) xs)
    [(i, j). i\<leftarrow>[0..<Suc n], j\<leftarrow>[0..<Suc n], (i > 0 \<or> j > 0) \<and> i \<le> n \<and> j \<le> n \<and> m (i, j) \<noteq> \<infinity>])"

definition
  "dbm_minus_canonical_check_upd n xs M =
  filter (\<lambda>M. \<not> check_diag n M) (dbm_minus_canonical_upd n xs M)"

definition
  "dbm_subset_fed_upd n M xs \<equiv>
   let xs = filter (\<lambda>M. \<not> check_diag n M) xs;
       is_direct_subset = list_ex (\<lambda>M'. dbm_subset' n M M') xs
   in is_direct_subset \<or>
     list_all (\<lambda> M. check_diag n M) (fold (\<lambda>m S. dbm_minus_canonical_check_upd n S m) xs [M])"

(* XXX Move? *)
lemma list_all_filter_neg:
  "list_all P (filter (\<lambda>x. \<not> P x) xs) \<longleftrightarrow> (filter (\<lambda>x. \<not> P x) xs) = []"
  by (metis Cons_eq_filterD list_all_simps(2) list_pred_cases)

lemma dbm_subset_fed_upd_alt_def:
  "dbm_subset_fed_upd n M xs \<equiv>
   let xs = filter (\<lambda>M. \<not> check_diag n M) xs
   in if xs = [] then check_diag n M
      else if list_ex (\<lambda>M'. dbm_subset' n M M') xs then True
      else fold (\<lambda>m S. dbm_minus_canonical_check_upd n S m) xs [M] = []"
  unfolding dbm_subset_fed_upd_def short_circuit_conv using list_last
  by (intro eq_reflection;force simp: list_all_filter_neg dbm_minus_canonical_check_upd_def Let_def)

definition
  "V_dbm' n = (\<lambda>(i, j). (if i = j \<or> i = 0 \<and> j > 0 \<or> i > n \<or> j > n then 0 else \<infinity>))"

definition
  down_upd :: "nat \<Rightarrow> _ DBM' \<Rightarrow> _ DBM'"
where
  "down_upd n M \<equiv> \<lambda>(i, j).
  if i = 0 \<and> j > 0 \<and> i \<le> n \<and> j \<le> n then Min ({Le 0} \<union> {M (k, j) | k. 1 \<le> k \<and> k \<le> n}) else M (i, j)"

definition
  "restrict_zero_upd n M x \<equiv>
    let
      M1 = and_entry_upd x 0 (Le 0) M;
      M2 = and_entry_upd 0 x (Le 0) M1
    in Normalized_Zone_Semantics_Impl_Semantic_Refinement.repair_pair n M2 x 0"

definition
  free_upd :: "nat \<Rightarrow> _ DBM' \<Rightarrow> nat \<Rightarrow> _ DBM'"
where
  "free_upd n M x \<equiv>
   \<lambda> (i, j). if i = x \<and> j \<noteq> x \<and> i \<le> n \<and> j \<le> n
    then \<infinity> else if i \<noteq> x \<and> j = x \<and> i \<le> n \<and> j \<le> n then M (i, 0) else M (i, j)"

definition
  "pre_reset_upd n M x \<equiv> free_upd n (restrict_zero_upd n M x) x"

definition
  "pre_reset_list_upd n M r \<equiv> fold (\<lambda> x M. pre_reset_upd n M x) r M"


subsection \<open>Transferring properties\<close>

context
  includes lifting_syntax
begin

lemma neg_dbm_entry_transfer[transfer_rule]:
  "(rel_DBMEntry ri ===> rel_DBMEntry ri) neg_dbm_entry neg_dbm_entry"
  by (auto elim!: DBMEntry.rel_cases intro!: rel_funI)

lemma fold_min_transfer:
  "((list_all2 (rel_DBMEntry ri)) ===> rel_DBMEntry ri ===> rel_DBMEntry ri) (fold min) (fold min)"
  by transfer_prover

context
  fixes n :: nat
begin

definition
  "RI2 M D \<equiv> RI n (uncurry M) D"

lemma and_entry_transfer[transfer_rule]:
  "((=) ===> (=) ===> rel_DBMEntry ri ===> RI2 ===> RI2) and_entry and_entry_upd"
  unfolding and_entry_def and_entry_upd_def
  unfolding rel_fun_def eq_onp_def RI2_def
  by (auto intro: min_ri_transfer[unfolded rel_fun_def, rule_format])

lemma FWI_transfer[transfer_rule]:
  "(RI2 ===> eq_onp (\<lambda>x. x = n) ===> eq_onp (\<lambda>x. x < Suc n) ===> RI2) FWI FWI'" (is "?A")
and FW_transfer[transfer_rule]:
  "(RI2 ===> eq_onp (\<lambda>x. x = n) ===> RI2) FW FW'" (is "?B")
proof -
  define RI' where
    "RI' = (eq_onp (\<lambda> x. x < Suc n) ===> eq_onp (\<lambda> x. x < Suc n) ===> rel_DBMEntry ri)"
  have RI_iff: "RI' M M' \<longleftrightarrow> RI n (uncurry M) (uncurry M')" for M M'
    unfolding RI'_def rel_fun_def by auto
  { fix M D k assume "RI n (uncurry M) D" "k < Suc n"
    then have "RI' M (curry D)"
      by (simp add: RI_iff)
    with \<open>k < Suc n\<close> have "RI' (FWI M n k) (FWI (curry D) n k)"
      unfolding FWI_def
      by (intro fwi_RI_transfer[of n, folded RI'_def, unfolded rel_fun_def, rule_format])
        (auto simp: eq_onp_def)
    then have "RI n (uncurry (FWI M n k)) (uncurry (FWI (curry D) n k))"
      by (simp add: RI_iff)
  } note * = this
  show ?A
    unfolding FWI'_def
    unfolding rel_fun_def
    unfolding RI2_def
    apply clarsimp
    apply (subst (asm) (3) eq_onp_def)
    apply (subst (asm) (3) eq_onp_def)
    apply clarsimp
    by (intro *)
  { fix M D assume "RI n (uncurry M) D"
    then have "RI' M (curry D)"
      by (simp add: RI_iff)
    then have "RI' (FW M n) (FW (curry D) n)"
      by (intro FW_RI_transfer[of n, folded RI'_def, unfolded rel_fun_def, rule_format])
         (auto simp: eq_onp_def)
    then have "RI n (uncurry (FW M n)) (FW' D n)"
      by (simp add: RI_iff FW'_def)
  } note * = this
  show ?B
    unfolding rel_fun_def
    unfolding RI2_def
    apply clarsimp
    apply (subst (asm) (3) eq_onp_def)
    apply clarsimp
    by (intro *)
qed

lemma repair_pair_transfer[transfer_rule]:
  "(eq_onp (\<lambda>x. x = n) ===> RI2 ===> eq_onp (\<lambda>x. x < Suc n) ===> eq_onp (\<lambda>x. x < Suc n) ===> RI2)
    repair_pair Normalized_Zone_Semantics_Impl_Semantic_Refinement.repair_pair"
  unfolding repair_pair_def Normalized_Zone_Semantics_Impl_Semantic_Refinement.repair_pair_def
  by transfer_prover

lemma and_entry_transfer_weak:
  "(eq_onp (\<lambda>x. x < Suc n) ===> eq_onp (\<lambda>x. x < Suc n) ===> rel_DBMEntry ri ===> RI2 ===> RI2)
    and_entry and_entry_upd"
  using and_entry_transfer unfolding rel_fun_def eq_onp_def by auto

lemma and_entry_repair_transfer[transfer_rule]:
  "(eq_onp (\<lambda>x. x = n) ===> eq_onp (\<lambda>x. x < Suc n) ===> eq_onp (\<lambda>x. x < Suc n) ===> rel_DBMEntry ri
    ===> RI2 ===> RI2) and_entry_repair and_entry_repair_upd
  "
  supply [transfer_rule] = and_entry_transfer_weak
  unfolding and_entry_repair_def and_entry_repair_upd_def by transfer_prover

lemma dbm_minus_canonical_transfer[transfer_rule]:
  "(eq_onp (\<lambda>x. x = n) ===> list_all2 RI2 ===> RI2 ===> list_all2 RI2)
    dbm_minus_canonical dbm_minus_canonical_upd
  "
  unfolding dbm_minus_canonical_def dbm_minus_canonical_upd_def
  apply (intro rel_funI)
  apply (rule concat_transfer[unfolded rel_fun_def, rule_format])
  apply (rule list.map_transfer[unfolded rel_fun_def, rule_format,
        where Rb = "rel_prod (eq_onp (\<lambda>x. x < Suc n)) (eq_onp (\<lambda>x. x < Suc n))"])
   apply clarsimp
  subgoal
    apply (rule list_all2_mapI)
    apply (erule list_all2_mono)
    apply (rule and_entry_repair_transfer[unfolded rel_fun_def, rule_format])
        apply assumption+
    subgoal
      unfolding RI2_def rel_fun_def
      by (auto intro: neg_dbm_entry_transfer[unfolded rel_fun_def, rule_format])
    apply assumption
    done
  subgoal premises prems for n1 n2 xs ys M D
  proof -
    have [simp]: "D (i, j) \<noteq> \<infinity> \<longleftrightarrow> M i j \<noteq> \<infinity>" if "i < Suc n" "j < Suc n" for i j
      using prems that by (auto 4 3 simp: eq_onp_def rel_fun_def RI2_def elim!: DBMEntry.rel_cases)
    from prems have [simp]: "n1 = n" "n2 = n"
      by (auto simp: eq_onp_def)
    let ?a = "(concat
       (map (\<lambda>i. concat
                   (map (\<lambda>j. if (0 < i \<or> 0 < j) \<and>
                                 i \<le> n \<and> j \<le> n \<and> M i j \<noteq> \<infinity>
                              then [(i, j)] else [])
                     [0..<Suc n]))
         [0..<Suc n]))"
    let ?b = "(concat
       (map (\<lambda>i. concat
                   (map (\<lambda>j. if (0 < i \<or> 0 < j) \<and>
                                 i \<le> n \<and> j \<le> n \<and> D (i, j) \<noteq> \<infinity>
                              then [(i, j)] else [])
                     [0..<Suc n]))
         [0..<Suc n]))"
    have "?b = ?a"
      by (auto intro!: arg_cong[where f = concat] simp del: upt_Suc)
    then show ?thesis
      by (simp del: upt_Suc add: list_all2_same eq_onp_def)
  qed
  done

lemma check_diag_transfer[transfer_rule]:
  "(eq_onp (\<lambda>x. x = n) ===> RI2 ===> (=)) (\<lambda>n M. check_diag n (uncurry M)) check_diag"
  unfolding RI2_def rel_fun_def check_diag_def
  by (auto 0 5 dest: neutral_RI simp: eq_onp_def less_Suc_eq_le neutral[symmetric])

lemma dbm_minus_canonical_check_transfer[transfer_rule]:
  "(eq_onp (\<lambda>x. x = n) ===> list_all2 RI2 ===> RI2 ===> list_all2 RI2)
    dbm_minus_canonical_check dbm_minus_canonical_check_upd
  "
  unfolding dbm_minus_canonical_check_def dbm_minus_canonical_check_upd_def by transfer_prover

(* XXX Move *)
lemma le_rel_DBMEntry_iff:
  "a \<le> b \<longleftrightarrow> x \<le> y" if "rel_DBMEntry ri a x" "rel_DBMEntry ri b y"
  using that by (auto elim!: DBMEntry.rel_cases simp: dbm_entry_simps ri_def)

lemma dbm_subset'_transfer[transfer_rule]:
  "(eq_onp (\<lambda>x. x = n) ===> RI2 ===> RI2 ===> (=))
    (\<lambda> n M M'. dbm_subset' n (uncurry M) (uncurry M')) dbm_subset'"
  unfolding RI2_def rel_fun_def dbm_subset'_def
  using le_rel_DBMEntry_iff by (clarsimp simp: eq_onp_def pointwise_cmp_def less_Suc_eq_le) meson

lemma dbm_subset_fed_transfer:
  "(eq_onp (\<lambda>x. x = n) ===> RI2 ===> list_all2 RI2 ===> (=)) dbm_subset_fed_check dbm_subset_fed_upd"
  unfolding dbm_subset_fed_check_def dbm_subset_fed_upd_def by transfer_prover

lemma V_dbm_transfer[transfer_rule]:
  "RI2 V_dbm (V_dbm' n)"
  unfolding V_dbm_def V_dbm'_def RI2_def by (auto simp: rel_fun_def neutral eq_onp_def zero_RI)

lemma down_transfer[transfer_rule]:
  "(eq_onp (\<lambda>x. x = n) ===> RI2 ===> RI2) down down_upd"
  unfolding down_def down_upd_def
proof (clarsimp simp: rel_fun_def RI2_def eq_onp_def, goal_cases)
  case prems: (1 M D x)
  have A: "(insert (Le 0) {M k x |k. Suc 0 \<le> k \<and> k \<le> n})
      = (set (Le 0 # [M k x. k \<leftarrow> [1..<Suc n]]))"
    by auto
  have B: "insert (Le 0) {D (k, x) |k. Suc 0 \<le> k \<and> k \<le> n} 
      = (set (Le 0 # [D (k, x). k \<leftarrow> [1..<Suc n]]))"
    by auto
  show ?case
    unfolding A B Min.set_eq_fold
    apply (rule fold_min_transfer[unfolded rel_fun_def, rule_format])
    unfolding list.rel_map list_all2_same using prems by (auto simp: zero_RI)
qed

lemma free_upd[transfer_rule]:
  "(eq_onp (\<lambda>x. x = n) ===> RI2 ===> (=) ===> RI2) free free_upd"
  unfolding free_def free_upd_def by (auto simp: RI2_def rel_fun_def eq_onp_def)

lemma pre_reset_transfer[transfer_rule]:
  "(eq_onp (\<lambda>x. x = n) ===> RI2 ===> eq_onp (\<lambda>x. x < Suc n) ===> RI2) pre_reset pre_reset_upd"
proof -
  have [transfer_rule]: "eq_onp (\<lambda>x. x = n) n n"
    by (simp add: eq_onp_def)
  note [transfer_rule] = and_entry_transfer_weak
  have [transfer_rule]:
    "(eq_onp (\<lambda>x. x = n) ===> RI2 ===> eq_onp (\<lambda>x. x < Suc n) ===> RI2) free free_upd"
    using free_upd unfolding rel_fun_def eq_onp_def by blast
  show ?thesis
    unfolding pre_reset_def pre_reset_upd_def
    unfolding restrict_zero_def restrict_zero_upd_def
    by transfer_prover
qed

lemma pre_reset_list_transfer[transfer_rule]:
  "(eq_onp (\<lambda>x. x = n) ===> RI2 ===> list_all2 (eq_onp (\<lambda>x. x < Suc n)) ===> RI2)
    pre_reset_list pre_reset_list_upd"
  unfolding pre_reset_list_def pre_reset_list_upd_def by transfer_prover

end (* Fixed n *)
end (* Lifting Syntax *)

(* Unused *)
definition
  "unbounded_dbm \<equiv> \<lambda> i j. if i = j then 0 else \<infinity>"

lemma canonical_unbounded_dbm:
  "canonical unbounded_dbm n"
  by (auto simp: unbounded_dbm_def any_le_inf)

lemma diag_unbounded_dbm:
  "unbounded_dbm i i = 0"
  unfolding unbounded_dbm_def by simp

lemma down_diag:
  "down n M i i = M i i"
  unfolding down_def by auto

definition
  "abstr_FW n cc M v \<equiv> FW (abstr cc M v) n"

definition
  "abstr_FW_upd n cc M \<equiv> FW' (abstr_upd cc M) n"

lemma abstr_mono:
  "abstr cc M v i j \<le> M i j"
  by (subst abstr.simps, induction cc arbitrary: M) (auto intro: order.trans abstra_mono)

lemma abstr_FW_mono:
  "abstr_FW n cc M v i j \<le> M i j" if "i \<le> n" "j \<le> n"
  unfolding abstr_FW_def by (blast intro: that abstr_mono fw_mono order.trans)

lemma abstr_FW_diag_preservation:
  "\<forall>k\<le>n. abstr_FW n cc M v k k \<le> 0" if "\<forall>k\<le>n. M k k \<le> 0"
  using that by (blast intro: abstr_FW_mono order.trans)

lemma FW_canonical:
  "canonical' n (FW M n)"
  unfolding canonical'_def using FW_canonical[of n M] by (simp add: check_diag_def neutral)

lemma abstr_FW_canonical:
  "canonical' n (abstr_FW n cc M v)"
  unfolding abstr_FW_def by (rule FW_canonical)

lemma down_check_diag:
  "check_diag n (uncurry (down n M))" if "check_diag n (uncurry M)"
  using that unfolding check_diag_def down_def by force

context Default_Nat_Clock_Numbering
begin

lemma clock_numbering:
  "\<forall> c. v c > 0 \<and> (\<forall>x. \<forall>y. v x \<le> n \<and> v y \<le> n \<and> v x = v y \<longrightarrow> x = y)"
  by (metis neq0_conv v_0 v_id)

lemma V_dbm_correct:
  "\<lbrakk>V_dbm\<rbrakk> = V"
  unfolding V_def DBM_zone_repr_def DBM_val_bounded_alt_def2 
  by (auto simp: dbm_entry_val'_iff_bounded V_dbm_def dbm_entry_simps neutral)

lemma abstr_correct:
  "\<lbrakk>abstr cc M v\<rbrakk> = \<lbrakk>M\<rbrakk> \<inter> {u. u \<turnstile> cc}" if "\<forall>c\<in>collect_clks cc. 0 < c \<and> c \<le> n"
  apply (rule dbm_abstr_zone_eq2)
  subgoal
    by (rule clock_numbering)
  subgoal
    using that by (auto simp: v_is_id)
  done

(* Unused *)
lemma unbounded_dbm_correct:
  "\<lbrakk>unbounded_dbm\<rbrakk> = UNIV"
  unfolding DBM_zone_repr_def DBM_val_bounded_alt_def2 unbounded_dbm_def neutral
  by (simp add: dbm_entry_val'_iff_bounded any_le_inf)

(* Unused *)
lemma abstr_correct':
  "\<lbrakk>abstr cc unbounded_dbm v\<rbrakk> = {u. u \<turnstile> cc}" if "\<forall>c\<in>collect_clks cc. 0 < c \<and> c \<le> n"
  by (simp add: unbounded_dbm_correct abstr_correct[OF that] del: abstr.simps)

lemma abstr_FW_correct:
  "\<lbrakk>abstr_FW n cc M v\<rbrakk> = \<lbrakk>M\<rbrakk> \<inter> {u. u \<turnstile> cc}" if "\<forall>c\<in>collect_clks cc. 0 < c \<and> c \<le> n"
  unfolding abstr_FW_def by (subst FW_zone_equiv[symmetric]; intro surj_on abstr_correct that)

lemma abstr_FW_correct':
  "\<lbrakk>abstr_FW n cc unbounded_dbm v\<rbrakk> = {u. u \<turnstile> cc}" if "\<forall>c\<in>collect_clks cc. 0 < c \<and> c \<le> n"
  by (simp add: unbounded_dbm_correct abstr_FW_correct[OF that])

lemma down_V:
  "\<lbrakk>down n M\<rbrakk> \<subseteq> V"
  by (rule V_structuralI) (auto simp: down_def neutral intro: Min_le)

lemma down_correct':
  "\<lbrakk>down n M\<rbrakk> = \<lbrakk>M\<rbrakk>\<^sup>\<down> \<inter> V" if "canonical M n"
  apply safe
  subgoal for u
    by (erule down_sound, rule that)
  subgoal for u
    using down_V by blast
  subgoal for u
    unfolding V_def by (erule down_complete) simp
  done

lemma down_correct:
  "\<lbrakk>down n M\<rbrakk> = \<lbrakk>M\<rbrakk>\<^sup>\<down> \<inter> V" if "canonical' n M"
  using that unfolding canonical'_def
  apply standard
  subgoal
    by (rule down_correct')
  by (frule down_check_diag) (simp add: check_diag_empty zone_time_pre_def)

lemma pre_reset_diag_preservation:
  "pre_reset n M x i i \<le> M i i" if "i \<le> n"
  unfolding pre_reset_def by (auto simp add: free_diag restrict_zero_mono that)

lemma pre_reset_list_diag:
  "pre_reset_list n M r i i \<le> M i i" if "i \<le> n"
  apply (induction r arbitrary: M)
   apply (simp add: pre_reset_list_def; fail)
  apply (simp add: pre_reset_list_Cons, blast intro: pre_reset_diag_preservation that order.trans)
  done

context
  includes lifting_syntax
begin

lemma abstra_upd_abstra:
  "abstra_upd ac M (i, j) = abstra ac (curry M) v i j" if "0 < constraint_clk ac" "i \<le> n" "j \<le> n"
  using that by (cases ac) (auto simp: le_n_iff v_is_id v_0)

lemma abstra_transfer[transfer_rule]:
  "(rel_acconstraint (eq_onp (\<lambda> x. 0 < x \<and> x < Suc n)) ri ===> RI2 n ===> RI2 n)
    (\<lambda> cc M. abstra cc M v) abstra_upd"
  apply (intro rel_funI)
  apply (subst RI2_def)
  apply (intro rel_funI)
  apply (elim rel_prod.cases)
  apply (simp only:)
  apply (subst abstra_upd_abstra)
  by (auto 4 3 simp: eq_onp_def RI2_def rel_fun_def
       intro!: min_ri_transfer[unfolded rel_fun_def, rule_format]
       elim!: acconstraint.rel_cases
     )

lemma abstr_transfer[transfer_rule]:
  "(list_all2 (rel_acconstraint (eq_onp (\<lambda> x. 0 < x \<and> x < Suc n)) ri) ===> RI2 n ===> RI2 n)
    (\<lambda> cc M. abstr cc M v) abstr_upd"
  unfolding abstr.simps abstr_upd_def by transfer_prover

lemma abstr_FW_transfer[transfer_rule]:
  "(list_all2 (rel_acconstraint (eq_onp (\<lambda> x. 0 < x \<and> x < Suc n)) ri) ===> RI2 n ===> RI2 n)
    (\<lambda> cc M. abstr_FW n cc M v) (abstr_FW_upd n)"
proof -
  have [transfer_rule]: "eq_onp (\<lambda>x. x = n) n n"
    by (simp add: eq_onp_def)
  show ?thesis
    unfolding abstr_FW_def abstr_FW_upd_def by transfer_prover
qed

end

end

lemma RI2_trivial_transfer[transfer_rule]: "(RI2 n) (curry (conv_M M)) M"
  unfolding RI2_def rel_fun_def by (auto simp: eq_onp_def)

end
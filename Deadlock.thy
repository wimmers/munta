theory Deadlock
  imports
    TA.Timed_Automata TA.CTL TA.DBM_Operations TA.Normalized_Zone_Semantics
begin

text \<open>Operations\<close>

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

context
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

abbreviation
  "dbm_fed S \<equiv> \<Union> m \<in> S. [m]\<^bsub>v,n\<^esub>"

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

abbreviation
  "dbm_entry_val' u a b e \<equiv> dbm_entry_val u (clock_to_option a) (clock_to_option b) e"

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
  by (induction xs; simp add: and_entry_correct[OF that, symmetric] Int_Un_distrib2)

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
    by (cases x; simp add: neg_entry')
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

lemma dbm_list_empty_check:
  "dbm_list xs = {} \<longleftrightarrow> list_all (\<lambda>m. [m]\<^bsub>v,n\<^esub> = {}) xs"
  unfolding list_all_iff by auto

lemmas dbm_list_superset_op =
  dbm_fed_superset_fold''[OF dbm_list_subtract[symmetric], unfolded dbm_list_empty_check]

end (* Anonymous context *)

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

end
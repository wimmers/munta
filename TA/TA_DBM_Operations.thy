theory TA_DBM_Operations
  imports Timed_Automata DBM.DBM_Operations
begin

section \<open>From Clock Constraints to DBMs\<close>

fun abstra ::
  "('c, 't::{linordered_cancel_ab_monoid_add,uminus}) acconstraint \<Rightarrow> 't DBM \<Rightarrow> ('c \<Rightarrow> nat) \<Rightarrow> 't DBM"
where
  "abstra (EQ c d) M v =
    (\<lambda> i j . if i = 0 \<and> j = v c then min (M i j) (Le (-d)) else if i = v c \<and> j = 0 then min (M i j) (Le d) else M i j)" |
  "abstra (LT c d) M v =
    (\<lambda> i j . if i = v c \<and> j = 0 then min (M i j) (Lt d) else M i j)" |
  "abstra (LE c d) M v =
    (\<lambda> i j . if i = v c \<and> j = 0 then min (M i j) (Le d) else M i j)" |
  "abstra (GT c d) M v =
    (\<lambda> i j. if i = 0 \<and> j = v c then min (M i j) (Lt (- d)) else M i j)" |
  "abstra (GE c d) M v =
    (\<lambda> i j. if i = 0 \<and> j = v c then min (M i j) (Le (- d)) else M i j)"

fun abstr ::"('c, 't::{linordered_cancel_ab_monoid_add,uminus}) cconstraint \<Rightarrow> 't DBM \<Rightarrow> ('c \<Rightarrow> nat) \<Rightarrow> 't DBM"
where
  "abstr cc M v = fold (\<lambda> ac M. abstra ac M v) cc M"

(* XXX Move *)
lemma collect_clks_Cons[simp]:
  "collect_clks (ac # cc) = insert (constraint_clk ac) (collect_clks cc)"
unfolding collect_clks_def by auto

lemma abstr_id1:
  "c \<notin> collect_clks cc \<Longrightarrow> clock_numbering' v n \<Longrightarrow> \<forall> c \<in> collect_clks cc. v c \<le> n
    \<Longrightarrow> abstr cc M v 0 (v c) = M 0 (v c)"
apply (induction cc arbitrary: M c)
apply (simp; fail)
 subgoal for a
  apply simp
  apply (cases a)
 by auto
done

lemma abstr_id2:
  "c \<notin> collect_clks cc \<Longrightarrow> clock_numbering' v n \<Longrightarrow> \<forall> c \<in> collect_clks cc. v c \<le> n
    \<Longrightarrow> abstr cc M v (v c) 0 = M (v c) 0"
apply (induction cc arbitrary: M c)
apply (simp; fail)
 subgoal for a
  apply simp
  apply (cases a)
 by auto
done

text \<open>
  This lemma is trivial because we constrained our theory to difference constraints.
\<close>

lemma abstra_id3:
  assumes "clock_numbering v"
  shows "abstra ac M v (v c1) (v c2) = M (v c1) (v c2)"
proof -
  have "\<And>c. v c = 0 \<Longrightarrow> False"
  proof -
    fix c assume "v c = 0"
    moreover from assms have "v c > 0" by auto
    ultimately show False by linarith
  qed
  then show ?thesis by (cases ac) auto
qed

lemma abstr_id3:
  "clock_numbering v \<Longrightarrow> abstr cc M v (v c1) (v c2) = M (v c1) (v c2)"
by (induction cc arbitrary: M) (auto simp add: abstra_id3)

lemma abstra_id3':
  assumes "\<forall>c. 0 < v c"
  shows "abstra ac M v 0 0 = M 0 0"
proof -
  have "\<And>c. v c = 0 \<Longrightarrow> False"
  proof -
    fix c assume "v c = 0"
    moreover from assms have "v c > 0" by auto
    ultimately show False by linarith
  qed
  then show ?thesis by (cases ac) auto
qed

lemma abstr_id3':
  "clock_numbering v \<Longrightarrow> abstr cc M v 0 0 = M 0 0"
by (induction cc arbitrary: M) (auto simp add: abstra_id3')

(* XXX Move *)
lemma clock_numberingD:
  assumes "clock_numbering v" "v c = 0"
  shows "A"
proof-
  from assms(1) have "v c > 0" by auto
  with \<open>v c = 0\<close> show ?thesis by linarith
qed

lemma dbm_abstra_soundness:
  "\<lbrakk>u \<turnstile>\<^sub>a ac; u \<turnstile>\<^bsub>v,n\<^esub> M; clock_numbering' v n; v (constraint_clk ac) \<le> n\<rbrakk>
    \<Longrightarrow> DBM_val_bounded v u (abstra ac M v) n"
proof (unfold DBM_val_bounded_def, auto, goal_cases)
  case prems: 1
  from abstra_id3'[OF this(4)] have "abstra ac M v 0 0 = M 0 0" .
  with prems show ?case unfolding dbm_le_def by auto
next
  case prems: (2 c)
  then have "clock_numbering' v n" by auto
  note A = prems(1) this prems(6,3)
  let ?c = "constraint_clk ac"
  show ?case
  proof (cases "c = ?c")
    case True
    then show ?thesis using prems by (cases ac) (auto split: split_min intro: clock_numberingD)
  next
    case False
    then show ?thesis using A(3) prems by (cases ac) auto
  qed
next
  case prems: (3 c)
  then have "clock_numbering' v n" by auto
  then have gt0: "v c > 0" by auto
  let ?c = "constraint_clk ac"
  show ?case
  proof (cases "c = ?c")
    case True
    then show ?thesis using prems gt0 by (cases ac) (auto split: split_min intro: clock_numberingD)
  next
    case False
    then show ?thesis using \<open>clock_numbering' v n\<close> prems by (cases ac) auto
  qed
next
  text \<open>Trivial because of missing difference constraints\<close>
  case prems: (4 c1 c2)
  from abstra_id3[OF this(4)] have "abstra ac M v (v c1) (v c2) = M (v c1) (v c2)" by auto
  with prems show ?case by auto
qed

lemma dbm_abstr_soundness':
  "\<lbrakk>u \<turnstile> cc; u \<turnstile>\<^bsub>v,n\<^esub> M; clock_numbering' v n; \<forall> c \<in> collect_clks cc. v c \<le> n\<rbrakk>
    \<Longrightarrow> DBM_val_bounded v u (abstr cc M v) n"
  by (induction cc arbitrary: M) (auto simp: clock_val_def dest: dbm_abstra_soundness)

lemmas dbm_abstr_soundness = dbm_abstr_soundness'[OF _ DBM_triv]

lemma dbm_abstra_completeness:
  "\<lbrakk>DBM_val_bounded v u (abstra ac M v) n; \<forall>c. v c > 0; v (constraint_clk ac) \<le> n\<rbrakk>
    \<Longrightarrow> u \<turnstile>\<^sub>a ac"
proof (cases ac, goal_cases)
  case prems: (1 c d)
  then have "v c \<le> n" by auto
  with prems(1,4) have "dbm_entry_val u (Some c) None ((abstra (LT c d) M v) (v c) 0)"
  by (auto simp: DBM_val_bounded_def)
  moreover from prems(2) have "v c > 0" by auto
  ultimately show ?case using prems(4) by (auto dest: dbm_entry_dbm_min3)
next
  case prems: (2 c d)
  from this have "v c \<le> n" by auto
  with prems(1,4) have "dbm_entry_val u (Some c) None ((abstra (LE c d) M v) (v c) 0)"
  by (auto simp: DBM_val_bounded_def)
  moreover from prems(2) have "v c > 0" by auto
  ultimately show ?case using prems(4) by (auto dest: dbm_entry_dbm_min3)
next
  case prems: (3 c d)
  from this have c: "v c > 0" "v c \<le> n" by auto
  with prems(1,4) have B:
    "dbm_entry_val u (Some c) None ((abstra (EQ c d) M v) (v c) 0)"
    "dbm_entry_val u None (Some c) ((abstra (EQ c d) M v) 0 (v c))"
  by (auto simp: DBM_val_bounded_def)
  from c B have "u c \<le> d" "- u c \<le> -d" by (auto dest: dbm_entry_dbm_min2 dbm_entry_dbm_min3)
  with prems(4) show ?case by auto
next
  case prems: (4 c d)
  from this have "v c \<le> n" by auto
  with prems(1,4) have "dbm_entry_val u None (Some c) ((abstra (GT c d) M v) 0 (v c))"
  by (auto simp: DBM_val_bounded_def)
  moreover from prems(2) have "v c > 0" by auto
  ultimately show ?case using prems(4) by (auto dest!: dbm_entry_dbm_min2)
next
  case prems: (5 c d)
  from this have "v c \<le> n" by auto
  with prems(1,4) have "dbm_entry_val u None (Some c) ((abstra (GE c d) M v) 0 (v c))"
  by (auto simp: DBM_val_bounded_def)
  moreover from prems(2) have "v c > 0" by auto
  ultimately show ?case using prems(4) by (auto dest!: dbm_entry_dbm_min2)
qed

lemma abstra_mono:
  "abstra ac M v i j \<le> M i j"
by (cases ac) auto

lemma abstra_subset:
  "[abstra ac M v]\<^bsub>v,n\<^esub> \<subseteq> [M]\<^bsub>v,n\<^esub>"
using abstra_mono
 apply (simp add: less_eq)
 apply safe
by (rule DBM_le_subset; force)

lemma abstr_subset:
  "[abstr cc M v]\<^bsub>v,n\<^esub> \<subseteq> [M]\<^bsub>v,n\<^esub>"
apply (induction cc arbitrary: M)
 apply (simp; fail)
using abstra_subset by fastforce

(* Move to DBM operations *)
lemma dbm_abstra_zone_eq:
  assumes "clock_numbering' v n" "v (constraint_clk ac) \<le> n"
  shows "[abstra ac M v]\<^bsub>v,n\<^esub> = {u. u \<turnstile>\<^sub>a ac} \<inter> [M]\<^bsub>v,n\<^esub>"
  apply safe
  subgoal
    unfolding DBM_zone_repr_def using assms by (auto intro: dbm_abstra_completeness)
  subgoal
    using abstra_subset by blast
  subgoal
    unfolding DBM_zone_repr_def using assms by (auto intro: dbm_abstra_soundness)
  done

(* XXX Move *)
lemma [simp]:
  "u \<turnstile> []"
  by (force simp: clock_val_def)

lemma clock_val_Cons:
  assumes "u \<turnstile>\<^sub>a ac" "u \<turnstile> cc"
  shows "u \<turnstile> (ac # cc)"
  using assms by (induction cc) (auto simp: clock_val_def)

lemma abstra_commute:
  "abstra ac1 (abstra ac2 M v) v = abstra ac2 (abstra ac1 M v) v"
  by (cases ac1; cases ac2; fastforce simp: min.commute min.left_commute clock_val_def)

lemma dbm_abstr_completeness_aux:
  "\<lbrakk>DBM_val_bounded v u (abstr cc (abstra ac M v) v) n; \<forall>c. v c > 0; v (constraint_clk ac) \<le> n\<rbrakk>
    \<Longrightarrow> u \<turnstile>\<^sub>a ac"
apply (induction cc arbitrary: M)
 apply (auto intro: dbm_abstra_completeness; fail)
apply simp
apply (subst (asm) abstra_commute)
by auto

lemma dbm_abstr_completeness:
  "\<lbrakk>DBM_val_bounded v u (abstr cc M v) n; \<forall>c. v c > 0; \<forall> c \<in> collect_clks cc. v c \<le> n\<rbrakk>
    \<Longrightarrow> u \<turnstile> cc"
apply (induction cc arbitrary: M)
 apply (simp; fail)
apply (rule clock_val_Cons)
apply (rule dbm_abstr_completeness_aux)
by auto

lemma dbm_abstr_zone_eq:
  assumes "clock_numbering' v n" "\<forall>c\<in>collect_clks cc. v c \<le> n"
  shows "[abstr cc (\<lambda>i j. \<infinity>) v]\<^bsub>v,n\<^esub> = {u. u \<turnstile> cc}"
using dbm_abstr_soundness dbm_abstr_completeness assms unfolding DBM_zone_repr_def by metis

lemma dbm_abstr_zone_eq2:
  assumes "clock_numbering' v n" "\<forall>c\<in>collect_clks cc. v c \<le> n"
  shows "[abstr cc M v]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub> \<inter> {u. u \<turnstile> cc}"
apply standard
 apply (rule Int_greatest)
  apply (rule abstr_subset)
 unfolding DBM_zone_repr_def
 apply safe
 apply (rule dbm_abstr_completeness)
   using assms apply auto[3]
apply (rule dbm_abstr_soundness')
using assms by auto


abbreviation global_clock_numbering ::
  "('a, 'c, 't, 's) ta \<Rightarrow> ('c \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool"
where
  "global_clock_numbering A v n \<equiv>
    clock_numbering' v n \<and> (\<forall> c \<in> clk_set A. v c \<le> n) \<and> (\<forall>k\<le>n. k > 0 \<longrightarrow> (\<exists>c. v c = k))"

lemma dbm_int_all_abstra:
  assumes "dbm_int_all M" "snd (constraint_pair ac) \<in> \<int>"
  shows "dbm_int_all (abstra ac M v)"
using assms by (cases ac) (auto split: split_min)

lemma dbm_int_all_abstr:
  assumes "dbm_int_all M" "\<forall> (x, m) \<in> collect_clock_pairs g. m \<in> \<int>"
  shows "dbm_int_all (abstr g M v)"
using assms
proof (induction g arbitrary: M)
  case Nil
  then show ?case by auto
next
  case (Cons ac cc)
  from Cons.IH[OF dbm_int_all_abstra, OF Cons.prems(1)] Cons.prems(2-) have
    "dbm_int_all (abstr cc (abstra ac M v) v)"
  unfolding collect_clock_pairs_def by force
  then show ?case by auto
qed

lemma dbm_int_all_abstr':
  assumes "\<forall> (x, m) \<in> collect_clock_pairs g. m \<in> \<int>"
  shows "dbm_int_all (abstr g (\<lambda>i j. \<infinity>) v)"
 apply (rule dbm_int_all_abstr)
using assms by auto

lemma dbm_int_all_inv_abstr:
  assumes "\<forall>(x,m) \<in> clkp_set A. m \<in> \<nat>"
  shows "dbm_int_all (abstr (inv_of A l) (\<lambda>i j. \<infinity>) v)"
proof -
  from assms have "\<forall> (x, m) \<in> collect_clock_pairs (inv_of A l). m \<in> \<int>"
  unfolding clkp_set_def collect_clki_def inv_of_def using Nats_subset_Ints by auto
  from dbm_int_all_abstr'[OF this] show ?thesis .
qed

lemma dbm_int_all_guard_abstr:
  assumes "\<forall> (x, m) \<in> clkp_set A. m \<in> \<nat>" "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"
  shows "dbm_int_all (abstr g (\<lambda>i j. \<infinity>) v)"
proof -
  from assms have "\<forall> (x, m) \<in> collect_clock_pairs g. m \<in> \<int>"
  unfolding clkp_set_def collect_clkt_def using assms(2) Nats_subset_Ints by fastforce
  from dbm_int_all_abstr'[OF this] show ?thesis .
qed

lemma dbm_int_abstra:
  assumes "dbm_int M n" "snd (constraint_pair ac) \<in> \<int>"
  shows "dbm_int (abstra ac M v) n"
using assms by (cases ac) (auto split: split_min)

lemma dbm_int_abstr:
  assumes "dbm_int M n" "\<forall> (x, m) \<in> collect_clock_pairs g. m \<in> \<int>"
  shows "dbm_int (abstr g M v) n"
using assms
proof (induction g arbitrary: M)
  case Nil
  then show ?case by auto
next
  case (Cons ac cc)
  from Cons.IH[OF dbm_int_abstra, OF Cons.prems(1)] Cons.prems(2-) have
    "dbm_int (abstr cc (abstra ac M v) v) n"
  unfolding collect_clock_pairs_def by force
  then show ?case by auto
qed

lemma dbm_int_abstr':
  assumes "\<forall> (x, m) \<in> collect_clock_pairs g. m \<in> \<int>"
  shows "dbm_int (abstr g (\<lambda>i j. \<infinity>) v) n"
 apply (rule dbm_int_abstr)
using assms by auto

lemma int_zone_dbm:
  assumes "clock_numbering' v n"
    "\<forall> (_,d) \<in> collect_clock_pairs cc. d \<in> \<int>" "\<forall> c \<in> collect_clks cc. v c \<le> n"
  obtains M where "{u. u \<turnstile> cc} = [M]\<^bsub>v,n\<^esub>"
            and   "\<forall> i \<le> n. \<forall> j \<le> n. M i j \<noteq> \<infinity> \<longrightarrow> get_const (M i j) \<in> \<int>"
proof -
  let ?M = "abstr cc (\<lambda>i j. \<infinity>) v"
  from assms(2) have "\<forall> i \<le> n. \<forall> j \<le> n. ?M i j \<noteq> \<infinity> \<longrightarrow> get_const (?M i j) \<in> \<int>"
  by (rule dbm_int_abstr')
  with dbm_abstr_zone_eq[OF assms(1) assms(3)] show ?thesis by (auto intro: that)
qed

lemma dbm_int_inv_abstr:
  assumes "\<forall>(x,m) \<in> clkp_set A. m \<in> \<nat>"
  shows "dbm_int (abstr (inv_of A l) (\<lambda>i j. \<infinity>) v) n"
proof -
  from assms have "\<forall> (x, m) \<in> collect_clock_pairs (inv_of A l). m \<in> \<int>"
  unfolding clkp_set_def collect_clki_def inv_of_def using Nats_subset_Ints by auto
  from dbm_int_abstr'[OF this] show ?thesis .
qed

lemma dbm_int_guard_abstr:
  assumes "\<forall> (x, m) \<in> clkp_set A. m \<in> \<nat>" "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"
  shows "dbm_int (abstr g (\<lambda>i j. \<infinity>) v) n"
proof -
  from assms have "\<forall> (x, m) \<in> collect_clock_pairs g. m \<in> \<int>"
  unfolding clkp_set_def collect_clkt_def using assms(2) Nats_subset_Ints by fastforce
  from dbm_int_abstr'[OF this] show ?thesis .
qed

lemma collect_clks_id: "collect_clks cc = fst ` collect_clock_pairs cc"
proof -
  have "constraint_clk ac = fst (constraint_pair ac)" for ac by (cases ac) auto
  then show ?thesis unfolding collect_clks_def collect_clock_pairs_def by auto
qed

end
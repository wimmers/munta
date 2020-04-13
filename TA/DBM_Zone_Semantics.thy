subsection \<open>Semantics Based on DBMs\<close>

theory DBM_Zone_Semantics
imports TA_DBM_Operations
begin

no_notation infinity ("\<infinity>")
hide_const (open) D

subsection \<open>Single Step\<close>

inductive step_z_dbm ::
  "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> 't :: {linordered_cancel_ab_monoid_add,uminus} DBM
    \<Rightarrow> ('c \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 'a action \<Rightarrow> 's \<Rightarrow> 't DBM \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto>\<^bsub>_,_,_\<^esub> \<langle>_, _\<rangle>" [61,61,61,61] 61)
where
  step_t_z_dbm:
    "D_inv = abstr (inv_of A l) (\<lambda>i j. \<infinity>) v \<Longrightarrow> A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l,And (up D) D_inv\<rangle>" |
  step_a_z_dbm:
    "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'
    \<Longrightarrow> A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>v,n,\<upharpoonleft>a\<^esub> \<langle>l',And (reset' (And D (abstr g (\<lambda>i j. \<infinity>) v)) n r v 0)
                                             (abstr (inv_of A l') (\<lambda>i j. \<infinity>) v)\<rangle>"
inductive_cases step_z_t_cases: "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l', D'\<rangle>"
inductive_cases step_z_a_cases: "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,\<upharpoonleft>a\<^esub> \<langle>l', D'\<rangle>"
lemmas step_z_cases = step_z_a_cases step_z_t_cases

declare step_z_dbm.intros[intro]

lemma step_z_dbm_preserves_int_all:
  fixes D D' :: "('t :: {time, ring_1} DBM)"
  assumes "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l',D'\<rangle>" "global_clock_numbering A v n" "\<forall> (x, m) \<in> clkp_set A. m \<in> \<nat>"
          "dbm_int_all D"
  shows "dbm_int_all D'"
using assms
proof (cases, goal_cases)
  case (1 D'')
  hence "\<forall>c\<in>clk_set A. v c \<le> n" by blast+
  from dbm_int_all_inv_abstr[OF 1(2)] 1 have D''_int: "dbm_int_all D''" by simp
  show ?thesis unfolding 1(6)
    by (intro And_int_all_preservation up_int_all_preservation dbm_int_inv_abstr D''_int 1)
next
  case (2 g a r)
  hence assms: "clock_numbering' v n" "\<forall>c\<in>clk_set A. v c \<le> n"
    by blast+
  from dbm_int_all_inv_abstr[OF 2(2)] have D'_int:
    "dbm_int_all (abstr (inv_of A l') (\<lambda>i j. \<infinity>) v)"
  by simp
  from dbm_int_all_guard_abstr 2 have D''_int: "dbm_int_all (abstr g (\<lambda>i j. \<infinity>) v)" by simp
  have "set r \<subseteq> clk_set A" using 2(6) unfolding trans_of_def collect_clkvt_def by fastforce
  hence *:"\<forall>c\<in>set r. v c \<le> n" using assms(2) by fastforce
  show ?thesis unfolding 2(5)
  by (intro And_int_all_preservation DBM_reset'_int_all_preservation dbm_int_all_inv_abstr 2 D''_int)
     (simp_all add: assms(1) *)
qed

lemma step_z_dbm_preserves_int:
  fixes D D' :: "('t :: {time, ring_1} DBM)"
  assumes "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l',D'\<rangle>" "global_clock_numbering A v n" "\<forall> (x, m) \<in> clkp_set A. m \<in> \<nat>"
          "dbm_int D n"
  shows "dbm_int D' n"
using assms
proof (cases, goal_cases)
  case (1 D'')
  from dbm_int_inv_abstr[OF 1(2)] 1 have D''_int: "dbm_int D'' n" by simp
  show ?thesis unfolding 1(6)
    by (intro And_int_preservation up_int_preservation dbm_int_inv_abstr D''_int 1)
next
  case (2 g a r)
  hence assms: "clock_numbering' v n" "\<forall>c\<in>clk_set A. v c \<le> n"
    by blast+
  from dbm_int_inv_abstr[OF 2(2)] have D'_int: "dbm_int (abstr (inv_of A l') (\<lambda>i j. \<infinity>) v) n"
    by simp
  from dbm_int_guard_abstr 2 have D''_int: "dbm_int (abstr g (\<lambda>i j. \<infinity>) v) n" by simp
  have "set r \<subseteq> clk_set A" using 2(6) unfolding trans_of_def collect_clkvt_def by fastforce
  hence *:"\<forall>c\<in>set r. v c \<le> n" using assms(2) by fastforce
  show ?thesis unfolding 2(5)
  by (intro And_int_preservation DBM_reset'_int_preservation dbm_int_inv_abstr 2 D''_int)
     (simp_all add: assms(1) 2(2) *)
qed

lemma up_correct:
  assumes "clock_numbering' v n"
  shows "[up M]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>\<^sup>\<up>"
using assms
 apply safe
  apply (rule DBM_up_sound')
   apply assumption+
 apply (rule DBM_up_complete')
  apply auto
done

lemma step_z_dbm_sound:
  assumes "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', D'\<rangle>" "global_clock_numbering A v n"
  shows "A \<turnstile> \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l', [D']\<^bsub>v,n\<^esub>\<rangle>"
using assms
proof (cases, goal_cases)
  case (1 D'')
  hence "clock_numbering' v n" "\<forall>c\<in>clk_set A. v c \<le> n" by blast+
  note assms = assms(1) this
  from assms(3) have *: "\<forall>c\<in>collect_clks (inv_of A l). v c \<le> n"
  unfolding clkp_set_def collect_clki_def inv_of_def by (fastforce simp: collect_clks_id)
  from 1 have D'':"[D'']\<^bsub>v,n\<^esub> = {u. u \<turnstile> inv_of A l}" using dbm_abstr_zone_eq[OF assms(2) *] by metis
  with And_correct have A11: "[And D D'']\<^bsub>v,n\<^esub> = ([D]\<^bsub>v,n\<^esub>) \<inter> ({u. u \<turnstile> inv_of A l})" by blast
  from D'' have
    "[D']\<^bsub>v,n\<^esub> = ([up D]\<^bsub>v,n\<^esub>) \<inter> ({u. u \<turnstile> inv_of A l})"
    unfolding 1(4) And_correct[symmetric] by simp
  with up_correct[OF assms(2)] A11 have "[D']\<^bsub>v,n\<^esub> = ([D]\<^bsub>v,n\<^esub>)\<^sup>\<up> \<inter> {u. u \<turnstile> inv_of A l}" by metis
  then show ?thesis by (auto simp: 1(2,3))
next
  case (2 g a r)
  hence "clock_numbering' v n" "\<forall>c\<in>clk_set A. v c \<le> n" "\<forall>k\<le>n. k > 0 \<longrightarrow> (\<exists>c. v c = k)" by blast+
  note assms = assms(1) this
  from assms(3) have *: "\<forall>c\<in>collect_clks (inv_of A l'). v c \<le> n"
  unfolding clkp_set_def collect_clki_def inv_of_def by (fastforce simp: collect_clks_id)
  have D':
    "[abstr (inv_of A l') (\<lambda>i j. \<infinity>) v]\<^bsub>v,n\<^esub> = {u. u \<turnstile> inv_of A l'}"
  using 2 dbm_abstr_zone_eq[OF assms(2) *] by simp
  from assms(3) 2(4) have *: "\<forall>c\<in>collect_clks g. v c \<le> n"
  unfolding clkp_set_def collect_clkt_def inv_of_def by (fastforce simp: collect_clks_id)
  have D'':"[abstr g (\<lambda>i j. \<infinity>) v]\<^bsub>v,n\<^esub> = {u. u \<turnstile> g}" using 2 dbm_abstr_zone_eq[OF assms(2) *] by auto
  with And_correct have A11: "[And D (abstr g (\<lambda>i j. \<infinity>) v)]\<^bsub>v,n\<^esub> = ([D]\<^bsub>v,n\<^esub>) \<inter> ({u. u \<turnstile> g})" by blast
  let ?D = "reset' (And D (abstr g (\<lambda>i j. \<infinity>) v)) n r v 0"
  have "set r \<subseteq> clk_set A" using 2(4) unfolding trans_of_def collect_clkvt_def by fastforce
  hence **:"\<forall>c\<in>set r. v c \<le> n" using assms(3) by fastforce
  have D_reset: "[?D]\<^bsub>v,n\<^esub> = zone_set (([D]\<^bsub>v,n\<^esub>) \<inter> {u. u \<turnstile> g}) r"
  proof safe
    fix u assume u: "u \<in> [?D]\<^bsub>v,n\<^esub>"
    from DBM_reset'_sound[OF assms(4,2) ** this] obtain ts where
      "set_clocks r ts u \<in> [And D (abstr g (\<lambda>i j. \<infinity>) v)]\<^bsub>v,n\<^esub>"
    by auto
    with A11 have *: "set_clocks r ts u \<in> ([D]\<^bsub>v,n\<^esub>) \<inter> ({u. u \<turnstile> g})" by blast
    from DBM_reset'_resets[OF assms(4,2) **] u
    have "\<forall>c \<in> set r. u c = 0" unfolding DBM_zone_repr_def by auto
    from reset_set[OF this] have "[r\<rightarrow>0]set_clocks r ts u = u" by simp
    with * show "u \<in> zone_set (([D]\<^bsub>v,n\<^esub>) \<inter> {u. u \<turnstile> g}) r" unfolding zone_set_def by force
  next
    fix u assume u: "u \<in> zone_set (([D]\<^bsub>v,n\<^esub>) \<inter> {u. u \<turnstile> g}) r"
    from DBM_reset'_complete[OF _ assms(2) **] u A11
    show "u \<in> [?D]\<^bsub>v,n\<^esub>" unfolding DBM_zone_repr_def zone_set_def by force
  qed
  from D' And_correct D_reset have A22:
    "[And ?D (abstr (inv_of A l') (\<lambda>i j. \<infinity>) v)]\<^bsub>v,n\<^esub> = ([?D]\<^bsub>v,n\<^esub>) \<inter> ({u. u \<turnstile> inv_of A l'})"
  by blast
  with D_reset 2(2-4) show ?thesis by auto
qed

lemma step_z_dbm_DBM:
  assumes "A \<turnstile> \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l', Z\<rangle>" "global_clock_numbering A v n"
  obtains D' where "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', D'\<rangle>" "Z = [D']\<^bsub>v,n\<^esub>"
using assms
proof (cases, goal_cases)
  case 1
  hence "clock_numbering' v n" "\<forall>c\<in>clk_set A. v c \<le> n" by metis+
  note assms = assms(1) this
  from assms(3) have *: "\<forall>c\<in>collect_clks (inv_of A l). v c \<le> n"
  unfolding clkp_set_def collect_clki_def inv_of_def by (fastforce simp: collect_clks_id)
  obtain D'' where D''_def: "D'' = abstr (inv_of A l) (\<lambda>i j. \<infinity>) v" by auto
  hence D'':"[D'']\<^bsub>v,n\<^esub> = {u. u \<turnstile> inv_of A l}" using dbm_abstr_zone_eq[OF assms(2) *] by metis
  obtain D_up where D_up': "D_up = up D" by blast
  with up_correct assms(2) have D_up: "[D_up]\<^bsub>v,n\<^esub> = ([D]\<^bsub>v,n\<^esub>)\<^sup>\<up>" by metis
  obtain A2 where A2: "A2 = And D_up D''" by fast
  with And_correct D'' have A22: "[A2]\<^bsub>v,n\<^esub> = ([D_up]\<^bsub>v,n\<^esub>) \<inter> ({u. u \<turnstile> inv_of A l})" by blast
  have "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l, A2\<rangle>" unfolding A2 D_up' D''_def by blast
  moreover have
    "[A2]\<^bsub>v,n\<^esub> = ([D]\<^bsub>v,n\<^esub>)\<^sup>\<up> \<inter> {u. u \<turnstile> inv_of A l}"
  unfolding A22 D_up ..
  ultimately show thesis using 1 by (intro that[of A2]) auto
next
  case (2 g a r)
  hence "clock_numbering' v n" "\<forall>c\<in>clk_set A. v c \<le> n" "\<forall>k\<le>n. k > 0 \<longrightarrow> (\<exists>c. v c = k)" by metis+
  note assms = assms(1) this
  from assms(3) have *: "\<forall>c\<in>collect_clks (inv_of A l'). v c \<le> n"
  unfolding clkp_set_def collect_clki_def inv_of_def by (fastforce simp: collect_clks_id)
  obtain D' where D'_def: "D' = abstr (inv_of A l') (\<lambda>i j. \<infinity>) v" by blast
  hence D':"[D']\<^bsub>v,n\<^esub> = {u. u \<turnstile> inv_of A l'}" using dbm_abstr_zone_eq[OF assms(2) *] by simp
  from assms(3) 2(5) have *: "\<forall>c\<in>collect_clks g. v c \<le> n"
  unfolding clkp_set_def collect_clkt_def inv_of_def by (fastforce simp: collect_clks_id)
  obtain D'' where D''_def: "D'' = abstr g (\<lambda>i j. \<infinity>) v" by blast
  hence D'':"[D'']\<^bsub>v,n\<^esub> = {u. u \<turnstile> g}" using dbm_abstr_zone_eq[OF assms(2) *] by auto
  obtain A1 where A1: "A1 = And D D''" by fast
  with And_correct D'' have A11: "[A1]\<^bsub>v,n\<^esub> = ([D]\<^bsub>v,n\<^esub>) \<inter> ({u. u \<turnstile> g})" by blast
  let ?D = "reset' A1 n r v 0"
  have "set r \<subseteq> clk_set A" using 2(5) unfolding trans_of_def collect_clkvt_def by fastforce
  hence **:"\<forall>c\<in>set r. v c \<le> n" using assms(3) by fastforce
  have D_reset: "[?D]\<^bsub>v,n\<^esub> = zone_set (([D]\<^bsub>v,n\<^esub>) \<inter> {u. u \<turnstile> g}) r"
  proof safe
    fix u assume u: "u \<in> [?D]\<^bsub>v,n\<^esub>"
    from DBM_reset'_sound[OF assms(4,2) ** this] obtain ts where
      "set_clocks r ts u \<in> [A1]\<^bsub>v,n\<^esub>"
    by auto
    with A11 have *: "set_clocks r ts u \<in> ([D]\<^bsub>v,n\<^esub>) \<inter> ({u. u \<turnstile> g})" by blast
    from DBM_reset'_resets[OF assms(4,2) **] u
    have "\<forall>c \<in> set r. u c = 0" unfolding DBM_zone_repr_def by auto
    from reset_set[OF this] have "[r\<rightarrow>0]set_clocks r ts u = u" by simp
    with * show "u \<in> zone_set (([D]\<^bsub>v,n\<^esub>) \<inter> {u. u \<turnstile> g}) r" unfolding zone_set_def by force
  next
    fix u assume u: "u \<in> zone_set (([D]\<^bsub>v,n\<^esub>) \<inter> {u. u \<turnstile> g}) r"
    from DBM_reset'_complete[OF _ assms(2) **] u A11
    show "u \<in> [?D]\<^bsub>v,n\<^esub>" unfolding DBM_zone_repr_def zone_set_def by force
  qed
  obtain A2 where A2: "A2 = And ?D D'" by fast
  with And_correct D' have A22: "[A2]\<^bsub>v,n\<^esub> = ([?D]\<^bsub>v,n\<^esub>) \<inter> ({u. u \<turnstile> inv_of A l'})" by blast
  from 2(5) A2 D'_def D''_def A1 have "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>v,n,\<upharpoonleft>a\<^esub> \<langle>l',A2\<rangle>" by blast
  moreover from A22 D_reset have
    "[A2]\<^bsub>v,n\<^esub> = zone_set (([D]\<^bsub>v,n\<^esub>) \<inter> {u. u \<turnstile> g}) r \<inter> {u. u \<turnstile> inv_of A l'}"
  by auto
  ultimately show ?thesis using 2 by (intro that[of A2]) simp+
qed

lemma step_z_computable:
  assumes "A \<turnstile> \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l',Z\<rangle>" "global_clock_numbering A v n"
  obtains D' where "Z = [D']\<^bsub>v,n\<^esub>"
using step_z_dbm_DBM[OF assms] by blast

lemma step_z_dbm_complete:
  assumes "global_clock_numbering A v n" "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>"
  and     "u \<in> [(D )]\<^bsub>v,n\<^esub>"
  shows "\<exists> D' a. A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l',D'\<rangle> \<and> u' \<in> [D']\<^bsub>v,n\<^esub>"
proof -
  note A = assms
  from step_z_complete[OF A(2,3)] obtain Z' a where Z':
    "A \<turnstile> \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l',Z'\<rangle>" "u' \<in> Z'" by auto
  with step_z_dbm_DBM[OF Z'(1) A(1)] obtain D' where D':
    "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l',D'\<rangle>" "Z' = [D']\<^bsub>v,n\<^esub>"
  by metis
  with Z'(2) show ?thesis by auto
qed


subsection \<open>Additional Useful Properties\<close>

lemma step_z_equiv:
  assumes "global_clock_numbering A v n" "A \<turnstile> \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l', Z\<rangle>" "[D]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>"
  shows "A \<turnstile> \<langle>l, [M]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l', Z\<rangle>"
using step_z_dbm_complete[OF assms(1)] step_z_dbm_sound[OF _ assms(1), THEN step_z_sound]
assms(2,3) by force

lemma step_z_dbm_equiv:
  assumes "global_clock_numbering A v n" "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', D'\<rangle>" "[D]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>"
  shows "\<exists> M'. A \<turnstile> \<langle>l, M\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', M'\<rangle> \<and> [D']\<^bsub>v,n\<^esub> = [M']\<^bsub>v,n\<^esub>"
proof -
  from step_z_dbm_sound[OF assms(2,1)] have "A \<turnstile> \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l', [D']\<^bsub>v,n\<^esub>\<rangle>" .
  with step_z_equiv[OF assms(1) this assms(3)] have "A \<turnstile> \<langle>l, [M]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l', [D']\<^bsub>v,n\<^esub>\<rangle>" by auto
  from step_z_dbm_DBM[OF this assms(1)] show ?thesis by auto
qed

lemma step_z_empty:
  assumes "A \<turnstile> \<langle>l, {}\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l', Z\<rangle>"
  shows "Z = {}"
using step_z_sound[OF assms] by auto

lemma step_z_dbm_empty:
  assumes "global_clock_numbering A v n" "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', D'\<rangle>" "[D]\<^bsub>v,n\<^esub> = {}"
  shows "[D']\<^bsub>v,n\<^esub> = {}"
using step_z_dbm_sound[OF assms(2,1)] assms(3) by - (rule step_z_empty, auto)

end
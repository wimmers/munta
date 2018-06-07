chapter \<open>Forward Analysis with DBMs and Widening\<close>

theory Normalized_Zone_Semantics
  imports DBM_Zone_Semantics Approx_Beta Simulation_Graphs_TA
begin

no_notation infinity ("\<infinity>")

(* XXX Move *)
lemma rtranclp_backwards_invariant_iff:
  assumes invariant: "\<And> y z. E\<^sup>*\<^sup>* x y \<Longrightarrow> P z \<Longrightarrow> E y z \<Longrightarrow> P y"
    and E': "E' = (\<lambda> x y. E x y \<and> P y)"
  shows "E'\<^sup>*\<^sup>* x y \<and> P x \<longleftrightarrow> E\<^sup>*\<^sup>* x y \<and> P y"
  unfolding E'
  by (safe; induction rule: rtranclp_induct; auto dest: invariant intro: rtranclp.intros(2))

(* XXX Move *)
context Bisimulation_Invariant
begin

context
  fixes \<phi> :: "'a \<Rightarrow> bool" and \<psi> :: "'b \<Rightarrow> bool"
  assumes compatible: "a \<sim> b \<Longrightarrow> PA a \<Longrightarrow> PB b \<Longrightarrow> \<phi> a \<longleftrightarrow> \<psi> b"
begin

lemma reaches_ex_iff:
  "(\<exists> b. A.reaches a b \<and> \<phi> b) \<longleftrightarrow> (\<exists> b. B.reaches a' b \<and> \<psi> b)" if "a \<sim> a'" "PA a" "PB a'"
  using that by (force simp: compatible equiv'_def dest: bisim.A_B_reaches bisim.B_A_reaches)

lemma reaches_all_iff:
  "(\<forall> b. A.reaches a b \<longrightarrow> \<phi> b) \<longleftrightarrow> (\<forall> b. B.reaches a' b \<longrightarrow> \<psi> b)" if "a \<sim> a'" "PA a" "PB a'"
  using that by (force simp: compatible equiv'_def dest: bisim.A_B_reaches bisim.B_A_reaches)

end (* Context for Compatibility *)

end (* Bisimulation Invariant *)

(* XXX Move *)
lemma step_z_dbm_delay_loc:
  "l' = l" if "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l', D'\<rangle>"
  using that by (auto elim!: step_z_dbm.cases)

lemma step_z_dbm_action_state_set1:
  "l \<in> state_set A" if "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,\<upharpoonleft>a\<^esub> \<langle>l', D'\<rangle>"
  using that by (auto elim!: step_z_dbm.cases intro: state_setI1)

lemma step_z_dbm_action_state_set2:
  "l' \<in> state_set A" if "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,\<upharpoonleft>a\<^esub> \<langle>l', D'\<rangle>"
  using that by (auto elim!: step_z_dbm.cases intro: state_setI2)

lemma step_delay_loc:
  "l' = l" if "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l', u'\<rangle>"
  using that by (auto elim!: step_t.cases)

lemma step_a_state_set1:
  "l \<in> state_set A" if "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l', u'\<rangle>"
  using that by (auto elim!: step_a.cases intro: state_setI1)

lemma step'_state_set1:
  "l \<in> state_set A" if "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>"
  using that by (auto elim!: step'.cases intro: step_a_state_set1 dest: step_delay_loc)

section \<open>DBM-based Semantics with Normalization\<close>

subsection \<open>Single Step\<close>

inductive step_z_norm ::
  "('a, 'c, t, 's) ta
  \<Rightarrow> 's \<Rightarrow> t DBM \<Rightarrow> ('s \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> ('c \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 'a action \<Rightarrow> 's \<Rightarrow> t DBM \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto>\<^bsub>_,_,_,_\<^esub> \<langle>_, _\<rangle>" [61,61,61,61,61,61] 61)
where step_z_norm:
  "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', D'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>k,v,n,a\<^esub> \<langle>l', norm (FW D' n) (k l') n\<rangle>"

inductive step_z_norm' ::
  "('a, 'c, t, 's) ta \<Rightarrow> 's \<Rightarrow> t DBM \<Rightarrow> ('s \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> ('c \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> t DBM \<Rightarrow> bool"
("_ \<turnstile>' \<langle>_, _\<rangle> \<leadsto>\<^bsub>_,_,_\<^esub> \<langle>_, _\<rangle>" [61,61,61,61,61] 61)
where
  step: "A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l'', Z''\<rangle>
        \<Longrightarrow> A \<turnstile> \<langle>l'', Z''\<rangle> \<leadsto>\<^bsub>k,v,n,\<upharpoonleft>(a)\<^esub> \<langle>l''', Z'''\<rangle>
        \<Longrightarrow> A \<turnstile>' \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>k,v,n\<^esub> \<langle>l''', Z'''\<rangle>"

abbreviation steps_z_norm ::
  "('a, 'c, t, 's) ta \<Rightarrow> 's \<Rightarrow> t DBM \<Rightarrow> ('s \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> ('c \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> t DBM \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto>\<^bsub>_,_,_\<^esub>* \<langle>_, _\<rangle>" [61,61,61,61,61] 61) where
 "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>k,v,n\<^esub>* \<langle>l', D'\<rangle> \<equiv> (\<lambda> (l, Z) (l', Z'). A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsub>k,v,n\<^esub> \<langle>l', Z'\<rangle>)\<^sup>*\<^sup>* (l, D) (l', D')"

lemma norm_empty_diag_preservation_real:
  fixes k :: "nat \<Rightarrow> nat"
  assumes "i \<le> n"
  assumes "M i i < Le 0"
  shows "norm M (real o k) n i i < Le 0"
using assms unfolding norm_def by (force simp: Let_def less dest: dbm_lt_trans)

context Regions_defs
begin

inductive valid_dbm where
  "[M]\<^bsub>v,n\<^esub> \<subseteq> V \<Longrightarrow> dbm_int M n \<Longrightarrow> valid_dbm M"

inductive_cases valid_dbm_cases[elim]: "valid_dbm M"

declare valid_dbm.intros[intro]

end (* End of context for augmenting definitions for local and global sets of regions *)

locale Regions_common =
  Regions_defs X v n for X :: "'c set" and v n +
  fixes not_in_X
  assumes finite: "finite X"
  assumes clock_numbering: "clock_numbering' v n" "\<forall>k\<le>n. k > 0 \<longrightarrow> (\<exists>c \<in> X. v c = k)"
                           "\<forall> c \<in> X. v c \<le> n"
  assumes not_in_X: "not_in_X \<notin> X"
  assumes non_empty: "X \<noteq> {}"
begin

lemma FW_zone_equiv_spec:
  shows "[M]\<^bsub>v,n\<^esub> = [FW M n]\<^bsub>v,n\<^esub>"
apply (rule FW_zone_equiv) using clock_numbering(2) by auto

lemma dbm_non_empty_diag:
  assumes "[M]\<^bsub>v,n\<^esub> \<noteq> {}"
  shows "\<forall> k \<le> n. M k k \<ge> 0"
proof safe
  fix k assume k: "k \<le> n"
  have "\<forall>k\<le>n. 0 < k \<longrightarrow> (\<exists>c. v c = k)" using clock_numbering(2) by blast
  from k not_empty_cyc_free[OF this assms(1)] show "0 \<le> M k k" by (simp add: cyc_free_diag_dest')
qed

lemma cn_weak: "\<forall>k\<le>n. 0 < k \<longrightarrow> (\<exists>c. v c = k)" using clock_numbering(2) by blast

lemma negative_diag_empty:
  assumes "\<exists> k \<le> n. M k k < 0"
  shows "[M]\<^bsub>v,n\<^esub> = {}"
using dbm_non_empty_diag assms by force

lemma non_empty_cyc_free:
  assumes "[M]\<^bsub>v,n\<^esub> \<noteq> {}"
  shows "cyc_free M n"
  using FW_neg_cycle_detect FW_zone_equiv_spec assms negative_diag_empty by blast

lemma FW_valid_preservation:
  assumes "valid_dbm M"
  shows "valid_dbm (FW M n)"
proof standard
  from FW_int_preservation assms show "dbm_int (FW M n) n" by blast
next
  from FW_zone_equiv_spec[of M, folded neutral] assms show "[FW M n]\<^bsub>v,n\<^esub> \<subseteq> V" by fastforce
qed

end

context Regions_global
begin

sublocale Regions_common by standard (rule finite clock_numbering not_in_X non_empty)+

abbreviation "v' \<equiv> beta_interp.v'"

lemma apx_empty_iff'':
  assumes "canonical M1 n" "[M1]\<^bsub>v,n\<^esub> \<subseteq> V" "dbm_int M1 n"
  shows "[M1]\<^bsub>v,n\<^esub> = {} \<longleftrightarrow> [norm M1 (k o v') n]\<^bsub>v,n\<^esub> = {}"
  using beta_interp.apx_norm_eq[OF assms] apx_empty_iff'[of "[M1]\<^bsub>v,n\<^esub>"] assms
  unfolding V'_def by blast

lemma norm_FW_empty:
  assumes "valid_dbm M"
  assumes "[M]\<^bsub>v,n\<^esub> = {}"
  shows "[norm (FW M n) (k o v') n]\<^bsub>v,n\<^esub> = {}" (is "[?M]\<^bsub>v,n\<^esub> = {}")
proof -
  from assms(2) cyc_free_not_empty clock_numbering(1) have "\<not> cyc_free M n"
    by metis
  from FW_neg_cycle_detect[OF this] obtain i where i: "i \<le> n" "FW M n i i < 0" by auto
  with norm_empty_diag_preservation_real[folded neutral] have
    "?M i i < 0"
  unfolding comp_def by auto
  with \<open>i \<le> n\<close> show ?thesis using beta_interp.neg_diag_empty_spec by auto
qed

lemma apx_norm_eq_spec:
  assumes "valid_dbm M"
    and "[M]\<^bsub>v,n\<^esub> \<noteq> {}"
  shows "beta_interp.Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>) = [norm (FW M n) (k o v') n]\<^bsub>v,n\<^esub>"
proof -
  note cyc_free = non_empty_cyc_free[OF assms(2)]
  from assms(1) FW_zone_equiv_spec[of M] have "[M]\<^bsub>v,n\<^esub> = [FW M n]\<^bsub>v,n\<^esub>" by (auto simp: neutral)
  with beta_interp.apx_norm_eq[OF fw_canonical[OF cyc_free] _ FW_int_preservation]
      dbm_non_empty_diag[OF assms(2)] assms(1)
 show "Approx\<^sub>\<beta> ([M]\<^bsub>v,n\<^esub>) = [norm (FW M n) (k o v') n]\<^bsub>v,n\<^esub>" by auto
qed

lemma norm_FW_valid_preservation_non_empty:
  assumes "valid_dbm M" "[M]\<^bsub>v,n\<^esub> \<noteq> {}"
  shows "valid_dbm (norm (FW M n) (k o v') n)" (is "valid_dbm ?M")
proof -
  from FW_valid_preservation[OF assms(1)] have valid: "valid_dbm (FW M n)" .
  show ?thesis
  proof standard
    from valid beta_interp.norm_int_preservation show "dbm_int ?M n" by blast
  next
    from fw_canonical[OF non_empty_cyc_free] assms have "canonical (FW M n) n" by auto
    from beta_interp.norm_V_preservation[OF _ this ] valid show "[?M]\<^bsub>v,n\<^esub> \<subseteq> V" by fast
  qed
qed

lemma norm_int_all_preservation:
  fixes M :: "real DBM"
  assumes "dbm_int_all M"
  shows "dbm_int_all (norm M (k o v') n)"
using assms unfolding norm_def by (auto simp: Let_def)

lemma norm_FW_valid_preservation_empty:
  assumes "valid_dbm M" "[M]\<^bsub>v,n\<^esub> = {}"
  shows "valid_dbm (norm (FW M n) (k o v') n)" (is "valid_dbm ?M")
proof -
  from FW_valid_preservation[OF assms(1)] have valid: "valid_dbm (FW M n)" .
  show ?thesis
  proof standard
    from valid beta_interp.norm_int_preservation show "dbm_int ?M n" by blast
  next
    from norm_FW_empty[OF assms(1,2)] show "[?M]\<^bsub>v,n\<^esub> \<subseteq> V" by fast
  qed
qed

lemma norm_FW_valid_preservation:
  assumes "valid_dbm M"
  shows "valid_dbm (norm (FW M n) (k o v') n)"
using assms norm_FW_valid_preservation_empty norm_FW_valid_preservation_non_empty by metis

lemma norm_FW_equiv:
  assumes valid: "dbm_int D n" "dbm_int M n" "[D]\<^bsub>v,n\<^esub> \<subseteq> V"
      and equiv: "[D]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>"
  shows "[norm (FW D n) (k o v') n]\<^bsub>v,n\<^esub> = [norm (FW M n) (k o v') n]\<^bsub>v,n\<^esub>"
proof (cases "[D]\<^bsub>v,n\<^esub> = {}")
  case False
  with equiv fw_shortest[OF non_empty_cyc_free] FW_zone_equiv_spec have
    "canonical (FW D n) n" "canonical (FW M n) n" "[FW D n]\<^bsub>v,n\<^esub> = [D]\<^bsub>v,n\<^esub>" "[FW M n]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>"
  by blast+
  with valid equiv show ?thesis
   apply -
   apply (subst beta_interp.apx_norm_eq[symmetric])
   prefer 4
   apply (subst beta_interp.apx_norm_eq[symmetric])
  by (simp add: FW_int_preservation)+
next
  case True
  show ?thesis
   apply (subst norm_FW_empty)
   prefer 3
   apply (subst norm_FW_empty)
  using valid equiv True by blast+
qed

end (* End of context for global set of regions *)

context Regions
begin

sublocale Regions_common by standard (rule finite clock_numbering not_in_X non_empty)+

definition "v' \<equiv> \<lambda> i. if 0 < i \<and> i \<le> n then (THE c. c \<in> X \<and> v c = i) else not_in_X"
(*abbreviation "v' \<equiv> beta_interp.v'"*)

abbreviation step_z_norm' ("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto>\<^bsub>\<N>(_)\<^esub> \<langle>_, _\<rangle>" [61,61,61,61] 61)
where
  "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l', D'\<rangle> \<equiv> A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>(\<lambda> l. k l o v'),v,n,a\<^esub> \<langle>l', D'\<rangle>"

definition step_z_norm'' ("_ \<turnstile>' \<langle>_, _\<rangle> \<leadsto>\<^bsub>\<N>(_)\<^esub> \<langle>_, _\<rangle>" [61,61,61,61] 61)
where
  "A \<turnstile>' \<langle>l, D\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l'', D''\<rangle> \<equiv>
  \<exists> l' D'. A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l', D'\<rangle> \<and> A \<turnstile> \<langle>l', D'\<rangle> \<leadsto>\<^bsub>\<N>(\<upharpoonleft>a)\<^esub> \<langle>l'', D''\<rangle>"

abbreviation steps_z_norm' ("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto>\<^sub>\<N>* \<langle>_, _\<rangle>" [61,61,61] 61)
where
  "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^sub>\<N>* \<langle>l', D'\<rangle> \<equiv> (\<lambda> (l,D) (l',D'). \<exists> a. A \<turnstile>' \<langle>l, D\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l', D'\<rangle>)\<^sup>*\<^sup>* (l,D) (l',D')"

inductive_cases step_z_norm'_elims[elim!]: "A \<turnstile> \<langle>l, u\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l',u'\<rangle>"

declare step_z_norm.intros[intro]

lemma step_z_valid_dbm:
  assumes "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', D'\<rangle>"
    and "global_clock_numbering A v n" "valid_abstraction A X k" "valid_dbm D"
  shows "valid_dbm D'"
proof -
  from step_z_V step_z_dbm_sound[OF assms(1,2)] step_z_dbm_preserves_int[OF assms(1,2)]
       assms(3,4)
  have
    "dbm_int D' n" "A \<turnstile> \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l', [D']\<^bsub>v,n\<^esub>\<rangle>"
  by (fastforce dest!: valid_abstraction_pairsD)+
  with step_z_V[OF this(2)] assms(4) show ?thesis by auto
qed

(* Crudely copied from step_z_norm.inducts *)
lemma step_z_norm_induct[case_names _ step_z_norm step_z_refl]:
  assumes "x1 \<turnstile> \<langle>x2, x3\<rangle> \<leadsto>\<^bsub>(\<lambda> l. k l o v'),v,n,a\<^esub> \<langle>x7,x8\<rangle>"
    and step_z_norm:
    "\<And>A l D l' D'.
        A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l',D'\<rangle> \<Longrightarrow>
        P A l D l' (norm (FW D' n) (k l' o v') n)"
  shows "P x1 x2 x3 x7 x8"
using assms by (induction rule: step_z_norm.inducts) auto

context
  fixes l' :: 's
begin

interpretation regions: Regions_global _ _ _ "k l'"
  by standard (rule finite clock_numbering not_in_X non_empty)+

lemma [simp]:
  "regions.v' = v'"
  unfolding v'_def regions.beta_interp.v'_def by simp

lemma step_z_norm_int_all_preservation:
  assumes
    "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l',D'\<rangle>" "global_clock_numbering A v n"
    "\<forall>(x, m)\<in>Timed_Automata.clkp_set A. m \<in> \<nat>" "dbm_int_all D"
  shows "dbm_int_all D'"
using assms
 apply cases
 apply simp
 apply (rule regions.norm_int_all_preservation[simplified])
 apply (rule FW_int_all_preservation)
 apply (erule step_z_dbm_preserves_int_all)
by fast+

lemma step_z_norm_valid_dbm_preservation:
  assumes
    "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l',D'\<rangle>" "global_clock_numbering A v n" "valid_abstraction A X k" "valid_dbm D"
  shows "valid_dbm D'"
  using assms
  by cases (simp; rule regions.norm_FW_valid_preservation[simplified]; erule step_z_valid_dbm; fast)

lemma norm_beta_sound:
  assumes "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l',D'\<rangle>" "global_clock_numbering A v n" "valid_abstraction A X k"
  and     "valid_dbm D"
shows   "A \<turnstile> \<langle>l,[D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l',[D']\<^bsub>v,n\<^esub>\<rangle>" using assms(2-)
  apply (induction A l D l' \<equiv> l' D' rule: step_z_norm_induct, (subst assms(1); blast))
proof goal_cases
  case step_z_norm: (1 A l D D')
  from step_z_dbm_sound[OF step_z_norm(1,2)] have "A \<turnstile> \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l',[D']\<^bsub>v,n\<^esub>\<rangle>" by blast
  then have *: "A \<turnstile> \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l',Approx\<^sub>\<beta> l' ([D']\<^bsub>v,n\<^esub>)\<rangle>" by force
  show ?case
  proof (cases "[D']\<^bsub>v,n\<^esub> = {}")
    case False
    from regions.apx_norm_eq_spec[OF step_z_valid_dbm[OF step_z_norm] False] *
    show ?thesis by auto
  next
    case True
    with
      regions.norm_FW_empty[OF step_z_valid_dbm[OF step_z_norm] this] regions.beta_interp.apx_empty *
    show ?thesis by auto
  qed
qed

lemma step_z_norm_valid_dbm:
  assumes
    "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l',D'\<rangle>" "global_clock_numbering A v n"
    "valid_abstraction A X k" "valid_dbm D"
  shows "valid_dbm D'" using assms(2-)
apply (induction A l D l' \<equiv> l' D' rule: step_z_norm_induct, (subst assms(1); blast))
proof goal_cases
  case step_z_norm: (1 A l D D')
  with regions.norm_FW_valid_preservation[OF step_z_valid_dbm[OF step_z_norm]] show ?case by auto
qed

lemma norm_beta_complete:
  assumes "A \<turnstile> \<langle>l,[D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l',Z\<rangle>" "global_clock_numbering A v n" "valid_abstraction A X k"
  and     "valid_dbm D"
  obtains D' where "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l',D'\<rangle>" "[D']\<^bsub>v,n\<^esub> = Z" "valid_dbm D'"
proof -
  from assms(3) have ta_int: "\<forall>(x, m)\<in>Timed_Automata.clkp_set A. m \<in> \<nat>"
    by (fastforce dest!: valid_abstraction_pairsD)
  from assms(1) obtain Z' where Z': "A \<turnstile> \<langle>l,[D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l',Z'\<rangle>" "Z = Approx\<^sub>\<beta> l' Z'" by auto
  from assms(4) have "dbm_int D n" by auto
  with step_z_dbm_DBM[OF Z'(1) assms(2)] step_z_dbm_preserves_int[OF _ assms(2) ta_int] obtain D'
    where D': "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l',D'\<rangle>" "Z' = [D']\<^bsub>v,n\<^esub>" "dbm_int D' n"
  by auto
  note valid_D' = step_z_valid_dbm[OF D'(1) assms(2,3)]
  obtain D'' where D'': "D'' = norm (FW D' n) (k l' \<circ> v') n" by auto
  show ?thesis
  proof (cases "Z' = {}")
    case False
    with D' have *: "[D']\<^bsub>v,n\<^esub> \<noteq> {}" by auto
    from regions.apx_norm_eq_spec[OF valid_D' this] D'' D'(2) Z'(2) assms(4) have "Z = [D'']\<^bsub>v,n\<^esub>"
      by auto
    with regions.norm_FW_valid_preservation[OF valid_D'] D' D'' *  assms(4)
    show thesis
      apply -
      apply (rule that[of D''])
      by (drule step_z_norm.intros[where k = "\<lambda> l. k l o v'"]) simp+
  next
    case True
    with regions.norm_FW_empty[OF valid_D'[OF assms(4)]] D'' D' Z'(2)
         regions.norm_FW_valid_preservation[OF valid_D'[OF assms(4)]] regions.beta_interp.apx_empty
    show thesis
    apply -
    apply (rule that[of D''])
      apply blast
    by fastforce+
  qed
qed

(* XXX Maybe move *)
lemma step_z_norm_mono:
  assumes "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l',D'\<rangle>" "global_clock_numbering A v n" "valid_abstraction A X k"
  and     "valid_dbm D" "valid_dbm M"
  and "[D]\<^bsub>v,n\<^esub> \<subseteq> [M]\<^bsub>v,n\<^esub>"
  shows "\<exists> M'. A \<turnstile> \<langle>l, M\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l', M'\<rangle> \<and> [D']\<^bsub>v,n\<^esub> \<subseteq> [M']\<^bsub>v,n\<^esub>"
proof -
  from norm_beta_sound[OF assms(1,2,3,4)] have "A \<turnstile> \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l', [D']\<^bsub>v,n\<^esub>\<rangle>" .
  from step_z_beta_mono[OF this assms(6)] assms(5) obtain Z where
    "A \<turnstile> \<langle>l, [M]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l', Z\<rangle>" "[D']\<^bsub>v,n\<^esub> \<subseteq> Z"
  by auto
  with norm_beta_complete[OF this(1) assms(2,3,5)] show ?thesis by metis
qed

lemma step_z_norm_equiv:
  assumes step: "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l',D'\<rangle>"
      and prems: "global_clock_numbering A v n" "valid_abstraction A X k"
      and valid: "valid_dbm D" "valid_dbm M"
      and equiv: "[D]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>"
  shows "\<exists> M'. A \<turnstile> \<langle>l, M\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l', M'\<rangle> \<and> [D']\<^bsub>v,n\<^esub> = [M']\<^bsub>v,n\<^esub>"
using step
 apply cases
 apply (frule step_z_dbm_equiv[OF prems(1)])
 apply (rule equiv)
 apply clarify
 apply (drule regions.norm_FW_equiv[rotated 3])
   prefer 4
   apply force
using step_z_valid_dbm[OF _ prems] valid by (simp add: valid_dbm.simps)+

end (* End of context for fixed location *)

subsection \<open>Multi Step\<close>

lemma valid_dbm_V':
  assumes "valid_dbm M"
  shows "[M]\<^bsub>v,n\<^esub> \<in> V'"
using assms unfolding V'_def by force

lemma step_z_empty:
  assumes "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l', Z'\<rangle>" "Z = {}"
  shows "Z' = {}"
  using assms
  apply cases
  unfolding zone_delay_def zone_set_def
  by auto

subsection \<open>Connecting with Correctness Results for Approximating Semantics\<close>

context
  fixes A :: "('a, 'c, real, 's) ta"
    assumes gcn: "global_clock_numbering A v n"
    and va: "valid_abstraction A X k"
begin

context
  notes [intro] = step_z_valid_dbm[OF _ gcn va]
begin

lemma valid_dbm_step_z_norm'':
  "valid_dbm D'" if "A \<turnstile>' \<langle>l, D\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l', D'\<rangle>" "valid_dbm D"
  using that unfolding step_z_norm''_def by (auto intro: step_z_norm_valid_dbm[OF _ gcn va])

lemma steps_z_norm'_valid_dbm_invariant:
  "valid_dbm D'" if "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^sub>\<N>* \<langle>l', D'\<rangle>" "valid_dbm D"
  using that by (induction rule: rtranclp_induct2) (auto intro: valid_dbm_step_z_norm'')

lemma norm_beta_sound'':
  assumes "A \<turnstile>' \<langle>l, D\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l'', D''\<rangle>"
      and "valid_dbm D"
    shows "A \<turnstile> \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l'', [D'']\<^bsub>v,n\<^esub>\<rangle>"
proof -
  from assms(1) obtain l' D' where
    "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l', D'\<rangle>" "A \<turnstile> \<langle>l', D'\<rangle> \<leadsto>\<^bsub>\<N>(\<upharpoonleft>a)\<^esub> \<langle>l'', D''\<rangle>"
    by (auto simp: step_z_norm''_def)
  moreover with \<open>valid_dbm D\<close> have "valid_dbm D'"
    by auto
  ultimately have "A \<turnstile> \<langle>l', [D']\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^bsub>\<beta>\<upharpoonleft>a\<^esub> \<langle>l'', [D'']\<^bsub>v,n\<^esub>\<rangle>"
    by - (rule norm_beta_sound[OF _ gcn va])
  with step_z_dbm_sound[OF \<open>A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l', D'\<rangle>\<close> gcn] show ?thesis
    unfolding step_z_beta'_def by - (frule step_z.cases[where P = "l' = l"]; force)
qed

lemma norm_beta_complete1:
  assumes "A \<turnstile> \<langle>l,[D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l'',Z''\<rangle>"
  and     "valid_dbm D"
  obtains a D'' where "A \<turnstile>' \<langle>l,D\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l'',D''\<rangle>" "[D'']\<^bsub>v,n\<^esub> = Z''" "valid_dbm D''"
proof -
  from assms(1) obtain a l' Z' where steps:
    "A \<turnstile> \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l', Z'\<rangle>" "A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>\<beta>(\<upharpoonleft>a)\<^esub> \<langle>l'', Z''\<rangle>"
    by (auto simp: step_z_beta'_def)
  from step_z_dbm_DBM[OF this(1) gcn] obtain D' where D':
    "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l', D'\<rangle>" "Z' = [D']\<^bsub>v,n\<^esub>"
    by auto
  with \<open>valid_dbm D\<close> have "valid_dbm D'"
    by auto
  from steps D' show ?thesis
    by (auto
        intro!: that[unfolded step_z_norm''_def]
        elim!: norm_beta_complete[OF _ gcn va \<open>valid_dbm D'\<close>]
        )
qed

lemma bisim:
  "Bisimulation_Invariant
  (\<lambda> (l, Z) (l', Z'). A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {})
  (\<lambda> (l, D) (l', D'). \<exists> a. A \<turnstile>' \<langle>l, D\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l', D'\<rangle> \<and> [D']\<^bsub>v,n\<^esub> \<noteq> {})
  (\<lambda> (l, Z) (l', D). l = l' \<and> Z = [D]\<^bsub>v,n\<^esub>)
  (\<lambda> _. True) (\<lambda> (l, D). valid_dbm D)"
proof (standard, goal_cases)
  \<comment> \<open>\<open>\<beta> \<Rightarrow> \<N>\<close>\<close>
  case (1 a b a')
  then show ?case
    by (blast elim: norm_beta_complete1)
next
  \<comment> \<open>\<open>\<N> \<Rightarrow> \<beta>\<close>\<close>
  case (2 a a' b')
  then show ?case
    by (blast intro: norm_beta_sound'')
next
  \<comment> \<open>\<open>\<beta>\<close> invariant\<close>
  case (3 a b)
  then show ?case
    by simp
next
  \<comment> \<open>\<open>\<N>\<close> invariant\<close>
  case (4 a b)
  then show ?case
    unfolding step_z_norm''_def
    by (auto intro: step_z_norm_valid_dbm[OF _ gcn va])
qed

end (* Setup for Automation *)

interpretation Bisimulation_Invariant
  "\<lambda> (l, Z) (l', Z'). A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {}"
  "\<lambda> (l, D) (l', D'). \<exists> a. A \<turnstile>' \<langle>l, D\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l', D'\<rangle> \<and> [D']\<^bsub>v,n\<^esub> \<noteq> {}"
  "\<lambda> (l, Z) (l', D). l = l' \<and> Z = [D]\<^bsub>v,n\<^esub>"
  "\<lambda> _. True" "\<lambda> (l, D). valid_dbm D"
  by (rule bisim)

lemma step_z_norm''_non_empty:
  "[D]\<^bsub>v,n\<^esub> \<noteq> {}" if "A \<turnstile>' \<langle>l, D\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l', D'\<rangle>" "[D']\<^bsub>v,n\<^esub> \<noteq> {}" "valid_dbm D"
proof -
  from that B_A_step[of "(l, D)" "(l', D')" "(l, [D]\<^bsub>v,n\<^esub>)"] have
    "A \<turnstile> \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l', [D']\<^bsub>v,n\<^esub>\<rangle>"
    by auto
  with \<open>_ \<noteq> {}\<close> show ?thesis
    by (auto 4 3 dest: step_z_beta'_empty)
qed

lemma norm_steps_empty:
  "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^sub>\<N>* \<langle>l', D'\<rangle> \<and> [D']\<^bsub>v,n\<^esub> \<noteq> {} \<longleftrightarrow> B.reaches (l, D) (l', D') \<and> [D]\<^bsub>v,n\<^esub> \<noteq> {}"
  if "valid_dbm D"
  apply (subst rtranclp_backwards_invariant_iff[
    of "\<lambda>(l, D) (l', D'). \<exists> a. A \<turnstile>' \<langle>l, D\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l', D'\<rangle>" "(l, D)" "\<lambda>(l, D). [D]\<^bsub>v,n\<^esub> \<noteq> {}",
    simplified
    ])
  using \<open>valid_dbm D\<close>
  by (auto dest!: step_z_norm''_non_empty intro: steps_z_norm'_valid_dbm_invariant)

context
  fixes P Q :: "'s \<Rightarrow> bool" \<comment> \<open>The state property we want to check\<close>
begin

interpretation bisim_\<psi>: Bisimulation_Invariant
  "\<lambda> (l, Z) (l', Z'). A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {} \<and> Q l'"
  "\<lambda> (l, D) (l', D'). \<exists> a. A \<turnstile>' \<langle>l, D\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l', D'\<rangle> \<and> [D']\<^bsub>v,n\<^esub> \<noteq> {} \<and> Q l'"
  "\<lambda> (l, Z) (l', D). l = l' \<and> Z = [D]\<^bsub>v,n\<^esub>"
  "\<lambda> _. True" "\<lambda> (l, D). valid_dbm D"
  by (rule Bisimulation_Invariant_filter[OF bisim, of "\<lambda> (l, _). Q l" "\<lambda> (l, _). Q l"]) auto

end (* Context for State Formulae *)

context
  assumes finite_state_set: "finite (state_set A)"
begin

interpretation R: Regions_TA
  by (standard; rule va finite_state_set)

lemma A_reaches_non_empty:
  "Z' \<noteq> {}" if "A.reaches (l, Z) (l', Z')" "Z \<noteq> {}"
  using that by cases auto

lemma A_reaches_start_non_empty_iff:
  "(\<exists>Z'. (\<exists>u. u \<in> Z') \<and> A.reaches (l, Z) (l', Z')) \<longleftrightarrow> (\<exists>Z'. A.reaches (l, Z) (l', Z')) \<and> Z \<noteq> {}"
  apply safe
    apply blast
  subgoal
    by (auto dest: step_z_beta'_empty elim: converse_rtranclpE2)
  by (auto dest: A_reaches_non_empty)

(* XXX Move *)
lemma step_z_norm''_state_set1:
  "l \<in> state_set A" if "A \<turnstile>' \<langle>l, D\<rangle> \<leadsto>\<^bsub>\<N>a\<^esub> \<langle>l', D'\<rangle>"
  using that unfolding step_z_norm''_def
  by (auto dest: step_z_dbm_delay_loc intro: step_z_dbm_action_state_set1)

lemma step_z_norm''_state_set2:
  "l' \<in> state_set A" if "A \<turnstile>' \<langle>l, D\<rangle> \<leadsto>\<^bsub>\<N>a\<^esub> \<langle>l', D'\<rangle>"
  using that unfolding step_z_norm''_def by (auto intro: step_z_dbm_action_state_set2)

theorem steps_z_norm_decides_emptiness:
  assumes "valid_dbm D"
  shows "(\<exists> D'. A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^sub>\<N>* \<langle>l',D'\<rangle> \<and> [D']\<^bsub>v,n\<^esub> \<noteq> {})
     \<longleftrightarrow> (\<exists> u \<in> [D]\<^bsub>v,n\<^esub>. (\<exists> u'. A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>))"
proof (cases "[D]\<^bsub>v,n\<^esub> = {}")
  case True
  then show ?thesis
    unfolding norm_steps_empty[OF \<open>valid_dbm D\<close>] by auto
next
  case F: False
  show ?thesis
  proof (cases "l \<in> state_set A")
    case True
    interpret Regions_TA_Start_State v n not_in_X X k A l "[D]\<^bsub>v,n\<^esub>"
      using assms F True by - (standard, auto elim!: valid_dbm_V')
    show ?thesis
      unfolding steps'_iff[symmetric] norm_steps_empty[OF \<open>valid_dbm D\<close>]
      using
        reaches_ex_iff[of "\<lambda> (l, _). l = l'" "\<lambda> (l, _). l = l'" "(l, [D]\<^bsub>v,n\<^esub>)" "(l, D)"]
        \<open>valid_dbm D\<close> ta_reaches_ex_iff[of "\<lambda> (l, _). l = l'"]
      by (auto simp: A_reaches_start_non_empty_iff from_R_def a\<^sub>0_def)
  next
    case False
    have "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^sub>\<N>* \<langle>l',D'\<rangle> \<longleftrightarrow> (D' = D \<and> l' = l)" for D'
      using False by (blast dest: step_z_norm''_state_set1 elim: converse_rtranclpE2)
    moreover have "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<longleftrightarrow> (u' = u \<and> l' = l)" for u u'
      unfolding steps'_iff[symmetric] using False
      by (blast dest: step'_state_set1 elim: converse_rtranclpE2)
    ultimately show ?thesis
      using F by auto
  qed
qed

end (* Finite State Set *)

end (* Context for Global Clock Numbering *)

context
  fixes A :: "('a, 'c, real, 's) ta"
    assumes gcn: "global_clock_numbering A v n"
    and va: "valid_abstraction A X k"
begin

lemmas
  step_z_norm_valid_dbm' = step_z_norm_valid_dbm[OF _ gcn va]

lemmas
  step_z_valid_dbm' = step_z_valid_dbm[OF _ gcn va]

lemmas norm_beta_sound' = norm_beta_sound[OF _ gcn va]

lemma v_bound:
  "\<forall> c \<in> clk_set A. v c \<le> n"
  using gcn by blast

lemmas alpha_beta_step'' = alpha_beta_step'[OF _ va v_bound]

lemmas step_z_dbm_sound' = step_z_dbm_sound[OF _ gcn]

lemmas step_z_V'' = step_z_V'[OF _ va v_bound]

end

end

section \<open>Finiteness of the Search Space\<close>

abbreviation "dbm_default M n \<equiv> (\<forall> i > n. \<forall> j. M i j = 0) \<and> (\<forall> j > n. \<forall> i. M i j = 0)"

lemma norm_default_preservation:
  "dbm_default M n \<Longrightarrow> dbm_default (norm M k n) n"
by (simp add: norm_def)

instance int :: linordered_cancel_ab_monoid_add by (standard; simp)

(* XXX Move *)
lemma inf_lt_impl_False[simp]:
  "\<infinity> < x = False"
  by auto

(* XXX Copy from Normalized_Zone_Semantics *)
lemma normalized_integral_dbms_finite:
  "finite {norm M (k :: nat \<Rightarrow> nat) n | M. dbm_default M n}"
proof -
  let ?u = "Max {k i | i. i \<le> n}" let ?l = "- ?u"
  let ?S = "(Le ` {d :: int. ?l \<le> d \<and> d \<le> ?u}) \<union> (Lt ` {d :: int. ?l \<le> d \<and> d \<le> ?u}) \<union> {\<infinity>}"
  from finite_set_of_finite_funs2[of "{0..n}" "{0..n}" ?S] have fin:
    "finite {f. \<forall>x y. (x \<in> {0..n} \<and> y \<in> {0..n} \<longrightarrow> f x y \<in> ?S)
                \<and> (x \<notin> {0..n} \<longrightarrow> f x y = 0) \<and> (y \<notin> {0..n} \<longrightarrow> f x y = 0)}" (is "finite ?R")
  by auto
  { fix M :: "int DBM" assume A: "dbm_default M n"
    let ?M = "norm M k n"
    from norm_default_preservation[OF A] have
      A: "dbm_default ?M n"
    by auto
    { fix i j assume "i \<in> {0..n}" "j \<in> {0..n}"
      then have B: "i \<le> n" "j \<le> n" by auto
      have "?M i j \<in> ?S"
      proof (cases "?M i j = \<infinity>")
        case True then show ?thesis by auto
      next
        case False
        note not_inf = this
        have "?l \<le> get_const (?M i j) \<and> get_const (?M i j) \<le> ?u"
        proof (cases "i = 0")
          case True
          show ?thesis
          proof (cases "j = 0")
            case True
            with \<open>i = 0\<close> A(1) B have
              "?M i j = norm_lower (norm_upper (M 0 0) 0) 0"
            unfolding norm_def by auto
            also have "\<dots> \<noteq> \<infinity> \<longrightarrow> get_const \<dots> = 0" by (cases "M 0 0"; fastforce)
            finally show ?thesis using not_inf by auto
          next
            case False
            with \<open>i = 0\<close> B not_inf have "?M i j \<le> Le 0" "Lt (-int (k j)) \<le> ?M i j"
            unfolding norm_def
              apply (simp del: norm_upper.simps norm_lower.simps)
              apply (auto simp: less[symmetric]; fail)
              using \<open>i = 0\<close> B not_inf apply (auto simp: Let_def less[symmetric] intro: any_le_inf)[]
              apply (drule leI)
              apply (drule leI)
            by (rule order.trans; fastforce)
            with not_inf have "get_const (?M i j) \<le> 0" "-k j \<le> get_const (?M i j)"
            by (cases "?M i j"; auto)+
            moreover from \<open>j \<le> n\<close> have "- k j \<ge> ?l" by (auto intro: Max_ge)
            ultimately show ?thesis by auto
          qed
        next
          case False
          then have "i > 0" by simp
          show ?thesis
          proof (cases "j = 0")
            case True
            with \<open>i > 0\<close> A(1) B not_inf have "Lt 0 \<le> ?M i j" "?M i j \<le> Le (int (k i))"
            unfolding norm_def
              apply (simp del: norm_upper.simps norm_lower.simps)
              apply (auto simp: less[symmetric])[]

             using \<open>i > 0\<close> \<open>j = 0\<close> A(1) B not_inf unfolding norm_def
            by (auto simp: Let_def less[symmetric] intro: any_le_inf)[]
            with not_inf have "0 \<le> get_const (?M i j)" "get_const (?M i j) \<le> k i"
            by (cases "?M i j"; auto)+
            moreover from \<open>i \<le> n\<close> have "k i \<le> ?u" by (auto intro: Max_ge)
            ultimately show ?thesis by auto
          next
            case False
            with \<open>i > 0\<close> A(1) B not_inf have
              "Lt (-int (k j)) \<le> ?M i j" "?M i j \<le> Le (int (k i))"
            unfolding norm_def
              apply (simp del: norm_upper.simps norm_lower.simps)
              apply (auto simp: less[symmetric])[]
             using \<open>i > 0\<close> \<open>j \<noteq> 0\<close> A(1) B not_inf unfolding norm_def
            by (auto simp: Let_def less[symmetric] intro: any_le_inf)[]
            with not_inf have "- k j \<le> get_const (?M i j)" "get_const (?M i j) \<le> k i"
            by (cases "?M i j"; auto)+
            moreover from \<open>i \<le> n\<close> \<open>j \<le> n\<close> have "k i \<le> ?u" "k j \<le> ?u" by (auto intro: Max_ge)
            ultimately show ?thesis by auto
          qed
        qed
        then show ?thesis by (cases "?M i j"; auto elim: Ints_cases)
      qed
    } moreover
    { fix i j assume "i \<notin> {0..n}"
      with A have "?M i j = 0" by auto
    } moreover
    { fix i j assume "j \<notin> {0..n}"
      with A have "?M i j = 0" by auto
    } moreover note the = calculation
  } then have "{norm M k n | M. dbm_default M n} \<subseteq> ?R" by blast
  with fin show ?thesis by (blast intro: finite_subset)
qed

subsection \<open>Additional Useful Properties of the Normalized Semantics\<close>

text \<open>Obsolete\<close>
lemma norm_diag_preservation:
  assumes "\<forall>l\<le>n. M1 l l \<le> 0"
  shows "\<forall>l\<le>n. (norm M1 (k :: nat \<Rightarrow> nat) n) l l \<le> 0" (is "\<forall> l \<le> n. ?M l l \<le> 0")
proof safe
  fix j assume j: "j \<le> n"
  show "?M j j \<le> 0"
  proof (cases "j = 0")
    case True
    with j assms show ?thesis unfolding norm_def neutral less_eq dbm_le_def by auto
  next
    case False
    have *: "k j \<ge> 0" by auto
    from j assms have **: "M1 j j \<le> Le 0" unfolding neutral by auto
    have "norm_upper (M1 j j) (k j) = M1 j j"
    using * ** apply (cases "M1 j j") apply auto by fastforce+
    with assms(1) j False have
      "?M j j = norm_lower (M1 j j) (- k j)"
    unfolding norm_def by auto
    with ** show ?thesis unfolding neutral by auto
  qed
qed

section \<open>Appendix: Standard Clock Numberings for Concrete Models\<close>

locale Regions' =
  fixes X and k :: "'c \<Rightarrow> nat" and v :: "'c \<Rightarrow> nat" and n :: nat and not_in_X
  assumes finite: "finite X"
  assumes clock_numbering': "\<forall> c \<in> X. v c > 0" "\<forall> c. c \<notin> X \<longrightarrow> v c > n"
  assumes bij: "bij_betw v X {1..n}"
  assumes non_empty: "X \<noteq> {}"
  assumes not_in_X: "not_in_X \<notin> X"

begin

lemma inj: "inj_on v X" using bij_betw_imp_inj_on bij by simp

lemma cn_weak: "\<forall> c. v c > 0" using clock_numbering' by force

lemma in_X: assumes "v x \<le> n" shows "x \<in> X" using assms clock_numbering'(2) by force

end

sublocale Regions' \<subseteq> Regions_global
proof (unfold_locales, auto simp: finite clock_numbering' non_empty cn_weak not_in_X, goal_cases)
  case (1 x y) with inj in_X show ?case unfolding inj_on_def by auto
next
  case (2 k)
  from bij have "v ` X = {1..n}" unfolding bij_betw_def by auto
  from 2 have "k \<in> {1..n}" by simp
  then obtain x where "x \<in> X" "v x = k" unfolding image_def
  by (metis (no_types, lifting) \<open>v ` X = {1..n}\<close> imageE)
  then show ?case by blast
next
  case (3 x) with bij show ?case unfolding bij_betw_def by auto
qed

(* This is for automata carrying real time annotations *)
lemma standard_abstraction:
  assumes
    "finite (Timed_Automata.clkp_set A)" "finite (Timed_Automata.collect_clkvt (trans_of A))"
    "\<forall>(_,m::real) \<in> Timed_Automata.clkp_set A. m \<in> \<nat>"
  obtains k :: "'c \<Rightarrow> nat" where "Timed_Automata.valid_abstraction A (clk_set A) k"
proof -
  from assms have 1: "finite (clk_set A)" by auto
  have 2: "Timed_Automata.collect_clkvt (trans_of A) \<subseteq> clk_set A" by auto
  from assms obtain L where L: "distinct L" "set L = Timed_Automata.clkp_set A"
    by (meson finite_distinct_list)
  let ?M = "\<lambda> c. {m . (c, m) \<in> Timed_Automata.clkp_set A}"
  let ?X = "clk_set A"
  let ?m = "map_of L"
  let ?k = "\<lambda> x. if ?M x = {} then 0 else nat (floor (Max (?M x)) + 1)"
  { fix c m assume A: "(c, m) \<in> Timed_Automata.clkp_set A"
    from assms(1) have "finite (snd ` Timed_Automata.clkp_set A)" by auto
    moreover have "?M c \<subseteq> (snd ` Timed_Automata.clkp_set A)" by force
    ultimately have fin: "finite (?M c)" by (blast intro: finite_subset)
    then have "Max (?M c) \<in> {m . (c, m) \<in> Timed_Automata.clkp_set A}" using Max_in A by auto
    with assms(3) have "Max (?M c) \<in> \<nat>" by auto
    then have "floor (Max (?M c)) = Max (?M c)" by (metis Nats_cases floor_of_nat of_int_of_nat_eq)
    with A have *: "?k c = Max (?M c) + 1"
    proof auto
      fix n :: int and x :: real
      assume "Max {m. (c, m) \<in> Timed_Automata.clkp_set A} = real_of_int n"
      then have "real_of_int (n + 1) \<in> \<nat>"
        using \<open>Max {m. (c, m) \<in> Timed_Automata.clkp_set A} \<in> \<nat>\<close> by auto
      then show "real (nat (n + 1)) = real_of_int n + 1"
        by (metis Nats_cases ceiling_of_int nat_int of_int_1 of_int_add of_int_of_nat_eq)
    qed
    from fin A have "Max (?M c) \<ge> m" by auto
    moreover from A assms(3) have "m \<in> \<nat>" by auto
    ultimately have "m \<le> ?k c" "m \<in> \<nat>" "c \<in> clk_set A" using A * by force+
  }
  then have "\<forall>(x, m) \<in> Timed_Automata.clkp_set A. m \<le> ?k x \<and> x \<in> clk_set A \<and> m \<in> \<nat>" by blast
  with 1 2 have "Timed_Automata.valid_abstraction A ?X ?k" by - (standard, assumption+)
  then show thesis ..
qed

definition
  "finite_ta A \<equiv>
    finite (Timed_Automata.clkp_set A) \<and> finite (Timed_Automata.collect_clkvt (trans_of A))
  \<and> (\<forall>(_,m) \<in> Timed_Automata.clkp_set A. m \<in> \<nat>) \<and> clk_set A \<noteq> {} \<and> -clk_set A \<noteq> {}"

lemma finite_ta_Regions':
  fixes A :: "('a, 'c, real, 's) ta"
  assumes "finite_ta A"
  obtains v n x where "Regions' (clk_set A) v n x"
proof -
  from assms obtain x where x: "x \<notin> clk_set A" unfolding finite_ta_def by auto
  from assms(1) have "finite (clk_set A)" unfolding finite_ta_def by auto
  with standard_numbering[of "clk_set A"] assms obtain v and n :: nat where
            "bij_betw v (clk_set A) {1..n}"
            "\<forall>c\<in>clk_set A. 0 < v c" "\<forall>c. c \<notin> clk_set A \<longrightarrow> n < v c"
  by auto
  then have "Regions' (clk_set A) v n x" using x assms unfolding finite_ta_def by - (standard, auto)
  then show ?thesis ..
qed

lemma finite_ta_RegionsD:
  fixes A :: "('a, 'c, t, 's) ta"
  assumes "finite_ta A"
  obtains k :: "'c \<Rightarrow> nat" and v n x where
    "Regions' (clk_set A) v n x" "Timed_Automata.valid_abstraction A (clk_set A) k"
    "global_clock_numbering A v n"
proof -
  from standard_abstraction assms obtain k :: "'c \<Rightarrow> nat" where k:
    "Timed_Automata.valid_abstraction A (clk_set A) k"
  unfolding finite_ta_def by blast
  from finite_ta_Regions'[OF assms] obtain v n x where *: "Regions' (clk_set A) v n x" .
  then interpret interp: Regions' "clk_set A" k v n x .
  from interp.clock_numbering have "global_clock_numbering A v n" by blast
  with * k show ?thesis ..
qed

definition valid_dbm where "valid_dbm M n \<equiv> dbm_int M n \<and> (\<forall> i \<le> n. M 0 i \<le> 0)"

lemma dbm_positive:
  assumes "M 0 (v c) \<le> 0" "v c \<le> n" "DBM_val_bounded v u M n"
  shows "u c \<ge> 0"
proof -
  from assms have "dbm_entry_val u None (Some c) (M 0 (v c))" unfolding DBM_val_bounded_def by auto
  with assms(1) show ?thesis
  proof (cases "M 0 (v c)", goal_cases)
    case 1
    then show ?case unfolding less_eq neutral using order_trans by (fastforce dest!: le_dbm_le)
  next
    case 2
    then show ?case unfolding less_eq neutral
    by (auto dest!: lt_dbm_le) (meson less_trans neg_0_less_iff_less not_less)
  next
    case 3
    then show ?case unfolding neutral less_eq dbm_le_def by auto
  qed
qed

lemma valid_dbm_pos:
  assumes "valid_dbm M n"
  shows "[M]\<^bsub>v,n\<^esub> \<subseteq> {u. \<forall> c. v c \<le> n \<longrightarrow> u c \<ge> 0}"
using dbm_positive assms unfolding valid_dbm_def unfolding DBM_zone_repr_def by fast

lemma (in Regions') V_alt_def:
  shows "{u. \<forall> c. v c > 0 \<and> v c \<le> n \<longrightarrow> u c \<ge> 0} = V"
unfolding V_def using clock_numbering by metis

end (* Theory *)

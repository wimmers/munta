theory Normalized_Zone_Semantics_Certification
  imports Normalized_Zone_Semantics_Impl_Semantic_Refinement
begin

no_notation Reachability_Problem_Defs.step_impl' ("\<langle>_, _\<rangle> \<leadsto>\<^bsub>_\<^esub> \<langle>_, _\<rangle>" [61,61,61] 61)

context Reachability_Problem_Defs
begin

definition
  "E_precise_op l r g l' M \<equiv>
    let
      M' = FW' (abstr_upd (inv_of A l) (up_canonical_upd M n)) n;
      M'' = FW' (abstr_upd (inv_of A l') (reset'_upd (FW' (abstr_upd g M') n) n r 0)) n
    in M''"

definition
  "E_precise_op' l r g l' M \<equiv>
    let
      M1 = abstr_repair (inv_of A l) (up_canonical_upd M n);
      M2 = filter_diag (\<lambda> M. abstr_repair g M) M1;
      M3 = filter_diag (\<lambda> M. abstr_repair (inv_of A l') (reset'_upd M n r 0)) M2
    in M3"

lemma E_precise_op'_alt_def:
  "E_precise_op' l r g l' M \<equiv>
    let
      M' = abstr_repair (inv_of A l) (up_canonical_upd M n);
      f1 = \<lambda> M. abstr_repair g M;
      f2 = \<lambda> M. abstr_repair (inv_of A l') (reset'_upd M n r 0)
    in filter_diag (filter_diag f2 o f1) M'"
  unfolding E_precise_op'_def filter_diag_def by (rule HOL.eq_reflection) (auto simp: Let_def)

no_notation step_impl' ("\<langle>_, _\<rangle> \<leadsto>\<^bsub>_\<^esub> \<langle>_, _\<rangle>" [61,61,61] 61)

abbreviation step_impl_precise ("\<langle>_, _\<rangle> \<leadsto>\<^bsub>_\<^esub> \<langle>_, _\<rangle>" [61,61,61] 61)
where
  "\<langle>l, Z\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l'', Z''\<rangle> \<equiv> \<exists> l' Z'.
    A \<turnstile>\<^sub>I \<langle>l, Z\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l', Z'\<rangle> \<and> A \<turnstile>\<^sub>I \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a\<^esub> \<langle>l'', Z''\<rangle>"

(* sublocale Graph_Defs "\<lambda> (l, u) (l', u'). conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>" . *)

definition "E_precise \<equiv> (\<lambda>(l, Z) (l'', Z''). \<exists>a. \<langle>l, Z\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l'', Z''\<rangle>)"

end



locale E_Precise_Bisim = E_From_Op +
  assumes op_bisim:
    "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<Longrightarrow> wf_dbm M \<Longrightarrow> f l r g l' M \<simeq> E_precise_op l r g l' M"
    and op_wf:
    "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<Longrightarrow> wf_dbm M \<Longrightarrow> wf_dbm (f l r g l' M)"
begin

lemma E_precise_E_op:
  "E_precise = (\<lambda>(l, M) (l', M'''). \<exists>g a r. A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<and> M''' = E_precise_op l r g l' M)"
  unfolding E_precise_op_def E_precise_def by (intro ext) (auto elim!: step_impl.cases)

lemma E_E_from_op_step:
  "\<exists>c. E_from_op a c \<and> b \<sim> c" if "E_precise a b" "wf_state a"
  using that unfolding E_precise_E_op E_from_op_def wf_state_def state_equiv_def
  by (blast intro: op_bisim dbm_equiv_sym)

lemma E_from_op_E_step:
  "\<exists>c. E_precise a c \<and> b \<sim> c" if "E_from_op a b" "wf_state a"
  using that unfolding E_precise_E_op E_from_op_def wf_state_def state_equiv_def
  by (blast intro: op_bisim)

lemma E_from_op_wf_state:
  "wf_state b" if "wf_state a" "E_from_op a b"
  using that unfolding E_E_op E_from_op_def wf_state_def state_equiv_def by (blast intro: op_wf)

lemma E_precise_wf_dbm[intro]:
  "wf_dbm D'" if "E_precise (l, D) (l', D')" "wf_dbm D"
  using that unfolding wf_state_def E_def E_precise_def by (auto intro: step_impl_wf_dbm)

lemma E_precise_wf_state:
  "wf_state a \<Longrightarrow> E_precise a b \<Longrightarrow> wf_state b"
  unfolding wf_state_def by auto

(* lemma E_E_from_op_steps_empty:
  "(\<exists>l' M'. E_precise\<^sup>*\<^sup>* a\<^sub>0 (l', M') \<and> [curry (conv_M M')]\<^bsub>v,n\<^esub> = {}) \<longleftrightarrow>
   (\<exists>l' M'. E_from_op\<^sup>*\<^sup>* a\<^sub>0 (l', M') \<and> [curry (conv_M M')]\<^bsub>v,n\<^esub> = {})"
  by (rule E_E\<^sub>1_steps_empty[OF E_E_from_op_step E_from_op_E_step E_from_op_wf_state]) *)

theorem E_from_op_reachability_check:
  "(\<exists> l' D'. E_precise\<^sup>*\<^sup>* a\<^sub>0 (l', D') \<and> F_rel (l', D'))
  \<longleftrightarrow> (\<exists> l' D'. E_from_op\<^sup>*\<^sup>* a\<^sub>0 (l', D') \<and> F_rel (l', D'))"
  oops
(*   apply (rule E_E\<^sub>1_steps_equiv[OF E_E_from_op_step E_from_op_E_step E_from_op_wf_state])
  by
    (auto
      simp: F_rel_def state_equiv_def wf_state_def dbm_equiv_def
      dest!:
        check_diag_empty_spec[OF check_diag_conv_M]
        canonical_check_diag_empty_iff[OF wf_dbm_altD(1)]
    ) *)

lemma E_from_op_mono:
  assumes "E_from_op (l,D) (l',D')"
    and   "wf_dbm D" "wf_dbm M"
    and "[curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M)]\<^bsub>v,n\<^esub>"
  shows "\<exists> M'. E_from_op (l,M) (l',M') \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M')]\<^bsub>v,n\<^esub>"
  (* using assms by - (rule E\<^sub>1_mono[OF E_E_from_op_step E_from_op_E_step E_from_op_wf_state]; blast) *)
  oops

lemma E_from_op_mono':
  assumes "E_from_op (l,D) (l',D')"
    and   "wf_dbm D" "wf_dbm M"
    and "dbm_subset n D M"
  shows "\<exists> M'. E_from_op (l,M) (l',M') \<and> dbm_subset n D' M'"
  (* using assms by - (rule E\<^sub>1_mono'[OF E_E_from_op_step E_from_op_E_step E_from_op_wf_state]; blast) *)
  oops

  thm E_E_from_op_step E_from_op_E_step E_from_op_wf_state

lemma E_equiv:
  "\<exists> b'. E_precise b b' \<and> a' \<sim> b'" if "E_precise a a'" "a \<sim> b" "wf_state a" "wf_state b"
  using that
  unfolding wf_state_def E_precise_def
  apply safe
  apply (frule step_impl_equiv, assumption, assumption, rule state_equiv_D, assumption)
  by (safe, drule step_impl_equiv, auto intro: step_impl_wf_dbm simp: state_equiv_def)

lemma E_from_op_bisim:
  "Bisimulation_Invariant E_precise E_from_op (\<sim>) wf_state wf_state"
  apply standard
  subgoal
    by (drule E_equiv, assumption+) (auto dest!: E_E_from_op_step)
  subgoal
    by (drule (1) E_from_op_E_step, safe, drule E_equiv) (auto 4 4 intro: state_equiv_sym)
   apply (rule E_precise_wf_state; assumption)
  apply (rule E_from_op_wf_state; assumption)
  done

end (* End of context for bisimilarity *)

definition step_z_dbm' ::
  "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> 't :: {linordered_cancel_ab_monoid_add,uminus} DBM
    \<Rightarrow> ('c \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> 't DBM \<Rightarrow> bool"
("_ \<turnstile>' \<langle>_, _\<rangle> \<leadsto>\<^bsub>_,_,_\<^esub> \<langle>_, _\<rangle>" [61,61,61,61] 61) where
  "A \<turnstile>' \<langle>l,D\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l'',D''\<rangle> \<equiv>
  \<exists>l' D'. A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l', D'\<rangle> \<and> A \<turnstile> \<langle>l', D'\<rangle> \<leadsto>\<^bsub>v,n,\<upharpoonleft>a\<^esub> \<langle>l'', D''\<rangle>"

context Reachability_Problem
begin

lemma E_precise_op'_bisim:
  "E_precise_op' l r g l' M \<simeq> E_precise_op l r g l' M" if "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" "wf_dbm M"
proof -
  note intros =
    dbm_equiv_refl dbm_equiv_trans[OF filter_diag_equiv, rotated]
    wf_dbm_abstr_repair_equiv_FW[rotated] reset'_upd_equiv
  have "\<forall>c\<in>constraint_clk ` set (inv_of A l). 0 < c \<and> c \<le> n"
    using clock_range collect_clks_inv_clk_set[of A l] unfolding collect_clks_def by blast
  moreover have
    "\<forall>c\<in>constraint_clk ` set (inv_of A l'). 0 < c \<and> c \<le> n"
    "\<forall>c\<in>constraint_clk ` set (inv_of A l'). 0 < c"
    using clock_range collect_clks_inv_clk_set[of A l'] unfolding collect_clks_def by blast+
  moreover have "\<forall>c\<in>constraint_clk ` set g. 0 < c \<and> c \<le> n" "\<forall>c\<in>constraint_clk ` set g. 0 < c"
    using clock_range collect_clocks_clk_set[OF that(1)] unfolding collect_clks_def by blast+
  moreover have "\<forall>i\<in>set r. 0 < i \<and> i \<le> n" "\<forall>i\<in>set r. 0 < i"
    using clock_range reset_clk_set[OF that(1)] unfolding collect_clks_def by blast+
  moreover note side_conds = calculation that(2)
  note wf_intros =
    wf_dbm_abstr_repair wf_dbm_reset'_upd wf_dbm_up_canonical_upd filter_diag_wf_dbm
    wf_dbm_FW'_abstr_upd
  note check_diag_intros =
    reset'_upd_check_diag_preservation abstr_repair_check_diag_preservation
  show ?thesis unfolding E_precise_op'_def E_precise_op_def
    by simp (intro intros check_diag_intros side_conds wf_intros order.refl)
qed

lemma step_z_'_step_z_dbm'_equiv:
  "Bisimulation_Invariant
     (\<lambda> (l, D) (l', D'). \<exists> a. step_z' (conv_A A) l D l' D')
     (\<lambda> (l, D) (l', D'). \<exists> a. step_z_dbm' (conv_A A) l D v n a l' D')
     (\<lambda>(l, Z) (l', M). l = l' \<and> [M]\<^bsub>v,n\<^esub> = Z)
     (\<lambda>(l, Z). True)
     (\<lambda>(l, y). True)"
proof (standard, goal_cases)
  case prems: (1 a b a')
  obtain l Z l' Z' l1 M where unfolds[simp]: "a = (l, Z)" "b = (l', Z')" "a' = (l1, M)"
    by force+
  from prems have [simp]: "l1 = l"
    by auto
  from prems have "conv_A A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle>" "[M]\<^bsub>v,n\<^esub> = Z"
    by auto
  from this(1) guess Z1 a
    unfolding step_z'_def by safe
  note Z1 = this
  from step_z_dbm_DBM[OF Z1(1)[folded \<open>_ = Z\<close>]] guess M1 .
  note M1 = this
  from step_z_dbm_DBM[OF Z1(2)[unfolded \<open>Z1 = _\<close>]] guess Z2 .
  with M1 Z1 show ?case
    unfolding step_z_dbm'_def by auto
next
  case prems: (2 a a' b')
  obtain l M l' M' l1 Z where unfolds[simp]: "a' = (l, M)" "b' = (l', M')" "a = (l1, Z)"
    by force+
  from prems have [simp]: "l1 = l"
    by auto
  from prems obtain a1 where "conv_A A \<turnstile>' \<langle>l, M\<rangle> \<leadsto>\<^bsub>v,n,a1\<^esub> \<langle>l', M'\<rangle>" "[M]\<^bsub>v,n\<^esub> = Z"
    by auto
  from this(1) guess l1' Z1
    unfolding step_z_dbm'_def by safe
  note Z1 = this
  then have [simp]: "l1' = l"
    by (intro step_z_dbm_delay_loc)
  from Z1 \<open>_ = Z\<close> show ?case
    unfolding step_z'_def by (auto dest: step_z_dbm_sound)
next
  case (3 a b)
  then show ?case
    by auto
next
  case (4 a b)
  then show ?case
    by auto
qed

lemma step_z_dbm'_step_impl_precise_equiv:
  "Bisimulation_Invariant
     (\<lambda> (l, D) (l', D'). \<exists> a. step_z_dbm' (conv_A A) l D v n a l' D')
     (\<lambda>(l, D) (l', D'). \<exists>a. \<langle>l, D\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l', D'\<rangle>)
     (\<lambda>(l, M) (l', D). l = l' \<and> [curry (conv_M D)]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>)
     (\<lambda>(l, y). valid_dbm y)
     wf_state"
proof (standard, goal_cases)
  case prems: (1 a b a')
  obtain l M l' M' l1 D where unfolds[simp]: "a = (l, M)" "b = (l', M')" "a' = (l1, D)"
    by force+
  from prems have [simp]: "l1 = l"
    by auto
  from prems obtain a1 where
    "step_z_dbm' (conv_A A) l M v n a1 l' M'"
    by auto
  then obtain l2 M1 where steps:
    "conv_A A \<turnstile> \<langle>l,  M\<rangle>  \<leadsto>\<^bsub>v,n,\<tau>\<^esub>   \<langle>l2, M1\<rangle>"
    "conv_A A \<turnstile> \<langle>l2, M1\<rangle> \<leadsto>\<^bsub>v,n,\<upharpoonleft>a1\<^esub> \<langle>l', M'\<rangle>"
    unfolding step_z_dbm'_def by auto
  from step_z_dbm_equiv'[OF steps(1), of "curry (conv_M D)"] prems(2-) obtain M2 where
    "conv_A A \<turnstile> \<langle>l, curry (conv_M D)\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l2, M2\<rangle>" "wf_dbm D" "[M1]\<^bsub>v,n\<^esub> = [M2]\<^bsub>v,n\<^esub>"
    by (auto simp: wf_state_def)
  with step_impl_complete''_improved[OF this(1)] obtain D2 where D2:
    "A \<turnstile>\<^sub>I \<langle>l, D\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l2, D2\<rangle>" "[curry (conv_M D2)]\<^bsub>v,n\<^esub> = [M1]\<^bsub>v,n\<^esub>"
    by auto
  from step_impl_wf_dbm[OF D2(1) \<open>wf_dbm D\<close>] have "wf_dbm D2" .
  from step_z_dbm_equiv'[OF steps(2) sym[OF D2(2)]] obtain D3 where D3:
    "conv_A A \<turnstile> \<langle>l2, curry (conv_M D2)\<rangle> \<leadsto>\<^bsub>v,n,\<upharpoonleft>a1\<^esub> \<langle>l', D3\<rangle>" "[M']\<^bsub>v,n\<^esub> = [D3]\<^bsub>v,n\<^esub>"
    by (elim conjE exE)
  from step_impl_complete''_improved[OF D3(1) \<open>wf_dbm D2\<close>] obtain D4 where D4:
    "A \<turnstile>\<^sub>I \<langle>l2, D2\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a1\<^esub> \<langle>l', D4\<rangle>" "[curry (conv_M D4)]\<^bsub>v,n\<^esub> = [D3]\<^bsub>v,n\<^esub>"
    by auto
  with D2(1) have "\<langle>l, D\<rangle> \<leadsto>\<^bsub>a1\<^esub> \<langle>l', D4\<rangle>"
    by auto
  with D4(2) D3 show ?case
    by force
next
  case prems: (2 a a' b')
  obtain l M l' D' l1 D where unfolds[simp]: "a = (l, M)" "b' = (l', D')" "a' = (l1, D)"
    by force+
  from prems have [simp]: "l1 = l"
    by auto
  from prems obtain a1 where "\<langle>l, D\<rangle> \<leadsto>\<^bsub>a1\<^esub> \<langle>l', D'\<rangle>"
    by auto
  then obtain D1 where steps:
    "A \<turnstile>\<^sub>I \<langle>l, D\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l, D1\<rangle>" "A \<turnstile>\<^sub>I \<langle>l, D1\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a1\<^esub> \<langle>l', D'\<rangle>"
    by (auto dest: step_impl_delay_loc_eq)
  from prems have "wf_dbm D"
    by (auto simp: wf_state_def)
  with steps have "wf_dbm D1"
    by (blast intro: step_impl_wf_dbm)
  from step_impl_sound'[OF steps(1)] \<open>wf_dbm D\<close> obtain M2 where M2:
    "conv_A A \<turnstile> \<langle>l, curry (conv_M D)\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l, M2\<rangle>"
    "[curry (conv_M D1)]\<^bsub>v,n\<^esub> = [M2]\<^bsub>v,n\<^esub>"
    using wf_dbm_D by auto
  from step_impl_sound'[OF steps(2)] \<open>wf_dbm D1\<close> obtain M3 where M3:
    "step_z_dbm (conv_A A) l (curry (conv_M D1)) v n \<upharpoonleft>a1 l' M3"
    "[curry (conv_M D')]\<^bsub>v,n\<^esub> = [M3]\<^bsub>v,n\<^esub>"
    using wf_dbm_D by auto
  from step_z_dbm_equiv'[OF M2(1), of M] prems(2) obtain M2' where M2':
    "conv_A A \<turnstile> \<langle>l, M\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l, M2'\<rangle>" "[M2]\<^bsub>v,n\<^esub> = [M2']\<^bsub>v,n\<^esub>"
    by auto
  from step_z_dbm_equiv'[OF M3(1), of M2'] M2(2) M2'(2) obtain M3' where
    "conv_A A \<turnstile> \<langle>l, M2'\<rangle> \<leadsto>\<^bsub>v,n,\<upharpoonleft>a1\<^esub> \<langle>l', M3'\<rangle>" "[M3]\<^bsub>v,n\<^esub> = [M3']\<^bsub>v,n\<^esub>"
    by auto
  with M2'(1) M3(2) show ?case
    unfolding step_z_dbm'_def by auto
next
  case (3 a b)
  then show ?case
    unfolding step_z_dbm'_def using step_z_norm_valid_dbm'_spec step_z_valid_dbm' by auto
next
  case (4 a b)
  then show ?case
    by (clarsimp simp: norm_step_wf_dbm step_impl_wf_dbm wf_state_def)
qed

lemma E_precise_op'_wf:
  assumes "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" "wf_dbm M"
    shows "wf_dbm (E_precise_op' l r g l' M)"
proof -
  have "\<forall>c\<in>constraint_clk ` set (inv_of A l). 0 < c \<and> c \<le> n"
    using clock_range collect_clks_inv_clk_set[of A l] unfolding collect_clks_def by blast
  moreover have "\<forall>c\<in>constraint_clk ` set (inv_of A l'). 0 < c \<and> c \<le> n"
    using clock_range collect_clks_inv_clk_set[of A l'] unfolding collect_clks_def by blast
  moreover have "\<forall>c\<in>constraint_clk ` set g. 0 < c \<and> c \<le> n"
    using clock_range collect_clocks_clk_set[OF assms(1)] unfolding collect_clks_def by blast
  moreover have "\<forall>i\<in>set r. 0 < i \<and> i \<le> n"
    using clock_range reset_clk_set[OF assms(1)] unfolding collect_clks_def by blast
  moreover note side_conds = calculation assms(2)
  note wf_intros =
    wf_dbm_abstr_repair wf_dbm_reset'_upd wf_dbm_up_canonical_upd filter_diag_wf_dbm
  show ?thesis
    unfolding E_precise_op'_def by simp (intro wf_intros side_conds order.refl)
qed

sublocale E_precise_op': E_Precise_Bisim _ _ _ _ _ E_precise_op'
  by standard (rule E_precise_op'_bisim E_precise_op'_wf; assumption)+

lemma step_z_dbm'_final_bisim:
  "Bisimulation_Invariant
     (\<lambda> (l, D) (l', D'). \<exists> a. step_z_dbm' (conv_A A) l D v n a l' D')
     E_precise_op'.E_from_op
     (\<lambda> (l, M) (l', D'). l' = l \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>)
     (\<lambda>(l, y). valid_dbm y) wf_state"
  by (rule Bisimulation_Invariant_sim_replace,
      rule Bisimulation_Invariant_composition[
        OF step_z_dbm'_step_impl_precise_equiv[folded E_precise_def] E_precise_op'.E_from_op_bisim
      ]) (auto simp add: state_equiv_def dbm_equiv_def)

end (* Reachability Problem *)

context E_Precise_Bisim
begin

theorem step_z_dbm'_mono:
  assumes "conv_A A \<turnstile>' \<langle>l, M\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', M'\<rangle>" and "[M]\<^bsub>v,n\<^esub> \<subseteq> [D]\<^bsub>v,n\<^esub>"
  shows "\<exists>D'. conv_A A \<turnstile>' \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', D'\<rangle> \<and> [M']\<^bsub>v,n\<^esub> \<subseteq> [D']\<^bsub>v,n\<^esub>"
  using assms unfolding step_z_dbm'_def
  apply clarsimp
  apply (drule step_z_dbm_mono, assumption)
  apply safe
  apply (drule step_z_dbm_mono, assumption)
  apply auto
  done

interpretation
  Bisimulation_Invariant
  "(\<lambda> (l, D) (l', D'). \<exists> a. step_z_dbm' (conv_A A) l D v n a l' D')"
  E_from_op
  "\<lambda> (l, M) (l', D'). l' = l \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>"
  "\<lambda>(l, y). valid_dbm y"
  wf_state
  by (rule Bisimulation_Invariant_sim_replace,
      rule Bisimulation_Invariant_composition[
        OF step_z_dbm'_step_impl_precise_equiv[folded E_precise_def] E_from_op_bisim
      ]) (auto simp add: state_equiv_def dbm_equiv_def)

lemmas step_z_dbm'_E_from_op_bisim = Bisimulation_Invariant_axioms

lemma E_from_op_mono:
  assumes "E_from_op (l,D) (l',D')"
    and   "wf_dbm D" "wf_dbm M"
    and "[curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M)]\<^bsub>v,n\<^esub>"
  shows "\<exists> M'. E_from_op (l,M) (l',M') \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M')]\<^bsub>v,n\<^esub>"
proof -
  from B_A_step[OF assms(1), of "(l, curry (conv_M D))"] assms(2) obtain a D1 where D1:
    "conv_A A \<turnstile>' \<langle>l, curry (conv_M D)\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', D1\<rangle>" "[D1]\<^bsub>v,n\<^esub> = [curry (conv_M D')]\<^bsub>v,n\<^esub>"
    unfolding wf_state_def by (force dest: wf_dbm_D)
  from step_z_dbm'_mono[OF this(1) assms(4)] guess M1
    by safe
  note M1 = this
  with A_B_step[of "(l, curry (conv_M M))" "(l', M1)" "(l, M)"] assms(3) obtain M2 where
    "E_from_op (l, M) (l', M2)" "[curry (conv_M M2)]\<^bsub>v,n\<^esub> = [M1]\<^bsub>v,n\<^esub>"
    unfolding wf_state_def by (force dest: wf_dbm_D)
  with assms(3) M1(2) D1(2) show ?thesis
    by auto
qed

(* XXX Duplication (E_mono') *)
lemma E_from_op_mono':
  assumes "E_from_op (l,D) (l',D')"
    and   "wf_dbm D" "wf_dbm M"
    and "dbm_subset n D M"
  shows "\<exists> M'. E_from_op (l,M) (l',M') \<and> dbm_subset n D' M'"
  using assms
  apply -
  apply (frule E_from_op_mono[where M = M], assumption+)
   apply (subst dbm_subset_correct'', assumption+)
   apply (rule dbm_subset_conv, assumption)
  apply safe
  apply (subst (asm) dbm_subset_correct'')
  subgoal
    using B_invariant[unfolded wf_state_def] by auto
  subgoal
    using B_invariant[unfolded wf_state_def] by auto
  apply (blast intro: dbm_subset_conv_rev)
  done

end

end
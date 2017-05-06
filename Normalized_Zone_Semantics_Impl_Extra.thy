theory Normalized_Zone_Semantics_Impl_Extra
  imports Normalized_Zone_Semantics_Impl
begin

context Reachability_Problem
begin

lemma step_impl_sound'':
  assumes step: "A \<turnstile>\<^sub>I \<langle>l,D\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l',D'\<rangle>"
    and     reachable: "E\<^sup>*\<^sup>* a\<^sub>0 (l, D)"
  shows
    "\<exists> M'. step_z_norm' (conv_A A) l (curry (conv_M D)) a l' M'
    \<and> [curry (conv_M (FW' (norm_upd D' (k' l') n) n))]\<^bsub>v,n\<^esub> = [M']\<^bsub>v,n\<^esub>"
  apply -
  apply (rule step_impl_norm_sound[OF step])
  using canonical_reachable reachable apply (simp only: check_diag_def neutral; blast)
  using valid_dbm_reachable reachable diag_reachable' by auto

lemma reachable_sound:
  assumes "E\<^sup>*\<^sup>* a\<^sub>0 (l', D')"
  shows
    "\<exists> M'. steps_z_norm' (conv_A A) l\<^sub>0 (curry init_dbm) l' M' \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> = [M']\<^bsub>v,n\<^esub>"
  using assms unfolding E_closure
proof (induction l \<equiv> "l\<^sub>0" Z \<equiv> "init_dbm :: int DBM'" _ _ _ _ rule: steps_impl_induct)
  case refl
  show ?case
    apply (rule exI[where x = "curry init_dbm"])
    apply standard
     apply blast
    using RI_zone_equiv[symmetric] RI_init_dbm by fastforce
next
  case (step l' M' l'' M'' a l''' M''')
  from step have reachable: "E\<^sup>*\<^sup>* a\<^sub>0 (l', M')" unfolding E_closure by auto
  note valid = valid_dbm_reachable[OF reachable]
  from step.hyps(2) obtain D' where D':
    "steps_z_norm' (conv_A A) l\<^sub>0 (curry init_dbm) l' D'" "[curry (conv_M M')]\<^bsub>v,n\<^esub> = [D']\<^bsub>v,n\<^esub>"
    by auto
  from step_impl_sound'[OF step(3)] canonical_reachable diag_reachable' valid reachable
  obtain D'' where D'':
    "(conv_A A) \<turnstile> \<langle>l', curry (conv_M M')\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l'', D''\<rangle>" "[curry (conv_M M'')]\<^bsub>v,n\<^esub> = [D'']\<^bsub>v,n\<^esub>"
    unfolding check_diag_def neutral by auto
  from valid diag_reachable' canonical_reachable reachable have valid_M'':
    "valid_dbm (curry (conv_M M''))"
    apply -
    apply (rule step_impl_valid_dbm)
       apply (rule step(3))
      apply assumption+
    by auto
  with canonical_reachable diag_reachable' valid reachable
  obtain D''' where D''':
    "step_z_norm' (conv_A A) l'' (curry (conv_M M'')) (\<upharpoonleft>a) l''' D'''"
    "[curry (conv_M (FW' (norm_upd M''' (k' l''') n) n))]\<^bsub>v,n\<^esub> = [D''']\<^bsub>v,n\<^esub>"
    apply atomize_elim
    apply -
    apply (rule step_impl_norm_sound[OF step(4)])
      (* XXX *)
      (* s/h *)
      apply (metis Reachability_Problem.diag_reachable Reachability_Problem.step_impl_canonical Reachability_Problem_axioms check_diag_def neutral step.hyps(3))
     apply (metis (no_types, lifting) DBMEntry.map(1) Reachability_Problem.step_impl_diag_preservation Reachability_Problem_axioms comp_def conv_dbm_entry_mono curry_def diag_reachable neutral of_int_simps(1) step.hyps(3))
    by assumption
  from step_z_dbm_equiv'[OF D''(1) D'(2)] obtain M2 where M2:
    "conv_A A \<turnstile> \<langle>l', D'\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l'', M2\<rangle>" "[D'']\<^bsub>v,n\<^esub> = [M2]\<^bsub>v,n\<^esub>"
    by blast
  have "valid_dbm D'" using D'(1) steps_z_norm'_valid_dbm_preservation by blast
  then have valid_M2: "valid_dbm M2" by (rule step_z_valid_dbm'[OF M2(1)])
  from M2 D''(2) have "[curry (conv_M M'')]\<^bsub>v,n\<^esub> = [M2]\<^bsub>v,n\<^esub>" by simp
  from step_z_norm_equiv'[OF D'''(1) valid_M'' valid_M2 this] obtain M3 where
    "step_z_norm' (conv_A A) l'' M2 (\<upharpoonleft>a) l''' M3" "[D''']\<^bsub>v,n\<^esub> = [M3]\<^bsub>v,n\<^esub>"
    by blast
  with M2(1) D'(1) D'''(2) show ?case by auto
qed

lemma step_impl_complete2:
  assumes step: "conv_A A \<turnstile> \<langle>l, curry (conv_M M)\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', D\<rangle>"
    and wf_dbm: "wf_dbm M"
  shows "\<exists> M'. A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l', M'\<rangle> \<and> [curry (conv_M M')]\<^bsub>v,n\<^esub> \<supseteq> [D]\<^bsub>v,n\<^esub>"
  using assms(1) wf_dbm_D[OF assms(2)] by (intro step_impl_complete'')

lemma reachable_complete:
  assumes "steps_z_norm' (conv_A A) l\<^sub>0 (curry init_dbm) l' M'"
  shows
    "\<exists> D'. E\<^sup>*\<^sup>* a\<^sub>0 (l', D') \<and> [M']\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M D')]\<^bsub>v,n\<^esub>"
  using assms unfolding E_closure
proof (induction "conv_A A" x2 \<equiv> l\<^sub>0 "curry init_dbm :: real DBM" l' M' rule: steps_z_norm_induct)
  case refl
  show ?case by (auto intro: steps_impl.refl)
next
  case (step a l' M' l'' M'' l''' M''')
  then obtain D' where D':
    "A \<turnstile>\<^sub>I \<langle>l\<^sub>0, init_dbm\<rangle> \<leadsto>\<^bsub>k',n\<^esub>* \<langle>l', D'\<rangle>" "[M']\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M D')]\<^bsub>v,n\<^esub>"
    by auto
  from step_z_dbm_mono[OF step(3) D'(2)] obtain D'' where D'':
    "conv_A A \<turnstile> \<langle>l', curry (conv_M D')\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l'', D''\<rangle>"
    "[M'']\<^bsub>v,n\<^esub> \<subseteq> [D'']\<^bsub>v,n\<^esub>"
    by auto
  from step have reachable: "E\<^sup>*\<^sup>* a\<^sub>0 (l', D')" using D'(1) E_closure by blast (* s/h *)
  from step_impl_complete2[OF D''(1) reachable_wf_dbm[OF this]] step obtain D2 where D2:
    "A \<turnstile>\<^sub>I \<langle>l', D'\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l'', D2\<rangle>" "[D'']\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M D2)]\<^bsub>v,n\<^esub>"
    by auto
  have "valid_dbm M''" (* s/h *)
    using step(1,3) step_z_valid_dbm' steps_z_norm'_valid_dbm_preservation valid_init_dbm by blast
  have valid3:"valid_dbm (curry (conv_M D2))"
    apply (rule step_impl_valid_dbm[OF D2(1)])
    using valid_dbm_reachable canonical_reachable reachable
    using diag_reachable[OF reachable] diag_conv by (auto intro!: canonical_reachable)
  from step_z_norm_mono'[OF step(4) \<open>valid_dbm M''\<close> valid3] D''(2) D2(2) obtain M3 where M3:
    "step_z_norm' (conv_A A) l'' (curry (conv_M D2)) \<upharpoonleft>a l''' M3" "[M''']\<^bsub>v,n\<^esub> \<subseteq> [M3]\<^bsub>v,n\<^esub>"
    by auto
  have canonical: "canonical (curry (conv_M D2)) n \<or> check_diag n D2"
    using step_impl_canonical[OF D2(1) diag_reachable[OF reachable]]
    unfolding check_diag_def neutral by auto
  have diag: "\<forall>i\<le>n. conv_M D2 (i, i) \<le> 0"
    using step_impl_diag_preservation[OF D2(1) diag_reachable[OF reachable]] diag_conv by auto
  from step_impl_norm_complete''[OF M3(1) valid3 canonical diag] obtain D3 where
    "A \<turnstile>\<^sub>I \<langle>l'', D2\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a\<^esub> \<langle>l''', D3\<rangle> "
    "[M3]\<^bsub>v,n\<^esub> \<subseteq> [curry ((map_DBMEntry real_of_int \<circ>\<circ>\<circ> FW') (norm_upd D3 (k' l''') n) n)]\<^bsub>v,n\<^esub>"
    by auto
  with D'(1) D2 M3(2) show ?case by (auto intro: steps_impl.step)
qed


lemma step_impl_mono_reachable:
    assumes "A \<turnstile>\<^sub>I \<langle>l,D\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l',D'\<rangle>"
    and     "wf_dbm D" "wf_dbm M"
    and "[curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M)]\<^bsub>v,n\<^esub>"
  shows "\<exists> M'. A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l', M'\<rangle> \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M')]\<^bsub>v,n\<^esub>"
  proof -
    note prems_D = wf_dbm_D[OF assms(2)]
    note prems_M = wf_dbm_D[OF assms(3)]
    from step_impl_sound'[OF assms(1) prems_D] diag_conv obtain M' where
      "conv_A A \<turnstile> \<langle>l, curry (conv_M D)\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', M'\<rangle>"
      "[curry (conv_M D')]\<^bsub>v,n\<^esub> = [M']\<^bsub>v,n\<^esub>"
      unfolding check_diag_def neutral by auto
    with step_impl_complete2[OF _ assms(3)] step_z_dbm_mono[OF _ assms(4)] show ?thesis by force
  qed

lemma step_impl_norm_mono_reachable:
    assumes "A \<turnstile>\<^sub>I \<langle>l,D\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l',D'\<rangle>"
        and prems_D: "wf_dbm D"
        and prems_M: "wf_dbm M"
    and subs: "[curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M)]\<^bsub>v,n\<^esub>"
    shows
      "\<exists> M'. A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l', M'\<rangle>
      \<and> [curry (conv_M (FW' (norm_upd D' (k' l') n) n))]\<^bsub>v,n\<^esub>
      \<subseteq> [curry ((map_DBMEntry real_of_int \<circ>\<circ>\<circ> FW') (norm_upd M' (k' l') n) n)]\<^bsub>v,n\<^esub>"
  proof -
    note prems_D = wf_dbm_D[OF prems_D]
    note prems_M = wf_dbm_D[OF prems_M]
    from step_impl_norm_sound[OF assms(1) prems_D] obtain M' where M':
      "step_z_norm'
        (conv_A A)
        l (curry (conv_M D)) a l' M'"
       "[curry ((map_DBMEntry real_of_int \<circ>\<circ>\<circ> FW') (norm_upd D' (k' l') n) n)]\<^bsub>v,n\<^esub> = [M']\<^bsub>v,n\<^esub>"
      by auto
    from
      step_z_norm_mono'[OF this(1) prems_D(3) prems_M(3) subs]
      step_impl_norm_complete''[OF _ prems_M(3,1,2)] M'(2)
    show ?thesis by fast
  qed


lemma step_impl_mono_reachable':
    assumes step:
      "A \<turnstile>\<^sub>I \<langle>l, D\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l', D'\<rangle>"
      "A \<turnstile>\<^sub>I \<langle>l', D'\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a\<^esub> \<langle>l'', D''\<rangle>"
      "D''' = FW' (norm_upd D'' (k' l'') n) n"
    and wf_dbm: "wf_dbm D" "wf_dbm M"
    and subset: "dbm_subset n D M"
    shows
      "\<exists> M' M'' M'''. A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l', M'\<rangle> \<and> A \<turnstile>\<^sub>I \<langle>l', M'\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a\<^esub> \<langle>l'', M''\<rangle>
       \<and> M''' = FW' (norm_upd M'' (k' l'') n) n \<and> dbm_subset n D''' M'''"
  proof -
    from dbm_subset_correct''[OF wf_dbm] subset[THEN dbm_subset_conv] have
      "([curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M)]\<^bsub>v,n\<^esub>)"
      by simp
    from step_impl_mono_reachable[OF step(1) wf_dbm this] obtain M' where M':
      "A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l', M'\<rangle>" "[curry (conv_M D')]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M')]\<^bsub>v,n\<^esub>"
      by auto
    from step_impl_wf_dbm[OF step(1) wf_dbm(1)] step_impl_wf_dbm[OF M'(1) wf_dbm(2)] have wf_dbm':
      "wf_dbm D'" "wf_dbm M'" by auto
    from step_impl_norm_mono_reachable[OF step(2) wf_dbm' M'(2)] obtain M'' where M'':
      "A \<turnstile>\<^sub>I \<langle>l', M'\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a\<^esub> \<langle>l'', M''\<rangle>"
      "[curry (conv_M (FW' (norm_upd D'' (k' l'') n) n))]\<^bsub>v,n\<^esub>
      \<subseteq> [curry (conv_M (FW' (norm_upd M'' (k' l'') n) n))]\<^bsub>v,n\<^esub>"
      using diag_conv by auto
    from step_impl_wf_dbm[OF step(2)] step_impl_wf_dbm[OF M''(1)] wf_dbm' have
      "wf_dbm D''" "wf_dbm M''"
      by auto
    from norm_step_wf_dbm[OF this(1)] norm_step_wf_dbm[OF this(2)] have
      "wf_dbm (FW' (norm_upd D'' (k' l'') n) n)" "wf_dbm (FW' (norm_upd M'' (k' l'') n) n)"
      by auto
    from M'(1) dbm_subset_correct''[OF this] M''(2) dbm_subset_conv_rev have
      "dbm_subset n (FW' (norm_upd D'' (k' l'') n) n) (FW' (norm_upd M'' (k' l'') n) n)"
      by auto
    with M'(1) M''(1) show ?thesis unfolding \<open>D''' = _\<close> by auto
  qed

lemma step_impl_mono_reachable'':
    assumes step:
      "A \<turnstile>\<^sub>I \<langle>l, D\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l', D'\<rangle>"
      "A \<turnstile>\<^sub>I \<langle>l', D'\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a\<^esub> \<langle>l'', D''\<rangle>"
      "D''' = FW' (norm_upd D'' (k' l'') n) n"
    and wf_dbm: "wf_dbm D" "wf_dbm M"
    and subset: "[curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M)]\<^bsub>v,n\<^esub>"
    shows
      "\<exists> M' M'' M'''. A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l', M'\<rangle> \<and> A \<turnstile>\<^sub>I \<langle>l', M'\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a\<^esub> \<langle>l'', M''\<rangle>
       \<and> M''' = FW' (norm_upd M'' (k' l'') n) n
       \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M')]\<^bsub>v,n\<^esub>
       \<and> [curry (conv_M D''')]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M''')]\<^bsub>v,n\<^esub>"
  proof -
    from step_impl_mono_reachable[OF step(1) wf_dbm subset] obtain M' where M':
      "A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l', M'\<rangle>" "[curry (conv_M D')]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M')]\<^bsub>v,n\<^esub>"
      by auto
    from step_impl_wf_dbm[OF step(1) wf_dbm(1)] step_impl_wf_dbm[OF M'(1) wf_dbm(2)] have wf_dbm':
      "wf_dbm D'" "wf_dbm M'" by auto
    from step_impl_norm_mono_reachable[OF step(2) wf_dbm' M'(2)] obtain M'' where M'':
      "A \<turnstile>\<^sub>I \<langle>l', M'\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a\<^esub> \<langle>l'', M''\<rangle>"
      "[curry (conv_M (FW' (norm_upd D'' (k' l'') n) n))]\<^bsub>v,n\<^esub>
      \<subseteq> [curry (conv_M (FW' (norm_upd M'' (k' l'') n) n))]\<^bsub>v,n\<^esub>"
      using diag_conv by auto
    with M' M''(1) show ?thesis unfolding \<open>D''' = _\<close> by auto
  qed

lemma step_impl_mono_reachable__:
  assumes step:
    "A \<turnstile>\<^sub>I \<langle>l, D\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l', D'\<rangle>"
    "A \<turnstile>\<^sub>I \<langle>l', D'\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a\<^esub> \<langle>l'', D''\<rangle>"
    "D''' = FW' (norm_upd D'' (k' l'') n) n"
    and wf_dbm: "wf_dbm D" "wf_dbm M"
    and subset: "dbm_subset n D M"
  shows
    "\<exists> M' M'' M'''. A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l', M'\<rangle> \<and> A \<turnstile>\<^sub>I \<langle>l', M'\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a\<^esub> \<langle>l'', M''\<rangle>
     \<and> M''' = FW' (norm_upd M'' (k' l'') n) n \<and> dbm_subset n D''' M'''"
proof -
  from dbm_subset_correct''[OF wf_dbm] subset[THEN dbm_subset_conv] have
    "([curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M)]\<^bsub>v,n\<^esub>)"
    by simp
  from step_impl_mono_reachable[OF step(1) wf_dbm this] obtain M' where M':
    "A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l', M'\<rangle>" "[curry (conv_M D')]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M')]\<^bsub>v,n\<^esub>"
    by auto
  from step_impl_wf_dbm[OF step(1) wf_dbm(1)] step_impl_wf_dbm[OF M'(1) wf_dbm(2)] have wf_dbm':
    "wf_dbm D'" "wf_dbm M'" by auto
  from step_impl_norm_mono_reachable[OF step(2) wf_dbm' M'(2)] obtain M'' where M'':
    "A \<turnstile>\<^sub>I \<langle>l', M'\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a\<^esub> \<langle>l'', M''\<rangle>"
    "[curry (conv_M (FW' (norm_upd D'' (k' l'') n) n))]\<^bsub>v,n\<^esub>
    \<subseteq> [curry (conv_M (FW' (norm_upd M'' (k' l'') n) n))]\<^bsub>v,n\<^esub>"
    using diag_conv by auto
  from step_impl_wf_dbm[OF step(2)] step_impl_wf_dbm[OF M''(1)] wf_dbm' have
    "wf_dbm D''" "wf_dbm M''"
    by auto
  from norm_step_wf_dbm[OF this(1)] norm_step_wf_dbm[OF this(2)] have
    "wf_dbm (FW' (norm_upd D'' (k' l'') n) n)" "wf_dbm (FW' (norm_upd M'' (k' l'') n) n)"
    by auto
  from M'(1) dbm_subset_correct''[OF this] M''(2) dbm_subset_conv_rev have
    "dbm_subset n (FW' (norm_upd D'' (k' l'') n) n) (FW' (norm_upd M'' (k' l'') n) n)"
    by auto
  with M'(1) M''(1) show ?thesis unfolding \<open>D''' = _\<close> by auto
qed

end

end
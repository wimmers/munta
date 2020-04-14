theory TA_Equivalences
  imports
    TA.Timed_Automata
    TA_Impl.Normalized_Zone_Semantics_Impl_Refine
    TA_Library.Graphs
begin

locale TA_Equiv =
  fixes A B :: "('a, 'c, 't :: time, 's) ta"
  fixes S :: "'s set"
  assumes state_set_trans_of: "state_set (trans_of A) \<subseteq> S"
  assumes invs: "\<forall> l \<in> S. inv_of A l = inv_of B l"
  assumes trans_eq: "trans_of A = trans_of B"
begin

lemma delay1:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l',u'\<rangle>" if "l \<in> S" "B \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l',u'\<rangle>"
  using that invs by (auto elim!: step_t.cases)

lemma action1:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l',u'\<rangle>" if "B \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l',u'\<rangle>"
proof -
  from that have "l \<in> S" "l' \<in> S"
    using state_set_trans_of by (auto elim!: step_a.cases simp: trans_eq state_set_def)
  with that invs show ?thesis
    by (auto elim!: step_a.cases simp: trans_eq intro: step_a.intros)
qed

lemma delay2:
  "B \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l',u'\<rangle>" if "l \<in> S" "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l',u'\<rangle>"
  using that invs by (auto elim!: step_t.cases)

lemma action2:
  "B \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l',u'\<rangle>" if "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l',u'\<rangle>"
proof -
  from that have "l \<in> S" "l' \<in> S"
    using state_set_trans_of by (auto elim!: step_a.cases simp: trans_eq[symmetric] state_set_def)
  with that invs show ?thesis
    by (auto elim!: step_a.cases simp: trans_eq [symmetric] intro: step_a.intros)
qed

lemma step1:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>" if "l \<in> S" "B \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>"
  using that(2,1) by cases (auto dest: action1 delay1)

lemma step2:
  "B \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>" if "l \<in> S" "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>"
  using that(2,1) by cases (auto dest: action2 delay2)

print_locale Bisimulation_Invariant

term "step A"

lemma S_inv:
  "l' \<in> S" if "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>" "l \<in> S"
  using that state_set_trans_of
  by (auto elim!: step.cases step_a.cases step_t.cases simp: state_set_def)

interpretation interp: Bisimulation_Invariant
  "\<lambda> (l, u) (l', u'). A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>"
  "\<lambda> (l, u) (l', u'). B \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>"
  "\<lambda> lu lu'. lu' = lu" "\<lambda> (l, u). l \<in> S" "\<lambda> (l, u). l \<in> S"
  by standard (auto dest: step1 step2 intro: S_inv)



end (* TA Equiv *)

end (* Theory *)
theory Worklist_Common
  imports Worklist_Locales
begin

lemma (in Search_Space_finite) finitely_branching:
  assumes "reachable a"
  shows "finite ({a'. E a a' \<and> \<not> empty a'})"
proof -
  have "{a'. E a a' \<and> \<not> empty a'} \<subseteq> {a'. reachable a' \<and> \<not> empty a'}"
    using assms(1) by (auto intro: reachable_step)
  then show ?thesis using finite_reachable
    by (rule finite_subset)
qed

end (* Theory *)
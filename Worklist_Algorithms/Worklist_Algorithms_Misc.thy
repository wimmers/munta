theory Worklist_Algorithms_Misc
  imports "HOL-Library.Multiset"
begin

lemma mset_eq_empty_iff:
  "M = {#} \<longleftrightarrow> set_mset M = {}"
  by auto

lemma filter_mset_eq_empty_iff:
  "{#x \<in># A. P x#} = {#} \<longleftrightarrow> (\<forall>x \<in> set_mset A. \<not> P x)"
  by (auto simp: mset_eq_empty_iff)

end
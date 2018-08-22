theory TA_More2
  imports TA_Impl.TA_More
begin

lemma collect_clock_pairs_concat:
  "collect_clock_pairs (concat xxs) = (\<Union> x \<in> set xxs. collect_clock_pairs x)"
  unfolding collect_clock_pairs_def by auto

end
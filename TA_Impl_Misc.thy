theory TA_Impl_Misc
  imports Main
begin

(* XXX Move *)
subsection \<open>Invariants on folds\<close>

lemma fold_acc_preserv:
  assumes "\<And> x acc. P acc \<Longrightarrow> P (f x acc)" "P acc"
  shows "P (fold f xs acc)"
  using assms(2) by (induction xs arbitrary: acc) (auto intro: assms(1))

lemma fold_acc_ev_preserv':
  fixes x
  assumes
    "\<And> x acc. P acc \<Longrightarrow> P (f x acc)" "\<And> x acc. Q acc \<Longrightarrow> Q (f x acc)"
    "\<And> acc. Q acc \<Longrightarrow> P (f x acc)" "x \<in> set xs" "Q acc"
  shows "P (fold f xs acc) \<and> Q (fold f xs acc)"
  using assms(4,5) apply (induction xs arbitrary: acc)
  using assms(1,2,3) by (auto intro: fold_acc_preserv)

lemma fold_acc_ev_preserv:
  fixes x
  assumes
    "\<And> x acc. P acc \<Longrightarrow> Q acc \<Longrightarrow> P (f x acc)" "\<And> x acc. Q acc \<Longrightarrow> Q (f x acc)"
    "\<And> acc. Q acc \<Longrightarrow> P (f x acc)" "x \<in> set xs" "Q acc"
  shows "P (fold f xs acc) \<and> Q (fold f xs acc)"
  apply (rule fold_acc_ev_preserv'[where P = "\<lambda> acc. P acc \<and> Q acc" and Q = Q, THEN conjunct1])
  by (auto intro: assms)

lemmas fold_ev_preserv = fold_acc_ev_preserv[where Q = "\<lambda> _. True", simplified]

lemma fold_evD':
  assumes "\<not> P acc" "P (fold f xs acc)"
    shows "\<exists> x ys zs. xs = ys @ x # zs \<and> \<not> P (fold f ys acc) \<and> P (f x (fold f ys acc))"
  using assms
  apply (induction xs arbitrary: acc)
   apply (simp; fail)
  subgoal premises prems for x xs acc
    apply (cases "P (f x acc)")
     using prems(2-) apply fastforce
     apply (drule prems(1))
     using prems apply simp
     apply clarsimp
     subgoal for xa ys zs
       apply (rule exI[where x = xa])
       apply (rule exI[where x = "x # ys"])
       by fastforce
     done
   done

lemma fold_evD:
  assumes
    "P y (fold f xs acc)" "\<not> P y acc" "\<And> acc x. \<not> P y acc \<Longrightarrow> Q acc \<Longrightarrow> P y (f x acc) \<Longrightarrow> x = y"
    "Q acc" "\<And> acc x. Q acc \<Longrightarrow> Q (f x acc)" "\<And> acc x. \<not> P y acc \<Longrightarrow> Q acc \<Longrightarrow> P y (f x acc) \<Longrightarrow> R y"
  shows "\<exists> ys zs. xs = ys @ y # zs \<and> \<not> P y (fold f ys acc) \<and> P y (f y (fold f ys acc)) \<and> R y"
proof -
  from fold_evD'[OF assms(2,1)] obtain x ys zs where *:
    "xs = ys @ x # zs" "\<not> P y (fold f ys acc)" "P y (f x (fold f ys acc))"
    by auto
  moreover from assms(4-) have "Q (fold f ys acc)" by (auto intro: fold_acc_preserv)
  ultimately show ?thesis using assms(3,6) by auto
qed

lemmas fold_evD'' = fold_evD[where R = "\<lambda> _. True", simplified]

end
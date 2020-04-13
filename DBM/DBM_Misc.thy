theory DBM_Misc
  imports Main HOL.Real
begin

lemma finite_set_of_finite_funs2:
  fixes A :: "'a set" 
    and B :: "'b set"
    and C :: "'c set"
    and d :: "'c" 
  assumes "finite A"
    and "finite B"
    and "finite C"
  shows "finite {f. \<forall>x. \<forall>y. (x \<in> A \<and> y \<in> B \<longrightarrow> f x y \<in> C) \<and> (x \<notin> A \<longrightarrow> f x y = d) \<and> (y \<notin> B \<longrightarrow> f x y = d)}"
proof -
  let ?S = "{f. \<forall>x. \<forall>y. (x \<in> A \<and> y \<in> B \<longrightarrow> f x y \<in> C) \<and> (x \<notin> A \<longrightarrow> f x y = d) \<and> (y \<notin> B \<longrightarrow> f x y = d)}"
  let ?R = "{g. \<forall>x. (x \<in> B \<longrightarrow> g x \<in> C) \<and> (x \<notin> B \<longrightarrow> g x = d)}"
  let ?Q = "{f. \<forall>x. (x \<in> A \<longrightarrow> f x \<in> ?R) \<and> (x \<notin> A \<longrightarrow> f x = (\<lambda>y. d))}"
  from finite_set_of_finite_funs[OF assms(2,3)] have "finite ?R" .
  from finite_set_of_finite_funs[OF assms(1) this, of "\<lambda> y. d"] have "finite ?Q" .
  moreover have "?S = ?Q" by auto (case_tac "xa \<in> A", auto)
  ultimately show ?thesis by simp
qed

end
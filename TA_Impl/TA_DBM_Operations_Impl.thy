theory TA_DBM_Operations_Impl
  imports
    TA.TA_DBM_Operations
    DBM.DBM_Operations_Impl_Refine
    Sepref_Acconstraint
    TA_Library.TA_Syntax_Bundles
begin

unbundle no_library_syntax

section \<open>Constraints\<close>

(*
fun abstra' :: "(nat, 't::time) acconstraint \<Rightarrow> 't DBM \<Rightarrow> 't DBM"
where
  "abstra' (EQ c d) M =
    (\<lambda> i j . if i = 0 \<and> j = c then min (M i j) (Le (-d)) else if i = c \<and> j = 0 then min (M i j) (Le d) else M i j)" |
  "abstra' (LT c d) M =
    (\<lambda> i j . if i = c \<and> j = 0 then min (M i j) (Lt d) else M i j)" |
  "abstra' (LE c d) M =
    (\<lambda> i j . if i = c \<and> j = 0 then min (M i j) (Le d) else M i j)" |
  "abstra' (GT c d) M =
    (\<lambda> i j. if i = 0 \<and> j = c then min (M i j) (Lt (- d)) else M i j)" |
  "abstra' (GE c d) M =
    (\<lambda> i j. if i = 0 \<and> j = c then min (M i j) (Le (- d)) else M i j)"
*)

definition "abstra' ac M = abstra ac M id"

lemma abstra_abstra':
  assumes "v (constraint_clk ac) = constraint_clk ac"
  shows "abstra ac M v = abstra' ac M"
unfolding abstra'_def using assms by (cases ac; fastforce)

definition "abstr' cc M = abstr cc M id"

lemma abstr_abstr':
  assumes "\<forall> c \<in> collect_clks cc. v c = c"
  shows "abstr cc M v = abstr' cc M"
unfolding abstr'_def using assms
by (auto simp: collect_clks_def intro: fold_cong abstra_abstra'[unfolded abstra'_def])

(* XXX Move? *)
lemma And_abstr:
  assumes "clock_numbering' v n" "\<forall> c \<in> collect_clks cc. v c \<le> n"
  shows "[And M (abstr cc (\<lambda> i j. \<infinity>) v)]\<^bsub>v,n\<^esub> = [abstr cc M v]\<^bsub>v,n\<^esub>"
using And_correct dbm_abstr_zone_eq[OF assms] dbm_abstr_zone_eq2[OF assms] by blast

(* XXX Move *)
lemma min_inf_r:
  "min a \<infinity> = a"
  by (cases a) (auto split: split_min simp: less_eq dbm_le_def)

lemma min_inf_l:
  "min \<infinity> b = b"
  by (cases b) (auto split: split_min simp: less_eq dbm_le_def)

lemma And_abstra_commute:
  assumes "clock_numbering' v n" "\<forall> c \<in> collect_clks cc. v c \<le> n"
  shows "And M (abstra ac (\<lambda> i j. \<infinity>) v) = abstra ac M v"
  by (cases ac) (auto simp: min_inf_l min_inf_r any_le_inf intro!: ext)

(* Could be proven by using the facts that abstra commutes with itself and And*)
lemma
  assumes "clock_numbering' v n" "\<forall> c \<in> collect_clks cc. v c \<le> n"
  shows "And M (abstr cc (\<lambda> i j. \<infinity>) v) = abstr cc M v"
apply (induction cc)
apply simp
apply (simp add: min_inf_r)
oops

lemma abstra_canonical_diag_preservation:
  assumes "clock_numbering v"
  shows "(abstra ac M v) i i = M i i"
using assms by (cases ac) (auto dest: clock_numberingD)

lemma abstr_canonical_diag_preservation:
  assumes "clock_numbering v"
  shows "(abstr cc M v) i i = M i i"
using assms
apply (induction cc arbitrary: M)
apply (simp; fail)
 subgoal for ac cc M
 using abstra_canonical_diag_preservation[where v = v and ac = ac] by auto
done

fun abstra_upd :: "(nat, 't::{linorder,uminus}) acconstraint \<Rightarrow> 't DBM' \<Rightarrow> 't DBM'"
where
  "abstra_upd (EQ c d) M =
    (let
      m0c = op_mtx_get M (0, c);
      mc0 = op_mtx_get M(c, 0)
     in M((0, c) := min m0c (Le (-d)), (c, 0) := min mc0 (Le d)))" |
  "abstra_upd (LT c d) M =
    M((c, 0) := min (op_mtx_get M (c, 0)) (Lt d))" |
  "abstra_upd (LE c d) M =
    M((c, 0) := min (op_mtx_get M (c, 0)) (Le d))" |
  "abstra_upd (GT c d) M =
    M((0, c) := min (op_mtx_get M ((0, c))) (Lt (- d)))" |
  "abstra_upd (GE c d) M =
    M((0, c) := min (op_mtx_get M (0, c)) (Le (- d)))"

lemma abstra_upd_alt_def:
  "abstra_upd ac M = case_acconstraint
    (\<lambda> c d. M((c, 0) := min (op_mtx_get M (c, 0)) (Lt d)))
    (\<lambda> c d. M((c, 0) := min (op_mtx_get M (c, 0)) (Le d)))
    (\<lambda> c d. let m0c = op_mtx_get M (0, c); mc0 = op_mtx_get M(c, 0) in M((0, c) := min m0c (Le (-d)), (c, 0) := min mc0 (Le d)))
    (\<lambda> c d. M((0, c) := min (op_mtx_get M ((0, c))) (Lt (- d))))
    (\<lambda> c d. M((0, c) := min (op_mtx_get M (0, c)) (Le (- d))))
    ac"
by (cases ac) auto

lemma abstra_upd_eq_abstra':
  assumes "constraint_clk ac > 0"
  shows "curry (abstra_upd ac M) = abstra' ac (curry M)"
unfolding abstra'_def using assms by (cases ac; fastforce)

lemma abstra_upd_int_preservation:
  assumes "snd (constraint_pair ac) \<in> \<int>" "dbm_int (curry M) n"
  shows "dbm_int (curry (abstra_upd ac M)) n"
using assms by (cases ac; simp split: split_min)

definition abstr_upd where
  "abstr_upd = fold (\<lambda> ac M. abstra_upd ac M)"

lemma abstr_upd_alt_def:
  "RETURN oo abstr_upd = (\<lambda> cc M. nfoldli cc (\<lambda> _. True) (\<lambda> ac M. RETURN (abstra_upd ac M)) M)"
by (intro ext, simp add: abstr_upd_def fold_eq_nfoldli)


lemma abstr_upd_abstr':
  assumes "\<forall> c \<in> collect_clks cc. c > 0"
  shows "curry (abstr_upd cc M) = abstr' cc (curry M)"
unfolding abstr_upd_def abstr'_def using assms
by (induction cc arbitrary: M) (auto simp: abstra_abstra' abstra_upd_eq_abstra')

lemma abstra_upd_out_of_bounds1:
  assumes "constraint_clk ac \<le> n" "i > n"
  shows "(abstra_upd ac M) (i, j) = M (i, j)"
using assms by (cases ac) auto

lemma abstra_upd_out_of_bounds2:
  assumes "constraint_clk ac \<le> n" "j > n"
  shows "(abstra_upd ac M) (i, j) = M (i, j)"
using assms by (cases ac) auto

lemma abstr_upd_out_of_bounds1:
  assumes "\<forall> c \<in> collect_clks cc. c \<le> n" "i > n"
  shows "(abstr_upd cc M) (i, j) = M (i, j)"
using assms by (induction cc arbitrary: M) (auto simp: abstr_upd_def abstra_upd_out_of_bounds1)

lemma abstr_upd_out_of_bounds2:
  assumes "\<forall> c \<in> collect_clks cc. c \<le> n" "j > n"
  shows "(abstr_upd cc M) (i, j) = M (i, j)"
using assms by (induction cc arbitrary: M) (auto simp: abstr_upd_def abstra_upd_out_of_bounds2)

lemma abstr_upd_int_preservation:
  assumes "\<forall> (_,d) \<in> collect_clock_pairs cc. d \<in> \<int>" "dbm_int (curry M) n"
  shows "dbm_int (curry (abstr_upd cc M)) n"
unfolding abstr_upd_def using assms
proof (induction cc arbitrary: M)
  case Nil then show ?case by simp
next
  case (Cons c cc)
  show ?case
   apply simp
   apply (rule Cons.IH[simplified])
   defer
   apply (rule abstra_upd_int_preservation[simplified])
  using Cons.prems unfolding collect_clock_pairs_def by auto
qed

(*
fun abstra_upd :: "('c, 't::time) acconstraint \<Rightarrow> 't DBM' \<Rightarrow> ('c \<Rightarrow> nat) \<Rightarrow> 't DBM'"
where
  "abstra_upd (EQ c d) M v =
    (let m0c = op_mtx_get M (0, v c); mc0 = op_mtx_get M(v c, 0) in M((0, v c) := min m0c (Le (-d)), (v c, 0) := min mc0 (Le d)))" |
  "abstra_upd (LT c d) M v =
    M((v c, 0) := min (op_mtx_get M (v c, 0)) (Lt d))" |
  "abstra_upd (LE c d) M v =
    M((v c, 0) := min (op_mtx_get M (v c, 0)) (Le d))" |
  "abstra_upd (GT c d) M v =
    M((0, v c) := min (op_mtx_get M ((0, v c))) (Lt (- d)))" |
  "abstra_upd (GE c d) M v =
    M((0, v c) := min (op_mtx_get M (0, v c)) (Le (- d)))"

lemma abstra_upd_eq_abstra:
  assumes "clock_numbering v"
  shows "curry (abstra_upd ac M v) = abstra ac (curry M) v"
using assms by (cases ac; fastforce dest: clock_numberingD)
*)

context
  fixes n :: nat
begin

interpretation DBM_Impl n .

sepref_definition abstra_upd_impl is
  "uncurry (RETURN oo abstra_upd)" ::
  "(acconstraint_assn clock_assn id_assn)\<^sup>k *\<^sub>a mtx_assn\<^sup>d \<rightarrow>\<^sub>a mtx_assn"
unfolding abstra_upd_alt_def zero_clock_def[symmetric] by sepref

sepref_register abstra_upd ::
  "(nat, ('a :: {linordered_cancel_ab_monoid_add,uminus,heap})) acconstraint
  \<Rightarrow> 'a DBMEntry i_mtx \<Rightarrow> 'a DBMEntry i_mtx"

lemmas [sepref_fr_rules] = abstra_upd_impl.refine

sepref_definition abstr_upd_impl is
  "uncurry (RETURN oo abstr_upd)"
  :: "(list_assn (acconstraint_assn clock_assn id_assn))\<^sup>k *\<^sub>a mtx_assn\<^sup>d \<rightarrow>\<^sub>a mtx_assn"
  unfolding abstr_upd_alt_def by sepref

end

export_code abstr_upd_impl abstra_upd_impl in SML_imp

end
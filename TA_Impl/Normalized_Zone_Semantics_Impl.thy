theory Normalized_Zone_Semantics_Impl
  imports
    TA.Normalized_Zone_Semantics
    Worklist_Algorithms.Worklist_Locales
    TA_DBM_Operations_Impl
    DBM.FW_Code
    TA.TA_More
    TA_Library.Syntax_Bundles
begin

unbundle no_library_syntax

chapter \<open>Implementation of Reachability Checking\<close>

hide_const D

no_notation Extended_Nat.infinity_class.infinity ("\<infinity>")

definition default_ceiling where
  "default_ceiling A = (
    let M = (\<lambda> c. {m . (c, m) \<in> Timed_Automata.clkp_set A}) in
      (\<lambda> x. if M x = {} then 0 else nat (Max (M x))))"

section \<open>Potential Graveyard\<close>

(* XXX *)
definition default_ceiling_real where
  "default_ceiling_real A = (
    let M = (\<lambda> c. {m . (c, m) \<in> Timed_Automata.clkp_set A}) in
      (\<lambda> x. if M x = {} then 0 else nat (floor (Max (M x)) + 1)))"

(* This is for automata carrying real time annotations *)
(* XXX Unused *)
lemma standard_abstraction_real:
  assumes
    "finite (Timed_Automata.clkp_set A)" "finite (Timed_Automata.collect_clkvt (trans_of A))"
    "\<forall>(_,m::real) \<in> Timed_Automata.clkp_set A. m \<in> \<nat>"
  shows "Timed_Automata.valid_abstraction A (clk_set A) (default_ceiling_real A)"
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
  then show ?thesis unfolding default_ceiling_real_def by auto
qed

(* XXX Unused *)
(* This is for automata carrying int time annotations *)
lemma standard_abstraction_int:
  assumes
    "finite (Timed_Automata.clkp_set A)" "finite (Timed_Automata.collect_clkvt (trans_of A))"
    "\<forall>(_,m::int) \<in> Timed_Automata.clkp_set A. m \<in> \<nat>"
  and "clk_set A \<subseteq> X" "finite X"
  shows "Timed_Automata.valid_abstraction A X (default_ceiling A)"
proof -
  from \<open>_ \<subseteq> X\<close> have 2: "Timed_Automata.collect_clkvt (trans_of A) \<subseteq> X" by auto
  from assms obtain L where L: "distinct L" "set L = Timed_Automata.clkp_set A"
    by (meson finite_distinct_list)
  let ?M = "\<lambda> c. {m . (c, m) \<in> Timed_Automata.clkp_set A}"
  let ?X = "clk_set A"
  let ?m = "map_of L"
  let ?k = "\<lambda> x. if ?M x = {} then 0 else nat (Max (?M x))"
  { fix c m assume A: "(c, m) \<in> Timed_Automata.clkp_set A"
    from assms(1) have "finite (snd ` Timed_Automata.clkp_set A)" by auto
    moreover have "?M c \<subseteq> (snd ` Timed_Automata.clkp_set A)" by force
    ultimately have fin: "finite (?M c)" by (blast intro: finite_subset)
    then have "Max (?M c) \<in> {m . (c, m) \<in> Timed_Automata.clkp_set A}" using Max_in A by auto
    with assms(3) have "Max (?M c) \<in> \<nat>" by auto
    with A have "?k c = nat (Max (?M c))" by auto
    from fin A have "Max (?M c) \<ge> m" by auto
    moreover from A assms(3) have "m \<in> \<nat>" by auto
    ultimately have "m \<le> ?k c" "m \<in> \<nat>" "c \<in> X" using A \<open>clk_set A \<subseteq> X\<close> by force+
  }
  then have "\<forall>(x, m) \<in> Timed_Automata.clkp_set A. m \<le> ?k x \<and> x \<in> X \<and> m \<in> \<nat>" by blast
  with \<open>finite X\<close> 2 have "Timed_Automata.valid_abstraction A X ?k" by - (standard; assumption)
  then show ?thesis unfolding default_ceiling_def by auto
qed

(* XXX Not specific enough for implementation *)
definition default_numbering where
  "default_numbering A = (SOME v. bij_betw v A {1..card A} \<and>
  (\<forall> c \<in> A. v c > 0) \<and>
  (\<forall> c. c \<notin> A \<longrightarrow> v c > card A))"

(* XXX Not specific enough for implementation *)
lemma default_numbering:
  assumes "finite S"
  defines "v \<equiv> default_numbering S"
  defines "n \<equiv> card S"
  shows "bij_betw v S {1..n}" (is "?A")
  and "\<forall> c \<in> S. v c > 0" (is "?B")
  and "\<forall> c. c \<notin> S \<longrightarrow> v c > n" (is "?C")
proof -
  from standard_numbering[OF \<open>finite S\<close>] obtain v' and n' :: nat where v':
    "bij_betw v' S {1..n'} \<and> (\<forall> c \<in> S. v' c > 0) \<and> (\<forall> c. c \<notin> S \<longrightarrow> v' c > n')"
  by metis
  moreover from this(1) \<open>finite S\<close> have "n' = n" unfolding n_def by (auto simp: bij_betw_same_card)
  ultimately have "?A \<and> ?B \<and> ?C" unfolding v_def default_numbering_def
  by - (drule someI[where x = v']; simp add: n_def)
  then show ?A ?B ?C by auto
qed

(* XXX Unused *)
lemma finite_ta_Regions'_real:
  fixes A :: "('a, 'c, real, 's) ta"
  defines "x \<equiv> SOME x. x \<notin> clk_set A"
  assumes "finite_ta A"
  shows "Regions' (clk_set A) (default_numbering (clk_set A)) (card (clk_set A)) x"
proof -
  from assms obtain x' where x': "x' \<notin> clk_set A" unfolding finite_ta_def by auto
  then have x: "x \<notin> clk_set A" unfolding x_def by (rule someI)
  from \<open>finite_ta A\<close> have "finite (clk_set A)" unfolding finite_ta_def by auto
  with default_numbering[of "clk_set A"] assms have
            "bij_betw (default_numbering (clk_set A)) (clk_set A) {1..(card (clk_set A))}"
            "\<forall>c\<in>clk_set A. 0 < (default_numbering (clk_set A)) c"
            "\<forall>c. c \<notin> clk_set A \<longrightarrow> (card (clk_set A)) < (default_numbering (clk_set A)) c"
  by auto
  then show ?thesis using x assms unfolding finite_ta_def by - (standard, auto)
qed

(* XXX *)
lemma finite_ta_RegionsD_real:
  assumes "finite_ta A"
  defines "S \<equiv> clk_set A"
  defines "v \<equiv> default_numbering S"
  defines "n \<equiv> card S"
  defines "x \<equiv> SOME x. x \<notin> S"
  defines "k \<equiv> default_ceiling_real A"
  shows
    "Regions' (clk_set A) v n x" "Timed_Automata.valid_abstraction A (clk_set A) k"
    "global_clock_numbering A v n"
proof -
  from standard_abstraction_real assms have k:
    "Timed_Automata.valid_abstraction A (clk_set A) k"
  unfolding finite_ta_def by blast
  from finite_ta_Regions'_real[OF \<open>finite_ta A\<close>] have *: "Regions' (clk_set A) v n x" unfolding assms .
  then interpret interp: Regions' "clk_set A" k v n x .
  from interp.clock_numbering have "global_clock_numbering A v n" by blast
  with * k show
    "Regions' (clk_set A) v n x" "Timed_Automata.valid_abstraction A (clk_set A) k"
    "global_clock_numbering A v n"
  .
oops

lemma finite_ta_Regions'_int:
  fixes A :: "('a, 'c, int, 's) ta"
  defines "x \<equiv> SOME x. x \<notin> clk_set A"
  assumes "finite_ta A"
  shows "Regions' (clk_set A) (default_numbering (clk_set A)) (card (clk_set A)) x"
proof -
  from assms obtain x' where x': "x' \<notin> clk_set A" unfolding finite_ta_def by auto
  then have x: "x \<notin> clk_set A" unfolding x_def by (rule someI)
  from \<open>finite_ta A\<close> have "finite (clk_set A)" unfolding finite_ta_def by auto
  with default_numbering[of "clk_set A"] assms have
            "bij_betw (default_numbering (clk_set A)) (clk_set A) {1..(card (clk_set A))}"
            "\<forall>c\<in>clk_set A. 0 < (default_numbering (clk_set A)) c"
            "\<forall>c. c \<notin> clk_set A \<longrightarrow> (card (clk_set A)) < (default_numbering (clk_set A)) c"
  by auto
  then show ?thesis using x assms unfolding finite_ta_def by - (standard, auto)
qed

lemma finite_ta_RegionsD_int:
  fixes A :: "('a, 'c, int, 's) ta"
  assumes "finite_ta A"
  defines "S \<equiv> clk_set A"
  defines "v \<equiv> default_numbering S"
  defines "n \<equiv> card S"
  defines "x \<equiv> SOME x. x \<notin> S"
  defines "k \<equiv> default_ceiling A"
  shows
    "Regions' (clk_set A) v n x" "Timed_Automata.valid_abstraction A (clk_set A) k"
    "global_clock_numbering A v n"
proof -
  from standard_abstraction_int assms have k:
    "Timed_Automata.valid_abstraction A (clk_set A) k"
  unfolding finite_ta_def by blast
  from finite_ta_Regions'_int[OF \<open>finite_ta A\<close>] have *: "Regions' (clk_set A) v n x" unfolding assms .
  then interpret interp: Regions' "clk_set A" k v n x .
  from interp.clock_numbering have "global_clock_numbering A v n" by blast
  with * k show
    "Regions' (clk_set A) v n x" "Timed_Automata.valid_abstraction A (clk_set A) k"
    "global_clock_numbering A v n"
  .
qed

section \<open>Misc\<close>

(* XXX Interesting case of proving finiteness *)
(* XXX Move *)
lemma finite_project_snd:
  assumes "finite S" "\<And> a. finite (f a ` T)"
  shows "finite ((\<lambda> (a, b) . f a b) ` (S \<times> T))" (is "finite ?S")
proof -
  have "?S = {x . \<exists> a b. a \<in> S \<and> (b \<in> T \<and> x = f a b)}" by auto
  then show ?thesis
    using [[simproc add: finite_Collect]]
    by (auto simp: assms)
qed

lemma list_all_upt:
  fixes a b i :: nat
  shows "list_all (\<lambda> x. x < b) [a..<b]"
unfolding list_all_iff by auto

lemma norm_k_cong:
  assumes "\<forall> i \<le> n. k i = k' i"
  shows "norm M k n = norm M k' n"
using assms unfolding norm_def by fastforce

lemma norm_upd_norm'':
  fixes k :: "nat list"
  assumes "length k \<ge> Suc n"
  shows "curry (norm_upd M k n) = norm (curry M) (\<lambda> i. real (k ! i)) n"
 apply (simp add: curry_def norm_upd_norm)
 apply (rule norm_k_cong)
using assms by simp

lemma normalized_integral_dbms_finite':
  assumes "length k = Suc n"
  shows "finite {norm_upd M (k :: nat list) n | M. dbm_default (curry M) n}" (is "finite ?S")
proof -
  let ?k = "(\<lambda> i. k ! i)"
  have "norm_upd M k n = uncurry (norm (curry M) ?k n)" for M
    using assms by (subst norm_upd_norm, subst norm_k_cong) auto
  then have
    "?S \<subseteq> uncurry `
      {norm (curry M) (\<lambda>i. k ! i) n | M. dbm_default (curry M) n}"
    by auto
  moreover have "finite \<dots>"
    by (rule finite_imageI, rule finite_subset[rotated])
       (rule normalized_integral_dbms_finite[where n = n and k = ?k], blast)
  ultimately show ?thesis
    by (auto intro: finite_subset)
qed

(* XXX Move, here unnecessary *)
lemma And_commute:
  "And A B = And B A"
by (auto intro: min.commute)

lemma FW'_diag_preservation:
  assumes "\<forall> i \<le> n. M (i, i) \<le> 0"
  shows "\<forall> i \<le> n. (FW' M n) (i, i) \<le> 0"
using assms FW_diag_preservation[of n "curry M"] unfolding FW'_def by auto

lemma FW_neg_diag_preservation:
  "M i i < 0 \<Longrightarrow> i \<le> n \<Longrightarrow> (FW M n) i i < 0"
using fw_mono[of i n i M n] by auto

lemma FW'_neg_diag_preservation:
  assumes "M (i, i) < 0" "i \<le> n"
  shows "(FW' M n) (i, i) < 0"
using assms FW_neg_diag_preservation[of "curry M"] unfolding FW'_def by auto

lemma norm_empty_diag_preservation_int:
  fixes k :: "nat \<Rightarrow> nat"
  assumes "i \<le> n"
  assumes "M i i < Le 0"
  shows "norm M k n i i < Le 0"
  using assms unfolding norm_def norm_diag_def by (force simp: Let_def less dest: dbm_lt_trans)

lemma norm_diag_preservation_int:
  fixes k :: "nat \<Rightarrow> nat"
  assumes "i \<le> n"
  assumes "M i i \<le> Le 0"
  shows "norm M k n i i \<le> Le 0"
  using assms unfolding norm_def norm_diag_def
  by (force simp: Let_def less_eq dbm_le_def dest: dbm_lt_trans)

lemma And_diag1:
  assumes "A i i \<le> 0"
  shows "(And A B) i i \<le> 0"
using assms by (auto split: split_min)

lemma And_diag2:
  assumes "B i i \<le> 0"
  shows "(And A B) i i \<le> 0"
using assms by (auto split: split_min)

lemma abstra_upd_diag_preservation:
  assumes "i \<le> n" "constraint_clk ac \<noteq> 0"
  shows "(abstra_upd ac M) (i, i) = M (i, i)"
using assms by (cases ac) auto

lemma abstr_upd_diag_preservation:
  assumes "i \<le> n" "\<forall> c \<in> collect_clks cc. c \<noteq> 0"
  shows "(abstr_upd cc M) (i, i) = M (i, i)"
using assms unfolding abstr_upd_def
by (induction cc arbitrary: M) (auto simp: abstra_upd_diag_preservation)

lemma abstr_upd_diag_preservation':
  assumes "\<forall> i \<le> n. M (i, i) \<le> 0" "\<forall> c \<in> collect_clks cc. c \<noteq> 0"
  shows "\<forall> i \<le> n. (abstr_upd cc M) (i, i) \<le> 0"
using assms unfolding abstr_upd_def
by (induction cc arbitrary: M) (auto simp: abstra_upd_diag_preservation)

lemma up_diag_preservation:
  assumes "M i i \<le> 0"
  shows "(up M) i i \<le> 0"
  using assms unfolding up_def by (auto split: split_min)

lemma reset_diag_preservation:
  assumes "M i i \<le> 0" "d \<le> 0"
  shows "reset M n k d i i \<le> 0"
  using assms min_le_iff_disj unfolding neutral reset_def by auto

lemma reset'_diag_preservation:
  assumes "\<forall> i \<le> n. M i i \<le> 0" "d \<le> 0"
  shows "\<forall> i \<le> n. reset' M n cs v d i i \<le> 0"
  using assms
  by (induction cs) (auto intro: reset_diag_preservation)

section \<open>Implementation Semantics\<close>

lemma FW'_out_of_bounds1:
  assumes "i' > n"
  shows "(FW' M n) (i', j') = M (i', j')"
unfolding FW'_def using FW_out_of_bounds1[OF assms, where M = "curry M"] by auto

lemma FW'_out_of_bounds2:
  assumes "j' > n"
  shows "(FW' M n) (i', j') = M (i', j')"
unfolding FW'_def using FW_out_of_bounds2[OF assms, where M = "curry M"] by auto

inductive step_impl ::
  "('a, nat, 't :: linordered_ab_group_add, 's) ta \<Rightarrow> 's \<Rightarrow> 't DBM'
    \<Rightarrow> nat \<Rightarrow> 'a action \<Rightarrow> 's \<Rightarrow> 't DBM' \<Rightarrow> bool"
("_ \<turnstile>\<^sub>I \<langle>_, _\<rangle> \<leadsto>\<^bsub>_,_\<^esub> \<langle>_, _\<rangle>" [61,61,61] 61)
where
  step_t_impl:
    "A \<turnstile>\<^sub>I \<langle>l, D\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l, FW' (abstr_upd (inv_of A l) (up_canonical_upd D n)) n\<rangle>" |
  step_a_impl:
    "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'
    \<Longrightarrow> A \<turnstile>\<^sub>I \<langle>l, D\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a\<^esub> \<langle>l', FW' (abstr_upd (inv_of A l') (reset'_upd (FW' (abstr_upd g D) n) n r 0)) n\<rangle>"

inductive_cases step_impl_cases: "A \<turnstile>\<^sub>I \<langle>l, D\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l', D'\<rangle>"

declare step_impl.intros[intro]

lemma FW'_default:
  assumes "dbm_default (curry M) n"
  shows "dbm_default (curry (FW' M n)) n"
using assms by (simp add: FW'_out_of_bounds1 FW'_out_of_bounds2)

lemma abstr_upd_default:
  assumes "dbm_default (curry M) n" "\<forall>c\<in>collect_clks cc. c \<le> n"
  shows "dbm_default (curry (abstr_upd cc M)) n"
using assms by (auto simp: abstr_upd_out_of_bounds1 abstr_upd_out_of_bounds2)

lemma up_canonical_upd_default:
  assumes "dbm_default (curry M) n"
  shows "dbm_default (curry (up_canonical_upd M n)) n"
using assms by (auto simp: up_canonical_out_of_bounds1 up_canonical_out_of_bounds2)

lemma reset'_upd_default:
  assumes "dbm_default (curry M) n" "\<forall>c\<in>set cs. c \<le> n"
  shows "dbm_default (curry (reset'_upd M n cs d)) n"
using assms by (auto simp: reset'_upd_out_of_bounds1 reset'_upd_out_of_bounds2)

lemma FW'_int_preservation:
  assumes "dbm_int (curry M) n"
  shows "dbm_int (curry (FW' M n)) n"
using FW_int_preservation[OF assms] unfolding FW'_def curry_def by auto

lemma step_impl_norm_dbm_default_dbm_int:
  assumes "A \<turnstile>\<^sub>I \<langle>l, D\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l', D'\<rangle>" "dbm_default (curry D) n" "dbm_int (curry D) n"
    "\<forall> c \<in> clk_set A. c \<le> n \<and> c \<noteq> 0" "\<forall> (_, d)  \<in> Timed_Automata.clkp_set A. d \<in> \<int>"
  shows "dbm_default (curry D') n \<and> dbm_int (curry D') n"
  using assms
 apply (cases rule: step_impl.cases)

  subgoal \<comment> \<open>Step is a time delay step\<close>
  apply standard
  apply standard
  apply standard
      apply safe[]

    apply (simp add: FW'_out_of_bounds1)
    apply (subst abstr_upd_out_of_bounds1[where n = n])
    using collect_clks_inv_clk_set[of A] apply fastforce
    apply assumption
    apply (simp add: up_canonical_out_of_bounds1 FW'_out_of_bounds1; fail)

    apply standard
    apply safe[]
    apply (simp add: FW'_out_of_bounds2)
    apply (subst abstr_upd_out_of_bounds2[where n = n])
    using collect_clks_inv_clk_set[of A] apply fastforce
    apply assumption
    apply (simp add: up_canonical_out_of_bounds2 FW'_out_of_bounds2; fail)

    apply (simp only:)
    apply (rule FW'_int_preservation)
    apply (rule abstr_upd_int_preservation)
    defer
    apply (rule up_canonical_upd_int_preservation)
    apply (simp add: Timed_Automata.clkp_set_def Timed_Automata.collect_clki_def; fast)+
  done

  subgoal for g a r \<comment> \<open>Step is an action step\<close>
  apply standard
  apply standard
  apply standard
  apply safe[]

    apply (simp add: FW'_out_of_bounds1)
    apply (subst abstr_upd_out_of_bounds1[where n = n])
    using collect_clks_inv_clk_set[of A] apply fastforce
    apply assumption
    apply (subst reset'_upd_out_of_bounds1[where n = n])
    apply (fastforce simp: Timed_Automata.collect_clkvt_def)
    apply assumption
    apply (simp add: FW'_out_of_bounds1)
    apply (subst abstr_upd_out_of_bounds1[where n = n])
    using collect_clocks_clk_set apply fast
    apply assumption
    apply (simp; fail)

    apply safe[]
    apply (simp add: FW'_out_of_bounds2)
    apply (subst abstr_upd_out_of_bounds2[where n = n])
    using collect_clks_inv_clk_set[of A] apply fastforce
    apply assumption
    apply (subst reset'_upd_out_of_bounds2[where n = n])
    apply (fastforce simp: Timed_Automata.collect_clkvt_def)
    apply assumption
    apply (simp add: FW'_out_of_bounds2)
    apply (subst abstr_upd_out_of_bounds2[where n = n])
    using collect_clocks_clk_set apply fast
    apply assumption
    apply (simp; fail)

    apply (simp only:)
    apply (rule FW'_int_preservation)
    apply (rule abstr_upd_int_preservation)
    defer
    apply (rule reset'_upd_int_preservation)
    apply (rule FW'_int_preservation)
    apply (rule abstr_upd_int_preservation)
    apply (simp add: Timed_Automata.clkp_set_def Timed_Automata.collect_clkt_def; fast)
    apply assumption
    apply simp
    apply (auto dest!: reset_clk_set; fail)
    apply (simp add: Timed_Automata.clkp_set_def Timed_Automata.collect_clki_def; fast)
 done
done

inductive steps_impl ::
  "('a, nat, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('t :: linordered_ab_group_add) DBM'
  \<Rightarrow> ('s \<Rightarrow> 't list) \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> 't DBM' \<Rightarrow> bool"
("_ \<turnstile>\<^sub>I \<langle>_, _\<rangle> \<leadsto>\<^bsub>_,_\<^esub>* \<langle>_, _\<rangle>" [61,61,61,61] 61)
where
  refl: "A \<turnstile>\<^sub>I \<langle>l, Z\<rangle> \<leadsto>\<^bsub>k,n\<^esub>* \<langle>l, Z\<rangle>" |
  step: "A \<turnstile>\<^sub>I \<langle>l, Z\<rangle> \<leadsto>\<^bsub>k,n\<^esub>* \<langle>l', Z'\<rangle> \<Longrightarrow> A \<turnstile>\<^sub>I \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l'', Z''\<rangle>
        \<Longrightarrow> A \<turnstile>\<^sub>I \<langle>l'', Z''\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a\<^esub> \<langle>l''', Z'''\<rangle>
        \<Longrightarrow> A \<turnstile>\<^sub>I \<langle>l, Z\<rangle> \<leadsto>\<^bsub>k,n\<^esub>* \<langle>l''', FW' (norm_upd Z''' (k l''') n) n\<rangle>"

lemma steps_impl_induct[consumes 1, case_names refl step]:
  fixes
    A ::
      "('a \<times>
        (nat, 'b :: linordered_ab_group_add) acconstraint list \<times>
        'c \<times> nat list \<times> 'a) set \<times>
       ('a \<Rightarrow> (nat, 'b) acconstraint list)"

  assumes "A \<turnstile>\<^sub>I \<langle>x2, x3\<rangle> \<leadsto>\<^bsub>k,n\<^esub>* \<langle>x6, x7\<rangle>"
    and "\<And>l Z. P A l Z k n l Z"
    and
    "\<And>l Z l' Z' l'' Z'' a l''' Z'''.
        A \<turnstile>\<^sub>I \<langle>l, Z\<rangle> \<leadsto>\<^bsub>k,n\<^esub>* \<langle>l', Z'\<rangle> \<Longrightarrow>
        P A l Z k n l' Z' \<Longrightarrow>
        A \<turnstile>\<^sub>I \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l'', Z''\<rangle> \<Longrightarrow>
        A \<turnstile>\<^sub>I \<langle>l'', Z''\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a\<^esub> \<langle>l''', Z'''\<rangle> \<Longrightarrow>
        P A l Z k n l''' (FW' (norm_upd Z''' (k l''') n) n)"
  shows "P A x2 x3 k n x6 x7"
  using assms by (induction A\<equiv>A x2 x3 k \<equiv> k n \<equiv> n x6 x7; blast)

lemma steps_impl_norm_dbm_default_dbm_int:
  assumes "A \<turnstile>\<^sub>I \<langle>l, D\<rangle> \<leadsto>\<^bsub>k,n\<^esub>* \<langle>l', D'\<rangle>"
    and "dbm_default (curry D) n"
    and "dbm_int (curry D) n"
    and "\<forall>c\<in>clk_set A. c \<le> n \<and> c \<noteq> 0"
    and "\<forall>(_, d)\<in>Timed_Automata.clkp_set A. d \<in> \<int>"
    and "\<forall> l. \<forall>c\<in>set (k l). c \<in> \<int>"
    and "\<forall> l. length (k l) = Suc n"
  shows "l' = l \<and> D' = D \<or> (\<exists>M. D' = FW' (norm_upd M (k l') n) n \<and>
             ((\<forall>i>n. \<forall>j. curry M i j = 0) \<and> (\<forall>j>n. \<forall>i. curry M i j = 0)) \<and> dbm_int (curry M) n)"
using assms proof (induction)
  case refl then show ?case by auto
next
  case (step A l Z k n l' Z' l'' Z'' a l''' Z''')
  then have "
    Z' = Z \<or>
    (\<exists>M. Z' = FW' (norm_upd M (k l') n) n \<and>
         ((\<forall>i>n. \<forall>j. curry M i j = 0) \<and> (\<forall>j>n. \<forall>i. curry M i j = 0)) \<and> dbm_int (curry M) n)"
  by auto
  then show ?case
  proof (standard, goal_cases)
    case 1
    with step.prems step.hyps show ?thesis
      apply simp
      apply (drule step_impl_norm_dbm_default_dbm_int; simp)
      apply (drule step_impl_norm_dbm_default_dbm_int; simp)
      by metis
  next
    case 2
    then obtain M where M:
      "Z' = FW' (norm_upd M (k l') n) n" "dbm_default (curry M) n" "dbm_int (curry M) n"
    by auto
    with step.prems(3-) step.hyps show ?case
     apply -
     apply (drule step_impl_norm_dbm_default_dbm_int; simp)
      using FW'_default[OF norm_upd_default, where M2 = M] apply force
      using FW'_int_preservation[OF norm_upd_int_preservation, where M2 = M] apply force
      apply (drule step_impl_norm_dbm_default_dbm_int; simp)
      by metis
  qed
qed

(* XXX Naming conflict *)
definition valid_dbm where "valid_dbm M n \<equiv> dbm_int M n \<and> (\<forall> i \<le> n. M 0 i \<le> 0)"

lemma valid_dbm_pos:
  assumes "valid_dbm M n"
  shows "[M]\<^bsub>v,n\<^esub> \<subseteq> {u. \<forall> c. v c \<le> n \<longrightarrow> u c \<ge> 0}"
using dbm_positive assms unfolding valid_dbm_def unfolding DBM_zone_repr_def by fast

definition "init_dbm = (\<lambda> (x, y). Le 0)"


definition n_eq ("_ =\<^sub>_ _" [51,51,51] 50) where
  "n_eq M n M' \<equiv> \<forall> i \<le> n. \<forall> j \<le> n. M i j = M' i j"

lemma canonical_eq_upto:
  fixes A B :: "real DBM"
  assumes
    "clock_numbering' v n" "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
    "canonical A n" "canonical B n"
    "[A]\<^bsub>v,n\<^esub> \<noteq> {}" "[A]\<^bsub>v,n\<^esub> = [B]\<^bsub>v,n\<^esub>"
    "\<forall> i \<le> n. A i i = 0" "\<forall> i \<le> n. B i i = 0"
  shows "A =\<^sub>n B"
unfolding n_eq_def
using assms
apply -
apply standard
apply standard
apply standard
apply standard
subgoal for i j
  apply (cases "i = j")
  apply fastforce
  apply (rule order.antisym)
  apply (rule DBM_canonical_subset_le; auto)
  apply (rule DBM_canonical_subset_le; auto)
done
done

lemma up_canonical_upd_up_canonical':
  shows "curry (up_canonical_upd M n) =\<^sub>n up_canonical (curry M)"
by (auto simp: n_eq_def intro: up_canonical_upd_up_canonical)

lemma And_eqI':
  assumes "A =\<^sub>n A'" "B =\<^sub>n B'"
  shows "And A B =\<^sub>n (And A' B')"
using assms unfolding n_eq_def by auto

lemma n_eq_subst:
  assumes "A =\<^sub>n B"
  shows "(A =\<^sub>n C) = (B =\<^sub>n C)"
using assms unfolding n_eq_def by auto

lemma reset'''_reset'_upd'':
  assumes "\<forall>c\<in>set cs. c \<noteq> 0"
  shows "(curry (reset'_upd M n cs d)) =\<^sub>n (reset''' (curry M) n cs d)"
using reset'''_reset'_upd'[OF assms] unfolding n_eq_def by auto

lemma norm_eq_upto:
  assumes "A =\<^sub>n B"
  shows "norm A k n =\<^sub>n norm B k n"
using assms unfolding n_eq_def by (auto simp: norm_def)



lemma FW'_FW:
  "curry (FW' M n) = FW (curry M) n"
unfolding FW'_def by auto

lemma And_eqI:
  assumes "[A]\<^bsub>v,n\<^esub> = [A1]\<^bsub>v,n\<^esub>" "[B]\<^bsub>v,n\<^esub> = [B1]\<^bsub>v,n\<^esub>"
  shows "[And A B]\<^bsub>v,n\<^esub> = [And A1 B1]\<^bsub>v,n\<^esub>"
using assms by (simp only: And_correct[symmetric])

lemma DBM_zone_repr_up_eqI:
  assumes "clock_numbering' v n" "[A]\<^bsub>v,n\<^esub> = [B]\<^bsub>v,n\<^esub>"
  shows "[up A]\<^bsub>v,n\<^esub> = [up B]\<^bsub>v,n\<^esub>"
using assms DBM_up_complete'[where v = v] DBM_up_sound'[OF assms(1)] by fastforce

lemma reset'_correct:
  assumes "\<forall>c. 0 < v c \<and> (\<forall>x y. v x \<le> n \<and> v y \<le> n \<and> v x = v y \<longrightarrow> x = y)"
    and "\<forall>c\<in>set cs. v c \<le> n"
    and "\<forall>k\<le>n. 0 < k \<longrightarrow> (\<exists>c. v c = k)"
  shows "{[cs\<rightarrow>d]u | u. u \<in> [M]\<^bsub>v,n\<^esub>} = [reset' M n cs v d]\<^bsub>v,n\<^esub>"
proof safe
  fix u
  assume "u \<in> [M]\<^bsub>v,n\<^esub>"
  with DBM_reset'_complete[OF _ assms(1,2)] show
    "[cs\<rightarrow>d]u \<in> [reset' M n cs v d]\<^bsub>v,n\<^esub>"
  by (auto simp: DBM_zone_repr_def)
next
  fix u
  assume "u \<in> [reset' M n cs v d]\<^bsub>v,n\<^esub>"
  show "\<exists>u'. u = [cs\<rightarrow>d]u' \<and> u' \<in> [M]\<^bsub>v,n\<^esub>"
  proof (cases "[M]\<^bsub>v,n\<^esub> = {}")
    case True
    with \<open>u \<in> _\<close> DBM_reset'_empty[OF assms(3,1,2)] show ?thesis by auto
  next
    case False
    from DBM_reset'_sound[OF assms(3,1,2) \<open>u \<in> _\<close>] obtain ts where
      "set_clocks cs ts u \<in> [M]\<^bsub>v,n\<^esub>"
    by blast
    from DBM_reset'_resets'[OF assms(1,2)] \<open>u \<in> _\<close> \<open>_ \<noteq> {}\<close>
    have "u = [cs \<rightarrow> d](set_clocks cs ts u)" by (fastforce simp: reset_set DBM_zone_repr_def)
    with \<open>set_clocks _ _ _ \<in> _\<close> show ?thesis by auto
  qed
qed

lemma DBM_zone_repr_reset'_eqI:
  assumes "\<forall>c. 0 < v c \<and> (\<forall>x y. v x \<le> n \<and> v y \<le> n \<and> v x = v y \<longrightarrow> x = y)"
    and "\<forall>c\<in>set cs. v c \<le> n"
    and "\<forall>k\<le>n. 0 < k \<longrightarrow> (\<exists>c. v c = k)"
    and "[A]\<^bsub>v,n\<^esub> = [B]\<^bsub>v,n\<^esub>"
  shows "[reset' A n cs v d]\<^bsub>v,n\<^esub> = [reset' B n cs v d]\<^bsub>v,n\<^esub>"
using assms(4) reset'_correct[OF assms(1-3)] by blast

lemma up_canonical_neg_diag:
  assumes "M i i < 0"
  shows "(up_canonical M) i i < 0"
using assms unfolding up_canonical_def by auto

lemma up_neg_diag:
  assumes "M i i < 0"
  shows "(up M) i i < 0"
using assms unfolding up_def by (auto split: split_min)

lemma reset''_neg_diag:
  fixes v :: "'c \<Rightarrow> nat"
  assumes "\<forall> c. v c > 0" "M i i < 0" "i \<le> n"
  shows "(reset'' M n cs v d) i i < 0"
using reset''_diag_preservation[OF assms(1), where M = M and n = n] assms(2-) by auto

lemma FW_canonical':
  assumes "\<forall> i \<le> n. (FW M n) i i \<ge> 0"
  shows "canonical (FW M n) n"
  using FW_neg_cycle_detect assms
  unfolding cycle_free_diag_equiv
  by - (rule fw_canonical[unfolded cycle_free_diag_equiv]; fastforce)

lemma FW_neg_diag_equiv:
  assumes diag: "\<exists> i \<le> n. (FW A n) i i < 0"
      and surj: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
      and cn: "\<forall> c. v c > 0"
      and equiv: "[A]\<^bsub>v,n\<^esub> = [B]\<^bsub>v,n\<^esub>"
  shows "\<exists> i \<le> n. (FW B n) i i < 0"
proof -
  from assms obtain i where "(FW A n) i i < 0" "i \<le> n" by force
  with neg_diag_empty[OF surj] FW_zone_equiv[OF surj] equiv have "[B]\<^bsub>v,n\<^esub> = {}" by fastforce
  with FW_zone_equiv[OF surj] have "[FW B n]\<^bsub>v,n\<^esub> = {}" by auto
  then obtain i where
    "(FW B n) i i < 0" "i \<le> n"
  using FW_detects_empty_zone[OF surj, where M = B, folded neutral] cn
  by auto
  then show ?thesis by auto
qed

lemma FW_dbm_zone_repr_eqI2:
  assumes f_diag: "\<And> M i. i \<le> n \<Longrightarrow> M i i < 0 \<Longrightarrow> (f M) i i < 0"
      and g_diag: "\<And> M i. i \<le> n \<Longrightarrow> M i i < 0 \<Longrightarrow> (g M) i i < 0"
      and canonical:
      "\<And> A B. canonical A n \<Longrightarrow> canonical B n \<Longrightarrow> \<forall> i \<le> n. A i i = 0 \<Longrightarrow> \<forall> i \<le> n. B i i = 0
      \<Longrightarrow> [A]\<^bsub>v,n\<^esub> = [B]\<^bsub>v,n\<^esub>
      \<Longrightarrow> [f A]\<^bsub>v,n\<^esub> = [g B]\<^bsub>v,n\<^esub>"
      and surj: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
      and cn: "\<forall> c. v c > 0"
      and equiv: "[A]\<^bsub>v,n\<^esub> = [B]\<^bsub>v,n\<^esub>"
      and diag: "\<forall> i \<le> n. A i i \<le> 0" "\<forall> i \<le> n. B i i \<le> 0"
  shows "[f (FW A n)]\<^bsub>v,n\<^esub> = [g (FW B n)]\<^bsub>v,n\<^esub>"
proof (cases "\<forall> i \<le> n. (FW A n) i i \<ge> 0")
  case True
  with FW_neg_diag_equiv[OF _ surj cn equiv[symmetric]] have *: "\<forall>i\<le>n. 0 \<le> (FW B n) i i" by fastforce
  with True FW_diag_preservation[where M = A, OF diag(1)] FW_diag_preservation[where M = B, OF diag(2)]
        FW_zone_equiv[OF surj, of A] FW_zone_equiv[OF surj, of B] equiv
  show ?thesis by - (rule canonical[OF FW_canonical'[OF True] FW_canonical'[OF *]]; fastforce)
next
  case False
  then obtain i where "(FW A n) i i < 0" "i \<le> n" by force
  moreover with FW_neg_diag_equiv[OF _ surj cn equiv] obtain j where
    "(FW B n) j j < 0" "j \<le> n"
  using FW_detects_empty_zone[OF surj, where M = B, folded neutral] cn by auto
  ultimately have "f (FW A n) i i < 0" "g (FW B n) j j < 0" using f_diag g_diag by auto
  with \<open>i \<le> n\<close> \<open>j \<le> n\<close> neg_diag_empty[OF surj] show ?thesis by auto
qed

lemma FW_dbm_zone_repr_eqI:
  assumes f_diag: "\<And> M i. i \<le> n \<Longrightarrow> M i i < 0 \<Longrightarrow> (f M) i i < 0"
      and g_diag: "\<And> M i. i \<le> n \<Longrightarrow> M i i < 0 \<Longrightarrow> (g M) i i < 0"
      and canonical: "\<And> M. canonical M n \<Longrightarrow> [f M]\<^bsub>v,n\<^esub> = [g M]\<^bsub>v,n\<^esub>"
      and surj: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
  shows "[f (FW M n)]\<^bsub>v,n\<^esub> = [g (FW M n)]\<^bsub>v,n\<^esub>"
proof (cases "\<forall> i \<le> n. (FW M n) i i \<ge> 0")
  case True
  from canonical[OF FW_canonical'[OF True]] show ?thesis .
next
  case False
  then obtain i where "(FW M n) i i < 0" "i \<le> n" by force
  with f_diag g_diag have "f (FW M n) i i < 0" "g (FW M n) i i < 0" by auto
  with \<open>i \<le> n\<close> neg_diag_empty[OF surj] show ?thesis by auto
qed

lemma FW_dbm_zone_repr_eqI':
  assumes f_diag: "\<And> M i. i \<le> n \<Longrightarrow> M i i < 0 \<Longrightarrow> (f M) i i < 0"
      and g_diag: "\<And> M i. i \<le> n \<Longrightarrow> M i i < 0 \<Longrightarrow> (g M) i i < 0"
      and canonical: "\<And> M. canonical M n \<Longrightarrow> \<forall> i \<le> n. M i i = 0 \<Longrightarrow> [f M]\<^bsub>v,n\<^esub> = [g M]\<^bsub>v,n\<^esub>"
      and surj: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
      and diag: "\<forall> i \<le> n. M i i \<le> 0"
  shows "[f (FW M n)]\<^bsub>v,n\<^esub> = [g (FW M n)]\<^bsub>v,n\<^esub>"
proof (cases "\<forall> i \<le> n. (FW M n) i i \<ge> 0")
  case True
  with FW_diag_preservation[where M = M, OF diag] canonical[OF FW_canonical'[OF True]] show ?thesis
  by fastforce
next
  case False
  then obtain i where "(FW M n) i i < 0" "i \<le> n" by force
  with f_diag g_diag have "f (FW M n) i i < 0" "g (FW M n) i i < 0" by auto
  with \<open>i \<le> n\<close> neg_diag_empty[OF surj] show ?thesis by auto
qed


subsection \<open>Transfer Proofs\<close>

lemma conv_dbm_entry_mono:
  assumes "a \<le> b"
  shows "map_DBMEntry real_of_int a \<le> map_DBMEntry real_of_int b"
using assms by (cases a; cases b) (auto simp: less_eq dbm_le_def elim!: dbm_lt.cases)

lemma conv_dbm_entry_mono_strict:
  assumes "a < b"
  shows "map_DBMEntry real_of_int a < map_DBMEntry real_of_int b"
using assms by (cases a; cases b) (auto simp: less elim!: dbm_lt.cases)

(* Begin lifting syntax *)
context
  includes lifting_syntax
begin

definition "ri = (\<lambda> a b. real_of_int b = a)"

abbreviation "acri \<equiv> rel_acconstraint (=) ri"

abbreviation "acri' n \<equiv> rel_acconstraint (eq_onp (\<lambda> x. x < Suc n)) ri"

abbreviation
  "RI n \<equiv> (rel_prod (eq_onp (\<lambda> x. x < Suc n)) (eq_onp (\<lambda> x. x < Suc n)) ===> rel_DBMEntry ri)"

lemma rel_DBMEntry_map_DBMEntry_ri [simp, intro]:
  "rel_DBMEntry ri (map_DBMEntry real_of_int x) x"
by (cases x) (auto simp: ri_def)

lemma RI_fun_upd[transfer_rule]:
  "(RI n ===> (=) ===> rel_DBMEntry ri ===> RI n) fun_upd fun_upd"
unfolding rel_fun_def eq_onp_def by auto

lemma min_ri_transfer[transfer_rule]:
  "(rel_DBMEntry ri ===> rel_DBMEntry ri ===> rel_DBMEntry ri) min min"
unfolding rel_fun_def
  apply (simp split: split_min)
  apply safe

  subgoal for x y x' y'
    apply (drule not_le_imp_less)
    apply (drule conv_dbm_entry_mono_strict)
  by (cases x; cases x'; cases y; cases y'; auto simp: ri_def; fail)

  subgoal for x y x' y'
    apply (drule not_le_imp_less)
    apply (drule conv_dbm_entry_mono)
  by (cases x; cases x'; cases y; cases y'; auto simp: ri_def; fail)

done

lemma ri_neg[transfer_rule, intro]:
  "ri a b \<Longrightarrow> ri (-a) (-b)"
unfolding ri_def by auto

lemma abstra_upd_RI[transfer_rule]:
  "(acri' n ===> RI n ===> RI n) abstra_upd abstra_upd"
 apply rule
 apply rule
 subgoal for x y _ _
  apply (cases x; cases y)
 using min_ri_transfer unfolding eq_onp_def rel_fun_def by (auto dest: ri_neg)
done

lemma abstr_upd_RI[transfer_rule]:
  "(list_all2 (acri' n) ===> RI n ===> RI n) abstr_upd abstr_upd"
unfolding abstr_upd_def by transfer_prover

lemma uminus_RI[transfer_rule]:
  "(ri ===> ri) uminus uminus"
unfolding ri_def by auto

lemma add_RI[transfer_rule]:
  "(ri ===> ri ===> ri) ((+) ) (+)"
unfolding ri_def rel_fun_def by auto

lemma add_rel_DBMEntry_transfer[transfer_rule]:
  assumes R: "(A ===> B ===> C) (+) (+)"
  shows "(rel_DBMEntry A ===> rel_DBMEntry B ===> rel_DBMEntry C) (+) (+)"
  using R unfolding rel_fun_def[abs_def] apply safe
  subgoal for x1 y1 x2 y2
    by (cases x1; cases x2; cases y1; cases y2; simp add: add)
  done

lemma add_DBMEntry_RI[transfer_rule]:
  "(rel_DBMEntry ri ===> rel_DBMEntry ri ===> rel_DBMEntry ri) ((+) ) (+)"
  by transfer_prover

lemma norm_upper_RI[transfer_rule]:
  "(rel_DBMEntry ri ===> ri ===> rel_DBMEntry ri) norm_upper norm_upper"
  apply (intro rel_funI)
  subgoal for x y
    by (cases x; cases y; fastforce simp: ri_def less[symmetric])
  done

lemma norm_lower_RI[transfer_rule]:
  "(rel_DBMEntry ri ===> ri ===> rel_DBMEntry ri) norm_lower norm_lower"
  apply (intro rel_funI)
  subgoal for x y
    by (cases x; cases y; fastforce simp: ri_def less[symmetric])
  done

lemma norm_lower_RI':
  "(rel_DBMEntry ri ===> (=) ===> rel_DBMEntry ri) norm_lower norm_lower"
  apply (intro rel_funI)
  subgoal for x y
    by (cases x; cases y; fastforce simp: ri_def less[symmetric])
  done

lemma norm_diag_RI[transfer_rule]:
  "(rel_DBMEntry ri ===> rel_DBMEntry ri) norm_diag norm_diag"
  unfolding norm_diag_def
  apply (intro rel_funI)
  subgoal for x y
    by (cases x; cases y; fastforce simp: ri_def less[symmetric])
  done

lemma zero_RI[transfer_rule]:
  "ri 0 0"
by (simp add: ri_def)

lemma nth_transfer[transfer_rule]:
  fixes n :: nat
  shows "((\<lambda> x y. list_all2 A x y \<and> length x = n) ===> eq_onp (\<lambda> x. x < n) ===> A) (!) (!)"
by (auto simp: eq_onp_def ri_def rel_fun_def dest: list_all2_nthD)

lemma nth_RI:
  fixes n :: nat
  shows "((\<lambda> x y. list_all2 ri x y \<and> length x = n) ===> eq_onp (\<lambda> x. x < n) ===> ri) (!) (!)"
by (auto simp: eq_onp_def ri_def rel_fun_def dest: list_all2_nthD)

lemma nth_RI':
  fixes n :: nat
  shows "((\<lambda> x y. list_all2 ri x y \<and> length x = n) ===> (\<lambda> x y. x = y \<and> x < n) ===> ri) (!) (!)"
by (auto simp: ri_def rel_fun_def dest: list_all2_nthD)

lemma weakening:
  assumes "\<And> x y. B x y \<Longrightarrow> A x y" "(A ===> C) f g"
  shows "(B ===> C) f g"
using assms by (simp add: rel_fun_def)

lemma weakening':
  assumes "\<And> x y. B x y \<Longrightarrow> A x y" "(C ===> B) f g"
  shows "(C ===> A) f g"
using assms by (simp add: rel_fun_def)

lemma eq_onp_Suc:
  fixes n :: nat
  shows "(eq_onp (\<lambda> x. x = n) ===> eq_onp (\<lambda> x. x = Suc n)) Suc Suc"
unfolding rel_fun_def eq_onp_def by auto

lemma upt_transfer_upper_bound[transfer_rule]:
  "((=) ===> eq_onp (\<lambda> x. x = n) ===> list_all2 (eq_onp (\<lambda> x. x < n))) upt upt"
unfolding rel_fun_def eq_onp_def apply clarsimp
 apply (subst list.rel_eq_onp[unfolded eq_onp_def])
unfolding list_all_iff by auto

lemma zero_nat_transfer:
  "eq_onp (\<lambda> x. x < Suc n) 0 0"
by (simp add: eq_onp_def)

lemma [transfer_rule]:
  "bi_unique (rel_prod (eq_onp (\<lambda>x. x < Suc n)) (eq_onp (\<lambda>x. x < Suc n)))"
unfolding bi_unique_def eq_onp_def by auto

lemma [transfer_rule]:
  "(eq_onp P ===> (=) ===> (=)) (+) (+)"
unfolding eq_onp_def rel_fun_def by auto

lemma up_canonical_upd_RI2[transfer_rule]:
  "(RI n ===> (eq_onp (\<lambda> x. x < Suc n)) ===> RI n) up_canonical_upd up_canonical_upd"
unfolding up_canonical_upd_def[abs_def] by transfer_prover

lemma up_canonical_upd_RI[transfer_rule]:
  "(RI n ===> (eq_onp (\<lambda> x. x = n)) ===> RI n) up_canonical_upd up_canonical_upd"
unfolding up_canonical_upd_def[abs_def] by transfer_prover

lemma up_canonical_upd_RI3[transfer_rule]:
  "((rel_prod (=) (=) ===>
   rel_DBMEntry (=)) ===> (eq_onp (\<lambda> x. x = n)) ===> (rel_prod (=) (=) ===>
   rel_DBMEntry (=))) up_canonical_upd up_canonical_upd"
unfolding up_canonical_upd_def[abs_def] by transfer_prover

lemma eq_transfer:
  "(eq_onp (\<lambda> x. x < Suc n) ===> eq_onp (\<lambda> x. x < Suc n) ===> (=)) (=) (=)"
  by (intro rel_funI; simp add: eq_onp_def)

lemma norm_upd_norm:
  "norm_upd = (\<lambda>M k n (i, j). norm (curry M) (\<lambda>i. k ! i) n i j)"
  unfolding norm_upd_norm[symmetric] by simp

lemma less_transfer:
  "(eq_onp (\<lambda>x. x < Suc n) ===> eq_onp (\<lambda>x. x < Suc n) ===> (=)) (<) (<)"
  by (intro rel_funI; simp add: eq_onp_def)

lemma less_eq_transfer:
  "(eq_onp (\<lambda>x. x < Suc n) ===> eq_onp (\<lambda>x. x = n) ===> (=)) (\<le>) (\<le>)"
  by (intro rel_funI; simp add: eq_onp_def)

lemma norm_upd_transfer[transfer_rule]:
  fixes n :: nat
  notes eq_onp_Suc[of n, transfer_rule] zero_nat_transfer[transfer_rule] eq_transfer[transfer_rule]
    less_transfer[transfer_rule] less_eq_transfer[transfer_rule]
  shows
    "(RI n ===> (\<lambda>x y. list_all2 ri x y \<and> length x = Suc n) ===> eq_onp (\<lambda>x. x = n)  ===> RI n)
    norm_upd norm_upd"
    unfolding norm_upd_norm norm_def by transfer_prover

lemma dbm_entry_val_ri:
  assumes "rel_DBMEntry ri e e'" "dbm_entry_val u c d e"
  shows "dbm_entry_val u c d (map_DBMEntry real_of_int e')"
using assms by (cases e; cases e') (auto simp: ri_def)

lemma dbm_entry_val_ir:
  assumes "rel_DBMEntry ri e e'" "dbm_entry_val u c d (map_DBMEntry real_of_int e')"
  shows "dbm_entry_val u c d e"
using assms by (cases e; cases e') (auto simp: ri_def)

lemma bi_unique_eq_onp_less_Suc[transfer_rule]:
  "bi_unique (eq_onp (\<lambda>x. x < Suc n))"
by (simp add: eq_onp_def bi_unique_def)

lemma fw_upd_transfer[transfer_rule]:
 "((eq_onp (\<lambda> x. x < Suc n) ===> eq_onp (\<lambda> x. x < Suc n) ===> rel_DBMEntry ri)
  ===> eq_onp (\<lambda> x. x < Suc n) ===> eq_onp (\<lambda> x. x < Suc n) ===> eq_onp (\<lambda> x. x < Suc n)
  ===> (eq_onp (\<lambda> x. x < Suc n) ===> eq_onp (\<lambda> x. x < Suc n) ===> rel_DBMEntry ri))
  fw_upd fw_upd"
  unfolding fw_upd_def Floyd_Warshall.upd_def by transfer_prover

lemma fw_upd_transfer'[transfer_rule]:
 "(((=) ===> (=) ===> rel_DBMEntry ri)
  ===> (=) ===> (=) ===> (=)
  ===> ((=) ===> (=) ===> rel_DBMEntry ri))
  fw_upd fw_upd"
  unfolding fw_upd_def Floyd_Warshall.upd_def by transfer_prover

lemma fwi_RI_transfer_aux:
  assumes
    "((\<lambda>x y. x < Suc n \<and> x = y) ===> (\<lambda>x y. x < Suc n \<and> x = y) ===> rel_DBMEntry ri) M M'"
    "k < Suc n" "i < Suc n" "j < Suc n"
  shows
  "((\<lambda>x y. x < Suc n \<and> x = y) ===> (\<lambda>x y. x < Suc n \<and> x = y) ===> rel_DBMEntry ri)
   (fwi M n k i j) (fwi M' n k i j)"
using assms
apply (induction _ "(i, j)" arbitrary: i j
    rule: wf_induct[of "less_than <*lex*> less_than"]
  )
  apply (auto; fail)
 subgoal for i j
 apply (cases i; cases j; auto simp add: fw_upd_out_of_bounds2)
 unfolding eq_onp_def[symmetric]
 apply (drule rel_funD[OF fw_upd_transfer[of n]])
 apply (auto simp: eq_onp_def dest: rel_funD; fail)

 subgoal premises prems for n'
 proof -
  from prems have
    "(eq_onp (\<lambda>x. x < Suc n) ===> eq_onp (\<lambda>x. x < Suc n) ===> rel_DBMEntry ri)
        (fwi M n k 0 n') (fwi M' n k 0 n')"
  by auto
  then show ?thesis
   apply -
   apply (drule rel_funD[OF fw_upd_transfer[of n]])
   apply (drule rel_funD[where x = k and y = k])
   apply (simp add: eq_onp_def \<open>k < Suc n\<close>; fail)
   apply (drule rel_funD[where x = 0 and y = 0])
   apply (simp add: eq_onp_def; fail)
   apply (drule rel_funD[where x = "Suc n'" and y = "Suc n'"])
   using prems apply (simp add: eq_onp_def; fail)
   apply assumption
  done
 qed

 subgoal premises prems for n'
 proof -
  from prems have
    "(eq_onp (\<lambda>x. x < Suc n) ===> eq_onp (\<lambda>x. x < Suc n) ===> rel_DBMEntry ri)
        (fwi M n k n' n) (fwi M' n k n' n)"
  by auto
  then show ?thesis
   apply -
   apply (drule rel_funD[OF fw_upd_transfer[of n]])
   apply (drule rel_funD[where x = k and y = k])
   apply (simp add: eq_onp_def \<open>k < Suc n\<close>; fail)
   apply (drule rel_funD[where x = "Suc n'" and y = "Suc n'"])
   using prems apply (simp add: eq_onp_def; fail)
   apply (drule rel_funD[where x = 0 and y = 0])
   using prems apply (simp add: eq_onp_def; fail)
   apply assumption
  done
 qed

 subgoal premises prems for i j
 proof -
  from prems have
    "(eq_onp (\<lambda>x. x < Suc n) ===> eq_onp (\<lambda>x. x < Suc n) ===> rel_DBMEntry ri)
        (fwi M n k (Suc i) j) (fwi M' n k (Suc i) j)"
  by auto
  then show ?thesis
   apply -
   apply (drule rel_funD[OF fw_upd_transfer[of n]])
   apply (drule rel_funD[where x = k and y = k])
   apply (simp add: eq_onp_def \<open>k < Suc n\<close>; fail)
   apply (drule rel_funD[where x = "Suc i" and y = "Suc i"])
   using prems apply (simp add: eq_onp_def; fail)
   apply (drule rel_funD[where x = "Suc j" and y = "Suc j"])
   using prems apply (simp add: eq_onp_def; fail)
   apply assumption
  done
 qed
done
done

lemma fw_RI_transfer_aux:
  assumes
    "((\<lambda>x y. x < Suc n \<and> x = y) ===> (\<lambda>x y. x < Suc n \<and> x = y) ===> rel_DBMEntry ri) M M'"
    "k < Suc n"
  shows
    "((\<lambda>x y. x < Suc n \<and> x = y) ===> (\<lambda>x y. x < Suc n \<and> x = y) ===> rel_DBMEntry ri)
   (fw M n k) (fw M' n k)"
  using assms
  by (induction k) (auto intro: fwi_RI_transfer_aux)

lemma fwi_RI_transfer[transfer_rule]:
  "((eq_onp (\<lambda> x. x < Suc n) ===> eq_onp (\<lambda> x. x < Suc n) ===> rel_DBMEntry ri)
  ===> eq_onp (\<lambda> x. x = n) ===> eq_onp (\<lambda> x. x < Suc n) ===> eq_onp (\<lambda> x. x < Suc n)
  ===> eq_onp (\<lambda> x. x < Suc n) ===> (eq_onp (\<lambda> x. x < Suc n) ===> eq_onp (\<lambda> x. x < Suc n)
  ===> rel_DBMEntry ri)) fwi fwi"
 apply (rule rel_funI)
 apply (rule rel_funI)
 apply (rule rel_funI)
 apply (rule rel_funI)
 apply (rule rel_funI)
by (auto intro: fwi_RI_transfer_aux simp: eq_onp_def)

lemma fw_RI_transfer[transfer_rule]:
  "((eq_onp (\<lambda> x. x < Suc n) ===> eq_onp (\<lambda> x. x < Suc n) ===> rel_DBMEntry ri)
  ===> eq_onp (\<lambda> x. x = n) ===> eq_onp (\<lambda> x. x < Suc n)
  ===> (eq_onp (\<lambda> x. x < Suc n) ===> eq_onp (\<lambda> x. x < Suc n) ===> rel_DBMEntry ri))
  fw fw"
 apply (rule rel_funI)
 apply (rule rel_funI)
 apply (rule rel_funI)
by (auto intro: fw_RI_transfer_aux simp: eq_onp_def)

lemma FW_RI_transfer[transfer_rule]:
  "((eq_onp (\<lambda> x. x < Suc n) ===> eq_onp (\<lambda> x. x < Suc n) ===> rel_DBMEntry ri)
  ===> eq_onp (\<lambda> x. x = n)
  ===> (eq_onp (\<lambda> x. x < Suc n) ===> eq_onp (\<lambda> x. x < Suc n) ===> rel_DBMEntry ri)) FW FW"
by standard+ (drule rel_funD[OF fw_RI_transfer]; auto simp: rel_fun_def eq_onp_def)

lemma FW_RI_transfer'[transfer_rule]:
  "(RI n ===> eq_onp (\<lambda> x. x = n) ===> RI n) FW' FW'"
using FW_RI_transfer[of n] unfolding FW'_def uncurry_def[abs_def] rel_fun_def by auto

definition RI_I :: "nat \<Rightarrow> (nat, real, 's) invassn \<Rightarrow> (nat, int, 's) invassn \<Rightarrow> bool" where
  "RI_I n \<equiv> ((=) ===> list_all2 (acri' n))"

definition
  "RI_T n \<equiv> rel_prod (=) (rel_prod (list_all2 (acri' n)) (rel_prod (=) (rel_prod (list_all2 (eq_onp (\<lambda> x. x < Suc n))) (=))))"

definition RI_A :: "nat \<Rightarrow> ('a, nat, real, 's) ta \<Rightarrow> ('a, nat, int, 's) ta \<Rightarrow> bool" where
  "RI_A n \<equiv> rel_prod (rel_set (RI_T n)) (RI_I n)"

lemma inv_of_transfer [transfer_rule]:
  "(RI_A n ===> RI_I n) inv_of inv_of"
unfolding RI_A_def inv_of_def by transfer_prover

lemma FW'_rsp:
  "((=) ===> (=) ===> (=)) FW' FW'"
unfolding rel_fun_def by auto

lemma [transfer_rule]:
  "(list_all2 (eq_onp (\<lambda> x. x < Suc n))) [1..n] [1..n]"
unfolding eq_onp_def
apply (rule list_all2I)
(* apply (smt atLeastAtMost_iff mem_Collect_eq of_nat_Suc prod.simps(2) set_upto set_zip set_zip_rightD) *)
apply auto
apply (metis ab_semigroup_add_class.add.commute atLeastAtMost_iff in_set_zipE int_le_real_less of_int_less_iff of_int_of_nat_eq of_nat_Suc set_upto)
by (simp add: zip_same)

lemmas [transfer_rule] = zero_nat_transfer

definition
  "reset_canonical_upd' n M = reset_canonical_upd M n"

lemma [transfer_rule]:
  "(eq_onp (\<lambda>x. x < int (Suc n)) ===> eq_onp (\<lambda>x. x < Suc n)) nat nat"
unfolding eq_onp_def rel_fun_def by auto

lemma reset_canonical_upd_RI_aux:
  "(RI n ===> eq_onp (\<lambda> x. x < Suc n) ===> ri ===> RI n)
  (reset_canonical_upd' n) (reset_canonical_upd' n)"
unfolding reset_canonical_upd'_def[abs_def] reset_canonical_upd_def[abs_def] by transfer_prover

lemma reset_canonical_upd_RI[transfer_rule]:
  "(RI n ===> eq_onp (\<lambda> x. x = n) ===> eq_onp (\<lambda> x. x < Suc n) ===> ri ===> RI n)
  reset_canonical_upd reset_canonical_upd"
using reset_canonical_upd_RI_aux unfolding reset_canonical_upd'_def[abs_def] rel_fun_def eq_onp_def
by auto

lemma reset'_upd_RI[transfer_rule]:
  "(RI n ===> eq_onp (\<lambda> x. x = n) ===> list_all2 (eq_onp (\<lambda> x. x < Suc n)) ===> ri ===> RI n)
  reset'_upd reset'_upd"
unfolding reset'_upd_def[abs_def] by transfer_prover

(* Information hiding for transfer prover *)
definition "ri_len n = (\<lambda> x y. list_all2 ri x y \<and> length x = Suc n)"

lemma RI_complete:
  assumes lifts: "RI n D M" "RI_A n A' A"
      and step: "A' \<turnstile>\<^sub>I \<langle>l,D\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l',D'\<rangle>"
  shows "\<exists> M'. A \<turnstile>\<^sub>I \<langle>l,M\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l',M'\<rangle> \<and> RI n D' M'"
using step proof cases
  case prems: step_t_impl
  let ?M' =
    "FW' (abstr_upd (inv_of A l) (up_canonical_upd M n)) n"

  note [transfer_rule] = lifts inv_of_transfer[unfolded RI_I_def]
  have [transfer_rule]: "eq_onp (\<lambda>x. x = n) n n" by (simp add: eq_onp_def)
  have "RI n D' ?M'" unfolding prems by transfer_prover
  with \<open>a = \<tau>\<close> \<open>l' = l\<close> show ?thesis by auto
next
  case prems: (step_a_impl g' a r')
  obtain T I T' I' where "A = (T, I)" and "A' = (T', I')" by force
  with lifts(2) prems(3) obtain g r where
    "(rel_prod (=) (rel_prod (list_all2 (acri' n)) (rel_prod (=) (rel_prod (list_all2 (eq_onp (\<lambda> x. x < Suc n))) (=)))))
     (l, g', a, r', l') (l, g, a, r, l')"
    "(l, g, a, r, l') \<in> T"
  unfolding RI_A_def RI_T_def rel_set_def trans_of_def by (cases rule: rel_prod.cases) fastforce
  with \<open>A = _\<close> have g':
    "list_all2 (acri' n) g' g" "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" "(list_all2 (eq_onp (\<lambda> x. x < Suc n))) r' r"
  unfolding trans_of_def by (auto dest: rel_prod.cases)
  from this(3) have "r' = r" unfolding eq_onp_def by (simp add: list_all2_eq list_all2_mono)

  let ?M' = "FW' (abstr_upd (inv_of A l') (reset'_upd (FW' (abstr_upd g M) n) n r 0)) n"
  have [transfer_rule]: "eq_onp (\<lambda>x. x = n) n n" by (simp add: eq_onp_def)
  note [transfer_rule] = g'[unfolded \<open>r' = r\<close>] lifts inv_of_transfer[unfolded RI_I_def]
  have "RI n D' ?M'" unfolding prems \<open>r' = r\<close> by transfer_prover
  with g' prems(1) show ?thesis unfolding \<open>r' = r\<close> by auto
qed

lemma IR_complete:
  assumes lifts: "RI n D M" "RI_A n A' A"
      and step: "A \<turnstile>\<^sub>I \<langle>l,M\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l',M'\<rangle>"
  shows "\<exists> D'. A' \<turnstile>\<^sub>I \<langle>l,D\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l',D'\<rangle> \<and> RI n D' M'"
using step proof cases
  case prems: step_t_impl
  let ?D' =
    "FW' (abstr_upd (inv_of A' l) (up_canonical_upd D n)) n"

  note [transfer_rule] = lifts inv_of_transfer[unfolded RI_I_def]
  have [transfer_rule]: "eq_onp (\<lambda>x. x = n) n n" by (simp add: eq_onp_def)
  have "RI n ?D' M'" unfolding prems by transfer_prover
  with \<open>l' = l\<close> \<open>a = \<tau>\<close> show ?thesis by auto
next
  case prems: (step_a_impl g a r)
  obtain T I T' I' where "A = (T, I)" and "A' = (T', I')" by force
  with lifts(2) prems(3) obtain g' r' where
    "(rel_prod (=) (rel_prod (list_all2 (acri' n)) (rel_prod (=) (rel_prod (list_all2 (eq_onp (\<lambda> x. x < Suc n))) (=)))))
     (l, g', a, r', l') (l, g, a, r, l')"
    "(l, g', a, r', l') \<in> T'"
  unfolding RI_A_def RI_T_def rel_set_def trans_of_def by (cases rule: rel_prod.cases) fastforce
  with \<open>A' = _\<close> have g':
    "list_all2 (acri' n) g' g" "A' \<turnstile> l \<longrightarrow>\<^bsup>g',a,r'\<^esup> l'" "(list_all2 (eq_onp (\<lambda> x. x < Suc n))) r' r"
  unfolding trans_of_def by (auto dest: rel_prod.cases)
  from this(3) have "r' = r" unfolding eq_onp_def by (simp add: list_all2_eq list_all2_mono)

  let ?D' = "FW' (abstr_upd (inv_of A' l') (reset'_upd (FW' (abstr_upd g' D) n) n r 0)) n"
  have [transfer_rule]: "eq_onp (\<lambda>x. x = n) n n" by (simp add: eq_onp_def)
  note [transfer_rule] = g'[unfolded \<open>r' = r\<close>] lifts inv_of_transfer[unfolded RI_I_def]
  have "RI n ?D' M'" unfolding prems by transfer_prover
  with g' prems(1) show ?thesis unfolding \<open>r' = r\<close> by auto
qed

lemma RI_norm_step:
  assumes lifts: "RI n D M" "list_all2 ri k' k"
      and len: "length k' = Suc n"
  shows "RI n (FW' (norm_upd (FW' D n) k' n) n) (FW' (norm_upd (FW' M n) k n) n)"
proof -
  note [transfer_rule] = lifts norm_upd_transfer[folded ri_len_def]
  have [transfer_rule]: "eq_onp (\<lambda>x. x = n) n n" by (simp add: eq_onp_def)
  have [transfer_rule]: "(ri_len n) k' k" using len lifts by (simp add: ri_len_def eq_onp_def)

  show ?thesis by transfer_prover
qed

end (* End of lifting syntax *)



subsection \<open>Semantic Equivalence\<close>

lemma delay_step_impl_correct:
  assumes "canonical (curry D) n" (* XXX atm unused, would need for optimized variant without full FW *)
          "clock_numbering' v n" "\<forall>c\<in>collect_clks (inv_of A l). v c = c \<and> c > 0 \<and> v c \<le> n"
      and surj: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
  assumes D_inv: "D_inv = abstr (inv_of A l) (\<lambda>i j. \<infinity>) v"
  shows
  "[curry (abstr_upd (inv_of A l) (up_canonical_upd D n))]\<^bsub>v,n\<^esub> =
  [And (up (curry D)) D_inv]\<^bsub>v,n\<^esub>"
  apply (subst abstr_upd_abstr')
   defer
   apply (subst abstr_abstr'[symmetric])
    defer
  unfolding D_inv
    apply (subst And_abstr[symmetric])
      defer
      defer
      apply (rule And_eqI)
       apply (subst DBM_up_to_equiv[folded n_eq_def, OF up_canonical_upd_up_canonical'])
  using assms by (fastforce intro!: up_canonical_equiv_up)+

lemma action_step_impl_correct:
  assumes "canonical (curry D) n" (* XXX atm unused, would need for optimized variant without full FW *)
    "clock_numbering' v n" "\<forall>c\<in>collect_clks (inv_of A l'). v c = c \<and> c > 0 \<and> v c \<le> n"
    "\<forall>c\<in>collect_clks g. v c = c \<and> c > 0 \<and> v c \<le> n"
    "\<forall>c\<in> set r. v c = c \<and> c > 0 \<and> v c \<le> n"
    "\<forall> i \<le> n. D (i, i) \<le> 0"
    and surj: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
  shows
    "[curry (abstr_upd (inv_of A l') (reset'_upd (FW' (abstr_upd g D) n) n r 0))]\<^bsub>v,n\<^esub> =
   [And (reset' (And (curry D) (abstr g (\<lambda>i j. \<infinity>) v)) n r v 0)
                               (abstr (inv_of A l') (\<lambda>i j. \<infinity>) v)]\<^bsub>v,n\<^esub>"
  apply (subst abstr_upd_abstr', use assms in fastforce)
  apply (subst abstr_abstr'[symmetric, where v = v], use assms in fastforce)
  apply (subst And_abstr[symmetric], use assms in fastforce, use assms in fastforce)
  apply (rule And_eqI[rotated], rule HOL.refl)
  apply (subst DBM_up_to_equiv[folded n_eq_def, OF reset'''_reset'_upd''],
      use assms in fastforce)
  apply (subst reset''_reset'''[symmetric, where v = v], use assms in fastforce)
  apply (subst FW'_FW)
  apply (subst FW_dbm_zone_repr_eqI'[where g = "\<lambda> M. reset' M n r v 0"])
       apply (rule reset''_neg_diag; fastforce simp: assms(2))
      apply (erule DBM_reset'_neg_diag_preservation',
        assumption, use assms(2) in fastforce, use assms in fastforce)
     apply (erule reset'_reset''_equiv[symmetric]; use assms in fastforce)
  using assms apply fastforce
  subgoal
  proof -
    show "\<forall>i\<le>n. curry (abstr_upd g D) i i \<le> 0"
      using assms(4) abstr_upd_diag_preservation'[OF assms(6)] by fastforce
  qed
  apply (rule DBM_zone_repr_reset'_eqI,
      use assms in fastforce, use assms in fastforce, use assms in fastforce)
  apply (subst FW_zone_equiv[symmetric], use assms in fastforce)
  apply (subst abstr_upd_abstr', use assms in fastforce)
  apply (subst abstr_abstr'[symmetric, where v = v], use assms in fastforce)
  apply (rule And_abstr[symmetric]; use assms in fastforce)
  done

lemma norm_impl_correct:
  fixes k :: "nat list"
  assumes (* XXX atm unused, would need for optimized variant without full FW *)
          "clock_numbering' v n"
          "\<forall> i \<le> n. D (i, i) \<le> 0"
          "\<forall> i \<le> n. M i i \<le> 0"
      and surj: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
      and k: "Suc n \<le> length k"
      and equiv: "[curry D]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>"
  shows
    "[curry (FW' (norm_upd (FW' D n) k n) n)]\<^bsub>v,n\<^esub> = [norm (FW M n) (\<lambda> i. k ! i) n]\<^bsub>v,n\<^esub>"
 apply (subst FW'_FW)
 apply (subst FW_zone_equiv[symmetric, OF surj])
 apply (subst norm_upd_norm'')
  apply (simp add: k; fail)
 apply (subst FW'_FW)
 subgoal
  apply (rule FW_dbm_zone_repr_eqI2)
  apply (rule norm_empty_diag_preservation_real[folded neutral, unfolded comp_def]; assumption)
  apply (rule norm_empty_diag_preservation_real[folded neutral, unfolded comp_def]; assumption)
  subgoal
   apply (rule DBM_up_to_equiv[folded n_eq_def])
   apply (rule norm_eq_upto)
   apply (rule canonical_eq_upto)
   apply (rule assms)
   apply (rule assms)
   apply assumption
   apply assumption
   using \<open>clock_numbering' v n\<close>
   apply - apply (rule cyc_free_not_empty[OF canonical_cyc_free])
  by simp+
  using assms by fastforce+
done

lemma norm_action_step_impl_correct:
  fixes k :: "nat list"
  assumes "canonical (curry D) n" (* XXX atm unused, would need for optimized variant without full FW *)
          "clock_numbering' v n" "\<forall>c\<in>collect_clks (inv_of A l'). v c = c \<and> c > 0 \<and> v c \<le> n"
          "\<forall>c\<in>collect_clks g. v c = c \<and> c > 0 \<and> v c \<le> n"
          "\<forall>c\<in> set r. v c = c \<and> c > 0 \<and> v c \<le> n"
          "\<forall> i \<le> n. D (i, i) \<le> 0"
      and surj: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
      and k: "Suc n \<le> length k"
  shows
  "[curry (FW' (norm_upd (FW' (abstr_upd (inv_of A l') (reset'_upd (FW' (abstr_upd g D) n) n r 0)) n) k n) n)]\<^bsub>v,n\<^esub> =
   [norm (FW(And (reset' (And (curry D) (abstr g (\<lambda>i j. \<infinity>) v)) n r v 0)
                               (abstr (inv_of A l') (\<lambda>i j. \<infinity>) v)) n) (\<lambda> i. k ! i) n]\<^bsub>v,n\<^esub>"
 apply (rule norm_impl_correct)
 apply (rule assms)

 subgoal
  apply (rule abstr_upd_diag_preservation')
  apply safe[]
  apply (subst reset'_upd_diag_preservation)
  using assms(5) apply fastforce
  apply assumption
  apply (simp add: FW'_def)
  apply (rule FW_diag_preservation[rule_format])
  apply (simp add: curry_def)
  apply (rule abstr_upd_diag_preservation'[rule_format, where n = n])
  using assms(6) apply fastforce
  using assms(4) apply fastforce
  apply assumption
  apply assumption
 using assms(3) by fastforce

 subgoal
  apply safe[]
  apply (rule And_diag1)
  apply (rule DBM_reset'_diag_preservation[rule_format])
  apply (rule And_diag1)
  using assms(6) apply simp
  using assms(2) apply simp
  using assms(5) apply metis
 by assumption

 apply (rule surj; fail)
 apply (rule k; fail)
 apply (rule action_step_impl_correct; rule assms)
done

lemma norm_delay_step_impl_correct:
  fixes k :: "nat list"
  assumes "canonical (curry D) n" (* XXX atm unused, would need for optimized variant without full FW *)
          "clock_numbering' v n" "\<forall>c\<in>collect_clks (inv_of A l). v c = c \<and> c > 0 \<and> v c \<le> n"
          "\<forall> i \<le> n. D (i, i) \<le> 0"
      and surj: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
      and k: "Suc n \<le> length k"
  assumes D_inv: "D_inv = abstr (inv_of A l) (\<lambda>i j. \<infinity>) v"
  shows
  "[curry (FW' (norm_upd (FW' (abstr_upd (inv_of A l) (up_canonical_upd D n)) n) k n) n)]\<^bsub>v,n\<^esub> =
  [norm (FW(And (up (curry D)) D_inv) n) (\<lambda> i. k ! i) n]\<^bsub>v,n\<^esub>"
 apply (rule norm_impl_correct)
 apply (rule assms)

 subgoal
  apply (rule abstr_upd_diag_preservation')
  apply safe[]
  apply (subst up_canonical_upd_diag_preservation)
  using assms(3,4) by fastforce+

 subgoal
  apply safe[]
  apply (rule And_diag1)
  apply (rule up_diag_preservation)
  using assms(4) apply fastforce
 done

 apply (rule surj; fail)
 apply (rule k; fail)
 apply (rule delay_step_impl_correct; rule assms; fail)

done

lemma step_impl_sound:
  assumes step: "A \<turnstile>\<^sub>I \<langle>l,M\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l',M'\<rangle>"
  assumes canonical: "canonical (curry M) n"
  assumes numbering: "global_clock_numbering A v n" "\<forall> c \<in> clk_set A. v c = c"
  assumes diag: "\<forall>i\<le>n. M (i, i) \<le> 0"
  shows "\<exists> D. A \<turnstile> \<langle>l,curry M\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l',D\<rangle> \<and> [curry M']\<^bsub>v,n\<^esub> = [D]\<^bsub>v,n\<^esub>"
proof -
  have *:
    "\<forall>c. 0 < v c \<and> (\<forall>x y. v x \<le> n \<and> v y \<le> n \<and> v x = v y \<longrightarrow> x = y)"
    "\<forall>k\<le>n. 0 < k \<longrightarrow> (\<exists>c. v c = k)" "\<forall>c\<in>clk_set A. v c \<le> n"
  using numbering by metis+
  from step show ?thesis
  proof cases
    case prems: step_t_impl
    from *(1,3) numbering(2) collect_clks_inv_clk_set have
      "\<forall>c\<in>collect_clks (inv_of A l). v c = c \<and> 0 < v c \<and> v c \<le> n"
    by fast
    then have **:
      "\<forall>c\<in>collect_clks (inv_of A l). v c = c \<and> 0 < c \<and> v c \<le> n"
    by fastforce
    let ?D_inv = "abstr (inv_of A l) (\<lambda>i j. \<infinity>) v"
    from prems delay_step_impl_correct[OF canonical *(1) ** *(2)] have
      "[curry M']\<^bsub>v,n\<^esub> = [And (up (curry M)) ?D_inv]\<^bsub>v,n\<^esub>"
      by (simp add: FW'_FW FW_zone_equiv[OF *(2), symmetric])
    moreover have
      "A \<turnstile> \<langle>l,curry M\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l',And (up (curry M)) ?D_inv\<rangle>"
      unfolding \<open>a = _\<close> \<open>l' = l\<close> by blast
    ultimately show ?thesis by blast
  next
    case prems: (step_a_impl g a' r)
    let ?M =
      "And (reset' (And (curry M) (abstr g (\<lambda>i j. \<infinity>) v)) n r v 0) (abstr (inv_of A l') (\<lambda>i j. \<infinity>) v)"
    from prems *(1,3) numbering(2) collect_clks_inv_clk_set collect_clocks_clk_set reset_clk_set have
      "\<forall>c\<in>collect_clks (inv_of A l'). v c = c \<and> 0 < v c \<and> v c \<le> n"
      "\<forall>c\<in>collect_clks g. v c = c \<and> 0 < v c \<and> v c \<le> n"
      "\<forall>c\<in>set r. v c = c \<and> 0 < v c \<and> v c \<le> n"
    by fast+
    then have **:
      "\<forall>c\<in>collect_clks (inv_of A l'). v c = c \<and> 0 < c \<and> v c \<le> n"
      "\<forall>c\<in>collect_clks g. v c = c \<and> 0 < c \<and> v c \<le> n"
      "\<forall>c\<in>set r. v c = c \<and> 0 < c \<and> v c \<le> n"
      by fastforce+
    from prems action_step_impl_correct[OF canonical *(1) ** diag *(2)] have
      "[curry M']\<^bsub>v,n\<^esub> = [?M]\<^bsub>v,n\<^esub>"
      by (simp add: FW'_FW FW_zone_equiv[OF *(2), symmetric])
    moreover have
      "A \<turnstile> \<langle>l,curry M\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l',?M\<rangle>" unfolding \<open>a = _\<close> by - (intro step_z_norm step_a_z_dbm prems)
    ultimately show ?thesis by auto
  qed
qed

lemma step_impl_complete:
  assumes step: "A \<turnstile> \<langle>l,curry D\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l',curry D'\<rangle>"
  assumes canonical: "canonical (curry D) n"
  assumes numbering: "global_clock_numbering A v n" "\<forall> c \<in> clk_set A. v c = c"
  assumes diag: "\<forall>i\<le>n. D (i, i) \<le> 0"
  shows "\<exists> M'. A \<turnstile>\<^sub>I \<langle>l,D\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l',M'\<rangle> \<and> [curry M']\<^bsub>v,n\<^esub> = [curry D']\<^bsub>v,n\<^esub>"
proof -
  have *:
    "\<forall>c. 0 < v c \<and> (\<forall>x y. v x \<le> n \<and> v y \<le> n \<and> v x = v y \<longrightarrow> x = y)"
    "\<forall>k\<le>n. 0 < k \<longrightarrow> (\<exists>c. v c = k)" "\<forall>c\<in>clk_set A. v c \<le> n"
  using numbering by metis+
  from step show ?thesis
   apply cases
  proof goal_cases
    case prems: (1 D_inv)
    from *(1,3) numbering(2) collect_clks_inv_clk_set have
      "\<forall>c\<in>collect_clks (inv_of A l). v c = c \<and> 0 < v c \<and> v c \<le> n"
    by fast
    then have **:
      "\<forall>c\<in>collect_clks (inv_of A l). v c = c \<and> 0 < c \<and> v c \<le> n"
    by fastforce
    let ?D_inv = "abstr (inv_of A l) (\<lambda>i j. \<infinity>) v"
    let ?M' = "FW' (abstr_upd (inv_of A l) (up_canonical_upd D n)) n"
    have
      "[curry D']\<^bsub>v,n\<^esub> = [And (up (curry D)) ?D_inv]\<^bsub>v,n\<^esub>"
      by (simp only: prems)
    also from prems delay_step_impl_correct[OF canonical *(1) ** *(2)] have
      "\<dots> = [curry ?M']\<^bsub>v,n\<^esub>"
      by (simp only: FW'_FW FW_zone_equiv[OF *(2), symmetric])
    finally moreover have "A \<turnstile>\<^sub>I \<langle>l,D\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l',?M'\<rangle>" by (auto simp only: \<open>l' = l\<close> \<open>a = _\<close>)
    ultimately show ?thesis by auto
  next
    case prems: (2 g a' r)
    let ?M =
      "FW' (abstr_upd (inv_of A l') (reset'_upd (FW' (abstr_upd g D) n) n r 0)) n"
    from prems *(1,3) numbering(2) collect_clks_inv_clk_set collect_clocks_clk_set reset_clk_set have
      "\<forall>c\<in>collect_clks (inv_of A l'). v c = c \<and> 0 < v c \<and> v c \<le> n"
      "\<forall>c\<in>collect_clks g. v c = c \<and> 0 < v c \<and> v c \<le> n"
      "\<forall>c\<in>set r. v c = c \<and> 0 < v c \<and> v c \<le> n"
    by fast+
    then have **:
      "\<forall>c\<in>collect_clks (inv_of A l'). v c = c \<and> 0 < c \<and> v c \<le> n"
      "\<forall>c\<in>collect_clks g. v c = c \<and> 0 < c \<and> v c \<le> n"
      "\<forall>c\<in>set r. v c = c \<and> 0 < c \<and> v c \<le> n"
    by fastforce+
    from prems action_step_impl_correct[OF canonical *(1) ** diag *(2)] have
      "[curry D']\<^bsub>v,n\<^esub> = [curry ?M]\<^bsub>v,n\<^esub>"
    by (simp only: FW'_FW FW_zone_equiv[OF *(2), symmetric])
    moreover have "A \<turnstile>\<^sub>I \<langle>l,D\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l',?M\<rangle>" using prems by auto
    ultimately show ?thesis by auto
  qed
qed


section \<open>Reachability Checker\<close>

abbreviation conv_M :: "int DBM' \<Rightarrow> real DBM'" where "conv_M \<equiv> (o) (map_DBMEntry real_of_int)"

abbreviation conv_ac :: "('a, int) acconstraint \<Rightarrow> ('a, real) acconstraint" where
  "conv_ac \<equiv> map_acconstraint id real_of_int"

abbreviation conv_cc :: "('a, int) cconstraint \<Rightarrow> ('a, real) cconstraint" where
  "conv_cc \<equiv> map (map_acconstraint id real_of_int)"

abbreviation "conv_t \<equiv> \<lambda> (l,g,a,r,l'). (l,conv_cc g,a,r,l')"

definition "conv_A \<equiv> \<lambda> (T, I). (conv_t ` T, conv_cc o I)"

lemma RI_zone_equiv:
  assumes "RI n M M'"
  shows "[curry M]\<^bsub>v,n\<^esub> = [curry (conv_M M')]\<^bsub>v,n\<^esub>"
using assms unfolding DBM_zone_repr_def DBM_val_bounded_def rel_fun_def eq_onp_def
 apply clarsimp
 apply safe
 apply (cases "M (0, 0)"; cases "M' (0, 0)"; fastforce simp: dbm_le_def ri_def; fail)
 subgoal for _ c by (force intro: dbm_entry_val_ri[of "M (0, v c)"])
 subgoal for _ c by (force intro: dbm_entry_val_ri[of "M (v c, 0)"])
 subgoal for _ c1 c2 by (force intro: dbm_entry_val_ri[of "M (v c1, v c2)"])
 apply (cases "M (0, 0)"; cases "M' (0, 0)"; fastforce simp: dbm_le_def ri_def; fail)
 subgoal for _c by (rule dbm_entry_val_ir[of "M (0, v c)"]; auto)
 subgoal for _ c by (rule dbm_entry_val_ir[of "M (v c, 0)"]; auto)
 subgoal for _ c1 c2 by (rule dbm_entry_val_ir[of "M (v c1, v c2)"]; auto)
done

(* XXX Unused *)
locale unused
begin

lemma conv_abstra_upd:
  "conv_M (abstra_upd ac M) = abstra_upd (conv_ac ac) (conv_M M)"
apply (intro ext)
apply safe
apply (cases ac)

apply auto[]
apply (auto split: split_min)[]
apply (auto dest: conv_dbm_entry_mono)[]
apply (drule not_le_imp_less)
apply (auto dest: conv_dbm_entry_mono_strict)[]

apply (auto split: split_min)[]
apply (auto dest: conv_dbm_entry_mono)[]
apply (drule not_le_imp_less)
apply (auto dest: conv_dbm_entry_mono_strict)[]

apply auto[]
apply (auto split: split_min)[]
apply (auto dest: conv_dbm_entry_mono)[]
apply (drule not_le_imp_less)
apply (auto dest: conv_dbm_entry_mono_strict)[]

apply (auto split: split_min)[]
apply (auto dest: conv_dbm_entry_mono)[]
apply (drule not_le_imp_less)
apply (auto dest: conv_dbm_entry_mono_strict)[]

apply (auto split: split_min)[]
apply (auto dest: conv_dbm_entry_mono)[]
apply (drule not_le_imp_less)
apply (auto dest: conv_dbm_entry_mono_strict)[]

apply (auto split: split_min)[]
apply (auto dest: conv_dbm_entry_mono)[]
apply (drule not_le_imp_less)
apply (auto dest: conv_dbm_entry_mono_strict)[]

apply (auto split: split_min)[]
apply (auto dest: conv_dbm_entry_mono)[]
apply (drule not_le_imp_less)
apply (auto dest: conv_dbm_entry_mono_strict)[]

apply (auto split: split_min)[]
apply (auto dest: conv_dbm_entry_mono)[]
apply (drule not_le_imp_less)
apply (auto dest: conv_dbm_entry_mono_strict)[]
done

(* XXX Unused *)
lemma conv_M_abstr_upd:
  "conv_M (abstr_upd cc M) = abstr_upd (conv_cc cc) (conv_M M)"
by (induction cc arbitrary: M) (auto simp: abstr_upd_def conv_abstra_upd)

end (* End unused *)

lemma collect_clkvt_conv_A:
  "collect_clkvt (trans_of A) = collect_clkvt (trans_of (conv_A A))"
proof -
  obtain T I where "A = (T, I)" by force
  have "collect_clkvt (trans_of A) = \<Union>((set o fst \<circ> snd \<circ> snd \<circ> snd) ` T)"
  unfolding collect_clkvt_alt_def \<open>A = _\<close> trans_of_def by simp
  also have
    "\<dots>= \<Union>((set o fst \<circ> snd \<circ> snd \<circ> snd) ` (\<lambda>(l, g, a, r, l'). (l, map conv_ac g, a, r, l')) ` T)"
  by auto
  also have "\<dots> = collect_clkvt ((\<lambda>(l, g, a, r, l'). (l, map conv_ac g, a, r, l')) ` T)"
  unfolding collect_clkvt_alt_def[symmetric] ..
  also have "\<dots> = collect_clkvt (trans_of (conv_A A))" unfolding \<open>A = _\<close> trans_of_def
    by (simp add: conv_A_def)
  finally show ?thesis .
qed

lemma conv_ac_clock_id:
  "constraint_pair (conv_ac ac) = (\<lambda> (a, b). (a, real_of_int b)) (constraint_pair ac)"
by (cases ac) auto

lemma collect_clock_pairs_conv_cc:
  "collect_clock_pairs (map conv_ac cc) = (\<lambda> (a, b). (a, real_of_int b)) ` collect_clock_pairs cc"
by (auto simp: conv_ac_clock_id collect_clock_pairs_def) (metis conv_ac_clock_id image_eqI prod.simps(2))

lemma collect_clock_pairs_conv_cc':
  fixes S :: "('a, int) acconstraint list set"
  shows
    "(collect_clock_pairs ` map conv_ac ` S)
    = (((`) (\<lambda> (a, b). (a, real_of_int b))) ` collect_clock_pairs ` S)"
 apply safe
 apply (auto simp: collect_clock_pairs_conv_cc; fail)
by (auto simp: collect_clock_pairs_conv_cc[symmetric])

lemma collect_clock_pairs_conv_cc'':
  fixes S :: "('a, int) acconstraint list set"
  shows "(\<Union>x\<in>collect_clock_pairs ` map conv_ac ` S. x) = (\<Union>x\<in>collect_clock_pairs ` S. (\<lambda> (a, b). (a, real_of_int b)) ` x)"
by (simp add: collect_clock_pairs_conv_cc')

lemma clkp_set_conv_A:
  "clkp_set (conv_A A) l = (\<lambda> (a, b). (a, real_of_int b)) ` clkp_set A l"
  unfolding clkp_set_def collect_clki_def collect_clkt_alt_def inv_of_def trans_of_def conv_A_def
  apply (simp only: image_Un image_Union split: prod.split)
  by (auto simp: collect_clock_pairs_conv_cc' collect_clock_pairs_conv_cc[symmetric])

lemma ta_clkp_set_conv_A:
  "Timed_Automata.clkp_set (conv_A A) = (\<lambda> (a, b). (a, real_of_int b)) ` Timed_Automata.clkp_set A"
 apply (simp split: prod.split add: conv_A_def)
 unfolding
   Timed_Automata.clkp_set_def ta_collect_clki_alt_def ta_collect_clkt_alt_def inv_of_def trans_of_def
 apply (simp only: image_Un image_Union)
 apply (subst collect_clock_pairs_conv_cc''[symmetric])
 apply (subst collect_clock_pairs_conv_cc''[symmetric])
 by fastforce

lemma clkp_set_conv_A':
  "fst ` Timed_Automata.clkp_set A = fst ` Timed_Automata.clkp_set (conv_A A)"
by (fastforce simp: ta_clkp_set_conv_A)

lemma clk_set_conv_A:
  "clk_set (conv_A A) = clk_set A"
  unfolding collect_clkvt_conv_A clkp_set_conv_A' ..

lemma global_clock_numbering_conv:
  assumes "global_clock_numbering A v n"
  shows "global_clock_numbering (conv_A A) v n"
using assms clk_set_conv_A by metis

lemma real_of_int_nat:
  assumes "a \<in> \<nat>"
  shows "real_of_int a \<in> \<nat>"
using assms by (metis Nats_cases of_int_of_nat_eq of_nat_in_Nats)

lemma valid_abstraction_conv':
  assumes "Timed_Automata.valid_abstraction A X' k"
  shows "Timed_Automata.valid_abstraction (conv_A A) X' (\<lambda> x. real (k x))"
  using assms
  apply cases
  apply (rule Timed_Automata.valid_abstraction.intros)
    apply (auto intro: real_of_int_nat simp: ta_clkp_set_conv_A; fail)
  using collect_clkvt_conv_A apply fast
  by assumption

lemma valid_abstraction_conv:
  assumes "valid_abstraction A X' k"
  shows "valid_abstraction (conv_A A) X' (\<lambda> l x. real (k l x))"
  using assms
  apply cases
  apply (rule valid_abstraction.intros)
     apply (auto 4 3 simp: clkp_set_conv_A intro: real_of_int_nat; fail)
  using collect_clkvt_conv_A apply fast
  by (auto split: prod.split_asm simp: trans_of_def conv_A_def)

text \<open>Misc\<close>

lemma map_nth:
  fixes m :: nat
  assumes "i \<le> m"
  shows "map f [0..<Suc m] ! i = f i"
  using assms
by (metis add.left_neutral diff_zero le_imp_less_Suc nth_map_upt)

lemma ints_real_of_int_ex:
  assumes "z \<in> \<int>"
  shows "\<exists>n. z = real_of_int n"
using assms Ints_cases by auto

lemma collect_clock_pairs_trans_clkp_set:
  assumes "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"
  shows "collect_clock_pairs g \<subseteq> Timed_Automata.clkp_set A"
using assms unfolding Timed_Automata.clkp_set_def Timed_Automata.collect_clkt_def by force

lemma collect_clock_pairs_inv_clkp_set:
  "collect_clock_pairs (inv_of A l) \<subseteq> Timed_Automata.clkp_set A"
unfolding Timed_Automata.clkp_set_def Timed_Automata.collect_clki_def by force

lemma finite_collect_clock_pairs[intro, simp]:
  "finite (collect_clock_pairs x)"
unfolding collect_clock_pairs_def by auto

lemma finite_collect_clks[intro, simp]:
  "finite (collect_clks x)"
unfolding collect_clks_def by auto

(* XXX Better name? *)
lemma check_diag_subset:
  assumes "\<not> check_diag n D" "dbm_subset n D M"
  shows "\<not> check_diag n M"
using assms unfolding dbm_subset_def check_diag_def pointwise_cmp_def by fastforce

(* XXX Unused *)
lemma dbm_int_dbm_default_convD:
  assumes "dbm_int M n" "dbm_default M n"
  shows "\<exists> M'. curry (conv_M M') = M"
proof -
  let ?unconv = "(o) (map_DBMEntry floor)"
  let ?M' = "?unconv (uncurry M)"
  show ?thesis
   apply (rule exI[where x = ?M'])
   using assms apply (intro ext)
   apply clarsimp
   subgoal for i j
   by (cases "M i j"; cases "i > n"; cases "j > n";
       fastforce dest!: leI intro: ints_real_of_int_ex simp: neutral
     )
  done
qed

(* XXX Unused *)
lemma dbm_int_all_convD:
  assumes "dbm_int_all M"
  shows "\<exists> M'. curry (conv_M M') = M"
proof -
  let ?unconv = "(o) (map_DBMEntry floor)"
  let ?M' = "?unconv (uncurry M)"
  show ?thesis
   apply (rule exI[where x = ?M'])
   using assms apply (intro ext)
   apply clarsimp
   subgoal for i j
    apply (cases "M i j")
    apply (auto intro!: ints_real_of_int_ex simp: neutral)
    subgoal premises prems for d
    proof -
      from prems(2) have "M i j \<noteq> \<infinity>" by auto
      with prems show ?thesis by fastforce
    qed
    subgoal premises prems for d
    proof -
       from prems(2) have "M i j \<noteq> \<infinity>" by auto
       with prems show ?thesis by fastforce
    qed
    done
  done
qed

lemma acri'_conv_ac:
  assumes "fst (constraint_pair ac) < Suc n"
  shows "acri' n (conv_ac ac) ac"
using assms
by (cases ac) (auto simp: ri_def eq_onp_def)

lemma ri_conv_cc:
  assumes "\<forall> c \<in> fst ` collect_clock_pairs cc. c < Suc n"
  shows "(list_all2 (acri' n)) (conv_cc cc) cc"
using assms
apply -
apply (rule list_all2I)
apply safe
subgoal premises prems for a b
proof -
  from prems(2) have "a = conv_ac b" by (metis in_set_zip nth_map prod.sel(1) prod.sel(2))
  moreover from prems(1,2) have
    "fst (constraint_pair b) < Suc n"
  unfolding collect_clock_pairs_def by simp (meson set_zip_rightD)
  ultimately show ?thesis by (simp add: acri'_conv_ac)
qed
by simp

lemma canonical_conv_aux:
  assumes "a \<le> b + c"
  shows "map_DBMEntry real_of_int a \<le> map_DBMEntry real_of_int b + map_DBMEntry real_of_int c"
  using assms unfolding less_eq add dbm_le_def
  by (cases a; cases b; cases c) (auto elim!: dbm_lt.cases)

lemma canonical_conv_aux_rev:
  assumes "map_DBMEntry real_of_int a \<le> map_DBMEntry real_of_int b + map_DBMEntry real_of_int c"
  shows "a \<le> b + c"
  using assms unfolding less_eq add dbm_le_def
  by (cases a; cases b; cases c) (auto elim!: dbm_lt.cases)

(* XXX Unused *)
lemma canonical_conv:
  assumes "canonical (curry M) n"
  shows "canonical (curry (conv_M M)) n"
  using assms by (auto intro: canonical_conv_aux)

lemma canonical_conv_rev:
  assumes "canonical (curry (conv_M M)) n"
  shows "canonical (curry M) n"
  using assms by (auto intro: canonical_conv_aux_rev)

lemma canonical_RI_aux1:
  assumes "rel_DBMEntry ri a1 b1" "rel_DBMEntry ri a2 b2" "rel_DBMEntry ri a3 b3" "a1 \<le> a2 + a3"
  shows "b1 \<le> b2 + b3"
  using assms unfolding ri_def less_eq add dbm_le_def
  by (cases a1; cases a2; cases a3; cases b1; cases b2; cases b3) (auto elim!: dbm_lt.cases)

lemma canonical_RI_aux2:
  assumes "rel_DBMEntry ri a1 b1" "rel_DBMEntry ri a2 b2" "rel_DBMEntry ri a3 b3" "b1 \<le> b2 + b3"
  shows "a1 \<le> a2 + a3"
  using assms unfolding ri_def less_eq add dbm_le_def
  by (cases a1; cases a2; cases a3; cases b1; cases b2; cases b3) (auto elim!: dbm_lt.cases)

lemma canonical_RI:
  assumes "RI n D M"
  shows "canonical (curry D) n = canonical (curry M) n"
  using assms unfolding rel_fun_def eq_onp_def
  apply safe
  subgoal for i j k
    by (rule canonical_RI_aux1[of "D (i, k)" _ "D (i, j)" _ "D (j, k)"]; auto)
  subgoal for i j k
    by (rule canonical_RI_aux2[of _ "M (i, k)" _ "M (i, j)" _ "M (j, k)"]; auto)
  done

lemma RI_conv_M[transfer_rule]:
  "(RI n) (conv_M M) M"
  by (auto simp: rel_fun_def DBMEntry.rel_map(1) ri_def eq_onp_def DBMEntry.rel_refl)

lemma canonical_conv_M_FW':
  "canonical (curry (conv_M (FW' M n))) n = canonical (curry (FW' (conv_M M) n)) n"
proof -
  have [transfer_rule]: "eq_onp (\<lambda>x. x = n) n n" by (simp add: eq_onp_def)
  note [transfer_rule] = RI_conv_M
  have 1: "RI n (FW' (conv_M M) n) (FW' M n)" by transfer_prover
  have 2: "RI n (conv_M (FW' M n)) (FW' M n)" by (rule RI_conv_M)
  from canonical_RI[OF 1] canonical_RI[OF 2] show ?thesis by simp
qed

lemma diag_conv:
  assumes "\<forall> i \<le> n. (curry M) i i \<le> 0"
  shows "\<forall> i \<le> n. (curry (conv_M M)) i i \<le> 0"
  using assms by (auto simp: neutral dest!: conv_dbm_entry_mono)

lemma map_DBMEntry_int_const:
  assumes "get_const (map_DBMEntry real_of_int a) \<in> \<int>"
  shows "get_const a \<in> \<int>"
  using assms by (cases a; auto simp: Ints_def)

lemma map_DBMEntry_not_inf:
  fixes a :: "_ DBMEntry"
  assumes "a \<noteq> \<infinity>"
  shows "map_DBMEntry real_of_int a \<noteq> \<infinity>"
  using assms by (cases a; auto simp: Ints_def)

lemma dbm_int_conv_rev:
  assumes "dbm_int (curry (conv_M Z)) n"
  shows "dbm_int (curry Z) n"
  using assms by (auto intro: map_DBMEntry_int_const dest: map_DBMEntry_not_inf)

lemma neutral_RI:
  assumes "rel_DBMEntry ri a b"
  shows "a \<ge> 0 \<longleftrightarrow> b \<ge> 0"
  using assms by (cases a; cases b; auto simp: neutral ri_def less_eq dbm_le_def elim!: dbm_lt.cases)

lemma diag_RI:
  assumes "RI n D M" "i \<le> n"
  shows "D (i, i) \<ge> 0 \<longleftrightarrow> M (i, i) \<ge> 0"
  using neutral_RI assms unfolding rel_fun_def eq_onp_def by auto

lemma diag_conv_M:
  assumes "i \<le> n"
  shows "curry (conv_M (FW' M n)) i i \<ge> 0 \<longleftrightarrow> curry (FW' (conv_M M) n) i i \<ge> 0"
proof -
  have [transfer_rule]: "eq_onp (\<lambda>x. x = n) n n" by (simp add: eq_onp_def)
  note [transfer_rule] = RI_conv_M
  have 1: "RI n (FW' (conv_M M) n) (FW' M n)" by transfer_prover
  have 2: "RI n (conv_M (FW' M n)) (FW' M n)" by (rule RI_conv_M)
  from \<open>i \<le> n\<close> diag_RI[OF 1] diag_RI[OF 2] show ?thesis by simp
qed

lemma conv_dbm_entry_mono_rev:
  assumes "map_DBMEntry real_of_int a \<le> map_DBMEntry real_of_int b"
  shows "a \<le> b"
  using assms
  apply (cases a; cases b)
          apply (auto simp: less_eq dbm_le_def)
     apply (cases rule: dbm_lt.cases, auto; fail)+
  done

lemma conv_dbm_entry_mono_strict_rev:
  assumes "map_DBMEntry real_of_int a < map_DBMEntry real_of_int b"
  shows "a < b"
  using assms
  apply (cases a; cases b)
          apply (auto simp: less)
     apply (cases rule: dbm_lt.cases, auto; fail)+
  done

lemma diag_conv_rev:
  assumes "\<forall> i \<le> n. (curry (conv_M M)) i i \<le> 0"
  shows "\<forall> i \<le> n. (curry M) i i \<le> 0"
  using assms by (simp add: conv_dbm_entry_mono_rev neutral)

lemma dbm_subset_conv:
  assumes "dbm_subset n D M"
  shows "dbm_subset n (conv_M D) (conv_M M)"
  using assms unfolding dbm_subset_def pointwise_cmp_def check_diag_def
  by (auto intro: conv_dbm_entry_mono dest!: conv_dbm_entry_mono_strict)

lemma dbm_subset_conv_rev:
  assumes "dbm_subset n (conv_M D) (conv_M M)"
  shows "dbm_subset n D M"
  using assms conv_dbm_entry_mono_strict_rev
  unfolding dbm_subset_def pointwise_cmp_def check_diag_def
  by (auto intro: conv_dbm_entry_mono_rev)

(* XXX Unused *)
lemma dbm_subset_correct:
  fixes D :: "real DBM'"
  assumes "dbm_subset n D M"
    and "canonical (curry D) n"
    and "\<forall>i\<le>n. (curry D) i i \<le> 0"
    and "\<forall>i\<le>n. (curry M) i i \<le> 0"
    and "global_clock_numbering A v n"
  shows "[curry D]\<^bsub>v,n\<^esub> \<subseteq> [curry M]\<^bsub>v,n\<^esub>"
  using assms
  apply (subst subset_eq_dbm_subset[where v= v and M' = M])
       apply (auto; fail)
      apply (auto; fail)
     apply (auto; fail)
  by blast+

lemma dbm_subset_correct':
  fixes D M :: "real DBM'"
  assumes "canonical (curry D) n \<or> check_diag n D"
    and "\<forall>i\<le>n. (curry D) i i \<le> 0"
    and "\<forall>i\<le>n. (curry M) i i \<le> 0"
    and "global_clock_numbering A v n"
  shows "[curry D]\<^bsub>v,n\<^esub> \<subseteq> [curry M]\<^bsub>v,n\<^esub> \<longleftrightarrow> dbm_subset n D M"
  using assms
  apply -
  apply (rule subset_eq_dbm_subset[OF assms(1)])
     apply (auto; fail)
    apply (auto; fail)
  by blast+

lemma step_z_dbm_diag_preservation:
  assumes "step_z_dbm A l D v n a l' D'" "\<forall> i \<le> n. D i i \<le> 0"
  shows "\<forall> i \<le> n. D' i i \<le> 0"
  using assms
  apply cases
  using And_diag1 up_diag_preservation apply blast
  by (metis And_diag1 order_mono_setup.refl reset'_diag_preservation)

(* XXX Move? *)
context AlphaClosure
begin

lemma step_z_dbm_mono:
  "\<exists> D'. A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', D'\<rangle> \<and> [M']\<^bsub>v,n\<^esub> \<subseteq> [D']\<^bsub>v,n\<^esub>" if
  gcn: "global_clock_numbering A v n" and that: "A \<turnstile> \<langle>l, M\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', M'\<rangle>" "[M]\<^bsub>v,n\<^esub> \<subseteq> [D]\<^bsub>v,n\<^esub>"
  using step_z_mono[of A] step_z_dbm_sound[OF _ gcn] step_z_dbm_DBM[OF _ gcn] that by metis

end

(* XXX Move *)
lemma FW_canonical:
  "canonical (FW M n) n \<or> (\<exists> i \<le> n. (FW M n) i i < 0)"
  using FW_canonical' leI by blast

lemma FW'_canonical:
  "canonical (curry (FW' M n)) n \<or> (\<exists> i \<le> n. (FW' M n) (i, i) < 0)"
  by (metis FW'_FW FW_canonical curry_def)

lemma fw_upd_conv_M'':
  "fw_upd (map_DBMEntry real_of_int \<circ>\<circ> M) k i j = map_DBMEntry real_of_int \<circ>\<circ> fw_upd M k i j"
  unfolding fw_upd_def Floyd_Warshall.upd_def
  by (rule ext; simp split: prod.split; cases "M i j"; cases "M i k"; cases "M k j")
     (force simp: add min_def | force simp: min_inf_r | force simp: min_inf_l)+

lemma fw_upd_conv_M':
  "conv_M (uncurry (fw_upd M k i j)) = uncurry (fw_upd (map_DBMEntry real_of_int \<circ>\<circ> M) k i j)"
  unfolding fw_upd_conv_M'' by auto

lemma fw_upd_conv_M:
  "uncurry (fw_upd (curry (conv_M (uncurry M))) h i j)
  = (map_DBMEntry real_of_int \<circ>\<circ> uncurry) (fw_upd M h i j)"
  unfolding fw_upd_conv_M' by (auto simp: curry_def comp_def)

lemma fwi_conv_M'':
  "map_DBMEntry real_of_int \<circ>\<circ> fwi M n k i j = fwi (map_DBMEntry real_of_int \<circ>\<circ> M) n k i j"
  apply (induction _ "(i, j)" arbitrary: i j
    rule: wf_induct[of "less_than <*lex*> less_than"]
  )
  apply (auto; fail)
  subgoal for i j
    by (cases i; cases j; auto simp add: fw_upd_conv_M''[symmetric])
  done

lemma fwi_conv_M':
  "conv_M (uncurry (fwi M n k i j)) = uncurry (fwi (map_DBMEntry real_of_int \<circ>\<circ> M) n k i j)"
  unfolding fwi_conv_M''[symmetric] by auto

lemma fwi_conv_M:
  "conv_M (uncurry (fwi (curry M) n k i j)) = uncurry (fwi (curry (conv_M M)) n k i j)"
  unfolding fwi_conv_M' by (auto simp: curry_def comp_def)

lemma fw_conv_M'':
  "map_DBMEntry real_of_int \<circ>\<circ> fw M n k = fw (map_DBMEntry real_of_int \<circ>\<circ> M) n k"
  by (induction k; simp only: fw.simps fwi_conv_M'')

lemma fw_conv_M':
  "conv_M (uncurry (fw M n k)) = uncurry (fw (map_DBMEntry real_of_int \<circ>\<circ> M) n k)"
  unfolding fw_conv_M''[symmetric] by auto

lemma fw_conv_M:
  "conv_M (uncurry (fw (curry M) n k)) = uncurry (fw (curry (conv_M M)) n k)"
  unfolding fw_conv_M' by (auto simp: curry_def comp_def)

lemma FW_conv_M:
  "uncurry (FW (curry (conv_M M)) n) = conv_M (uncurry (FW (curry M) n))"
  using fw_conv_M by metis

lemma FW'_conv_M:
  "FW' (conv_M M) n = conv_M (FW' M n)"
  using FW_conv_M unfolding FW'_def by simp

lemma (in Regions) v_v':
  "\<forall> c \<in> X. v' (v c) = c"
  using clock_numbering unfolding v'_def by auto

definition
  "subsumes n
  = (\<lambda> (l, M) (l', M'). check_diag n M \<or> l = l' \<and> pointwise_cmp (\<le>) n (curry M) (curry M'))"

lemma subsumes_simp_1:
  "subsumes n (l, M) (l', M') = dbm_subset n M M'" if "l = l'"
  using that unfolding subsumes_def dbm_subset_def by simp

lemma subsumes_simp_2:
  "subsumes n (l, M) (l', M') = check_diag n M" if "l \<noteq> l'"
  using that unfolding subsumes_def dbm_subset_def by simp


lemma TA_clkp_set_unfold:
  "Timed_Automata.clkp_set A = \<Union> (clkp_set A ` UNIV)"
  unfolding clkp_set_def Timed_Automata.clkp_set_def
  unfolding Timed_Automata.collect_clki_def Timed_Automata.collect_clkt_def
  unfolding collect_clki_def collect_clkt_def
  by blast

locale TA_Start_No_Ceiling_Defs =
  fixes A :: "('a, nat, int, 's) ta"
    and l\<^sub>0 :: 's
    and n :: nat
begin

definition "X \<equiv> {1..n}"

(* Tailored towards the needs of the specific implementation semantics *)
definition "v i \<equiv> if i > 0 \<and> i \<le> n then i else (Suc n)"
definition "x \<equiv> SOME x. x \<notin> X"

definition "a\<^sub>0 = (l\<^sub>0, init_dbm)"

abbreviation
  "canonical' D \<equiv> canonical (curry D) n"

abbreviation
  "canonical_diag' D \<equiv> canonical' D \<or> check_diag n D"

abbreviation
  "canonical_diag D \<equiv> canonical' (conv_M D) \<or> check_diag n D"

abbreviation
  "canonical_subs' I M \<equiv> canonical_subs n I (curry M)"

definition "locations \<equiv> {l\<^sub>0} \<union> fst ` trans_of A \<union> (snd o snd o snd o snd) ` trans_of A"

lemma X_alt_def:
  "X = {1..<Suc n}"
  unfolding X_def by auto

lemma v_bij:
  "bij_betw v {1..<Suc n} {1..n}"
  unfolding v_def[abs_def] bij_betw_def inj_on_def by auto

lemma triv_numbering:
  "\<forall> i \<in> {1..n}. v i = i"
  unfolding v_def by auto

lemma canonical_diagI:
  "canonical_diag D"  if "canonical_diag' D"
  using that canonical_conv by auto

(* This used (by used theorems) *)
lemma v_id:
  "v c = c" if "v c \<le> n"
  by (metis Suc_n_not_le_n that v_def)

end


locale TA_Start_No_Ceiling = TA_Start_No_Ceiling_Defs +
  assumes finite_trans[intro, simp]: "finite (trans_of A)"
      and finite_inv[intro]: "finite (range (inv_of A))"
      and clocks_n: "clk_set A \<subseteq> {1..n}"
      and consts_nats: "\<forall>(_, d) \<in> Timed_Automata.clkp_set A. d \<in> \<nat>"
      and n_gt0[intro, simp]: "n > 0"
begin

lemma clock_range:
  "\<forall>c\<in>clk_set A. c \<le> n \<and> c \<noteq> 0"
  using clocks_n by force

lemma clk_set_X:
  "clk_set A \<subseteq> X"
  unfolding X_def using clocks_n .

lemma finite_X:
  "finite X"
  unfolding X_def by (metis finite_atLeastAtMost)

lemma finite_clkp_set_A[intro, simp]:
  "finite (Timed_Automata.clkp_set A)"
  unfolding Timed_Automata.clkp_set_def ta_collect_clkt_alt_def ta_collect_clki_alt_def by fast

lemma finite_collect_clkvt[intro]:
  "finite (collect_clkvt (trans_of A))"
  unfolding collect_clkvt_def using [[simproc add: finite_Collect]] by auto

lemma consts_ints:
  "\<forall>(_, d) \<in> Timed_Automata.clkp_set A. d \<in> \<int>"
  using consts_nats unfolding Nats_def by auto

lemma n_bounded:
  "\<forall> c \<in> X. c \<le> n"
  unfolding X_def by auto

lemma finite_locations:
  "finite locations"
  unfolding locations_def using finite_trans by auto

lemma RI_I_conv_cc:
  "RI_I n (conv_cc o snd A) (snd A)"
  using clocks_n
  unfolding RI_I_def rel_fun_def Timed_Automata.clkp_set_def ta_collect_clki_alt_def inv_of_def
  by (force intro: ri_conv_cc)

lemma triv_numbering':
  "\<forall> c \<in> clk_set A. v c = c"
  using triv_numbering clocks_n by auto

lemma triv_numbering'':
  "\<forall> c \<in> clk_set (conv_A A). v c = c"
  using triv_numbering' unfolding clk_set_conv_A .

lemma global_clock_numbering:
  "global_clock_numbering A v n"
  using clocks_n unfolding v_def by auto

lemmas global_clock_numbering' = global_clock_numbering_conv[OF global_clock_numbering]

lemma ri_conv_t:
  assumes "t \<in> fst A"
  shows "(RI_T n) (conv_t t) t"
  unfolding RI_T_def apply (auto split: prod.split)
   apply (rule ri_conv_cc)
  using assms clocks_n unfolding Timed_Automata.clkp_set_def ta_collect_clkt_alt_def trans_of_def
   apply fastforce
  using assms using clocks_n unfolding clkp_set_def collect_clkvt_alt_def trans_of_def eq_onp_def
  by (fastforce intro: list_all2I simp: zip_same)

lemma RI_T_conv_t:
  "rel_set (RI_T n) (conv_t ` fst A) (fst A)"
  using ri_conv_t unfolding rel_set_def by (fastforce split: prod.split)

lemma RI_A_conv_A:
  "RI_A n (conv_A A) A"
  using RI_T_conv_t RI_I_conv_cc unfolding RI_A_def conv_A_def by (auto split: prod.split)

lemma step_impl_diag_preservation:
  assumes step: "A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l', M'\<rangle>"
    and diag: "\<forall> i \<le> n. (curry M) i i \<le> 0"
  shows
    "\<forall> i \<le> n. (curry M') i i \<le> 0"
proof -
  have FW':
    "(FW' M n) (i, i) \<le> 0" if "i \<le> n" "\<forall> i \<le> n. M (i, i) \<le> 0" for i and M :: "int DBM'"
    using that FW'_diag_preservation[OF that(2)] diag by auto
  have *:
    "\<forall> c \<in> collect_clks (inv_of A l). c \<noteq> 0"
    using clock_range collect_clks_inv_clk_set[of A l] by auto
  from step diag * show ?thesis
    apply cases

    subgoal \<comment> \<open>delay step\<close>
      apply simp
      apply (rule FW'_diag_preservation)
      apply (rule abstr_upd_diag_preservation')
       apply (subst up_canonical_upd_diag_preservation)
      by auto

    subgoal \<comment> \<open>action step\<close>
      apply simp
      apply (rule FW'_diag_preservation)
      apply (rule abstr_upd_diag_preservation')
       apply (standard, standard)
       apply (subst reset'_upd_diag_preservation)
         defer
         apply assumption
        apply (erule FW')
        apply (erule abstr_upd_diag_preservation')
        apply (metis (no_types) clock_range collect_clocks_clk_set subsetCE)
       apply (metis (no_types) clock_range collect_clks_inv_clk_set subsetCE)
      apply (drule reset_clk_set)
      using clock_range by blast
    done
qed

lemma step_impl_neg_diag_preservation:
  assumes step: "A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l', M'\<rangle>"
    and le: "i \<le> n"
    and diag: "(curry M) i i < 0"
  shows "(curry M') i i < 0"
  using assms
  apply cases

  subgoal \<comment> \<open>delay step\<close>
    apply simp
    apply (rule FW'_neg_diag_preservation)
     apply (subst abstr_upd_diag_preservation)
       apply assumption
      apply (metis (no_types) clock_range collect_clks_inv_clk_set subsetCE)
     apply (subst up_canonical_upd_diag_preservation)
    by auto

  subgoal \<comment> \<open>action step\<close>
    apply simp
    apply (rule FW'_neg_diag_preservation)
     apply (subst abstr_upd_diag_preservation)
       apply assumption
      apply (metis (no_types) clock_range collect_clks_inv_clk_set subsetCE)
     apply (subst reset'_upd_diag_preservation)
      defer
      apply assumption
     apply (rule FW'_neg_diag_preservation)
      apply (subst abstr_upd_diag_preservation)
        apply assumption
       apply (metis (no_types) clock_range collect_clocks_clk_set subsetCE)
      apply assumption+
    apply (drule reset_clk_set)
    using clock_range by blast
  done

lemma step_impl_canonical:
  assumes step: "A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l', M'\<rangle>"
    and diag: "\<forall> i \<le> n. (curry M) i i \<le> 0"
  shows
    "canonical (curry (conv_M M')) n \<or> (\<exists> i \<le> n. M' (i, i) < 0)"
proof -
  from step_impl_diag_preservation[OF assms] have diag: "\<forall>i\<le>n. curry M' i i \<le> 0" .
  from step obtain M'' where "M' = FW' M'' n" by cases auto
  show ?thesis
  proof (cases "\<exists> i \<le> n. M' (i, i) < 0")
    case True
    then show ?thesis by auto
  next
    case False
    with diag have "\<forall>i\<le>n. curry M' i i \<ge> 0" by auto
    then have
      "\<forall>i\<le>n. curry (conv_M M') i i \<ge> 0"
      unfolding neutral by (auto dest!: conv_dbm_entry_mono)
    with FW_canonical'[of n "curry (conv_M M'')"] canonical_conv_M_FW' diag_conv_M show ?thesis
      unfolding \<open>M' = _\<close> FW'_FW[symmetric] canonical_conv_M_FW' by auto
  qed
qed

lemma step_impl_int_preservation:
  assumes step: "A \<turnstile>\<^sub>I \<langle>l,D\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l',D'\<rangle>"
    and  int: "dbm_int (curry D) n"
  shows "dbm_int (curry D') n"
  using assms
  apply cases

  subgoal premises prems
    unfolding prems
    apply (intro
        FW'_int_preservation norm_upd_int_preservation abstr_upd_int_preservation[rotated]
        up_canonical_upd_int_preservation
        )
    using consts_ints assms unfolding Timed_Automata.clkp_set_def Timed_Automata.collect_clki_def
    by auto

  subgoal premises prems
    unfolding prems
    apply (intro
        FW'_int_preservation norm_upd_int_preservation abstr_upd_int_preservation[rotated]
        reset'_upd_int_preservation
        )
    using assms prems(4) consts_ints collect_clock_pairs_inv_clkp_set[of A l']
        apply (auto dest!: collect_clock_pairs_trans_clkp_set)
    using prems(4) clock_range by (auto dest!: reset_clk_set)
  done

lemma check_diag_empty_spec:
  assumes "check_diag n M"
  shows "[curry M]\<^bsub>v,n\<^esub> = {}"
  apply (rule check_diag_empty)
  using assms global_clock_numbering by fast+

lemma init_dbm_semantics:
  assumes "u \<in> [curry (conv_M init_dbm)]\<^bsub>v,n\<^esub>" "0 < c" "c \<le> n"
  shows "u c = 0"
proof -
  from assms(2,3) have "v c \<le> n" unfolding v_def by auto
  with assms(1) show ?thesis unfolding DBM_zone_repr_def init_dbm_def DBM_val_bounded_def v_def
    by auto
qed

lemma dbm_int_conv:
  "dbm_int (curry (conv_M Z)) n"
  apply safe
  subgoal for i j
    by (cases "Z (i, j)") auto
  done

lemma RI_init_dbm:
  "RI n init_dbm init_dbm"
  unfolding init_dbm_def rel_fun_def ri_def by auto

lemma conv_M_init_dbm[simp]:
  "conv_M init_dbm = init_dbm"
  unfolding init_dbm_def by auto

lemmas
  step_z_dbm_equiv' = step_z_dbm_equiv[OF global_clock_numbering']

lemma step_impl_complete':
  assumes step: "step_z_dbm (conv_A A) l (curry (conv_M M)) v n a l' M'"
    and canonical: "canonical (curry (conv_M M)) n"
    and diag: "\<forall>i\<le>n. conv_M M (i, i) \<le> 0"
  shows "\<exists> D'. A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l', D'\<rangle> \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> = [M']\<^bsub>v,n\<^esub>"
proof -
  let ?A = "conv_A A"
  have A: "RI_A n ?A A" by (rule RI_A_conv_A)
  have M_conv: "RI n (conv_M M) M" unfolding eq_onp_def by auto
  let ?M' = "uncurry M'"
  from
    step_impl_complete[of ?A l "conv_M M" _ _ a _ ?M',
      OF _ canonical global_clock_numbering' triv_numbering'' diag
      ] step
  obtain M'' where M'':
    "?A \<turnstile>\<^sub>I \<langle>l, conv_M M\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l', M''\<rangle>" "[curry M'']\<^bsub>v,n\<^esub> = [curry ?M']\<^bsub>v,n\<^esub>"
    by auto
  from RI_complete[OF M_conv A this(1)] obtain MM where MM:
    "A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l', MM\<rangle>" "RI n M'' MM"
    by auto
  moreover from MM(2) M''(2) M''(2) have
    "[M']\<^bsub>v,n\<^esub> = [curry (conv_M MM)]\<^bsub>v,n\<^esub>"
    by (auto dest!: RI_zone_equiv[where v = v])
  ultimately show ?thesis by auto
qed

(* XXX Move? *)
lemma step_impl_check_diag:
  assumes "check_diag n M" "A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l', M'\<rangle>"
  shows "check_diag n M'"
  using step_impl_neg_diag_preservation assms unfolding check_diag_def neutral by auto

lemmas
  step_z_dbm_sound = step_z_dbm_sound[OF _ global_clock_numbering']

lemmas
  step_z_dbm_DBM = step_z_dbm_DBM[OF _ global_clock_numbering']

lemmas dbm_subset_correct' = dbm_subset_correct'[OF _ _ _ global_clock_numbering]

subsection \<open>Bisimilarity\<close>

definition dbm_equiv (infixr "\<simeq>" 60) where
  "dbm_equiv M M' \<equiv> [curry (conv_M M)]\<^bsub>v,n\<^esub> = [curry (conv_M M')]\<^bsub>v,n\<^esub>"

definition state_equiv (infixr "\<sim>" 60) where
  "state_equiv \<equiv> \<lambda> (l, M) (l', M'). l = l' \<and> M \<simeq> M'"

lemma dbm_equiv_trans[intro]:
  "a \<simeq> c" if "a \<simeq> b" "b \<simeq> c"
  using that unfolding dbm_equiv_def by simp

lemma state_equiv_trans[intro]:
  "a \<sim> c" if "a \<sim> b" "b \<sim> c"
  using that unfolding state_equiv_def by blast

lemma dbm_equiv_refl[intro]:
  "a \<simeq> a"
  unfolding dbm_equiv_def by simp

lemma state_equiv_refl[intro]:
  "a \<sim> a"
  unfolding state_equiv_def by blast

lemma dbm_equiv_sym:
  "a \<simeq> b" if "b \<simeq> a"
  using that unfolding dbm_equiv_def by simp

lemma state_equiv_sym:
  "a \<sim> b" if "b \<sim> a"
  using that unfolding state_equiv_def by (auto intro: dbm_equiv_sym)

lemma state_equiv_D:
  "M \<simeq> M'" if "(l, M) \<sim> (l', M')"
  using that unfolding state_equiv_def by auto


lemma finite_trans':
    "finite (trans_of (conv_A A))"
    using finite_trans unfolding trans_of_def conv_A_def by (cases A) auto

lemma init_dbm_semantics':
    assumes "u \<in> [(curry init_dbm :: real DBM)]\<^bsub>v,n\<^esub>"
    shows "\<forall> c \<in> {1..n}. u c = 0"
  using assms init_dbm_semantics by auto

  lemma init_dbm_semantics'':
    assumes "\<forall> c \<in> {1..n}. u c = 0"
    shows "u \<in> [(curry init_dbm :: real DBM)]\<^bsub>v,n\<^esub>"
  unfolding DBM_zone_repr_def DBM_val_bounded_def init_dbm_def using assms by (auto simp: v_def)

end (* TA Start No Ceiling *)


locale TA_Start_Defs =
  TA_Start_No_Ceiling_Defs A l\<^sub>0 n for A :: "('a, nat, int, 's) ta" and l\<^sub>0 n +
  fixes k :: "'s \<Rightarrow> nat \<Rightarrow> nat"
begin

definition "k' l \<equiv> map (int o k l) [0..<Suc n]"

definition "E = (\<lambda> (l, M) (l'', M''').
  \<exists> M' l' M'' a.
  A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l', M'\<rangle>
  \<and> A \<turnstile>\<^sub>I \<langle>l', M'\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a\<^esub> \<langle>l'', M''\<rangle>
  \<and> M''' = FW' (norm_upd M'' (k' l'') n) n)"

lemma E_alt_def: "E = (\<lambda> (l, M) (l', M''').
  \<exists> g a r M' M''.
  A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<and>
  M' = FW' (abstr_upd (inv_of A l) (up_canonical_upd M n)) n \<and>
  M'' = FW' (abstr_upd (inv_of A l') (reset'_upd (FW' (abstr_upd g M') n) n r 0)) n \<and>
  M''' = FW' (norm_upd M'' (k' l') n) n
  )"
  unfolding E_def by (force elim!: step_impl.cases)

  lemma length_k':
    "length (k' l) = Suc n"
  unfolding k'_def by auto

end


locale Reachability_Problem_No_Ceiling_Defs =
  TA_Start_No_Ceiling_Defs A l\<^sub>0 n for A :: "('a, nat, int, 's) ta" and l\<^sub>0 n+
  fixes F :: "'s \<Rightarrow> bool"
begin

definition "F_rel \<equiv> \<lambda> (l, M). F l \<and> \<not> check_diag n M"

end

(* locale Reachability_Problem_no_ceiling = TA_Start + Reachability_Problem_no_ceiling_Defs *)

locale Reachability_Problem_Defs = TA_Start_Defs + Reachability_Problem_No_Ceiling_Defs
begin

end (* Reachability Problem Defs *)

lemma check_diag_conv_M[intro]:
  assumes "check_diag n M"
  shows "check_diag n (conv_M M)"
  using assms unfolding check_diag_def by (auto dest!: conv_dbm_entry_mono_strict)

(* XXX Clean this *)
  lemma canonical_variant:
    "canonical (curry (conv_M D)) n \<or> check_diag n D
    \<longleftrightarrow> canonical (curry (conv_M D)) n \<or> (\<exists>i\<le>n. D (i, i) < 0)"
    unfolding check_diag_def neutral ..

locale TA_Start =
  TA_Start_No_Ceiling A l\<^sub>0 n +
  TA_Start_Defs A l\<^sub>0 n k for A :: "('a, nat, int, 's) ta" and l\<^sub>0 n k +
  assumes k_ceiling:
    "\<forall> l. \<forall>(x,m) \<in> clkp_set A l. m \<le> k l x"
    "\<forall> l g a r l' c. A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<and> c \<notin> set r \<longrightarrow> k l' c \<le> k l c"
  and k_bound: "\<forall> l. \<forall> i > n. k l i = 0"
  and k_0: "\<forall> l. k l 0 = 0"
begin

lemma E_closure:
  "E\<^sup>*\<^sup>* a\<^sub>0 (l', M') \<longleftrightarrow> A \<turnstile>\<^sub>I \<langle>l\<^sub>0, init_dbm\<rangle> \<leadsto>\<^bsub>k',n\<^esub>* \<langle>l', M'\<rangle>"
  unfolding a\<^sub>0_def E_def
  apply safe
   apply (drule rtranclp_induct[where P = "\<lambda> (l', M'). A \<turnstile>\<^sub>I \<langle>l\<^sub>0, init_dbm\<rangle> \<leadsto>\<^bsub>k',n\<^esub>* \<langle>l', M'\<rangle>"];
      auto dest: step intro: refl; fail
      )
  apply (induction rule: steps_impl.induct; simp add: rtranclp.intros(2))
  by (rule rtranclp.intros(2)) auto

lemma FW'_normalized_integral_dbms_finite':
  "finite {FW' (norm_upd M (k' l) n) n | M. dbm_default (curry M) n}"
  (is "finite ?S")
proof -
  let ?S' = "{norm_upd M (k' l) n | M. dbm_default (curry M) n}"
  have "finite ?S'"
    using normalized_integral_dbms_finite'[where k = "map (k l) [0..<Suc n]"] by (simp add: k'_def)
  moreover have "?S = (\<lambda> M. FW' M n) ` ?S'" by auto
  ultimately show ?thesis by auto
qed

lemma E_closure_finite:
  "finite {x. E\<^sup>*\<^sup>* a\<^sub>0 x}"
proof -
  have k': "map int (map (k l) [0..<Suc n]) = k' l" for l unfolding k'_def by auto
  have *: "(l, M) = a\<^sub>0 \<or> (\<exists>M'. M = FW' (norm_upd M' (k' l) n) n \<and> dbm_default (curry M') n)"
    if "E\<^sup>*\<^sup>* a\<^sub>0 (l, M)" for l M
    using that unfolding E_closure
    apply -
    apply (drule steps_impl_norm_dbm_default_dbm_int)
          apply (auto simp: init_dbm_def neutral)[]
         apply (auto simp: init_dbm_def)[]
        defer
        defer
        apply (simp add: k'_def; fail)
       apply (simp add: k'_def; fail)
      apply (simp add: a\<^sub>0_def)
    using clock_range consts_ints by (auto simp: X_def)
  moreover have **: "l \<in> locations" if "E\<^sup>*\<^sup>* a\<^sub>0 (l, M)" for l M
    using that unfolding E_closure locations_def
    apply (induction rule: steps_impl.induct)
     apply (simp; fail)
    by (force elim!: step_impl.cases)
  have
    "{x. E\<^sup>*\<^sup>* a\<^sub>0 x} \<subseteq>
        {a\<^sub>0} \<union> (locations \<times> {FW' (norm_upd M (k' l) n) n | l M. l \<in> locations \<and> dbm_default (curry M) n})"
    (is "_ \<subseteq> _ \<union> ?S")
    apply safe
     apply (rule **, assumption)
    apply (frule *)
    by (auto intro: **)
  moreover have "finite ?S"
    using FW'_normalized_integral_dbms_finite' finite_locations
    using [[simproc add: finite_Collect]]
    by (auto simp: k'_def finite_project_snd)
  ultimately show ?thesis by (auto intro: finite_subset)
qed

sublocale Regions "{1..<Suc n}" v n k "Suc n"
  apply standard
       apply (simp; fail)
  using default_numbering(2)[OF finite_X] apply (subst (asm) X_def) apply (simp add: v_def; fail)
  using default_numbering(2)[OF finite_X] apply (subst (asm) X_def) apply (simp add: v_def; fail)
  by (auto simp: v_def)

lemma k_simp_1:
  "(\<lambda> l i. if i \<le> n then map (k l) [0..<Suc n] ! i else 0) = k"
proof (rule ext)+
  fix l i
  show "(if i \<le> n then map (k l) [0..<Suc n] ! i else 0) = k l i"
  proof (cases "i \<le> n")
    case False
    with k_bound show ?thesis by auto
  next
    case True
    with map_nth[OF this] show ?thesis by auto
  qed
qed

lemma k_simp_2:
  "(\<lambda> l. k l \<circ> v') = k"
proof (rule ext)+
  fix l i
  show "(\<lambda> l. k l o v') l i = k l i"
  proof (cases "i > n")
    case True
    then show ?thesis unfolding v'_def by (auto simp: k_bound)
  next
    case False
    show ?thesis
    proof (cases "i = 0")
      case True
      with k_0 have "k l i = 0" by simp
      moreover have "v' 0 = Suc n" unfolding v'_def by auto
      ultimately show ?thesis using True by (auto simp: k_bound)
    next
      case False
      with \<open>\<not> n < i\<close> have "v' (v i) = i" using v_v' by auto
      moreover from False \<open>\<not> n < i\<close> triv_numbering have "v i = i" by auto
      ultimately show ?thesis by auto
    qed
  qed
qed

lemma valid_abstraction:
  "valid_abstraction A X k"
  using k_ceiling consts_nats clk_set_X unfolding X_def
  by (fastforce intro!: valid_abstraction.intros simp: TA_clkp_set_unfold)

lemma norm_upd_diag_preservation:
  assumes "i \<le> n" "M (i, i) \<le> 0"
  shows "(norm_upd M (k' l) n) (i, i) \<le> 0"
  apply (subst norm_upd_norm)
  apply (subst norm_k_cong[where k' = "k l"])
   apply (safe; simp only: k'_def map_nth; simp; fail)
  using norm_diag_preservation_int assms unfolding neutral by auto

lemma norm_upd_neg_diag_preservation:
  assumes "i \<le> n" "M (i, i) < 0"
  shows "(norm_upd M (k' l) n) (i, i) < 0"
  apply (subst norm_upd_norm)
  apply (subst norm_k_cong[where k' = "k l"])
   apply (safe; simp only: k'_def map_nth; simp; fail)
  using norm_empty_diag_preservation_int assms unfolding neutral by auto

lemmas valid_abstraction' = valid_abstraction_conv[OF valid_abstraction, unfolded X_alt_def]

lemma step_impl_V_preservation_canonical:
  assumes step: "A \<turnstile>\<^sub>I \<langle>l,D\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l',D'\<rangle>"
    and canonical: "canonical (curry (conv_M D)) n"
    and diag: "\<forall>i\<le>n. conv_M D (i, i) \<le> 0"
    and valid: "valid_dbm (curry (conv_M D))"
  shows "[curry (conv_M D')]\<^bsub>v,n\<^esub> \<subseteq> V"
proof -
  let ?A = "conv_A A"
  have A: "RI_A n ?A A" by (rule RI_A_conv_A)
  have "RI n (conv_M D) D" unfolding eq_onp_def by auto
  from IR_complete[OF this A step] obtain M' where M':
    "?A \<turnstile>\<^sub>I \<langle>l, conv_M D\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l', M'\<rangle>" "RI n M' D'"
    by auto
  from
    step_impl_sound[of ?A l "conv_M D",
      OF this(1) canonical global_clock_numbering' triv_numbering'' diag(1)
      ]
  obtain M'' where M'':
    "?A \<turnstile> \<langle>l, curry (conv_M D)\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', M''\<rangle>" "[curry M']\<^bsub>v,n\<^esub> = [M'']\<^bsub>v,n\<^esub>"
    by (auto simp add: k_simp_1)
  from step_z_valid_dbm[OF M''(1) global_clock_numbering' valid_abstraction'] valid have
    "valid_dbm M''"
    by auto
  then have "[M'']\<^bsub>v,n\<^esub> \<subseteq> V" by cases
  with M''(2) RI_zone_equiv[OF M'(2)] show ?thesis by auto
qed

lemma step_impl_V_preservation:
  assumes step: "A \<turnstile>\<^sub>I \<langle>l,D\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l',D'\<rangle>"
    and canonical: "canonical (curry (conv_M D)) n \<or> (\<exists>i\<le>n. D (i, i) < 0)"
    and diag: "\<forall>i\<le>n. conv_M D (i, i) \<le> 0"
    and valid: "valid_dbm (curry (conv_M D))"
  shows "[curry (conv_M D')]\<^bsub>v,n\<^esub> \<subseteq> V"
proof -
  from canonical show ?thesis
  proof (standard, goal_cases)
    case 1
    from step_impl_V_preservation_canonical[OF step this diag valid] show ?thesis .
  next
    case 2
    with step_impl_neg_diag_preservation[OF step] have "\<exists>i\<le>n. D' (i, i) < 0" by auto
    then have
      "[curry (conv_M D')]\<^bsub>v,n\<^esub> = {}"
      by - (rule check_diag_empty_spec;
          auto dest!: conv_dbm_entry_mono_strict simp: check_diag_def neutral
          )
    then show ?thesis by blast
  qed
qed

lemma norm_step_diag_preservation:
  "\<forall>i\<le>n. curry (FW' (norm_upd D (k' l) n) n) i i \<le> 0" if "\<forall>i\<le>n. (curry D) i i \<le> 0"
  by (metis FW'_diag_preservation curry_conv norm_upd_diag_preservation that)

lemma norm_step_check_diag_preservation:
  "check_diag n (FW' (norm_upd D (k' l) n) n)" if "check_diag n D"
  by (metis FW'_neg_diag_preservation check_diag_def neutral norm_upd_neg_diag_preservation that)

lemma diag_reachable:
  assumes "E\<^sup>*\<^sup>* a\<^sub>0 (l, M)"
  shows "\<forall> i \<le> n. (curry M) i i \<le> 0"
  using assms unfolding E_closure
  apply (induction Z \<equiv> "init_dbm :: int DBM'" _ _ _ _ rule: steps_impl_induct)
   apply (auto simp: init_dbm_def neutral; fail)
  apply (assumption | rule norm_step_diag_preservation step_impl_diag_preservation)+
  done

(* XXX Move all 'norm_step' lemmas somewhere else *)
lemma canonical_norm_step:
  "canonical (curry (conv_M (FW' (norm_upd M (k' l) n) n))) n
   \<or> (\<exists> i \<le> n. (FW' (norm_upd M (k' l) n) n) (i, i) < 0)"
  by (metis FW'_canonical canonical_conv)

lemma canonical_reachable:
  assumes "E\<^sup>*\<^sup>* a\<^sub>0 (l, M)"
  shows "canonical (curry (conv_M M)) n \<or> (\<exists>i \<le> n. M (i, i) < 0)"
  using assms unfolding E_closure
proof (induction l \<equiv> l\<^sub>0 Z \<equiv> "init_dbm :: int DBM'" _ _ _ _ rule: steps_impl_induct)
  case refl
  show ?case unfolding init_dbm_def by simp (simp add: neutral[symmetric])
next
  case step
  show ?case by (rule canonical_norm_step)
qed

lemma diag_reachable':
  assumes "E\<^sup>*\<^sup>* a\<^sub>0 (l, M)"
  shows "\<forall> i \<le> n. (curry (conv_M M)) i i \<le> 0"
  using diag_reachable[OF assms] by (auto simp: neutral dest!: conv_dbm_entry_mono)

context (* XXX Fix smt *)
    fixes l' :: 's
  begin

  interpretation regions: Regions_global "{1..<Suc n}" v n "k l'" "Suc n"
    by (standard; rule finite clock_numbering not_in_X non_empty)

  lemma v'_v'[simp]:
    "Regions.v' {1..<Suc n} v n (Suc n) = Beta_Regions'.v' {1..<Suc n} v n (Suc n)"
    unfolding v'_def regions.beta_interp.v'_def ..

  lemma k_simp_2': "(\<lambda> x. real ((k l' \<circ>\<circ>\<circ> Beta_Regions'.v' {1..<Suc n} v) n (Suc n) x)) = k l'"
    using k_simp_2 v'_v' by metis

  lemma norm_upd_V_preservation:
    "[curry (conv_M (norm_upd M (k' l') n))]\<^bsub>v,n\<^esub> \<subseteq> V"
    if "[curry (conv_M M)]\<^bsub>v,n\<^esub> \<subseteq> V" "canonical (curry (conv_M M)) n"
  proof -
    from regions.beta_interp.norm_V_preservation[OF that] have
      "[norm (curry (conv_M M)) (\<lambda> x. real (k l' x)) n]\<^bsub>v,n\<^esub> \<subseteq> V"
      by (simp only: k_simp_2')
    then have *: "[norm (curry (conv_M M)) ((!) (map real_of_int (k' l'))) n]\<^bsub>v,n\<^esub> \<subseteq> V"
      apply (subst norm_k_cong[of _ _ "(\<lambda> x. real (k l' x))"])
       apply safe
      (* s/h *)
      proof -
        fix i :: nat
        assume "i \<le> n"
        then have "map real_of_int (k' l') ! i = (real_of_int \<circ>\<circ>\<circ> (\<circ>)) int (k l') i"
          by (metis (no_types) Normalized_Zone_Semantics_Impl.map_nth k'_def map_map)
        then show "map real_of_int (k' l') ! i = real (k l' i)"
          by simp
      qed

    note [transfer_rule] = norm_upd_transfer[folded ri_len_def]
    have [transfer_rule]: "eq_onp (\<lambda>x. x = n) n n" by (simp add: eq_onp_def)
    have [transfer_rule]: "(ri_len n) (map real_of_int (k' l')) (k' l')"
      by (simp add: ri_len_def eq_onp_def length_k' list_all2_conv_all_nth ri_def)
    have "RI n (norm_upd (conv_M M) (map real_of_int (k' l')) n) (norm_upd M (k' l') n)"
      by transfer_prover
    from RI_zone_equiv[OF this] * have
      "[curry (conv_M (norm_upd M (k' l') n))]\<^bsub>v,n\<^esub> \<subseteq> V"
      by (auto simp add: norm_upd_norm'[symmetric])
    then show ?thesis .
  qed

  lemma norm_step_correct:
    assumes diag: "\<forall>i\<le>n. conv_M D (i, i) \<le> 0" "\<forall>i\<le>n. M i i \<le> 0"
        and canonical: "canonical (curry (conv_M D)) n \<or> (\<exists>i\<le>n. D (i, i) < 0)"
        and equiv: "[curry (conv_M D)]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>"
        and valid: "valid_dbm M"
    shows
    "[curry (conv_M (FW' (norm_upd D (k' l') n) n))]\<^bsub>v,n\<^esub>
   = [norm (FW M n) (\<lambda>x. real (k l' x)) n]\<^bsub>v,n\<^esub>"
  proof (cases "check_diag n D")
    case False
    let ?k = "map real_of_int (k' l')"
    have k_alt_def: "?k = map (k l') [0..<Suc n]" unfolding k'_def by auto
    have k: "list_all2 ri ?k (k' l')" by (simp add: list_all2_conv_all_nth ri_def)
    from canonical False have "canonical (curry (conv_M D)) n"
      unfolding check_diag_def neutral by simp
    from canonical_conv_rev[OF this] have "canonical (curry D) n"
      by simp
    from FW_canonical_id[OF this] have "FW (curry D) n = curry D" .
    then have "FW' D n = D"
      apply (subst (asm) FW'_FW[symmetric])
      unfolding curry_def by (rule ext, safe, meson)
    have "RI n (FW' (norm_upd (FW' (conv_M D) n) (map real_of_int (k' l')) n) n)
       (FW' (norm_upd (FW' D n) (k' l') n) n)"
      by (intro RI_norm_step RI_conv_M k; simp add: length_k')
    moreover have "[curry (conv_M D)]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>" by (rule equiv)
    moreover have "\<forall> i \<le> n. (\<lambda>x. real (map (k l') [0..<Suc n] ! x)) i = (\<lambda>x. real (k l' x)) i"
      using map_nth by auto
    ultimately show ?thesis
      using diag
      apply -
      apply (subst \<open>_ = D\<close>[symmetric])
      apply (subst RI_zone_equiv[symmetric, where M = "FW' (norm_upd (FW' (conv_M D) n) ?k n) n"])
       apply assumption
      unfolding k_alt_def
      using norm_impl_correct[where D = "conv_M D", where M = M]
      apply (subst norm_impl_correct[where M = M])
            prefer 4
      using global_clock_numbering apply satx
      using global_clock_numbering apply satx
          apply (simp; fail)+
      apply (subst norm_k_cong[of _ "(\<lambda>x. real (k l' x))"])
      by auto
  next
    case True
    then have "check_diag n (conv_M D)" by auto
    from check_diag_empty_spec[OF this] equiv have *:
      "[curry (conv_M D)]\<^bsub>v,n\<^esub> = {}" "[M]\<^bsub>v,n\<^esub> = {}"
      by auto
    from regions.norm_FW_empty[OF valid *(2)] k_simp_2' have **:
      "[norm (FW M n) (\<lambda>x. real (k l' x)) n]\<^bsub>v,n\<^esub> = {}"
      by auto
    from norm_step_check_diag_preservation[OF True] have
      "check_diag n (FW' (norm_upd D (k' l') n) n)" .
    then have "check_diag n (conv_M (FW' (norm_upd D (k' l') n) n))" by auto
    from check_diag_empty_spec[OF this] have
      "[curry (conv_M (FW' (norm_upd D (k' l') n) n))]\<^bsub>v,n\<^esub> = {}" .
    with ** step' show ?thesis by auto
  qed

  lemma step_z_norm'_empty_preservation:
    assumes "step_z_norm' (conv_A A) l D a l' D'" "valid_dbm D" "[D]\<^bsub>v,n\<^esub> = {}"
    shows "[D']\<^bsub>v,n\<^esub> = {}"
    using assms(1)
    apply cases
    unfolding v'_v'
    apply simp
    apply (rule regions.norm_FW_empty[simplified])
    using assms(2) step_z_valid_dbm[OF _ global_clock_numbering' valid_abstraction'] apply (simp; fail)
    apply (rule step_z_dbm_empty[OF global_clock_numbering'])
    using assms(3) by auto

  lemma canonical_empty_check_diag:
    assumes "canonical (curry (conv_M D')) n \<or> (\<exists>i\<le>n. D' (i, i) < 0)" "[curry (conv_M D')]\<^bsub>v,n\<^esub> = {}"
    shows "check_diag n D'"
  proof -
    from assms(1)
    show ?thesis
    proof
      assume "canonical (curry (conv_M D')) n"
      from regions.beta_interp.canonical_empty_zone_spec[OF this] assms(2) have
        "\<exists>i\<le>n. curry (conv_M D') i i < 0"
      by fast
      with conv_dbm_entry_mono_strict_rev show ?thesis unfolding check_diag_def neutral by force
    next
      assume "\<exists>i\<le>n. D' (i, i) < 0"
      then show ?thesis unfolding check_diag_def neutral by auto
    qed
  qed

  end (* End of context for global set of regions *)

lemma FW'_valid_preservation:
  assumes "valid_dbm (curry (conv_M M))"
  shows "valid_dbm (curry (conv_M (FW' M n)))"
proof -
  from FW_valid_preservation[OF assms]
  show ?thesis by (simp add: FW'_FW[symmetric] FW'_conv_M)
qed

lemma norm_step_valid_dbm:
  "valid_dbm (curry (conv_M (FW' (norm_upd M (k' l') n) n)))" if
  "[curry (conv_M M)]\<^bsub>v,n\<^esub> \<subseteq> V" "canonical (curry (conv_M M)) n \<or> (\<exists> i \<le> n. M (i, i) < 0)"
proof -
  let ?M1 = "curry (conv_M (norm_upd M (k' l') n))"
  have "dbm_int ?M1 n" by (rule dbm_int_conv)
  from that(2) have "[?M1]\<^bsub>v,n\<^esub> \<subseteq> V"
  proof
    assume "canonical (curry (conv_M M)) n"
    from that(1) norm_upd_V_preservation[OF _ this] show "[?M1]\<^bsub>v,n\<^esub> \<subseteq> V" by auto
  next
    assume "\<exists>i\<le>n. M (i, i) < 0"
    then have "[?M1]\<^bsub>v,n\<^esub> = {}"
      by (intro check_diag_empty_spec, simp add: check_diag_def)
         (metis DBMEntry.simps(15) conv_dbm_entry_mono_strict neutral norm_upd_neg_diag_preservation
            of_int_0)
    then show ?thesis by simp
  qed
  with \<open>dbm_int ?M1 n\<close> have "valid_dbm ?M1" by - rule
  from FW'_valid_preservation[OF this] show ?thesis .
qed

lemma valid_dbm_V:
  "[M]\<^bsub>v,n\<^esub> \<subseteq> V" if "valid_dbm M"
  using that by cases

lemma step_impl_valid_dbm:
  "valid_dbm (curry (conv_M M'))" if
  "A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l', M'\<rangle>" "valid_dbm (curry (conv_M M))"
  "canonical (curry (conv_M M)) n \<or> (\<exists>i\<le>n. M (i, i) < 0)" "\<forall>i\<le>n. conv_M M (i, i) \<le> 0"
  apply (rule valid_dbm.intros)
  subgoal
    using that by - (erule step_impl_V_preservation; assumption)
  subgoal
    by (rule dbm_int_conv)
  done

(* XXX Refactor to Isar *)
lemma valid_dbm_reachable:
  assumes "E\<^sup>*\<^sup>* a\<^sub>0 (l, M)"
  shows "valid_dbm (curry (conv_M M))"
  using assms unfolding E_closure
  apply (induction l \<equiv> "l\<^sub>0" Z \<equiv> "init_dbm :: int DBM'" _ _ _ _ rule: steps_impl_induct)
  subgoal
    apply (rule valid_dbm.intros)
    using init_dbm_semantics unfolding V_def apply force
    by (auto simp: init_dbm_def ; fail)

  subgoal
    apply (rule norm_step_valid_dbm)
     apply (rule valid_dbm_V)

     apply (rule step_impl_valid_dbm, assumption)
       apply (rule step_impl_valid_dbm, assumption)
         apply assumption
        apply (rule canonical_reachable[unfolded E_closure], assumption)
       apply (drule diag_conv[OF diag_reachable, unfolded E_closure]; simp; fail)
      apply (rule step_impl_canonical step_impl_diag_preservation, assumption)
      apply (drule diag_conv[OF diag_reachable, unfolded E_closure],
        simp add: conv_dbm_entry_mono_rev neutral; fail)

    subgoal
      apply (drule step_impl_diag_preservation)
       apply (drule diag_conv[OF diag_reachable, unfolded E_closure])
       apply (auto simp: conv_dbm_entry_mono_rev neutral)[]
      apply (auto simp: conv_dbm_entry_mono_rev neutral)[]
      using conv_dbm_entry_mono by fastforce

    apply (rule step_impl_canonical)
     apply assumption
    apply (rule step_impl_diag_preservation)
     apply assumption
    apply (rule diag_reachable)
    unfolding E_closure .
  done

lemma step_impl_sound':
  assumes step: "A \<turnstile>\<^sub>I \<langle>l, D\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l', D'\<rangle>"
    and canonical: "canonical (curry (conv_M D)) n \<or> check_diag n D"
    and diag: "\<forall>i\<le>n. conv_M D (i, i) \<le> 0"
    and valid: "valid_dbm (curry (conv_M D))"
  shows
    "\<exists> M'. step_z_dbm (conv_A A) l (curry (conv_M D)) v n a l' M'
          \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> = [M']\<^bsub>v,n\<^esub>"
proof -
  let ?A = "conv_A A"
  have A: "RI_A n ?A A" by (rule RI_A_conv_A)
  have "RI n (conv_M D) D" unfolding eq_onp_def by auto
  from IR_complete[OF this A step] obtain M' where M':
    "?A \<turnstile>\<^sub>I \<langle>l, conv_M D\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l', M'\<rangle>" "RI n M' D'"
    by auto
  show ?thesis
  proof (cases "check_diag n D")
    case False
    with
      step_impl_sound[of ?A l "conv_M D",
        OF M'(1) _ global_clock_numbering' triv_numbering'' diag
        ] canonical(1)
    obtain M'' where M'':
      "?A \<turnstile> \<langle>l, curry (conv_M D)\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', M''\<rangle>" "[curry M']\<^bsub>v,n\<^esub> = [M'']\<^bsub>v,n\<^esub>"
      by auto
    with M'(2) M''(2) show ?thesis by (auto dest!: RI_zone_equiv[where v = v])
  next
    case True (* XXX This part is duplicated very often *)
    with step_impl_neg_diag_preservation[OF step] have
      "check_diag n D'"
      unfolding check_diag_def neutral by auto
    moreover from step obtain M' where M': "conv_A A \<turnstile> \<langle>l,curry (conv_M D)\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l',M'\<rangle>"
    proof cases
      case prems: step_t_impl
      then show thesis by - (rule that; simp; rule step_t_z_dbm; rule HOL.refl)
    next
      case prems: (step_a_impl g a' r)
      then show thesis
        apply -
        apply (rule that)
        unfolding \<open>a = _\<close>
        apply (rule step_a_z_dbm[where A = "conv_A A", of l "map conv_ac g" a' r l'])
        by (fastforce split: prod.split simp: trans_of_def conv_A_def)
    qed
    moreover from step_z_dbm_empty[OF global_clock_numbering' this check_diag_empty_spec] True have
      "[M']\<^bsub>v,n\<^esub> = {}"
      by auto
    ultimately show ?thesis using check_diag_empty_spec[OF check_diag_conv_M] by auto
  qed
qed

lemma step_impl_norm_sound:
  assumes step: "A \<turnstile>\<^sub>I \<langle>l, D\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l', D'\<rangle>"
    and canonical: "canonical (curry (conv_M D)) n \<or> check_diag n D"
    and diag: "\<forall>i\<le>n. conv_M D (i, i) \<le> 0"
    and valid: "valid_dbm (curry (conv_M D))"
  shows
    "\<exists> M'. step_z_norm' (conv_A A) l (curry (conv_M D)) a l' M'
           \<and> [curry (conv_M (FW' (norm_upd D' (k' l') n) n))]\<^bsub>v,n\<^esub> = [M']\<^bsub>v,n\<^esub>"
proof -
  from step_impl_sound'[OF step canonical diag valid] obtain M' where M':
    "step_z_dbm (conv_A A) l (curry (conv_M D)) v n a l' M'" "[curry (conv_M D')]\<^bsub>v,n\<^esub> = [M']\<^bsub>v,n\<^esub>"
    by auto
  from step_z_norm[OF this(1), of k] have
    "conv_A A \<turnstile> \<langle>l, curry (conv_M D)\<rangle> \<leadsto>\<^bsub>k,v,n,a\<^esub> \<langle>l', norm (FW M' n) (k l') n\<rangle>" .
  then have step':
    "step_z_norm' (conv_A A) l (curry (conv_M D)) a l' (norm (FW M' n) (k l') n)"
    using k_simp_2 by auto
  from diag have "\<forall>i\<le>n. curry D i i \<le> 0"
    by (simp add: conv_dbm_entry_mono_rev neutral)
  from step_impl_canonical[OF step this] have
    "canonical (curry (conv_M D')) n \<or> (\<exists>i\<le>n. D' (i, i) < 0)" .
  moreover have "\<forall>i\<le>n. conv_M D' (i, i) \<le> 0"
    using step_impl_diag_preservation[OF assms(1) \<open>\<forall>i\<le>n. curry D i i \<le> 0\<close>]
    by (auto dest!: conv_dbm_entry_mono simp: neutral)
  moreover have "\<forall> i \<le> n. M' i i \<le> 0"
    using step_z_dbm_diag_preservation[OF M'(1)] diag by auto
  moreover from step_z_valid_dbm[OF M'(1) global_clock_numbering' valid_abstraction' valid] have
    "valid_dbm M'" .
  ultimately have "[curry (conv_M (FW' (norm_upd D' (k' l') n) n))]\<^bsub>v,n\<^esub>
         = [norm (FW M' n) (\<lambda>x. real (k l' x)) n]\<^bsub>v,n\<^esub>"
    using M'(2) by - (rule norm_step_correct; auto)
  with step' show ?thesis
    by auto
qed

lemmas steps_z_norm'_valid_dbm_preservation =
  steps_z_norm'_valid_dbm_invariant[OF global_clock_numbering' valid_abstraction']

lemma valid_init_dbm[intro]:
  "valid_dbm (curry (init_dbm :: real DBM'))"
  apply rule
  subgoal
    unfolding V_def
    apply safe
    subgoal for u c
      by (auto dest: init_dbm_semantics[unfolded conv_M_init_dbm, where c = c])
    done
  unfolding init_dbm_def by auto

lemmas
  step_z_norm_equiv' = step_z_norm_equiv[OF _ global_clock_numbering' valid_abstraction']

lemmas
  step_z_valid_dbm' = step_z_valid_dbm[OF _ global_clock_numbering' valid_abstraction']

lemma step_impl_norm_complete:
  assumes step: "step_z_norm' (conv_A A) l (curry (conv_M M)) a l' M'"
    and canonical: "canonical (curry (conv_M M)) n"
    and diag: "\<forall>i\<le>n. conv_M M (i, i) \<le> 0"
    and valid: "valid_dbm (curry (conv_M M))"
  shows
    "\<exists> D'. A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l', D'\<rangle>
    \<and> [curry (conv_M (FW' (norm_upd D' (k' l') n) n))]\<^bsub>v,n\<^esub> = [M']\<^bsub>v,n\<^esub>"
proof -
  let ?k = "map real_of_int (k' l')"
  have k_alt_def: "?k = map (k l') [0..<Suc n]" unfolding k'_def by auto
  have k: "list_all2 ri ?k (k' l')" by (simp add: list_all2_conv_all_nth ri_def)
  have "length ?k = Suc n" using length_k' by auto
  let ?A = "conv_A A"
  have A: "RI_A n ?A A" by (rule RI_A_conv_A)
  have M_conv: "RI n (conv_M M) M" unfolding eq_onp_def by auto
  let ?M' = "uncurry M'"
  from step obtain D' where D':
    "M' = norm (FW D' n) (k l') n"
    "conv_A A \<turnstile> \<langle>l, curry (conv_M M)\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', D'\<rangle>"
    apply cases
    apply (subst (asm) v'_v')
    apply (subst (asm) k_simp_2')
    by (auto simp: k_simp_2')
  from step_impl_complete'[OF D'(2) canonical diag] obtain D'' where D'':
    "A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l', D''\<rangle>" "[curry (conv_M D'')]\<^bsub>v,n\<^esub> = [D']\<^bsub>v,n\<^esub>"
    by auto
  from diag have "\<forall>i\<le>n. curry M i i \<le> 0"
    by (simp add: conv_dbm_entry_mono_rev neutral)
  have "\<forall>i\<le>n. conv_M D'' (i, i) \<le> 0"
    using step_impl_diag_preservation[OF D''(1) \<open>\<forall>i\<le>n. curry M i i \<le> 0\<close>]
    by (auto dest!: conv_dbm_entry_mono simp: neutral)
  moreover have "\<forall>i\<le>n. D' i i \<le> 0"
    using step_z_dbm_diag_preservation[OF D'(2)] diag by auto
  moreover have "canonical (curry (conv_M D'')) n \<or> (\<exists>i\<le>n. D'' (i, i) < 0)"
    using step_impl_canonical[OF D''(1) \<open>\<forall>i\<le>n. curry M i i \<le> 0\<close>] .
  moreover have "[curry (conv_M D'')]\<^bsub>v,n\<^esub> = [D']\<^bsub>v,n\<^esub>" by fact
  moreover have "valid_dbm D'"
    using step_z_valid_dbm[OF D'(2) global_clock_numbering' valid_abstraction' valid] .
  ultimately have
    "[curry ((map_DBMEntry real_of_int \<circ>\<circ>\<circ> FW') (norm_upd D'' (k' l') n) n)]\<^bsub>v,n\<^esub>
     = [norm (FW D' n) (\<lambda>x. real (k l' x)) n]\<^bsub>v,n\<^esub>"
    by (rule norm_step_correct)
  with D''(1) show ?thesis by (auto simp add: D'(1))
qed

definition wf_dbm where
  "wf_dbm D \<equiv>
    (canonical (curry (conv_M D)) n \<or> check_diag n D)
    \<and> (\<forall>i\<le>n. conv_M D (i, i) \<le> 0)
    \<and> valid_dbm (curry (conv_M D))"

lemma wf_dbm_D:
  "canonical (curry (conv_M D)) n \<or> check_diag n D"
  "\<forall>i\<le>n. conv_M D (i, i) \<le> 0"
  "valid_dbm (curry (conv_M D))"
  if "wf_dbm D"
  using that unfolding wf_dbm_def by auto

lemma wf_dbm_I:
  "wf_dbm D" if
  "canonical (curry (conv_M D)) n \<or> check_diag n D"
  "\<forall>i\<le>n. conv_M D (i, i) \<le> 0"
  "valid_dbm (curry (conv_M D))"
  using that unfolding wf_dbm_def by auto

lemma reachable_wf_dbm:
  "wf_dbm M" if "E\<^sup>*\<^sup>* a\<^sub>0 (l, M)"
  using canonical_reachable[OF that] diag_reachable[OF that] valid_dbm_reachable[OF that]
  apply (intro wf_dbm_I)
  unfolding check_diag_def neutral[symmetric] using diag_conv by auto

lemma canonical_check_diag_empty_iff:
  "[curry (conv_M D)]\<^bsub>v,n\<^esub> = {} \<longleftrightarrow> check_diag n D" if "canonical_diag' D"
  apply standard
  subgoal
    apply (rule canonical_empty_check_diag)
    using canonical_diagI[OF that] unfolding check_diag_def neutral by auto
  by (intro check_diag_empty_spec check_diag_conv_M)

lemma step_impl_norm_complete'':
  assumes step: "step_z_norm' (conv_A A) l (curry (conv_M M)) a l' D"
    and valid: "valid_dbm (curry (conv_M M))"
    and canonical: "canonical (curry (conv_M M)) n \<or> check_diag n M"
    and diag: "\<forall>i\<le>n. conv_M M (i, i) \<le> 0"
  shows
    "\<exists> M'. A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l', M'\<rangle>
           \<and> [curry (conv_M (FW' (norm_upd M' (k' l') n) n))]\<^bsub>v,n\<^esub> = [D]\<^bsub>v,n\<^esub>"
proof (cases "check_diag n M")
  case True
  then have "[curry (conv_M M)]\<^bsub>v,n\<^esub> = {}" by (intro check_diag_empty_spec check_diag_conv_M)
  with step valid have
    "[D]\<^bsub>v,n\<^esub> = {}"
    by (rule step_z_norm'_empty_preservation)
  from step obtain M' where M': "A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l', M'\<rangle>"
    apply cases
    apply (cases rule: step_z_dbm.cases)
      apply assumption
  proof goal_cases
    case 1
    then show ?thesis by - (rule that; simp; rule step_t_impl)
  next
    case prems: (2 _ g a' r)
    obtain g' where "A \<turnstile> l \<longrightarrow>\<^bsup>g',a',r\<^esup> l'"
    proof -
      obtain T I where "A = (T, I)" by force
      from prems(6) show ?thesis by (fastforce simp: \<open>A = _\<close> trans_of_def conv_A_def intro: that)
    qed
    then show ?thesis
      apply -
      apply (rule that)
      unfolding \<open>a = _\<close> by (rule step_a_impl)
  qed
  from step_impl_check_diag[OF \<open>check_diag n M\<close> M'] have "check_diag n M'" .
  from norm_step_check_diag_preservation[OF this] have
    "check_diag n (FW' (norm_upd M' (k' l') n) n)"
    by auto
  with M' \<open>[D]\<^bsub>v,n\<^esub> = {}\<close> canonical_check_diag_empty_iff show ?thesis
    by blast
next
  case False
  with canonical have
    "canonical (curry (conv_M M)) n"
    unfolding check_diag_def neutral by auto
  then show ?thesis using diag valid step_impl_norm_complete[OF step] by auto
qed

lemmas
  step_z_dbm_mono = step_z_dbm_mono[OF global_clock_numbering']

lemmas
  step_z_norm_mono' = step_z_norm_mono[OF _ global_clock_numbering' valid_abstraction']

lemma dbm_subset_correct'':
  assumes "wf_dbm D" and "wf_dbm M"
  shows "[curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M)]\<^bsub>v,n\<^esub> \<longleftrightarrow> dbm_subset n (conv_M D) (conv_M M)"
  apply (rule dbm_subset_correct')
  using wf_dbm_D[OF assms(1)] wf_dbm_D[OF assms(2)] by auto

lemma step_impl_wf_dbm:
  assumes step: "A \<turnstile>\<^sub>I \<langle>l, D\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l', D'\<rangle>"
    and wf_dbm: "wf_dbm D"
  shows "wf_dbm D'"
  apply (rule wf_dbm_I)
  using
    step_impl_diag_preservation[OF step] step_impl_canonical[OF step] step_impl_valid_dbm[OF step]
    wf_dbm_D[OF wf_dbm]
  unfolding canonical_variant
  using diag_conv_rev diag_conv by simp+

lemma norm_step_wf_dbm:
  "wf_dbm (FW' (norm_upd D (k' l) n) n)" if "wf_dbm D"
  apply (rule wf_dbm_I)
  subgoal
    using canonical_norm_step
    unfolding canonical_variant .
  subgoal
    using wf_dbm_D[OF that] norm_step_diag_preservation
    using diag_conv[of n "FW' (norm_upd D (k' l) n) n"] diag_conv_rev by simp
  subgoal
    using wf_dbm_D[OF that]
    unfolding canonical_variant
    by (force intro!: valid_dbm_V norm_step_valid_dbm)
  done

lemma step_impl_complete''_improved:
  assumes step: "conv_A A \<turnstile> \<langle>l, curry (conv_M M)\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', D\<rangle>"
    and wf_dbm: "wf_dbm M"
  shows "\<exists> M'. A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l', M'\<rangle> \<and> [curry (conv_M M')]\<^bsub>v,n\<^esub> = [D]\<^bsub>v,n\<^esub>"
proof -
  note prems = wf_dbm_D[OF wf_dbm]
  show ?thesis
  proof (cases "check_diag n M")
    case True
    then have "[curry (conv_M M)]\<^bsub>v,n\<^esub> = {}" by (intro check_diag_empty_spec check_diag_conv_M)
    with step prems have
      "[D]\<^bsub>v,n\<^esub> = {}"
      by - (rule step_z_dbm_empty[OF global_clock_numbering'])
    moreover from step obtain M' where M': "A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l', M'\<rangle>"
    apply cases
    proof goal_cases
      case 1
      then show ?thesis by - (rule that; simp; rule step_t_impl)
    next
      case prems: (2 g a' r)
      obtain g' where "A \<turnstile> l \<longrightarrow>\<^bsup>g',a',r\<^esup> l'"
      proof -
        obtain T I where "A = (T, I)" by force
        from prems(4) show ?thesis by (fastforce simp: \<open>A = _\<close> trans_of_def conv_A_def intro: that)
      qed
      then show ?thesis
        apply -
        apply (rule that)
        unfolding \<open>a = _\<close> by (rule step_a_impl)
    qed
    ultimately show ?thesis
      using step_impl_check_diag[OF True M', THEN check_diag_conv_M, THEN check_diag_empty_spec]
      by auto
  next
    case False
    with prems have
      "canonical (curry (conv_M M)) n"
    unfolding check_diag_def neutral by fast
    moreover from prems have
      "\<forall>i\<le>n. conv_M M (i, i) \<le> 0" by fast
    ultimately show ?thesis using step_impl_complete'[OF step] by fast
  qed
qed


subsection \<open>Bisimilarity\<close>

lemma step_impl_equiv:
  assumes "A \<turnstile>\<^sub>I \<langle>l,D\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l',D'\<rangle>"
    and     "wf_dbm D" "wf_dbm M"
    and "D \<simeq> M"
  shows "\<exists> M'. A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l', M'\<rangle> \<and> D' \<simeq> M'"
proof -
  note prems_D = wf_dbm_D[OF assms(2)]
  from step_impl_sound'[OF assms(1) prems_D] diag_conv obtain M' where
    "conv_A A \<turnstile> \<langle>l, curry (conv_M D)\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', M'\<rangle>"
    "[curry (conv_M D')]\<^bsub>v,n\<^esub> = [M']\<^bsub>v,n\<^esub>"
    unfolding check_diag_def neutral by auto
  from step_z_dbm_equiv'[OF this(1) assms(4)[unfolded dbm_equiv_def]] this(2)
  show ?thesis
    by (auto simp: dbm_equiv_def dest!: step_impl_complete''_improved[OF _ assms(3)])
qed

lemma norm_step_correct':
  assumes wf_dbm: "wf_dbm D" "wf_dbm M"
    and equiv:  "D \<simeq> M"
  shows
    "[curry (conv_M (FW' (norm_upd D (k' l') n) n))]\<^bsub>v,n\<^esub>
     = [norm (FW (curry (conv_M M)) n) (\<lambda>x. real (k l' x)) n]\<^bsub>v,n\<^esub>"
  apply (rule norm_step_correct)
  using wf_dbm_D[OF wf_dbm(1)] wf_dbm_D[OF wf_dbm(2)] equiv
  unfolding dbm_equiv_def[symmetric] canonical_variant
  by auto

lemma step_impl_norm_equiv:
  assumes step:
    "A \<turnstile>\<^sub>I \<langle>l, D\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l', D'\<rangle>"
    "A \<turnstile>\<^sub>I \<langle>l', D'\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a\<^esub> \<langle>l'', D''\<rangle>"
    "D''' = FW' (norm_upd D'' (k' l'') n) n"
    and wf_dbm: "wf_dbm D" "wf_dbm M"
    and equiv: "D \<simeq> M"
  shows "\<exists> M' M'' M'''. A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l', M'\<rangle> \<and> A \<turnstile>\<^sub>I \<langle>l', M'\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a\<^esub> \<langle>l'', M''\<rangle>
       \<and> M''' = FW' (norm_upd M'' (k' l'') n) n \<and> D''' \<simeq> M'''"
proof -
  from step_impl_equiv[OF step(1) wf_dbm equiv] obtain M' where M':
    "A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l', M'\<rangle>" "D' \<simeq> M'"
    by auto
  from wf_dbm step(1) M'(1) have wf_dbm':
    "wf_dbm D'" "wf_dbm M'"
    by (auto intro: step_impl_wf_dbm)
  from step_impl_equiv[OF step(2) this M'(2)] obtain M'' where M'':
    "A \<turnstile>\<^sub>I \<langle>l', M'\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a\<^esub> \<langle>l'', M''\<rangle>" "D'' \<simeq> M''"
    by auto
  with wf_dbm' step(2) have wf_dbm'':
    "wf_dbm D''" "wf_dbm M''"
    by (auto intro: step_impl_wf_dbm)
  let ?M''' = "FW' (norm_upd M'' (k' l'') n) n"
  have "D''' \<simeq> ?M'''"
    unfolding step(3) dbm_equiv_def
    apply (subst norm_step_correct'[of M'' D''])
       prefer 4
       apply (subst norm_step_correct'[of D'' D''])
    using wf_dbm'' \<open>D'' \<simeq> M''\<close>
    by (auto intro: dbm_equiv_sym)
  with M'(1) M''(1) show ?thesis by auto
qed

definition
  "wf_state \<equiv> \<lambda> (l, M). wf_dbm M"

lemma E_equiv:
  "\<exists> b'. E b b' \<and> a' \<sim> b'" if "E a a'" "wf_state a" "wf_state b" "a \<sim> b"
  using that
  unfolding wf_state_def E_def
  apply safe
  by (drule step_impl_norm_equiv; force simp: state_equiv_def dest: state_equiv_D)

lemma E_wf_dbm[intro]:
  "wf_dbm D'" if "E (l, D) (l', D')" "wf_dbm D"
  using that unfolding wf_state_def E_def by (auto simp: norm_step_wf_dbm step_impl_wf_dbm)

lemma E_wf_state[intro]:
  "wf_state b" if "E a b" "wf_state a"
  using that unfolding wf_state_def by auto

lemma E_steps_wf_state[intro]:
  "wf_state b" if "E\<^sup>*\<^sup>* a b" "wf_state a"
  using that by (induction rule: rtranclp_induct) auto

lemma wf_dbm_init_dbm[intro, simp]:
  "wf_dbm init_dbm"
  apply (rule wf_dbm_I)
  using valid_init_dbm
  unfolding conv_M_init_dbm
  unfolding init_dbm_def neutral[symmetric]
  by simp+

lemma wf_state_init[intro, simp]:
  "wf_state a\<^sub>0"
  unfolding wf_state_def a\<^sub>0_def by simp

context
  fixes E\<^sub>1 :: "'s \<times> _ \<Rightarrow> 's \<times> _ \<Rightarrow> bool" and P
  assumes E_E\<^sub>1_step: "E a b \<Longrightarrow> wf_state a \<Longrightarrow> (\<exists> c. E\<^sub>1 a c \<and> b \<sim> c)"
  assumes E\<^sub>1_E_step: "E\<^sub>1 a b \<Longrightarrow> wf_state a \<Longrightarrow> (\<exists> c. E a c \<and> b \<sim> c)"
  assumes E\<^sub>1_equiv: "E\<^sub>1 a b \<Longrightarrow> a \<sim> a' \<Longrightarrow> P a \<Longrightarrow> P a' \<Longrightarrow> \<exists> b'. E\<^sub>1 a' b' \<and> b \<sim> b'"
  assumes E\<^sub>1_P[intro]: "P a \<Longrightarrow> E\<^sub>1 a b \<Longrightarrow> P b"
  assumes wf_state_P[intro]: "wf_state a \<Longrightarrow> P a"
begin

private lemma E\<^sub>1_steps_P:
  "P b" if "E\<^sub>1\<^sup>*\<^sup>* a b" "P a"
  using that by (induction rule: rtranclp_induct) auto

context
  notes [intro] = E\<^sub>1_steps_P
begin

private lemma E_E\<^sub>1_step':
  "(\<exists> b'. E\<^sub>1 b b' \<and> a' \<sim> b')" if "E a a'" "wf_state a" "wf_state b" "a \<sim> b"
  using that E_equiv[OF that] by (blast dest: E_E\<^sub>1_step)

private lemma E\<^sub>1_E_step':
  "(\<exists> b'. E b b' \<and> a' \<sim> b')" if "E\<^sub>1 a a'" "wf_state a" "wf_state b" "a \<sim> b"
  using that
  apply -
  apply (drule E\<^sub>1_E_step, assumption)
  apply safe
  by (drule E_equiv; blast)

private lemma E_E\<^sub>1_steps:
  "\<exists> b'. E\<^sub>1\<^sup>*\<^sup>* a b' \<and> a' \<sim> b'" if "E\<^sup>*\<^sup>* a a'" "wf_state a"
  using that
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by blast
next
  case (step y z)
  then obtain b where b: "E\<^sub>1\<^sup>*\<^sup>* a b" "y \<sim> b" by auto
  from step obtain z' where "E\<^sub>1 y z'" "z \<sim> z'"
    by atomize_elim (blast intro: E_E\<^sub>1_step)
  from step b \<open>E\<^sub>1 y z'\<close> obtain b' where "E\<^sub>1 b b'" "z' \<sim> b'"
    by atomize_elim (blast intro: E\<^sub>1_equiv)
  with b \<open>z \<sim> z'\<close> show ?case
    by (blast intro: rtranclp.intros(2))
qed

private lemma E\<^sub>1_E_steps:
  "\<exists> b'. E\<^sup>*\<^sup>* a b' \<and> a' \<sim> b'" if "E\<^sub>1\<^sup>*\<^sup>* a a'" "wf_state a"
  using that
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by blast
next
  case (step y z)
  then obtain y' where y': "E\<^sup>*\<^sup>* a y'" "y \<sim> y'"
    by auto
  with step obtain z' where "E\<^sub>1 y' z'" "z \<sim> z'"
    by atomize_elim (blast intro: E\<^sub>1_equiv)
  with y' \<open>wf_state _\<close> obtain z'' where "E y' z''" "z' \<sim> z''"
    by atomize_elim (blast intro: E\<^sub>1_E_step)
  with y' \<open>z \<sim> z'\<close> show ?case
    by (blast intro: rtranclp.intros(2))
qed

lemma E_E\<^sub>1_steps_equiv:
  "(\<exists> M'. E\<^sup>*\<^sup>* a\<^sub>0 (l', M') \<and> [curry (conv_M M')]\<^bsub>v,n\<^esub> \<noteq> {}) \<longleftrightarrow>
   (\<exists> M'. E\<^sub>1\<^sup>*\<^sup>* a\<^sub>0 (l', M') \<and> [curry (conv_M M')]\<^bsub>v,n\<^esub> \<noteq> {})"
  by (auto 4 4 simp: state_equiv_def dbm_equiv_def dest: E_E\<^sub>1_steps E\<^sub>1_E_steps)

end (* End of anonymous context for intro declaration *)

end (* End of anonymous context *)

definition "E_step \<equiv>
  \<lambda> (l, D) (l'', D'').
    \<exists> l' M' a M''. conv_A A \<turnstile> \<langle>l, curry (conv_M D)\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l', M'\<rangle>
           \<and> step_z_norm' (conv_A A) l' M' (\<upharpoonleft>a) l'' M''
           \<and> [curry (conv_M D'')]\<^bsub>v,n\<^esub> = [M'']\<^bsub>v,n\<^esub>"

lemma step_impl_sound_wf:
  assumes step: "A \<turnstile>\<^sub>I \<langle>l,D\<rangle> \<leadsto>\<^bsub>n,a\<^esub> \<langle>l',D'\<rangle>"
    and     wf: "wf_dbm D"
  shows
    "\<exists> M'. step_z_norm' (conv_A A) l (curry (conv_M D)) a l' M'
    \<and> [curry (conv_M (FW' (norm_upd D' (k' l') n) n))]\<^bsub>v,n\<^esub> = [M']\<^bsub>v,n\<^esub>"
  using step_impl_norm_sound[OF step wf_dbm_D[OF wf]] .

lemmas valid_dbm_convI = valid_dbm.intros[OF _ dbm_int_conv]
lemmas step_z_norm_valid_dbm'_spec =
  step_z_norm_valid_dbm'[OF global_clock_numbering' valid_abstraction']

lemma E_E\<^sub>1_step_aux:
  "\<exists> l' M' a M''.
    conv_A A \<turnstile> \<langle>l, curry (conv_M D)\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l', M'\<rangle> \<and>
    step_z_norm' (conv_A A) l' M' (\<upharpoonleft>a) l'' M'' \<and> [curry (conv_M D'')]\<^bsub>v,n\<^esub> = [M'']\<^bsub>v,n\<^esub>"
  if "E (l, D) (l'', D'')" "wf_dbm D"
  using that unfolding E_def
proof (safe, goal_cases)
  case prems: (1 D1 l' D2 a)
  from step_impl_sound'[OF prems(2)] prems(1) obtain M' where M':
    "conv_A A \<turnstile> \<langle>l, curry (conv_M D)\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l', M'\<rangle>" "[curry (conv_M D1)]\<^bsub>v,n\<^esub> = [M']\<^bsub>v,n\<^esub>"
    by (blast dest: wf_dbm_D)
  from prems have "wf_dbm D1"
    by (blast intro: step_impl_wf_dbm)
  from step_impl_sound_wf[OF prems(3) this] obtain M'' where M'':
    "step_z_norm'(conv_A A) l' (curry (conv_M D1)) (\<upharpoonleft>a) l'' M''"
    "[curry (conv_M (FW' (norm_upd D2 (k' l'') n) n))]\<^bsub>v,n\<^esub> = [M'']\<^bsub>v,n\<^esub>"
    by blast
  from \<open>wf_dbm D1\<close> \<open>wf_dbm D\<close> M'(1) have "valid_dbm (curry (conv_M D1))" "valid_dbm M'"
    by (blast intro: wf_dbm_D step_z_valid_dbm')+
  with step_z_norm_equiv'[OF M''(1) _ _ M'(2)] obtain M''' where
    "step_z_norm'(conv_A A) l' M' (\<upharpoonleft>a) l'' M'''" "[M'']\<^bsub>v,n\<^esub> = [M''']\<^bsub>v,n\<^esub>"
    by blast
  with M'(1) M''(2) show ?case by auto
qed

lemma E_E\<^sub>1_step: "\<exists> c. E_step a c \<and> b \<sim> c" if "E a b" "wf_state a"
  apply (cases a)
  apply (cases b)
  using that
  apply simp
  unfolding wf_state_def
  apply (drule E_E\<^sub>1_step_aux)
  unfolding E_step_def
  unfolding state_equiv_def dbm_equiv_def
  by blast+

lemma E\<^sub>1_E_step: "\<exists> c. E a c \<and> b \<sim> c" if "E_step a b" "wf_state a"
  using that
  unfolding wf_state_def
  unfolding E_step_def
proof (safe del: step_z_norm'_elims, goal_cases)
  case prems: (1 l D l'' D'' l' M' a M'')
  from step_impl_complete''_improved[OF prems(4,1)] obtain M1 where M1:
    "A \<turnstile>\<^sub>I \<langle>l, D\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l', M1\<rangle>" "[curry (conv_M M1)]\<^bsub>v,n\<^esub> = [M']\<^bsub>v,n\<^esub>"
    by blast
  with prems have "valid_dbm M'" "wf_dbm M1" "valid_dbm (curry (conv_M M1))"
    by (blast intro: wf_dbm_D step_z_valid_dbm' step_impl_wf_dbm)+
  with step_z_norm_equiv'[OF prems(5) _ _ M1(2)[symmetric]] obtain M2 where M2:
    "step_z_norm' (conv_A A) l' (curry (conv_M M1)) (\<upharpoonleft>a) l'' M2" "[M'']\<^bsub>v,n\<^esub> = [M2]\<^bsub>v,n\<^esub>"
    by blast
  from wf_dbm_D(1)[OF \<open>wf_dbm M1\<close>] have "canonical (curry (conv_M M1)) n \<or> check_diag n M1" .
  then show ?case
  proof standard
    assume "canonical (curry (conv_M M1)) n"
    with \<open>wf_dbm M1\<close> step_impl_norm_complete[OF M2(1)] obtain D3 where
      "A \<turnstile>\<^sub>I \<langle>l', M1\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a\<^esub> \<langle>l'', D3\<rangle>"
      "[curry (conv_M (FW' (norm_upd D3 (k' l'') n) n))]\<^bsub>v,n\<^esub> = [M2]\<^bsub>v,n\<^esub>"
      by (blast dest: wf_dbm_D)
    with M1(1) M2(2) prems(6) show ?case
      unfolding E_def state_equiv_def dbm_equiv_def by blast
  next
    assume "check_diag n M1"
    with M1(2) have "[M']\<^bsub>v,n\<^esub> = {}" by (auto dest: check_diag_conv_M simp: check_diag_empty_spec)
    with prems(5) \<open>valid_dbm M'\<close> have "[M'']\<^bsub>v,n\<^esub> = {}"
      by - (drule step_z_norm'_empty_preservation; assumption)
    (* XXX Can probably eliminate some step_impl_norm_complete variants and directly argue here *)
    from step_impl_norm_complete''[OF M2(1)] \<open>wf_dbm M1\<close> obtain D3 where D3:
      "A \<turnstile>\<^sub>I \<langle>l', M1\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a\<^esub> \<langle>l'', D3\<rangle>"
      "[M2]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M (FW' (norm_upd D3 (k' l'') n) n))]\<^bsub>v,n\<^esub>"
      by (blast dest: wf_dbm_D)
    from step_impl_check_diag[OF \<open>check_diag n M1\<close> D3(1)] have "check_diag n D3" .
    then have "[curry (conv_M (FW' (norm_upd D3 (k' l'') n) n))]\<^bsub>v,n\<^esub> = {}"
      using check_diag_empty_spec norm_step_check_diag_preservation by blast
    with D3 \<open>[M'']\<^bsub>v,n\<^esub> = {}\<close> M1(1) prems(6) show ?case
      unfolding E_def state_equiv_def dbm_equiv_def by blast
  qed
qed

lemma E\<^sub>1_equiv:
  defines "P \<equiv> valid_dbm o curry o conv_M o snd"
  assumes that: "E_step a b" "a \<sim> a'" "P a" "P a'"
  shows "\<exists> b'. E_step a' b' \<and> b \<sim> b'"
  using that
  unfolding E_step_def state_equiv_def dbm_equiv_def
  apply (safe del: step_z_norm'_elims)
  apply (frule step_z_dbm_equiv', assumption)
  apply (erule exE conjE)+
  unfolding P_def
  by (drule step_z_norm_equiv'; fastforce dest: step_z_valid_dbm')

lemma E\<^sub>1_P:
  defines "P \<equiv> valid_dbm o curry o conv_M o snd"
  assumes that: "E_step a b" "P a"
  shows "P b"
  using that
  unfolding E_step_def P_def
  apply (safe del: step_z_norm'_elims)
  apply (drule step_z_valid_dbm', (simp; fail))
  apply (drule step_z_norm_valid_dbm'_spec, (simp; fail))
  using valid_dbm_convI by (fastforce dest: valid_dbm_V)

lemma E_steps_equiv:
  "(\<exists> M'. E\<^sup>*\<^sup>* a\<^sub>0 (l', M') \<and> [curry (conv_M M')]\<^bsub>v,n\<^esub> \<noteq> {}) \<longleftrightarrow>
   (\<exists> M'. E_step\<^sup>*\<^sup>* a\<^sub>0 (l', M') \<and> [curry (conv_M M')]\<^bsub>v,n\<^esub> \<noteq> {})"
proof -
  define P :: "'s \<times> _ \<Rightarrow> bool" where "P \<equiv> valid_dbm o curry o conv_M o snd"
  show ?thesis
    apply (rule E_E\<^sub>1_steps_equiv[where P = P])
        apply (rule E_E\<^sub>1_step; assumption)
       apply (rule E\<^sub>1_E_step; assumption)
      apply (rule E\<^sub>1_equiv; simp add: P_def)
     apply (drule E\<^sub>1_P; simp add: P_def)
    unfolding P_def wf_state_def by (auto dest: wf_dbm_D)
qed


subsection \<open>First Layer of Simulation\<close>

lemma E_step_valid_dbm[intro]:
  assumes "valid_dbm (curry (conv_M D))" "E_step (l, D) (l', D')"
  shows "valid_dbm (curry (conv_M D'))"
  using assms unfolding E_step_def
  proof (safe del: step_z_norm'_elims, goal_cases)
    case prems: (1 l' M' a M'')
    then have "valid_dbm M''"
      by (elim step_z_norm_valid_dbm'_spec step_z_valid_dbm')
    with prems(4) show ?case
      by (blast elim!: valid_dbm.cases intro: valid_dbm_convI)
  qed

lemma E_steps_valid_dbm[intro]:
  assumes "E_step\<^sup>*\<^sup>* a\<^sub>0 (l, D)"
  shows "valid_dbm (curry (conv_M D))"
  using assms
  apply (induction "(l, D)" arbitrary: l D rule: rtranclp_induct)
  subgoal
    using valid_init_dbm by (auto simp only: conv_M_init_dbm a\<^sub>0_def)
  subgoal for x l D
    by (cases x) blast
  done

lemma E_steps_steps_z_norm':
  "\<exists> M'. steps_z_norm' (conv_A A) l\<^sub>0 (curry init_dbm) l' M' \<and> [M']\<^bsub>v,n\<^esub> = [curry (conv_M D')]\<^bsub>v,n\<^esub>"
  if "E_step\<^sup>*\<^sup>* a\<^sub>0 (l', D')"
using that proof (induction "(l', D')" arbitrary: l' D' rule: rtranclp_induct)
  case base
  then show ?case by (auto simp: a\<^sub>0_def; fail)
next
  case (step y)
  obtain l D where [simp]: "y = (l, D)"
    by force
  from step(3-)[OF this] obtain M' where M':
    "steps_z_norm' (conv_A A) l\<^sub>0 (curry init_dbm) l M'" "[M']\<^bsub>v,n\<^esub> = [curry (conv_M D)]\<^bsub>v,n\<^esub>"
    by atomize_elim
  from step(2) obtain Mi li a M'' where step':
    "conv_A A \<turnstile> \<langle>l, curry (conv_M D)\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>li, Mi\<rangle>"
    "step_z_norm' (conv_A A) li Mi (\<upharpoonleft>a) l' M''"
    "[curry (conv_M D')]\<^bsub>v,n\<^esub> = [M'']\<^bsub>v,n\<^esub>"
    unfolding E_step_def by auto
  from step_z_dbm_equiv'[OF this(1) M'(2)[symmetric]] obtain Mi' where Mi':
    "conv_A A \<turnstile> \<langle>l, M'\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>li, Mi'\<rangle>" "[Mi]\<^bsub>v,n\<^esub> = [Mi']\<^bsub>v,n\<^esub>"
    by atomize_elim
  with step'(1) M'(1) step(1) have "valid_dbm Mi" "valid_dbm Mi'"
    unfolding \<open>y = _\<close> by (blast intro: steps_z_norm'_valid_dbm_preservation step_z_valid_dbm')+
  from step_z_norm_equiv'[OF step'(2) this Mi'(2)] obtain M''' where
    "step_z_norm' (conv_A A) li Mi' (\<upharpoonleft>a) l' M'''" "[M'']\<^bsub>v,n\<^esub> = [M''']\<^bsub>v,n\<^esub>"
    by atomize_elim
  with Mi'(1) M'(1) step'(3) show ?case
    unfolding step_z_norm''_def by (auto 4 5 elim: rtranclp.intros(2))
qed

lemma dbm_int_conv_M_equiv:
  "\<exists> D. [M]\<^bsub>v,n\<^esub> = [curry (conv_M D)]\<^bsub>v,n\<^esub>" if "dbm_int M n"
proof -
  define D where "D \<equiv> \<lambda> (i, j). map_DBMEntry floor (M i j)"
  have "rel_DBMEntry ri (M i j) (D (i, j))" if "i \<le> n" "j \<le> n" for i j
  proof -
    from that \<open>dbm_int M n\<close> have "M i j \<noteq> \<infinity> \<longrightarrow> get_const (M i j) \<in> \<int>" by blast
    then show ?thesis
      unfolding D_def ri_def by (cases "M i j") (auto elim: Ints_cases)
  qed
  then have "RI n (uncurry M) D"
    unfolding eq_onp_def by auto
  from RI_zone_equiv[OF this] show ?thesis
    by auto
qed

definition "A' = conv_A A"

interpretation Bisimulation_Invariant
  "\<lambda> (l, Z) (l', Z'). \<exists> a. step_z_norm'' (conv_A A) l Z a l' Z'"
  E_step
  "\<lambda> (l, M) (l', D). l' = l \<and> [M]\<^bsub>v,n\<^esub> = [curry (conv_M D)]\<^bsub>v,n\<^esub>"
  "\<lambda> (l, M). valid_dbm M" "\<lambda> (l, D). valid_dbm (curry (conv_M D))"
  apply standard
  subgoal premises prems for a b a'
  proof -
    from prems(2) obtain l M D l' M' where [simp]: "a = (l, M)" "a' = (l, D)" "b = (l', M')"
      by force
    from prems[unfolded step_z_norm''_def, simplified, folded A'_def] obtain l1 M1 a where steps:
      "A' \<turnstile> \<langle>l, M\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l1, M1\<rangle>"
      "A' \<turnstile> \<langle>l1, M1\<rangle> \<leadsto>\<^bsub>(\<lambda>l. (k l \<circ>\<circ>\<circ> Regions.v' {Suc 0..<Suc n} v) n (Suc n)),v,n,\<upharpoonleft>a\<^esub> \<langle>l', M'\<rangle>"
      by auto
    from step_z_dbm_equiv'[folded A'_def, OF this(1), of "curry (conv_M D)"] prems(2) obtain M2
      where M2: "A' \<turnstile> \<langle>l, curry (conv_M D)\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l1, M2\<rangle>" "[M1]\<^bsub>v,n\<^esub> = [M2]\<^bsub>v,n\<^esub>"
      by auto
    from steps(2) obtain M3
      where M3:
        "A' \<turnstile> \<langle>l1, M2\<rangle> \<leadsto>\<^bsub>(\<lambda>l. (k l \<circ>\<circ>\<circ> Regions.v' {Suc 0..<Suc n} v) n (Suc n)),v,n,\<upharpoonleft>a\<^esub> \<langle>l', M3\<rangle>"
        "[M']\<^bsub>v,n\<^esub> = [M3]\<^bsub>v,n\<^esub>"
      using prems(3,4) steps(1) M2(1)
      by atomize_elim (auto
          intro!: step_z_norm_equiv'[folded A'_def, simplified, OF steps(2) _ _ M2(2)]
          dest: step_z_valid_dbm'[folded A'_def]
          )
    from prems(4) M2(1) M3(1) have "valid_dbm M3"
      by - (rule step_z_norm_valid_dbm'_spec[folded A'_def], fastforce,
          fastforce dest: step_z_valid_dbm'[folded A'_def]
          )
    then have "dbm_int M3 n"
      by - (erule valid_dbm_cases)
    from dbm_int_conv_M_equiv[OF this] obtain D' where "[M3]\<^bsub>v,n\<^esub> = [curry (conv_M D')]\<^bsub>v,n\<^esub>"
      by auto
    with \<open>[M']\<^bsub>v,n\<^esub> = _\<close> show ?thesis
      unfolding E_step_def A'_def[symmetric] by (fastforce intro: M2(1) M3(1))
  qed

  subgoal for a a' b'
    unfolding step_z_norm''_def E_step_def A'_def[symmetric]
    apply clarsimp
    apply (frule step_z_dbm_equiv'[folded A'_def], rule sym, assumption)
    apply clarify
    by (frule step_z_norm_equiv'[folded A'_def, simplified];
        auto elim: step_z_valid_dbm'[folded A'_def, simplified]
        ) auto

  subgoal for a b
    by (blast intro: steps_z_norm'_valid_dbm_preservation)

  subgoal for a b
    by blast
  done

lemma steps_z_norm'_E_steps:
  "\<exists> D'. E_step\<^sup>*\<^sup>* a\<^sub>0 (l', D') \<and> [M']\<^bsub>v,n\<^esub> = [curry (conv_M D')]\<^bsub>v,n\<^esub>" if
  "steps_z_norm' (conv_A A) l\<^sub>0 (curry init_dbm) l' M'"
  using bisim.A_B_reaches[OF that, of a\<^sub>0] valid_init_dbm unfolding a\<^sub>0_def equiv'_def by auto

lemma E_steps_steps_z_norm'_iff:
  "(\<exists> D'. E_step\<^sup>*\<^sup>* a\<^sub>0 (l', D') \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> \<noteq> {})
  \<longleftrightarrow> (\<exists> M'. steps_z_norm' (conv_A A) l\<^sub>0 (curry init_dbm) l' M' \<and> [M']\<^bsub>v,n\<^esub> \<noteq> {})"
  using steps_z_norm'_E_steps E_steps_steps_z_norm' by fast

subsection \<open>Monotonicity\<close>

lemma E_step_mono_reachable:
  assumes "E_step (l,D) (l',D')"
    and   "wf_dbm D" "wf_dbm M"
    and "[curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M)]\<^bsub>v,n\<^esub>"
  shows "\<exists> M'. E_step (l,M) (l',M') \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M')]\<^bsub>v,n\<^esub>"
  using assms
  unfolding E_step_def
  apply (safe del: step_z_norm'_elims)
  apply (frule step_z_dbm_mono, assumption)
  apply (safe del: step_z_norm'_elims)
  apply (drule step_z_norm_mono')
     prefer 3
     apply assumption
    apply (blast intro: step_z_valid_dbm' wf_dbm_D)
   apply (blast intro: step_z_valid_dbm' wf_dbm_D)
  apply (safe del: step_z_norm'_elims)
  subgoal premises prems for l'' M' a M'' D'' M'''
  proof -
    from prems have "valid_dbm M'''"
      by (fast intro: step_z_valid_dbm' wf_dbm_D step_z_norm_valid_dbm'_spec)
    with dbm_int_conv_M_equiv[of M'''] obtain D''' where D''':
      "[M''']\<^bsub>v,n\<^esub> = [curry (conv_M D''')]\<^bsub>v,n\<^esub>"
      by (blast elim!: valid_dbm.cases)
    with prems show ?thesis
      by fastforce
  qed
  done

lemma E_mono:
  assumes "E (l,D) (l',D')"
    and   "wf_dbm D" "wf_dbm M"
    and "[curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M)]\<^bsub>v,n\<^esub>"
  shows "\<exists> M'. E (l,M) (l',M') \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M')]\<^bsub>v,n\<^esub>"
  using assms
  apply -
  apply (drule E_E\<^sub>1_step)
   apply (simp add: wf_state_def; fail)
  apply safe
  apply (drule E_step_mono_reachable[where M = M], assumption+)
  by (force simp: wf_state_def state_equiv_def dbm_equiv_def dest: E\<^sub>1_E_step)

lemma E_mono':
  assumes "E (l,D) (l',D')"
    and   "wf_dbm D" "wf_dbm M"
    and "dbm_subset n D M"
  shows "\<exists> M'. E (l,M) (l',M') \<and> dbm_subset n D' M'"
  using assms
  apply -
  apply (frule E_mono[where M = M], assumption+)
   apply (subst dbm_subset_correct'', assumption+)
   apply (rule dbm_subset_conv, assumption)
  apply safe
  apply (subst (asm) dbm_subset_correct'')
    apply (blast intro: dbm_subset_conv_rev)+
  done

lemma reachable_steps_z_norm':
  "(\<exists> D'. E\<^sup>*\<^sup>* a\<^sub>0 (l', D') \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> \<noteq> {})
    \<longleftrightarrow> (\<exists> M'. steps_z_norm' (conv_A A) l\<^sub>0 (curry init_dbm) l' M' \<and> [M']\<^bsub>v,n\<^esub> \<noteq> {})"
  unfolding E_steps_steps_z_norm'_iff E_steps_equiv ..

subsection \<open>Instantiating the Reachability Problem\<close>

theorem reachable_decides_emptiness:
  "(\<exists> D'. E\<^sup>*\<^sup>* a\<^sub>0 (l', D') \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> \<noteq> {})
    \<longleftrightarrow> (\<exists> u \<in> [curry init_dbm]\<^bsub>v,n\<^esub>. \<exists> u'. conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>)"
  by (subst reachable_steps_z_norm')
    (subst
      steps_z_norm_decides_emptiness
      [OF global_clock_numbering' valid_abstraction'[unfolded X_alt_def]
        finite_trans_of_finite_state_set[OF finite_trans'] valid_init_dbm
        ],
      rule HOL.refl
      )

lemma reachable_decides_emptiness':
  "(\<exists> D'. E\<^sup>*\<^sup>* a\<^sub>0 (l', D') \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> \<noteq> {})
    \<longleftrightarrow> (\<exists> u u'. conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall> c \<in> {1..n}. u c = 0))"
  using reachable_decides_emptiness init_dbm_semantics' init_dbm_semantics'' by blast

lemma reachable_empty_check_diag:
  assumes "E\<^sup>*\<^sup>* a\<^sub>0 (l', D')" "[curry (conv_M D')]\<^bsub>v,n\<^esub> = {}"
  shows "check_diag n D'"
  using canonical_reachable[OF assms(1)] canonical_empty_check_diag assms(2) by simp

lemma check_diag_E_preservation:
  "check_diag n M'" if "check_diag n M" "E (l, M) (l', M')"
  using that unfolding E_def check_diag_def neutral[symmetric]
  by (fastforce
      simp: curry_def dest: step_impl_neg_diag_preservation
      intro: FW'_neg_diag_preservation norm_upd_neg_diag_preservation
      )

lemma cn_weak:
  "\<forall>c. 0 < v c"
  using clock_numbering(1) by auto

end (* TA Start *)


locale Reachability_Problem =
  TA_Start A l\<^sub>0 n k +
  Reachability_Problem_Defs A l\<^sub>0 n k F for A :: "('a, nat, int, 's) ta" and l\<^sub>0 n k F
begin

theorem reachability_check:
  "(\<exists> D'. E\<^sup>*\<^sup>* a\<^sub>0 (l', D') \<and> F_rel (l', D'))
    \<longleftrightarrow> (\<exists> u u'. conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall> c \<in> {1..n}. u c = 0) \<and> F l')"
  using reachable_decides_emptiness'[of l'] check_diag_empty_spec reachable_empty_check_diag
  unfolding F_rel_def by auto

sublocale Standard_Search_Space: Search_Space E a\<^sub>0 F_rel "subsumes n" "\<lambda> (l, M). check_diag n M"
  apply standard
  subgoal for a
    apply (rule prod.exhaust[of a])
    by (auto simp add: subsumes_simp_1 dbm_subset_refl)
  subgoal for a b c
    apply (rule prod.exhaust[of a], rule prod.exhaust[of b], rule prod.exhaust[of c])
    subgoal for l1 M1 l2 M2 l3 M3
      apply simp
      apply (cases "check_diag n M1")
       apply (simp add: subsumes_def; fail)
      apply (simp add: subsumes_def)
      by (meson check_diag_subset dbm_subset_def dbm_subset_trans)
    done
  subgoal for a b a'
    apply (rule prod.exhaust[of a], rule prod.exhaust[of b], rule prod.exhaust[of a'])
    apply safe
    by (drule E_mono';
        fastforce simp: E_def subsumes_def dbm_subset_def Graph_Start_Defs.reachable_def
        intro!: reachable_wf_dbm)
  subgoal
    unfolding F_rel_def subsumes_def by auto
  subgoal
    using check_diag_subset unfolding subsumes_def dbm_subset_def by auto
  subgoal
    using check_diag_E_preservation by auto
  unfolding F_rel_def subsumes_def
  unfolding check_diag_def pointwise_cmp_def
  by fastforce

sublocale Standard_Search_Space_finite_strict:
  Search_Space_finite_strict E a\<^sub>0 F_rel "subsumes n" "\<lambda> (l, M). check_diag n M"
  apply standard
  using E_closure_finite unfolding Graph_Start_Defs.reachable_def by (auto; fail)



paragraph \<open>Nice to have (to be moved)\<close>
  (* XXX Unused, move *)
lemma V_I:
  assumes "\<forall> i \<in> {1..<Suc n}. M 0 i \<le> 0"
  shows "[M]\<^bsub>v,n\<^esub> \<subseteq> V"
  unfolding V_def DBM_zone_repr_def
proof (safe, goal_cases)
  case prems: (1 u i)
  then have "v i = i"
    using X_alt_def X_def triv_numbering by blast
  with prems have "v i > 0" "v i \<le> n" by auto
  with prems have "dbm_entry_val u None (Some i) (M 0 (v i))"
    unfolding DBM_val_bounded_def by auto
  moreover from assms \<open>v i > 0\<close> \<open>v i \<le> n\<close> have "M 0 (v i) \<le> 0" by auto
  ultimately
  show ?case
    apply (cases "M 0 (v i)")
    unfolding neutral less_eq dbm_le_def
    by (auto elim!: dbm_lt.cases simp: \<open>v i = i\<close>)
qed

lemma V_canonicalD:
  assumes V: "[M]\<^bsub>v,n\<^esub> \<subseteq> V" and canonical: "canonical M n"
  shows "(\<exists> i \<le> n. M i i < 0) \<or> (\<forall> i \<in> {1..<Suc n}. M 0 i \<le> 0)"
proof clarify
  (*
    fix i assume A: "\<not> (\<exists>i\<le>n. M i i < 0)" "i \<in> {1..<Suc n}"
    with assms have "cyc_free M n"
    from \<open>i \<in> _\<close> have "v i = i"
    show "M 0 i \<le> 0"
    proof (rule ccontr)
      assume F: "\<not> M 0 i \<le> 0"
      from F have "M 0 i > Le 0" unfolding neutral by auto
      then obtain d u where "d > 0" "u \<in> [M]\<^bsub>v,n\<^esub>" "- u i = d"
      with V \<open>i \<in> _\<close> show False unfolding V_def by force
    qed
    *)
  oops

lemma clock_val_cong:
  "\<forall>c\<in>{Suc 0..n}. u c = d \<Longrightarrow> \<forall>c\<in>{Suc 0..n}. u' c = d \<Longrightarrow> u \<turnstile> inv_of (conv_A A) l\<^sub>0
    \<Longrightarrow> u' \<turnstile> inv_of (conv_A A) l\<^sub>0"
  oops

(* XXX Unused *)
(* XXX Generalize (see haves on clock numbering), move? *)
lemma DBM_val_bounded_cong':
  "\<forall>c\<in>{Suc 0..n}. u c = u' c \<Longrightarrow> u \<turnstile>\<^bsub>v,n\<^esub> M \<Longrightarrow> u' \<turnstile>\<^bsub>v,n\<^esub> M"
  unfolding DBM_val_bounded_def
proof (safe, goal_cases)
  case prems: (1 c)
  from prems have v: "v c = c" "v c > 0" by (auto simp: cn_weak intro: v_id)
  show ?case
  proof (cases "M 0 (v c)")
    case (Le d)
    with prems have "- u c \<le> d" by auto
    with Le v prems show ?thesis by auto
  next
    case (Lt d)
    with prems have "- u c < d" by auto
    with Lt v prems show ?thesis by auto
  qed auto
next
  case prems: (2 c)
  from prems have v: "v c = c" "v c > 0" by (auto simp: cn_weak intro: v_id)
  show ?case
  proof (cases "M (v c) 0")
    case (Le d)
    with prems have "u c \<le> d" by auto
    with Le v prems show ?thesis by auto
  next
    case (Lt d)
    with prems have "u c < d" by auto
    with Lt v prems show ?thesis by auto
  qed auto
next
  case prems: (3 c1 c2)
  from prems have v: "v c1 = c1" "v c1 > 0" "v c2 = c2" "v c2 > 0"
    by (auto simp: cn_weak intro: v_id)
  show ?case
  proof (cases "M (v c1) (v c2)")
    case (Le d)
    with prems have "u c1 - u c2 \<le> d" by (auto 4 3)
    with Le v prems show ?thesis by auto
  next
    case (Lt d)
    with prems have "u c1 - u c2 < d" by (auto 4 3)
    with Lt v prems show ?thesis by auto
  qed auto
qed

lemma DBM_val_bounded_cong:
  "\<forall>c\<in>{Suc 0..n}. u c = d \<Longrightarrow> \<forall>c\<in>{Suc 0..n}. u' c = d \<Longrightarrow> u \<turnstile>\<^bsub>v,n\<^esub> M \<Longrightarrow> u' \<turnstile>\<^bsub>v,n\<^esub> M"
  using DBM_val_bounded_cong' by force

end (* End of locale context *)

lemma abstr_upd_correct:
  assumes gcn: "\<forall>c. 0 < v c \<and> (\<forall>x y. v x \<le> n \<and> v y \<le> n \<and> v x = v y \<longrightarrow> x = y)"
      and surj: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
      and clocks: "\<forall>c\<in>collect_clks (inv_of A l). v c = c \<and> 0 < c \<and> v c \<le> n"
  shows
  "[curry (abstr_upd (inv_of A l) D)]\<^bsub>v,n\<^esub> = [And (curry D) (abstr (inv_of A l) (\<lambda>i j. \<infinity>) v)]\<^bsub>v,n\<^esub>"
  apply (subst abstr_upd_abstr')
   defer
   apply (subst abstr_abstr'[symmetric])
    defer
    apply (subst And_abstr[symmetric])
  using assms by fastforce+

locale Reachability_Problem_start =
  Reachability_Problem +
  assumes start_inv: "[(curry init_dbm :: real DBM)]\<^bsub>v,n\<^esub> \<subseteq> {u. u \<turnstile> conv_cc (inv_of A l\<^sub>0)}"
begin

lemma start_inv':
  "[(curry init_dbm :: real DBM)]\<^bsub>v,n\<^esub> \<subseteq> {u. u \<turnstile> inv_of (conv_A A) l\<^sub>0}"
  using start_inv unfolding conv_A_def
  (* XXX SMT *)
  (* s/h *)
  by (smt case_prod_conv comp_apply inv_of_def prod.collapse snd_conv subset_Collect_conv)

lemma start_vals:
  "u \<turnstile> inv_of (conv_A A) l\<^sub>0" if "\<forall> c \<in> {1..n}. u c = 0"
  using that start_inv' init_dbm_semantics'' by auto

lemma steps_steps'_equiv':
  "(\<exists> u u'. conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall> c \<in> {1..n}. u c = 0))
  \<longleftrightarrow> (\<exists> u u'. conv_A A \<turnstile> \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall> c \<in> {1..n}. u c = 0))"
  using steps_steps'_equiv[of _ \<open>conv_A A\<close> l\<^sub>0] start_vals by fast

corollary reachability_check_start:
  "(\<exists> D'. E\<^sup>*\<^sup>* a\<^sub>0 (l', D') \<and> F_rel (l', D'))
  \<longleftrightarrow> (\<exists> u u'. conv_A A \<turnstile> \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall> c \<in> {1..n}. u c = 0) \<and> F l')"
  using reachability_check steps_steps'_equiv' by fast

end (* End of locale context for ensuring that the invariant of the start state is satisfied *)

lemma check_diag_conv_M_rev:
  assumes "check_diag n (conv_M M)"
  shows "check_diag n M"
using assms unfolding check_diag_def by (auto intro!: conv_dbm_entry_mono_strict_rev)

context TA_Start_No_Ceiling
begin

lemma surj_numbering:
  "\<forall>k\<le>n. 0 < k \<longrightarrow> (\<exists>c. v c = k)"
  using global_clock_numbering[THEN conjunct2, THEN conjunct2] .

lemma collect_clks_numbering:
  "\<forall>c\<in>collect_clks (inv_of A l\<^sub>0). v c = c \<and> 0 < c \<and> v c \<le> n"
  by (metis collect_clks_inv_clk_set global_clock_numbering subsetCE v_id)

lemma collect_clks_numbering':
  "\<forall>c\<in>collect_clks (inv_of (conv_A A) l\<^sub>0). v c = c \<and> 0 < c \<and> v c \<le> n"
  by (metis (no_types, lifting) collect_clks_inv_clk_set global_clock_numbering' subsetCE triv_numbering'')

lemmas dbm_abstr_zone_eq' = dbm_abstr_zone_eq[OF global_clock_numbering[THEN conjunct1]]

end

definition (in TA_Start_No_Ceiling_Defs)
  "unbounded_dbm = (\<lambda> (i, j). (if i = j \<or> i > n \<or> j > n then Le 0 else \<infinity>))"

context TA_Start
begin

lemmas abstr_upd_correct' =
  abstr_upd_correct[OF clock_numbering(1) surj_numbering collect_clks_numbering']

lemma FW'_zone_equiv:
  "[curry (conv_M (FW' M n))]\<^bsub>v,n\<^esub> = [curry (conv_M M)]\<^bsub>v,n\<^esub>"
  by (metis FW'_FW FW'_conv_M FW_zone_equiv_spec)

lemma unbounded_dbm_semantics:
  "[curry unbounded_dbm]\<^bsub>v,n\<^esub> = UNIV"
  unfolding unbounded_dbm_def
  unfolding DBM_zone_repr_def apply auto
  unfolding DBM_val_bounded_def
  apply auto
  (* s/h *)
  using cn_weak gr_implies_not_zero apply blast
  using cn_weak gr_implies_not_zero apply blast
  (* s/h *)
  by (metis dbm_entry_val.intros(5) diff_self order_mono_setup.refl v_id)

lemma And_unbounded_dbm:
  "[And (curry unbounded_dbm) M]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>"
  by (subst And_correct[symmetric]) (simp add: unbounded_dbm_semantics)

definition
  "start_inv_check \<equiv> dbm_subset n init_dbm (FW' (abstr_upd (inv_of A l\<^sub>0) unbounded_dbm) n)"

lemma conv_inv:
  "conv_cc (inv_of A l\<^sub>0) = inv_of (conv_A A) l\<^sub>0"
  unfolding inv_of_def conv_A_def by (simp split!: prod.split)

lemma start_inv_check:
  "start_inv_check \<longleftrightarrow> [(curry init_dbm :: real DBM)]\<^bsub>v,n\<^esub> \<subseteq> {u. u \<turnstile> conv_cc (inv_of A l\<^sub>0)}"
proof -
  let ?M = "FW' (abstr_upd (inv_of A l\<^sub>0) unbounded_dbm) n"
  have canonical: "canonical (curry init_dbm) n \<or> check_diag n init_dbm"
    unfolding init_dbm_def by (auto simp: neutral[symmetric])
  have diag: "\<forall>i\<le>n. curry (conv_M ?M) i i \<le> 0"
    apply (rule diag_conv)
    unfolding curry_def unbounded_dbm_def
    apply (rule FW'_diag_preservation)
    apply (rule abstr_upd_diag_preservation')
    using collect_clks_numbering unfolding neutral by auto
  have "\<forall>i\<le>n. curry init_dbm i i \<le> 0" unfolding init_dbm_def neutral by auto
  from dbm_subset_correct'[OF canonical this diag] canonical have
    "dbm_subset n init_dbm (conv_M ?M)
    \<longleftrightarrow> [(curry init_dbm :: real DBM)]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M ?M)]\<^bsub>v,n\<^esub>"
    by auto
  moreover have "[curry (conv_M ?M)]\<^bsub>v,n\<^esub> = {u. u \<turnstile> inv_of (conv_A A) l\<^sub>0}"
    apply (subst FW'_zone_equiv)
    apply (subst RI_zone_equiv[symmetric,
           where M = "abstr_upd (inv_of (conv_A A) l\<^sub>0) unbounded_dbm"])
     defer
     apply (subst abstr_upd_correct')
     apply (subst And_unbounded_dbm)
     apply (subst dbm_abstr_zone_eq')
    using collect_clks_numbering' apply force
     apply simp
    subgoal
    proof -
      have [transfer_rule]: "rel_DBMEntry ri 0 0" "rel_DBMEntry ri \<infinity> \<infinity>"
        unfolding ri_def neutral by auto
      have [transfer_rule]: "eq_onp (\<lambda>x. x < Suc n) n n"
        by (simp add: eq_onp_def)
      have [transfer_rule]:
        "rel_fun (eq_onp (\<lambda>x. x < Suc n)) (rel_fun (eq_onp (\<lambda>x. x < Suc n)) (=)) (<) (<)"
        unfolding rel_fun_def eq_onp_def by simp
      have [transfer_rule]: "(RI n) unbounded_dbm unbounded_dbm"
        unfolding unbounded_dbm_def by transfer_prover
      have [transfer_rule]: "RI_A n (conv_A A) A" by (rule RI_A_conv_A)
      note [transfer_rule] = inv_of_transfer[unfolded RI_I_def]
      show ?thesis by transfer_prover
    qed
    done
  ultimately show ?thesis
    unfolding start_inv_check_def conv_inv using dbm_subset_conv_rev dbm_subset_conv conv_M_init_dbm
    by metis
qed

(* XXX Move and clean proof *)
lemma start_inv_check_correct:
  "start_inv_check \<longleftrightarrow> (\<forall> u. (\<forall> c \<in> {1..n}. u c = 0) \<longrightarrow> u \<turnstile> inv_of (conv_A A) l\<^sub>0)"
  unfolding start_inv_check conv_inv using  init_dbm_semantics'' init_dbm_semantics' by fast

end

context Reachability_Problem
begin

lemma F_reachable_equiv':
  "(\<exists> l' u u'. conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall> c \<in> {1..n}. u c = 0))
    \<longleftrightarrow> (\<exists> l' u u'. conv_A A \<turnstile> \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall> c \<in> {1..n}. u c = 0))"
  if start_inv_check
proof -

  interpret start: Reachability_Problem_start A l\<^sub>0 n k
    apply standard
    using that unfolding start_inv_check .
  from start.steps_steps'_equiv' show ?thesis by fast
qed

lemma F_reachable_equiv:
  "(\<exists> l' u u'. conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall> c \<in> {1..n}. u c = 0) \<and> F l')
    \<longleftrightarrow> (\<exists> l' u u'. conv_A A \<turnstile> \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall> c \<in> {1..n}. u c = 0) \<and> F l')"
  if start_inv_check
proof -
  interpret start: Reachability_Problem_start A l\<^sub>0 n k
    apply standard
    using that unfolding start_inv_check .
  from start.steps_steps'_equiv' show ?thesis by fast
qed

end

(* XXX This is obsolete now *)
context TA_Start_No_Ceiling
begin

  context
  begin

  private abbreviation "k \<equiv> default_ceiling A"

  lemma k_bound:
    assumes "i > n"
    shows "k i = 0"
  proof -
    from \<open>i > n\<close> have "i \<notin> {1..n}" by auto
    then have
      "i \<notin> clk_set A"
      using clocks_n by fast
    then have "{m. (i, m) \<in> Timed_Automata.clkp_set A} = {}" by auto
    then show ?thesis unfolding default_ceiling_def by auto
  qed

  lemma k_0:
   "k 0 = 0"
    using clock_range unfolding default_ceiling_def by auto

  lemma valid_abstraction:
     "Timed_Automata.valid_abstraction A X k"
    by (rule standard_abstraction_int;
        force intro!: consts_nats clk_set_X[unfolded X_def] clk_set_X finite_X)

  (* XXX This is a bit clumsy *)
  lemma k_ge:
    "\<forall>(x,m) \<in> Timed_Automata.clkp_set A. m \<le> k x"
    using valid_abstraction by (auto elim!: Timed_Automata.valid_abstraction.cases)

  end

end


(* XXX Rename. Move? *)
lemma aux:
  "x \<in> set xs \<Longrightarrow> \<exists> i < length xs. xs ! i = x"
by (metis index_less_size_conv nth_index)

lemma collect_clock_pairs_empty[simp]:
  "collect_clock_pairs [] = {}"
unfolding collect_clock_pairs_def by auto

subsection \<open>Pre-compiled automata with states and clocks as natural numbers\<close>
locale Reachability_Problem_precompiled_defs =
  fixes n :: nat \<comment> \<open>Number of states. States are 0 through n - 1\<close>
    and m :: nat \<comment> \<open>Number of clocks\<close>
    and k :: "nat list list"
    \<comment> \<open>Clock ceiling. Maximal constant appearing in automaton for each clock for each state\<close>
    and inv :: "(nat, int) cconstraint list" \<comment> \<open>Clock invariants on states\<close>
    and trans :: "((nat, int) cconstraint * nat list * nat) list list"
        \<comment> \<open>Transitions between states\<close>
    and final :: "nat list" \<comment> \<open>Final states. Initial location is 0\<close>
begin

  definition "clkp_set' l \<equiv>
    collect_clock_pairs (inv ! l) \<union> \<Union> ((\<lambda> (g, _). collect_clock_pairs g) ` set (trans ! l))"
  definition clk_set'_def: "clk_set' =
    (\<Union> ((\<lambda> l. fst ` clkp_set' l) ` {0..<n}) \<union> \<Union> ((\<lambda> (g, r, _). set r) ` set (concat trans)))"

  text \<open>Definition of the corresponding automaton\<close>
  definition "label a \<equiv> \<lambda> (g, r, l'). (g, a, r, l')"
  definition "I l \<equiv> if l < n then inv ! l else []"
  definition "T \<equiv> {(l, label i (trans ! l ! i)) | l i. l < n \<and> i < length (trans ! l)}"
  definition "A \<equiv> (T, I)"
  definition "F \<equiv> \<lambda> x. x \<in> set final"

end


locale Reachability_Problem_precompiled = Reachability_Problem_precompiled_defs +
  assumes inv_length: "length inv = n"
    and trans_length: "length trans = n" (* "\<forall> xs \<in> set trans. length xs \<ge> n" *)
    and state_set: "\<forall> xs \<in> set trans. \<forall> (_, _, l) \<in> set xs. l < n"
    and k_length: "length k = n" "\<forall> l \<in> set k. length l = m + 1"
    \<comment> \<open>Zero entry is just a dummy for the zero clock\<close>
    (* XXX Make this an abbreviation? *)
  assumes k_ceiling:
    "\<forall> l < n. \<forall> (c, d) \<in> clkp_set' l. k ! l ! c \<ge> nat d" "\<forall> l < n. \<forall> c \<in> {1..m}. k ! l ! c \<ge> 0"
    "\<forall> l < n. k ! l ! 0 = 0"
    "\<forall> l < n. \<forall> (_, r, l') \<in> set (trans ! l). \<forall> c \<le> m. c \<notin> set r
        \<longrightarrow> k ! l ! c \<ge> k ! l' ! c"
  assumes consts_nats: "\<forall> l < n. snd ` clkp_set' l \<subseteq> \<nat>"
  assumes clock_set: "clk_set' = {1..m}"
    and m_gt_0: "m > 0"
    and n_gt_0: "n > 0" and start_has_trans: "trans ! 0 \<noteq> []" \<comment> \<open>Necessary for refinement\<close>
begin

lemma consts_nats':
  "\<forall> cc \<in> set inv. \<forall> (c, d) \<in> collect_clock_pairs cc. d \<in> \<nat>"
  "\<forall> xs \<in> set trans. \<forall> (g, _) \<in> set xs. \<forall> (c, d) \<in> collect_clock_pairs g. d \<in> \<nat>"
  using consts_nats unfolding clkp_set'_def
   apply safe
  using inv_length apply (auto dest!: aux; fail)
  using trans_length by - (drule aux, auto)

lemma clkp_set_simp_1:
  "collect_clock_pairs (inv ! l) = collect_clki (inv_of A) l" if "l < n"
  unfolding A_def inv_of_def collect_clki_def I_def[abs_def] using inv_length that by auto

lemma clkp_set_simp_1':
  "\<Union> (collect_clock_pairs ` set inv) = Timed_Automata.collect_clki (inv_of A)"
  unfolding A_def inv_of_def Timed_Automata.collect_clki_def I_def[abs_def] using inv_length
  by (auto simp add: collect_clks_id image_Union dest: nth_mem dest!: aux)

lemma clk_set_simp_2:
  "\<Union> ((\<lambda> (g, r, _). set r) ` set (concat trans)) = collect_clkvt (trans_of A)"
  unfolding A_def trans_of_def collect_clkvt_def T_def[abs_def] label_def using trans_length
  apply (clarsimp simp add: image_Union dest: nth_mem)
  apply safe
   apply ((drule aux)+, force)
  apply (drule nth_mem, simp)
    (* XXX Find these instances automatically *)
  apply (rule_tac x = "trans ! a" in bexI)
   apply (rule_tac x = "trans ! a ! i" in bexI)
  by auto

lemma clkp_set_simp_3:
  "\<Union> ((\<lambda> (g, _). collect_clock_pairs g) ` set (trans ! l))
      = collect_clkt (trans_of A) l" if "l < n"
  unfolding A_def trans_of_def collect_clkt_def T_def[abs_def] label_def
  using trans_length that
  apply (auto simp add: collect_clks_id image_Union dest: nth_mem)
  by (force dest!: aux)

lemma clkp_set_simp_3':
  "\<Union> ((\<lambda> (g, _). Timed_Automata.collect_clock_pairs g) ` set (concat trans))
      = Timed_Automata.collect_clkt (trans_of A)"
  unfolding A_def trans_of_def Timed_Automata.collect_clkt_def T_def[abs_def] label_def
  using trans_length
  apply (auto simp add: collect_clks_id image_Union dest: nth_mem)
   apply (auto dest!: aux)[]
   apply force
  apply (auto dest!: nth_mem)
  apply (rule_tac x = "trans ! aa" in bexI)
   apply (rule_tac x = "trans ! aa ! i" in bexI)
  by auto

lemma clkp_set'_eq:
  "clkp_set A l = clkp_set' l" if "l < n"
  using that
  by (fastforce simp: clkp_set'_def clkp_set_def image_Un image_Union
      clkp_set_simp_1[symmetric] clkp_set_simp_3[symmetric]
      )

lemma clkp_set_out_of_bounds:
  "clkp_set A l = {}" if "l \<ge> n" for l
  using that
  unfolding clkp_set_def collect_clki_def collect_clkt_def
  unfolding inv_of_def A_def I_def T_def trans_of_def
  by simp

lemma clkp_setD:
  "(x, d) \<in> clkp_set' l" if "(x, d) \<in> Closure.clkp_set A l"
  using that by (cases "l < n") (auto simp: clkp_set'_eq clkp_set_out_of_bounds)

lemma clkp_set_boundD:
  "l < n" if "pair \<in> clkp_set A l" for pair
  using that by - (rule ccontr, auto simp: clkp_set_out_of_bounds)

lemma clkp_set'_eq':
  "Timed_Automata.clkp_set A = \<Union> (clkp_set' ` {0..<n})"
proof -
  have "\<Union> (clkp_set A ` UNIV) = \<Union> (clkp_set A ` {0..<n})"
    apply safe
    subgoal for _ _ x
      by (cases "x < n") (auto simp: clkp_set_out_of_bounds)
    by auto
  then show ?thesis by (simp add: TA_clkp_set_unfold clkp_set'_eq)
qed

lemma clk_set'_eq[simp]:
  "clk_set A = clk_set'"
  unfolding clkp_set'_eq' clk_set'_def clk_set_simp_2 by auto

(* XXX Interesting for finiteness *)
(* XXX Move *)
lemma Collect_fold_pair:
  "{f a b | a b. P a b} = (\<lambda> (a, b). f a b) ` {(a, b). P a b}"
  by auto

(* XXX Interesting case of proving finiteness *)
lemma finite_T[intro, simp]:
  "finite (trans_of A)"
proof -
  have
    "{(l, i). l < n \<and> i < length (trans ! l)}
      = \<Union> ((\<lambda> l. {(l, i) | i. i < length (trans ! l)}) ` {l. l < n})"
    by auto
  then show ?thesis unfolding trans_of_def A_def T_def by (auto simp: Collect_fold_pair)
qed

lemma has_clock[intro]:
  "clk_set A \<noteq> {}"
  using clock_set m_gt_0 by simp

lemma clk_set:
  "clk_set A = {1..m}"
  using clock_set m_gt_0 by auto

lemma clk_set_eq:
  "clk_set A = {1..card (clk_set A)}"
  using clk_set by auto

lemma
  "\<forall>c\<in>clk_set A. c \<le> card (clk_set A) \<and> c \<noteq> 0"
  using clock_set by auto

lemma clkp_set_consts_nat:
  "\<forall>(_, d)\<in>Timed_Automata.clkp_set A. d \<in> \<nat>"
  unfolding
    Timed_Automata.clkp_set_def ta_collect_clki_alt_def ta_collect_clkt_alt_def
    A_def trans_of_def inv_of_def
    T_def I_def[abs_def] label_def
  using consts_nats' inv_length trans_length by (force dest: nth_mem)

lemma finite_range_inv_of_A[intro, simp]:
  "finite (range (inv_of A))"
  unfolding inv_of_def A_def I_def[abs_def] by (auto intro: finite_subset[where B = "{[]}"])

lemma transD:
  "(g, r, l') \<in> set (trans ! l) \<and> l < n" if "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"
  using that
  unfolding trans_of_def A_def T_def label_def
  by (auto dest!: nth_mem; simp split: prod.split_asm)

lemma clkp_set_clk_bound:
  "a \<le> m" if "(a, b) \<in> clkp_set' l" "l < n"
  using that clock_set clk_set'_def
  by fastforce

sublocale TA_Start_No_Ceiling A 0 m
  using has_clock clkp_set_consts_nat clk_set m_gt_0 by - (standard, auto)

(* XXX There is room for optimization here *)
sublocale Reachability_Problem A 0 m "\<lambda> l i. if l < n \<and> i \<le> m then k ! l ! i else 0" "PR_CONST F"
  apply standard
  subgoal
    apply safe
    apply (frule clkp_set_boundD)
    unfolding clkp_set'_eq
    using k_ceiling
    by (auto 4 10 dest: clkp_set_clk_bound)
  subgoal
    using k_ceiling(4) by (fastforce dest!: transD)
  subgoal
    using k_ceiling(2,3) by simp
  subgoal
    using k_ceiling(3) by simp
  done

end (* End of locale *)

end
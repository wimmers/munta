section \<open>Extrapolation of DBMs\<close>

theory DBM_Normalization
imports DBM_Basics TA_Misc
begin

subsection \<open>Classical extrapolation\<close>

text \<open>This is the implementation of the classical extrapolation operator (\<open>Extra\<^sub>M\<close>).\<close>

fun norm_upper :: "('t::linorder) DBMEntry \<Rightarrow> 't \<Rightarrow> 't DBMEntry"
where
  "norm_upper e t = (if Le t \<prec> e then \<infinity> else e)"
  
fun norm_lower :: "('t::linorder) DBMEntry \<Rightarrow> 't \<Rightarrow> 't DBMEntry"
where
  "norm_lower e t = (if e \<prec> Lt t then Lt t else e)"

text \<open>
  Note that literature pretends that \<open>\<zero>\<close> would have some (presumably infinite bound) in \<open>k\<close>
  and thus defines normalization uniformly. The easiest way to get around this seems to explicate
  this in the definition as below.
\<close>
definition norm :: "('t :: linordered_ab_group_add) DBM \<Rightarrow> (nat \<Rightarrow> 't) \<Rightarrow> nat \<Rightarrow> 't DBM"
where
  "norm M k n \<equiv> \<lambda>i j.
    let ub = if i > 0 then k i   else 0 in
    let lb = if j > 0 then - k j else 0 in
    if i \<le> n \<and> j \<le> n then norm_lower (norm_upper (M i j) ub) lb else M i j
  "

subsection \<open>Extrapolations based on lower and upper bounds\<close>

text \<open>This is the implementation of the LU-bounds based extrapolation operation (\<open>Extra_{LU}\<close>).\<close>
definition extra_lu ::
  "('t :: linordered_ab_group_add) DBM \<Rightarrow> (nat \<Rightarrow> 't) \<Rightarrow> (nat \<Rightarrow> 't) \<Rightarrow> nat \<Rightarrow> 't DBM"
where
  "extra_lu M l u n \<equiv> \<lambda>i j.
    let ub = if i > 0 then l i   else 0 in
    let lb = if j > 0 then - u j else 0 in
    if i \<le> n \<and> j \<le> n then norm_lower (norm_upper (M i j) ub) lb else M i j
  "

lemma norm_is_extra:
  "norm M k n = extra_lu M k k n"
  unfolding norm_def extra_lu_def ..


subsection \<open>Extrapolations are widening operators\<close>

lemma extra_lu_mono:
  assumes "\<forall>c. v c > 0" "u \<in> [M]\<^bsub>v,n\<^esub>"
  shows "u \<in> [extra_lu M L U n]\<^bsub>v,n\<^esub>" (is "u \<in> [?M2]\<^bsub>v,n\<^esub>")
proof -
  note A = assms
  note M1 = A(2)[unfolded DBM_zone_repr_def DBM_val_bounded_def]
  show ?thesis
  proof (unfold DBM_zone_repr_def DBM_val_bounded_def, auto)
    show "Le 0 \<preceq> ?M2 0 0"
    using A unfolding extra_lu_def DBM_zone_repr_def DBM_val_bounded_def dbm_le_def by auto
  next
    fix c assume "v c \<le> n"
    with M1 have M1: "dbm_entry_val u None (Some c) (M 0 (v c))" by auto
    from \<open>v c \<le> n\<close> A have *:
      "?M2 0 (v c) = norm_lower (norm_upper (M 0 (v c)) 0) (- U (v c))"
    unfolding extra_lu_def by auto
    show "dbm_entry_val u None (Some c) (?M2 0 (v c))"
    proof (cases "M 0 (v c) \<prec> Lt (- U (v c))")
      case True
      show ?thesis
      proof (cases "Le 0 \<prec> M 0 (v c)")
        case True with * show ?thesis by auto
      next
        case False 
        with * True have "?M2 0 (v c) = Lt (- U (v c))" by auto
        moreover from True dbm_entry_val_mono_2[OF M1] have
          "dbm_entry_val u None (Some c) (Lt (- U (v c)))"
        by auto
        ultimately show ?thesis by auto
      qed
    next
      case False
      show ?thesis
      proof (cases "Le 0 \<prec> M 0 (v c)")
        case True with * show ?thesis by auto
      next
        case F: False
        with M1 * False show ?thesis by auto
      qed
    qed
  next
    fix c assume "v c \<le> n"
    with M1 have M1: "dbm_entry_val u (Some c) None (M (v c) 0)" by auto
    from \<open>v c \<le> n\<close> A have *:
      "?M2 (v c) 0 = norm_lower (norm_upper (M (v c) 0) (L (v c))) 0"
    unfolding extra_lu_def by auto
    show "dbm_entry_val u (Some c) None (?M2 (v c) 0)"
    proof (cases "Le (L (v c)) \<prec> M (v c) 0")
      case True
      with A(1,2) \<open>v c \<le> n\<close> have "?M2 (v c) 0 = \<infinity>" unfolding extra_lu_def by auto
      then show ?thesis by auto
    next
      case False
      show ?thesis
      proof (cases "M (v c) 0 \<prec> Lt 0")
        case True with False * dbm_entry_val_mono_3[OF M1] show ?thesis by auto
      next
        case F: False
        with M1 * False show ?thesis by auto
      qed
    qed
  next
    fix c1 c2 assume "v c1 \<le> n" "v c2 \<le> n"
    with M1 have M1: "dbm_entry_val u (Some c1) (Some c2) (M (v c1) (v c2))" by auto
    then show "dbm_entry_val u (Some c1) (Some c2) (?M2 (v c1) (v c2))"
    proof (cases "Le (L (v c1)) \<prec> M (v c1) (v c2)")
      case True
      with A(1,2) \<open>v c1 \<le> n\<close> \<open>v c2 \<le> n\<close> have "?M2 (v c1) (v c2) = \<infinity>" unfolding extra_lu_def by auto
      then show ?thesis by auto
    next
      case False
      with A(1,2) \<open>v c1 \<le> n\<close> \<open>v c2 \<le> n\<close> have
        *: "?M2 (v c1) (v c2) = norm_lower (M (v c1) (v c2)) (- U (v c2))"
      unfolding extra_lu_def by auto
      show ?thesis
      proof (cases "M (v c1) (v c2) \<prec> Lt (- U (v c2))")
        case True
        with dbm_entry_val_mono_1[OF M1] have
          "dbm_entry_val u (Some c1) (Some c2) (Lt (- U (v c2)))"
        by auto
        then have "u c1 - u c2 < - U (v c2)" by auto
        with * True show ?thesis by auto
      next
        case False with M1 * show ?thesis by auto
      qed
    qed
  qed
qed

lemma norm_mono:
  assumes "\<forall>c. v c > 0" "u \<in> [M]\<^bsub>v,n\<^esub>"
  shows "u \<in> [norm M k n]\<^bsub>v,n\<^esub>"
  using assms unfolding norm_is_extra by (rule extra_lu_mono)



subsection \<open>Finiteness of extrapolations\<close>

abbreviation "dbm_default M n \<equiv> (\<forall> i > n. \<forall> j. M i j = 0) \<and> (\<forall> j > n. \<forall> i. M i j = 0)"

lemma norm_default_preservation:
  "dbm_default M n \<Longrightarrow> dbm_default (norm M k n) n"
  by (simp add: norm_def)

lemma extra_lu_default_preservation:
  "dbm_default M n \<Longrightarrow> dbm_default (extra_lu M L U n) n"
  by (simp add: extra_lu_def)

instance int :: linordered_cancel_ab_monoid_add by (standard; simp)

(* XXX Move *)
lemmas finite_subset_rev[intro?] = finite_subset[rotated]
lemmas [intro?] = finite_subset

lemma extra_lu_finite:
  "finite {extra_lu M (L :: nat \<Rightarrow> nat) (U :: nat \<Rightarrow> nat) n | M. dbm_default M n}"
proof -
  let ?u = "Max {L i | i. i \<le> n}" let ?l = "- Max {U i | i. i \<le> n}"
  let ?S = "(Le ` {d :: int. ?l \<le> d \<and> d \<le> ?u}) \<union> (Lt ` {d :: int. ?l \<le> d \<and> d \<le> ?u}) \<union> {\<infinity>}"
  from finite_set_of_finite_funs2[of "{0..n}" "{0..n}" ?S] have fin:
    "finite {f. \<forall>x y. (x \<in> {0..n} \<and> y \<in> {0..n} \<longrightarrow> f x y \<in> ?S)
                \<and> (x \<notin> {0..n} \<longrightarrow> f x y = 0) \<and> (y \<notin> {0..n} \<longrightarrow> f x y = 0)}" (is "finite ?R")
    by auto
  { fix M :: "int DBM" assume A: "dbm_default M n"
    let ?M = "extra_lu M L U n"
    from extra_lu_default_preservation[OF A] have A: "dbm_default ?M n" .
    { fix i j assume "i \<in> {0..n}" "j \<in> {0..n}"
      then have B: "i \<le> n" "j \<le> n"
        by auto
      have "?M i j \<in> ?S"
      proof (cases "?M i j = \<infinity>")
        case True then show ?thesis
          by auto
      next
        case False
        note not_inf = this
        have "?l \<le> get_const (?M i j) \<and> get_const (?M i j) \<le> ?u"
        proof (cases "i = 0")
          case True
          show ?thesis
          proof (cases "j = 0")
            case True
            with \<open>i = 0\<close> A(1) B have
              "?M i j = norm_lower (norm_upper (M 0 0) 0) 0"
              unfolding extra_lu_def by auto
            also have "\<dots> \<noteq> \<infinity> \<longrightarrow> get_const \<dots> = 0"
              by (cases "M 0 0"; fastforce)
            finally show ?thesis using not_inf
              by auto
          next
            case False
            with \<open>i = 0\<close> B not_inf have "?M i j \<le> Le 0" "Lt (-int (U j)) \<le> ?M i j"
              unfolding extra_lu_def
              apply (simp del: norm_upper.simps norm_lower.simps)
              apply (auto simp: less[symmetric]; fail)
              using \<open>i = 0\<close> B not_inf apply (auto simp: Let_def less[symmetric] intro: any_le_inf)[]
              apply (drule leI)
              apply (drule leI)
              by (rule order.trans; fastforce)
            with not_inf have "get_const (?M i j) \<le> 0" "-U j \<le> get_const (?M i j)"
              by (cases "?M i j"; auto)+
            moreover from \<open>j \<le> n\<close> have "- U j \<ge> ?l"
              by (auto intro: Max_ge)
            ultimately show ?thesis
              by auto
          qed
        next
          case False
          then have "i > 0" by simp
          show ?thesis
          proof (cases "j = 0")
            case True
            with \<open>i > 0\<close> A(1) B not_inf have "Lt 0 \<le> ?M i j" "?M i j \<le> Le (int (L i))"
              unfolding extra_lu_def
              apply (simp del: norm_upper.simps norm_lower.simps)
              apply (auto simp: less[symmetric])[]
              using \<open>i > 0\<close> \<open>j = 0\<close> A(1) B not_inf unfolding extra_lu_def
              by (auto simp: Let_def less[symmetric] intro: any_le_inf)[]
            with not_inf have "0 \<le> get_const (?M i j)" "get_const (?M i j) \<le> L i"
              by (cases "?M i j"; auto)+
            moreover from \<open>i \<le> n\<close> have "L i \<le> ?u"
              by (auto intro: Max_ge)
            ultimately show ?thesis
              by auto
          next
            case False
            with \<open>i > 0\<close> A(1) B not_inf have
              "Lt (-int (U j)) \<le> ?M i j" "?M i j \<le> Le (int (L i))"
              unfolding extra_lu_def
              apply (simp del: norm_upper.simps norm_lower.simps)
              apply (auto simp: less[symmetric])[]
              using \<open>i > 0\<close> \<open>j \<noteq> 0\<close> A(1) B not_inf unfolding extra_lu_def
              by (auto simp: Let_def less[symmetric] intro: any_le_inf)[]
            with not_inf have "- U j \<le> get_const (?M i j)" "get_const (?M i j) \<le> L i"
              by (cases "?M i j"; auto)+
            moreover from \<open>i \<le> n\<close> \<open>j \<le> n\<close> have "?l \<le> - U j" "L i \<le> ?u"
              by (auto intro: Max_ge)
            ultimately show ?thesis
              by auto
          qed
        qed
        then show ?thesis by (cases "?M i j"; auto elim: Ints_cases)
      qed
    } moreover
    { fix i j assume "i \<notin> {0..n}"
      with A have "?M i j = 0" by auto
    } moreover
    { fix i j assume "j \<notin> {0..n}"
      with A have "?M i j = 0" by auto
    } moreover note the = calculation
  } then have "{extra_lu M L U n | M. dbm_default M n} \<subseteq> ?R"
    by blast
  with fin show ?thesis ..
qed

lemma normalized_integral_dbms_finite:
  "finite {norm M (k :: nat \<Rightarrow> nat) n | M. dbm_default M n}"
  unfolding norm_is_extra by (rule extra_lu_finite)

end
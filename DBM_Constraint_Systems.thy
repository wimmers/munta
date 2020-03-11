chapter \<open>DBMs as Constraint Systems\<close>
theory DBM_Constraint_Systems
  imports
    DBM_Operations
    DBM_Normalization
begin

section \<open>Misc\<close>

no_notation infinity ("\<infinity>")

lemma Max_le_MinI:
  assumes "finite S" "finite T" "S \<noteq> {}" "T \<noteq> {}" "\<And>x y. x \<in> S \<Longrightarrow> y \<in> T \<Longrightarrow> x \<le> y"
  shows "Max S \<le> Min T" by (simp add: assms)

lemma Min_insert_cases:
  assumes "x = Min (insert a S)" "finite S"
  obtains (default) "x = a" | (elem) "x \<in> S"
  by (metis Min_in assms finite.insertI insertE insert_not_empty)

lemma cval_add_simp[simp]:
  "(u \<oplus> d) x = u x + d"
  unfolding cval_add_def by simp

lemmas [simp] = any_le_inf

lemma Le_in_between:
  assumes "a < b"
  obtains d where "a \<le> Le d" "Le d \<le> b"
  using assms by atomize_elim (cases a; cases b; auto)

lemma DBMEntry_le_to_sum:
  fixes e e' :: "'t :: time DBMEntry"
  assumes "e' \<noteq> \<infinity>" "e \<le> e'"
  shows "- e' + e \<le> 0"
  using assms by (cases e; cases e') (auto simp: DBM.neutral DBM.add uminus)

lemma DBMEntry_le_add:
  fixes a b c :: "'t :: time DBMEntry"
  assumes "a \<le> b + c" "c \<noteq> \<infinity>"
  shows "-c + a \<le> b"
  using assms
  by (cases a; cases b; cases c) (auto simp: DBM.neutral DBM.add uminus algebra_simps)

lemma DBM_triv_emptyI:
  assumes "M 0 0 < 0"
  shows "[M]\<^bsub>v,n\<^esub> = {}"
  using assms
  unfolding DBM_zone_repr_def DBM_val_bounded_def DBM.less_eq[symmetric] DBM.neutral by auto



section \<open>Definition and Semantics of Constraint Systems\<close>
datatype ('x, 'v) constr =
  Lower 'x "'v DBMEntry" | Upper 'x "'v DBMEntry" | Diff 'x 'x "'v DBMEntry"

type_synonym ('x, 'v) cs = "('x, 'v) constr set"

inductive entry_sem ("_ \<Turnstile>\<^sub>e _" [62, 62] 62) where
  "v \<Turnstile>\<^sub>e Lt x" if "v < x" |
  "v \<Turnstile>\<^sub>e Le x" if "v \<le> x" |
  "v \<Turnstile>\<^sub>e \<infinity>"

inductive constr_sem ("_ \<Turnstile>\<^sub>c _" [62, 62] 62) where
  "u \<Turnstile>\<^sub>c Lower x e" if "- u x \<Turnstile>\<^sub>e e" |
  "u \<Turnstile>\<^sub>c Upper x e" if   "u x \<Turnstile>\<^sub>e e" |
  "u \<Turnstile>\<^sub>c Diff x y e" if "u x - u y \<Turnstile>\<^sub>e e"

definition cs_sem ("_ \<Turnstile>\<^sub>c\<^sub>s _" [62, 62] 62) where
  "u \<Turnstile>\<^sub>c\<^sub>s cs \<longleftrightarrow> (\<forall>c \<in> cs. u \<Turnstile>\<^sub>c c)"

definition cs_models ("_ \<Turnstile> _" [62, 62] 62) where
  "cs \<Turnstile> c \<equiv> \<forall>u. u \<Turnstile>\<^sub>c\<^sub>s cs \<longrightarrow> u \<Turnstile>\<^sub>c c"

definition cs_equiv ("_ \<equiv>\<^sub>c\<^sub>s _" [62, 62] 62) where
  "cs \<equiv>\<^sub>c\<^sub>s cs' \<equiv> \<forall>u. u \<Turnstile>\<^sub>c\<^sub>s cs \<longleftrightarrow> u \<Turnstile>\<^sub>c\<^sub>s cs'"

definition
  "closure cs \<equiv> {c. cs \<Turnstile> c}"

definition
  "bot_cs = {Lower undefined (Lt 0), Upper undefined (Lt 0)}"

lemma constr_sem_less_eq_iff:
  "u \<Turnstile>\<^sub>c Lower x e \<longleftrightarrow> Le (-u x) \<le> e"
  "u \<Turnstile>\<^sub>c Upper x e \<longleftrightarrow> Le (u x) \<le> e"
  "u \<Turnstile>\<^sub>c Diff x y e \<longleftrightarrow> Le (u x - u y) \<le> e"
  by (cases e; auto simp: constr_sem.simps entry_sem.simps)+

lemma constr_sem_mono:
  assumes "e \<le> e'"
  shows
    "u \<Turnstile>\<^sub>c Lower x e  \<Longrightarrow> u \<Turnstile>\<^sub>c Lower x e'"
    "u \<Turnstile>\<^sub>c Upper x e  \<Longrightarrow> u \<Turnstile>\<^sub>c Upper x e'"
    "u \<Turnstile>\<^sub>c Diff x y e \<Longrightarrow> u \<Turnstile>\<^sub>c Diff x y e'"
  using assms unfolding constr_sem_less_eq_iff by simp+

lemma constr_sem_triv[simp,intro]:
  "u \<Turnstile>\<^sub>c Upper x \<infinity>" "u \<Turnstile>\<^sub>c Lower y \<infinity>" "u \<Turnstile>\<^sub>c Diff x y \<infinity>"
  unfolding constr_sem.simps entry_sem.simps by auto

lemma cs_sem_antimono:
  assumes "cs \<subseteq> cs'" "u \<Turnstile>\<^sub>c\<^sub>s cs'"
  shows "u \<Turnstile>\<^sub>c\<^sub>s cs"
  using assms unfolding cs_sem_def by auto

lemma cs_equivD[intro, dest]:
  assumes "u \<Turnstile>\<^sub>c\<^sub>s cs" "cs \<equiv>\<^sub>c\<^sub>s cs'"
  shows "u \<Turnstile>\<^sub>c\<^sub>s cs'"
  using assms unfolding cs_equiv_def by auto

lemma cs_equiv_sym:
  "cs \<equiv>\<^sub>c\<^sub>s cs'" if "cs' \<equiv>\<^sub>c\<^sub>s cs"
  using that unfolding cs_equiv_def by fast

lemma cs_equiv_union:
  "cs \<equiv>\<^sub>c\<^sub>s cs \<union> cs'" if "cs \<equiv>\<^sub>c\<^sub>s cs'"
  using that unfolding cs_equiv_def cs_sem_def by blast

lemma cs_equiv_alt_def:
  "cs \<equiv>\<^sub>c\<^sub>s cs' \<longleftrightarrow> (\<forall>c. cs \<Turnstile> c \<longleftrightarrow> cs' \<Turnstile> c)"
  unfolding cs_equiv_def cs_models_def cs_sem_def by auto

lemma closure_equiv:
  "closure cs \<equiv>\<^sub>c\<^sub>s cs"
  unfolding cs_equiv_alt_def closure_def cs_models_def cs_sem_def by auto

lemma closure_superset:
  "cs \<subseteq> closure cs"
  unfolding closure_def cs_models_def cs_sem_def by auto

lemma bot_cs_empty:
  "\<not> (u :: ('c \<Rightarrow> 't :: linordered_ab_group_add)) \<Turnstile>\<^sub>c\<^sub>s bot_cs"
  unfolding bot_cs_def cs_sem_def by (auto elim!: constr_sem.cases entry_sem.cases)

lemma finite_bot_cs:
  "finite bot_cs"
  unfolding bot_cs_def by auto

definition cs_vars where
  "cs_vars cs = \<Union> (set1_constr ` cs)"

definition map_cs_vars where
  "map_cs_vars v cs = map_constr v id ` cs"

lemma constr_sem_rename_vars:
  assumes "inj_on v S" "set1_constr c \<subseteq> S"
  shows "(u o inv_into S v) \<Turnstile>\<^sub>c map_constr v id c \<longleftrightarrow> u \<Turnstile>\<^sub>c c"
  using assms
  by (cases c) (auto intro!: constr_sem.intros elim!: constr_sem.cases simp: DBMEntry.map_id)

lemma cs_sem_rename_vars:
  assumes "inj_on v (cs_vars cs)"
  shows "(u o inv_into (cs_vars cs) v) \<Turnstile>\<^sub>c\<^sub>s map_cs_vars v cs \<longleftrightarrow> u \<Turnstile>\<^sub>c\<^sub>s cs"
  using assms constr_sem_rename_vars unfolding map_cs_vars_def cs_sem_def cs_vars_def by blast


section \<open>Conversion of DBMs to Constraint Systems and Back\<close>

definition dbm_to_cs :: "nat \<Rightarrow> ('x \<Rightarrow> nat) \<Rightarrow> ('v :: {linorder,zero}) DBM \<Rightarrow> ('x, 'v) cs" where
  "dbm_to_cs n v M \<equiv> if M 0 0 < 0 then bot_cs else
    {Lower x (M 0 (v x)) | x. v x \<le> n} \<union>
    {Upper x (M (v x) 0) | x. v x \<le> n} \<union>
    {Diff x y (M (v x) (v y)) | x y. v x \<le> n \<and> v y \<le> n}"

lemma dbm_entry_val_Lower_iff:
  "dbm_entry_val u None (Some x) e \<longleftrightarrow> u \<Turnstile>\<^sub>c Lower x e"
  by (cases e) (auto simp: constr_sem_less_eq_iff)

lemma dbm_entry_val_Upper_iff:
  "dbm_entry_val u (Some x) None e \<longleftrightarrow> u \<Turnstile>\<^sub>c Upper x e"
  by (cases e) (auto simp: constr_sem_less_eq_iff)

lemma dbm_entry_val_Diff_iff:
  "dbm_entry_val u (Some x) (Some y) e \<longleftrightarrow> u \<Turnstile>\<^sub>c Diff x y e"
  by (cases e) (auto simp: constr_sem_less_eq_iff)

lemmas dbm_entry_val_constr_sem_iff =
  dbm_entry_val_Lower_iff
  dbm_entry_val_Upper_iff
  dbm_entry_val_Diff_iff

theorem dbm_to_cs_correct:
  "u \<turnstile>\<^bsub>v,n\<^esub> M \<longleftrightarrow> u \<Turnstile>\<^sub>c\<^sub>s dbm_to_cs n v M"
  apply (rule iffI)
  unfolding DBM_val_bounded_def dbm_entry_val_constr_sem_iff dbm_to_cs_def
  subgoal
    by (auto simp: DBM.neutral DBM.less_eq[symmetric] cs_sem_def)
  using bot_cs_empty by (cases "M 0 0 < 0", auto simp: DBM.neutral DBM.less_eq[symmetric] cs_sem_def)

definition
  "cs_to_dbm v cs \<equiv> if (\<forall>u. \<not>u \<Turnstile>\<^sub>c\<^sub>s cs) then (\<lambda>_ _. Lt 0) else (
    \<lambda>i j.
      if i = 0 then
        if j = 0 then
          Le 0
        else
          Min (insert \<infinity> {e. \<exists>x. Lower x e \<in> cs \<and> v x = j})
      else
        if j = 0 then
          Min (insert \<infinity> {e. \<exists>x. Upper x e \<in> cs \<and> v x = i})
        else
          Min (insert \<infinity> {e. \<exists>x y. Diff x y e \<in> cs \<and> v x = i \<and> v y = j})
  )"

lemma finite_dbm_to_cs:
  assumes "finite {x. v x \<le> n}"
  shows "finite (dbm_to_cs n v M)"
  using [[simproc add: finite_Collect]] unfolding dbm_to_cs_def
  by (auto intro: assms simp: finite_bot_cs)

lemma empty_dbm_empty:
  "u \<turnstile>\<^bsub>v,n\<^esub> \<lambda>_ _. Lt 0 \<longleftrightarrow> False"
  unfolding DBM_val_bounded_def by (auto simp: DBM.less_eq[symmetric])

fun expr_of_constr where
  "expr_of_constr (Lower _ e) = e" |
  "expr_of_constr (Upper _ e) = e" |
  "expr_of_constr (Diff _ _ e) = e"

lemma cs_to_dbm1:
  assumes "\<forall>x \<in> cs_vars cs. v x > 0 \<and> v x \<le> n" "finite cs"
  assumes "u \<turnstile>\<^bsub>v,n\<^esub> cs_to_dbm v cs"
  shows "u \<Turnstile>\<^sub>c\<^sub>s cs"
proof (cases "\<forall>u. \<not>u \<Turnstile>\<^sub>c\<^sub>s cs")
  case True
  with assms(3) show ?thesis
    unfolding cs_to_dbm_def by (simp add: empty_dbm_empty)
next
  case False
  show "u \<Turnstile>\<^sub>c\<^sub>s cs"
    unfolding cs_sem_def
  proof (rule ballI)
    fix c
    assume "c \<in> cs"
    show "u \<Turnstile>\<^sub>c c"
    proof (cases c)
      case (Lower x e)
      with assms(1) \<open>c \<in> cs\<close> have *: "0 < v x" "v x \<le> n"
        by (auto simp: cs_vars_def)
      let ?S = "{e. \<exists>x'. Lower x' e \<in> cs \<and> v x' = v x}"
      let ?e = "Min (insert \<infinity> ?S)"
      have "?S \<subseteq> expr_of_constr ` cs"
        by force
      with \<open>finite cs\<close> \<open>c \<in> cs\<close> \<open>c = _\<close> have "?e \<le> e"
        using finite_subset finite_imageI by (blast intro: Min_le)
      moreover from * assms(3) False have "dbm_entry_val u None (Some x) ?e"
        unfolding DBM_val_bounded_def cs_to_dbm_def by (auto 4 4)
      ultimately have "dbm_entry_val u None (Some x) (e)"
        by - (rule dbm_entry_val_mono[folded DBM.less_eq])
      then show ?thesis
        unfolding dbm_entry_val_constr_sem_iff[symmetric] \<open>c = _\<close> .
    next
      case (Upper x e)
      with assms(1) \<open>c \<in> cs\<close> have *: "0 < v x" "v x \<le> n"
        by (auto simp: cs_vars_def)
      let ?S = "{e. \<exists>x'. Upper x' e \<in> cs \<and> v x' = v x}"
      let ?e = "Min (insert \<infinity> ?S)"
      have "?S \<subseteq> expr_of_constr ` cs"
        by force
      with \<open>finite cs\<close> \<open>c \<in> cs\<close> \<open>c = _\<close> have "?e \<le> e"
        using finite_subset finite_imageI by (blast intro: Min_le)
      moreover from * assms(3) False have "dbm_entry_val u (Some x) None ?e"
        unfolding DBM_val_bounded_def cs_to_dbm_def by (auto 4 4)
      ultimately have "dbm_entry_val u (Some x) None e"
        by - (rule dbm_entry_val_mono[folded DBM.less_eq])
      then show ?thesis
        unfolding dbm_entry_val_constr_sem_iff \<open>c = _\<close> .
    next
      case (Diff x y e)
      with assms(1) \<open>c \<in> cs\<close> have *: "0 < v x" "v x \<le> n" "0 < v y" "v y \<le> n"
        by (auto simp: cs_vars_def)
      let ?S = "{e. \<exists>x' y'. Diff x' y' e \<in> cs \<and> v x' = v x \<and> v y' = v y}"
      let ?e = "Min (insert \<infinity> ?S)"
      have "?S \<subseteq> expr_of_constr ` cs"
        by force
      with \<open>finite cs\<close> \<open>c \<in> cs\<close> \<open>c = _\<close> have "?e \<le> e"
        using finite_subset finite_imageI by (blast intro: Min_le)
      moreover from * assms(3) False have "dbm_entry_val u (Some x) (Some y) ?e"
        unfolding DBM_val_bounded_def cs_to_dbm_def by (auto 4 4)
      ultimately have "dbm_entry_val u (Some x) (Some y) e"
        by - (rule dbm_entry_val_mono[folded DBM.less_eq])
      then show ?thesis
        unfolding dbm_entry_val_constr_sem_iff \<open>c = _\<close> .
    qed
  qed
qed

lemma cs_to_dbm2:
  assumes "\<forall>x. v x \<le> n \<longrightarrow> v x > 0" "\<forall>x y. v x \<le> n \<and> v y \<le> n \<and> v x = v y \<longrightarrow> x = y"
  assumes "finite cs"
  assumes "u \<Turnstile>\<^sub>c\<^sub>s cs"
  shows "u \<turnstile>\<^bsub>v,n\<^esub> cs_to_dbm v cs"
proof (cases "\<forall>u. \<not>u \<Turnstile>\<^sub>c\<^sub>s cs")
  case True
  with assms show ?thesis
    unfolding cs_to_dbm_def by (simp add: empty_dbm_empty)
next
  case False
  let ?M = "cs_to_dbm v cs"
  show "u \<turnstile>\<^bsub>v,n\<^esub> cs_to_dbm v cs"
    unfolding DBM_val_bounded_def
  proof (clarsimp simp: DBM.less_eq [symmetric] ; safe)
    show "Le 0 \<le> cs_to_dbm v cs 0 0"
      using False unfolding cs_to_dbm_def by auto
  next
    fix x :: 'a
    assume "v x \<le> n"
    let ?S = "{e. \<exists>x'. Lower x' e \<in> cs \<and> v x' = v x}"
    from \<open>v x \<le> n\<close> assms have "v x > 0"
      by simp
    with False have "?M 0 (v x) = Min (insert \<infinity> ?S)"
      unfolding cs_to_dbm_def by auto
    moreover have "finite ?S"
    proof -
      have "?S \<subseteq> expr_of_constr ` cs"
        by force
      also have "finite \<dots>"
        using \<open>finite cs\<close> by (rule finite_imageI)
      finally show ?thesis .
    qed
    ultimately show "dbm_entry_val u None (Some x) (?M 0 (v x))"
      using assms(2-) \<open>v x \<le> n\<close>
      by (cases rule: Min_insert_cases, (auto; fail))
        (simp add: dbm_entry_val_constr_sem_iff cs_sem_def, metis)
  next
    fix x :: 'a
    assume "v x \<le> n"
    let ?S = "{e. \<exists>x'. Upper x' e \<in> cs \<and> v x' = v x}"
    from \<open>v x \<le> n\<close> assms have "v x > 0"
      by simp
    with False have "?M (v x) 0 = Min (insert \<infinity> ?S)"
      unfolding cs_to_dbm_def by auto
    moreover have "finite ?S"
    proof -
      have "?S \<subseteq> expr_of_constr ` cs"
        by force
      also have "finite \<dots>"
        using \<open>finite cs\<close> by (rule finite_imageI)
      finally show ?thesis .
    qed
    ultimately show "dbm_entry_val u (Some x) None (cs_to_dbm v cs (v x) 0)"
      using \<open>v x \<le> n\<close> assms(2-)
      by (cases rule: Min_insert_cases, (auto; fail))
        (simp add: dbm_entry_val_constr_sem_iff cs_sem_def, metis)
  next
    fix x y :: 'a
    assume "v x \<le> n" "v y \<le> n"
    let ?S = "{e. \<exists>x' y'. Diff x' y' e \<in> cs \<and> v x' = v x \<and> v y' = v y}"
    from \<open>v x \<le> n\<close> \<open>v y \<le> n\<close> assms have "v x > 0" "v y > 0"
      by auto
    with False have "?M (v x) (v y) = Min (insert \<infinity> ?S)"
      unfolding cs_to_dbm_def by auto
    moreover have "finite ?S"
    proof -
      have "?S \<subseteq> expr_of_constr ` cs"
        by force
      also have "finite \<dots>"
        using \<open>finite cs\<close> by (rule finite_imageI)
      finally show ?thesis .
    qed
    ultimately show "dbm_entry_val u (Some x) (Some y) (cs_to_dbm v cs (v x) (v y))"
      using \<open>v x \<le> n\<close> \<open>v y \<le> n\<close> assms(2-)
      by (cases rule: Min_insert_cases, (auto; fail))
        (simp add: dbm_entry_val_constr_sem_iff cs_sem_def, metis)
  qed
qed

theorem cs_to_dbm_correct:
  assumes "\<forall>x \<in> cs_vars cs. v x \<le> n" "\<forall>x. v x \<le> n \<longrightarrow> v x > 0"
    "\<forall>x y. v x \<le> n \<and> v y \<le> n \<and> v x = v y \<longrightarrow> x = y"
    "finite cs"
  shows "u \<turnstile>\<^bsub>v,n\<^esub> cs_to_dbm v cs \<longleftrightarrow> u \<Turnstile>\<^sub>c\<^sub>s cs"
  using assms by (blast intro: cs_to_dbm1 cs_to_dbm2)

corollary cs_to_dbm_correct':
  assumes
    "bij_betw v (cs_vars cs) {1..n}" "\<forall>x. v x \<le> n \<longrightarrow> v x > 0" "\<forall>x. x \<notin> cs_vars cs \<longrightarrow> v x > n"
    "finite cs"
  shows "u \<turnstile>\<^bsub>v,n\<^esub> cs_to_dbm v cs \<longleftrightarrow> u \<Turnstile>\<^sub>c\<^sub>s cs"
proof (rule cs_to_dbm_correct , safe)
  fix x assume "x \<in> cs_vars cs"
  then show "v x \<le> n"
    using assms(1) unfolding bij_betw_def by auto
next
  fix x assume "v x \<le> n"
  then show "0 < v x"
    using assms(2) by blast
next
  fix x y :: 'a
  assume A: "v x \<le> n" "v y \<le> n" "v x = v y"
  with A assms show "x = y"
    unfolding bij_betw_def by (auto dest!: inj_onD)
next
  show "finite cs"
    by (rule assms)
qed


section \<open>Application: Up On Constraint Systems\<close>
text \<open>The following is a sample application of viewing DBMs as constraint systems.
We show define an equivalent of the @{term up} operation on DBMs, prove it correct,
and then derive an alternative correctness proof for @{term up}.
\<close>
definition
  "up_cs cs = {c. c \<in> cs \<and> (case c of Upper _ _ \<Rightarrow> False | _ \<Rightarrow> True)}"

lemma Lower_shiftI:
  "u \<oplus> d \<Turnstile>\<^sub>c Lower x e" if "u \<Turnstile>\<^sub>c Lower x e" "(d :: 't :: linordered_ab_group_add) \<ge> 0"
  using that
  apply (cases e)
    apply (auto simp: constr_sem_less_eq_iff)
  using diff_mono apply fastforce
  using less_trans not_less_iff_gr_or_eq apply fastforce
  done

lemma Upper_shiftI:
  "u \<oplus> d \<Turnstile>\<^sub>c Upper x e" if "u \<Turnstile>\<^sub>c Upper x e" "(d :: 't :: linordered_ab_group_add) \<le> 0"
  using that
  apply (cases e)
    apply (auto simp: constr_sem_less_eq_iff)
   apply (simp add: add.commute add_decreasing; fail)
  using add_less_le_mono apply fastforce
  done

lemma Diff_shift:
  "u \<oplus> d \<Turnstile>\<^sub>c Diff x y e \<longleftrightarrow> u \<Turnstile>\<^sub>c Diff x y e" for d :: "'t :: linordered_ab_group_add"
  by (cases e) (auto simp: constr_sem_less_eq_iff)

lemma up_cs_complete:
  "u \<oplus> d \<Turnstile>\<^sub>c\<^sub>s up_cs cs" if "u \<Turnstile>\<^sub>c\<^sub>s cs" "d \<ge> 0" for d :: "'t :: linordered_ab_group_add"
  using that unfolding up_cs_def cs_sem_def
  apply clarsimp
  subgoal for x
    by (cases x) (auto simp: Diff_shift intro: Lower_shiftI)
  done


definition
  "lower_upper_closed cs \<equiv> \<forall>x y e e'.
    Lower x e \<in> cs \<and> Upper y e' \<in> cs \<longrightarrow> (\<exists> e''. Diff y x e'' \<in> cs \<and> e'' \<le> e + e')"

lemma up_cs_sound:
  assumes "u \<Turnstile>\<^sub>c\<^sub>s up_cs cs" "lower_upper_closed cs" "finite cs"
  obtains u' and d :: "'t :: time" where "d \<ge> 0" "u' \<Turnstile>\<^sub>c\<^sub>s cs" "u = u' \<oplus> d"
proof -
  define U and L and LT where
    "U \<equiv> {e  + Le (-u x) | x e. Upper x e \<in> cs \<and> e \<noteq> \<infinity>}"
    and "L \<equiv> {-e + Le (-u x) | x e. Lower x e \<in> cs \<and> e \<noteq> \<infinity>}"
    and "LT \<equiv> {Le (-d - u x) | x d. Lower x (Lt d) \<in> cs}"
  note defs = U_def L_def LT_def
  let ?l = "Max L" and ?u = "Min U"
  have "LT \<subseteq> L"
    by (force simp: DBM_arith_defs defs)
  have Diff_semD: "u \<Turnstile>\<^sub>c Diff y x (e + e')" if "Lower x e \<in> cs" "Upper y e' \<in> cs" for x y e e'
  proof -
    from assms that obtain e'' where "Diff y x e'' \<in> cs" "e'' \<le> e + e'"
      unfolding lower_upper_closed_def cs_equiv_def by blast
    with assms(1) show ?thesis
      unfolding cs_sem_def up_cs_def by (auto intro: constr_sem_mono)
  qed
  have Lower_semD: "u \<Turnstile>\<^sub>c Lower x e" if "Lower x e \<in> cs" for x e
    using that assms unfolding cs_sem_def up_cs_def by auto
  have Lower_boundI: "-e + Le (-u x) \<le> 0" if "Lower x e \<in> cs" "e \<noteq> \<infinity>" for x e
    using Lower_semD[OF that(1)] that(2) unfolding constr_sem_less_eq_iff
    by (intro DBMEntry_le_to_sum)
  from \<open>finite cs\<close> have "finite L"
    unfolding defs
    by (force intro: finite_subset[where B = "(\<lambda>c. case c of Lower x e \<Rightarrow> - e + Le (- u x)) ` cs"])
  from \<open>finite cs\<close> have "finite U"
    unfolding defs
    by (force intro: finite_subset[where B = "(\<lambda>c. case c of Upper x e \<Rightarrow> e + Le (- u x)) ` cs"])
  note L_ge = Max_ge[OF \<open>finite L\<close>] and U_le = Min_le[OF \<open>finite U\<close>]
  have L_0: "Max L \<le> 0" if "L \<noteq> {}"
    by (intro Max.boundedI \<open>finite L\<close> that) (auto intro: Lower_boundI simp: defs)
  have L_U: "Max L \<le> Min U" if "L \<noteq> {}" "U \<noteq> {}"
    apply (intro Max_le_MinI \<open>finite L\<close> \<open>finite U\<close> that)
    apply (clarsimp simp: defs)
    apply (drule (1) Diff_semD)
    subgoal for x y e e'
      unfolding constr_sem_less_eq_iff
      by (cases e; cases e'; simp add: DBM_arith_defs; simp add: algebra_simps)
    done
  consider
    (L_empty) "L = {}" | (Lt_empty) "LT = {}" | (L_gt_Lt) "Max L > Max LT" |
    (Lt_Max) x d where "Lower x (Lt d) \<in> cs" "Le (-d - u x) \<in> LT" "Max L = Le (-d - u x)"
    by (smt finite_subset Max_in Max_mono \<open>finite L\<close> \<open>LT \<subseteq> L\<close> less_le mem_Collect_eq defs)
  note L_Lt_cases = this
  have Lt_Max_rule: "- c - u x < 0"
    if "Lower x (Lt c) \<in> cs" "Max L = Le (- c - u x)" "L \<noteq> {}" for c x
    using that
    by (metis DBMEntry.distinct(1) L_0 Le_le_LeD Le_less_Lt Lower_semD
          add.inverse_inverse constr_sem_less_eq_iff(1) eq_iff_diff_eq_0 less_le neutral)
  have LT_0_boundI: "\<exists>d \<le> 0. (\<forall>l \<in> L. l \<le> Le d) \<and> (\<forall>l \<in> LT. l < Le d)" if \<open>L \<noteq> {}\<close>
  proof -
    obtain d where d: "?l \<le> Le d" "d \<le> 0"
      by (metis L_0 \<open>L \<noteq> {}\<close> neutral order_refl)
    show ?thesis
    proof (cases rule: L_Lt_cases)
      case L_empty
      with \<open>L \<noteq> {}\<close> show ?thesis
        by simp
    next
      case Lt_empty
      then show ?thesis
        by (smt L_ge d(1,2) empty_iff leD leI less_le_trans)
    next
      case L_gt_Lt
      then show ?thesis
        by (smt finite_subset Max_ge \<open>finite L\<close> \<open>LT \<subseteq> L\<close> d(1,2) leD leI less_le_trans)
    next
      case (Lt_Max x c)
      define d where "d \<equiv> - c - u x"
      from Lt_Max(1,3) \<open>L \<noteq> {}\<close> have "d < 0"
        unfolding d_def by (rule Lt_Max_rule)
      then obtain d' where d': "d < d'" "d' < 0"
        using dense by auto
      have "\<forall>l \<in> L. l < Le d'"
      proof safe
        fix l
        assume "l \<in> L"
        then have "l \<le> Le d"
          unfolding d_def \<open>Max L = _\<close>[symmetric] by (rule L_ge)
        also from d' have "\<dots> < Le d'"
          by auto
        finally show "l < Le d'" .
      qed
      with Lt_Max(1,3) d' \<open>finite L\<close> \<open>L \<noteq> {}\<close> \<open>LT \<subseteq> L\<close> show ?thesis
        by (intro exI[of _ d']) auto
    qed
  qed
  consider
      (none)   "L = {}" "U = {}"
    | (upper)  "L = {}" "U \<noteq> {}"
    | (lower)  "L \<noteq> {}" "U = {}"
    | (proper) "L \<noteq> {}" "U \<noteq> {}"
    by force
  text \<open>The main statement of of the proof. Note that most of the lengthiness of the proof is
  owed to the third conjunct. Our initial hope was that this conjunct would not be needed.\<close>
  then obtain d where d: "d \<le> 0" "\<forall>l \<in> L. l \<le> Le d" "\<forall>l \<in> LT. l < Le d" "\<forall>u \<in> U. Le d \<le> u"
  proof cases
    case none
    then show ?thesis
      by (intro that[of 0]) (auto simp: defs)
  next
    case upper
    obtain d where "Le d \<le> Min U" "d \<le> 0"
      by (smt DBMEntry.distinct(3) add_inf(2) any_le_inf neg_le_0_iff_le DBM.neutral
            order.not_eq_order_implies_strict sum_gt_neutral_dest')
    then show ?thesis
      using upper \<open>finite U\<close> by (intro that[of d]) (auto simp: defs)
  next
    case lower
    obtain d where d: "Max L \<le> Le d" "d \<le> 0"
      by (smt L_0 lower(1) neutral order_refl)
    show ?thesis
    proof (cases rule: L_Lt_cases)
      case L_empty
      with lower(1) show ?thesis
        by simp
    next
      case Lt_empty
      then show ?thesis
        by (metis (lifting) L_ge d(1,2) empty_iff leD leI less_le_trans lower(2) that)
    next
      case L_gt_Lt
      then show ?thesis
        by (smt finite_subset Max_ge \<open>finite L\<close> \<open>LT \<subseteq> L\<close> d(1,2) empty_iff
              leD leI less_le_trans lower(2) that)
    next
      case (Lt_Max x c)
      define d where "d \<equiv> - c - u x"
      from Lt_Max(1,3) lower(1) have "d < 0"
        unfolding d_def by (rule Lt_Max_rule)
      then obtain d' where d': "d < d'" "d' < 0"
        using dense by auto
      have "\<forall>l \<in> L. l < Le d'"
      proof safe
        fix l
        assume "l \<in> L"
        then have "l \<le> Le d"
          unfolding d_def \<open>Max L = _\<close>[symmetric] by (rule L_ge)
        also from d' have "\<dots> < Le d'"
          by auto
        finally show "l < Le d'" .
      qed
      with Lt_Max(1,3) d' \<open>finite L\<close> lower \<open>LT \<subseteq> L\<close> show ?thesis
        by (intro that[of d']) auto
    qed
  next
    case proper
    with L_U L_0 have "Max L \<le> Min U" "Max L \<le> 0"
      by auto
    from \<open>finite U\<close> \<open>U \<noteq> {}\<close> have "?u \<in> U"
      unfolding U_def by (rule Min_in)
    have main:
      "\<exists>d'. -d - u x < d' \<and> Le d' < ?u"
      if "Lower x (Lt d) \<in> cs" "Le (-d - u x) \<in> LT" "?l = Le (-d - u x)" for d x
    proof (cases ?u)
      case (Le d')
      with \<open>?u \<in> U\<close> obtain e y where *: "Le d' = e + Le (- u y)" "Upper y e \<in> cs"
        unfolding U_def by auto
      then obtain d1 where "e = Le d1"
        by (cases e) (auto simp: DBM_arith_defs)
      with * have "d' = d1 - u y"
        by (auto simp: DBM_arith_defs)
      from Diff_semD[OF \<open>Lower x (Lt d) \<in> cs\<close> \<open>Upper y e \<in> _\<close>] have "u y - u x < d + d1"
        unfolding constr_sem_less_eq_iff \<open>e = _\<close> by (simp add: DBM_arith_defs)
      then have "- d - u x < d'"
        unfolding \<open>d' = _\<close> by (simp add: algebra_simps)
      then obtain d1 where "-d - u x < d1" "d1 < d'"
        using dense by auto
      with \<open>?u = _\<close> show ?thesis
        by (intro exI[where x = d1]) auto
    next
      case (Lt d')
      with \<open>?u \<in> U\<close> obtain e y where *: "Lt d' = e + Le (- u y)" "Upper y e \<in> cs"
        unfolding U_def by auto
      then obtain d1 where "e = Lt d1"
        by (cases e) (auto simp: DBM_arith_defs)
      with * have "d' = d1 - u y"
        by (auto simp: DBM_arith_defs)
      from Diff_semD[OF \<open>Lower x (Lt d) \<in> cs\<close> \<open>Upper y e \<in> _\<close>] have "u y - u x < d + d1"
        unfolding constr_sem_less_eq_iff \<open>e = _\<close> by (simp add: DBM_arith_defs)
      then have "- d - u x < d'"
        unfolding \<open>d' = _\<close> by (simp add: algebra_simps)
      then obtain d1 where "-d - u x < d1" "d1 < d'"
        using dense by auto
      with \<open>?u = _\<close> show ?thesis
        by (intro exI[where x = d1]) auto
    next
      case INF
      with \<open>?u \<in> U\<close> show ?thesis
        using Lt_Max_rule proper(1) that(1,3) by fastforce
    qed
    consider (eq) "Max L = Min U" | (0) "Min U \<ge> 0" | (gt) "Max L < Min U" "Min U < 0"
      using \<open>Max L \<le> Min U\<close> by fastforce
    then show ?thesis
    proof cases
      case eq
      from proper \<open>finite L\<close> \<open>finite U\<close> have "?l \<in> L" "?u \<in> U"
        by - (rule Max_in Min_in; assumption)+
      then obtain x y e e' where *:
        "?l = - e + Le (- u x)" "Lower x e \<in> cs" "e \<noteq> \<infinity>"
        "?u = e' + Le (- u y)" "Upper y e' \<in> cs" "e' \<noteq> \<infinity>"
        unfolding defs by auto
      with \<open>?l = ?u\<close> obtain d where d: "?l = Le d"
        apply (cases e; cases e'; simp add: DBM_arith_defs)
        subgoal for a b
        proof -
          assume prems: "- a - u x = b - u y" "e = Le a" "e' = Lt b"
          from * have "u \<Turnstile>\<^sub>c Diff y x (e + e')"
            by (intro Diff_semD)
          with prems have False
            by (simp add: DBM_arith_defs constr_sem_less_eq_iff algebra_simps)
          then show ?thesis ..
        qed
        done
      from \<open>?l \<le> 0\<close> have **: "d \<le> 0" "\<forall>l \<in> L. l \<le> Le d" "\<forall>u \<in> U. Le d \<le> u"
          apply (simp add: DBM.neutral d; fail)
         apply (auto simp: d[symmetric] intro: L_ge; fail)
        apply (auto simp: d[symmetric] eq intro: U_le; fail)
        done
      show ?thesis
      proof (cases rule: L_Lt_cases)
        case L_empty
        with \<open>L \<noteq> {}\<close> show ?thesis
          by simp
      next
        case Lt_empty
        with ** show ?thesis
          by (intro that[of d]) auto
      next
        case L_gt_Lt
        with ** show ?thesis
          by (intro that[of d]; simp)
             (metis finite_subset Max_ge \<open>LT \<subseteq> L\<close> \<open>finite L\<close> d le_less_trans)
      next
        case (Lt_Max y d1)
        from main[OF this] obtain d' where "d' > - d1 - u y" "Le d' < Min U"
          by auto
        with ** Lt_Max(3)[symmetric] d eq show ?thesis
          by (intro that[of d']; simp)
      qed
    next
      case 0
      from LT_0_boundI[OF \<open>L \<noteq> {}\<close>] obtain d where "d \<le> 0" "\<forall>l\<in>L. l \<le> Le d" "\<forall>l\<in>LT. l < Le d"
        by safe
      with \<open>Max L \<le> 0\<close> \<open>finite L\<close> \<open>finite U\<close> proper 0 show ?thesis
        by (intro that[of d]) (auto simp: DBM.neutral intro: order_trans)
    next
      case gt
      then obtain d where d: "Max L \<le> Le d" "Le d \<le> Min U"
        by (elim Le_in_between)
      with \<open>_ < 0\<close> have "Le d < 0"
        by auto
      then have "d \<le> 0"
        by (simp add: neutral)
      show ?thesis
      proof (cases rule: L_Lt_cases)
        case L_empty
        with \<open>L \<noteq> {}\<close> show ?thesis
          by simp
      next
        case Lt_empty
        with d \<open>d \<le> 0\<close> show ?thesis
          using proper \<open>finite L\<close> \<open>finite U\<close> by (intro that[of d]) (auto intro: L_ge U_le)
      next
        case L_gt_Lt
        with d \<open>d \<le> 0\<close> proper \<open>finite L\<close> \<open>finite U\<close> show ?thesis
          by (intro that[of d]) (auto intro: L_ge U_le; fail
              | meson finite_subset Max_ge \<open>LT \<subseteq> L\<close> le_less_trans less_le_trans)+
      next
        case (Lt_Max y d1)
        from main[OF this] obtain d' where d': "d' > - d1 - u y" "Le d' < Min U"
          by auto
        with d have d_bounds: "?l < Le d'" "Le d' \<le> ?u"
          unfolding \<open>?l = _\<close> by auto
        from \<open>?l < Le d'\<close> have "\<forall>l \<in> L. l < Le d'"
          using Max_less_iff \<open>finite L\<close> by blast
        moreover from \<open>Le d' \<le> ?u\<close> \<open>?u < 0\<close> have "d' \<le> 0"
          by (metis Le_le_LeD le_less_trans neutral order.strict_iff_order)
        with d Lt_Max(3)[symmetric] d_bounds d' \<open>LT \<subseteq> L\<close> show ?thesis
          using proper \<open>finite L\<close> \<open>finite U\<close>
          by (intro that[of d']; auto)
      qed
    qed
  qed
  have "u \<oplus> d \<Turnstile>\<^sub>c\<^sub>s cs"
    unfolding cs_sem_def
  proof clarsimp
    fix c :: "('a, 't) constr"
    assume "c \<in> cs"
    show "u \<oplus> d \<Turnstile>\<^sub>c c"
    proof (cases c)
      case (Lower x e)
      show ?thesis
      proof (cases "e = \<infinity>")
        case True
        with \<open>c = _\<close> show ?thesis
          by (auto simp: constr_sem_less_eq_iff)
      next
        case False
        with \<open>c = _\<close> \<open>c \<in> _\<close> have "-e + Le (-u x) \<in> L"
          unfolding defs by auto
        with d have "-e + Le (-u x) \<le> Le d"
          by auto
        then show ?thesis
          using d(3) \<open>c \<in> _\<close> unfolding \<open>c = _\<close> constr_sem_less_eq_iff
          apply (cases e; simp add: defs DBM_arith_defs)
           apply (metis diff_le_eq minus_add_distrib minus_le_iff uminus_add_conv_diff)
          apply (metis ab_group_add_class.ab_diff_conv_add_uminus leD le_less less_diff_eq
                minus_diff_eq neg_less_iff_less)
          done
      qed
    next
      case (Upper x e)
      show ?thesis
      proof (cases "e = \<infinity>")
        case True
        with \<open>c = _\<close> show ?thesis
          by (auto simp: constr_sem_less_eq_iff)
      next
        case False
        with \<open>c = _\<close> \<open>c \<in> _\<close> have "e + Le (-u x) \<in> U"
          by (auto simp: defs)
        with d show ?thesis
          by (cases e) (auto simp: \<open>c = _\<close> constr_sem_less_eq_iff DBM_arith_defs algebra_simps)
      qed
    next
      case (Diff x y e)
      with assms \<open>c \<in> cs\<close> show ?thesis
        by (auto simp: Diff_shift cs_sem_def up_cs_def)
    qed
  qed
  with \<open>d \<le> 0\<close> show ?thesis
    by (intro that[of "-d" "u \<oplus> d"]; simp add: cval_add_def)
qed
text \<open>Note that if we compare this proof to @{thm DBM_up_sound'}, we can see that we have
not gained much. Settling on DBM entry arithmetic as done above was not the optimal choice for this
proof, while it can drastically simply some other proofs.
Also, note that the final theorem we obtain below (\<open>DBM_up_correct\<close>)
is slightly stronger than what we would get with @{thm DBM_up_sound'}.
Finally, note that a more elegant definition of @{term lower_upper_closed} would probably be:
\<comment> \<open>
definition
  "lower_upper_closed cs \<equiv> \<forall>x y e e'.
    cs \<Turnstile> Lower x e \<and> cs \<Turnstile> Upper y e' \<longrightarrow> (\<exists> e''. cs \<Turnstile> Diff y x e'' \<and> e'' \<le> e + e')"\<close>
This would mean that in the proof we would have to replace minimum and maximum by
supremum and infimum. The advantage would be that the finiteness assumption could be removed. 
However, as our DBM entries do not come with \<open>-\<infinity>\<close>, they do not form a complete lattice.
Thus we would either have to make this extension or directly refer to the embedded values
directly, which would again have to form a complete lattice.
Both variants come with some technical inconvenience.
\<close>

lemma up_cs_sem:
  fixes cs :: "('x, 'v :: time) cs"
  assumes "lower_upper_closed cs" "finite cs"
  shows "{u. u \<Turnstile>\<^sub>c\<^sub>s up_cs cs} = {u \<oplus> d | u d. u \<Turnstile>\<^sub>c\<^sub>s cs \<and> d \<ge> 0}"
  by safe (metis up_cs_sound up_cs_complete assms)+

definition
  close_lu :: "('t::linordered_cancel_ab_semigroup_add) DBM \<Rightarrow> 't DBM"
where
  "close_lu M \<equiv> \<lambda>i j. if i > 0 then min (dbm_add (M i 0) (M 0 j)) (M i j) else M i j"

definition
  up' :: "('t::linordered_cancel_ab_semigroup_add) DBM \<Rightarrow> 't DBM"
where
  "up' M \<equiv> \<lambda>i j. if i > 0 \<and> j = 0 then \<infinity> else M i j"

lemma up_alt_def:
  "up M = up' (close_lu M)"
  by (intro ext) (simp add: up_def up'_def close_lu_def)

lemma close_lu_equiv:
  fixes M :: "'t ::time DBM"
  shows "dbm_to_cs n v M \<equiv>\<^sub>c\<^sub>s dbm_to_cs n v (close_lu M)"
  unfolding cs_equiv_def dbm_to_cs_correct[symmetric]
    DBM_val_bounded_def close_lu_def dbm_entry_val_constr_sem_iff
  apply (auto simp: min_def DBM.add[symmetric])
  unfolding constr_sem_less_eq_iff
  unfolding DBM.less_eq[symmetric] DBM.neutral[symmetric]
            apply (simp add: add_increasing2; fail)
           apply (metis le0)+
  subgoal premises prems for u c1 c2
  proof -
    have "Le (u c1 - u c2) = Le (u c1) + Le (- u c2)"
      by (simp add: DBM_arith_defs)
    also from prems have "\<dots> \<le> M (v c1) 0 + M 0 (v c2)"
      by (intro add_mono) auto
    finally show ?thesis .
  qed
  by (smt leI le_zero_eq order_trans | metis le0)+

lemma close_lu_closed:
  "lower_upper_closed (dbm_to_cs n v (close_lu M))" if "M 0 0 \<ge> 0"
  using that unfolding lower_upper_closed_def dbm_to_cs_def close_lu_def
  apply (clarsimp; safe)
  subgoal
    by auto
  subgoal for x y
    by (auto simp: DBM.add[symmetric])
       (metis add.commute add.right_neutral add_left_mono min.absorb2 min.cobounded1)
  by (simp add: add_increasing2)

lemma close_lu_closed':
  "lower_upper_closed (dbm_to_cs n v (close_lu M) \<union> dbm_to_cs n v M)" if "M 0 0 \<ge> 0"
  using that unfolding lower_upper_closed_def dbm_to_cs_def close_lu_def
  apply (clarsimp; safe)
  subgoal
    by auto
  subgoal for x y
    by (metis DBM.add add.commute add.right_neutral add_left_mono min.absorb2 min.cobounded1)
  subgoal for x y
    by (metis DBM.add add.commute min.cobounded1)
  by (simp add: add_increasing2)

lemma up_cs_up'_equiv:
  fixes M :: "'t ::time DBM"
  assumes "M 0 0 \<ge> 0" "clock_numbering v"
  shows "up_cs (dbm_to_cs n v M) \<equiv>\<^sub>c\<^sub>s dbm_to_cs n v (up' M)"
  using assms
  unfolding up'_def up_cs_def cs_equiv_def dbm_to_cs_correct[symmetric]
    DBM_val_bounded_def close_lu_def dbm_entry_val_constr_sem_iff
  by (auto split: if_split_asm
      simp: dbm_to_cs_def cs_sem_def DBM.add[symmetric] DBM.less_eq[symmetric] DBM.neutral)

lemma up_equiv_cong:
  fixes cs cs' :: "('x, 'v :: time) cs"
  assumes "cs \<equiv>\<^sub>c\<^sub>s cs'" "finite cs" "finite cs'" "lower_upper_closed cs" "lower_upper_closed cs'"
  shows "up_cs cs \<equiv>\<^sub>c\<^sub>s up_cs cs'"
  using assms unfolding cs_equiv_def by (metis up_cs_complete up_cs_sound)

lemma DBM_up_correct:
  fixes M :: "'t ::time DBM"
  assumes "clock_numbering v" "finite {x. v x \<le> n}"
  shows "u \<in> ([M]\<^bsub>v,n\<^esub>)\<^sup>\<up> \<longleftrightarrow> u \<in> [up M]\<^bsub>v,n\<^esub>"
proof (cases "M 0 0 \<ge> 0")
  case True
  have "u \<in> ([M]\<^bsub>v,n\<^esub>)\<^sup>\<up> \<longleftrightarrow> (\<exists>d u'. u' \<turnstile>\<^bsub>v,n\<^esub> M \<and> d \<ge> 0 \<and> u = u' \<oplus> d)"
    unfolding DBM_zone_repr_def zone_delay_def by auto
  also have "\<dots> \<longleftrightarrow> (\<exists>d u'. u' \<Turnstile>\<^sub>c\<^sub>s dbm_to_cs n v M \<and> d \<ge> 0 \<and> u = u' \<oplus> d)"
    unfolding dbm_to_cs_correct ..
  also have "\<dots> \<longleftrightarrow> (\<exists>d u'. u' \<Turnstile>\<^sub>c\<^sub>s dbm_to_cs n v (close_lu M) \<and> d \<ge> 0 \<and> u = u' \<oplus> d)"
    using cs_equivD close_lu_equiv cs_equiv_sym by metis
  also have "\<dots> \<longleftrightarrow> u \<Turnstile>\<^sub>c\<^sub>s up_cs (dbm_to_cs n v (close_lu M))"
  proof safe
    fix d u'
    assume "u' \<Turnstile>\<^sub>c\<^sub>s dbm_to_cs n v (close_lu M)"
      and "0 \<le> d"
      and "u = u' \<oplus> d"
    then show "u' \<oplus> d \<Turnstile>\<^sub>c\<^sub>s up_cs (dbm_to_cs n v (close_lu M))"
      by (intro up_cs_complete)
  next
    let ?cs = "dbm_to_cs n v M" and ?cs' = "dbm_to_cs n v (close_lu M)"
    assume A: "u \<Turnstile>\<^sub>c\<^sub>s up_cs ?cs'"
    have "?cs' \<equiv>\<^sub>c\<^sub>s ?cs"
      by (intro close_lu_equiv cs_equiv_sym)
    then have "?cs' \<union> ?cs \<equiv>\<^sub>c\<^sub>s ?cs'"
      by - (rule cs_equiv_sym, rule cs_equiv_union)
    moreover have "lower_upper_closed (?cs' \<union> ?cs)" "lower_upper_closed ?cs'"
      by (intro close_lu_closed' close_lu_closed True)+
    moreover have "finite ?cs'" "finite (?cs' \<union> ?cs)"
      by (intro finite_dbm_to_cs assms finite_UnI)+
    moreover have "u \<Turnstile>\<^sub>c\<^sub>s up_cs (?cs' \<union> ?cs)"
      by (rule cs_equivD, rule A, rule up_equiv_cong, rule cs_equiv_sym) fact+
    ultimately show "\<exists>d u'. u' \<Turnstile>\<^sub>c\<^sub>s dbm_to_cs n v (close_lu M) \<and> 0 \<le> d \<and> u = u' \<oplus> d"
      by - (rule up_cs_sound, assumption+, auto)
  qed
  also have "\<dots> \<longleftrightarrow> u \<Turnstile>\<^sub>c\<^sub>s dbm_to_cs n v (up' (close_lu M))"
  proof -
    from \<open>M 0 0 \<ge> 0\<close> have "up_cs (dbm_to_cs n v (close_lu M)) \<equiv>\<^sub>c\<^sub>s dbm_to_cs n v (up' (close_lu M))"
      by (intro up_cs_up'_equiv[OF _ \<open>clock_numbering v\<close>], simp add: close_lu_def)
    then show ?thesis
      using cs_equivD cs_equiv_sym by metis
  qed
  also have "\<dots> \<longleftrightarrow> u \<Turnstile>\<^sub>c\<^sub>s dbm_to_cs n v (up M)"
    unfolding up_alt_def ..
  also have "\<dots> \<longleftrightarrow> u \<turnstile>\<^bsub>v,n\<^esub> up M"
    unfolding dbm_to_cs_correct ..
  also have "\<dots> \<longleftrightarrow> u \<in> [up M]\<^bsub>v,n\<^esub>"
    unfolding DBM_zone_repr_def by blast
  finally show ?thesis .
next
  case False
  then have "M 0 0 < 0"
    by auto
  then have "up M 0 0 < 0"
    unfolding up_def by auto
  with \<open>M 0 0 < 0\<close> have "[M]\<^bsub>v,n\<^esub> = {}" "[up M]\<^bsub>v,n\<^esub> = {}"
    by (auto intro!: DBM_triv_emptyI)
  then show ?thesis
    unfolding zone_delay_def by blast
qed

end
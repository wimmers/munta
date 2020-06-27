theory UPPAAL_Asm_AbsInt_Flat
  imports UPPAAL_Asm
begin

subsection "Stepping"

inductive steps_exact :: "program \<Rightarrow> fuel \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
  "steps_exact prog 0 start start" |
  "steps_exact prog (Suc n) (pc, st) s'" if
    "step cmd (pc, st) = Some s"
    "prog pc = Some cmd"
    "steps_exact prog n s s'"

lemma steps_exact_zero:
  assumes "steps_exact prog 0 ins outs"
  shows "ins = outs"
  using assms by cases simp

lemma steps_exact_suc_fwd:
  assumes "steps_exact prog (Suc n) ins outs"
  shows "\<exists>ims. (steps_exact prog 1 ins ims) \<and> (steps_exact prog n ims outs)"
  using assms
proof (cases)
  case (2 cmd pc st ims)
  from this have "steps_exact prog 1 ins ims" using steps_exact.intros(1) steps_exact.intros(2) by auto
  from this 2 show ?thesis by blast
qed

lemma steps_exact_suc_bwd:
  assumes "\<exists>ims. (steps_exact prog 1 ins ims) \<and> (steps_exact prog n ims outs)"
  shows "steps_exact prog (Suc n) ins outs"
proof -
  from assms obtain ims where parts: "steps_exact prog 1 ins ims" "steps_exact prog n ims outs" by blast
  from this(1) show ?thesis
  proof(cases)
    case 1
    then show ?thesis by simp
  next
    case (2 cmd pc st s)
    from this parts have "s = ims" using steps_exact_zero by auto
    from 2 this have "step cmd (pc, st) = Some ims" by simp
    from this 2(4) parts(2) have "steps_exact prog (Suc n) (pc, st) outs" using steps_exact.intros(2) by blast
    from this 2 show ?thesis by simp
  qed
qed

lemma steps_exact_suc: "(steps_exact prog (Suc n) ins outs) \<longleftrightarrow> (\<exists>ims. (steps_exact prog 1 ins ims) \<and> (steps_exact prog n ims outs))"
  using steps_exact_suc_bwd steps_exact_suc_fwd by blast

lemma steps_exact_chain:
  assumes "steps_exact prog a ins ims" "steps_exact prog b ims outs"
  shows "steps_exact prog (a + b) ins outs"
using assms proof (induction a arbitrary: ins ims outs)
  case 0
  hence "ins = ims" using steps_exact_zero by simp
  from this 0 show ?case by simp
next
  case (Suc a)
  from this(2) have "\<exists>ins'. (steps_exact prog 1 ins ins') \<and> (steps_exact prog a ins' ims)" using steps_exact_suc_fwd by simp
  then obtain ins' where "(steps_exact prog 1 ins ins') \<and> (steps_exact prog a ins' ims)" by blast
  from this Suc.IH Suc.prems(2) have "steps_exact prog (Suc (a + b)) ins outs" using steps_exact_suc_bwd by blast
  then show ?case using steps_exact_suc_bwd using add_Suc by presburger
qed

inductive steps_upto :: "program \<Rightarrow> fuel \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
  "count \<le> n \<Longrightarrow> steps_exact prog count start end \<Longrightarrow> steps_upto prog n start end"

lemma steps_upto_zero:
  assumes "steps_upto prog 0 ins outs"
  shows "ins = outs"
  using assms by cases (simp add: steps_exact_zero)

lemma steps_upto_further:
  "n \<le> m \<Longrightarrow> steps_upto prog n start end \<Longrightarrow> steps_upto prog m start end"
  by (meson le_trans steps_upto.simps)

lemma steps_upto_suc_fwd:
  assumes "steps_upto prog (Suc n) ins outs"
  shows "\<exists>ims. (steps_upto prog 1 ins ims) \<and> (steps_upto prog n ims outs)"
using assms proof(cases)
  case (1 count)
  then show ?thesis
  proof(cases count)
    case 0 then show ?thesis using 1(2) steps_exact.intros(1) steps_upto.intros by blast
  next
    case (Suc count')
    from this 1(2) have "steps_exact prog (Suc count') ins outs" by blast
    from this obtain ims where "steps_exact prog 1 ins ims" "steps_exact prog count' ims outs" using steps_exact_suc_fwd by blast
    hence "steps_upto prog 1 ins ims \<and> steps_upto prog count' ims outs" using steps_upto.simps by auto
    then show ?thesis using steps_upto_further 1(1) Suc by blast
  qed
qed

lemma steps_upto_suc_bwd:
  assumes "\<exists>ims. (steps_upto prog 1 ins ims) \<and> (steps_upto prog n ims outs)"
  shows "steps_upto prog (Suc n) ins outs"
proof -
  from assms obtain ims where parts: "steps_upto prog 1 ins ims" "steps_upto prog n ims outs" by blast
  from parts(1) have "\<exists>countl. countl \<le> 1 \<and> steps_exact prog countl ins ims" by cases blast
  then obtain countl where countl: "countl \<le> 1 \<and> steps_exact prog countl ins ims" by blast
  from parts(2) have countr_ex: "\<exists>countr. countr \<le> n \<and> steps_exact prog countr ims outs" by cases blast
  then obtain countr where countr: "countr \<le> n \<and> steps_exact prog countr ims outs" by blast
  from countl countr have add_le: "(countl + countr) \<le> Suc n" by simp
  from countl countr have add_chain: "steps_exact prog (countl + countr) ins outs" using steps_exact_chain by blast
  from add_le add_chain show ?thesis using steps_upto.intros by blast
qed

lemma steps_upto_suc:
  "steps_upto prog (Suc n) ins outs \<longleftrightarrow> (\<exists>ims. (steps_upto prog 1 ins ims) \<and> (steps_upto prog n ims outs))"
  using steps_upto_suc_fwd steps_upto_suc_bwd by blast

lemma steps_upto_chain:
  assumes "steps_upto prog a ins ims" "steps_upto prog b ims outs"
  shows "steps_upto prog (a + b) ins outs"
using assms proof (induction a arbitrary: ins ims outs)
  case 0
  hence "ins = ims" using steps_exact_zero by (simp add: steps_upto.simps)
  from this 0 show ?case by simp
next
  case (Suc a)
  from this(2) have "\<exists>ins'. (steps_upto prog 1 ins ins') \<and> (steps_upto prog a ins' ims)" using steps_upto_suc_fwd by simp
  then obtain ins' where "(steps_upto prog 1 ins ins') \<and> (steps_upto prog a ins' ims)" by blast
  from this Suc.IH Suc.prems(2) have "steps_upto prog (Suc (a + b)) ins outs" using steps_upto_suc_bwd by blast
  then show ?case using steps_upto_suc_bwd using add_Suc by presburger
qed

subsection "Flat Collecting"

definition step_all_flat :: "program \<Rightarrow> state set \<Rightarrow> state set" where
  "step_all_flat prog instates = {outst. \<exists>(pc, st)\<in>instates.\<exists>instr. prog pc = Some instr \<and> step instr (pc, st) = Some outst}"

inductive_set step_all_flat_induct for prog instates where
  "(pc, st) \<in> instates
    \<Longrightarrow> prog pc = Some instr
    \<Longrightarrow> step instr (pc, st) = Some outst
    \<Longrightarrow> outst \<in> step_all_flat_induct (prog::program) instates"

lemma "step_all_flat prog instates = step_all_flat_induct prog instates"
proof (standard)
  show "step_all_flat prog instates \<subseteq> step_all_flat_induct prog instates" using step_all_flat_def step_all_flat_induct.simps by fastforce
  show "step_all_flat_induct prog instates \<subseteq> step_all_flat prog instates"
  proof(standard)
    fix x assume "x \<in> step_all_flat_induct prog instates"
    thus "x \<in> step_all_flat prog instates" using step_all_flat_def by cases auto
  qed
qed

definition collect_step_flat :: "program \<Rightarrow> state set \<Rightarrow> state set" where
  "collect_step_flat prog instates = instates \<union> step_all_flat prog instates"

inductive_set collect_step_flat_induct for prog instates where
  keep: "st \<in> instates \<Longrightarrow> st \<in> collect_step_flat_induct prog instates" |
  step: "st \<in> step_all_flat_induct prog instates \<Longrightarrow> st \<in> collect_step_flat_induct prog instates"

lemma collect_step_flat_eq: "collect_step_flat prog instates = collect_step_flat_induct prog instates"
proof(standard)
  show "collect_step_flat prog instates \<subseteq> collect_step_flat_induct prog instates"
    using collect_step_flat_def collect_step_flat_induct.intros(1) collect_step_flat_induct.intros(2) step_all_flat_def step_all_flat_induct.intros by auto
  show "collect_step_flat_induct prog instates \<subseteq> collect_step_flat prog instates"
    using collect_step_flat_def collect_step_flat_induct.simps step_all_flat_def step_all_flat_induct.simps by fastforce
qed

lemma collect_step_flat_steps_exact:
  assumes "outs \<in> collect_step_flat_induct prog instates"
  shows "\<exists>ins\<in>instates. steps_upto prog 1 ins outs"
using assms proof(cases)
  case keep
  then show ?thesis using steps_exact.intros(1) steps_upto.intros by blast
next
  case step
  then show ?thesis
  proof(cases)
    case (1 pc st instr)
    hence "steps_exact prog 0 (pc, st) (pc, st)" using steps_exact.intros(1) by blast
    from 1 have exact: "steps_exact prog (Suc 0) (pc, st) outs" using steps_exact.intros(2) using steps_exact.simps by blast
    have n: "Suc 0 \<le> 1" using One_nat_def by simp
    from n exact have "steps_upto prog 1 (pc, st) outs" using steps_upto.intros by blast
    from this 1(1) show ?thesis by blast
  qed
qed

lemma step_in_collect_flat: "step_all_flat prog sts \<subseteq> collect_step_flat prog sts"
  by (simp add: collect_step_flat_def)

fun collect_flat_loop :: "program \<Rightarrow> fuel \<Rightarrow> state set \<Rightarrow> state set" where
  "collect_flat_loop _ 0 instates = instates" |
  "collect_flat_loop prog (Suc n) instates = collect_flat_loop prog n (collect_step_flat prog instates)"

lemma collect_flat_loop_correct:
  "collect_flat_loop prog n instates = {st. \<exists>ins\<in>instates. steps_upto prog n ins st}"
proof standard
  show "collect_flat_loop prog n instates \<subseteq> {st. \<exists>ins\<in>instates. steps_upto prog n ins st}"
  proof standard
    fix x assume "x \<in> collect_flat_loop prog n instates"
    hence "\<exists>ins\<in>instates. steps_upto prog n ins x"
    proof(induction n arbitrary: instates)
      case 0
      from this have nostep: "x \<in> instates" by simp
      have "steps_upto prog 0 x x" by (simp add: steps_exact.intros(1) steps_upto.intros)
      from this nostep show ?case by blast
    next
      case (Suc fuel)
      hence "\<exists>ins'\<in>(collect_step_flat prog instates). steps_upto prog fuel ins' x" by simp
      from this obtain "ins'" where ins': "ins' \<in> collect_step_flat prog instates" "steps_upto prog fuel ins' x" by blast
      from this(1) have "\<exists>ins\<in>instates. steps_upto prog 1 ins ins'" using collect_step_flat_steps_exact collect_step_flat_eq by auto
      from this ins' show ?case using steps_upto_suc_bwd by blast
    qed
    thus "x \<in> {st. \<exists>ins\<in>instates. steps_upto prog n ins st}" by blast
  qed

  show "{st. \<exists>ins\<in>instates. steps_upto prog n ins st} \<subseteq> collect_flat_loop prog n instates"
  proof standard
    fix x assume "x \<in> {st. \<exists>ins\<in>instates. steps_upto prog n ins st}"
    then obtain ins where ins: "ins \<in> instates" "steps_upto prog n ins x" by blast
    show "x \<in> collect_flat_loop prog n instates"
    using ins proof(induction n arbitrary: instates ins)
    case 0
      then show ?case using steps_upto_zero collect_flat_loop.simps(1) by blast
    next
      case (Suc n)
      from Suc(3) obtain ims where ims: "steps_upto prog 1 ins ims" "steps_upto prog n ims x" using steps_upto_suc by blast
      from this(2) Suc.prems(1) Suc.IH have continue: "\<And>imstates. ims \<in> imstates \<Longrightarrow> x \<in> collect_flat_loop prog n imstates" by blast
      from ims(1) this show ?case
      proof(cases)
        case (1 count)
        then show ?thesis
        proof(cases "count = 0")
          case True
          then show ?thesis by (metis "1"(2) Suc.prems(1) continue collect_step_flat_eq collect_step_flat_induct.keep collect_flat_loop.simps(2) steps_exact_zero)
        next
          case False
          from this 1 have "count = 1" by simp
          from this 1 have "steps_exact prog 1 ins ims" by simp
          then show ?thesis
          proof(cases)
            case 1 then show ?thesis by simp
          next
            case (2 cmd pc st s n)
            then show ?thesis using Suc.prems(1) collect_step_flat_eq collect_step_flat_induct.intros(2) continue step_all_flat_induct.intros steps_exact_zero by auto
          qed
        qed
      qed
    qed
  qed
qed

end
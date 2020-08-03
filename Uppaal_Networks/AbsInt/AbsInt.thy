theory AbsInt
imports
  Collect_Flat
  Uppaal_Networks.UPPAAL_Asm_Map
  "HOL.List"
  "HOL.Complete_Lattices"
begin

subsection "Abstract Stepping"

text \<open>Type for any abstract stepping function. Performs a single forward step on an abstract state.\<close>
type_synonym 'a astep = "instr \<Rightarrow> addr \<Rightarrow> 'a \<Rightarrow> 'a state_map"

fun astep_succs :: "('a::bot) astep \<Rightarrow> instr \<Rightarrow> addr \<Rightarrow> 'a \<Rightarrow> addr set" where
  "astep_succs f op ipc ins = domain (f op ipc ins)"

text \<open>Performs a step for all states in the map and returns the join of all resulting states at a given address.
  Could also be seen as inverse-stepping, i.e. pulling all resulting states ending at the given address.\<close>
fun slurp :: "'a::bot astep \<Rightarrow> program \<Rightarrow> 'a state_map \<Rightarrow> addr \<Rightarrow> 'a set" where
  "slurp f prog ctx pc = {ost. \<exists>ipc op. prog ipc = Some op \<and> lookup ctx ipc \<noteq> \<bottom> \<and> lookup (f op ipc (lookup ctx ipc)) pc = ost}"

text \<open>Perform a single step over an entire map\<close>
fun step_map :: "('a::{bot, Sup}) astep \<Rightarrow> program \<Rightarrow> 'a state_map \<Rightarrow> 'a state_map" where
  "step_map f prog ctx = SM (\<lambda>pc. \<Squnion>(slurp f prog ctx pc))"

text \<open>Advance the Abstract Interpretation one step forward, i.e. step the map and merge it with the previous.\<close>
fun advance :: "('a::{semilattice_sup, Sup, bot}) astep \<Rightarrow> program \<Rightarrow> 'a state_map \<Rightarrow> 'a state_map" where
  "advance f prog ctx = ctx \<squnion> step_map f prog ctx"

text \<open>Full Abstract Interpretation Loop, advancing n times\<close>
fun loop :: "('a::{semilattice_sup, Sup, bot}) astep \<Rightarrow> program \<Rightarrow> fuel \<Rightarrow> 'a state_map \<Rightarrow> 'a state_map" where
  "loop f prog 0 st = st" |
  "loop f prog (Suc n) st = loop f prog n (advance f prog st)"

lemma loop_pull: "loop f prog n (advance f prog st) = advance f prog (loop f prog n st)"
  by(induction n arbitrary: st, simp, metis loop.simps(2))

subsection "Collecting Semantics"

type_synonym collect_state = "stack * rstate * flag * nat list"
type_synonym collect_ctx = "collect_state set state_map"

subsubsection \<open>Conversion between Map and Flat Collecting\<close>

inductive_set states_at for states pc where
  "(pc, s) \<in> states \<Longrightarrow> s \<in> states_at states pc"

fun deepen :: "(addr * 'a) set \<Rightarrow> 'a set state_map" where
  "deepen states = SM (states_at states)"

lemma deepen_fwd: "(pc, st) \<in> flat \<Longrightarrow> st \<in> lookup (deepen flat) pc" by (simp add: states_at.intros)
lemma deepen_bwd: "st \<in> lookup (deepen flat) pc \<Longrightarrow> (pc, st) \<in> flat" by (simp add: states_at.simps)

inductive_set flatten for sm where
  "st \<in> lookup sm pc \<Longrightarrow> (pc, st) \<in> flatten sm"

lemma flatten_fwd: "st \<in> lookup deep pc \<Longrightarrow> (pc, st) \<in> flatten deep" by (simp add: flatten.intros)
lemma flatten_bwd: "(pc, st) \<in> flatten deep \<Longrightarrow> st \<in> lookup deep pc" by (meson flatten.cases)

lemma flatten_deepen: "flatten (deepen m) = m"
proof (intro Set.equalityI Set.subsetI)
  fix x assume ass: "x \<in> flatten (deepen m)"
  from ass obtain pc st where splitx: "x = (pc, st)" using prod.exhaust_sel by blast
  from ass this have "(pc, st) \<in> flatten (deepen m)" by blast
  hence "st \<in> lookup (deepen m) pc" by cases
  hence "st \<in> states_at m pc" by simp
  thus "x \<in> m" using splitx deepen_bwd by fastforce
next
  fix x assume ass: "x \<in> m"
  from ass obtain pc st where splitx: "x = (pc, st)" using prod.exhaust_sel by blast
  have "st \<in> lookup (deepen m) pc" using ass deepen_fwd splitx by fastforce
  from this splitx show "x \<in> flatten (deepen m)" using flatten_fwd by force
qed

lemma deepen_flatten: "deepen (flatten m) = m"
proof -
  have fwd: "deepen (flatten m) \<le> m"
    by (meson deepen_bwd flatten.cases less_eq_state_map_def subsetI)
  have bwd: "m \<le> deepen (flatten m)"
    by (meson deepen_fwd flatten_fwd less_eq_state_map_def subsetI)
  from fwd bwd show ?thesis by simp
qed

lemma flatten_lift_sup: "flatten (a \<squnion> b) = flatten a \<squnion> flatten b"
proof (intro Set.equalityI Set.subsetI)
  fix x assume ass: "x \<in> flatten (a \<squnion> b)"
  from ass obtain pc st where splitx: "x = (pc, st)" using prod.exhaust_sel by blast
  from this ass have "st \<in> lookup (a \<squnion> b) pc" using flatten_bwd by fastforce
  hence "st \<in> lookup a pc \<or> st \<in> lookup b pc" by simp
  hence "(pc, st) \<in> flatten a \<or> (pc, st) \<in> flatten b" using flatten_fwd by force
  from this splitx show "x \<in> flatten a \<union> flatten b" by simp
next
  fix x assume ass: "x \<in> flatten a \<union> flatten b"
  from ass obtain pc st where splitx: "x = (pc, st)" using prod.exhaust_sel by blast
  from this ass have "(pc, st) \<in> flatten a \<or> (pc, st) \<in> flatten b" by simp
  hence "st \<in> lookup a pc \<or> st \<in> lookup b pc" using flatten_bwd by force
  hence "st \<in> lookup (a \<squnion> b) pc" by fastforce
  from this splitx show "x \<in> flatten (a \<squnion> b)" by (simp add: flatten_fwd)
qed

subsubsection \<open>Implementation\<close>

fun collect_step :: "instr \<Rightarrow> addr \<Rightarrow> collect_state set \<Rightarrow> collect_state set state_map" where
  "collect_step op ipc sts = SM (\<lambda>pc. {st. \<exists>ist\<in>sts. step op (ipc, ist) = Some (pc, st)})"

definition[simp]: "collect_slurp prog ctx pc \<equiv> \<Squnion>(slurp collect_step prog ctx pc)"

lemma collect_step_bot: "collect_step op pc \<bottom> = \<bottom>"
  by (intro state_map_eq_fwd Set.equalityI Set.subsetI, auto)

lemma collect_slurp_fwd:
  assumes
    "ist \<in> lookup ctx ipc"
    "prog ipc = Some op"
    "step op (ipc, ist) = Some (pc, ost)"
  shows "ost \<in> collect_slurp prog ctx pc"
proof -
  have "ost \<in> lookup (collect_step op ipc (lookup ctx ipc)) pc" using assms(1) assms(3) by auto
  from assms(2) this show ?thesis by auto
qed

lemma collect_slurp_bwd:
  assumes "ost \<in> collect_slurp prog ctx pc"
  shows "\<exists>ist op ipc. ist \<in> lookup ctx ipc \<and> prog ipc = Some op \<and> step op (ipc, ist) = Some (pc, ost)"
proof -
  from assms obtain ipc op where ipcop: "prog ipc = Some op" "ost \<in> lookup (collect_step op ipc (lookup ctx ipc)) pc" by auto
  from this(2) obtain ist where ist: "ist \<in> lookup ctx ipc" "step op (ipc, ist) = Some (pc, ost)" by auto
  from ist(1) ipcop(1) ist(2) show ?thesis by blast
qed

definition[simp]: "collect_step_map \<equiv> step_map collect_step"

lemma step_all_correct: "flatten (collect_step_map prog (deepen flat)) = step_all_flat prog flat"
proof (intro Set.equalityI Set.subsetI)
  fix x assume ass: "x \<in> flatten (collect_step_map prog (deepen flat))"
  then obtain pc st where splitx: "x = (pc, st)" using prod.exhaust_sel by blast
  from this ass have "st \<in> lookup (collect_step_map prog (deepen flat)) pc" using flatten_bwd by fastforce
  hence stepped: "st \<in> collect_slurp prog (deepen flat) pc" by simp
  from this obtain ist ipc op where stuff: "ist \<in> lookup (deepen flat) ipc" "prog ipc = Some op" "step op (ipc, ist) = Some (pc, st)" using collect_slurp_bwd by blast
  hence bwd: "(ipc, ist) \<in> flat" by (simp add: deepen_bwd)
  from this stuff show "x \<in> step_all_flat prog flat" using splitx step_all_flat.intros by blast
next
  fix x assume ass: "x \<in> step_all_flat prog flat"
  then obtain pc st where splitx: "x = (pc, st)" using prod.exhaust_sel by blast
  from ass obtain ipc ist instr where stuff: "(ipc, ist) \<in> flat" "prog ipc = Some instr" "step instr (ipc, ist) = Some (pc, st)" by cases (simp add: splitx)
  from stuff have "ist \<in> lookup (deepen flat) ipc" by (simp add: states_at.intros)
  from this stuff have "st \<in> collect_slurp prog (deepen flat) pc" using collect_slurp_fwd by blast
  thus "x \<in> flatten (collect_step_map prog (deepen flat))" using splitx by (simp add: flatten_fwd)
qed

fun collect_advance :: "program \<Rightarrow> collect_ctx \<Rightarrow> collect_ctx" where
  "collect_advance prog ctx = ctx \<squnion> collect_step_map prog ctx"

lemma collect_advance_correct: "flatten (collect_advance prog (deepen flat)) = advance_flat prog flat"
proof -
  have "collect_advance prog (deepen flat) = deepen flat \<squnion> collect_step_map prog (deepen flat)" by simp
  hence "flatten (collect_advance prog (deepen flat)) = flatten (deepen flat) \<squnion> flatten (collect_step_map prog (deepen flat))" by (simp add: flatten_lift_sup flatten_deepen)
  hence "flatten (collect_advance prog (deepen flat)) = flat \<squnion> step_all_flat prog flat" using flatten_deepen step_all_correct by blast
  thus ?thesis by (simp add: advance_flat_def)
qed

definition[simp]: "collect_loop \<equiv> loop collect_step"

lemma collect_loop_as_flat:
  "flatten (collect_loop prog n (deepen flat)) = collect_loop_flat prog n flat"
proof (induction n arbitrary: flat)
  case 0 then show ?case using flatten_deepen by auto
next
  case (Suc n)
  obtain flatstep where flatstep: "deepen flatstep = collect_advance prog (deepen flat)" using deepen_flatten by blast
  hence "flatten (collect_loop prog (Suc n) (deepen flat)) = flatten (collect_loop prog n (deepen flatstep))" by simp
  from this Suc have loop: "flatten (collect_loop prog (Suc n) (deepen flat)) = collect_loop_flat prog n flatstep" by simp
  have step: "flatstep = advance_flat prog flat" by (metis collect_advance_correct flatstep flatten_deepen)
  from loop step show ?case by simp
qed

theorem collect_loop_correct:
  "flatten (collect_loop prog n (deepen entries)) = {st. \<exists>entry\<in>entries. steps_upto prog n entry st}"
  using collect_loop_as_flat collect_loop_flat_correct by blast

fun errors_all :: "program \<Rightarrow> collect_ctx \<Rightarrow> interpret_error set" where
  "errors_all prog ctx = {err. \<exists>pc st. st \<in> lookup ctx pc \<and> error_step prog (pc, st) = Some err}"

lemma errors_all_as_flat: "errors_all prog (deepen flat) = errors_all_flat prog flat"
proof (intro Set.equalityI Set.subsetI)
  fix err assume "err \<in> errors_all prog (deepen flat)"
  from this obtain pc st where step: "st \<in> lookup (deepen flat) pc" "error_step prog (pc, st) = Some err" by auto
  from this show "err \<in> errors_all_flat prog flat" using deepen_bwd by force
next
  fix err assume "err \<in> errors_all_flat prog flat"
  from this obtain pc st where step: "(pc, st) \<in> flat" "error_step prog (pc, st) = Some err" by auto
  hence deep: "st \<in> lookup (deepen flat) pc" using deepen_fwd by auto
  from step deep show "err \<in> errors_all prog (deepen flat)" using errors_all.simps by blast
qed

fun errors_loop :: "program \<Rightarrow> fuel \<Rightarrow> collect_ctx \<Rightarrow> interpret_error set" where
  "errors_loop _ 0 _ = {}" |
  "errors_loop prog (Suc n) ctx = errors_all prog ctx \<squnion> errors_loop prog n (collect_advance prog ctx)"

lemma errors_loop_as_flat:
  "errors_loop prog n (deepen flat) = errors_loop_flat prog n flat"
proof (induction n arbitrary: flat)
  case 0 then show ?case by simp
next
  case (Suc n)
  then show ?case by (metis collect_advance_correct deepen_flatten errors_all_as_flat errors_loop.simps(2) errors_loop_flat.simps(2))
qed

subsection \<open>Abstract Interpretation\<close>

class absstate = bounded_semilattice_sup_bot + order_top

text\<open>Least upper bound if the set is finite, else some random upper bound (just always \<top>)\<close>
fun finite_sup :: "'a::{bounded_semilattice_sup_bot, order_top} set \<Rightarrow> 'a" where
  "finite_sup s = (if finite s then folding.F sup \<bottom> s else \<top>)"

global_interpretation finite_sup: folding
  where f = "(sup::('a::bounded_semilattice_sup_bot \<Rightarrow> 'a \<Rightarrow> 'a))"
  and z = "\<bottom>"
proof (standard, rule ext)
  fix x y z
  have l: "((\<squnion>) (y::'a) \<circ> (\<squnion>) x) z = x \<squnion> (y \<squnion> z)" using sup_left_commute by force
  have r: "((\<squnion>) x \<circ> (\<squnion>) y) z = x \<squnion> (y \<squnion> z)" by auto
  from l r show "((\<squnion>) y \<circ> (\<squnion>) x) z = ((\<squnion>) x \<circ> (\<squnion>) y) z" by simp
qed

lemma finite_sup_upper:
  assumes
    "finite (s::'a::{bounded_semilattice_sup_bot, order_top} set)"
    "x \<in> s"
  shows "x \<le> finite_sup s"
proof(cases "finite s")
  case True
  then show ?thesis using assms finite_sup.remove by fastforce
qed simp

lemma finite_sup_least:
  assumes
    "finite s" \<comment> \<open>This is the main difference to Sup. It's only the least if the set is finite.\<close>
    "(\<And>x. x \<in> s \<Longrightarrow> x \<le> z)"
  shows "finite_sup s \<le> z"
using assms proof (induction s rule: finite_induct)
  case (insert x F)
  hence "finite_sup (insert x F) = x \<squnion> finite_sup F" using finite_sup.insert by simp
  then show ?case using insert.IH insert.prems by simp
qed simp

lemma finite_sup_complete: " \<Squnion>(s::'a::complete_lattice set) \<le> finite_sup s"
proof (cases "finite s")
  case True
  then show ?thesis using Sup_least finite_sup_upper by blast
qed simp

lemma finite_sup_union_distrib: "finite_sup(A \<union> B) = finite_sup A \<squnion> finite_sup B"
proof (cases "finite A \<and> finite B")
  case True
  hence "finite B" by simp
  from this show ?thesis
  proof (induction "B" rule: finite_induct)
    case (insert x F)
    then show ?case
      by (smt True Un_insert_right finite.insertI finite_UnI finite_sup.insert finite_sup.insert_remove finite_sup.simps insert_absorb sup.left_idem sup_left_commute)
  qed simp
next
  case False
  hence "finite_sup A \<squnion> finite_sup B = \<top>" by (metis finite_sup.simps sup.orderE sup_commute top_greatest)
  then show ?thesis by (simp add: False)
qed

fun step_infinite :: "'a::absstate astep \<Rightarrow> program \<Rightarrow> 'a state_map \<Rightarrow> bool" where
  "step_infinite f prog ctx = (\<exists>ipc op. prog ipc = Some op \<and> lookup ctx ipc \<noteq> \<bottom> \<and> infinite (domain (f op ipc (lookup ctx ipc))))"

text\<open>Same as step_map but escapes to \<top> if not finite\<close>
fun finite_step_map :: "'a::absstate astep \<Rightarrow> program \<Rightarrow> 'a state_map \<Rightarrow> 'a state_map" where
  "finite_step_map f prog ctx = (if step_infinite f prog ctx then \<top> else SM (\<lambda>pc. finite_sup (slurp f prog ctx pc)))"

lemma finite_step_map_complete:
  "step_map f prog (ctx::'a::{complete_lattice, absstate} state_map) \<le> finite_step_map f prog ctx"
proof (rule state_map_leI, goal_cases)
  case (1 p)
  then show ?case
  proof (cases "step_infinite f prog ctx")
    case False
    then show ?thesis using finite_sup_complete
      by (metis finite_step_map.elims lookup.simps step_map.simps)
  qed simp
qed

fun finite_advance :: "'a::absstate astep \<Rightarrow> program \<Rightarrow> 'a state_map \<Rightarrow> 'a state_map" where
  "finite_advance f prog ctx = ctx \<squnion> finite_step_map f prog ctx"

fun finite_loop :: "'a::absstate astep \<Rightarrow> program \<Rightarrow> fuel \<Rightarrow> 'a state_map \<Rightarrow> 'a state_map" where
  "finite_loop f prog 0 st = st" |
  "finite_loop f prog (Suc n) st = finite_loop f prog n (finite_advance f prog st)"

lemma finite_loop_pull: "finite_loop f prog n (finite_advance f prog st) = finite_advance f prog (finite_loop f prog n st)"
  by(induction n arbitrary: st, simp, metis finite_loop.simps(2))

locale AbsInt =
fixes \<gamma> :: "'as::absstate \<Rightarrow> collect_state set"
  assumes mono_gamma: "a \<le> b \<Longrightarrow> \<gamma> a \<le> \<gamma> b"
  and gamma_Top[simp]: "\<gamma> \<top> = \<top>"
fixes ai_step :: "'as astep"
  assumes astep_correct: "lookup (collect_step op ipc (\<gamma> a)) pc \<le> \<gamma> (lookup (ai_step op ipc a) pc)"
  and astep_keep_bot: "lookup (ai_step op ipc \<bottom>) pc = \<bottom>"
begin

fun \<gamma>_map :: "'as state_map \<Rightarrow> collect_ctx" where
  "\<gamma>_map (SM m) = SM (\<lambda>pc. \<gamma> (m pc))"

lemma \<gamma>_lookup: "lookup (\<gamma>_map m) pc = \<gamma> (lookup m pc)"
  by (metis \<gamma>_map.simps lookup.elims lookup.simps)

lemma \<gamma>_lookup_le:
  assumes "a \<le> \<gamma>_map b"
  shows "lookup a pc \<le> \<gamma> (lookup b pc)"
  using \<gamma>_lookup assms less_eq_state_map_def by blast

lemma \<gamma>_map_mono: "a \<le> b \<Longrightarrow> \<gamma>_map a \<le> \<gamma>_map b"
  by (simp add: \<gamma>_lookup less_eq_state_map_def mono_gamma)

definition[simp]: "ai_slurp prog ctx pc \<equiv> finite_sup (slurp ai_step prog ctx pc)"
lemma ai_slurp_correct:
  assumes "a \<le> \<gamma>_map b"
  shows "collect_slurp prog a pc \<le> \<gamma> (ai_slurp prog b pc)"
proof standard
  fix x assume "x \<in> collect_slurp prog a pc"
  from this obtain ipc op where slurped: "prog ipc = Some op" "lookup a ipc \<noteq> \<bottom>" "x \<in> lookup (collect_step op ipc (lookup a ipc)) pc" by auto
  from assms have "lookup a ipc \<subseteq> \<gamma> (lookup b ipc)" using \<gamma>_lookup_le by blast
  from slurped(3) this have "x \<in> lookup (collect_step op ipc (\<gamma> (lookup b ipc))) pc" by auto
  from this have "x \<in> \<gamma> (lookup (ai_step op ipc (lookup b ipc)) pc)" using astep_correct ..
  from this obtain ax where ax: "x \<in> \<gamma> ax" "ax = lookup (ai_step op ipc (lookup b ipc)) pc" using slurped by blast
  have "ax \<le> ai_slurp prog b pc"
  proof(cases "lookup b ipc = \<bottom>")
    case False
    let ?slurpset = "slurp ai_step prog b pc"
    from False have "ax \<in> ?slurpset" using slurped(1) ax(2) by auto
    then show ?thesis using finite_sup_upper by fastforce
  qed (simp add: astep_keep_bot ax(2))
  thus "x \<in> \<gamma> (ai_slurp prog b pc)" using ax mono_gamma by blast
qed

definition[simp]: "ai_step_map \<equiv> finite_step_map ai_step"
lemma ai_step_map_correct:
  assumes "a \<le> \<gamma>_map b"
  shows "collect_step_map prog a \<le> \<gamma>_map (ai_step_map prog b)"
proof (rule state_map_leI, goal_cases)
  case (1 p)
  show ?case
  proof (cases "step_infinite ai_step prog b")
    case False
    hence "lookup (\<gamma>_map (ai_step_map prog b)) p = \<gamma> (finite_sup(slurp ai_step prog b p))" by auto
    then show ?thesis using ai_slurp_correct assms by auto
  qed (simp add: \<gamma>_lookup)
qed

definition[simp]: "ai_advance \<equiv> finite_advance ai_step"
lemma ai_advance_correct:
  assumes "a \<le> \<gamma>_map b"
  shows "collect_advance prog a \<le> \<gamma>_map (ai_advance prog b)"
proof -
  have "\<gamma>_map (ai_step_map prog b) \<le> \<gamma>_map (finite_advance ai_step prog b)" by (metis \<gamma>_map_mono finite_advance.simps ai_step_map_def sup_ge2)
  hence step_le: "collect_step_map prog a \<le> \<gamma>_map (finite_advance ai_step prog b)" using ai_step_map_correct order.trans assms by blast

  have "b \<le> finite_advance ai_step prog b" by simp
  then have "a \<le> \<gamma>_map (finite_advance ai_step prog b)" by (meson \<gamma>_map_mono assms order.trans)

  from step_le this show ?thesis by force
qed

definition[simp, code]: "ai_loop \<equiv> finite_loop ai_step"

theorem ai_loop_correct: "collect_loop prog n (\<gamma>_map entry) \<le> \<gamma>_map (ai_loop prog n entry)"
proof (induction n arbitrary: entry)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc this have "collect_advance prog (collect_loop prog n (\<gamma>_map entry)) \<le> \<gamma>_map (ai_advance prog (ai_loop prog n entry))" using ai_advance_correct by blast
  then have "advance collect_step prog (loop collect_step prog n (\<gamma>_map entry)) \<le> \<gamma>_map (finite_advance ai_step prog (finite_loop ai_step prog n entry))" by auto
  then have "loop collect_step prog n (advance collect_step prog (\<gamma>_map entry)) \<le> \<gamma>_map (finite_loop ai_step prog n (finite_advance ai_step prog entry))" using finite_loop_pull loop_pull by metis
  thus ?case by simp
qed

end

subsubsection \<open>Useful Lemmas\<close>

text \<open>Characteristics of @{term step}\<close>

lemma step_pop1_pred:
  assumes "op = NOT \<or> op = AND \<or> op = POP \<or> op = CALL"
    "step op (ipc, ist) = Some (pc, st)"
  shows "\<exists>b st m f rs. ist = (b # st, m, f, rs)"
proof -
  obtain abst m f rs where split: "ist = (abst, m, f, rs)" by (metis prod_cases4)
  show ?thesis using assms
    apply safe
    apply (metis list.exhaust option.simps(3) prod.exhaust_sel step.simps(20))
    apply (metis list.exhaust option.simps(3) prod.exhaust_sel step.simps(21))
    apply (metis list.exhaust option.simps(3) prod.exhaust_sel step.simps(28))
    apply (metis list.exhaust option.simps(3) prod.exhaust_sel step.simps(31))
  done
qed

lemma step_pop2_pred:
  assumes "op = ADD \<or> op = LT \<or> op = LE \<or> op = EQ \<or> op = STORE"
    "step op (ipc, ist) = Some (pc, st)"
  shows "\<exists>a b st m f rs. ist = (a # b # st, m, f, rs)"
proof -
  obtain abst m f rs where "ist = (abst, m, f, rs)" by (metis prod_cases4)
  from this show ?thesis using assms
    apply safe
    apply (metis option.simps(3) remdups_adj.cases step.simps(18) step.simps(19))
    apply (metis option.simps(3) remdups_adj.cases step.simps(22) step.simps(23))
    apply (metis list.exhaust option.simps(3) step.simps(24) step.simps(25))
    apply (metis list.exhaust option.simps(3) step.simps(26) step.simps(27))
    apply (metis option.discI remdups_adj.cases step.simps(29) step.simps(30))
  done
qed

lemma step_jmpz_true:
  assumes "step (JMPZ tgt) (ipc, (istack, iregs, True, irs)) = Some (opc, (ostack, oregs, oflag, ors))"
  shows
    "ostack = istack"
    "oregs = iregs"
    "oflag = True"
    "opc = Suc ipc"
    "ors = irs"
  using assms by auto

lemma step_jmpz_false:
  assumes "step (JMPZ tgt) (ipc, (istack, iregs, False, irs)) = Some (opc, (ostack, oregs, oflag, ors))"
  shows
    "ostack = istack"
    "oregs = iregs"
    "oflag = False"
    "opc = tgt"
    "ors = irs"
  using assms by auto

lemma step_jmpz:
  assumes "step (JMPZ tgt) (ipc, (istack, iregs, iflag, irs)) = Some (opc, (ostack, oregs, oflag, ors))"
  shows
    "ostack = istack"
    "oregs = iregs"
    "oflag = iflag"
    "ors = irs"
  using assms by auto

lemma step_jmpz_succ:
  assumes "step (JMPZ tgt) (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc \<or> pc = tgt"
proof -
  from assms obtain sta m f rs where "ist = (sta, m, f, rs)" by (metis prod_cases4)
  from assms this show ?thesis by auto
qed

lemma step_add:
  assumes "step ADD (ipc, (istack, iregs, iflag, irs)) = Some (opc, (ostack, oregs, oflag, ors))"
  shows
    "opc = Suc ipc"
    "oregs = iregs"
    "oflag = iflag"
    "ors = irs"
    "\<exists>a b rest. istack = a # b # rest \<and> ostack = (a + b) # rest"
proof -
  from assms obtain a b st where split: "istack = a # b # st" using step_pop2_pred by blast
  from assms split show "opc = Suc ipc" by simp
  from assms split show "oregs = iregs" by simp
  from assms split show "oflag = iflag" by simp
  from assms split show "ors = irs" by simp
  from assms split show "\<exists>a b rest. istack = a # b # rest \<and> ostack = (a + b) # rest" by simp
qed

lemma step_add_succ:
  assumes "step ADD (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc"
proof -
  from assms obtain a b sta m f rs where split: "(a # b # sta, m, f, rs) = ist" using step_pop2_pred by metis
  from assms this show ?thesis by auto
qed

lemma step_not:
  assumes "step NOT (ipc, (istack, iregs, iflag, irs)) = Some (opc, (ostack, oregs, oflag, ors))"
  shows
    "opc = Suc ipc"
    "oregs = iregs"
    "oflag = (\<not> iflag)"
    "ors = irs"
    "\<exists>ia. istack = ia # ostack"
proof -
  from assms obtain a st where split: "istack = a # st" using step_pop1_pred by blast
  from assms split show "opc = Suc ipc" by simp
  from assms split show "oregs = iregs" by simp
  from assms split show "oflag = (\<not> iflag)" by simp
  from assms split show "ors = irs" by simp
  from assms split show "\<exists>ia. istack = ia # ostack" by simp
qed

lemma step_not_succ:
  assumes "step NOT (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc"
proof -
  from assms obtain b sta m f rs where "ist = (b # sta, m, f, rs)" using step_pop1_pred by blast
  from assms this show ?thesis by auto
qed

lemma step_and:
  assumes "step AND (ipc, (istack, iregs, iflag, irs)) = Some (opc, (ostack, oregs, oflag, ors))"
  shows
    "opc = Suc ipc"
    "oregs = iregs"
    "ors = irs"
    "\<exists>ia. istack = ia # ostack \<and> (ia = 1 \<or> ia = 0) \<and> oflag = (ia = 1 \<and> iflag)"
proof -
  from assms obtain a st where split: "istack = a # st" using step_pop1_pred by blast
  have cond[simp]: "a = 0 \<or> a = 1" proof(rule ccontr, goal_cases) case 1 from this assms split show ?case by simp qed
  from assms split show "opc = Suc ipc" by simp
  from assms split show "oregs = iregs" by simp
  from assms split show "ors = irs" by simp

  from split have "step AND (ipc, istack, iregs, iflag, irs) = Some (ipc + 1, st, iregs, a = 1 \<and> iflag, irs)" by simp
  hence ostack: "st = ostack" using assms by simp
  from assms this split have "oflag = (a = 1 \<and> iflag)" by simp
  from split ostack cond this show "\<exists>ia. istack = ia # ostack \<and> (ia = 1 \<or> ia = 0) \<and> oflag = (ia = 1 \<and> iflag)" by blast
qed

lemma step_and_succ:
  assumes "step AND (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc"
proof -
  from assms obtain b sta m f rs where "ist = (b # sta, m, f, rs)" using step_pop1_pred by blast
  from assms this show ?thesis by (cases "b = 0 \<or> b = 1"; auto)
qed

lemma step_lt:
  assumes "step LT (ipc, (istack, iregs, iflag, irs)) = Some (opc, (ostack, oregs, oflag, ors))"
  shows
    "opc = Suc ipc"
    "oregs = iregs"
    "ors = irs"
    "\<exists>ia ib. istack = ia # ib # ostack \<and> oflag = (ia < ib)"
proof -
  from assms obtain a b st where split: "istack = a # b # st" using step_pop2_pred by blast
  from assms split show "opc = Suc ipc" by simp
  from assms split show "oregs = iregs" by simp
  from assms split show "ors = irs" by simp
  from assms split have "oflag = (a < b)" by simp
  moreover from assms split have "istack = a # b # ostack" by simp
  ultimately show "\<exists>ia ib. istack = ia # ib # ostack \<and> oflag = (ia < ib)" by blast
qed

lemma step_lt_succ:
  assumes "step LT (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc"
proof -
  from assms obtain a b sta m f rs where split: "(a # b # sta, m, f, rs) = ist" using step_pop2_pred by metis
  from assms this show ?thesis by auto
qed

lemma step_le:
  assumes "step LE (ipc, (istack, iregs, iflag, irs)) = Some (opc, (ostack, oregs, oflag, ors))"
  shows
    "opc = Suc ipc"
    "oregs = iregs"
    "ors = irs"
    "\<exists>ia ib. istack = ia # ib # ostack \<and> oflag = (ia \<le> ib)"
proof -
  from assms obtain a b st where split: "istack = a # b # st" using step_pop2_pred by blast
  from assms split show "opc = Suc ipc" by simp
  from assms split show "oregs = iregs" by simp
  from assms split show "ors = irs" by simp
  from assms split have "oflag = (a \<le> b)" by simp
  moreover from assms split have "istack = a # b # ostack" by simp
  ultimately show "\<exists>ia ib. istack = ia # ib # ostack \<and> oflag = (ia \<le> ib)" by blast
qed

lemma step_le_succ:
  assumes "step LE (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc"
proof -
  from assms obtain a b sta m f rs where split: "(a # b # sta, m, f, rs) = ist" using step_pop2_pred by metis
  from assms this show ?thesis by auto
qed

lemma step_eq:
  assumes "step EQ (ipc, (istack, iregs, iflag, irs)) = Some (opc, (ostack, oregs, oflag, ors))"
  shows
    "opc = Suc ipc"
    "oregs = iregs"
    "ors = irs"
    "\<exists>ia ib. istack = ia # ib # ostack \<and> oflag = (ia = ib)"
proof -
  from assms obtain a b st where split: "istack = a # b # st" using step_pop2_pred by blast
  from assms split show "opc = Suc ipc" by simp
  from assms split show "oregs = iregs" by simp
  from assms split show "ors = irs" by simp
  from assms split have "oflag = (a = b)" by simp
  moreover from assms split have "istack = a # b # ostack" by simp
  ultimately show "\<exists>ia ib. istack = ia # ib # ostack \<and> oflag = (ia = ib)" by blast
qed

lemma step_eq_succ:
  assumes "step EQ (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc"
proof -
  from assms obtain a b sta m f rs where split: "(a # b # sta, m, f, rs) = ist" using step_pop2_pred by metis
  from assms this show ?thesis by auto
qed

lemma step_push:
  assumes "step (PUSH v) (ipc, (istack, iregs, iflag, irs)) = Some (opc, (ostack, oregs, oflag, ors))"
  shows
    "opc = Suc ipc"
    "ostack = v # istack"
    "oregs = iregs"
    "oflag = iflag"
    "ors = irs"
  using assms by auto

lemma step_push_succ:
  assumes "step (PUSH x) (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc"
proof -
  from assms obtain sta m f rs where "ist = (sta, m, f, rs)" using prod_cases4 by blast
  from assms this show ?thesis by auto
qed

lemma step_pop:
  assumes "step POP (ipc, (istack, iregs, iflag, irs)) = Some (opc, (ostack, oregs, oflag, ors))"
  shows
    "opc = Suc ipc"
    "oregs = iregs"
    "oflag = iflag"
    "ors = irs"
    "\<exists>v. istack = v # ostack"
proof -
  from assms have "\<exists>v rstack. istack = v # rstack" by (metis list.exhaust option.simps(3) step.simps(28))
  from this assms obtain v where v: "istack = v # ostack" by auto
  thus "\<exists>v. istack = v # ostack" ..
  from assms show "opc = Suc ipc" using step_pop1_pred by force
  from assms v show "oregs = iregs" by auto
  from assms v show "oflag = iflag" by auto
  from assms v show "ors = irs" by auto
qed

lemma step_pop_succ:
  assumes "step POP (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc"
proof -
  from assms obtain b sta m f rs where "ist = (b # sta, m, f, rs)" using step_pop1_pred by blast
  from assms this show ?thesis by auto
qed

lemma step_lid_succ:
  assumes "step (LID r) (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc"
proof -
  from assms obtain sta m f rs where "ist = (sta, m, f, rs)" using prod_cases4 by blast
  from assms this show ?thesis by auto
qed

lemma step_store_succ:
  assumes "step STORE (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc"
proof -
  from assms obtain v r sta m f rs where split: "(v # r # sta, m, f, rs) = ist" using step_pop2_pred by metis
  from assms this show ?thesis by (cases "r \<ge> 0", auto)
qed

lemma step_storei_succ:
  assumes "step (STOREI r v) (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc"
proof -
  from assms obtain sta m f rs where "ist = (sta, m, f, rs)" using prod_cases4 by blast
  from assms this show ?thesis by auto
qed

lemma step_copy_succ:
  assumes "step COPY (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc"
proof -
  from assms obtain sta m f rs where "ist = (sta, m, f, rs)" using prod_cases4 by blast
  from assms this show ?thesis by auto
qed

lemma step_storec_succ:
  assumes "step (STOREC c d) (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc"
proof -
  from assms obtain sta m f rs where "ist = (sta, m, f, rs)" using prod_cases4 by blast
  from assms this show ?thesis by (cases "d = 0"; auto)
qed

text \<open>Resulting characteristics of @{term collect_step},
  useful for proving abstract step functions against it.\<close>

lemma collect_step_none: "lookup (collect_step op ipc {}) pc = {}"
  by simp

lemma collect_step_jmpz_succ: "pc \<noteq> Suc ipc \<Longrightarrow> pc \<noteq> tgt \<Longrightarrow> lookup (collect_step (JMPZ tgt) ipc sts) pc = \<bottom>" using step_jmpz_succ by fastforce
lemma collect_step_fallthrough_succ:
  assumes "pc \<noteq> Suc ipc"
  shows
    "lookup (collect_step ADD          ipc sts) pc = \<bottom>"
    "lookup (collect_step NOT          ipc sts) pc = \<bottom>"
    "lookup (collect_step AND          ipc sts) pc = \<bottom>"
    "lookup (collect_step LT           ipc sts) pc = \<bottom>"
    "lookup (collect_step LE           ipc sts) pc = \<bottom>"
    "lookup (collect_step EQ           ipc sts) pc = \<bottom>"
    "lookup (collect_step (PUSH x)     ipc sts) pc = \<bottom>"
    "lookup (collect_step POP          ipc sts) pc = \<bottom>"
    "lookup (collect_step (LID r)      ipc sts) pc = \<bottom>"
    "lookup (collect_step STORE        ipc sts) pc = \<bottom>"
    "lookup (collect_step (STOREI r v) ipc sts) pc = \<bottom>"
    "lookup (collect_step COPY         ipc sts) pc = \<bottom>"
    "lookup (collect_step (STOREC c d) ipc sts) pc = \<bottom>"
    "lookup (collect_step (SETF b)     ipc sts) pc = \<bottom>"
proof(goal_cases)
  case 1 show ?case using step_add_succ assms by auto next
  case 2 show ?case using step_not_succ assms by auto next
  case 3 show ?case using step_and_succ assms by auto next
  case 4 show ?case using step_lt_succ assms by auto next
  case 5 show ?case using step_le_succ assms by auto next
  case 6 show ?case using step_eq_succ assms by auto next
  case 7 show ?case using step_push_succ assms by auto next
  case 8 show ?case using step_pop_succ assms by auto next
  case 9 show ?case using step_lid_succ assms by auto next
  case 10 show ?case using step_store_succ assms by auto next
  case 11 show ?case using step_storei_succ assms by auto next
  case 12 show ?case using step_copy_succ assms by auto
next
  case 13
  show ?case
  proof (standard; standard)
    fix x assume "x \<in> lookup (collect_step (STOREC c d) ipc sts) pc"
    from this obtain ist where "ist \<in> sts" "step (STOREC c d) (ipc, ist) = Some (pc, x)" by auto
    from this(2) assms show "x \<in> {}" using step_storec_succ by blast
  qed
next
  case 14 then show ?case using assms by auto
qed
lemma collect_step_halt_succ: "lookup (collect_step HALT ipc sts) pc = \<bottom>" by simp

lemmas collect_step_succ = collect_step_jmpz_succ collect_step_fallthrough_succ

lemma jmpz_cases:
  assumes
    suc: "lookup (collect_step (JMPZ target) ipc (\<gamma> ins)) (Suc ipc) \<subseteq> \<gamma> (lookup (some_step (JMPZ target) ipc ins) (Suc ipc))" and
    target: "lookup (collect_step (JMPZ target) ipc (\<gamma> ins)) target \<subseteq> \<gamma> (lookup (some_step (JMPZ target) ipc ins) target)"
  shows "lookup (collect_step (JMPZ target) ipc (\<gamma> ins)) pc \<subseteq> \<gamma> (lookup (some_step (JMPZ target) ipc ins) pc)"
  using assms ex_in_conv by fastforce
                           
subsection \<open>Helpers to conveniently define Abstract Step Functions\<close>

fun deep_merge :: "(addr * ('a::absstate)) set \<Rightarrow> 'a state_map" where
  "deep_merge sts = SM (\<lambda>pc. finite_sup {st. (pc, st) \<in> sts})"

lemma deep_merge_lookup:
  assumes "(pc, (st::'a::absstate)) \<in> sts"
  shows "st \<le> lookup (deep_merge sts) pc"
proof -
  have "lookup (deep_merge sts) pc = finite_sup {st. (pc, st) \<in> sts}" by simp
  show ?thesis
  proof (cases "finite {st. (pc, st) \<in> sts}")
    case True
    then show ?thesis using assms finite_sup_upper by fastforce
  qed simp
qed

lemma deep_merge_empty: "deep_merge ({}::(addr * ('a::absstate)) set) = \<bottom>"
  by (rule state_map_eq_fwd; simp)

lemma prod_set_split: "{st. (k, st) \<in> (set xs \<union> {x})} = {st. (k, st) \<in> set xs} \<union> {st. (k, st) \<in> {x}}"
  by (intro Set.equalityI Set.subsetI; blast)

lemma deep_merge_cons: "deep_merge (set ((k, v) # xs)) = deep_merge (set xs) \<squnion> single k v"
proof (rule state_map_eq_fwd)
  fix p
  let ?x = "(k, v)"
  have "finite_sup{st. (p, st) \<in> (set (?x # xs))} = finite_sup{st. (p, st) \<in> (set xs)} \<squnion> finite_sup{st. (p, st) \<in> {?x}}"
  proof (cases "p = k")
    case True
    hence "finite_sup{st. (p, st) \<in> {(k, v)}} = v" by simp
    have "finite_sup{st. (p, st) \<in> set ((k, v) # xs)} = finite_sup{st. (p, st) \<in> (set xs \<union> {?x})}" by simp
    hence "finite_sup{st. (p, st) \<in> set ((k, v) # xs)} = finite_sup({st. (p, st) \<in> set xs} \<union> {st. (p, st) \<in> {?x}})" using prod_set_split by metis
    then show ?thesis using finite_sup_union_distrib by metis
  next
    case False
    hence bot: "finite_sup{st. (p, st) \<in> {?x}} = \<bottom>" by simp
    from False have "{st. (p, st) \<in> set (?x # xs)} = {st. (p, st) \<in> set xs}" by simp
    from this have "finite_sup{st. (p, st) \<in> set (?x # xs)} = finite_sup{st. (p, st) \<in> set xs} \<squnion> \<bottom>" by simp
    from this bot show ?thesis by presburger
  qed
  thus "lookup (deep_merge (set (?x # xs))) p = lookup (deep_merge (set xs) \<squnion> single k v) p" by simp
qed

lemma deep_merge_bot: "deep_merge (set ((k, \<bottom>) # xs)) = deep_merge (set xs)"
proof (rule state_map_eq_fwd)
  fix p
  show "lookup (deep_merge (set ((k, \<bottom>) # xs))) p = lookup (deep_merge (set xs)) p"
    by (smt boolean_algebra_cancel.sup0 deep_merge_cons lookup.simps single.simps sup_lookup)
qed

end

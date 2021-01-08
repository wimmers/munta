theory Abs_Int
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

lemma collect_loop_steps:
  assumes
    "steps prog (Suc n) (pc, st, s, f, rs) (pc', st', s', f', rs')"
    "(st, s, f, rs) \<in> lookup entry pc"
  shows "(st', s', f', rs') \<in> lookup (collect_loop prog n entry) pc'" using assms
proof -
  from assms(1) have "steps_upto prog n (pc, st, s, f, rs) (pc', st', s', f', rs')" using steps_upto_steps by simp
  hence "(pc', st', s', f', rs') \<in> {st. \<exists>entry\<in>(flatten entry). steps_upto prog n entry st}" using assms(2) flatten.intros by fastforce
  thus ?thesis by (metis collect_loop_correct deepen_flatten flatten_bwd)
qed

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

class absstate = semilattice_sup + order_bot + order_top

text\<open>Least upper bound if the set is finite, else some random upper bound (just always \<top>)\<close>
fun finite_sup :: "'a::{semilattice_sup, order_bot, order_top} set \<Rightarrow> 'a" where
  "finite_sup s = (if finite s then folding.F sup \<bottom> s else \<top>)"

global_interpretation finite_sup: folding
  where f = "(sup::('a::{semilattice_sup, order_bot} \<Rightarrow> 'a \<Rightarrow> 'a))"
  and z = "\<bottom>"
proof (standard, rule ext)
  fix x y z
  have l: "((\<squnion>) (y::'a) \<circ> (\<squnion>) x) z = x \<squnion> (y \<squnion> z)" using sup_left_commute by force
  have r: "((\<squnion>) x \<circ> (\<squnion>) y) z = x \<squnion> (y \<squnion> z)" by auto
  from l r show "((\<squnion>) y \<circ> (\<squnion>) x) z = ((\<squnion>) x \<circ> (\<squnion>) y) z" by simp
qed

lemma finite_sup_upper:
  assumes
    "finite (s::'a::{semilattice_sup, order_bot, order_top} set)"
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
      by (smt True Un_insert_right finite.insertI finite_UnI finite_sup.insert
            finite_sup.insert_remove finite_sup.simps insert_absorb sup.left_idem sup_left_commute)
  qed (simp add: sup.absorb1)
next
  case False
  hence "finite_sup A \<squnion> finite_sup B = \<top>" by (metis finite_sup.simps sup.orderE sup_commute top_greatest)
  then show ?thesis by (simp add: False)
qed

fun step_infinite :: "'a::absstate astep \<Rightarrow> program \<Rightarrow> 'a state_map \<Rightarrow> bool" where
  "step_infinite f prog ctx \<longleftrightarrow> infinite (domain ctx) \<or> (\<exists>ipc op. prog ipc = Some op \<and> lookup ctx ipc \<noteq> \<bottom> \<and> infinite (domain (f op ipc (lookup ctx ipc))))"

text\<open>Same as step_map but escapes to \<top> if not finite\<close>
fun finite_step_map :: "'a::absstate astep \<Rightarrow> program \<Rightarrow> 'a state_map \<Rightarrow> 'a state_map" where
  "finite_step_map f prog ctx = (if step_infinite f prog ctx then \<top> else SM (\<lambda>pc. finite_sup (slurp f prog ctx pc)))"

lemma finite_these:
  assumes "finite A"
  shows "finite (Option.these (f ` A))"
  using assms by (simp add: Option.these_def)

lemma finite_step_map_finite:
  "finite_step_map f prog entry = \<top> \<or> finite (domain (finite_step_map f prog entry))"
proof (cases "step_infinite f prog entry")
  case False
  hence finite_domain: "prog ipc = Some op \<Longrightarrow> lookup entry ipc \<noteq> \<bottom> \<Longrightarrow> finite (domain (f op ipc (lookup entry ipc)))"
    for ipc op using step_infinite.simps by blast
  have finite_slurp: "finite {pc. slurp f prog entry pc \<noteq> {\<bottom>} \<and> slurp f prog entry pc \<noteq> {}}"
  proof -
    have "{pc. \<exists>ipc op. prog ipc = Some op \<and> lookup entry ipc \<noteq> \<bottom> \<and> lookup (f op ipc (lookup entry ipc)) pc \<noteq> \<bottom>}
      \<subseteq> \<Union>{d. \<exists>op ipc. prog ipc = Some op \<and> lookup entry ipc \<noteq> \<bottom> \<and> d = domain (f op ipc (lookup entry ipc)) }"
    proof (standard, goal_cases)
      case (1 pc)
      then obtain ipc op where "prog ipc = Some op \<and> lookup entry ipc \<noteq> \<bottom> \<and> lookup (f op ipc (lookup entry ipc)) pc \<noteq> \<bottom>" by auto
      hence "prog ipc = Some op \<and> lookup entry ipc \<noteq> \<bottom> \<and> pc \<in> domain (f op ipc (lookup entry ipc))"
        by (metis (mono_tags, lifting) CollectI domain.simps lookup.elims)
      hence "\<exists>op ipc. prog ipc = Some op \<and> lookup entry ipc \<noteq> \<bottom> \<and> pc \<in> domain (f op ipc (lookup entry ipc))" by blast
      then show ?case by blast
    qed
    moreover have "finite (\<Union>{d. \<exists>op ipc. prog ipc = Some op \<and> lookup entry ipc \<noteq> \<bottom> \<and> d = domain (f op ipc (lookup entry ipc)) })"
    proof -
      have "finite (domain entry)" using False step_infinite.simps by blast
      hence "finite {ipc. lookup entry ipc \<noteq> \<bottom>}" by (metis domain.elims lookup.simps)
      moreover have "{(op, ipc). prog ipc = Some op \<and> lookup entry ipc \<noteq> \<bottom>}
        = Option.these ((\<lambda>ipc. case prog ipc of Some op \<Rightarrow> Some (op, ipc) | _ \<Rightarrow> None) ` {ipc. lookup entry ipc \<noteq> \<bottom>})"
      proof (intro Set.equalityI Set.subsetI, goal_cases)
        case (1 x)
        then show ?case using image_iff in_these_eq by fastforce
      next
        case (2 x)
        then obtain op ipc where "x = (op, ipc)" by (meson surj_pair)
        from this 2 have "Some (op, ipc) \<in> ((\<lambda>ipc. case prog ipc of None \<Rightarrow> None | Some op \<Rightarrow> Some (op, ipc)) ` {ipc. lookup entry ipc \<noteq> \<bottom>})"
          by (simp add: in_these_eq)
        then show ?case by (simp add: \<open>x = (op, ipc)\<close> image_iff option.case_eq_if)
      qed
      ultimately have "finite {(op, ipc). prog ipc = Some op \<and> lookup entry ipc \<noteq> \<bottom>}" using finite_these by simp
      moreover have "{d. \<exists>op ipc. prog ipc = Some op \<and> lookup entry ipc \<noteq> \<bottom> \<and> d = domain (f op ipc (lookup entry ipc)) }
        = (\<lambda>(op, ipc). domain (f op ipc (lookup entry ipc))) ` {(op, ipc). prog ipc = Some op \<and> lookup entry ipc \<noteq> \<bottom>}" by auto
      ultimately have "finite {d. \<exists>op ipc. prog ipc = Some op \<and> lookup entry ipc \<noteq> \<bottom> \<and> d = domain (f op ipc (lookup entry ipc)) }" by simp
      thus ?thesis using finite_domain by blast
    qed
    ultimately have fin: "finite {pc. \<exists>ipc op. prog ipc = Some op \<and> lookup entry ipc \<noteq> \<bottom> \<and> lookup (f op ipc (lookup entry ipc)) pc \<noteq> \<bottom>}"
      using infinite_super by blast

    have "{pc. slurp f prog entry pc \<noteq> {\<bottom>} \<and> slurp f prog entry pc \<noteq> {}}
      \<subseteq> {pc. \<exists>ipc op. prog ipc = Some op \<and> lookup entry ipc \<noteq> \<bottom> \<and> lookup (f op ipc (lookup entry ipc)) pc \<noteq> \<bottom>}"
    proof (standard, goal_cases)
      case (1 pc)
      hence "slurp f prog entry pc \<noteq> {\<bottom>} \<and> slurp f prog entry pc \<noteq> {}" by simp
      then obtain st where "st \<in> slurp f prog entry pc \<and> st \<noteq> \<bottom>" by blast
      hence "\<exists>ipc op. prog ipc = Some op \<and> lookup entry ipc \<noteq> \<bottom> \<and> lookup (f op ipc (lookup entry ipc)) pc \<noteq> \<bottom>" by auto
      then show ?case by simp
    qed

    hence "finite {pc. slurp f prog entry pc \<noteq> {\<bottom>} \<and> slurp f prog entry pc \<noteq> {}}" using fin by (simp add: finite_subset)
    thus ?thesis by simp
  qed
  have "finite {pc. finite_sup (slurp f prog entry pc) \<noteq> \<bottom>}"
  proof -
    have slurp: "finite_sup (slurp f prog entry pc) \<noteq> \<bottom> \<Longrightarrow> slurp f prog entry pc \<noteq> \<bottom> \<and> slurp f prog entry pc \<noteq> {\<bottom>}" for pc
    proof (rule ccontr, goal_cases)
      case 1
      hence "slurp f prog entry pc = {} \<or> slurp f prog entry pc = {\<bottom>}" by blast
      thus ?case proof (rule disjE)
        assume "slurp f prog entry pc = {}"
        hence "finite_sup (slurp f prog entry pc) = finite_sup {}" by presburger
        also have "\<dots> = \<bottom>" by simp
        finally show False using 1 by blast
      next
        assume "slurp f prog entry pc = {\<bottom>}"
        hence "finite_sup (slurp f prog entry pc) = finite_sup {\<bottom>}" by presburger
        also have "\<dots> = \<bottom>" by simp
        finally show False using 1 by blast
      qed
    qed
    thus ?thesis using finite_slurp infinite_super by (smt Collect_mono)
  qed
  then show ?thesis by simp
qed simp

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

lemma finite_step_map_step:
  assumes f_keep_bot: "f op ipc \<bottom> = \<bottom>"
    and op: "prog ipc = Some op"
  shows "f op ipc (lookup ctx ipc) \<le> finite_step_map f prog ctx"
proof (cases "step_infinite f prog ctx")
  case False
  have "f op ipc (lookup ctx ipc) \<le> SM (\<lambda>pc. finite_sup (slurp f prog ctx pc))"
  proof (rule state_map_leI, goal_cases)
    case (1 p)
    have "lookup (f op ipc (lookup ctx ipc)) p \<le> finite_sup (slurp f prog ctx p)"
    proof (cases "lookup ctx ipc \<noteq> \<bottom>")
      case True
      hence in_slurp: "lookup (f op ipc (lookup ctx ipc)) p \<in> slurp f prog ctx p"
        using op by auto
      then show ?thesis
      proof (cases "finite (slurp f prog ctx p)")
        case True then show ?thesis using in_slurp by (rule finite_sup_upper)
      qed simp
    next
      case False then show ?thesis using f_keep_bot by simp
    qed
    then show ?case using 1 by simp
  qed
  then show ?thesis using False by simp
qed simp

fun finite_advance :: "'a::absstate astep \<Rightarrow> program \<Rightarrow> 'a state_map \<Rightarrow> 'a state_map" where
  "finite_advance f prog ctx = ctx \<squnion> finite_step_map f prog ctx"

lemma finite_advance_finite:
  assumes "entry = \<top> \<or> finite (domain entry)"
  shows "finite_advance f prog entry = \<top> \<or> finite (domain (finite_advance f prog entry))"
proof -
  have "finite_step_map f prog entry = \<top> \<or> finite (domain (finite_step_map f prog entry))"
    by (rule finite_step_map_finite)
  thus ?thesis
  proof (rule disjE, goal_cases)
    case 2
    from assms show ?case
    proof (rule disjE, goal_cases)
      case 2
      show ?case using sup_domain_finite[OF 2 \<open>finite (domain (finite_step_map _ _ _))\<close>] by simp
    qed (simp add: sup_top)
  qed (simp add: sup_top2)
qed

lemma finite_advance_preserve: "entry \<le> finite_advance f prog entry" by simp

fun finite_loop :: "'a::absstate astep \<Rightarrow> program \<Rightarrow> fuel \<Rightarrow> 'a state_map \<Rightarrow> 'a state_map" where
  "finite_loop f prog 0 st = st" |
  "finite_loop f prog (Suc n) st = finite_loop f prog n (finite_advance f prog st)"

lemma finite_loop_pull: "finite_loop f prog n (finite_advance f prog st) = finite_advance f prog (finite_loop f prog n st)"
  by(induction n arbitrary: st, simp, metis finite_loop.simps(2))

lemma finite_loop_finite:
  assumes "entry = \<top> \<or> finite (domain entry)"
  shows "finite_loop f prog n entry = \<top> \<or> finite (domain (finite_loop f prog n entry))"
using assms proof (induction n arbitrary: entry)
  case (Suc n)
  then show ?case using Suc.IH finite_advance_finite[OF Suc.prems] by simp
qed simp

lemma finite_loop_preserve: "entry \<le> finite_loop f prog n entry"
proof (induction n arbitrary: entry)
  case (Suc n)
  then show ?case
    unfolding finite_loop.simps finite_loop_pull
    using finite_advance_preserve order.trans by blast
qed simp

fun finite_loop_fp :: "'a::absstate astep \<Rightarrow> program \<Rightarrow> fuel \<Rightarrow> 'a state_map \<Rightarrow> 'a state_map" where
  "finite_loop_fp f prog 0 st = \<top>" |
  "finite_loop_fp f prog (Suc n) st =
    (let next = finite_advance f prog st in
    if next = st then next else finite_loop_fp f prog n next)"

lemma finite_loop_fp_complete: "finite_loop f prog n st \<le> finite_loop_fp f prog n st"
proof (induction n arbitrary: st)
  case (Suc n)
  let ?next = "finite_advance f prog st"
  show ?case
  proof (cases "st = ?next")
    case True
    hence "finite_loop f prog (Suc n) st = finite_loop f prog n st" by auto
    moreover have "finite_loop_fp f prog (Suc n) st = st" for n using True by auto
    ultimately show ?thesis by (metis Suc.IH finite_loop.elims order_refl)
  next
    case False
    then show ?thesis by (simp add: Suc.IH)
  qed
qed simp

lemma finite_loop_fp_supercomplete: "finite_loop f prog m st \<le> finite_loop_fp f prog n st"
proof (induction n arbitrary: st)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?next = "finite_advance f prog st"
  show ?case
  proof (cases "st = ?next")
    case True
    hence "finite_loop f prog (Suc n) st = finite_loop f prog n st" by auto
    moreover have "finite_loop_fp f prog (Suc n) st = st" for n using True by auto
    ultimately show ?thesis by (metis True finite_loop.simps(2) finite_loop_fp_complete)
  next
    case False
    then show ?thesis by (smt Suc finite_advance.simps finite_loop_fp.simps(2) finite_loop_pull order_trans sup.cobounded1)
  qed
qed

locale Abs_Int =
fixes \<gamma> :: "'as::absstate \<Rightarrow> collect_state set"
  assumes mono_gamma: "a \<le> b \<Longrightarrow> \<gamma> a \<le> \<gamma> b"
  and gamma_Top[simp]: "\<gamma> \<top> = \<top>"
  and gamma_Bot[simp]: "\<gamma> \<bottom> = \<bottom>"
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

definition[simp]: "ai_loop \<equiv> finite_loop ai_step"

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

lemma ai_steps:
  assumes
    "steps prog (Suc n) (pc, st, s, f, rs) (pc', st', s', f', rs')"
    "(st, s, f, rs) \<in> \<gamma> (lookup entry pc)"
  shows "(st', s', f', rs') \<in> \<gamma> (lookup (ai_loop prog n entry) pc')"
proof -
  have "(st', s', f', rs') \<in> lookup (collect_loop prog n (\<gamma>_map entry)) pc'" using collect_loop_steps assms(1) assms(2) \<gamma>_lookup by blast
  thus ?thesis using assms using \<gamma>_lookup_le ai_loop_correct by blast
qed

lemma ai_steps_single:
  assumes
    "steps prog (Suc n) (pc, st, s, f, rs) (pc', st', s', f', rs')"
    "(st, s, f, rs) \<in> \<gamma> entry"
  shows "(st', s', f', rs') \<in> \<gamma> (lookup (ai_loop prog n (single pc entry)) pc')" using assms ai_steps by auto

lemma ai_steps_pc:
  assumes
    "steps prog (Suc n) (pc, st, s, f, rs) (pc', st', s', f', rs')"
    "(st, s, f, rs) \<in> \<gamma> entry"
  shows "pc' \<in> domain (ai_loop prog n (single pc entry))"
proof -
  from assms have "(st', s', f', rs') \<in> \<gamma> (lookup (ai_loop prog n (single pc entry)) pc')" by (rule ai_steps_single)
  hence "lookup (ai_loop prog n (single pc entry)) pc' \<noteq> \<bottom>" by auto
  thus ?thesis by (smt domain.elims lookup.simps mem_Collect_eq)
qed

definition[simp]: "ai_loop_fp \<equiv> finite_loop_fp ai_step"

theorem ai_loop_fp_correct: "collect_loop prog m (\<gamma>_map entry) \<le> \<gamma>_map (ai_loop_fp prog n entry)"
  by (metis (no_types, lifting) \<gamma>_map_mono ai_loop_correct ai_loop_def ai_loop_fp_def finite_loop_fp_supercomplete le_iff_sup le_sup_iff)

end

text\<open>
Extension of the original @{term Abs_Int} locale, adding the @{term kill_flag} function, which
modifies the state such that the flag can be both @{term True} and @{term False}.
This is used in the theory Abs_Int_C, but defined here to avoid unnecessary imports when
interpreting it.
\<close>
locale Abs_Int_C = Abs_Int +
  fixes kill_flag :: "'a \<Rightarrow> 'a"
  assumes kill_flag: "(st, s, f, rs) \<in> \<gamma> x \<Longrightarrow> (st, s, True, rs) \<in> \<gamma> (kill_flag x) \<and> (st, s, False, rs) \<in> \<gamma> (kill_flag x)"

subsubsection \<open>Useful Lemmas\<close>

text \<open>Characteristics of @{term step}\<close>

lemma step_pop1_pred:
  assumes "op = NOT \<or> op = AND \<or> op = POP \<or> op = CALL \<or> op = RETURN"
    "step op (ipc, ist) = Some (pc, st)"
  shows "\<exists>b st m f rs. ist = (b # st, m, f, rs)"
proof -
  obtain abst m f rs where split: "ist = (abst, m, f, rs)" by (metis prod_cases4)
  show ?thesis using assms
    apply safe
    apply (metis list.exhaust option.simps(3) prod.exhaust_sel step.simps(21))
    apply (metis list.exhaust option.simps(3) prod.exhaust_sel step.simps(22))
    apply (metis list.exhaust option.simps(3) prod.exhaust_sel step.simps(29))
    apply (metis list.exhaust option.simps(3) prod.exhaust_sel step.simps(32))
    apply (metis list.exhaust option.simps(3) prod.exhaust_sel step.simps(33))
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
    apply (metis option.simps(3) remdups_adj.cases step.simps(19) step.simps(20))
    apply (metis option.simps(3) remdups_adj.cases step.simps(23) step.simps(24))
    apply (metis list.exhaust option.simps(3) step.simps(25) step.simps(26))
    apply (metis list.exhaust option.simps(3) step.simps(27) step.simps(28))
    apply (metis option.discI remdups_adj.cases step.simps(30) step.simps(31))
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
  from assms have "\<exists>v rstack. istack = v # rstack" by (metis list.exhaust option.simps(3) step.simps(29))
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

lemma step_lid_safe:
  assumes "step (LID r) (ipc, (istack, iregs, iflag, irs)) = Some (opc, (ostack, oregs, oflag, ors))"
  shows "r < length iregs"
proof (rule ccontr, goal_cases)
  case 1 then show ?case using assms by simp
qed

lemma step_lid:
  assumes "step (LID r) (ipc, (istack, iregs, iflag, irs)) = Some (opc, (ostack, oregs, oflag, ors))"
  shows "opc = Suc ipc \<and> ostack = (iregs ! r) # istack \<and> oregs = iregs \<and> oflag = iflag \<and> ors = irs \<and> r < length iregs"
  using assms step_lid_safe by (metis Pair_inject Suc_eq_plus1 option.sel step.simps(11))

lemma step_lid_succ:
  assumes "step (LID r) (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc"
proof -
  from assms obtain sta m f rs where "ist = (sta, m, f, rs)" using prod_cases4 by blast
  moreover from assms this have "r < length m" using step_lid_safe by (metis option.simps(3) step.simps(11))
  ultimately show ?thesis using assms by auto
qed

lemma step_store:
  assumes "step STORE (ipc, (istack, iregs, iflag, irs)) = Some (opc, (ostack, oregs, oflag, ors))"
  shows
    "opc = Suc ipc \<and> oflag = iflag \<and> ors = irs"
    "\<exists>v r. istack = v # r # ostack \<and> nat r < length iregs \<and> r \<ge> 0 \<and> oregs = iregs[nat r := v]"
proof -
  from assms obtain v r rstack where istack: "istack = v # r # rstack" using step_pop2_pred by force
  hence step: "step STORE (ipc, (istack, iregs, iflag, irs)) = Some (Suc ipc, (rstack, iregs[nat r := v], iflag, irs))" by (metis Suc_eq_plus1 assms option.distinct(1) step.simps(12))
  from this assms show "opc = Suc ipc \<and> oflag = iflag \<and> ors = irs" by simp
  from step assms have ostack: "ostack = rstack" by simp
  have "istack = v # r # ostack \<and> nat r < length iregs \<and> r \<ge> 0 \<and> oregs = iregs[nat r := v]"
    by (metis Pair_inject assms istack option.inject option.simps(3) step.simps(12))
  thus "\<exists>v r. istack = v # r # ostack \<and> nat r < length iregs \<and> r \<ge> 0 \<and> oregs = iregs[nat r := v]" by blast
qed

lemma step_store_succ:
  assumes "step STORE (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc"
proof -
  from assms obtain v r sta m f rs where split: "(v # r # sta, m, f, rs) = ist" using step_pop2_pred by metis
  from assms this show ?thesis by (cases "r \<ge> 0 \<and> nat r < length m", auto)
qed

lemma step_storei:
  assumes "step (STOREI r v) (ipc, (istack, iregs, iflag, irs)) = Some (opc, (ostack, oregs, oflag, ors))"
  shows
    "opc = Suc ipc \<and> ostack = istack \<and> oregs = iregs[r := v] \<and> oflag = iflag \<and> ors = irs \<and> r < length iregs"
  using assms by (metis Pair_inject Suc_eq_plus1 option.sel option.simps(3) step.simps(13))

lemma step_storei_succ:
  assumes "step (STOREI r v) (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc"
proof -
  from assms obtain sta m f rs where ist: "ist = (sta, m, f, rs)" using prod_cases4 by blast
  moreover from assms obtain osta om ofl ors where ost: "st = (osta, om, ofl, ors)" using prod_cases4 by blast
  ultimately show ?thesis using step_storei using assms by blast
qed

lemma step_copy:
  assumes "step COPY (ipc, (istack, iregs, iflag, irs)) = Some (opc, (ostack, oregs, oflag, ors))"
  shows "opc = Suc ipc \<and> ostack = (int_of iflag) # istack \<and> oregs = iregs \<and> oflag = iflag \<and> ors = irs"
  using assms by (metis Suc_eq_plus1 old.prod.inject option.inject step.simps(14))

lemma step_copy_succ:
  assumes "step COPY (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc"
proof -
  from assms obtain sta m f rs where "ist = (sta, m, f, rs)" using prod_cases4 by blast
  from assms this show ?thesis by auto
qed

lemma step_call:
  assumes "step CALL (ipc, (istack, iregs, iflag, irs)) = Some (opc, (ostack, oregs, oflag, ors))"
  shows
    "oregs = iregs \<and> oflag = iflag \<and> ors = irs"
    "\<exists>rstack. istack = int opc # rstack \<and> ostack = int ipc # rstack"
proof -
  from assms obtain x rstack where istack: "istack = x # rstack" by (meson Pair_inject step_pop1_pred)
  then have "x \<ge> 0 \<and> nat x = opc" using assms by (metis Pair_inject option.sel option.simps(3) step.simps(15))
  then show "\<exists>rstack. istack = int opc # rstack \<and> ostack = int ipc # rstack" using istack assms by auto
  then show "oregs = iregs \<and> oflag = iflag \<and> ors = irs" using assms by auto
qed

lemma step_return:
  assumes "step RETURN (ipc, (istack, iregs, iflag, irs)) = Some (opc, (ostack, oregs, oflag, ors))"
  shows
    "oregs = iregs \<and> oflag = iflag \<and> ors = irs \<and> istack = int (opc - 1) # ostack \<and> opc > 0"
proof -
  from assms obtain x rstack where istack: "istack = x # rstack" using step_pop1_pred by force
  hence gr: "x \<ge> 0" using assms by (metis option.distinct(1) step.simps(16))
  from istack this have "nat x + 1 = opc" using assms by simp
  from this gr show ?thesis using assms istack by auto
qed

lemma step_storec:
  assumes "step (STOREC c d) (ipc, (istack, iregs, iflag, irs)) = Some (opc, (ostack, oregs, oflag, ors))"
  shows
    "opc = Suc ipc \<and> ostack = istack \<and> oregs = iregs \<and> oflag = iflag \<and> ors = c # irs \<and> d = 0"
  by (metis assms list.inject option.distinct(1) option.inject state_pc.simps step.simps(14) step.simps(17) step_copy)

lemma step_storec_succ:
  assumes "step (STOREC c d) (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc"
proof -
  from assms obtain sta m f rs where "ist = (sta, m, f, rs)" using prod_cases4 by blast
  from assms this show ?thesis by (cases "d = 0"; auto)
qed

lemma step_setf:
  assumes "step (SETF b) (ipc, (istack, iregs, iflag, irs)) = Some (opc, (ostack, oregs, oflag, ors))"
  shows
    "opc = Suc ipc \<and> ostack = istack \<and> oregs = iregs \<and> oflag = b \<and> ors = irs"
  using assms by simp

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
  case 9 show ?case using step_lid_succ assms by (smt Collect_empty_eq collect_step.simps lookup.simps) next
  case 10 show ?case using step_store_succ assms by auto next
  case 11 show ?case using step_storei_succ assms by (smt Collect_empty_eq collect_step.simps lookup.simps) next
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

lemma deep_merge_lookup_le:
  assumes "\<exists>mid. (st::'a::absstate) \<le> mid \<and> (pc, mid) \<in> sts"
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
    hence "finite_sup{st. (p, st) \<in> {(k, v)}} = v" by (simp add: sup_absorb1)
    have "finite_sup{st. (p, st) \<in> set ((k, v) # xs)} = finite_sup{st. (p, st) \<in> (set xs \<union> {?x})}" by simp
    hence "finite_sup{st. (p, st) \<in> set ((k, v) # xs)} = finite_sup({st. (p, st) \<in> set xs} \<union> {st. (p, st) \<in> {?x}})" using prod_set_split by metis
    then show ?thesis using finite_sup_union_distrib by metis
  next
    case False
    hence bot: "finite_sup{st. (p, st) \<in> {?x}} = \<bottom>" by simp
    from False have "{st. (p, st) \<in> set (?x # xs)} = {st. (p, st) \<in> set xs}" by simp
    from this have "finite_sup{st. (p, st) \<in> set (?x # xs)} = finite_sup{st. (p, st) \<in> set xs} \<squnion> \<bottom>" by (simp add: sup_absorb1)
    from this bot show ?thesis by presburger
  qed
  thus "lookup (deep_merge (set (?x # xs))) p = lookup (deep_merge (set xs) \<squnion> single k v) p" by (simp add: sup_absorb1)
qed

lemma deep_merge_bot: "deep_merge (set ((k, \<bottom>) # xs)) = deep_merge (set xs)"
proof (rule state_map_eq_fwd)
  fix p
  have "(\<bottom>::'a) = lookup (single k \<bottom>) p" by simp
  thus "lookup (deep_merge (set ((k, \<bottom>) # xs))) p = lookup (deep_merge (set xs)) p"
    using deep_merge_cons sup_lookup sup_absorb1 bot.extremum by metis
qed

end

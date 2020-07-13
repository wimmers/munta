theory UPPAAL_Asm_AbsInt
imports
  UPPAAL_Asm_AbsInt_Flat
  "HOL.List"
  "HOL.Complete_Lattices"
begin

(* ############# *)
(* Notation *)
notation
  sup (infixl "\<squnion>" 65) and
  inf (infixl "\<sqinter>" 70) and
  bot ("\<bottom>") and
  top ("\<top>") and
  Inf ("\<Sqinter>") and
  Sup ("\<Squnion>")

syntax
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3INF _./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3INF _\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3SUP _./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3SUP _\<in>_./ _)" [0, 0, 10] 10)

syntax
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)

translations
  "\<Sqinter>x y. f"   \<rightleftharpoons> "\<Sqinter>x. \<Sqinter>y. f"
  "\<Sqinter>x. f"     \<rightleftharpoons> "\<Sqinter>(CONST range (\<lambda>x. f))"
  "\<Sqinter>x\<in>A. f"   \<rightleftharpoons> "CONST Inf ((\<lambda>x. f) ` A)"
  "\<Squnion>x y. f"   \<rightleftharpoons> "\<Squnion>x. \<Squnion>y. f"
  "\<Squnion>x. f"     \<rightleftharpoons> "\<Squnion>(CONST range (\<lambda>x. f))"
  "\<Squnion>x\<in>A. f"   \<rightleftharpoons> "CONST Sup ((\<lambda>x. f) `  A)"
(* ############*)

subsection "State Map"

datatype 'a state_map = SM "addr \<Rightarrow> 'a"

lemma state_map_single_constructor: "\<exists>m. a = SM m"
  using state_map.exhaust by auto

fun lookup :: "'a state_map \<Rightarrow> addr \<Rightarrow> 'a" where
  "lookup (SM m) = m"

fun unwrap :: "'a state_map \<Rightarrow> addr \<Rightarrow> 'a" where
  "unwrap (SM m) = m"

lemma lookup_eq: "(\<And>k. lookup a k = lookup b k) \<Longrightarrow> (a = b)"
proof -
  assume ass: "\<And>k. lookup a k = lookup b k"
  obtain am bm where maps: "a = SM am" "b = SM bm" using state_map_single_constructor by blast
  have "\<And>am bm. ((\<And>k. lookup (SM am) k = lookup (SM bm) k) \<Longrightarrow> (SM am) = (SM bm))" by (simp add: ext)
  from this ass maps show ?thesis by auto
qed


fun domain :: "('b::bot) state_map \<Rightarrow> addr set" where
  "domain (SM m) = {a. m a \<noteq> \<bottom>}"

lemma state_map_eq_fwd: "(\<forall>p. lookup m p = lookup n p) \<Longrightarrow> m = n"
proof -
  assume lookeq: "\<forall>p. lookup m p = lookup n p"
  obtain mm where mm: "m = SM mm" using lookup.cases by blast
  obtain nm where nm: "n = SM nm" using lookup.cases by blast
  have "mm = nm" using lookeq nm mm by auto
  thus "m = n" using mm nm by blast
qed

lemma "(\<forall>p. lookup m p = lookup n p) \<longleftrightarrow> m = n" using state_map_eq_fwd by auto

instantiation state_map :: (order) order
begin
  definition less_eq_state_map :: "('a::order)state_map \<Rightarrow> 'a state_map \<Rightarrow> bool" where
  "C1 \<le> C2 \<longleftrightarrow> (\<forall>p. lookup C1 p \<le> lookup C2 p)"
  
  definition less_state_map :: "'a state_map \<Rightarrow> 'a state_map \<Rightarrow> bool" where
  "less_state_map x y = (x \<le> y \<and> \<not> y \<le> x)"
  
  instance proof (standard, goal_cases)
    case 1 show ?case by(simp add: less_state_map_def)
  next
    case 2 thus ?case by(auto simp: less_eq_state_map_def)
  next
    case 3 thus ?case using less_eq_state_map_def order_trans by fastforce
  next
    case 4 thus ?case by (simp add: less_eq_state_map_def dual_order.antisym state_map_eq_fwd)
  qed
end

instantiation state_map :: (bot) bot
begin
definition bot_state_map: "\<bottom> = SM (\<lambda>x. \<bottom>)"
instance ..
end

instantiation state_map :: (order_bot) order_bot
begin
lemma bot_lookup [simp]:
  "lookup \<bottom> x = \<bottom>"
  by (simp add: bot_state_map)
instance proof standard qed (simp add: less_eq_state_map_def)
end

instantiation state_map :: (top) top
begin
definition top_state_map[no_atp]: "\<top> = SM (\<lambda>x. \<top>)"
instance ..
end

instantiation state_map :: (order_top) order_top
begin
lemma top_lookup [simp]:
  "lookup \<top> x = \<top>"
  by (simp add: top_state_map)
instance proof standard qed (simp add: less_eq_state_map_def)
end

instantiation state_map :: (semilattice_sup) semilattice_sup
begin
definition "a \<squnion> b = SM (\<lambda>k. lookup a k \<squnion> lookup b k)"
lemma sup_lookup [simp]: "lookup (a \<squnion> b) x = lookup a x \<squnion> lookup b x"
  by (simp add: sup_state_map_def)
instance by standard (simp_all add: less_eq_state_map_def)
end

instantiation state_map :: (semilattice_inf) semilattice_inf
begin
definition "a \<sqinter> b = SM (\<lambda>x. lookup a x \<sqinter> lookup b x)"
lemma inf_apply [simp]: "lookup (a \<sqinter> b) x = lookup a x \<sqinter> lookup b x"
  by (simp add: inf_state_map_def)
instance by standard (simp_all add: less_eq_state_map_def)
end

instance state_map :: (lattice) lattice ..

instantiation state_map :: (Sup) Sup
begin
definition "\<Squnion>A = SM (\<lambda>x. \<Squnion>a\<in>A. lookup a x)"
lemma Sup_lookup [simp]: "lookup (\<Squnion>A) x = (\<Squnion>m\<in>A. lookup m x)"
  by (simp add: Sup_state_map_def)
instance ..
end

instantiation state_map :: (Inf) Inf
begin
definition "\<Sqinter>A = SM (\<lambda>x. \<Sqinter>a\<in>A. lookup a x)"
lemma Inf_lookup [simp]: "lookup (\<Sqinter>A) x = (\<Sqinter>m\<in>A. lookup m x)"
  by (simp add: Inf_state_map_def)
instance ..
end

instantiation state_map :: (complete_lattice) complete_lattice
begin
instance proof
  show "(x::'a state_map) \<in> A \<Longrightarrow> \<Sqinter>A \<le> x" for A x
  proof -
    fix x A assume ass: "(x::'a state_map) \<in> A"
    have "lookup (SM (\<lambda>x. \<Sqinter>a\<in>A. lookup a x)) p \<le> lookup x p" for p using ass le_INF_iff by fastforce
    thus "\<Sqinter>A \<le> x" by (simp add: less_eq_state_map_def)
  qed
  show "(\<And>x. x \<in> A \<Longrightarrow> (z::'a state_map) \<le> x) \<Longrightarrow> z \<le> \<Sqinter> A" for A z by (simp add: INF_greatest less_eq_state_map_def)
  show "(x::'a state_map) \<in> A \<Longrightarrow> x \<le> \<Squnion> A" for A x
  proof -
    fix x A assume ass: "(x::'a state_map) \<in> A"
    have "lookup x p \<le> lookup (SM (\<lambda>x. \<Squnion>a\<in>A. lookup a x)) p" for p using ass SUP_le_iff by fastforce
    thus "x \<le> \<Squnion>A" by (simp add: less_eq_state_map_def)
  qed
  show "(\<And>x. x \<in> A \<Longrightarrow> x \<le> (z::'a state_map)) \<Longrightarrow> \<Squnion> A \<le> z" for A z by (simp add: SUP_le_iff less_eq_state_map_def)
  show "\<Sqinter> ({}::'a state_map set) = \<top>" by (simp add: state_map_eq_fwd Inf_state_map_def)
  show "\<Squnion> ({}::'a state_map set) = \<bottom>" by (simp add: state_map_eq_fwd Sup_state_map_def)
qed
end

class absstate = complete_lattice
instantiation state_map :: (absstate) absstate begin instance proof qed end

subsection "Abstract Stepping"

text \<open>Type for any abstract stepping function. Performs a single forward step on an abstract state.\<close>
type_synonym 'a astep = "instr \<Rightarrow> addr \<Rightarrow> 'a \<Rightarrow> addr \<Rightarrow> 'a"

fun astep_succs :: "('a::bot) astep \<Rightarrow> instr \<Rightarrow> addr \<Rightarrow> 'a \<Rightarrow> addr set" where
  "astep_succs f op ipc ins = {pc. f op ipc ins pc \<noteq> \<bottom>}"

text \<open>Performs a step for all states in the map and returns the join of all resulting states at a given address.
  Could also be seen as inverse-stepping, i.e. pulling all resulting states ending at the given address.\<close>
fun slurp :: "('a::{Sup, bot}) astep \<Rightarrow> program \<Rightarrow> 'a state_map \<Rightarrow> addr \<Rightarrow> 'a" where
  "slurp f prog ctx pc = \<Squnion>{ost. \<exists>ipc op. prog ipc = Some op \<and> lookup ctx ipc \<noteq> \<bottom> \<and> f op ipc (lookup ctx ipc) pc = ost}"

text \<open>Perform a single step over an entire map\<close>
fun step_map :: "('a::{bot, Sup}) astep \<Rightarrow> program \<Rightarrow> 'a state_map \<Rightarrow> 'a state_map" where
  "step_map f prog ctx = SM (slurp f prog ctx)"

text \<open>Advance the Abstract Interpretation one step forward, i.e. step the map and merge it with the previous.\<close>
fun advance :: "('a::{semilattice_sup, Sup, bot}) astep \<Rightarrow> program \<Rightarrow> 'a state_map \<Rightarrow> 'a state_map" where
  "advance f prog ctx = ctx \<squnion> step_map f prog ctx"

text \<open>Full Abstract Interpretation Loop, advancing n times\<close>
fun loop :: "('a::{semilattice_sup, Sup, bot}) astep \<Rightarrow> program \<Rightarrow> fuel \<Rightarrow> 'a state_map \<Rightarrow> 'a state_map" where
  "loop f prog 0 st = st" |
  "loop f prog (Suc n) st = loop f prog n (advance f prog st)"

lemma loop_pull: "loop f prog n (advance f prog st) = advance f prog (loop f prog n st)"
  apply(induction n arbitrary: st) by simp simp

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

fun collect_step :: "instr \<Rightarrow> addr \<Rightarrow> collect_state set \<Rightarrow> addr \<Rightarrow> collect_state set" where
  "collect_step op ipc sts pc = {st. \<exists>ist\<in>sts. step op (ipc, ist) = Some (pc, st)}"

definition[simp]: "collect_slurp \<equiv> slurp collect_step"

lemma collect_slurp_fwd:
  assumes
    "ist \<in> lookup ctx ipc"
    "prog ipc = Some op"
    "step op (ipc, ist) = Some (pc, ost)"
  shows "ost \<in> collect_slurp prog ctx pc"
proof -
  have "ost \<in> collect_step op ipc (lookup ctx ipc) pc" using assms(1) assms(3) by auto
  from assms(2) this show ?thesis by auto
qed

lemma collect_slurp_bwd:
  assumes "ost \<in> collect_slurp prog ctx pc"
  shows "\<exists>ist op ipc. ist \<in> lookup ctx ipc \<and> prog ipc = Some op \<and> step op (ipc, ist) = Some (pc, ost)"
proof -
  from assms obtain ipc op where ipcop: "prog ipc = Some op" "ost \<in> collect_step op ipc (lookup ctx ipc) pc" by auto
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

subsection \<open>Abstract\<close>

locale AbsInt =
fixes \<gamma> :: "'as::absstate \<Rightarrow> collect_state set"
  assumes mono_gamma: "a \<le> b \<Longrightarrow> \<gamma> a \<le> \<gamma> b"
  and gamma_Top[simp]: "\<gamma> \<top> = UNIV"
fixes ai_step :: "'as astep"
  assumes astep_correct: "collect_step op ipc (\<gamma> a) pc \<le> \<gamma> (ai_step op ipc a pc)"
  and astep_keep_bot: "ai_step op ipc \<bottom> pc = \<bottom>"
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

definition[simp]: "ai_slurp \<equiv> slurp ai_step"
lemma ai_slurp_correct:
  assumes "a \<le> \<gamma>_map b"
  shows "collect_slurp prog a pc \<le> \<gamma> (ai_slurp prog b pc)"
proof standard
  fix x assume "x \<in> collect_slurp prog a pc"
  from this obtain ipc op where slurped: "prog ipc = Some op" "lookup a ipc \<noteq> \<bottom>" "x \<in> collect_step op ipc (lookup a ipc) pc" by auto
  from assms have "lookup a ipc \<subseteq> \<gamma> (lookup b ipc)" using \<gamma>_lookup_le by blast
  from slurped(3) this have "x \<in> collect_step op ipc (\<gamma> (lookup b ipc)) pc" by auto
  from this have "x \<in> \<gamma> (ai_step op ipc (lookup b ipc) pc)" using astep_correct ..
  from this obtain ax where ax: "x \<in> \<gamma> ax" "ax = ai_step op ipc (lookup b ipc) pc" using slurped by blast
  have "ax \<le> ai_slurp prog b pc"
  proof(cases "lookup b ipc = \<bottom>")
    case False
    from this have "ax \<in> {ost. \<exists>ipc op. prog ipc = Some op \<and> lookup b ipc \<noteq> \<bottom> \<and> ai_step op ipc (lookup b ipc) pc = ost}" using slurped(1) ax(2) by blast
    then show ?thesis by (simp add: Sup_upper)
  qed (simp add: astep_keep_bot ax(2))
  thus "x \<in> \<gamma> (ai_slurp prog b pc)" using ax mono_gamma by auto
qed

definition[simp]: "ai_step_map \<equiv> step_map ai_step"
lemma ai_step_map_correct:
  assumes "a \<le> \<gamma>_map b"
  shows "collect_step_map prog a \<le> \<gamma>_map (ai_step_map prog b)"
  using ai_slurp_correct assms by (simp add: less_eq_state_map_def)

definition[simp]: "ai_advance \<equiv> advance ai_step"
lemma ai_advance_correct:
  assumes "a \<le> \<gamma>_map b"
  shows "collect_advance prog a \<le> \<gamma>_map (ai_advance prog b)"
proof -
  have "\<gamma>_map (ai_step_map prog b) \<le> \<gamma>_map (advance ai_step prog b)" by (metis \<gamma>_map_mono advance.simps ai_step_map_def sup_ge2)
  hence step_le: "collect_step_map prog a \<le> \<gamma>_map (advance ai_step prog b)" using ai_step_map_correct order.trans assms by blast

  have "b \<le> advance ai_step prog b" by simp
  then have "a \<le> \<gamma>_map (advance ai_step prog b)" by (meson \<gamma>_map_mono assms order.trans)

  from step_le this show ?thesis by force
qed

definition[simp]: "ai_loop \<equiv> loop ai_step"
theorem ai_loop_correct: "collect_loop prog n (\<gamma>_map entry) \<le> \<gamma>_map (ai_loop prog n entry)"
proof (induction n arbitrary: entry)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc this have "collect_advance prog (collect_loop prog n (\<gamma>_map entry)) \<le> \<gamma>_map (ai_advance prog (ai_loop prog n entry))" using ai_advance_correct by blast
  then have "advance collect_step prog (loop collect_step prog n (\<gamma>_map entry)) \<le> \<gamma>_map (advance ai_step prog (loop ai_step prog n entry))" by auto
  then have "loop collect_step prog n (advance collect_step prog (\<gamma>_map entry)) \<le> \<gamma>_map (loop ai_step prog n (advance ai_step prog entry))" using loop_pull by metis
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

lemma step_jmpz_succ:
  assumes "step (JMPZ tgt) (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc \<or> pc = tgt"
proof -
  from assms obtain sta m f rs where "ist = (sta, m, f, rs)" by (metis prod_cases4)
  from assms this show ?thesis by auto
qed

lemma step_add_succ:
  assumes "step ADD (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc"
proof -
  from assms obtain a b sta m f rs where split: "(a # b # sta, m, f, rs) = ist" using step_pop2_pred by metis
  from assms this show ?thesis by auto
qed

lemma step_not_succ:
  assumes "step NOT (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc"
proof -
  from assms obtain b sta m f rs where "ist = (b # sta, m, f, rs)" using step_pop1_pred by blast
  from assms this show ?thesis by auto
qed

lemma step_and_succ:
  assumes "step AND (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc"
proof -
  from assms obtain b sta m f rs where "ist = (b # sta, m, f, rs)" using step_pop1_pred by blast
  from assms this show ?thesis by (cases "b = 0 \<or> b = 1"; auto)
qed

lemma step_lt_succ:
  assumes "step LT (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc"
proof -
  from assms obtain a b sta m f rs where split: "(a # b # sta, m, f, rs) = ist" using step_pop2_pred by metis
  from assms this show ?thesis by auto
qed

lemma step_le_succ:
  assumes "step LE (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc"
proof -
  from assms obtain a b sta m f rs where split: "(a # b # sta, m, f, rs) = ist" using step_pop2_pred by metis
  from assms this show ?thesis by auto
qed

lemma step_eq_succ:
  assumes "step EQ (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc"
proof -
  from assms obtain a b sta m f rs where split: "(a # b # sta, m, f, rs) = ist" using step_pop2_pred by metis
  from assms this show ?thesis by auto
qed

lemma step_push_succ:
  assumes "step (PUSH x) (ipc, ist) = Some (pc, st)"
  shows "pc = Suc ipc"
proof -
  from assms obtain sta m f rs where "ist = (sta, m, f, rs)" using prod_cases4 by blast
  from assms this show ?thesis by auto
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

lemma collect_step_jmpz_succ: "pc \<noteq> Suc ipc \<Longrightarrow> pc \<noteq> tgt \<Longrightarrow> collect_step (JMPZ tgt) ipc sts pc = \<bottom>" using step_jmpz_succ by fastforce
lemma collect_step_fallthrough_succ:
  assumes "pc \<noteq> Suc ipc"
  shows
    "collect_step ADD ipc sts pc = \<bottom>"
    "collect_step NOT ipc sts pc = \<bottom>"
    "collect_step AND ipc sts pc = \<bottom>"
    "collect_step LT ipc sts pc = \<bottom>"
    "collect_step LE ipc sts pc = \<bottom>"
    "collect_step EQ ipc sts pc = \<bottom>"
    "collect_step (PUSH x) ipc sts pc = \<bottom>"
    "collect_step POP ipc sts pc = \<bottom>"
    "collect_step (LID r) ipc sts pc = \<bottom>"
    "collect_step STORE ipc sts pc = \<bottom>"
    "collect_step (STOREI r v) ipc sts pc = \<bottom>"
    "collect_step COPY ipc sts pc = \<bottom>"
    "collect_step (STOREC c d) ipc sts pc = \<bottom>"
    "collect_step (SETF b) ipc sts pc = \<bottom>"
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
    fix x assume "x \<in> collect_step (STOREC c d) ipc sts pc"
    from this obtain ist where "ist \<in> sts" "step (STOREC c d) (ipc, ist) = Some (pc, x)" by auto
    from this(2) assms show "x \<in> {}" using step_storec_succ by blast
  qed
next
  case 14 then show ?case using assms by auto
qed
lemma collect_step_halt_succ: "collect_step HALT ipc sts pc = \<bottom>" by simp

lemmas collect_step_succ = collect_step_jmpz_succ collect_step_fallthrough_succ

subsection \<open>Alternative Type for Abstract Step Functions\<close>

text\<open>This type is easier to implement in certain cases and works better for code generation,
  but it may not be unique wrt. its {@term unique_astep}\<close>
type_synonym 'a asetstep = "instr \<Rightarrow> addr \<Rightarrow> 'a \<Rightarrow> (addr * 'a) set"

fun unique_astep :: "('a::Sup) asetstep \<Rightarrow> 'a astep" where
  "unique_astep f op ipc ins pc = \<Squnion>{st. (pc, st) \<in> f op ipc ins}"

lemma unique_astep_unique:
  assumes
    "(pc, (st::'a::absstate)) \<in> f op ipc ins"
    "\<And>sst. (pc, sst) \<in> f op ipc ins \<Longrightarrow> sst = st"
  shows "unique_astep f op ipc ins pc = st" 
proof -
  from assms have "{st. (pc, st) \<in> f op ipc ins} = {st}" by blast
  thus ?thesis using ccpo_Sup_singleton[of st] by simp
qed

end

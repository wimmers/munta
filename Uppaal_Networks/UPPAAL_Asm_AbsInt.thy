theory UPPAAL_Asm_AbsInt
imports
  UPPAAL_Asm_AbsInt_Flat
  "HOL.List"
  "HOL.Complete_Lattices"
begin

(*---------*)
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
(*---------*)

subsection "State Map"

datatype 'a state_map = SM "addr \<Rightarrow> 'a"

lemma state_map_single_constructor: "\<exists>m. a = SM m"
  using state_map.exhaust by auto

fun lookup :: "'a state_map \<Rightarrow> addr \<Rightarrow> 'a" where
  "lookup (SM m) = m"

fun unwrap :: "'a state_map \<Rightarrow> addr \<Rightarrow> 'a" where
  "unwrap (SM m) = m"

lemma lookup_eq: "(\<And>k kk. lookup a k = lookup b k) \<Longrightarrow> (a = b)"
proof -
  assume ass: "\<And>k kk. lookup a k = lookup b k"
  obtain am bm where maps: "a = SM am" "b = SM bm" using state_map_single_constructor by blast
  have "\<And>am bm. ((\<And>k kk. lookup (SM am) k = lookup (SM bm) k) \<Longrightarrow> (SM am) = (SM bm))" by (simp add: ext)
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
lemma bot_lookup [simp, code]:
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
lemma inf_apply [simp, code]: "lookup (a \<sqinter> b) x = lookup a x \<sqinter> lookup b x"
  by (simp add: inf_state_map_def)
instance by standard (simp_all add: less_eq_state_map_def)
end

instance state_map :: (lattice) lattice ..

instantiation state_map :: (Sup) Sup
begin
definition "\<Squnion>A = SM (\<lambda>x. \<Squnion>a\<in>A. lookup a x)"
lemma Sup_lookup [simp, code]: "lookup (\<Squnion>A) x = (\<Squnion>m\<in>A. lookup m x)"
  by (simp add: Sup_state_map_def)
instance ..
end

instantiation state_map :: (Inf) Inf
begin
definition "\<Sqinter>A = SM (\<lambda>x. \<Sqinter>a\<in>A. lookup a x)"
lemma Inf_lookup [simp, code]: "lookup (\<Sqinter>A) x = (\<Sqinter>m\<in>A. lookup m x)"
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

class absstate_base = semilattice_sup + top

class absstate = absstate_base + bot
instantiation state_map :: (absstate) absstate begin instance proof qed end

subsection "Abstract Stepping"

type_synonym 'a stepfn = "instr \<Rightarrow> addr \<Rightarrow> 'a \<Rightarrow> addr \<Rightarrow> 'a"

fun stepped_to :: "'a stepfn \<Rightarrow> program \<Rightarrow> 'a state_map \<Rightarrow> addr \<Rightarrow> ('a::Sup)" where
  "stepped_to f prog ctx pc = \<Squnion>{ost. \<exists>ipc op. prog ipc = Some op \<and> f op ipc (lookup ctx ipc) pc = ost}"

fun step_all :: "('a::Sup) stepfn \<Rightarrow> program \<Rightarrow> 'a state_map \<Rightarrow> 'a state_map" where
  "step_all f prog ctx = SM (stepped_to f prog ctx)"

subsection "Collecting Semantics"

type_synonym collect_state = "stack * rstate * flag * nat list"
type_synonym collect_ctx = "collect_state set state_map"

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

fun states_domain :: "(addr * 'a) set \<Rightarrow> addr set" where
  "states_domain states = fst ` states"

fun propagate :: "'a set state_map \<Rightarrow> (addr * 'a) set \<Rightarrow> 'a set state_map" where
  "propagate oldmap ss = oldmap \<squnion> deepen ss"

lemma propagate_preserve: "inm \<le> propagate inm sts" by simp

inductive_set stepped_to_base :: "collect_state set stepfn" for op ipc sts pc where
  "ist \<in> sts
    \<Longrightarrow> step op (ipc, ist) = Some (pc, st)
    \<Longrightarrow> st \<in> stepped_to_base op ipc sts pc"

definition[simp]: "stepped_to_collect \<equiv> stepped_to stepped_to_base"

lemma stepped_to_fwd:
  assumes
    "ist \<in> lookup ctx ipc"
    "prog ipc = Some op"
    "step op (ipc, ist) = Some (pc, ost)"
  shows "ost \<in> stepped_to_collect prog ctx pc"
proof -
  have "ost \<in> stepped_to_base op ipc (lookup ctx ipc) pc" using assms(1) assms(3) stepped_to_base.intros by blast
  from assms(2) this show ?thesis by auto
qed

lemma stepped_to_bwd:
  assumes "ost \<in> stepped_to_collect prog ctx pc"
  shows "\<exists>ist op ipc. ist \<in> lookup ctx ipc \<and> prog ipc = Some op \<and> step op (ipc, ist) = Some (pc, ost)"
proof -
  from assms obtain ipc op where ipcop: "prog ipc = Some op" "ost \<in> stepped_to_base op ipc (lookup ctx ipc) pc" by auto
  from this(2) obtain ist where ist: "ist \<in> lookup ctx ipc" "step op (ipc, ist) = Some (pc, ost)" by cases
  from ist(1) ipcop(1) ist(2) show ?thesis by blast
qed

definition[simp]: "step_all_collect \<equiv> step_all stepped_to_base"

lemma step_all_correct: "flatten (step_all_collect prog (deepen flat)) = step_all_flat prog flat"
proof (intro Set.equalityI Set.subsetI)
  fix x assume ass: "x \<in> flatten (step_all_collect prog (deepen flat))"
  then obtain pc st where splitx: "x = (pc, st)" using prod.exhaust_sel by blast
  from this ass have "st \<in> lookup (step_all_collect prog (deepen flat)) pc" using flatten_bwd by fastforce
  hence stepped: "st \<in> stepped_to_collect prog (deepen flat) pc" by simp
  from this obtain ist ipc op where stuff: "ist \<in> lookup (deepen flat) ipc" "prog ipc = Some op" "step op (ipc, ist) = Some (pc, st)" using stepped_to_bwd by blast
  hence bwd: "(ipc, ist) \<in> flat" by (simp add: deepen_bwd)
  from this stuff show "x \<in> step_all_flat prog flat" using splitx step_all_flat.intros by blast
next
  fix x assume ass: "x \<in> step_all_flat prog flat"
  then obtain pc st where splitx: "x = (pc, st)" using prod.exhaust_sel by blast
  from ass obtain ipc ist instr where stuff: "(ipc, ist) \<in> flat" "prog ipc = Some instr" "step instr (ipc, ist) = Some (pc, st)" by cases (simp add: splitx)
  from stuff have "ist \<in> lookup (deepen flat) ipc" by (simp add: states_at.intros)
  from this stuff have "st \<in> stepped_to_collect prog (deepen flat) pc" using stepped_to_fwd by blast
  thus "x \<in> flatten (step_all_collect prog (deepen flat))" using splitx by (simp add: flatten_fwd)
qed

fun collect_step :: "program \<Rightarrow> collect_ctx \<Rightarrow> collect_ctx" where
  "collect_step prog ctx = ctx \<squnion> step_all_collect prog ctx"

lemma collect_step_correct: "flatten (collect_step prog (deepen flat)) = collect_step_flat prog flat"
proof -
  have "collect_step prog (deepen flat) = deepen flat \<squnion> step_all_collect prog (deepen flat)" by simp
  hence "flatten (collect_step prog (deepen flat)) = flatten (deepen flat) \<squnion> flatten (step_all_collect prog (deepen flat))" by (simp add: flatten_lift_sup flatten_deepen)
  hence "flatten (collect_step prog (deepen flat)) = flat \<squnion> step_all_flat prog flat" using flatten_deepen step_all_correct by blast
  thus ?thesis by (simp add: collect_step_flat_def)
qed

lemma collect_step_correct2: "flatten (collect_step prog m) = collect_step_flat prog (flatten m)"
  using collect_step_correct deepen_flatten by metis

fun loop :: "(program \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> program \<Rightarrow> fuel \<Rightarrow> 'a \<Rightarrow> 'a" where
  "loop f prog 0 st = st" |
  "loop f prog (Suc n) st = loop f prog n (f prog st)"

definition[simp]: "collect_loop \<equiv> loop collect_step"

lemma collect_loop_as_flat:
  "flatten (collect_loop prog n (deepen flat)) = collect_loop_flat prog n flat"
proof (induction n arbitrary: flat)
  case 0 then show ?case using flatten_deepen by auto
next
  case (Suc n)
  obtain flatstep where flatstep: "deepen flatstep = collect_step prog (deepen flat)" using deepen_flatten by blast
  hence "flatten (collect_loop prog (Suc n) (deepen flat)) = flatten (collect_loop prog n (deepen flatstep))" by simp
  from this Suc have loop: "flatten (collect_loop prog (Suc n) (deepen flat)) = collect_loop_flat prog n flatstep" by simp
  have step: "flatstep = collect_step_flat prog flat" by (metis collect_step_correct flatstep flatten_deepen)
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
  "errors_loop prog (Suc n) ctx = errors_all prog ctx \<squnion> errors_loop prog n (collect_step prog ctx)"

lemma errors_loop_as_flat:
  "errors_loop prog n (deepen flat) = errors_loop_flat prog n flat"
proof (induction n arbitrary: flat)
  case 0 then show ?case by simp
next
  case (Suc n)
  then show ?case by (metis collect_step_correct deepen_flatten errors_all_as_flat errors_loop.simps(2) errors_loop_flat.simps(2))
qed

subsection \<open>Abstract\<close>

locale AbsInt =
fixes \<gamma> :: "'as::absstate \<Rightarrow> collect_state set"
  assumes mono_gamma: "a \<le> b \<Longrightarrow> \<gamma> a \<le> \<gamma> b"
  and gamma_Top[simp]: "\<gamma> \<top> = UNIV"
fixes astep :: "'as stepfn"
  assumes astep_sound: "stepped_to_base op ipc (\<gamma> a) pc \<le> \<gamma> (astep op ipc a pc)"
begin

fun \<gamma>_map :: "'as state_map \<Rightarrow> collect_ctx" where
  "\<gamma>_map (SM m) = SM (\<lambda>pc. \<gamma> (m pc))"

fun ai_step :: "program \<Rightarrow> 'as state_map \<Rightarrow> 'as state_map" where
  "ai_step prog st = undefined"

definition[simp]: "ai_loop \<equiv> loop ai_step"

lemma ai_loop_correct: "collect_loop prog n (\<gamma>_map entry) \<le> \<gamma>_map (ai_loop prog n entry)" sorry

end

end
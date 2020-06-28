theory UPPAAL_Asm_AbsInt
imports
  UPPAAL_Asm_AbsInt_Flat
  "HOL.List"
  "HOL.Complete_Lattices"
begin

(*---------*)
(* Notation *)
notation bot ("\<bottom>")
notation top ("\<top>")
notation inf (infixl "\<sqinter>" 70)
notation sup (infixl "\<squnion>" 65)
notation Inf ("\<Sqinter>")
notation Sup ("\<Squnion>")

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

subsection "Errors"

datatype interpret_error = InvalAddr addr | StepFailed addr

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
instance proof standard
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

inductive_set states_at for states pc where
  "(pc, s) \<in> states \<Longrightarrow> s \<in> states_at states pc"

fun deepen :: "(addr * 'a) set \<Rightarrow> 'a set state_map" where
  "deepen states = SM (states_at states)"

lemma deepen_fwd: "(pc, st) \<in> flat \<Longrightarrow> st \<in> lookup (deepen flat) pc" by (simp add: states_at.intros)
lemma deepen_bwd: "st \<in> lookup (deepen flat) pc \<Longrightarrow> (pc, st) \<in> flat" by (simp add: states_at.simps)

(*fun flatten :: "'a set state_map \<Rightarrow> (addr * 'a) set" where
  "flatten sm = {(pc, st). st \<in> lookup sm pc}"*)

inductive_set flatten for sm where
  "st \<in> lookup sm pc \<Longrightarrow> (pc, st) \<in> flatten sm"

lemma flatten_fwd: "st \<in> lookup deep pc \<Longrightarrow> (pc, st) \<in> flatten deep" by (simp add: flatten.intros)
lemma flatten_bwd: "(pc, st) \<in> flatten deep \<Longrightarrow> st \<in> lookup deep pc" by (meson flatten.cases) 

subsection "Collecting Semantics"

type_synonym collect_state = "stack * rstate * flag * nat list"
type_synonym collect_ctx = "collect_state set state_map"

fun states_domain :: "(addr * 'a) set \<Rightarrow> addr set" where
  "states_domain states = fst ` states"

fun propagate :: "'a set state_map \<Rightarrow> (addr * 'a) set \<Rightarrow> 'a set state_map" where
  "propagate oldmap ss = oldmap \<squnion> deepen ss"

lemma propagate_preserve: "inm \<le> propagate inm sts" by simp

inductive_set stepped_to for prog ctx pc where
  "ist \<in> lookup ctx ipc
    \<Longrightarrow> program ipc = Some op
    \<Longrightarrow> step op (ipc, ist) = Some (pc, st)
    \<Longrightarrow> st \<in> stepped_to prog ctx pc"

(*lemma "stepped_to prog ctx pc = {st. \<exists>ipc ist op. (ist \<in> lookup ctx ipc) \<and> (program ipc = Some op) \<and> (step op (ipc, ist) = Some (pc, st))}"*)

fun step_all :: "program \<Rightarrow> collect_ctx \<Rightarrow> collect_ctx" where
  "step_all prog ctx = SM (stepped_to prog ctx)"

(*definition step_all :: "instr \<Rightarrow> addr \<Rightarrow> collect_state set \<Rightarrow> state set" where
  "step_all op pc instates =
    {outs. (\<exists>ins\<in>instates. step op (pc, ins) = Some outs)}"*)

lemma step_all_correct: "flatten (step_all prog (deepen flat)) = step_all_flat prog flat"
proof standard
  show "flatten (step_all prog (deepen flat)) \<subseteq> step_all_flat prog flat"
  proof standard
    fix x assume ass: "x \<in> flatten (step_all prog (deepen flat))"
    then obtain pc st where splitx: "x = (pc, st)" using prod.exhaust_sel by blast
    from this ass have "st \<in> lookup (step_all prog (deepen flat)) pc" using flatten_bwd by fastforce
    hence "st \<in> stepped_to prog (deepen flat) pc" by simp

    thus "x \<in> step_all_flat prog flat" using step_all_flat_eq by blast
  qed
  show "step_all_flat prog flat \<subseteq> flatten (step_all prog (deepen flat))" sorry
qed

definition error_all :: "instr \<Rightarrow> addr \<Rightarrow> collect_state set \<Rightarrow> interpret_error set" where
  "error_all op pc instates =
     (if (\<exists>ins\<in>instates. step op (pc, ins) = None) then {StepFailed pc} else {})"

fun collect_step :: "program \<Rightarrow> collect_ctx \<Rightarrow> collect_ctx" where
  "collect_step prog ctx = ctx \<squnion> step_all prog ctx"

fun collect_loop :: "program \<Rightarrow> fuel \<Rightarrow> collect_ctx \<Rightarrow> collect_ctx" where
  "collect_loop prog 0 st = st" |
  "collect_loop prog (Suc n) st = collect_loop prog n (collect_step prog st)"

lemma collect_step_sound:
  assumes "collect_step prog inctx = outctx"
  shows "collect_step_flat prog (flatten inctx) = flatten outctx"
proof standard
  show "collect_step_flat prog (flatten inctx) \<subseteq> (flatten outctx::state set)"
  proof standard
    fix x::state obtain inpc inst where x_def: "x = (inpc, inst)" by (metis surj_pair)
    assume "x \<in> collect_step_flat prog (flatten inctx)"
    hence "x \<in> step_all_flat prog (flatten inctx) \<or> x \<in> flatten inctx" using collect_step_flat_def by auto
    thus "x \<in> flatten outctx"
    proof safe
      assume "x \<in> step_all_flat prog (flatten inctx)"
      show ?thesis sorry
    next
      assume "x \<in> flatten inctx"
      thus ?thesis using collect_step_preserve assms sorry
    qed
  qed

  show "flatten outctx \<subseteq> collect_step_flat prog (flatten inctx)"
  proof standard
    fix x 
    show "x \<in> flatten outctx \<Longrightarrow> x \<in> collect_step_flat prog (flatten inctx)" sorry
  qed
qed

(*lemma collect_step_sound:
"collect_step prog inctx = Some outctx
  \<Longrightarrow> outst \<in> lookup_def outctx outpc
  \<Longrightarrow> \<exists>inpc inst instr. (inst \<in> lookup_def inctx inpc) \<and> (prog inpc = Some instr) \<and> ((step instr (inpc, inst) = Some (outpc, outst)))" sorry*)

end
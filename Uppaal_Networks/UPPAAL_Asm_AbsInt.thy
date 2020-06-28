theory UPPAAL_Asm_AbsInt
imports
  UPPAAL_Asm_AbsInt_Flat
  "HOL.List"
  "HOL.Complete_Lattices"
begin

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

notation bot ("\<bottom>")
notation top ("\<top>")

fun domain :: "('b::bot) state_map \<Rightarrow> addr set" where
  "domain (SM m) = {a. m a \<noteq> \<bottom>}"

fun deepen :: "(addr * 'a) set \<Rightarrow> 'a set state_map" where
  "deepen states = SM (\<lambda>pc. {st. (\<exists>(spc, st) \<in> states. pc = spc)})"

fun flatten :: "'a set state_map \<Rightarrow> (addr * 'a) set" where
  "flatten sm = {(pc, st). st \<in> lookup sm pc}"

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



(*
instantiation state_map :: (complete_lattice) complete_lattice
begin

definition "\<Sqinter>sm = \<Sqinter>(unwrap \<acute> sm)"

definition "\<Squnion>sm = \<Sqinter>(unwrap \<acute> sm)"

instance
  by standard (auto intro: bool_induct)

end*)

subsection "Collecting Semantics"

type_synonym collect_state = "stack * rstate * flag * nat list"
type_synonym collect_ctx = "collect_state set state_map"

fun states_domain :: "(addr * 'a) set \<Rightarrow> addr set" where
  "states_domain states = fst ` states"

fun states_at :: "(addr * 'a) set \<Rightarrow> addr \<Rightarrow> 'a set" where
  "states_at states pc = snd ` {s\<in>states. fst s = pc}"

fun propagate :: "'a set state_map \<Rightarrow> (addr * 'a) set \<Rightarrow> 'a set state_map" where
  "propagate (SM oldmap) ss =
    (let newmap = (\<lambda>pc. oldmap pc \<union> (states_at ss pc))
    in (SM newmap))"

lemma propagate_preserve: "inm \<le> propagate inm sts" sorry

lemma mono_inside: "a \<le> b \<Longrightarrow> x \<in> lookup_def a pc \<Longrightarrow> x \<in> lookup_def b pc" sorry
lemma inside_mono: "x \<in> lookup_def a pc \<Longrightarrow> x \<in> lookup_def b pc \<Longrightarrow> a \<le> b" sorry

definition step_all :: "instr \<Rightarrow> addr \<Rightarrow> collect_state set \<Rightarrow> (state set * interpret_error set)" where
  "step_all op pc instates =
    ({outs. (\<exists>ins\<in>instates. step op (pc, ins) = Some outs)},
     (if (\<exists>ins\<in>instates. step op (pc, ins) = None) then {StepFailed pc} else {}))"

fun collect_step_single :: "program \<Rightarrow> addr \<Rightarrow> (collect_ctx * interpret_error set) \<Rightarrow> (collect_ctx * interpret_error set)" where
  "collect_step_single prog pc (ctx, inerrs) =
    (case prog pc of
      Some op \<Rightarrow> 
        let res = step_all op pc (lookup ctx pc) in
        (propagate ctx (fst res), snd res \<union> inerrs) |
      None \<Rightarrow> (ctx, { InvalAddr pc } \<union> inerrs))"

lemma collect_step_single_preserve:
  assumes "collect_step_single prog pc (inctx, inerrs) = (outctx, errors)"
  shows "inctx \<le> outctx"
proof (cases "prog pc")
  case None then show ?thesis using assms by simp
next
  case (Some op)
  from this assms have "outctx = propagate inctx (fst (step_all op pc (lookup inctx pc)))" unfolding Let_def
    by (metis (no_types, lifting) collect_step_single.simps fstI option.simps(5))
  then show ?thesis using propagate_preserve by blast
qed

fun collect_step :: "program \<Rightarrow> collect_ctx \<Rightarrow> collect_ctx" where
  "collect_step prog ctx =
    fst (fold (collect_step_single prog) (sorted_list_of_set (domain ctx)) (ctx, {}))"

lemma fold_preserve: "(\<forall>x acc. acc \<le> f x acc) \<Longrightarrow> (a::'a::order) \<le> fold f l a"
proof (induction l arbitrary: a)
  case Nil
  have "fold f [] a = a" by simp
  have "a \<le> a" by auto
  then show ?case by auto
next
  case (Cons el l)
  hence unf: "f el a \<le> fold f (el # l) a" by simp
  from Cons have "a \<le> f el a" by simp
  from unf this Cons(2) show ?case using order.trans by blast
qed

lemma fold_preserve_option: "(\<forall>x acc accy. (f x (Some acc) = Some accy) \<longrightarrow> (acc \<le> accy)) \<Longrightarrow> (\<forall>x. f x None = None) \<Longrightarrow> fold f l (Some a) = Some ay \<Longrightarrow> (a::'a::order) \<le> ay" sorry

lemma collect_step_preserve: "collect_step prog inctx = outctx \<Longrightarrow> inctx \<le> outctx"
proof -
  assume "collect_step prog inctx = outctx"
  show "inctx \<le> outctx" sorry
qed


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
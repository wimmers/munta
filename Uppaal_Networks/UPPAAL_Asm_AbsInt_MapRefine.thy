theory UPPAAL_Asm_AbsInt_MapRefine
imports                   
  "HOL-Library.RBT_Mapping"
  UPPAAL_Asm_AbsInt_State_Dumb
begin

type_synonym 'a r_state_map = "(addr, 'a) mapping"

fun r_lookup :: "('a::bot) r_state_map \<Rightarrow> addr \<Rightarrow> 'a" where
  "r_lookup m = Mapping.lookup_default \<bottom> m"

definition RSM :: "('a::bot) r_state_map \<Rightarrow> 'a state_map" where
  "RSM m = SM (r_lookup m)"

declare RSM_def[simp]

code_datatype RSM

definition "r_empty_map \<equiv> Mapping.empty::('a::bot) r_state_map"

lemma[code]: "empty_map = RSM r_empty_map"
  by (rule lookup_eq; simp add: empty_map_def lookup_default_empty r_empty_map_def)

lemma[code]: "lookup (RSM m) = r_lookup m" by simp

fun merge_single :: "('a::sup) state_map \<Rightarrow> addr \<Rightarrow> 'a \<Rightarrow> 'a state_map" where
  "merge_single (SM m) pc x = SM (\<lambda>npc. if npc = pc then x \<squnion> m npc else m npc)"

fun r_merge_single :: "('a::{semilattice_sup, bot, linorder}) r_state_map \<Rightarrow> addr \<Rightarrow> 'a \<Rightarrow> 'a r_state_map" where
  "r_merge_single tree pc x = Mapping.update pc (x \<squnion> (r_lookup tree pc)) tree"

lemma merge_single_neq:
  assumes "pc \<noteq> k"
  shows "lookup (RSM (r_merge_single m pc x)) k = lookup (RSM m) k"
proof -
  have r: "lookup (RSM m) k = Mapping.lookup_default \<bottom> m k" by simp
  from assms have l:"lookup (RSM (r_merge_single m pc x)) k = Mapping.lookup_default \<bottom> m k" by (simp add: lookup_default_update_neq) 
  from r l show ?thesis by simp
qed

lemma merge_single_eq:
  assumes "pc = k"
  shows "lookup (RSM (r_merge_single m pc x)) k = x \<squnion> lookup (RSM m) k"
proof -
  have r: "x \<squnion> lookup (RSM m) k = x \<squnion> Mapping.lookup_default \<bottom> m k" by simp
  from assms have l:"lookup (RSM (r_merge_single m pc x)) k = x \<squnion> Mapping.lookup_default \<bottom> m k" by (simp add: lookup_default_update) 
  from r l show ?thesis by simp
qed

lemma[code]: "merge_single (RSM m) pc x = RSM (r_merge_single m pc x)"
proof(rule lookup_eq)
  obtain mm where func: "RSM m = SM mm" using state_map_single_constructor by blast
  have "(if k = pc then x \<squnion> mm k else mm k) = lookup (RSM (r_merge_single m pc x)) k" for k
  proof(cases "k = pc")
    case True from this func show ?thesis using merge_single_eq by (metis lookup.simps) next
    case False from this func show ?thesis using merge_single_neq by (metis lookup.simps)
  qed
  thus "lookup (merge_single (RSM m) pc x) k = lookup (RSM (r_merge_single m pc x)) k" for k using func by auto
qed

fun r_domain :: "('b::bot) r_state_map \<Rightarrow> addr set" where
  "r_domain tree = Set.filter (\<lambda>pc. r_lookup tree pc \<noteq> \<bottom>) (Mapping.keys tree)"

lemma[code]: "domain (RSM m) = r_domain m"
proof (intro Set.equalityI Set.subsetI)
  fix x assume "x \<in> domain (RSM m)"
  hence lookup: "lookup (RSM m) x \<noteq> \<bottom>" by simp
  from lookup have r_lookup: "r_lookup m x \<noteq> \<bottom>" by simp
  hence keys: "x \<in> Mapping.keys m"
    by (metis Option.is_none_def empty_iff keys_empty keys_is_none_rep lookup_default_def lookup_default_empty r_lookup.simps)
  from keys r_lookup show "x \<in> r_domain m" by auto
qed auto

fun r_step_map_from :: "('a::absstate) astep \<Rightarrow> instr \<Rightarrow> addr \<Rightarrow> 'a state_map \<Rightarrow> 'a state_map" where
  "r_step_map_from f op ipc ctx = fold
    (\<lambda>pc acc. merge_single acc pc (f op ipc (lookup ctx ipc) pc))
    (sorted_list_of_set (astep_succs f op ipc (lookup ctx ipc))) ctx"

fun r_step_map :: "('a::absstate) astep \<Rightarrow> program \<Rightarrow> 'a state_map \<Rightarrow> 'a state_map" where
  "r_step_map f prog ctx = fold
    (\<lambda>ipc acc. case prog ipc of
      Some op \<Rightarrow> r_step_map_from f op ipc acc |
      None \<Rightarrow> acc)
    (sorted_list_of_set (domain ctx)) empty_map"

fun r_advance :: "('a::{semilattice_sup, Sup}) astep \<Rightarrow> program \<Rightarrow> 'a r_state_map \<Rightarrow> 'a r_state_map" where
  "r_advance f prog ctx = undefined"


fun dumb_step :: "dumb astep" where
  "dumb_step _ _ None _ = None" |
  "dumb_step (JMPZ target) ipc ins pc = (if pc = Suc ipc \<or> pc = target then Some Any else None)" |
  "dumb_step CALL ipc ins pc = Some Any" |
  "dumb_step RETURN ipc ins pc = Some Any" |
  "dumb_step HALT ipc ins pc = None" |
  "dumb_step _ ipc ins pc = (if pc = Suc ipc then Some Any else None)"

(***********)
lemma[code_unfold]: "astep_succs dumb_step op pc st =
  (case (op, st) of
    (_, None)        \<Rightarrow> {} |
    (JMPZ target, _) \<Rightarrow> {target, pc + 1} |
    (CALL, _)        \<Rightarrow> UNIV |
    (RETURN, _)      \<Rightarrow> UNIV |
    (HALT, _)        \<Rightarrow> {} |
    _                \<Rightarrow> {pc + 1})"
proof (cases st)
  case None
  then show ?thesis sorry
next
  case (Some a)
  then show ?thesis sorry
qed

value "
  let m = empty_map::bool state_map;
      m2 = merge_single m 42 True;
      m3 = merge_single m2 123 False in
  domain m3"

end
theory UPPAAL_Asm_AbsInt_MapRefine
imports                   
  "HOL-Library.RBT_Mapping"
  UPPAAL_Asm_AbsInt
begin

type_synonym 'a r_state_map = "(addr, 'a) mapping"

fun r_lookup :: "('a::bot) r_state_map \<Rightarrow> addr \<Rightarrow> 'a" where
  "r_lookup m = Mapping.lookup_default \<bottom> m"

definition RSM :: "('a::bot) r_state_map \<Rightarrow> 'a state_map" where
  "RSM m = SM (r_lookup m)"

declare RSM_def[simp]

code_datatype RSM

lemma[code]: "empty_map = RSM (Mapping.empty::('a::bot) r_state_map)"
  by (rule lookup_eq; simp add: empty_map_def lookup_default_empty)

lemma[code]: "lookup (RSM m) = r_lookup m" by simp

fun merge_single :: "('a::sup) state_map \<Rightarrow> addr \<Rightarrow> 'a \<Rightarrow> 'a state_map" where
  "merge_single (SM m) pc x = SM (\<lambda>npc. if npc = pc then x \<squnion> m npc else m npc)"

fun r_merge_single :: "('a::{semilattice_sup, bot, linorder}) r_state_map \<Rightarrow> addr \<Rightarrow> 'a \<Rightarrow> 'a r_state_map" where
  "r_merge_single tree pc x = Mapping.update pc (x \<squnion> (r_lookup tree pc)) tree"

lemma merge_single_neq:
  assumes "pc \<noteq> k"
  shows "lookup (RSM (r_merge_single m pc x)) k = lookup (RSM m) k"
proof -
  have r: "lookup (RSM m) k = Mapping.lookup_default \<bottom> m k" by (simp add: RSM_def)
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

value "
  let m = empty_map::bool state_map;
      m2 = merge_single m 42 True;
      m3 = merge_single m2 123 False in
  domain m3"

end
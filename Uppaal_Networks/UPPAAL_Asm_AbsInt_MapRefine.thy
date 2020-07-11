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

code_datatype RSM

lemma[code]: "lookup (RSM m) = r_lookup m"
  by (simp add: RSM_def)

fun merge_single :: "('a::sup) state_map \<Rightarrow> addr \<Rightarrow> 'a \<Rightarrow> 'a state_map" where
  "merge_single (SM m) pc x = SM (\<lambda>npc. if npc = pc then x \<squnion> m npc else m npc)"

fun r_merge_single :: "('a::{semilattice_sup, bot, linorder}) r_state_map \<Rightarrow> addr \<Rightarrow> 'a \<Rightarrow> 'a r_state_map" where
  "r_merge_single tree pc x = Mapping.update pc (x \<squnion> (r_lookup tree pc)) tree"

lemma "pc \<noteq> ppc \<Longrightarrow> lookup (RSM (r_merge_single m pc x)) k = lookup (RSM m) k" sorry

lemma[code]: "merge_single (RSM m) pc x = RSM (r_merge_single m pc x)"
proof(rule lookup_eq)
  obtain mm where func: "RSM m = SM mm" using state_map_single_constructor by blast
  have "(if k = pc then x \<squnion> mm k else mm k) = lookup (RSM (r_merge_single m pc x)) k" for k
  proof(cases "k = pc")
    case True
    then show ?thesis sorry
  next
    case False
    then show ?thesis sorry
  qed
  thus "lookup (merge_single (RSM m) pc x) k = lookup (RSM (r_merge_single m pc x)) k" for k by (simp add: func)
qed

end
theory UPPAAL_Asm_AbsInt_MapRefine
imports                   
  "HOL-Library.RBT_Mapping"
  UPPAAL_Asm_AbsInt_State_Dumb
begin

instantiation mapping :: (type,bot) bot
begin
definition "bot_mapping \<equiv> Mapping.empty"
instance ..
end

type_synonym 'a r_state_map = "(addr, 'a) mapping"

fun r_lookup :: "('a::bot) r_state_map \<Rightarrow> addr \<Rightarrow> 'a" where
  "r_lookup m = Mapping.lookup_default \<bottom> m"

definition RSM :: "('a::bot) r_state_map \<Rightarrow> 'a state_map" where
  "RSM m = SM (r_lookup m)"

declare RSM_def[simp]

code_datatype RSM

definition "r_empty_map \<equiv> Mapping.empty::('a::bot) r_state_map"

lemma[code]: "\<bottom> = RSM r_empty_map"
  by (rule lookup_eq; simp add: lookup_default_empty r_empty_map_def)

lemma[code]: "lookup (RSM m) = r_lookup m" by simp

fun merge_single :: "('a::sup) state_map \<Rightarrow> addr \<Rightarrow> 'a \<Rightarrow> 'a state_map" where
  "merge_single (SM m) pc x = SM (\<lambda>npc. if npc = pc then x \<squnion> m npc else m npc)"

fun r_merge_single :: "('a::{semilattice_sup, bot}) r_state_map \<Rightarrow> addr \<Rightarrow> 'a \<Rightarrow> 'a r_state_map" where
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

lemma[code]: "astep_succs f op ipc st = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}" (* TODO: this is completely wrong ofc *) sorry

(* TODO: maybe first refine the algorithm, then the type,
  but then the proof over the list won't work
  can we still prove it? *)
fun r_step_map_from_with_op :: "('a::absstate) astep \<Rightarrow> instr \<Rightarrow> addr \<Rightarrow> 'a r_state_map \<Rightarrow> 'a r_state_map \<Rightarrow> 'a r_state_map" where
  "r_step_map_from_with_op f op ipc ctx acc = fold
    (\<lambda>pc acc. r_merge_single acc pc (f op ipc (r_lookup ctx ipc) pc))
    (sorted_list_of_set (astep_succs f op ipc (r_lookup ctx ipc))) acc"

fun r_step_map_from :: "('a::absstate) astep \<Rightarrow> program \<Rightarrow> 'a r_state_map \<Rightarrow> addr \<Rightarrow> 'a r_state_map \<Rightarrow> 'a r_state_map" where
  "r_step_map_from f prog ctx ipc acc =
    (case prog ipc of
      Some op \<Rightarrow> r_step_map_from_with_op f op ipc ctx acc |
      None \<Rightarrow> acc)"

fun r_step_map :: "('a::absstate) astep \<Rightarrow> program \<Rightarrow> 'a r_state_map \<Rightarrow> 'a r_state_map" where
  "r_step_map f prog ctx = fold (r_step_map_from f prog ctx) (sorted_list_of_set (r_domain ctx)) \<bottom>"

lemma sorted_list_of_set_split:
  assumes "a \<in> s"
  shows "\<exists>pre post. pre @ a # post = sorted_list_of_set s"
  using assms(1) set_sorted_list_of_set split_list_first sorry

lemma[code]: "step_map (f::('a::absstate) astep) prog (RSM ctx) = RSM (r_step_map f prog ctx)"
proof(rule lookup_eq)
  have "\<Squnion>{ost. \<exists>ipc op. prog ipc = Some op \<and> r_lookup ctx ipc \<noteq> \<bottom> \<and> f op ipc (r_lookup ctx ipc) pc = ost} = r_lookup (r_step_map f prog ctx) pc" for pc
  proof(rule Sup_eqI, goal_cases)
    case (1 ost)
    then obtain ipc op where step: "prog ipc = Some op" "r_lookup ctx ipc \<noteq> \<bottom>" "f op ipc (r_lookup ctx ipc) pc = ost" by blast
    obtain m where "SM m = RSM ctx" using state_map_single_constructor by metis 
    from this step have "ipc \<in> domain (RSM ctx)" by auto                
    then obtain pre post where "pre @ ipc # post = sorted_list_of_set (domain (RSM ctx))" sorry
    then show ?case sorry
  next
    case (2 y)
    then show ?case sorry
  qed
  thus "lookup (step_map f prog (RSM ctx)) pc = lookup (RSM (r_step_map f prog ctx)) pc" for pc by simp
qed

fun r_advance :: "('a::{semilattice_sup, Sup}) astep \<Rightarrow> program \<Rightarrow> 'a r_state_map \<Rightarrow> 'a r_state_map" where
  "r_advance f prog ctx = undefined"

(***********)

value "
  let m = \<bottom>::bool state_map;
      m2 = merge_single m 42 True;
      m3 = merge_single m2 123 False in
  domain m3"

fun showit :: "bool state_map \<Rightarrow> string" where
  "showit m = (if m = \<top> then ''TOP!'' else ''something else'')"

(*definition BSM :: "bool state_map \<Rightarrow> 'a state_map" where
  "BSM m = SM (r_lookup m)"

declare RSM_def[simp]

code_datatype RSM

value "showit \<top>"*)

end
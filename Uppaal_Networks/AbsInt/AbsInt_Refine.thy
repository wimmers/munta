theory AbsInt_Refine
imports                   
  "HOL-Library.RBT_Mapping"
  State_Dumb
begin

instantiation mapping :: (type,bot) bot
begin
definition "bot_mapping \<equiv> Mapping.empty"
instance ..
end

type_synonym 'a r_state_map = "(addr, 'a) mapping"

fun r_lookup :: "('a::bot) r_state_map \<Rightarrow> addr \<Rightarrow> 'a" where
  "r_lookup m = Mapping.lookup_default \<bottom> m"

instantiation mapping :: (type, "{preorder, bot}") preorder
begin
  definition less_eq_mapping :: "('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping \<Rightarrow> bool" where
  "C1 \<le> C2 \<longleftrightarrow> (\<forall>p. Mapping.lookup_default \<bottom> C1 p \<le> Mapping.lookup_default \<bottom> C2 p)"
  
  definition less_mapping :: "('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping \<Rightarrow> bool" where
  "less_mapping x y = (x \<le> y \<and> \<not> y \<le> x)"
  
  instance proof (standard, goal_cases)
    case 1 show ?case by(simp add: less_mapping_def)
  next
    case 2 thus ?case by(auto simp: less_eq_mapping_def)
  next
    case 3 thus ?case using less_eq_mapping_def order_trans by fastforce
  qed
end

definition RSM :: "('a::bot) r_state_map \<Rightarrow> 'a state_map" where
  "RSM m = SM (r_lookup m)"

declare RSM_def[simp]

lemma RSM_mono: "a \<le> b \<Longrightarrow> RSM a \<le> RSM b"
proof -
  assume "a \<le> b"
  hence "lookup (RSM a) pc \<le> lookup (RSM b) pc" for pc by (simp add: less_eq_mapping_def)
  thus ?thesis using less_eq_state_map_def by blast
qed

code_datatype RSM

definition "r_empty_map \<equiv> Mapping.empty::('a::bot) r_state_map"

lemma[code]: "\<bottom> = RSM r_empty_map"
  by (rule lookup_eq; simp add: lookup_default_empty r_empty_map_def)

lemma[code]: "lookup (RSM m) = r_lookup m" by simp

fun merge_single :: "('a::semilattice_sup) state_map \<Rightarrow> addr \<Rightarrow> 'a \<Rightarrow> 'a state_map" where
  "merge_single (SM m) pc x = SM (\<lambda>npc. if npc = pc then x \<squnion> m npc else m npc)"

lemma merge_single_grows: "m \<le> merge_single m pc x"
proof -
  obtain mm where sm: "m = SM mm" using state_map_single_constructor by blast
  have "lookup (SM mm) p \<le> lookup (merge_single (SM mm) pc x) p" for p by simp
  from this sm show ?thesis using less_eq_state_map_def by blast
qed

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

lemma r_merge_single[code]: "merge_single (RSM m) pc x = RSM (r_merge_single m pc x)"
proof(rule lookup_eq)
  obtain mm where func: "RSM m = SM mm" using state_map_single_constructor by blast
  have "(if k = pc then x \<squnion> mm k else mm k) = lookup (RSM (r_merge_single m pc x)) k" for k
  proof(cases "k = pc")
    case True from this func show ?thesis using merge_single_eq by (metis lookup.simps) next
    case False from this func show ?thesis using merge_single_neq by (metis lookup.simps)
  qed
  thus "lookup (merge_single (RSM m) pc x) k = lookup (RSM (r_merge_single m pc x)) k" for k using func by auto
qed

lemma r_merge_single_grows: "m \<le> r_merge_single m pc x"
  by (simp add: less_eq_mapping_def lookup_default_update')

fun r_domain :: "('b::bot) r_state_map \<Rightarrow> addr set" where
  "r_domain tree = Set.filter (\<lambda>pc. r_lookup tree pc \<noteq> \<bottom>) (Mapping.keys tree)"

lemma r_domain[code]: "domain (RSM m) = r_domain m"
proof (intro Set.equalityI Set.subsetI)
  fix x assume "x \<in> domain (RSM m)"
  hence lookup: "lookup (RSM m) x \<noteq> \<bottom>" by simp
  from lookup have r_lookup: "r_lookup m x \<noteq> \<bottom>" by simp
  from r_lookup have keys: "x \<in> Mapping.keys m"
    by (metis Option.is_none_def empty_iff keys_empty keys_is_none_rep lookup_default_def lookup_default_empty r_lookup.simps)
  from keys r_lookup show "x \<in> r_domain m" by auto
qed auto

lemma r_domain_finite: "finite (r_domain (Mapping m))" by (simp add: keys_Mapping)
lemma domain_finite: "finite (domain (RSM (Mapping m)))" using r_domain r_domain_finite by metis

lemma[code]: "astep_succs f op ipc st = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}" (* TODO: this is completely wrong ofc *) sorry

lemma fold_grow:
  assumes "\<And>e acc. (acc::'a::preorder) \<le> f e acc"
  shows "a \<le> fold f l a"
proof(induction l arbitrary: a)
  case (Cons x xs)
  then show ?case using Cons.IH assms order_trans by fastforce
qed simp

fun r_step_map_from_with_op :: "('a::absstate) astep \<Rightarrow> instr \<Rightarrow> addr \<Rightarrow> 'a r_state_map \<Rightarrow> 'a r_state_map \<Rightarrow> 'a r_state_map" where
  "r_step_map_from_with_op f op ipc ctx acc = fold
    (\<lambda>pc acc. r_merge_single acc pc (f op ipc (r_lookup ctx ipc) pc))
    (sorted_list_of_set (astep_succs f op ipc (r_lookup ctx ipc))) acc"

lemma r_step_map_from_with_op_grows: "acc \<le> r_step_map_from_with_op f op ipc ctx acc" using r_merge_single_grows fold_grow
  by (metis (no_types, lifting) r_step_map_from_with_op.simps)

fun r_step_map_from :: "('a::absstate) astep \<Rightarrow> program \<Rightarrow> 'a r_state_map \<Rightarrow> addr \<Rightarrow> 'a r_state_map \<Rightarrow> 'a r_state_map" where
  "r_step_map_from f prog ctx ipc acc =
    (case prog ipc of
      Some op \<Rightarrow> r_step_map_from_with_op f op ipc ctx acc |
      None \<Rightarrow> acc)"

lemma r_step_map_from_grows: "acc \<le> r_step_map_from f prog ctx ipc acc"
  using r_step_map_from_with_op_grows by (cases "prog ipc"; simp)

fun r_step_map :: "('a::absstate) astep \<Rightarrow> program \<Rightarrow> 'a r_state_map \<Rightarrow> 'a r_state_map" where
  "r_step_map f prog ctx = fold (r_step_map_from f prog ctx) (sorted_list_of_set (r_domain ctx)) \<bottom>"

lemma sorted_list_of_set_split:
  assumes "a \<in> s" "finite s"
  shows "\<exists>pre post. pre @ a # post = sorted_list_of_set s"
  using assms set_sorted_list_of_set split_list_first by fastforce

lemma fold_split:
  "fold f (pre @ x # post) = fold f post \<circ> f x \<circ> fold f pre"
  by simp

lemma[code]: "step_map (f::('a::absstate) astep) prog (RSM (Mapping tree)) = RSM (r_step_map f prog (Mapping tree))"
proof(rule lookup_eq)
  let ?ctx = "Mapping tree"
  let ?smf = "r_step_map_from f prog ?ctx"
  have "\<Squnion>{ost. \<exists>ipc op. prog ipc = Some op \<and> r_lookup ?ctx ipc \<noteq> \<bottom> \<and> f op ipc (r_lookup ?ctx ipc) pc = ost} = r_lookup (r_step_map f prog ?ctx) pc" for pc
  proof(rule Sup_eqI, goal_cases)
    case (1 ost)
    then obtain ipc op where step: "prog ipc = Some op" "r_lookup ?ctx ipc \<noteq> \<bottom>" "f op ipc (r_lookup ?ctx ipc) pc = ost" by blast
    obtain m where "SM m = RSM ?ctx" using state_map_single_constructor by metis
    from this step have "ipc \<in> domain (RSM ?ctx)" by auto
    then obtain pre post where "pre @ ipc # post = sorted_list_of_set (domain (RSM ?ctx))" using sorted_list_of_set_split domain_finite by metis
    hence "r_step_map f prog ?ctx = (fold ?smf post \<circ> ?smf ipc \<circ> fold ?smf pre) \<bottom>" using fold_split by (metis r_domain r_step_map.simps)
    hence split: "r_step_map f prog ?ctx = fold ?smf post (?smf ipc (fold ?smf pre \<bottom>))" by simp
    hence post:"?smf ipc (fold ?smf pre \<bottom>) \<le> r_step_map f prog ?ctx" by (metis fold_grow r_step_map_from_grows)
    let ?prefold = "fold ?smf pre \<bottom>"
    have "ost \<le> r_lookup (?smf ipc ?prefold) pc"
    proof -
      have rip: "?smf ipc ?prefold = r_step_map_from_with_op f op ipc ?ctx ?prefold" using step by simp
      have "ost \<le> r_lookup (r_step_map_from_with_op f op ipc ?ctx ?prefold) pc" sorry
      thus ?thesis using step rip by simp
    qed
    from post this show ?case using less_eq_mapping_def order_trans by fastforce
  next
    case (2 y)
    then show ?case sorry
  qed
  thus "lookup (step_map f prog (RSM ?ctx)) pc = lookup (RSM (r_step_map f prog ?ctx)) pc" for pc by simp
qed

fun r_advance :: "('a::absstate) astep \<Rightarrow> program \<Rightarrow> 'a r_state_map \<Rightarrow> 'a r_state_map" where
  "r_advance f prog ctx = fold (r_step_map_from f prog ctx) (sorted_list_of_set (r_domain ctx)) ctx"

lemma[code]: "advance (f::('a::absstate) astep) prog (RSM ctx) = RSM (r_advance f prog ctx)" sorry

(***********)

value "
  let m = \<bottom>::bool state_map;
      m2 = merge_single m 42 True;
      m3 = merge_single m2 123 False in
  domain m3"

fun showit :: "bool state_map \<Rightarrow> string" where
  "showit m = (if m = \<top> then ''TOP!'' else ''something else'')"

end
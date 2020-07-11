theory UPPAAL_Asm_AbsInt_Refine
imports                   
  "HOL-Data_Structures.RBT_Map"
  UPPAAL_Asm_AbsInt
begin

lemma "states_at states pc = snd ` {s\<in>states. fst s = pc}"
proof standard
  show "states_at states pc \<subseteq> snd ` {s \<in> states. fst s = pc}" using image_iff states_at.simps by fastforce
  show "snd ` {s \<in> states. fst s = pc} \<subseteq> states_at states pc" by standard (auto simp: states_at.intros)
qed

type_synonym 'a rbt_state_map = "(addr * 'a) rbt"

fun def :: "'a \<Rightarrow> 'a option \<Rightarrow> 'a" where
  "def _ (Some v) = v" |
  "def d _ = d"

fun rbt_lookup :: "('a::bot) rbt_state_map \<Rightarrow> addr \<Rightarrow> 'a" where
  "rbt_lookup tree pc = def \<bottom> (Lookup2.lookup tree pc)"

definition RBT_SM :: "(addr * 'a) rbt \<Rightarrow> ('a::bot) state_map" where
  "RBT_SM tree = SM (rbt_lookup tree)"


(*code_datatype RBT_SM*)

lemma assumes "rbt t" "sorted1(inorder t)" shows "Lookup2.lookup (update k v t) k = Some v"
proof -
  from assms have "Lookup2.lookup (update k v t) = Lookup2.lookup t(k \<mapsto> v)" by (simp add: M.map_update M.invar_def)
  thus ?thesis by simp
qed

fun merge_single :: "('a::sup) state_map \<Rightarrow> addr \<Rightarrow> 'a \<Rightarrow> 'a state_map" where
  "merge_single (SM m) pc x = SM (\<lambda>npc. if npc = pc then x \<squnion> m npc else m npc)"

fun rbt_merge_single :: "('a::{semilattice_sup, bot, linorder}) rbt_state_map \<Rightarrow> addr \<Rightarrow> 'a \<Rightarrow> 'a rbt_state_map" where
  "rbt_merge_single tree pc x = update pc (x \<squnion> (rbt_lookup tree pc)) tree"

lemma[code]: "merge_single (RBT_SM tree) pc x = RBT_SM (rbt_merge_single tree pc x)"
proof(rule lookup_eq)
  obtain m where func: "RBT_SM tree = SM m" using state_map_single_constructor by blast
  have "(if k = pc then x \<squnion> m k else m k) = lookup (RBT_SM (rbt_merge_single tree pc x)) k" for k sorry
  then show "lookup (merge_single (RBT_SM tree) pc x) k = lookup (RBT_SM (rbt_merge_single tree pc x)) k" for k by (simp add: func)
qed

lemma deepen_RBT_SM[code]:
  "deepen (set states) = propagate (RBT_SM empty) (set states)" sorry

lemma lookup_RBT_SM[code]:
  "lookup (RBT_SM tree) pc = def \<bottom> (Lookup2.lookup tree pc)" sorry

lemma domain_RBT_SM[code]:
  "domain (RBT_SM tree) = fst ` set (inorder tree)" sorry

(*lemma "propagate (SM oldmap) ss =
  (SM (\<lambda>pc. oldmap pc \<union> (states_at ss pc)))"
proof -
  have fwd: "propagate (SM oldmap) ss \<le> (SM (\<lambda>pc. oldmap pc \<union> (states_at ss pc)))" sorry
  have bwd: "(SM (\<lambda>pc. oldmap pc \<union> (states_at ss pc))) \<le> propagate (SM oldmap) ss" sorry
  from fwd bwd have "propagate (SM oldmap) ss = (SM (\<lambda>pc. oldmap pc \<union> (states_at ss pc)))" using antisym by blast
qed*)

lemma propagate_RBT_SM[code]:
  "propagate (RBT_SM oldtree) (set ss) =
    RBT_SM (fold (\<lambda>(pc, st) tree.
      let newsts = (
        case Lookup2.lookup tree pc of
          Some sts \<Rightarrow> sts \<union> {st} |
          None \<Rightarrow> {st})
      in upd pc newsts tree
    ) ss oldtree)" sorry

find_consts "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"

lemma[code]: "step_all op pc (set instates) =
  (Option.these (set (map (\<lambda>ins. step op (pc, ins)) instates)),
  if list_ex (\<lambda>ins. step op (pc, ins) = None) instates then {StepFailed pc} else {})" sorry

end
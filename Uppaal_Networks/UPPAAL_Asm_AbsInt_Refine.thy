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

datatype 'a rbt_state_map = RBT_SM "(addr * 'a) rbt"

fun def :: "'a \<Rightarrow> 'a option \<Rightarrow> 'a" where
  "def _ (Some v) = v" |
  "def d _ = d"

definition RBT_SM :: "(addr * 'a) rbt \<Rightarrow> ('a::bot) state_map" where
  "RBT_SM tree = SM (\<lambda>pc. def \<bottom> (Lookup2.lookup tree pc))"

code_datatype RBT_SM

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
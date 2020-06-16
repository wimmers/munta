theory UPPAAL_Asm_AbsInt_Refine
imports                   
  "HOL-Data_Structures.RBT_Map"
  UPPAAL_Asm_AbsInt
begin

datatype 'a rbt_state_map = RBT_SM "(addr * 'a) rbt"

definition RBT_SM :: "(addr * 'a) rbt \<Rightarrow> 'a state_map" where
  "RBT_SM tree = SM (Lookup2.lookup tree)"

code_datatype RBT_SM

lemma entry_RBT_SM[code]:
  "entry (set states) = propagate (RBT_SM empty) (set states)" sorry

lemma lookup_RBT_SM[code]:
  "lookup (RBT_SM tree) = Lookup2.lookup tree" sorry

lemma domain_RBT_SM[code]:
  "domain (RBT_SM tree) = fst ` set (inorder tree)" sorry

lemma propagate_RBT_SM[code]:
  "propagate (RBT_SM oldtree) (set ss) =
    RBT_SM (fold (\<lambda>(pc, st) tree.
      let newsts = (
        case Lookup2.lookup tree pc of
          Some sts \<Rightarrow> sts \<union> {st} |
          None \<Rightarrow> {st})
      in upd pc newsts tree
    ) ss oldtree)" sorry

lemma[code]: "step_all op pc (set instates) =
  Option.these (set (map (\<lambda>ins. step op (pc, ins)) instates))" using in_these_eq by fastforce

end
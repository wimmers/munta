theory Worklist_Locales
  imports "$AFP/Refine_Imperative_HOL/Sepref" "$AFP/Collections/Lib/HashCode" "../library/Graphs"
begin

subsection \<open>Search Spaces\<close>
text \<open>
  A search space consists of a step relation, a start state,
  a final state predicate, and a subsumption preorder.
\<close>
locale Search_Space_Defs =
  fixes E :: "'a \<Rightarrow> 'a \<Rightarrow> bool" -- \<open>Step relation\<close>
    and a\<^sub>0 :: 'a                -- \<open>Start state\<close>
    and F :: "'a \<Rightarrow> bool"      -- \<open>Final states\<close>
    and subsumes :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<preceq>" 50) -- \<open>Subsumption preorder\<close>
begin

  sublocale Graph_Start_Defs E a\<^sub>0 .

  definition subsumes_strictly (infix "\<prec>" 50) where
    "subsumes_strictly x y = (x \<preceq> y \<and> \<not> y \<preceq> x)"

  no_notation fun_rel_syn (infixr "\<rightarrow>" 60)

  definition "F_reachable \<equiv> \<exists>a. reachable a \<and> F a"

end


locale Search_Space_Defs_Empty = Search_Space_Defs +
  fixes empty :: "'a \<Rightarrow> bool"

text \<open>The set of reachable states must be finite,
  subsumption must be a preorder, and be compatible with steps and final states.\<close>
locale Search_Space = Search_Space_Defs_Empty +
  assumes refl[intro!, simp]: "a \<preceq> a"
      and trans[trans]: "a \<preceq> b \<Longrightarrow> b \<preceq> c \<Longrightarrow> a \<preceq> c"

  assumes mono:
      "a \<preceq> b \<Longrightarrow> E a a' \<Longrightarrow> reachable a \<Longrightarrow> reachable b \<Longrightarrow> \<not> empty a \<Longrightarrow> \<exists> b'. E b b' \<and> a' \<preceq> b'"
      and empty_subsumes: "empty a \<Longrightarrow> a \<preceq> a'"
      and empty_mono: "\<not> empty a \<Longrightarrow> a \<preceq> b \<Longrightarrow> \<not> empty b"
      and empty_E: "reachable x \<Longrightarrow> empty x \<Longrightarrow> E x x' \<Longrightarrow> empty x'"
      and F_mono: "a \<preceq> a' \<Longrightarrow> F a \<Longrightarrow> F a'"
begin

  sublocale preorder "op \<preceq>" "op \<prec>"
    by standard (auto simp: subsumes_strictly_def intro: trans)

end (* Search Space *)

locale Search_Space_finite = Search_Space +
  assumes finite_reachable: "finite {a. reachable a \<and> \<not> empty a}"

locale Search_Space_finite_strict = Search_Space +
  assumes finite_reachable: "finite {a. reachable a}"

sublocale Search_Space_finite_strict \<subseteq> Search_Space_finite
  by standard (auto simp: finite_reachable)

locale Search_Space' = Search_Space +
  assumes final_non_empty: "F a \<Longrightarrow> \<not> empty a"

locale Search_Space'_finite = Search_Space' + Search_Space_finite

locale Search_Space''_Defs = Search_Space_Defs_Empty +
  fixes subsumes' :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<unlhd>" 50) -- \<open>Subsumption preorder\<close>

locale Search_Space''_pre = Search_Space''_Defs +
  assumes empty_subsumes': "\<not> empty a \<Longrightarrow> a \<preceq> b \<longleftrightarrow> a \<unlhd> b"

locale Search_Space''_start = Search_Space''_pre +
  assumes start_non_empty [simp]: "\<not> empty a\<^sub>0"

locale Search_Space'' = Search_Space''_pre + Search_Space'

locale Search_Space''_finite = Search_Space'' + Search_Space_finite

sublocale Search_Space''_finite \<subseteq> Search_Space'_finite ..

locale Search_Space''_finite_strict = Search_Space'' + Search_Space_finite_strict

locale Search_Space_Key_Defs =
  Search_Space''_Defs E for E :: "'v \<Rightarrow> 'v \<Rightarrow> bool" +
  fixes key :: "'v \<Rightarrow> 'k"

locale Search_Space_Key =
  Search_Space_Key_Defs + Search_Space'' +
  assumes subsumes_key[intro, simp]: "a \<unlhd> b \<Longrightarrow> key a = key b"

locale Worklist0_Defs = Search_Space_Defs +
  fixes succs :: "'a \<Rightarrow> 'a list"

locale Worklist0 = Worklist0_Defs + Search_Space +
  assumes succs_correct: "reachable a \<Longrightarrow> set (succs a) = Collect (E a)"

locale Worklist1_Defs = Worklist0_Defs + Search_Space_Defs_Empty

locale Worklist1 = Worklist1_Defs + Worklist0

locale Worklist2_Defs = Worklist1_Defs + Search_Space''_Defs

locale Worklist2 = Worklist2_Defs + Worklist1 + Search_Space''_pre + Search_Space

locale Worklist3_Defs = Worklist2_Defs +
  fixes F' :: "'a \<Rightarrow> bool"

locale Worklist3 = Worklist3_Defs + Worklist2 +
  assumes F_split: "F a \<longleftrightarrow> \<not> empty a \<and> F' a"

locale Worklist4 = Worklist3 + Search_Space''

locale Worklist_Map_Defs = Search_Space_Key_Defs + Worklist2_Defs

locale Worklist_Map =
  Worklist_Map_Defs + Search_Space_Key + Worklist2

locale Worklist_Map2_Defs = Worklist_Map_Defs + Worklist3_Defs

locale Worklist_Map2 = Worklist_Map2_Defs + Worklist_Map + Worklist3

locale Worklist_Map2_finite = Worklist_Map2 + Search_Space_finite

sublocale Worklist_Map2_finite \<subseteq> Search_Space''_finite ..

locale Worklist4_Impl_Defs = Worklist3_Defs +
  fixes A :: "'a \<Rightarrow> 'ai \<Rightarrow> assn"
  fixes succsi :: "'ai \<Rightarrow> 'ai list Heap"
  fixes a\<^sub>0i :: "'ai Heap"
  fixes Fi :: "'ai \<Rightarrow> bool Heap"
  fixes Lei :: "'ai \<Rightarrow> 'ai \<Rightarrow> bool Heap"
  fixes emptyi :: "'ai \<Rightarrow> bool Heap"

locale Worklist4_Impl = Worklist4_Impl_Defs + Worklist4 +
  (* TODO: This is the easy variant: Operations cannot depend on additional heap. *)
  assumes [sepref_fr_rules]: "(uncurry0 a\<^sub>0i, uncurry0 (RETURN (PR_CONST a\<^sub>0))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a A"
  assumes [sepref_fr_rules]: "(Fi,RETURN o PR_CONST F') \<in> A\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  assumes [sepref_fr_rules]: "(uncurry Lei,uncurry (RETURN oo PR_CONST op \<unlhd>)) \<in> A\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  assumes [sepref_fr_rules]: "(succsi,RETURN o PR_CONST succs) \<in> A\<^sup>k \<rightarrow>\<^sub>a list_assn A"
  assumes [sepref_fr_rules]: "(emptyi,RETURN o PR_CONST empty) \<in> A\<^sup>k \<rightarrow>\<^sub>a bool_assn"

locale Worklist4_Impl_finite_strict = Worklist4_Impl + Search_Space_finite_strict

sublocale Worklist4_Impl_finite_strict \<subseteq> Search_Space''_finite_strict ..

locale Worklist_Map2_Impl_Defs =
  Worklist4_Impl_Defs _ _ _ _ _ _ _ _ A + Worklist_Map2_Defs a\<^sub>0 _ _ _ _ _ key
  for A :: "'a \<Rightarrow> 'ai :: {heap} \<Rightarrow> _" and key :: "'a \<Rightarrow> 'ki :: {hashable, heap}" +
  fixes keyi :: "'ai \<Rightarrow> 'ki Heap"
  fixes copyi :: "'ai \<Rightarrow> 'ai Heap"

end (* Theory *)
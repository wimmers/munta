theory Normalized_Zone_Semantics_Impl_Refine
  imports
    Normalized_Zone_Semantics_Impl DBM.DBM_Operations_Impl_Refine
    "HOL-Library.IArray"
    HOL.Code_Numeral
    Worklist_Algorithms.Worklist_Subsumption_Impl1 Worklist_Algorithms.Unified_PW_Impl
    Worklist_Algorithms.Liveness_Subsumption_Impl Worklist_Algorithms.Leadsto_Impl
    Normalized_Zone_Semantics_Impl_Semantic_Refinement
    TA_Library.Printing Show.Show_Instances
    TA_Library.Abstract_Term
begin

  unbundle no_library_syntax

  notation fun_rel_syn (infixr "\<rightarrow>" 60)

  chapter \<open>Imperative Implementation of Reachability Checking\<close>

  section \<open>Misc\<close>

    (* XXX Move *)
  lemma (in -) rtranclp_equiv:
    "R\<^sup>*\<^sup>* x y \<longleftrightarrow> S\<^sup>*\<^sup>* x y" if "\<And> x y. P x \<Longrightarrow> R x y \<longleftrightarrow> S x y" "\<And> x y. P x \<Longrightarrow> R x y \<Longrightarrow> P y" "P x"
  proof
    assume A: "R\<^sup>*\<^sup>* x y"
    note that(1)[iff] that(2)[intro]
    from A \<open>P x\<close> have "P y \<and> S\<^sup>*\<^sup>* x y"
      by induction auto
    then show "S\<^sup>*\<^sup>* x y" ..
  next
    assume A: "S\<^sup>*\<^sup>* x y"
    note that(1)[iff] that(2)[intro] rtranclp.intros(2)[intro]
    from A \<open>P x\<close> have "P y \<and> R\<^sup>*\<^sup>* x y"
      by (induction; blast)
    then show "R\<^sup>*\<^sup>* x y" ..
  qed

  (* XXX Move *)
  lemma (in -) tranclp_equiv:
    "R\<^sup>+\<^sup>+ x y \<longleftrightarrow> S\<^sup>+\<^sup>+ x y" if "\<And> x y. P x \<Longrightarrow> R x y \<longleftrightarrow> S x y" "\<And> x y. P x \<Longrightarrow> R x y \<Longrightarrow> P y" "P x"
  proof
    assume A: "R\<^sup>+\<^sup>+ x y"
    note that(1)[iff] that(2)[intro]
    from A \<open>P x\<close> have "P y \<and> S\<^sup>+\<^sup>+ x y"
      by induction auto
    then show "S\<^sup>+\<^sup>+ x y" ..
  next
    assume A: "S\<^sup>+\<^sup>+ x y"
    note that(1)[iff] that(2)[intro] tranclp.intros(2)[intro]
    from A \<open>P x\<close> have "P y \<and> R\<^sup>+\<^sup>+ x y"
      by (induction; blast)
    then show "R\<^sup>+\<^sup>+ x y" ..
  qed

  lemma (in -) rtranclp_tranclp_equiv:
    "R\<^sup>*\<^sup>* x y \<and> R\<^sup>+\<^sup>+ y z \<longleftrightarrow> S\<^sup>*\<^sup>* x y \<and> S\<^sup>+\<^sup>+ y z" if
    "\<And> x y. P x \<Longrightarrow> R x y \<longleftrightarrow> S x y" "\<And> x y. P x \<Longrightarrow> R x y \<Longrightarrow> P y" "P x"
  proof
    assume A: "R\<^sup>*\<^sup>* x y \<and> R\<^sup>+\<^sup>+ y z"
    note that(1)[iff] that(2)[intro]
    from A[THEN conjunct1] \<open>P x\<close> have "P y"
      by induction auto
    then show "S\<^sup>*\<^sup>* x y \<and> S\<^sup>+\<^sup>+ y z"
      using rtranclp_equiv[of P R S x y, OF that] tranclp_equiv[of P R S y z, OF that(1,2)] A
      by fastforce
  next
    assume A: "S\<^sup>*\<^sup>* x y \<and> S\<^sup>+\<^sup>+ y z"
    note that(1)[iff] that(2)[intro]
    from A[THEN conjunct1] \<open>P x\<close> have "P y"
      by induction auto
    then show "R\<^sup>*\<^sup>* x y \<and> R\<^sup>+\<^sup>+ y z"
      using rtranclp_equiv[of P R S x y, OF that] tranclp_equiv[of P R S y z, OF that(1,2)] A
      by force
  qed


  section \<open>Mapping Transitions and Invariants\<close>

  type_synonym
    ('a, 'c, 'time, 's) transition_fun = "'s \<Rightarrow> (('c, 'time) cconstraint * 'a * 'c list * 's) list"

  (* XXX Can this be constructed from other primitives? *)
  definition transition_rel where
    "transition_rel X = {(f, r). \<forall> l \<in> X. \<forall> x. (l, x) \<in> r \<longleftrightarrow> x \<in> set (f l)}"

  (* XXX Rename *)
  definition inv_rel where \<comment> \<open>Invariant assignments for a restricted state set\<close>
    (* XXX Or use "inv_rel X = Id_on X \<rightarrow> Id" ? *)
    "inv_rel R X = b_rel R (\<lambda> x. x \<in> X) \<rightarrow> Id"

  lemma transition_rel_anti_mono:
  "transition_rel S \<subseteq> transition_rel R" if "R \<subseteq> S"
  using that unfolding transition_rel_def by auto

  lemma inv_rel_anti_mono:
    "inv_rel A S \<subseteq> inv_rel A R" if "R \<subseteq> S"
    using that unfolding inv_rel_def fun_rel_def b_rel_def by auto

  (* XXX Map from automaton? *)
  definition state_set :: "('a, 'c, 'time, 's) transition set \<Rightarrow> 's set" where
    "state_set T = fst ` T \<union> (snd o snd o snd o snd) ` T"

definition
  "trace_level (i :: int) (f :: unit \<Rightarrow> String.literal Heap) = ()"

locale Show_State_Defs =
  fixes n :: nat and show_state :: "'si \<Rightarrow> string" and show_clock :: "nat \<Rightarrow> string"
begin

definition
  "tracei type \<equiv> \<lambda> (l, M).
   let _ = trace_level 5 (
    \<lambda>_. do {
      let st = show_state l;
      m \<leftarrow> show_dbm_impl n show_clock show M;
      let s = type @ '': (''  @ st @ '', <'' @ m @ ''>)''; 
      let s = String.implode s;
      return s
    })
  in return ()
"

end

locale TA_Impl_No_Ceiling_Defs =
  Show_State_Defs n show_state +
  TA_Start_No_Ceiling_Defs A l\<^sub>0 n
  for show_state :: "'si :: {hashable, heap} \<Rightarrow> string"
  and A :: "('a, nat, int, 's) ta" and l\<^sub>0 :: 's and n :: nat +

  fixes trans_fun :: "('a, nat, int, 's) transition_fun"
    and inv_fun :: "(nat, int, 'si :: {hashable, heap}) invassn"
    and trans_impl :: "('a, nat, int, 'si) transition_fun"
    and l\<^sub>0i :: 'si
begin

(* XXX Should this be something different? *)
abbreviation "states \<equiv> {l\<^sub>0} \<union> (state_set (trans_of A))"

end

locale TA_Impl_Defs =
  TA_Start_Defs A l\<^sub>0 n k +
  TA_Impl_No_Ceiling_Defs show_clock show_state A l\<^sub>0 n trans_fun inv_fun trans_impl l\<^sub>0i
  for show_clock and show_state :: "'si :: {hashable, heap} \<Rightarrow> string"
  and A :: "('a, nat, int, 's) ta" and l\<^sub>0 :: 's and n :: nat and k
  and trans_fun inv_fun trans_impl l\<^sub>0i
  +
  fixes ceiling :: "'si \<Rightarrow> int iarray"
begin

definition "inv_of_A = inv_of A"

end

locale Reachability_Problem_Impl_Defs =
  Reachability_Problem_Defs A l\<^sub>0 n k F +
  TA_Impl_No_Ceiling_Defs show_clock show_state A l\<^sub>0 n trans_fun inv_fun trans_impl l\<^sub>0i
  for show_clock and show_state :: "'si :: {hashable, heap} \<Rightarrow> string"
  and A :: "('a, nat, int, 's) ta" and l\<^sub>0 :: 's and  n :: nat and k and F :: "'s \<Rightarrow> bool"
  and trans_fun inv_fun trans_impl and l\<^sub>0i
  +
  fixes F_fun :: "'si \<Rightarrow> bool"
begin

end (* Reachability Problem Impl Defs *)

definition "FWI'' n M = FWI' M n"

lemma fwi_impl'_refine_FWI'':
  "(fwi_impl' n, RETURN oo PR_CONST (\<lambda> M. FWI'' n M)) \<in> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle> nres_rel"
  unfolding FWI''_def by (rule fwi_impl'_refine_FWI')

lemmas fwi_impl_refine_FWI'' = fwi_impl.refine[FCOMP fwi_impl'_refine_FWI'']

context
  fixes n :: nat
begin

  context
    notes [map_type_eqs] = map_type_eqI[of "TYPE(nat * nat \<Rightarrow> 'e)" "TYPE('e i_mtx)"]
  begin

  sepref_register "PR_CONST (FWI'' n)"

  end

  lemmas [sepref_fr_rules] = fwi_impl_refine_FWI''

  lemma [def_pat_rules]: "FWI'' $ n \<equiv> UNPROTECT (FWI'' n)" by simp

  sepref_definition repair_pair_impl is
    "uncurry2 (RETURN ooo PR_CONST (repair_pair n))" ::
    "[\<lambda> ((_,a),b). a \<le> n \<and> b \<le> n]\<^sub>a (mtx_assn n)\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> mtx_assn n"
    unfolding repair_pair_def FWI''_def[symmetric] PR_CONST_def
    by sepref

  sepref_register repair_pair

  lemmas [sepref_fr_rules] = repair_pair_impl.refine

end

locale TA_Impl_No_Ceiling =
  TA_Impl_No_Ceiling_Defs _ _ A l\<^sub>0 n trans_fun inv_fun trans_impl l\<^sub>0i +
  TA_Start_No_Ceiling A l\<^sub>0 n
  for A :: "('a, nat, int, 's) ta"
  and l\<^sub>0 :: 's
  and n :: nat
  and trans_fun inv_fun
  and trans_impl :: "('a, nat, int, 'si :: {hashable, heap}) transition_fun"
  and l\<^sub>0i
  +
  fixes states' and loc_rel :: "('si \<times> 's) set"
  assumes trans_fun: "(trans_fun, trans_of A) \<in> transition_rel states'"
      and trans_impl:
        "(trans_impl, trans_fun) \<in> fun_rel_syn loc_rel (list_rel (Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r loc_rel))"
      and inv_fun: "(inv_fun, inv_of A) \<in> inv_rel loc_rel states'"
      and states'_states: "states \<subseteq> states'"
      and init_impl: "(l\<^sub>0i, l\<^sub>0) \<in> loc_rel"
      and loc_rel_left_unique:
        "\<And>l li li'. l \<in> states' \<Longrightarrow> (li, l) \<in> loc_rel \<Longrightarrow> (li', l) \<in> loc_rel \<Longrightarrow> li' = li"
      and loc_rel_right_unique:
        "\<And>l l' li. l \<in> states' \<Longrightarrow> l' \<in> states' \<Longrightarrow> (li,l) \<in> loc_rel \<Longrightarrow> (li,l') \<in> loc_rel
          \<Longrightarrow> l' = l"
begin

lemma trans_fun':
  "(trans_fun, trans_of A) \<in> transition_rel states"
  using transition_rel_anti_mono[OF states'_states] trans_fun by blast

lemma inv_fun': "(inv_fun, inv_of A) \<in> inv_rel loc_rel states"
  using inv_fun inv_rel_anti_mono[OF states'_states] by blast

abbreviation "location_rel \<equiv> b_rel loc_rel (\<lambda> x. x \<in> states')"

abbreviation "location_assn \<equiv> pure location_rel"

(* XXX Remove altogether? *)
abbreviation "state_assn \<equiv> prod_assn id_assn (mtx_assn n)"

abbreviation "state_assn' \<equiv> prod_assn location_assn (mtx_assn n)"

interpretation DBM_Impl n .

abbreviation
  "op_impl_assn \<equiv>
  location_assn\<^sup>k *\<^sub>a (list_assn clock_assn)\<^sup>k *\<^sub>a
  (list_assn (acconstraint_assn clock_assn id_assn))\<^sup>k *\<^sub>a location_assn\<^sup>k *\<^sub>a mtx_assn\<^sup>d \<rightarrow>\<^sub>a mtx_assn"

lemma tracei_refine:
  "(uncurry tracei, uncurry (\<lambda>_ _. RETURN ())) \<in> id_assn\<^sup>k *\<^sub>a state_assn'\<^sup>k \<rightarrow>\<^sub>a unit_assn"
    unfolding tracei_def
    using show_dbm_impl.refine[to_hnr, unfolded hn_refine_def, of n]
    by sepref_to_hoare sep_auto

end

locale TA_Impl =
  TA_Impl_Defs _ _ A l\<^sub>0 n k trans_fun inv_fun trans_impl l\<^sub>0i ceiling +
  TA_Impl_No_Ceiling _ _ A l\<^sub>0 n trans_fun inv_fun trans_impl l\<^sub>0i states' loc_rel +
  TA_Start A l\<^sub>0 n k
  for A :: "('a, nat, int, 's) ta"
  and l\<^sub>0 :: 's
  and n :: nat
  and k
  and trans_fun inv_fun
  and trans_impl :: "('a, nat, int, 'si :: {hashable, heap}) transition_fun"
  and l\<^sub>0i
  and ceiling
  and states' and loc_rel :: "('si \<times> 's) set"
  +
  assumes ceiling: "(ceiling, IArray o k') \<in> inv_rel loc_rel states'"
begin

lemma ceiling': "(ceiling, IArray o k') \<in> inv_rel loc_rel states"
  using ceiling inv_rel_anti_mono[OF states'_states] by blast

end

locale Reachability_Problem_Impl =
  Reachability_Problem_Impl_Defs _ _ A l\<^sub>0 n k F trans_fun inv_fun trans_impl l\<^sub>0i +
  TA_Impl _ _ A l\<^sub>0 n k trans_fun inv_fun trans_impl l\<^sub>0i ceiling states' loc_rel +
  Reachability_Problem A l\<^sub>0 n k F
  for A :: "('a, nat, int, 's) ta"
  and l\<^sub>0 :: 's
  and n :: nat
  and k
  and F
  and trans_fun inv_fun
  and trans_impl :: "('a, nat, int, 'si :: {hashable, heap}) transition_fun"
  and l\<^sub>0i
  and ceiling
  and states' and loc_rel :: "('si \<times> 's) set" +
  assumes F_fun: "(F_fun, F) \<in> inv_rel loc_rel states'"
begin

lemma F_fun':  "(F_fun, F) \<in> inv_rel loc_rel states"
  using F_fun inv_rel_anti_mono[OF states'_states] by blast

end

context Search_Space_finite
begin

sublocale liveness_search_space_pre:
  Liveness_Search_Space_pre "\<lambda> x y. E x y \<and> F x \<and> F y \<and> \<not> empty y" a\<^sub>0 F "(\<preceq>)"
  "\<lambda> v. reachable v \<and> \<not> empty v \<and> F v"
  using finite_reachable apply -
  apply (standard)
      apply (blast intro: finite_subset[rotated] F_mono trans)
     apply (blast intro: finite_subset[rotated] F_mono trans)
  subgoal
    by safe (blast dest: mono F_mono empty_mono)
   apply (blast intro: finite_subset[rotated] F_mono trans)
  apply (blast intro: finite_subset[rotated] F_mono trans)
  done

end

locale TA_Impl_Op =
  TA_Impl _ _ A l\<^sub>0 n k trans_fun inv_fun trans_impl l\<^sub>0i ceiling states' loc_rel
  + op: E_From_Op_Bisim A l\<^sub>0 n k f
  for A and l\<^sub>0 :: 's and n k
  and f trans_fun inv_fun trans_impl and l\<^sub>0i :: "'si:: {hashable,heap}"
  and ceiling  states' loc_rel
  +
  fixes op_impl
  assumes op_impl: "(uncurry4 op_impl, uncurry4 (\<lambda> l r. RETURN ooo f l r)) \<in> op_impl_assn"

(*
locale Reachability_Problem_Impl_Op =
  TA_Impl_Op _ _ A l\<^sub>0 n k f trans_fun inv_fun trans_impl l\<^sub>0i ceiling states' loc_rel
+ Reachability_Problem_Impl _ _ _ A l\<^sub>0 n k _ trans_fun inv_fun trans_impl l\<^sub>0i ceiling states' loc_rel
  for A and l\<^sub>0 :: 's and n k
  and f trans_fun inv_fun trans_impl and l\<^sub>0i :: "'si:: {hashable,heap}"
  and ceiling  states' loc_rel
*)

locale Reachability_Problem_Impl_Op =
  TA_Impl_Op _ _ A l\<^sub>0 n k f trans_fun inv_fun trans_impl l\<^sub>0i ceiling states' loc_rel
+ Reachability_Problem_Impl _ _ _ A l\<^sub>0 n k _ trans_fun inv_fun trans_impl l\<^sub>0i ceiling states' loc_rel
+ op: E_From_Op_Bisim_Finite_Reachability A l\<^sub>0 n k f
  for A and l\<^sub>0 :: 's and n k
  and f trans_fun inv_fun trans_impl and l\<^sub>0i :: "'si:: {hashable,heap}"
  and ceiling  states' loc_rel


section \<open>Implementing of the Successor Function\<close>

paragraph \<open>Shared Setup\<close>

context TA_Impl
begin

  interpretation DBM_Impl n .

  context
    notes [map_type_eqs] = map_type_eqI[of "TYPE(nat * nat \<Rightarrow> 'e)" "TYPE('e i_mtx)"]
  begin

  sepref_register trans_impl

  sepref_register abstr_upd up_canonical_upd norm_upd reset'_upd reset_canonical_upd

  sepref_register "PR_CONST (FW'' n)"

  sepref_register "PR_CONST (inv_of_A)"

  end

  lemmas [sepref_fr_rules] = fw_impl.refine[FCOMP fw_impl'_refine_FW'']

  lemma [def_pat_rules]: "FW'' $ n \<equiv> UNPROTECT (FW'' n)" by simp

  lemma trans_impl_clock_bounds3:
    "\<forall> c \<in> collect_clks (inv_of A l). c \<le> n"
  using collect_clks_inv_clk_set[of A l] clocks_n by force

  lemma inv_fun_rel:
    assumes "l \<in> states'" "(l1, l) \<in> loc_rel"
    shows "(inv_fun l1, inv_of A l) \<in> \<langle>\<langle>nbn_rel (Suc n), int_rel\<rangle>acconstraint_rel\<rangle>list_rel"
  proof -
    have "(xs, xs) \<in> \<langle>\<langle>nbn_rel (Suc n), int_rel\<rangle>acconstraint_rel\<rangle>list_rel"
      if "\<forall> c \<in> collect_clks xs. c \<le> n" for xs
    using that
      apply (induction xs)
      apply simp
      apply simp
      subgoal for a
        apply (cases a)
      by (auto simp: acconstraint_rel_def p2rel_def rel2p_def)
    done
    moreover have
      "inv_fun l1 = inv_of A l"
    using inv_fun assms unfolding inv_rel_def b_rel_def fun_rel_def by auto
    ultimately show ?thesis using trans_impl_clock_bounds3 by auto
  qed

  lemma [sepref_fr_rules]:
    "(return o inv_fun, RETURN o PR_CONST inv_of_A)
    \<in> location_assn\<^sup>k \<rightarrow>\<^sub>a list_assn (acconstraint_assn clock_assn int_assn)"
    using inv_fun_rel
   apply (simp add: b_assn_pure_conv aconstraint_assn_pure_conv list_assn_pure_conv inv_of_A_def)
  by sepref_to_hoare (sep_auto simp: pure_def)

  lemma [sepref_fr_rules]:
    "(return o ceiling, RETURN o PR_CONST k') \<in> location_assn\<^sup>k \<rightarrow>\<^sub>a iarray_assn"
    using ceiling by sepref_to_hoare (sep_auto simp: inv_rel_def fun_rel_def br_def)

  sepref_register "PR_CONST k'"

  lemma [def_pat_rules]: "(TA_Start_Defs.k' $ n $ k) \<equiv> PR_CONST k'" by simp

  lemma [simp]:
    "length (k' l) > n"
  by (simp add: k'_def)

  lemma [def_pat_rules]: "(TA_Impl_Defs.inv_of_A $ A) \<equiv> PR_CONST inv_of_A" by simp

  lemma reset_canonical_upd_impl_refine:
    "(uncurry3 (reset_canonical_upd_impl n), uncurry3 (\<lambda>x. RETURN \<circ>\<circ>\<circ> reset_canonical_upd x))
      \<in> [\<lambda>(((_, i), j), _).
             i \<le> n \<and>
             j \<le> n]\<^sub>a mtx_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a clock_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> mtx_assn"
    apply sepref_to_hnr
    apply (rule hn_refine_preI)
    apply (rule hn_refine_cons[OF _ reset_canonical_upd_impl.refine[to_hnr], simplified])
    by (sep_auto simp: hn_ctxt_def b_assn_def entailst_def)+

  lemmas [sepref_fr_rules] =
    abstr_upd_impl.refine up_canonical_upd_impl.refine norm_upd_impl.refine
    reset_canonical_upd_impl_refine

  lemma constraint_clk_acconstraint_rel_simps:
    assumes "(ai, a) \<in> \<langle>nbn_rel (Suc n), id_rel\<rangle>acconstraint_rel"
    shows "constraint_clk a < Suc n" "constraint_clk ai = constraint_clk a"
    using assms by (cases ai; cases a; auto simp: acconstraint_rel_def p2rel_def rel2p_def)+

  lemma [sepref_fr_rules]:
    "(return o constraint_clk, RETURN o constraint_clk)
     \<in> (acconstraint_assn clock_assn id_assn)\<^sup>k \<rightarrow>\<^sub>a clock_assn"
    apply (simp add: b_assn_pure_conv aconstraint_assn_pure_conv)
    by sepref_to_hoare (sep_auto simp: pure_def constraint_clk_acconstraint_rel_simps)

  sepref_register constraint_clk

  sepref_register
    "repair_pair n :: ((nat \<times> nat \<Rightarrow> ('b :: {linordered_cancel_ab_monoid_add}) DBMEntry)) \<Rightarrow> _" ::
    "(('ee DBMEntry) i_mtx) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ((nat \<times> nat \<Rightarrow> 'ee DBMEntry))"

  sepref_register abstra_upd :: "(nat, 'e) acconstraint \<Rightarrow> 'e DBMEntry i_mtx \<Rightarrow> 'e DBMEntry i_mtx"

  sepref_register n

  lemmas [sepref_import_param] = IdI[of n]

  sepref_definition abstra_repair_impl is
    "uncurry (RETURN oo PR_CONST abstra_repair)" ::
    "(acconstraint_assn clock_assn id_assn)\<^sup>k *\<^sub>a mtx_assn\<^sup>d \<rightarrow>\<^sub>a mtx_assn"
    unfolding abstra_repair_def PR_CONST_def by sepref

  sepref_register abstra_repair :: "(nat, 'e) acconstraint \<Rightarrow> 'e DBMEntry i_mtx \<Rightarrow> 'e DBMEntry i_mtx"

  lemmas [sepref_fr_rules] = abstra_repair_impl.refine

  sepref_definition abstr_repair_impl is
    "uncurry (RETURN oo PR_CONST abstr_repair)" ::
    "(list_assn (acconstraint_assn clock_assn id_assn))\<^sup>k *\<^sub>a mtx_assn\<^sup>d \<rightarrow>\<^sub>a mtx_assn"
    unfolding abstr_repair_def PR_CONST_def by sepref

  sepref_register abstr_repair ::
    "(nat, 'e) acconstraint list \<Rightarrow> 'e DBMEntry i_mtx \<Rightarrow> 'e DBMEntry i_mtx"

  lemmas [sepref_fr_rules] = abstr_repair_impl.refine

end (* TA Impl *)

paragraph \<open>Implementation for an Arbitrary DBM Successor Operation\<close>

context Reachability_Problem_Impl
begin

(* XXX Better implementation? *)
lemma F_rel_alt_def:
  "F_rel = (\<lambda> (l, M). F l  \<and> \<not> check_diag n M)"
unfolding F_rel_def by auto

sepref_register F

lemma [sepref_fr_rules]:
  "(return o F_fun, RETURN o F) \<in> location_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
using F_fun by sepref_to_hoare (sep_auto simp: inv_rel_def b_rel_def fun_rel_def)

sepref_definition F_impl is
  "RETURN o (\<lambda> (l, M). F l)" :: "state_assn'\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  by sepref

end

context TA_Impl_Op
begin

  definition succs where
    "succs \<equiv> \<lambda> (l, D). rev (map (\<lambda> (g,a,r,l'). (l', f l r g l' D)) (trans_fun l))"

  definition succs_P where
    "succs_P P \<equiv> \<lambda> (l, D).
      rev (map (\<lambda> (g,a,r,l'). (l', f l r g l' D)) (filter (\<lambda> (g,a,r,l'). P l') (trans_fun l)))"

  definition succs' where
    "succs' \<equiv> \<lambda> (l, D). do
      {
        xs \<leftarrow> nfoldli (trans_fun l) (\<lambda> _. True) (\<lambda> (g,a,r,l') xs.
          RETURN ((l', f l r g l' (op_mtx_copy D)) # xs)
        ) [];
        RETURN xs
      }"

  definition succs_P' where
    "succs_P' P \<equiv> \<lambda> (l, D). do
      {
        xs \<leftarrow> nfoldli (trans_fun l) (\<lambda> _. True) (\<lambda> (g,a,r,l') xs.
          RETURN (if P l' then (l', f l r g l' (op_mtx_copy D)) # xs else xs)
        ) [];
        RETURN xs
      }"

  (** XXX Unused *)
  lemma RETURN_split:
    "RETURN (f a b) = do
      {
        a \<leftarrow> RETURN a;
        b \<leftarrow> RETURN b;
        RETURN (f a b)
      }"
   by simp

  lemma succs'_succs:
    "succs' lD = RETURN (succs lD)"
  unfolding succs'_def succs_def rev_map_fold
    apply (cases lD)
    apply simp
    apply (rewrite fold_eq_nfoldli)
    apply (fo_rule arg_cong fun_cong)+
    apply auto
  done

  lemma succs_P'_succs_P:
    "succs_P' P lD = RETURN (succs_P P lD)"
    unfolding succs_P'_def succs_P_def rev_map_fold fold_filter
    apply (cases lD)
    apply simp
    apply (rewrite fold_eq_nfoldli)
    apply (fo_rule arg_cong fun_cong)+
    by auto

  lemmas [sepref_fr_rules] = dbm_subset'_impl.refine

  sepref_register "PR_CONST (dbm_subset' n)" :: "'e DBMEntry i_mtx \<Rightarrow> 'e DBMEntry i_mtx \<Rightarrow> bool"

  lemma [def_pat_rules]:
    "dbm_subset' $ n \<equiv> PR_CONST (dbm_subset' n)"
    by simp

  lemmas [sepref_fr_rules] = check_diag_impl.refine

  sepref_register "PR_CONST (check_diag n)" :: "'e DBMEntry i_mtx \<Rightarrow> bool"

  lemma [def_pat_rules]:
    "check_diag $ n \<equiv> PR_CONST (check_diag n)"
  by simp

  definition
  "subsumes' =
    (\<lambda> (l, M :: ('tt :: {zero,linorder}) DBM') (l', M').
      l = l' \<and> pointwise_cmp (\<le>) n (curry M) (curry M'))"

  context
  begin

  notation fun_rel_syn (infixr "\<rightarrow>" 60)

  lemma left_unique_location_rel:
    "IS_LEFT_UNIQUE location_rel"
    unfolding IS_LEFT_UNIQUE_def
    by (rule single_valuedI) (auto intro: loc_rel_left_unique single_valuedI)

  lemma right_unique_location_rel:
    "IS_RIGHT_UNIQUE location_rel"
    by (rule single_valuedI) (auto intro: loc_rel_right_unique)

  lemma [sepref_import_param]:
    "((=), (=)) \<in> location_rel \<rightarrow> location_rel \<rightarrow> Id"
    using left_unique_location_rel right_unique_location_rel
    by (blast dest: IS_LEFT_UNIQUED IS_RIGHT_UNIQUED)

  sepref_definition subsumes_impl is
    "uncurry (RETURN oo subsumes')" :: "state_assn'\<^sup>k *\<^sub>a state_assn'\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    unfolding subsumes'_def short_circuit_conv dbm_subset'_def[symmetric]
    by sepref

  end

  (* XXX Somewhat peculiar use of the zero instance for DBM entries *)
  lemma init_dbm_alt_def:
    "init_dbm = op_amtx_dfltNxM (Suc n) (Suc n) (Le 0)"
  unfolding init_dbm_def op_amtx_dfltNxM_def neutral by auto

  lemma [sepref_import_param]: "(Le 0, PR_CONST (Le 0)) \<in> Id" by simp

  lemma [def_pat_rules]: "Le $ 0 \<equiv> PR_CONST (Le 0)" by simp

  sepref_register "PR_CONST (Le 0)"

  sepref_definition init_dbm_impl is
    "uncurry0 (RETURN (init_dbm :: nat \<times> nat \<Rightarrow> _))" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a (mtx_assn n)"
  unfolding init_dbm_alt_def by sepref

  lemmas [sepref_fr_rules] = init_dbm_impl.refine

  sepref_register l\<^sub>0

  lemma [sepref_import_param]:
    "(l\<^sub>0i, l\<^sub>0) \<in> location_rel"
    using init_impl states'_states by auto

  sepref_definition a\<^sub>0_impl is
    "uncurry0 (RETURN a\<^sub>0)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a state_assn'"
    unfolding a\<^sub>0_def by sepref

  lemma trans_impl_trans_of[intro]:
    "(g, a, r, l') \<in> set (trans_fun l) \<Longrightarrow> l \<in> states' \<Longrightarrow> A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"
    using trans_fun unfolding transition_rel_def by auto

  lemma trans_of_trans_impl[intro]:
    "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<Longrightarrow> l \<in> states' \<Longrightarrow> (g, a, r, l') \<in> set (trans_fun l)"
    using trans_fun unfolding transition_rel_def by auto

  lemma trans_impl_clock_bounds1:
    "(g, a, r, l') \<in> set (trans_fun l) \<Longrightarrow> l \<in> states' \<Longrightarrow> \<forall> c \<in> set r. c \<le> n"
    using clocks_n reset_clk_set[OF trans_impl_trans_of] by fastforce

  lemma trans_impl_clock_bounds2:
    "(g, a, r, l') \<in> set (trans_fun l) \<Longrightarrow> l \<in> states' \<Longrightarrow> \<forall> c \<in> collect_clks g. c \<le> n"
    using clocks_n collect_clocks_clk_set[OF trans_impl_trans_of] by fastforce

  lemma trans_impl_states:
    "(g, a, r, l') \<in> set (trans_fun l) \<Longrightarrow> l \<in> states' \<Longrightarrow> l' \<in> state_set (trans_of A)"
     apply (drule trans_impl_trans_of)
     apply assumption
     unfolding state_set_def
     apply (rule UnI2)
     by force

  lemma trans_impl_states':
    "(g, a, r, l') \<in> set (trans_fun l) \<Longrightarrow> l \<in> states' \<Longrightarrow> l' \<in> states'"
    using trans_impl_states states'_states by auto

  lemma trans_of_states[intro]:
    "l' \<in> states" if "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" "l \<in> states'"
    using that by (auto intro: trans_impl_states)

  lemma trans_of_states'[intro]:
    "l' \<in> states'" if "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" "l \<in> states'"
    using that states'_states by (auto intro: trans_impl_states)

  abbreviation "clock_rel \<equiv> nbn_rel (Suc n)"

  lemma [sepref_import_param]:
    "(trans_impl, trans_fun)
      \<in> location_rel \<rightarrow>
        \<langle>\<langle>\<langle>clock_rel, int_rel\<rangle> acconstraint_rel\<rangle> list_rel \<times>\<^sub>r Id \<times>\<^sub>r \<langle>clock_rel\<rangle> list_rel \<times>\<^sub>r location_rel\<rangle>
        list_rel"
  proof (rule fun_relI)
    fix li l
    assume "(li, l) \<in> location_rel"
    { fix xs  :: "((nat, int) acconstraint list \<times> 'a \<times> nat list \<times> 's) list"
        and xs' :: "((nat, int) acconstraint list \<times> 'a \<times> nat list \<times> 'si) list"
      assume A:
        "\<forall> g a r l'. (g, a, r, l') \<in> set xs
          \<longrightarrow> (\<forall> c \<in> collect_clks g. c \<le> n) \<and> (\<forall> c \<in> set r. c \<le> n) \<and> l' \<in> states'"
      assume "(xs', xs) \<in> \<langle>Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r loc_rel\<rangle>list_rel"
      then have
        "(xs', xs) \<in>
          \<langle>\<langle>\<langle>clock_rel, int_rel\<rangle>acconstraint_rel\<rangle>list_rel
              \<times>\<^sub>r Id
              \<times>\<^sub>r \<langle>clock_rel\<rangle>list_rel
              \<times>\<^sub>r location_rel
          \<rangle>list_rel"
        using A
      proof (induction xs' xs)
        case 1 then show ?case
          by simp
      next
        case (2 x' x xs' xs)
        obtain g a r l' where [simp]: "x = (g, a, r, l')"
          by (cases x)
        obtain gi ai ri l'i where [simp]: "x' = (gi, ai, ri, l'i)"
          by (cases x')
        from 2 have r_bounds: "\<forall> c \<in> set r. c \<le> n"
          by auto
        from 2 have "\<forall> c \<in> collect_clks g. c \<le> n"
          by auto
        then have "(g, g) \<in> \<langle>\<langle>nbn_rel (Suc n), int_rel\<rangle>acconstraint_rel\<rangle>list_rel"
          apply (induction g; simp)
          subgoal for a
            by (cases a)
               (auto simp: acconstraint_rel_def p2rel_def rel2p_def split: acconstraint.split)
          done
        moreover from r_bounds have "(r, r) \<in> \<langle>nbn_rel (Suc n)\<rangle>list_rel"
          by (induction r) auto
        moreover from 2(1,4) have "(l'i, l') \<in> location_rel"
          by auto
        ultimately have
          "(x', x) \<in>
            \<langle>\<langle>clock_rel, int_rel\<rangle>acconstraint_rel\<rangle>list_rel \<times>\<^sub>r Id \<times>\<^sub>r \<langle>clock_rel\<rangle>list_rel \<times>\<^sub>r location_rel"
          using 2(1) by simp
        moreover from 2 have
          "(xs', xs)
            \<in> \<langle>\<langle>\<langle>clock_rel, int_rel\<rangle>acconstraint_rel\<rangle>list_rel \<times>\<^sub>r Id
                \<times>\<^sub>r \<langle>clock_rel\<rangle>list_rel \<times>\<^sub>r location_rel\<rangle>list_rel"
          by force
        ultimately show ?case by simp
      qed
    } note * = this
    from
      \<open>(li, l) \<in> _\<close> trans_impl_clock_bounds1 trans_impl_clock_bounds2 trans_impl_states' trans_impl
    show "(trans_impl li, trans_fun l)
        \<in> \<langle>\<langle>\<langle>clock_rel, int_rel\<rangle>acconstraint_rel\<rangle>list_rel \<times>\<^sub>r
           Id \<times>\<^sub>r \<langle>clock_rel\<rangle>list_rel \<times>\<^sub>r location_rel\<rangle>list_rel"
      by - (rule *, auto, (drule fun_relD, assumption, simp add: relAPP_def)+)
  qed

  lemma b_rel_subtype[sepref_frame_match_rules]:
    "hn_val (b_rel R P) a b \<Longrightarrow>\<^sub>t hn_val R a b"
  by (rule enttI) (sep_auto simp: hn_ctxt_def pure_def)

  lemma b_rel_subtype_merge[sepref_frame_merge_rules]:
    "hn_val (b_rel R p) a b \<or>\<^sub>A hn_val R a b \<Longrightarrow>\<^sub>t hn_val R a b"
    "hn_val R a b \<or>\<^sub>A hn_val (b_rel R p) a b \<Longrightarrow>\<^sub>t hn_val R a b"
  by (simp add: b_rel_subtype entt_disjE)+

  lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "asmtx_assn n a" for a]

  sepref_register f ::
    "'s \<Rightarrow> nat list \<Rightarrow> (nat, int) acconstraint list \<Rightarrow> 's \<Rightarrow> int DBMEntry i_mtx \<Rightarrow> int DBMEntry i_mtx"

  lemmas [sepref_fr_rules] = op_impl

  context
    notes [id_rules] = itypeI[of "PR_CONST n" "TYPE (nat)"]
      and [sepref_import_param] = IdI[of n]
  begin

  sepref_register trans_fun

  sepref_definition succs_impl is
    "RETURN o PR_CONST succs" :: "state_assn'\<^sup>k \<rightarrow>\<^sub>a list_assn state_assn'"
  unfolding PR_CONST_def
  unfolding
    comp_def succs'_succs[symmetric] succs'_def
    FW''_def[symmetric] rev_map_fold inv_of_A_def[symmetric]
  apply (rewrite "HOL_list.fold_custom_empty")
  by sepref

  sepref_register succs :: "'s \<times> (int DBMEntry i_mtx) \<Rightarrow> ('s \<times> (int DBMEntry i_mtx)) list"

  lemmas [sepref_fr_rules] = succs_impl.refine

  sepref_definition succs_impl' is
    "RETURN o (filter (\<lambda> (l, M). \<not>check_diag n M) o succs)"  :: "state_assn'\<^sup>k \<rightarrow>\<^sub>a list_assn state_assn'"
    apply (rewrite in succs PR_CONST_def[symmetric])
    unfolding list_filter_foldli (* XXX This might be slightly inefficient \<rightarrow> can we do better? *)
    apply (rewrite "HOL_list.fold_custom_empty")
    by sepref

  end (* End sepref setup *)

  context
    fixes P :: "'s \<Rightarrow> bool" and P_fun
    assumes P_fun: "(P_fun, P) \<in> inv_rel loc_rel states'"
  begin

  context
    notes [id_rules] = itypeI[of "PR_CONST n" "TYPE (nat)"]
      and [sepref_import_param] = IdI[of n]
  begin

  sepref_register "PR_CONST P"

  lemma [sepref_fr_rules]:
    "(return o P_fun, RETURN o PR_CONST P) \<in> location_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
    using P_fun by sepref_to_hoare (sep_auto simp: inv_rel_def b_rel_def fun_rel_def)

  sepref_definition succs_P_impl is
    "RETURN o PR_CONST (succs_P P)" :: "state_assn'\<^sup>k \<rightarrow>\<^sub>a list_assn state_assn'"
    unfolding PR_CONST_def
    apply (rewrite in P PR_CONST_def[symmetric])
    unfolding
      comp_def succs_P'_succs_P[symmetric] succs_P'_def
      FW''_def[symmetric] rev_map_fold inv_of_A_def[symmetric]
    apply (rewrite "HOL_list.fold_custom_empty")
    by sepref

  sepref_register "succs_P P" :: "'s \<times> (int DBMEntry i_mtx) \<Rightarrow> ('s \<times> (int DBMEntry i_mtx)) list"

  lemmas [sepref_fr_rules] = succs_P_impl.refine

  sepref_definition succs_P_impl' is
    "RETURN o (filter (\<lambda> (l, M). \<not>check_diag n M) o succs_P P)"  :: "state_assn'\<^sup>k \<rightarrow>\<^sub>a list_assn state_assn'"
    apply (rewrite in "succs_P P" PR_CONST_def[symmetric])
    unfolding list_filter_foldli (* XXX This might be slightly inefficient \<rightarrow> can we do better? *)
    apply (rewrite "HOL_list.fold_custom_empty")
    by sepref

  end (* End sepref setup *)

  end (* Fixed predicate *)

  (* XXX Move to different context *)
  lemma reachable_states:
    "l \<in> states" if "op.E_from_op\<^sup>*\<^sup>* a\<^sub>0 (l, M)"
    using that
    by (induction "(l, M)" arbitrary: l M; force simp: a\<^sub>0_def state_set_def op.E_from_op_def)

  definition "emptiness_check \<equiv> \<lambda> (l, M). check_diag n M"

  sepref_definition emptiness_check_impl  is
    "RETURN o emptiness_check" :: "state_assn'\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    unfolding emptiness_check_def
    by sepref

  lemma state_copy:
    "RETURN \<circ> COPY = (\<lambda> (l, M). do {M' \<leftarrow> mop_mtx_copy M; RETURN (l, M')})"
    by auto

  sepref_definition state_copy_impl is
    "RETURN \<circ> COPY" :: "state_assn'\<^sup>k \<rightarrow>\<^sub>a state_assn'"
    unfolding state_copy
    by sepref

  lemma location_assn_constraints:
    "is_pure location_assn"
    "IS_LEFT_UNIQUE (the_pure location_assn)"
    "IS_RIGHT_UNIQUE (the_pure location_assn)"
    using left_unique_location_rel right_unique_location_rel
    by (auto elim: single_valued_subset[rotated] simp: b_rel_def IS_LEFT_UNIQUE_def)

  lemma not_check_diag_init_dbm[intro, simp]:
      "\<not> check_diag n init_dbm"
      unfolding check_diag_def init_dbm_def by auto

end (* TA Impl Op *)

  section \<open>Instantiation of Worklist Algorithms\<close>

context Reachability_Problem_Impl_Op
begin

  sublocale Worklist0 op.E_from_op a\<^sub>0 F_rel "subsumes n" succs "\<lambda> (l, M). check_diag n M"
    apply standard
    apply (clarsimp simp: op.reachable_def split: prod.split dest!: reachable_states)
    unfolding succs_def op.E_from_op_def using states'_states by force

  sublocale Worklist1 op.E_from_op a\<^sub>0 F_rel "subsumes n" succs "\<lambda> (l, M). check_diag n M" ..

  sublocale Worklist2 op.E_from_op a\<^sub>0 F_rel "subsumes n" succs "\<lambda> (l, M). check_diag n M" subsumes'
    apply standard
    unfolding subsumes_def subsumes'_def by auto

  sublocale
    Worklist3
      op.E_from_op a\<^sub>0 F_rel "subsumes n" succs "\<lambda> (l, M). check_diag n M" subsumes' "\<lambda> (l, M). F l"
    apply standard
    unfolding F_rel_def by auto

  sublocale
    Worklist4
      op.E_from_op a\<^sub>0 F_rel "subsumes n" succs "\<lambda> (l, M). check_diag n M" subsumes' "\<lambda> (l, M). F l"
    apply standard
    unfolding F_rel_def by auto

  sublocale
    Worklist_Map a\<^sub>0 F_rel "subsumes n" "\<lambda> (l, M). check_diag n M" subsumes' op.E_from_op fst succs
    apply standard
    unfolding subsumes'_def by auto

  sublocale
    Worklist_Map2
      a\<^sub>0 F_rel "subsumes n" "\<lambda> (l, M). check_diag n M" subsumes' op.E_from_op
      fst succs "\<lambda> (l, M). F l"
    ..

  sublocale Worklist4_Impl
    op.E_from_op a\<^sub>0 F_rel "subsumes n" succs "\<lambda> (l, M). check_diag n M" subsumes' "\<lambda> (l, M). F l"
    state_assn' succs_impl a\<^sub>0_impl F_impl subsumes_impl emptiness_check_impl
    apply standard
    apply (unfold PR_CONST_def)
    by (rule
        a\<^sub>0_impl.refine F_impl.refine subsumes_impl.refine succs_impl.refine[unfolded PR_CONST_def]
        emptiness_check_impl.refine[unfolded emptiness_check_def]
        )+

  sublocale Worklist_Map2_Impl
    op.E_from_op a\<^sub>0 F_rel "subsumes n" succs "\<lambda> (l, M). check_diag n M" subsumes'
    "\<lambda> (l, M). F l" state_assn'
    succs_impl a\<^sub>0_impl F_impl subsumes_impl emptiness_check_impl fst "return o fst" state_copy_impl
    tracei location_assn
    apply standard
    subgoal
    unfolding PR_CONST_def
     apply sepref_to_hoare
    apply sep_auto
    done
  subgoal
    by (rule state_copy_impl.refine)
  subgoal
    unfolding trace_def by (rule tracei_refine)
  by (rule location_assn_constraints)+

  sublocale Worklist_Map2_Hashable
    op.E_from_op a\<^sub>0 F_rel "subsumes n" succs "\<lambda> (l, M). check_diag n M" subsumes' "\<lambda> (l, M). F l"
    state_assn' succs_impl a\<^sub>0_impl F_impl subsumes_impl emptiness_check_impl
    fst "return o fst" state_copy_impl tracei location_assn by standard

  sublocale liveness: Liveness_Search_Space_Key
    "\<lambda> (l, M) (l', M'). op.E_from_op (l, M) (l', M') \<and> F l \<and> F l' \<and> \<not> check_diag n M'" a\<^sub>0
    "\<lambda> _. False"
    "subsumes n" "\<lambda> (l, M). op.reachable (l, M) \<and> \<not> check_diag n M \<and> F l"
    "filter (\<lambda> (l, M). \<not>check_diag n M) o succs_P F" fst subsumes'
    apply standard
           apply blast
          apply (blast intro: op.liveness_search_space_pre.trans)
    subgoal for a b a'
      apply (drule op.liveness_search_space_pre.mono[where a'=a'])
      unfolding op.liveness_search_space_pre.G.E'_def by (auto simp: F_rel_def)
        apply blast
    subgoal
      using op.liveness_search_space_pre.finite_V
      by (auto elim: finite_subset[rotated] simp: F_rel_def)
    subgoal premises prems for a
    proof -
      have
        "set ((filter (\<lambda> (l, M). \<not>check_diag n M) o succs_P F) a)
        = {x. (\<lambda>(l, M) (l', M'). op.E_from_op (l, M) (l', M') \<and> F l' \<and> \<not> check_diag n M') a x}"
        unfolding op.E_from_op_def succs_P_def using prems states'_states
        by (safe; force dest!: reachable_states simp: op.reachable_def)
      also have "\<dots> =
        {x. Subgraph_Node_Defs.E'
         (\<lambda>(l, M) (l', M'). op.E_from_op (l, M) (l', M') \<and> F l \<and> F l' \<and> \<not> check_diag n M')
         (\<lambda>(l, M). op.reachable (l, M) \<and> \<not> check_diag n M \<and> F l) a x}"
        unfolding Subgraph_Node_Defs.E'_def using prems by auto
      finally show ?thesis .
    qed
    by (blast intro!: empty_subsumes')+

  sublocale liveness: Liveness_Search_Space_Key_Impl
    a\<^sub>0 "\<lambda> _. False" "subsumes n" "\<lambda> (l, M). op.reachable (l, M) \<and> \<not> check_diag n M \<and> F l"
    "filter (\<lambda> (l, M). \<not>check_diag n M) o succs_P F"
    "\<lambda> (l, M) (l', M'). op.E_from_op (l, M) (l', M') \<and> F l \<and> F l' \<and> \<not> check_diag n M'"
    subsumes' fst
    state_assn' "succs_P_impl' F_fun" a\<^sub>0_impl subsumes_impl "return o fst" state_copy_impl
    location_assn
    apply standard
    apply (rule location_assn_constraints)+
        apply (unfold PR_CONST_def, rule a\<^sub>0_impl.refine; fail)
       apply (unfold PR_CONST_def, rule subsumes_impl.refine; fail)
      apply (unfold PR_CONST_def, rule succs_P_impl'.refine[OF F_fun])
    subgoal
      by sepref_to_hoare sep_auto
    by (rule state_copy_impl.refine)

  lemma precond_a\<^sub>0:
    "case a\<^sub>0 of (l, M) \<Rightarrow> op.reachable (l, M) \<and> \<not> check_diag n M"
    unfolding op.reachable_def unfolding a\<^sub>0_def by auto

  lemma liveness_step_equiv:
    fixes x y
    assumes "(\<lambda> (l, M). op.reachable (l, M) \<and> \<not> check_diag n M \<and> F l) x"
    shows "liveness.G.E' x y \<longleftrightarrow>
      (\<lambda> (l, M) (l', M'). op.E_from_op (l, M) (l', M') \<and> F l \<and> F l' \<and> \<not> check_diag n M') x y"
    using assms unfolding liveness.G.E'_def by auto

  lemma liveness_check_equiv:
    "(\<exists>x. liveness.G.G'.reaches a\<^sub>0 x \<and> liveness.G.G'.reaches1 x x) \<longleftrightarrow>
       (\<exists> x. op.liveness_pre.reaches a\<^sub>0 x \<and> op.liveness_pre.reaches1 x x)"
    if "F l\<^sub>0"
    apply (subst rtranclp_tranclp_equiv[OF liveness_step_equiv])
       apply assumption
    subgoal
      unfolding liveness.G.E'_def by auto
    subgoal
      using that precond_a\<^sub>0 by (auto simp: a\<^sub>0_def)
    ..

  lemma liveness_spec_refine:
    "SPEC (\<lambda>r. r =
       (\<exists>x. liveness.G.G'.reaches a\<^sub>0 x \<and> liveness.G.G'.reaches1 x x)) \<le>
     (SPEC (\<lambda> r. r =
     (\<exists> x.
       (\<lambda> (l, M) (l', M'). op.E_from_op (l, M) (l', M') \<and> F l \<and> F l' \<and> \<not> check_diag n M')\<^sup>*\<^sup>* a\<^sub>0 x \<and>
       (\<lambda> (l, M) (l', M'). op.E_from_op (l, M) (l', M') \<and> F l \<and> F l' \<and> \<not> check_diag n M')\<^sup>+\<^sup>+ x x)
      )
     )
    " if "F l\<^sub>0"
    using liveness_check_equiv[OF that] by auto

  lemma liveness_hnr:
    "(uncurry0
      (dfs_map_impl' (succs_P_impl' F_fun) a\<^sub>0_impl subsumes_impl
        (return \<circ> fst) state_copy_impl),
     uncurry0 (SPEC (\<lambda>r. r = (\<exists>x. op.liveness_pre.reaches a\<^sub>0 x \<and> op.liveness_pre.reaches1 x x))))
      \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    if "F l\<^sub>0"
    apply (rule liveness.dfs_map_impl'_hnr[
        FCOMP liveness_spec_refine[THEN Id_SPEC_refine, THEN nres_relI]
        ])
    using that precond_a\<^sub>0 by (auto simp: a\<^sub>0_def)

  context
    fixes Q :: "'s \<Rightarrow> bool" and Q_fun
    assumes Q_fun: "(Q_fun, Q) \<in> inv_rel loc_rel states'"
  begin

  interpretation leadsto: Leadsto_Search_Space_Key
    a\<^sub>0 "\<lambda> _. False" "subsumes n" "\<lambda> (l, M). check_diag n M" subsumes'
    "\<lambda> (l, M) (l', M'). op.E_from_op (l, M) (l', M') \<and> \<not> check_diag n M'"
    fst "\<lambda> _. False" "\<lambda> (l, M). F l" "\<lambda> (l, M). Q l"
    "filter (\<lambda> (l, M). \<not>check_diag n M) o succs_P Q" "filter (\<lambda> (l, M). \<not>check_diag n M) o succs"
  proof (goal_cases)
    case 1
    interpret Subgraph_Start
      op.E_from_op a\<^sub>0 "\<lambda> (l, M) (l', M'). op.E_from_op (l, M) (l', M') \<and> \<not> check_diag n M'"
      by standard auto
    show ?case
      apply standard
                    apply blast
                   apply (blast intro: liveness.trans)
      subgoal for a b a'
        by (drule op.mono[where a' = a'], auto dest: op.empty_mono[rotated] intro: reachable)
                 apply (blast intro: op.empty_subsumes)
                apply (rule op.empty_mono; assumption)
      subgoal for x x'
        by (auto dest: op.E_from_op_check_diag)
              apply assumption
             apply blast
            apply blast
      subgoal for a
        by (auto dest: succs_correct reachable)
          apply (simp; fail)
      subgoal
        using op.finite_reachable by (auto intro: reachable elim!: finite_subset[rotated])
      subgoal for a a'
        by (auto simp: empty_subsumes' dest: subsumes_key)
      subgoal for a a'
        by (auto simp: empty_subsumes' dest: subsumes_key)
      subgoal premises prems for a
      proof -
        have
          "set ((filter (\<lambda> (l, M). \<not>check_diag n M) o succs_P Q) a)
            = {x. (\<lambda>(l, M) (l', M'). op.E_from_op (l, M) (l', M') \<and> Q l' \<and> \<not> check_diag n M') a x}"
          unfolding op.E_from_op_def succs_P_def using prems states'_states
          by (safe; force dest!: reachable reachable_states simp: op.reachable_def)
        then show ?thesis
          by auto
      qed
      done
  qed

  sepref_register "PR_CONST Q"

  lemma [sepref_fr_rules]:
    "(return o Q_fun, RETURN o PR_CONST Q) \<in> location_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
    using Q_fun by sepref_to_hoare (sep_auto simp: inv_rel_def b_rel_def fun_rel_def)

  sepref_definition Q_impl is
    "RETURN o (\<lambda> (l, M). Q l)" :: "state_assn'\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    by (rewrite in Q PR_CONST_def[symmetric]) sepref

  interpretation leadsto: Leadsto_Search_Space_Key_Impl
    "subsumes n" subsumes' location_assn fst a\<^sub>0 "\<lambda> _. False" "\<lambda> _. False" state_copy_impl
    "\<lambda> (l, M). F l" "\<lambda> (l, M). Q l"
    "\<lambda> (l, M). op.reachable (l, M) \<and> \<not> check_diag n M"
    "\<lambda> (l, M). check_diag n M"
    "filter (\<lambda> (l, M). \<not>check_diag n M) o succs_P Q" "filter (\<lambda> (l, M). \<not>check_diag n M) o succs"
    "\<lambda> (l, M) (l', M'). op.E_from_op (l, M) (l', M') \<and> \<not> check_diag n M'"
    state_assn'
    "succs_P_impl' Q_fun" a\<^sub>0_impl subsumes_impl "return o fst" succs_impl'
    emptiness_check_impl F_impl Q_impl tracei
    apply standard
                       apply blast
                      apply (blast intro: op.trans)
    subgoal for a b a'
      apply (drule op.mono[where a' = a'], auto dest: op.empty_mono[rotated])
      apply (intro exI conjI)
           apply (auto dest: op.empty_mono[rotated])
      by (auto simp: empty_subsumes' dest: subsumes_key)
                    apply blast
    subgoal
      using op.finite_reachable by (auto elim!: finite_subset[rotated])
    subgoal premises prems for a
    proof -
      have
        "set ((filter (\<lambda> (l, M). \<not>check_diag n M) o succs_P Q) a)
            = {x. (\<lambda>(l, M) (l', M'). op.E_from_op (l, M) (l', M') \<and> Q l' \<and> \<not> check_diag n M') a x}"
        unfolding op.E_from_op_def succs_P_def using prems states'_states
        by (safe; force dest!: reachable_states[folded op.reachable_def])
      also have "\<dots> =
            {x. Subgraph_Node_Defs.E'
             (\<lambda>x y.
              (case x of (l, M) \<Rightarrow> \<lambda>(l', M'). op.E_from_op (l, M) (l', M') \<and> \<not> check_diag n M') y
                \<and> \<not> (case y of (l, M) \<Rightarrow> check_diag n M) \<and> (case y of (l, M) \<Rightarrow> Q l)
              )
             (\<lambda>(l, M). op.reachable (l, M) \<and> \<not> check_diag n M) a x}"
        unfolding Subgraph_Node_Defs.E'_def using prems by auto
      finally show ?thesis .
    qed
                 apply blast
                apply (clarsimp simp: empty_subsumes'; fail)
               apply (rule location_assn_constraints)+
            apply (rule liveness.refinements)
           apply (rule liveness.refinements)
          apply (unfold PR_CONST_def, rule succs_P_impl'.refine[OF Q_fun])
    subgoal
      by sepref_to_hoare sep_auto
    by (rule
        succs_impl'.refine liveness.refinements
        emptiness_check_impl.refine[unfolded emptiness_check_def]
        F_impl.refine Q_impl.refine tracei_refine
        )+

  definition
    "leadsto_spec_alt = SPEC (\<lambda>r. r \<longleftrightarrow>
       (\<exists>a. leadsto.A.search_space.reaches a\<^sub>0 a \<and>
            \<not> (case a of (l, M) \<Rightarrow> check_diag n M) \<and>
            (case a of (l, M) \<Rightarrow> F l) \<and> (case a of (l, M) \<Rightarrow> Q l) \<and>
            (\<exists>b. leadsto.B.reaches a b \<and> leadsto.B.reaches1 b b))
     )
    "

  lemmas leadsto_impl_hnr =
    leadsto.leadsto_impl_hnr[
      unfolded leadsto.leadsto_spec_alt_def, unfolded leadsto.reaches_cycle_def,
      folded leadsto_spec_alt_def
    ]

  end (* Context for second predicate *)

end (* Reachability Problem Impl Op *)


section \<open>Implementation of the Invariant Precondition Check\<close>

context TA_Impl_Op
begin

  definition
    "unbounded_dbm' = unbounded_dbm"

  lemma unbounded_dbm_alt_def:
    "unbounded_dbm = op_amtx_new (Suc n) (Suc n) (unbounded_dbm')"
    unfolding unbounded_dbm'_def
    by simp

  text \<open>We need the custom rule here because unbounded\_dbm is a higher-order constant\<close>
  lemma [sepref_fr_rules]:
    "(uncurry0 (return unbounded_dbm'), uncurry0 (RETURN (PR_CONST (unbounded_dbm'))))
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a pure (nat_rel \<times>\<^sub>r nat_rel \<rightarrow> Id)"
    by sepref_to_hoare sep_auto

  sepref_register "init_dbm :: nat \<times> nat \<Rightarrow> _" :: "'e DBMEntry i_mtx"

  sepref_register "unbounded_dbm :: nat \<times> nat \<Rightarrow> int DBMEntry" :: "'b DBMEntry i_mtx"
  sepref_register "unbounded_dbm' :: nat \<times> nat \<Rightarrow> _ DBMEntry"

  text \<open>Necessary to solve side conditions of @{term op_amtx_new}\<close>
  lemma unbounded_dbm'_bounded:
    "mtx_nonzero unbounded_dbm' \<subseteq> {0..<Suc n} \<times> {0..<Suc n}"
    unfolding mtx_nonzero_def unbounded_dbm'_def unbounded_dbm_def neutral by auto

  text \<open>We need to pre-process the lemmas due to a failure of \<open>TRADE\<close>\<close>
  lemma unbounded_dbm'_bounded_1:
    "(a, b) \<in> mtx_nonzero unbounded_dbm' \<Longrightarrow> a < Suc n"
    using unbounded_dbm'_bounded by auto

  lemma unbounded_dbm'_bounded_2:
    "(a, b) \<in> mtx_nonzero unbounded_dbm' \<Longrightarrow> b < Suc n"
    using unbounded_dbm'_bounded by auto

  lemmas [sepref_fr_rules] = dbm_subset_impl.refine

  sepref_register "PR_CONST (dbm_subset n)" :: "'e DBMEntry i_mtx \<Rightarrow> 'e DBMEntry i_mtx \<Rightarrow> bool"

  lemma [def_pat_rules]:
    "dbm_subset $ n \<equiv> PR_CONST (dbm_subset n)"
    by simp

  context
    notes [id_rules] = itypeI[of "PR_CONST n" "TYPE (nat)"]
      and [sepref_import_param] = IdI[of n]
  begin

  sepref_definition unbounded_dbm_impl is
    "uncurry0 (RETURN (PR_CONST unbounded_dbm))" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a mtx_assn n"
    supply unbounded_dbm'_bounded_1[simp] unbounded_dbm'_bounded_2[simp]
    using unbounded_dbm'_bounded
    apply (subst unbounded_dbm_alt_def)
    unfolding PR_CONST_def by sepref

  sepref_definition start_inv_check_impl is
    "uncurry0 (RETURN (start_inv_check :: bool))" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    unfolding start_inv_check_def
      FW''_def[symmetric] rev_map_fold reset'_upd_def inv_of_A_def[symmetric]
    supply [sepref_fr_rules] = unbounded_dbm_impl.refine
    by sepref

  end (* End sepref setup *)

end (* End of locale *)


section \<open>Instantiation for the Concrete DBM Successor Operations\<close>

(* XXX Move *)
lemma (in Graph_Defs) Alw_ev:
  "Alw_ev \<phi> x" if "\<phi> x"
  using that unfolding Alw_ev_def by (auto simp: holds.simps)

context TA_Impl
begin

interpretation DBM_Impl n .

context
  notes [id_rules] = itypeI[of "PR_CONST n" "TYPE (nat)"]
    and [sepref_import_param] = IdI[of n]
begin

  sepref_definition E_op'_impl is
    "uncurry4 (\<lambda> l r. RETURN ooo E_op' l r)" :: "op_impl_assn"
    unfolding E_op'_def FW''_def[symmetric] reset'_upd_def inv_of_A_def[symmetric] PR_CONST_def
    by sepref

  sepref_definition E_op''_impl is
    "uncurry4 (\<lambda> l r. RETURN ooo E_op'' l r)" :: "op_impl_assn"
    unfolding E_op''_def FW''_def[symmetric] reset'_upd_def inv_of_A_def[symmetric] filter_diag_def
    by sepref

end (* End sepref setup *)

end (* TA Impl *)

subsection \<open>Correctness Theorems\<close>

context Reachability_Problem_Impl
begin

sublocale Reachability_Problem_Impl_Op
  where loc_rel = loc_rel and f = "PR_CONST E_op''" and op_impl = E_op''_impl
  unfolding PR_CONST_def by standard (rule E_op''_impl.refine)

lemma E_op_F_reachable:
  "op.F_reachable = E_op''.F_reachable" unfolding PR_CONST_def ..

lemma (in -) state_set_eq[simp]:
  "Simulation_Graphs_TA.state_set A = state_set (trans_of A)"
  unfolding Simulation_Graphs_TA.state_set_def state_set_def trans_of_def ..

lemma op_liveness_reaches_cycle_equiv:
  "(\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b) \<and> F (fst b))\<^sup>*\<^sup>* a\<^sub>0 a \<and>
   (\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b) \<and> F (fst b))\<^sup>+\<^sup>+ a b
  \<longleftrightarrow> op.liveness_pre.reaches a\<^sub>0 a \<and> op.liveness_pre.reaches1 a b" if "F l\<^sub>0"
  using that by - (rule rtranclp_tranclp_equiv[of "F o fst"], auto simp: a\<^sub>0_def)

lemma Alw_ev_impl_hnr:
  "(uncurry0
    (if F l\<^sub>0 then
      dfs_map_impl'
        (succs_P_impl' F_fun) a\<^sub>0_impl subsumes_impl (return \<circ> fst) state_copy_impl
     else return False),
   uncurry0 (SPEC (\<lambda>r. l\<^sub>0 \<in> state_set (trans_of A) \<longrightarrow>
    r \<longleftrightarrow> \<not> (\<forall>u\<^sub>0. (\<forall>c\<in>{1..n}. u\<^sub>0 c = 0) \<longrightarrow> Alw_ev (\<lambda>(l, u). \<not> F l) (l\<^sub>0, u\<^sub>0)))))
  \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding state_set_eq[symmetric]
  apply (cases "F l\<^sub>0")
  subgoal premises prems
  proof -
    define protected1 where "protected1 = E_op''.liveness_pre.reaches"
    define protected2 where "protected2 = E_op''.liveness_pre.reaches1"
    show ?thesis
      using prems Alw_ev_mc[folded a\<^sub>0_def, of F, unfolded op_liveness_reaches_cycle_equiv[OF prems]]
      apply (simp add: )
      unfolding protected1_def[symmetric] protected2_def[symmetric]
      using liveness_hnr[OF prems, to_hnr, unfolded hn_refine_def]
        apply sepref_to_hoare
      apply sep_auto
      apply (erule cons_post_rule)
      unfolding protected1_def[symmetric] protected2_def[symmetric]
      by sep_auto
  qed
  subgoal
    using Alw_ev_mc[folded a\<^sub>0_def, of F]
    apply simp
    by sepref_to_hoare sep_auto
  done

context
    fixes Q :: "'s \<Rightarrow> bool" and Q_fun
    assumes Q_fun: "(Q_fun, Q) \<in> inv_rel loc_rel states'"
    assumes no_deadlock: "\<forall>u\<^sub>0. (\<forall>c\<in>{1..n}. u\<^sub>0 c = 0) \<longrightarrow> \<not> deadlock (l\<^sub>0, u\<^sub>0)"
begin

lemma leadsto_spec_refine:
  "leadsto_spec_alt Q
  \<le> SPEC (\<lambda> r. \<not> r \<longleftrightarrow>
    (\<nexists>x. (\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b))\<^sup>*\<^sup>* (l\<^sub>0, init_dbm) x \<and>
       F (fst x) \<and>
       Q (fst x) \<and>
       (\<exists>a. (\<lambda>a b. E_op''.E_from_op a b \<and>
                   \<not> check_diag n (snd b) \<and> Q (fst b))\<^sup>*\<^sup>*
             x a \<and>
            (\<lambda>a b. E_op''.E_from_op a b \<and>
                   \<not> check_diag n (snd b) \<and> Q (fst b))\<^sup>+\<^sup>+
             a a))
    )"
proof -
  have *:"
    (\<lambda>x y. (case y of (l', M') \<Rightarrow> E_op''.E_from_op x (l', M') \<and> \<not> check_diag n M') \<and>
    \<not> (case y of (l, M) \<Rightarrow> check_diag n M))
    = (\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b))"
    by (intro ext) auto
  have **:
    "(\<lambda>x y. (case y of (l', M') \<Rightarrow> E_op''.E_from_op x (l', M') \<and> \<not> check_diag n M') \<and>
     (case y of (l, M) \<Rightarrow> Q l) \<and> \<not> (case y of (l, M) \<Rightarrow> check_diag n M))
     = (\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b) \<and> Q (fst b))"
    by (intro ext) auto
  have ***: "\<not> check_diag n b"
    if "(\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b))\<^sup>*\<^sup>* a\<^sub>0 (a, b)" for a b
    using that by cases (auto simp: a\<^sub>0_def)
  show ?thesis
    unfolding leadsto_spec_alt_def[OF Q_fun]
    unfolding PR_CONST_def a\<^sub>0_def[symmetric] by (auto dest: *** simp: * **)
  qed

lemma leadsto_impl_hnr:
  "(uncurry0
    (leadsto_impl state_copy_impl
      (succs_P_impl' Q_fun) a\<^sub>0_impl subsumes_impl (return \<circ> fst)
      succs_impl' emptiness_check_impl F_impl (Q_impl Q_fun) tracei),
   uncurry0
    (SPEC
      (\<lambda>r. l\<^sub>0 \<in> state_set (trans_of A) \<longrightarrow>
           (\<not> r) =
           (\<forall>u\<^sub>0. (\<forall>c\<in>{1..n}. u\<^sub>0 c = 0) \<longrightarrow>
                  leadsto (\<lambda>(l, u). F l) (\<lambda>(l, u). \<not> Q l) (l\<^sub>0, u\<^sub>0)))))
  \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"  
  unfolding state_set_eq[symmetric]
 using leadsto_impl_hnr[
    OF Q_fun precond_a\<^sub>0,
    FCOMP leadsto_spec_refine[THEN Id_SPEC_refine, THEN nres_relI], to_hnr, unfolded hn_refine_def]
  using leadsto_mc[OF _ no_deadlock, of F Q]
  apply (simp del: state_set_eq)
  apply sepref_to_hoare
  apply sep_auto
  apply (erule cons_post_rule)
  apply sep_auto
  done

end (* Context for leadsto predicate *)

end (* End of Reachability Problem Impl *)


section \<open>Instantiation for a Concrete Automaton\<close>

datatype result = REACHABLE | UNREACHABLE | INIT_INV_ERR

context Reachability_Problem_precompiled
begin

  sublocale Defs: Reachability_Problem_Impl_Defs
    _ _ A 0 m "\<lambda> l i. if l < n \<and> i \<le> m then k ! l ! i else 0" "PR_CONST F" .

  lemma
    "(IArray xs) !! i = xs ! i"
  by auto

  text \<open>Definition of implementation auxiliaries (later connected to the automaton via proof)\<close>
  (*
  definition
    "trans_impl l \<equiv> map (\<lambda> i. label i ((IArray trans) !! l ! i)) [0..<length (trans ! l)]"
  *)

  definition
    "trans_map \<equiv> map (\<lambda> xs. map (\<lambda> i. label i (xs ! i)) [0..<length xs]) trans"

  definition
    "trans_impl l \<equiv> (IArray trans_map) !! l"

  lemma trans_impl_alt_def:
    "l < n
    \<Longrightarrow> trans_impl l = map (\<lambda> i. label i ((IArray trans) !! l ! i)) [0..<length (trans ! l)]"
  unfolding trans_impl_def trans_map_def by (auto simp: trans_length)

  lemma state_set_n[intro, simp]:
    "state_set (trans_of A) \<subseteq> {0..<n}"
  unfolding state_set_def trans_of_def A_def T_def label_def using state_set trans_length
  by (force dest: nth_mem)

  lemma trans_impl_trans_of[intro, simp]:
    "(trans_impl, trans_of A) \<in> transition_rel Defs.states"
    using state_set_n n_gt_0 unfolding transition_rel_def trans_of_def A_def T_def
    by (fastforce simp: trans_impl_alt_def)

  definition "inv_fun l \<equiv> (IArray inv) !! l"

  lemma inv_fun_inv_of[intro, simp]:
    "(inv_fun, inv_of A) \<in> inv_rel Id Defs.states"
  using state_set_n n_gt_0 unfolding inv_rel_def inv_fun_def inv_of_def A_def I_def
  by auto

  definition "final_fun = List.member final"

  lemma final_fun_final[intro, simp]:
    "(final_fun, F) \<in> inv_rel Id Defs.states"
  using state_set_n unfolding F_def final_fun_def inv_rel_def by (auto simp: in_set_member)

  lemma start_states[intro, simp]:
    "0 \<in> Defs.states"
  proof -
    obtain g r l' where "trans ! 0 ! 0 = (g, r, l')" by (metis prod_cases3)
    with start_has_trans n_gt_0 trans_length show ?thesis
    unfolding state_set_def trans_of_def A_def T_def label_def by force
  qed

  lemma iarray_k':
    "(IArray.sub (IArray (map (IArray o map int) k)), IArray o k') \<in> inv_rel Id Defs.states"
    unfolding inv_rel_def k'_def
    apply (clarsimp simp del: upt_Suc)
    subgoal premises prems for j
    proof -
      have "j < n" using prems n_gt_0 state_set_n by fastforce
      with k_length have "length (k ! j) = m + 1" by simp
      with k_length(2) have
        "map (\<lambda>i. if i \<le> m then k ! j ! i else 0) [0..<Suc m] = map (\<lambda>i. k ! j ! i) [0..<Suc m]"
        by simp
      also have "\<dots> = k ! j" using \<open>length (k ! j) = _\<close> by (simp del: upt_Suc) (metis List.map_nth)
      also show ?thesis using \<open>j < n\<close> k_length(1)
          apply simp
          apply (subst calculation[symmetric])
        by simp
    qed
    done

  lemma trans_impl_refine_self:
    "(trans_impl, trans_impl)
      \<in> fun_rel_syn nat_rel (list_rel (Id \<times>\<^sub>r nat_rel \<times>\<^sub>r Id \<times>\<^sub>r nat_rel))"
    by auto (metis IdI list_rel_id_simp relAPP_def)

  (* XXX Room for optimization *)
  sublocale Reachability_Problem_Impl
    where A = A
    and inv_fun = inv_fun
    and F = "PR_CONST F"
    and F_fun = final_fun
    and trans_fun = trans_impl
    and trans_impl = trans_impl
    and ceiling = "IArray.sub (IArray (map (IArray o map int) k))"
    and k = "\<lambda> l i. if l < n \<and> i \<le> m then k ! l ! i else 0"
    and n = m
    and loc_rel = Id
    and l\<^sub>0 = "0::nat"
    and l\<^sub>0i = 0
    and show_state = "show"
    and show_clock = "show"
    and states' = Defs.states
    unfolding PR_CONST_def using iarray_k' trans_impl_refine_self by - (standard, fastforce+)

  subsection \<open>Correctness Theorems\<close>

  lemma F_reachable_correct:
    "op.F_reachable
    \<longleftrightarrow> (\<exists> l' u u'. conv_A A \<turnstile>' \<langle>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> l' \<in> set final)"
    using E_op''.E_from_op_reachability_check[of F_rel "PR_CONST F"] reachability_check
    unfolding E_op_F_reachable E_op''.F_reachable_def E_op''.reachable_def
    unfolding F_rel_def unfolding F_def by auto

  definition
    "reachability_checker_wl \<equiv>
      worklist_algo2_impl subsumes_impl a\<^sub>0_impl F_impl succs_impl emptiness_check_impl"

  definition
    "reachability_checker' \<equiv>
      pw_impl
        (return o fst) state_copy_impl tracei
        subsumes_impl a\<^sub>0_impl F_impl succs_impl emptiness_check_impl"

  theorem reachability_check':
    "(uncurry0 reachability_checker',
      uncurry0 (
        RETURN
          (\<exists> l' u u'. conv_A A \<turnstile>' \<langle>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> l' \<in> set final)
      )
     )
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    using pw_impl_hnr_F_reachable
    unfolding reachability_checker'_def F_reachable_correct .

  corollary reachability_checker'_hoare:
    "<emp> reachability_checker'
    <\<lambda> r. \<up>(r \<longleftrightarrow>
      (\<exists> l' u u'. conv_A A \<turnstile>' \<langle>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> l' \<in> set final))
    >\<^sub>t"
   apply (rule cons_post_rule)
   using reachability_check'[to_hnr] apply (simp add: hn_refine_def)
   by (sep_auto simp: pure_def)

  definition reachability_checker where
    "reachability_checker \<equiv> do
      {
        init_sat \<leftarrow> start_inv_check_impl;
        if init_sat then do
          { x \<leftarrow> reachability_checker';
            return (if x then REACHABLE else UNREACHABLE)
          }
        else
          return INIT_INV_ERR
      }"

  theorem reachability_check:
    "(uncurry0 reachability_checker,
       uncurry0 (
        RETURN (
          if start_inv_check
          then
            if
              \<exists> l' u u'. conv_A A \<turnstile> \<langle>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> l' \<in> set final
            then REACHABLE
            else UNREACHABLE
          else INIT_INV_ERR
        )
       )
      )
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  proof -
    define check_A where
      "check_A \<equiv> \<exists>l' u u'. conv_A A \<turnstile>' \<langle>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall>c \<in> {1..m}. u c = 0) \<and> l' \<in> set final"
    define check_B where
      "check_B \<equiv> \<exists>l' u u'. conv_A A \<turnstile> \<langle>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall>c \<in> {1..m}. u c = 0) \<and> l' \<in> set final"
    note F_reachable_equiv' =
      F_reachable_equiv
      [unfolded F_def PR_CONST_def check_A_def[symmetric] check_B_def[symmetric]]
    show ?thesis
      unfolding reachability_checker_def
      unfolding check_A_def[symmetric] check_B_def[symmetric]
      using F_reachable_equiv'
      supply reachability_check'
        [unfolded check_A_def[symmetric], to_hnr, unfolded hn_refine_def, rule_format, sep_heap_rules]
      supply start_inv_check_impl.refine
        [to_hnr, unfolded hn_refine_def, rule_format, sep_heap_rules]
      apply sepref_to_hoare
      by (sep_auto simp: pure_def)
  qed

  corollary reachability_checker_hoare':
    "<emp> reachability_checker
    <\<lambda> r.
    \<up>(r = (
      if (\<forall> u. (\<forall> c \<in> {1..m}. u c = 0) \<longrightarrow> u \<turnstile> inv_of (conv_A A) 0)
        then
          if
            \<exists> l' u u'. conv_A A \<turnstile> \<langle>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> l' \<in> set final
          then REACHABLE
          else UNREACHABLE
        else INIT_INV_ERR
      ))
    >\<^sub>t"
   unfolding start_inv_check_correct[symmetric]
   apply (rule cons_post_rule)
   using reachability_check[to_hnr] apply (simp add: hn_refine_def)
   by (sep_auto simp: pure_def)

  corollary reachability_checker_hoare:
    "<emp> reachability_checker
    <\<lambda> r.
    \<up>(
        if \<not> (\<forall> u. (\<forall> c \<in> {1..m}. u c = 0) \<longrightarrow> u \<turnstile> inv_of (conv_A A) 0)
          then r = INIT_INV_ERR
        else if \<exists> l' u u'. conv_A A \<turnstile> \<langle>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> l' \<in> set final
          then r = REACHABLE
        else r = UNREACHABLE
      )
    >\<^sub>t"
   unfolding start_inv_check_correct[symmetric]
   apply (rule cons_post_rule)
   using reachability_check[to_hnr] apply (simp add: hn_refine_def)
   by (sep_auto simp: pure_def)

  subsubsection \<open>Post-processing\<close>

  ML \<open>
    fun pull_let u t =
      let
        val t1 = abstract_over (u, t);
        val r1 = Const (@{const_name "HOL.Let"}, dummyT) $ u $ Abs ("I", dummyT, t1);
        val ct1 = Syntax.check_term @{context} r1;
        val g1 =
          Goal.prove @{context} [] [] (Logic.mk_equals (t, ct1))
          (fn {context, ...} => EqSubst.eqsubst_tac context [0] [@{thm Let_def}] 1
          THEN resolve_tac context [@{thm Pure.reflexive}] 1)
      in g1 end;

    fun get_rhs thm =
      let
        val Const ("Pure.eq", _) $ _ $ r = Thm.full_prop_of thm
      in r end;

    fun get_lhs thm =
      let
        val Const ("Pure.imp", _) $ (Const ("Pure.eq", _) $ l $ _) $ _ = Thm.full_prop_of thm
      in l end;

    fun pull_tac' u ctxt thm =
      let
        val l = get_lhs thm;
        val rewr = pull_let u l;
      in Local_Defs.unfold_tac ctxt [rewr] thm end;

    fun pull_tac u ctxt = SELECT_GOAL (pull_tac' u ctxt) 1;
  \<close>

  ML \<open>
    val th = @{thm succs_impl_def}
    val r = get_rhs th;
    val u1 = @{term "IArray.sub (IArray (map (IArray o map int) k))"};
    val rewr1 = pull_let u1 r;
    val r2 = get_rhs rewr1;
    val u2 = @{term "inv_fun"};
    val rewr2 = pull_let u2 r2;
    val r3 = get_rhs rewr2;
    val u3 = @{term "trans_impl"};
    val rewr3 = pull_let u3 r3;
    val mytac = fn ctxt => SELECT_GOAL (Local_Defs.unfold_tac ctxt [rewr1, rewr2, rewr3]) 1;
  \<close>

  lemma inv_fun_alt_def:
    "inv_fun i \<equiv> let I = (IArray inv) in I !! i"
  unfolding inv_fun_def by simp

  lemma inv_fun_rewr:
    "(let I0 = trans_impl; I = inv_fun; I1 = y in xx I0 I I1) \<equiv>
     (let I0 = trans_impl; I = (IArray inv); I' = \<lambda> i. I !! i; I1 = y in xx I0 I' I1)"
  unfolding inv_fun_def[abs_def] by simp

  lemma inv_fun_rewr':
    "(let I = inv_fun in xx I) \<equiv>
     (let I = (IArray inv); I' = \<lambda> i. I !! i in xx I')"
  unfolding inv_fun_def[abs_def] by simp

  schematic_goal succs_impl_alt_def':
    "succs_impl \<equiv> ?impl"
  unfolding succs_impl_def
   apply (tactic \<open>mytac @{context}\<close>)
   unfolding inv_fun_rewr' trans_impl_def[abs_def]
   apply (tactic \<open>pull_tac @{term "IArray trans_map"} @{context}\<close>)
  by (rule Pure.reflexive)

  schematic_goal succs_impl_alt_def:
    "succs_impl \<equiv> ?impl"
  unfolding succs_impl_def
   apply (tactic \<open>pull_tac @{term "IArray.sub (IArray (map (IArray o map int) k))"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "inv_fun"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "trans_impl"} @{context}\<close>)
   unfolding inv_fun_def[abs_def] trans_impl_def[abs_def]
   apply (tactic \<open>pull_tac @{term "IArray inv"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "IArray trans_map"} @{context}\<close>)
  by (rule Pure.reflexive)

  lemma reachability_checker'_alt_def':
    "reachability_checker' \<equiv>
      let
        key = return \<circ> fst;
        sub = subsumes_impl;
        copy = state_copy_impl;
        start = a\<^sub>0_impl;
        final = F_impl;
        succs = succs_impl;
        empty = emptiness_check_impl;
        trace = tracei
      in pw_impl key copy trace sub start final succs empty"
  unfolding reachability_checker'_def by simp

  schematic_goal reachability_checker_alt_def:
    "reachability_checker \<equiv> ?impl"
    unfolding reachability_checker_def
    unfolding reachability_checker'_alt_def' succs_impl_def
    unfolding E_op''_impl_def abstr_repair_impl_def abstra_repair_impl_def
    unfolding
      start_inv_check_impl_def unbounded_dbm_impl_def unbounded_dbm'_def
      unbounded_dbm_def
   apply (tactic \<open>pull_tac @{term "IArray.sub (IArray (map (IArray o map int) k))"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "inv_fun"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "trans_impl"} @{context}\<close>)
   unfolding inv_fun_def[abs_def] trans_impl_def[abs_def]
   apply (tactic \<open>pull_tac @{term "IArray inv"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "IArray trans_map"} @{context}\<close>)
   unfolding trans_map_def label_def
   unfolding init_dbm_impl_def a\<^sub>0_impl_def
   unfolding F_impl_def
   unfolding final_fun_def[abs_def]
   unfolding subsumes_impl_def
   unfolding emptiness_check_impl_def
   unfolding state_copy_impl_def
  by (rule Pure.reflexive)

  schematic_goal reachability_checker_alt_def:
    "reachability_checker \<equiv> ?impl"
  unfolding succs_impl_def reachability_checker_def reachability_checker'_def
   apply (tactic \<open>pull_tac @{term "IArray.sub (IArray (map (IArray o map int) k))"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "inv_fun"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "trans_impl"} @{context}\<close>)
   unfolding inv_fun_def[abs_def] trans_impl_def[abs_def]
   apply (tactic \<open>pull_tac @{term "IArray inv"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "IArray trans_map"} @{context}\<close>)
  oops

end (* End of locale *)

subsection \<open>Check preconditions\<close>
context Reachability_Problem_precompiled_defs
begin

  abbreviation
    "check_nat_subs \<equiv> \<forall> l < n. \<forall> (_, d) \<in> clkp_set' l. d \<ge> 0"

  lemma check_nat_subs:
    "check_nat_subs \<longleftrightarrow> (\<forall> l < n. snd ` clkp_set' l \<subseteq> \<nat>)"
  unfolding Nats_def apply safe
  subgoal for _ _ _ b using rangeI[of int "nat b"] by (auto 4 3)
  by (auto 4 3)

  definition
    "check_pre \<equiv>
      length inv = n \<and> length trans = n
      \<and> length k = n \<and> (\<forall> l \<in> set k. length l = m + 1)
      \<and> m > 0 \<and> n > 0 \<and> trans ! 0 \<noteq> []
      \<and> (\<forall> l < n. \<forall> (c, d) \<in> clkp_set' l. k ! l ! c \<ge> nat d)
      \<and> (\<forall> l < n. k ! l ! 0 = 0) \<and> (\<forall> l < n. \<forall> c \<in> {1..m}. k ! l ! c \<ge> 0)
      \<and> check_nat_subs \<and> clk_set' = {1..m}
      \<and> (\<forall> xs \<in> set trans. \<forall> (_, _, l) \<in> set xs. l < n)"

  (* Can be optimized with better enumeration *)
  abbreviation
    "check_ceiling \<equiv>
      \<forall> l < n. \<forall> (_, r, l') \<in> set (trans ! l). \<forall> c \<le> m. c \<notin> set r \<longrightarrow> k ! l ! c \<ge> k ! l' ! c"

  lemma finite_clkp_set'[intro, simp]:
    "finite (clkp_set' l)"
  unfolding clkp_set'_def by auto

  lemma check_axioms:
    "Reachability_Problem_precompiled n m k inv trans \<longleftrightarrow> check_pre \<and> check_ceiling"
  unfolding Reachability_Problem_precompiled_def check_pre_def check_nat_subs by auto

end

section \<open>Executable Checker\<close>

lemmas Reachability_Problem_precompiled_defs.check_axioms[code]

lemmas Reachability_Problem_precompiled_defs.clkp_set'_def[code]

lemmas Reachability_Problem_precompiled_defs.clk_set'_def[code]

lemmas Reachability_Problem_precompiled_defs.check_pre_def[code]

lemmas Show_State_Defs.tracei_def[code]

export_code Reachability_Problem_precompiled in SML module_name Test

concrete_definition succs_impl' uses Reachability_Problem_precompiled.succs_impl_alt_def

concrete_definition reachability_checker_impl
  uses Reachability_Problem_precompiled.reachability_checker_alt_def

export_code reachability_checker_impl in SML_imp module_name TA

definition [code]:
  "check_and_verify n m k I T final \<equiv>
    if Reachability_Problem_precompiled n m k I T
    then reachability_checker_impl m k I T final \<bind> (\<lambda> x. return (Some x))
    else return None"

lemmas [sep_heap_rules] = Reachability_Problem_precompiled.reachability_checker_hoare'

theorem reachability_check:
  "(uncurry0 (check_and_verify n m k I T final),
    uncurry0 (
       RETURN (
        if (Reachability_Problem_precompiled n m k I T)
        then Some (
          if (\<forall> u. (\<forall> c \<in> {1..m}. u c = 0)
              \<longrightarrow> u \<turnstile> inv_of (conv_A (Reachability_Problem_precompiled_defs.A n I T)) 0)
          then
            if
              \<exists> l' u u'.
              (conv_A (Reachability_Problem_precompiled_defs.A n I T)) \<turnstile> \<langle>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>
              \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> l' \<in> set final
            then REACHABLE
            else UNREACHABLE
          else INIT_INV_ERR
          )
        else None
       )
    )
   )
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
proof -
  define inv_pre where
    "inv_pre \<equiv>
    (\<forall> u. (\<forall> c \<in> {1..m}. u c = 0) \<longrightarrow>
     u \<turnstile> inv_of (conv_A (Reachability_Problem_precompiled_defs.A n I T)) 0)"
  define reach_check where
    "reach_check =
    (\<exists> l' u u'.
      (conv_A (Reachability_Problem_precompiled_defs.A n I T)) \<turnstile>
      \<langle>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> l' \<in> set final)"
  note [sep_heap_rules] =
    Reachability_Problem_precompiled.reachability_checker_hoare'
    [of n m k I T final,
      unfolded inv_pre_def[symmetric],
      unfolded reach_check_def[symmetric]
      ]
  show ?thesis
    unfolding inv_pre_def[symmetric] reach_check_def[symmetric]
    apply sepref_to_hoare
    unfolding check_and_verify_def
    by (sep_auto simp: reachability_checker_impl.refine[symmetric])
qed

export_code open check_and_verify checking SML

end (* End of theory *)

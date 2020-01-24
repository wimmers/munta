theory Unreachability_Certification
  imports
    TA_Impl.Worklist_Locales
    "../Simulation_Graphs_Certification"
    TA_Impl.Unified_PW_Impl
    TA_Impl.Leadsto_Impl
    TA_Library.Printing
    TA_Library.Imperative_Loops
    TA_Library.Trace_Timing
    Unreachability_Misc
begin



lemma monadic_list_all_nofailI:
  assumes "\<And> x. x \<in> set xs \<Longrightarrow> nofail (f x)"
  shows "nofail (monadic_list_all f xs)"
  sorry

lemma monadic_list_ex_nofailI:
  assumes "\<And> x. x \<in> set xs \<Longrightarrow> nofail (f x)"
  shows "nofail (monadic_list_ex f xs)"
  sorry

lemma no_fail_RES_bindI:
  assumes "\<And>x. x \<in> S \<Longrightarrow> nofail (f x)" "S \<noteq> {}"
  shows "nofail (RES S \<bind> f)"
  sorry



context
  fixes K :: "'k \<Rightarrow> ('ki :: {heap}) \<Rightarrow> assn"
  assumes pure_K: "is_pure K"
  assumes left_unique_K: "IS_LEFT_UNIQUE (the_pure K)"
  assumes right_unique_K: "IS_RIGHT_UNIQUE (the_pure K)"
begin

lemma pure_equality_impl:
  "(uncurry (return oo (=)), uncurry (RETURN oo (=))) \<in> (K\<^sup>k *\<^sub>a K\<^sup>k) \<rightarrow>\<^sub>a bool_assn"
proof -
  have 1: "K = pure (the_pure K)"
    using pure_K by auto
  have [dest]: "a = b" if "(bi, b) \<in> the_pure K" "(bi, a) \<in> the_pure K" for bi a b
    using that right_unique_K by (elim single_valuedD) auto
  have [dest]: "a = b" if "(a, bi) \<in> the_pure K" "(b, bi) \<in> the_pure K" for bi a b
    using that left_unique_K unfolding IS_LEFT_UNIQUE_def by (elim single_valuedD) auto
  show ?thesis
    by (subst 1, subst (2) 1, sepref_to_hoare, sep_auto)
qed

definition
  "is_member x L \<equiv> do {
    xs \<leftarrow> SPEC (\<lambda>xs. set xs = L);
    monadic_list_ex (\<lambda>y. RETURN (y = x)) xs
  }"

lemma is_member_refine:
  "is_member x L \<le> mop_set_member x L"
  unfolding mop_set_member_alt is_member_def
  by (refine_vcg monadic_list_ex_rule) (auto simp: list_ex_iff)

lemma is_member_correct:
  "(uncurry is_member, uncurry (RETURN \<circ>\<circ> op_set_member)) \<in> Id \<times>\<^sub>r Id \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using is_member_refine by (force simp: pw_le_iff pw_nres_rel_iff)

lemmas [sepref_fr_rules] = lso_id_hnr

sepref_definition is_member_impl is
  "uncurry is_member" :: "K\<^sup>k *\<^sub>a (lso_assn K)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  supply [sepref_fr_rules] = pure_equality_impl
  supply [safe_constraint_rules] = pure_K left_unique_K right_unique_K
  unfolding is_member_def monadic_list_ex_def list_of_set_def[symmetric] by sepref

lemmas op_set_member_lso_hnr = is_member_impl.refine[FCOMP is_member_correct]

end




paragraph \<open>Concrete Implementations\<close>

context Reachability_Impl
begin

definition
  "check_invariant' L' M' \<equiv> do {
  monadic_list_all (\<lambda>l.
  do {
    case op_map_lookup l M' of None \<Rightarrow> RETURN True  | Some xs \<Rightarrow> do {
      let succs = PR_CONST succs l xs;
      monadic_list_all (\<lambda>(l', xs). do {
        xs \<leftarrow> SPEC (\<lambda>xs'. set xs' = xs);
        if xs = [] then RETURN True
        else do {
          case op_map_lookup l' M' of None \<Rightarrow> RETURN False | Some ys \<Rightarrow> do {
            ys \<leftarrow> SPEC (\<lambda>xs.  set xs  = ys);
            monadic_list_all (\<lambda>x'.
              monadic_list_ex (\<lambda>y. RETURN (PR_CONST less_eq x' y)) ys
            ) xs
          }
        }
      }) succs
    }
  }) L'
}"

lemma succs_listD:
  assumes "(l', S') \<in> set (succs l S)" "finite S"
  shows "\<exists> xs. set xs = S'"
  using assms succs_finite by (force intro!: finite_list)

lemma check_invariant'_refine:
  "check_invariant' L_part M \<le> check_invariant L_part" if "L = dom M" "set L_part \<subseteq> L"
  unfolding check_invariant_def check_invariant'_def
  unfolding PR_CONST_def
  apply refine_mono
  apply (clarsimp split: option.splits simp: succs_empty)
  apply refine_mono
  apply (clarsimp split: option.splits)
  apply safe
  subgoal
    by refine_mono (auto simp: bind_RES monadic_list_all_False dest: M_listD)
  subgoal
    apply refine_mono
    apply clarsimp
    apply refine_mono
    apply clarsimp
    subgoal for xs1 xs2
      using monadic_list_all_list_ex_is_RETURN[of "\<lambda> x y. less_eq x y" xs2 xs1]
      by (auto simp: bind_RES \<open>L = dom M\<close>)
    done
  done

lemmas [safe_constraint_rules] = pure_K left_unique_K right_unique_K

lemmas [sepref_fr_rules] = lso_id_hnr

sepref_register
  "PR_CONST L" "list_of_set" "PR_CONST P'" "PR_CONST F" "PR_CONST succs" "PR_CONST less_eq"
  "PR_CONST M" :: "('k, 'b set) i_map"

lemma [sepref_import_param]: "(id, id) \<in> (Id :: (bool \<times> bool) set) \<rightarrow> Id"
  by simp

(*
lemmas [sepref_fr_rules] = M_impl
*)

sepref_definition check_prop_impl_wrong is
  "uncurry check_prop'" :: "(lso_assn K)\<^sup>k *\<^sub>a (hm.hms_assn' K (lso_assn A))\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding check_prop'_alt_def list_of_set_def[symmetric]
  unfolding monadic_list_all_def
  apply sepref_dbg_keep
  oops

sepref_decl_impl "map_lookup":
  copy_list_lso_assn_refine[OF copyi, THEN hms_hm.hms_lookup_hnr]
  uses op_map_lookup.fref[where V = Id] .

abbreviation "table_assn \<equiv> hm.hms_assn' K (lso_assn A)"

sepref_thm check_prop_impl is
  "uncurry (PR_CONST check_prop')" :: "(lso_assn K)\<^sup>k *\<^sub>a table_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding PR_CONST_def
  unfolding check_prop'_def list_of_set_def[symmetric]
  unfolding monadic_list_all_def
  by sepref

concrete_definition (in -) check_prop_impl
  uses Reachability_Impl.check_prop_impl.refine_raw is "(uncurry ?f,_)\<in>_"

sepref_thm check_final_impl is
  "uncurry (PR_CONST check_final')" :: "(lso_assn K)\<^sup>k *\<^sub>a table_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding PR_CONST_def
  unfolding check_final'_def list_of_set_def[symmetric]
  unfolding monadic_list_all_def
  by sepref

concrete_definition (in -) check_final_impl
  uses Reachability_Impl.check_final_impl.refine_raw is "(uncurry ?f,_)\<in>_"

lemma K_equality[sepref_fr_rules]:
  "(uncurry (return oo (=)), uncurry (RETURN oo (=))) \<in> (K\<^sup>k *\<^sub>a K\<^sup>k) \<rightarrow>\<^sub>a bool_assn"
proof -
  have 1: "K = pure (the_pure K)"
    using pure_K by auto
  have [dest]: "a = b" if "(bi, b) \<in> the_pure K" "(bi, a) \<in> the_pure K" for bi a b
    using that right_unique_K by (elim single_valuedD) auto
  have [dest]: "a = b" if "(a, bi) \<in> the_pure K" "(b, bi) \<in> the_pure K" for bi a b
    using that left_unique_K unfolding IS_LEFT_UNIQUE_def by (elim single_valuedD) auto
  show ?thesis
    by (subst 1, subst (2) 1, sepref_to_hoare, sep_auto)
qed

sepref_definition is_K_eq_impl is
  "uncurry (RETURN oo (=))" :: "(K\<^sup>k *\<^sub>a K\<^sup>k) \<rightarrow>\<^sub>a bool_assn"
  unfolding is_member_def monadic_list_ex_def list_of_set_def[symmetric] by sepref

lemmas [sepref_fr_rules] = op_set_member_lso_hnr[OF pure_K left_unique_K right_unique_K]

sepref_definition check_invariant_impl is
  "uncurry (PR_CONST check_invariant')" :: "(list_assn K)\<^sup>k *\<^sub>a table_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding PR_CONST_def
  unfolding check_invariant'_def list_of_set_def[symmetric]
  unfolding monadic_list_all_def monadic_list_ex_def
  by sepref

lemma check_invariant_impl_ht:
  "<table_assn M bi * list_assn K a ai>
    check_invariant_impl ai bi
  <\<lambda>r. table_assn M bi * list_assn K a ai * \<up>(r \<longrightarrow> check_invariant_spec (set a))>\<^sub>t"
  if "nofail (check_invariant' a M)" "L = dom M" "set a \<subseteq> L" "\<forall>l \<in> L. \<forall>s \<in> the (M l). P (l, s)"
  apply (rule cons_post_rule)
   apply (rule check_invariant_impl.refine[
        to_hnr, unfolded hn_refine_def hn_ctxt_def, simplified, rule_format])
  subgoal
    by (rule that)
  using that
  apply sep_auto
   apply (drule order.trans, rule order.trans[OF check_invariant'_refine check_invariant_correct])
  apply (sep_auto simp: pure_def split: option.splits)+
  done

(*
lemma check_invariant'_correct:
  "(uncurry0 check_invariant', uncurry0 (PR_CONST check_invariant)) \<in> Id \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using check_invariant'_refine by (auto simp: pw_le_iff pw_nres_rel_iff)

lemmas check_invariant_impl_refine = check_invariant_impl.refine_raw[FCOMP check_invariant'_correct]

concrete_definition (in -) check_invariant_impl
  uses Reachability_Impl.check_invariant_impl_refine is "(uncurry0 ?f,_)\<in>_"
*)

definition
  "check_all_pre' L' M' \<equiv> do {
  b1 \<leftarrow> RETURN (PR_CONST l\<^sub>0 \<in> L');
  b2 \<leftarrow> RETURN (PR_CONST P' (PR_CONST l\<^sub>0, PR_CONST s\<^sub>0));
  let S = op_map_lookup (PR_CONST l\<^sub>0) M';
  case S of None \<Rightarrow> RETURN False | Some S \<Rightarrow> do {
    xs \<leftarrow> SPEC (\<lambda>xs. set xs = S);
    b3 \<leftarrow> monadic_list_ex (\<lambda>s. RETURN (PR_CONST less_eq (PR_CONST s\<^sub>0) s)) xs;
    b4 \<leftarrow> PR_CONST check_prop' L' M';
    PRINT_CHECK STR ''Start state is in state list'' b1;
    PRINT_CHECK STR ''Start state fulfills property'' b2;
    PRINT_CHECK STR ''Start state is subsumed'' b3;
    PRINT_CHECK STR ''Check property'' b4;
    RETURN (b1 \<and> b2 \<and> b3 \<and> b4)
    }
  }
"

definition
  "check_all' L' M' \<equiv> do {
  b \<leftarrow> check_all_pre' L' M';
  if b
  then do {
    r \<leftarrow> RETURN (check_invariant_spec L');
    PRINT_CHECK STR ''State set invariant check'' r;
    RETURN r
  }
  else RETURN False
  }
"

definition check_init' where
  "check_init' S \<equiv>
  case S of None \<Rightarrow> RETURN False | Some S \<Rightarrow> do {
    xs \<leftarrow> SPEC (\<lambda>xs. set xs = S);
    monadic_list_ex (\<lambda>s. RETURN (PR_CONST less_eq (PR_CONST s\<^sub>0) s)) xs
  }
"

lemma check_all_pre'_refine:
  "check_all_pre' L M \<le> check_all_pre l\<^sub>0 s\<^sub>0"
  unfolding check_all_pre_def check_all_pre'_def PR_CONST_def Let_def
  using check_prop_gt_SUCCEED
  apply (cases "op_map_lookup l\<^sub>0 M"; simp add: bind_RES)
   apply (cases "check_prop P'")
    apply (clarsimp_all intro: less_eq_Sup simp: bind_RES check_prop_alt_def)
  apply (rule less_eq_Sup)
  subgoal for a v
    apply clarsimp
    apply (rule Sup_least)
    apply clarsimp
    supply [refine_mono] = monadic_list_ex_mono monadic_list_ex_RETURN_mono
    apply refine_mono
    apply (simp add: PRINT_CHECK_def)
    done
  subgoal
    by (auto dest: M_listD)
  done

lemma check_all'_refine:
  "check_all' L M \<le> check_all"
  supply [refine_mono] = check_all_pre'_refine
  unfolding check_all_def check_all'_def PRINT_CHECK_def by refine_mono auto

(*
lemma check_all'_correct:
  "(uncurry0 check_all', uncurry0 (PR_CONST check_all)) \<in> Id \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using check_all'_refine by (auto simp: pw_le_iff pw_nres_rel_iff)
*)
term check_invariant'
sepref_register
  "PR_CONST check_invariant'" :: "'k list \<Rightarrow> ('k, 'b set) i_map \<Rightarrow> bool nres"
  "PR_CONST check_all_pre'" :: "'k set \<Rightarrow> ('k, 'b set) i_map \<Rightarrow> bool nres"
  (* check_prop: "PR_CONST (check_prop P')" *)
  "PR_CONST check_prop'" :: "'k set \<Rightarrow> ('k, 'b set) i_map \<Rightarrow> bool nres"
  "PR_CONST check_all'" :: "'k set \<Rightarrow> ('k, 'b set) i_map \<Rightarrow> bool nres"
  "PR_CONST check_final'" :: "'k set \<Rightarrow> ('k, 'b set) i_map \<Rightarrow> bool nres"
  "PR_CONST check_init"
  "PR_CONST l\<^sub>0" "PR_CONST s\<^sub>0"

sepref_definition check_init_impl is
  "check_init'" :: "(option_assn (lso_assn A))\<^sup>d \<rightarrow>\<^sub>a bool_assn"
  unfolding check_init'_def list_of_set_def[symmetric]
  unfolding monadic_list_all_def monadic_list_ex_def
  by sepref

definition
  "L_member L' \<equiv> PR_CONST l\<^sub>0 \<in> L'"

sepref_thm L_member_impl is
  "RETURN o PR_CONST L_member" :: "(lso_assn K)\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding PR_CONST_def unfolding L_member_def by sepref

lemma L_member_fold:
  "PR_CONST l\<^sub>0 \<in> L' \<equiv> PR_CONST L_member L'"
  unfolding L_member_def PR_CONST_def .

(*
lemmas [sepref_fr_rules] =
  check_prop_impl.refine[OF Reachability_Impl_axioms]
  check_invariant_impl.refine[OF Reachability_Impl_axioms]
*)

definition
  "lookup (M' :: 'k \<Rightarrow> 'a set option) = op_map_lookup (PR_CONST l\<^sub>0) M'"

lemma looukp_fold:
  "op_map_lookup (PR_CONST l\<^sub>0) = PR_CONST lookup"
  unfolding lookup_def PR_CONST_def ..

sepref_register L_member lookup :: "('k, 'b set) i_map \<Rightarrow> 'b set option"

definition check2 where
  "check2 b = PR_CONST check_init' (PR_CONST lookup b)"

lemma check2_fold:
  "PR_CONST check_init' (PR_CONST lookup b) = PR_CONST check2 b"
  unfolding check2_def PR_CONST_def ..

sepref_register check2 :: "('k, 'b set) i_map \<Rightarrow> bool nres"

definition check1 where
  "check1 = PR_CONST P' (PR_CONST l\<^sub>0, PR_CONST s\<^sub>0)"

lemma check1_fold:
  "PR_CONST check1 = PR_CONST P' (PR_CONST l\<^sub>0, PR_CONST s\<^sub>0)"
  unfolding check1_def PR_CONST_def ..

sepref_register check1

sepref_thm check1_impl is
  "uncurry0 (RETURN (PR_CONST check1))" :: "id_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding PR_CONST_def unfolding check1_def by sepref

sepref_thm check2_impl is
  "PR_CONST check2" :: "table_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding PR_CONST_def
  unfolding check2_def
  unfolding PR_CONST_def
  unfolding check_init'_def lookup_def
  unfolding list_of_set_def[symmetric]
  unfolding monadic_list_all_def monadic_list_ex_def
  by sepref

lemmas [sepref_fr_rules] =
  L_member_impl.refine_raw
  check1_impl.refine_raw
  check2_impl.refine_raw
  check_prop_impl.refine_raw
  (* check_invariant_impl.refine_raw *)

context
  fixes splitter :: "'k list \<Rightarrow> 'k list list" and splitteri :: "'ki list \<Rightarrow> 'ki list list"
  (* assumes full_split: "set xs = (\<Union>xs \<in> set (splitteri xs). set xs)" *)
  assumes full_split: "set xs = (\<Union>xs \<in> set (splitter xs). set xs)"
(*
      and same_split:
      "(return o splitteri, RETURN o splitter) \<in> (list_assn K)\<^sup>k \<rightarrow>\<^sub>a list_assn (list_assn K)"
*)
  and same_split:
    "\<And>L Li. list_assn (list_assn K) (splitter L) (splitteri Li) = list_assn K L Li"
begin

definition
  "check_invariant_all_impl L' M' \<equiv> do {
    bs \<leftarrow> parallel_fold_map (\<lambda>L. check_invariant_impl L M') (splitteri L');
    return (list_all id bs)
  }"

definition
  "split_spec \<equiv> \<lambda>L M. RETURN (list_all (\<lambda>x. RETURN True \<le> check_invariant' x M) (splitter L))"

lemma check_invariant_all_impl_refine:
  "(uncurry check_invariant_all_impl, uncurry (PR_CONST split_spec))
  \<in> (list_assn K)\<^sup>k *\<^sub>a table_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding split_spec_def PR_CONST_def
  apply sepref_to_hoare
  apply sep_auto
  subgoal for M Mi L Li
  unfolding check_invariant_all_impl_def parallel_fold_map_def
  apply sep_auto
   apply (rule Hoare_Triple.cons_pre_rule[rotated])
    apply (rule fold_map_ht2[
        where Q = "\<lambda>L r. RETURN r \<le> check_invariant' L M"
          and R = "list_assn K" and A = "table_assn M Mi" and xs = "splitter L"
          ])
    apply (rule Hoare_Triple.cons_post_rule)
(* find_theorems intro does not find it *)
  apply (rule frame_rule)
     apply (rule check_invariant_impl.refine[to_hnr, unfolded hn_refine_def hn_ctxt_def, simplified, rule_format])
  subgoal
    unfolding check_invariant'_def
    apply (intro monadic_list_all_nofailI)
    apply (clarsimp split: option.splits)
    apply (intro monadic_list_all_nofailI)
    apply (clarsimp split: prod.splits)
    apply (rule no_fail_RES_bindI)
     apply (clarsimp split: option.splits)
     apply (rule no_fail_RES_bindI)
apply (intro monadic_list_all_nofailI monadic_list_ex_nofailI)
      apply auto
(* missing finiteness of table *)
    sorry
    apply (sep_auto simp: pure_def; fail)
  subgoal
    unfolding same_split by solve_entails
  apply sep_auto
  subgoal
    unfolding list_all_length list_all2_conv_all_nth by auto
  subgoal for x
    unfolding list_all_length
    unfolding list_all2_conv_all_nth
    apply auto
    apply (elim allE impE)
       apply assumption+
    subgoal for n
      apply (cases "x ! n")
       apply auto
      sorry
    done
  subgoal
    unfolding same_split by solve_entails
  done
  done

sepref_definition check_all_pre_impl is
  "uncurry (PR_CONST check_all_pre')" :: "(lso_assn K)\<^sup>k *\<^sub>a table_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding PR_CONST_def
  unfolding check_all_pre'_def list_of_set_def[symmetric]
  unfolding monadic_list_all_def monadic_list_ex_def
  by sepref

lemma check_all_pre_impl_ht:
  "<table_assn b bi * lso_assn K a ai>
    check_all_pre_impl ai bi
   <\<lambda>r. table_assn b bi * lso_assn K a ai * \<up> (RETURN r \<le> check_all_pre' a b)>\<^sub>t"
  if "nofail (check_all_pre' a b)"
  apply (rule cons_post_rule)
   apply (rule check_all_pre_impl.refine[to_hnr, unfolded hn_refine_def hn_ctxt_def, simplified, rule_format])
  subgoal
    by (rule that)
  apply (sep_auto simp: pure_def)
  done

definition
  "check_all'' L' M' \<equiv> do {
  b \<leftarrow> PR_CONST check_all_pre' L' M';
  if b
  then do {
    xs \<leftarrow> SPEC (\<lambda>xs. set xs = L');
    r \<leftarrow> PR_CONST split_spec xs M';
    PRINT_CHECK STR ''State set invariant check'' r;
    RETURN r
  }
  else RETURN False
  }
"

sepref_register split_spec :: "'k list \<Rightarrow> (('k, 'b set) i_map) \<Rightarrow> bool nres"

lemmas [sepref_fr_rules] =
  check_all_pre_impl.refine_raw
  check_invariant_all_impl_refine

sepref_thm check_all_impl is
  "uncurry (PR_CONST check_all'')" :: "(lso_assn K)\<^sup>k *\<^sub>a table_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding PR_CONST_def
  unfolding check_all''_def list_of_set_def[symmetric]
  by sepref

lemma [refine_mono]:
  "split_spec L' M \<le> RETURN (check_invariant_spec (set L'))" if "dom M = L" "set L' \<subseteq> L"
  sorry

lemma check_all''_refine:
  "check_all'' L' M \<le> check_all' L' M" if "dom M = L" "L' \<subseteq> L"
  using that
  unfolding check_all''_def check_all'_def PR_CONST_def
  apply refine_mono
  sorry

sepref_thm check_all_impl is
  "uncurry (PR_CONST check_all')" :: "(lso_assn K)\<^sup>k *\<^sub>a table_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding PR_CONST_def
  unfolding check_all'_def list_of_set_def[symmetric]
  unfolding monadic_list_all_def monadic_list_ex_def
  oops

sepref_thm check_all_impl is
  "uncurry (PR_CONST check_all')" :: "(lso_assn K)\<^sup>k *\<^sub>a table_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding PR_CONST_def
  unfolding check_all'_def check_all_pre'_def list_of_set_def[symmetric]
  unfolding monadic_list_all_def monadic_list_ex_def
  oops

(*
lemmas check_all_impl_refine = check_all_impl.refine_raw[FCOMP check_all'_correct]
*)

(*
concrete_definition (in -) check_all_impl
  uses Reachability_Impl.check_all_impl_refine is "(uncurry0 ?f,_)\<in>_"
*)

(*
thm check_all_impl.refine

lemmas [sepref_fr_rules] =
  check_final_impl.refine[OF Reachability_Impl_axioms]
  check_all_impl.refine[OF Reachability_Impl_axioms]
*)

lemma certify_unreachable_alt_def:
  "certify_unreachable \<equiv> do {
  b1 \<leftarrow> PR_CONST check_all;
  b2 \<leftarrow> PR_CONST check_final;
  RETURN (b1 \<and> b2)
  }"
  unfolding certify_unreachable_def PR_CONST_def .

definition certify_unreachable' where
  "certify_unreachable' L' M' \<equiv> do {
  START_TIMER ();
  b1 \<leftarrow> PR_CONST check_all'' L' M';
  SAVE_TIME STR ''Time for state space invariant check'';
  START_TIMER ();
  b2 \<leftarrow> PR_CONST check_final' L' M';
  SAVE_TIME STR ''Time to check final state predicate'';
  PRINT_CHECK STR ''All check: '' b1;
  PRINT_CHECK STR ''Target property check: '' b2;
  RETURN (b1 \<and> b2)
  }"

lemma certify_unreachable'_refine:
  "certify_unreachable' L M \<le> certify_unreachable" if "L = dom M"
  supply [refine_mono] =
    order.trans[OF check_all''_refine[OF that[symmetric] subset_refl] check_all'_refine]
  unfolding certify_unreachable'_def certify_unreachable_def PR_CONST_def check_final_alt_def
  unfolding PRINT_CHECK_def START_TIMER_def SAVE_TIME_def
  by simp refine_mono

sepref_register
  "PR_CONST check_all''" :: "'k set \<Rightarrow> (('k, 'b set) i_map) \<Rightarrow> bool nres"
  "PR_CONST check_final"

lemmas [sepref_fr_rules] =
  check_all_impl.refine_raw
  check_final_impl.refine_raw

sepref_thm certify_unreachable_impl' is
  "uncurry (PR_CONST certify_unreachable')" :: "(lso_assn K)\<^sup>k *\<^sub>a table_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding PR_CONST_def unfolding certify_unreachable'_def
  by sepref

lemma certify_unreachable_correct':
  "(uncurry0 (certify_unreachable' L M), uncurry0 (SPEC (\<lambda>r. r \<longrightarrow> (\<nexists>s'. E\<^sup>*\<^sup>* (l\<^sub>0, s\<^sub>0) s' \<and> F s'))))
    \<in> Id \<rightarrow> \<langle>bool_rel\<rangle>nres_rel" if "L = dom M"
  using certify_unreachable_correct' certify_unreachable'_refine[OF that]
  by (clarsimp simp: pw_le_iff pw_nres_rel_iff) fast

lemmas certify_unreachable_impl'_refine =
  certify_unreachable_impl'.refine_raw[
    unfolded is_member_impl_def[OF pure_K left_unique_K right_unique_K]
      check_invariant_all_impl_def check_invariant_impl_def
  ]


definition certify_unreachable_new where
  "certify_unreachable_new L_list M_table \<equiv> let
  _ = start_timer ();
  b1 = run_heap (do {M' \<leftarrow> M_table; check_all_pre_impl L_list M'});
  _ = save_time STR ''Time for checking basic preconditions'';
  _ = start_timer ();
  xs = run_map_heap (\<lambda>Li. do {M' \<leftarrow> M_table; check_invariant_impl Li M'}) (splitteri L_list);
  b2 = list_all id xs;
  _ = save_time STR ''Time for state space invariant check'';
  _ = print_check STR ''State set invariant check'' b2;
  _ = start_timer ();
  b3 = run_heap (do {M' \<leftarrow> M_table; check_final_impl Fi copyi L_list M'});
  _ = save_time STR ''Time to check final state predicate'';
  _ = print_check STR ''All check: '' (b1 \<and> b2);
  _ = print_check STR ''Target property check: '' b3
  in b1 \<and> b2 \<and> b3"

lemmas certify_unreachable_new_alt_def =
  certify_unreachable_new_def[unfolded
    check_invariant_impl_def
    check_all_pre_impl_def
    is_member_impl_def[OF pure_K left_unique_K right_unique_K]
    ]

end (* Splitter *)

concrete_definition (in -) check_all_impl
  uses Reachability_Impl.check_all_impl.refine_raw is "(uncurry ?f,_)\<in>_"

concrete_definition (in -) certify_unreachable_impl_inner
  uses Reachability_Impl.certify_unreachable_impl'_refine is "(uncurry ?f,_)\<in>_"

lemmas certify_unreachable'_impl_hnr =
  certify_unreachable_impl_inner.refine[OF Reachability_Impl_axioms]

(* lemmas certify_unreachable_impl_refine =
  certify_unreachable_impl.refine_raw[
    unfolded PR_CONST_def is_member_impl_def[OF pure_K left_unique_K right_unique_K]
  ]

concrete_definition (in -) certify_unreachable_impl
  uses Reachability_Impl.certify_unreachable_impl_refine is "(uncurry ?f,_)\<in>_"
 *)

concrete_definition (in -) certify_unreachable_impl2
  uses Reachability_Impl.certify_unreachable_new_alt_def

context
  fixes L_list and M_table
  assumes L_impl[sepref_fr_rules]:
    "(uncurry0 (return L_list), uncurry0 (RETURN (PR_CONST L))) \<in> id_assn\<^sup>k \<rightarrow>\<^sub>a lso_assn K"
  assumes M_impl[sepref_fr_rules]:
    "(uncurry0 M_table, uncurry0 (RETURN (PR_CONST M))) \<in> id_assn\<^sup>k \<rightarrow>\<^sub>a hm.hms_assn' K (lso_assn A)"
  fixes splitter :: "'k list \<Rightarrow> 'k list list" and splitteri :: "'ki list \<Rightarrow> 'ki list list"
  assumes full_split: "set xs = (\<Union>xs \<in> set (splitter xs). set xs)"
      and same_split:
    "\<And>L Li. list_assn (list_assn K) (splitter L) (splitteri Li) = list_assn K L Li"
begin

lemmas [sepref_fr_rules] = certify_unreachable'_impl_hnr[OF full_split same_split]

sepref_register
  "certify_unreachable' splitter" :: "'k set \<Rightarrow> ('k, 'b set) i_map \<Rightarrow> bool nres"

sepref_thm certify_unreachable_impl is
  "uncurry0 (PR_CONST (certify_unreachable' splitter) (PR_CONST L) (PR_CONST M))"
  :: "id_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  by sepref_dbg_keep

lemmas certify_unreachable_impl_refine =
  certify_unreachable_impl.refine_raw[
    unfolded PR_CONST_def is_member_impl_def[OF pure_K left_unique_K right_unique_K],
    FCOMP certify_unreachable_correct'[OF full_split same_split]
  ]

lemma certify_unreachable_new_correct:
  assumes "dom M = L"
  shows "certify_unreachable_new splitteri L_list M_table \<longrightarrow> (\<nexists>s'. E\<^sup>*\<^sup>* (l\<^sub>0, s\<^sub>0) s' \<and> F s')"
proof -
  have [sep_heap_rules]: "<emp> M_table <\<lambda>r. hm.hms_assn' K (lso_assn A) M r>\<^sub>t"
    by (sep_auto simp: pure_def heap: M_impl[to_hnr, unfolded hn_refine_def, simplified])
  have true_emp: "true = emp * true"
    by simp
  have *: "emp \<Longrightarrow>\<^sub>A lso_assn K L L_list * true"
    using L_impl[to_hnr, unfolded hn_refine_def, simplified]
    apply -
    apply (drule return_htD)
    apply (erule ent_trans)
    apply (sep_auto simp: pure_def)
    done
  then have *: "true \<Longrightarrow>\<^sub>A lso_assn K L L_list * true"
    by (subst true_emp) (erule ent_true_drop)
  have check_all_pre'_refine: "check_all_pre' L M \<le> RETURN (check_all_pre_spec l\<^sub>0 s\<^sub>0)"
    by (blast intro: check_all_pre_correct check_all_pre'_refine order.trans)
  have list_assn_K_eq: "list_assn K = pure (\<langle>the_pure K\<rangle>list_rel)"
    using pure_K by (simp add: list_assn_pure_conv[symmetric])
  have 1: "
    <emp>
      do {M' \<leftarrow> M_table; check_all_pre_impl L_list M'}
    <\<lambda>r. \<up> (r \<longrightarrow> check_all_pre_spec l\<^sub>0 s\<^sub>0)>\<^sub>t"
    apply sep_auto
    subgoal for Mi
      apply (rule cons_rule[rotated 2])
        apply (rule frame_rule[where R = true])
        apply (rule check_all_pre_impl_ht[OF full_split same_split, where a = L and b = M])
      subgoal
        using check_all_pre'_refine unfolding RETURN_def by (rule le_RES_nofailI)
      subgoal
        using * by (elim ent_frame_fwd) solve_entails+
      subgoal
        apply sep_auto
        apply (drule order.trans, rule check_all_pre'_refine)
        apply auto
        done
      done
    done
  have 3: "
    <emp>
      do {M' \<leftarrow> M_table; check_final_impl Fi copyi L_list M'}
    <\<lambda>r. \<up>(r \<longrightarrow> check_final_spec)>\<^sub>t"
    apply (sep_auto)
    subgoal for Mi
      apply (rule cons_rule[rotated 2])
        apply (rule frame_rule[where R = true])
        apply (rule check_final_impl.refine[
            OF Reachability_Impl_axioms, to_hnr, unfolded hn_refine_def hn_ctxt_def, simplified,
            rule_format, where a = L and b = M])
      subgoal
        sorry
      subgoal
        using * by (elim ent_frame_fwd) solve_entails+
      subgoal
        apply sep_auto
        unfolding check_final_alt_def
        apply (drule order.trans, rule check_final_correct)
        apply (sep_auto simp: pure_def)
        done
      done
    done
  have 2: "
    <emp>
      do {M' \<leftarrow> M_table; check_invariant_impl Li M'}
   <\<lambda>r. \<up>(r \<longrightarrow> check_invariant_spec (set L'))>\<^sub>t
  " if
    "\<forall>l\<in>L. \<forall>s\<in>the (M l). P (l, s)"
    "Li \<in> set (splitteri L_list)" "(Li, L') \<in> \<langle>(the_pure K)\<rangle>list_rel" "set L' \<subseteq> L"
  for Li L'
    apply sep_auto
    subgoal for Mi
      apply (rule cons_rule[rotated 2])
        apply (rule frame_rule[where R = true])
        apply (rule check_invariant_impl_ht[where bi = Mi and a = L'])
      subgoal
        sorry
      subgoal
        using \<open>dom M = L\<close> ..
      subgoal
        by (rule that)
      subgoal
        by (rule that(1))
      subgoal
        using that(3) unfolding list_assn_K_eq pure_def by sep_auto
      subgoal
        by sep_auto
      done
    done
  obtain LL where "set LL = L"
    using L_finite L_listD by blast
  have 2:
    "check_invariant_spec L"
    if "check_all_pre_spec l\<^sub>0 s\<^sub>0"
      "list_all id
     (run_map_heap (\<lambda>Li. M_table \<bind> check_invariant_impl Li)
       (splitteri L_list))"
  proof -
    let ?c = "(\<lambda>Li. M_table \<bind> check_invariant_impl Li)"
    have A: "\<forall>l\<in>L. \<forall>s\<in>the (M l). P (l, s)"
      using \<open>check_all_pre_spec l\<^sub>0 s\<^sub>0\<close> \<open>dom M = L\<close>
      unfolding check_all_pre_spec_def by (force intro: P'_P)
    have
      "list_all2 (\<lambda>L' r. r \<longrightarrow> check_invariant_spec (set L'))
        (splitter LL) (run_map_heap ?c (splitteri L_list))"
      apply (rule hoare_triple_run_map_heapD')
      subgoal
        apply (rule list_all2_all_nthI)
        subgoal B
          sorry
        apply (rule 2[OF A])
        using B apply simp
        subgoal for n
          sorry
        subgoal for n
          unfolding \<open>set LL = L\<close>[symmetric] by (subst (2) full_split) force
        done
      done
    then have "list_all (\<lambda>L'. check_invariant_spec (set L')) (splitter LL)"
      sorry
    with full_split[of LL] show ?thesis
      unfolding list_all_iff check_invariant_spec_def \<open>set LL = L\<close> by auto
  qed
  show ?thesis
    apply standard
    apply (rule certify_unreachableI[rule_format])
    using hoare_triple_run_heapD[OF 1] hoare_triple_run_heapD[OF 3]
    unfolding certify_unreachable_new_def[OF full_split same_split] check_all_spec_def
    by (auto intro: 2)
qed

lemmas certify_unreachable_impl2_refine =
  certify_unreachable_new_correct[
    unfolded certify_unreachable_impl2.refine[OF Reachability_Impl_axioms full_split same_split]
    ]

end

concrete_definition (in -) certify_unreachable_impl
  uses Reachability_Impl.certify_unreachable_impl_refine is "(uncurry0 ?f,_)\<in>_"

(*
lemmas certify_unreachable_impl_refine =
  certify_unreachable_impl.refine_raw[FCOMP certify_unreachable_correct']
*)

(*
concrete_definition (in -) certify_unreachable_impl
  uses Reachability_Impl.certify_unreachable_impl is "(uncurry0 ?f,_)\<in>_"
*)

paragraph \<open>Debugging\<close>



definition (in -)
  "mk_st_string s1 s2 \<equiv> STR ''<'' + s1 + STR '', '' + s2 + STR ''>''"

(* XXX Error: 'Tactic failed' inside context *)
lemma [sepref_import_param]: "(mk_st_string, mk_st_string) \<in> Id \<rightarrow> Id \<rightarrow> Id"
  by simp

definition (in -)
  "PRINTLN = RETURN o println"

lemma (in -) [sepref_import_param]:
  "(println, println) \<in> Id \<rightarrow> Id"
  by simp

sepref_definition (in -) print_line_impl is
  "PRINTLN" :: " id_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding PRINTLN_def by sepref

sepref_register (in -) PRINTLN

lemmas [sepref_fr_rules] = print_line_impl.refine

context
  fixes show_loc :: "'k \<Rightarrow> String.literal nres" and show_dbm :: "'a \<Rightarrow> String.literal nres"
    and show_dbm_impl and show_loc_impl
  assumes show_dbm_impl: "(show_dbm_impl, show_dbm) \<in> A\<^sup>d \<rightarrow>\<^sub>a id_assn"
  assumes show_loc_impl: "(show_loc_impl, show_loc) \<in> K\<^sup>d \<rightarrow>\<^sub>a id_assn"
begin

lemma [sepref_fr_rules]: "(show_dbm_impl, PR_CONST show_dbm) \<in> A\<^sup>d \<rightarrow>\<^sub>a id_assn"
  using show_dbm_impl unfolding PR_CONST_def .

lemma [sepref_fr_rules]: "(show_loc_impl, PR_CONST show_loc) \<in> K\<^sup>d \<rightarrow>\<^sub>a id_assn"
  using show_loc_impl unfolding PR_CONST_def .

definition
  "show_st \<equiv> \<lambda> (l, M).  do {
    s1 \<leftarrow> PR_CONST show_loc l;
    s2 \<leftarrow> PR_CONST show_dbm M;
    RETURN (mk_st_string s1 s2)
  }"

sepref_register "PR_CONST show_st" "PR_CONST show_loc" "PR_CONST show_dbm"

sepref_thm show_st_impl is
  "PR_CONST show_st" :: "(K \<times>\<^sub>a A)\<^sup>d \<rightarrow>\<^sub>a id_assn"
  unfolding PR_CONST_def unfolding show_st_def by sepref

lemmas [sepref_fr_rules] = show_st_impl.refine_raw

definition check_prop_fail where
  "check_prop_fail L' M' = do {
  l \<leftarrow> SPEC (\<lambda>xs. set xs = L');
  r \<leftarrow> monadic_list_all_fail' (\<lambda>l. do {
    let S = op_map_lookup l M';
    case S of None \<Rightarrow> RETURN None | Some S \<Rightarrow> do {
      xs \<leftarrow> SPEC (\<lambda>xs. set xs = S);
      r \<leftarrow> monadic_list_all_fail (\<lambda>s.
        RETURN (PR_CONST P' (l, s))
      ) xs;
      RETURN (case r of None \<Rightarrow> None | Some r \<Rightarrow> Some (l, r))


       \<^cancel>\<open>case r of None \<Rightarrow> RETURN None | Some r \<Rightarrow> RETURN (Some (l, r))\<close>
    }
    }
  ) l;
  case r of None \<Rightarrow> RETURN None |
    Some (l, M) \<Rightarrow> do {
    s \<leftarrow> PR_CONST show_st (l, COPY M);
    PRINTLN (STR ''Prop failed for: '');
    PRINTLN s;
    RETURN (Some (l, M))
  }
  }"

sepref_thm check_prop_fail_impl is
  "uncurry check_prop_fail" :: "(lso_assn K)\<^sup>k *\<^sub>a table_assn\<^sup>d \<rightarrow>\<^sub>a option_assn (K \<times>\<^sub>a A)"
  unfolding check_prop_fail_def list_of_set_def[symmetric]
  unfolding monadic_list_all_fail'_alt_def monadic_list_all_fail_alt_def
  by sepref

end (* Anonymous context *)

definition
  "check_invariant_fail L' M' \<equiv> do {
  l \<leftarrow> SPEC (\<lambda>xs. set xs = L');
  monadic_list_all_fail' (\<lambda>l.
  do {
    case op_map_lookup l M' of None \<Rightarrow> RETURN None  | Some as \<Rightarrow> do {
    let succs = PR_CONST succs l as;
    monadic_list_all_fail' (\<lambda>(l', xs). do {
      xs \<leftarrow> SPEC (\<lambda>xs'. set xs' = xs);
      if xs = [] then RETURN None
      else do {
        b1 \<leftarrow> RETURN (l' \<in> L'); \<comment> \<open>XXX Optimize this\<close>
        if b1 then do {
        case op_map_lookup l' M' of None \<Rightarrow> RETURN (Some (Inl (Inr (l, l', xs)))) | Some ys \<Rightarrow> do {
          ys \<leftarrow> SPEC (\<lambda>xs.  set xs  = ys);
          b2 \<leftarrow> monadic_list_all_fail (\<lambda>x'.
            monadic_list_ex (\<lambda>y. RETURN (PR_CONST less_eq x' y)) ys
          ) xs;
          case b2 of None \<Rightarrow> RETURN None | Some M \<Rightarrow> do {
            case op_map_lookup l M' of
              None \<Rightarrow> RETURN (Some (Inl (Inr (l, l', ys)))) \<comment> \<open>never used\<close>
            | Some as \<Rightarrow> do {
                as \<leftarrow> SPEC (\<lambda>xs'. set xs' = as);
                RETURN (Some (Inr (l, as, l', M, ys)))}
              }
          }
      }
      else RETURN (Some (Inl (Inl (l, l', xs))))
    }
    }) succs
  }
  }
  ) l
}"

sepref_thm check_invariant_fail_impl is
  "uncurry check_invariant_fail"
  :: "(lso_assn K)\<^sup>k *\<^sub>a table_assn\<^sup>k \<rightarrow>\<^sub>a
      option_assn ((K \<times>\<^sub>a K \<times>\<^sub>a list_assn A +\<^sub>a K \<times>\<^sub>a K \<times>\<^sub>a list_assn A) +\<^sub>a K \<times>\<^sub>a list_assn A \<times>\<^sub>a K \<times>\<^sub>a A \<times>\<^sub>a list_assn A)"
  unfolding PR_CONST_def
  unfolding check_invariant_fail_def list_of_set_def[symmetric]
  unfolding monadic_list_all_fail'_alt_def monadic_list_all_fail_alt_def
  unfolding monadic_list_all_def monadic_list_ex_def
  by sepref

lemmas check_invariant_fail_impl_refine = check_invariant_fail_impl.refine_raw[
  unfolded is_member_impl_def[OF pure_K left_unique_K right_unique_K]
]

end (* Reachability Impl *)

concrete_definition (in -) check_prop_fail_impl
  uses Reachability_Impl.check_prop_fail_impl.refine_raw is "(uncurry ?f,_)\<in>_"

concrete_definition (in -) check_invariant_fail_impl
  uses Reachability_Impl.check_invariant_fail_impl_refine is "(uncurry ?f,_)\<in>_"

export_code
  certify_unreachable_impl certify_unreachable_impl2 check_prop_fail_impl check_invariant_fail_impl
in SML module_name Test

end (* Theory *)
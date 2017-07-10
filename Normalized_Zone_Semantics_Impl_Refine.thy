theory Normalized_Zone_Semantics_Impl_Refine
  imports
    Normalized_Zone_Semantics_Impl DBM_Operations_Impl_Refine
    "~~/src/HOL/Library/IArray"
    Code_Numeral
    "Worklist_Algorithms/Worklist_Subsumption_Impl1" "Worklist_Algorithms/Unified_PW_Impl"
    Normalized_Zone_Semantics_Impl_Semantic_Refinement
begin

  chapter \<open>Imperative Implementation of Reachability Checking\<close>

  lemma rev_map_fold_append_aux:
    "fold (\<lambda> x xs. f x # xs) xs zs @ ys = fold (\<lambda> x xs. f x # xs) xs (zs@ys)"
   apply (induction xs arbitrary: zs)
  by auto

  lemma rev_map_fold:
  "rev (map f xs) = fold (\<lambda> x xs. f x # xs) xs []"
   apply (induction xs)
   apply simp
   apply (simp add: rev_map_fold_append_aux)
  done

  subsection \<open>Mapping Transitions and Invariants\<close>

  type_synonym
    ('a, 'c, 'time, 's) transition_fun = "'s \<Rightarrow> (('c, 'time) cconstraint * 'a * 'c list * 's) list"

  (* XXX Can this be constructed from other primitives? *)
  definition transition_rel where
    "transition_rel X = {(f, r). \<forall> l \<in> X. \<forall> x. (l, x) \<in> r \<longleftrightarrow> x \<in> set (f l)}"

  (* XXX Rename *)
  definition inv_rel where -- "Invariant assignments for a restricted state set"
    (* XXX Or use "inv_rel X = Id_on X \<rightarrow> Id" ? *)
    "inv_rel X = b_rel Id (\<lambda> x. x \<in> X) \<rightarrow> Id"

  (* XXX Map from automaton? *)
  definition state_set :: "('a, 'c, 'time, 's) transition set \<Rightarrow> 's set" where
    "state_set T = fst ` T \<union> (snd o snd o snd o snd) ` T"

locale Reachability_Problem_Impl_Defs =
  Reachability_Problem_no_ceiling A l\<^sub>0 F n
  for A :: "('a, nat, int, 's) ta" and l\<^sub>0 :: 's and F :: "'s \<Rightarrow> bool" and n :: nat +

  fixes trans_fun :: "('a, nat, int, 's) transition_fun"
    and inv_fun :: "(nat, int, 's) invassn"
    and F_fun :: "'s \<Rightarrow> bool"
    and ceiling :: "'s \<Rightarrow> int iarray"
begin

  (* XXX Should this be something different? *)
  abbreviation "states \<equiv> {l\<^sub>0} \<union> (state_set (trans_of A))"

end

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


locale Reachability_Problem_Impl =
  Reachability_Problem_Impl_Defs A l\<^sub>0 F n +
  Reachability_Problem l\<^sub>0 F n A k
  for A :: "('a, nat, int, 's :: {hashable, heap}) ta"
  and l\<^sub>0 :: 's
  and F :: "'s \<Rightarrow> bool"
  and n :: nat
  and k +
  assumes trans_fun: "(trans_fun, trans_of A) \<in> transition_rel states"
      and inv_fun: "(inv_fun, inv_of A) \<in> inv_rel states"
      and F_fun: "(F_fun, F) \<in> inv_rel states"
      and ceiling: "(ceiling, IArray o k') \<in> inv_rel states"
begin

  abbreviation "location_rel \<equiv> b_rel Id (\<lambda> x. x \<in> states)"

  abbreviation "location_assn \<equiv> pure location_rel"

  abbreviation "state_assn \<equiv> prod_assn id_assn (mtx_assn n)"

  abbreviation "state_assn' \<equiv> prod_assn location_assn (mtx_assn n)"

  abbreviation
    "op_impl_assn \<equiv>
    location_assn\<^sup>k *\<^sub>a (list_assn (clock_assn n))\<^sup>k *\<^sub>a
    (list_assn (acconstraint_assn (clock_assn n) id_assn))\<^sup>k *\<^sub>a location_assn\<^sup>k *\<^sub>a (mtx_assn n)\<^sup>d
    \<rightarrow>\<^sub>a mtx_assn n"

end

locale Reachability_Problem_Impl_Op =
  Reachability_Problem_Impl _ _ _ _ _ l\<^sub>0
  + op: E_From_Op_Bisim_Finite l\<^sub>0 for l\<^sub>0 :: "'s :: {hashable, heap}" +
  fixes op_impl
  assumes op_impl: "(uncurry4 op_impl, uncurry4 (\<lambda> l r. RETURN ooo f l r)) \<in> op_impl_assn"
begin

end

text \<open>Shared Setup\<close>
context Reachability_Problem_Impl
begin

  definition "inv_of_A = inv_of A"

  context
    notes [map_type_eqs] = map_type_eqI[of "TYPE(nat * nat \<Rightarrow> 'e)" "TYPE('e i_mtx)"]
  begin

  sepref_register trans_fun

  sepref_register abstr_upd up_canonical_upd norm_upd reset'_upd reset_canonical_upd

  sepref_register "PR_CONST (FW'' n)"

  sepref_register "PR_CONST (Reachability_Problem_Impl.inv_of_A A)"

  end

  lemmas [sepref_fr_rules] = fw_impl.refine[FCOMP fw_impl'_refine_FW'']

  lemma [def_pat_rules]: "FW'' $ n \<equiv> UNPROTECT (FW'' n)" by simp

  lemma trans_fun_clock_bounds3:
    "\<forall> c \<in> collect_clks (inv_of A l). c \<le> n"
  using collect_clks_inv_clk_set[of A l] clocks_n by force

  lemma inv_fun_rel:
    assumes "l \<in> states"
    shows "(inv_fun l, inv_of A l) \<in> \<langle>\<langle>nbn_rel (Suc n), int_rel\<rangle>acconstraint_rel\<rangle>list_rel"
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
      "inv_fun l = inv_of A l"
    using inv_fun assms unfolding inv_rel_def b_rel_def fun_rel_def by auto
    ultimately show ?thesis using trans_fun_clock_bounds3 by auto
  qed

  lemma [sepref_fr_rules]:
    "(return o inv_fun, RETURN o PR_CONST inv_of_A)
    \<in> location_assn\<^sup>k \<rightarrow>\<^sub>a list_assn (acconstraint_assn (clock_assn n) int_assn)"
    using inv_fun_rel
   apply (simp add: b_assn_pure_conv aconstraint_assn_pure_conv list_assn_pure_conv inv_of_A_def)
  by sepref_to_hoare (sep_auto simp: pure_def)

  lemma [sepref_fr_rules]:
    "(return o ceiling, RETURN o PR_CONST k') \<in> location_assn\<^sup>k \<rightarrow>\<^sub>a iarray_assn"
    using ceiling by sepref_to_hoare (sep_auto simp: inv_rel_def fun_rel_def br_def)

  sepref_register "PR_CONST k'"

  lemma [def_pat_rules]: "(Reachability_Problem_Defs.k' $ n $ k) \<equiv> PR_CONST k'" by simp

  lemma [simp]:
    "length (k' l) > n"
  by (simp add: k'_def)

  lemma [def_pat_rules]: "(Reachability_Problem_Impl.inv_of_A $ A) \<equiv> PR_CONST inv_of_A" by simp

  lemma reset_canonical_upd_impl_refine:
    "(uncurry3 (reset_canonical_upd_impl n), uncurry3 (\<lambda>x. RETURN \<circ>\<circ>\<circ> reset_canonical_upd x))
      \<in> [\<lambda>(((_, i), j), _).
             i \<le> n \<and>
             j \<le> n]\<^sub>a (mtx_assn n)\<^sup>d *\<^sub>a nat_assn\<^sup>k *\<^sub>a (nbn_assn (Suc n))\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> mtx_assn n"
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
    \<in> (acconstraint_assn (clock_assn n) id_assn)\<^sup>k \<rightarrow>\<^sub>a clock_assn n"
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
    "(acconstraint_assn (clock_assn n) id_assn)\<^sup>k *\<^sub>a (mtx_assn n)\<^sup>d \<rightarrow>\<^sub>a mtx_assn n"
    unfolding abstra_repair_def PR_CONST_def
    by sepref

  sepref_register abstra_repair :: "(nat, 'e) acconstraint \<Rightarrow> 'e DBMEntry i_mtx \<Rightarrow> 'e DBMEntry i_mtx"

  lemmas [sepref_fr_rules] = abstra_repair_impl.refine

  sepref_definition abstr_repair_impl is
    "uncurry (RETURN oo PR_CONST abstr_repair)" ::
    "(list_assn (acconstraint_assn (clock_assn n) id_assn))\<^sup>k *\<^sub>a (mtx_assn n)\<^sup>d \<rightarrow>\<^sub>a mtx_assn n"
    unfolding abstr_repair_def PR_CONST_def
    by sepref

  sepref_register abstr_repair ::
    "(nat, 'e) acconstraint list \<Rightarrow> 'e DBMEntry i_mtx \<Rightarrow> 'e DBMEntry i_mtx"

  lemmas [sepref_fr_rules] = abstr_repair_impl.refine

end (* End of Reachability Problem Impl *)

context Reachability_Problem_Impl_Op
begin

  definition succs where
    "succs \<equiv> \<lambda> (l, D). rev (map (\<lambda> (g,a,r,l'). (l', f l r g l' D)) (trans_fun l))"

  definition succs' where
    "succs' \<equiv> \<lambda> (l, D). do
      {
        xs \<leftarrow> nfoldli (trans_fun l) (\<lambda> _. True) (\<lambda> (g,a,r,l') xs. do
          {
            RETURN ((l', f l r g l' (op_mtx_copy D)) # xs)
          }
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
    (\<lambda> (l, M :: ('c :: {zero,linorder}) DBM') (l', M').
      l = l' \<and> pointwise_cmp (op \<le>) n (curry M) (curry M'))"

  context
  begin

  lemma [sepref_import_param]:
    "(op =, op =) \<in> location_rel \<rightarrow> location_rel \<rightarrow> Id"
    by auto

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
    "(l\<^sub>0, l\<^sub>0) \<in> location_rel"
  by auto

  sepref_definition a\<^sub>0_impl is
    "uncurry0 (RETURN a\<^sub>0)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a state_assn'"
  unfolding a\<^sub>0_def by sepref

  (* XXX Better implementation? *)
  lemma F_rel_alt_def:
    "F_rel = (\<lambda> (l, M). F l  \<and> \<not> check_diag n M)"
  unfolding F_rel_def by auto

  sepref_register F

  lemma [sepref_fr_rules]:
    "(return o F_fun, RETURN o F) \<in> location_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  using F_fun by sepref_to_hoare (sep_auto simp: inv_rel_def b_rel_def fun_rel_def)

  (* XXX Better implementation? *)
  lemma [sepref_import_param]: "(List.member, List.member) \<in> Id \<rightarrow> location_rel \<rightarrow> Id" by auto

  sepref_definition F_impl is
    "RETURN o (\<lambda> (l, M). F l)" :: "state_assn'\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  by sepref

  lemma trans_fun_trans_of[intro]:
    "(g, a, r, l') \<in> set (trans_fun l) \<Longrightarrow> l \<in> states \<Longrightarrow> A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"
  using trans_fun unfolding transition_rel_def by auto

  lemma trans_of_trans_fun[intro]:
    "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<Longrightarrow> l \<in> states \<Longrightarrow> (g, a, r, l') \<in> set (trans_fun l)"
  using trans_fun unfolding transition_rel_def by auto

  lemma trans_fun_clock_bounds1:
    "(g, a, r, l') \<in> set (trans_fun l) \<Longrightarrow> l \<in> states \<Longrightarrow> \<forall> c \<in> set r. c \<le> n"
  using clocks_n reset_clk_set[OF trans_fun_trans_of] by fastforce

  lemma trans_fun_clock_bounds2:
    "(g, a, r, l') \<in> set (trans_fun l) \<Longrightarrow> l \<in> states \<Longrightarrow> \<forall> c \<in> collect_clks g. c \<le> n"
  using clocks_n collect_clocks_clk_set[OF trans_fun_trans_of] by fastforce

  lemma trans_fun_states:
    "(g, a, r, l') \<in> set (trans_fun l) \<Longrightarrow> l \<in> states \<Longrightarrow> l' \<in> state_set (trans_of A)"
   apply (drule trans_fun_trans_of)
   apply auto[]
   unfolding state_set_def
   apply (rule UnI2)
  by force

  lemma trans_of_states[intro]:
    "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<Longrightarrow> l \<in> states \<Longrightarrow> l' \<in> states"
  by (auto intro: trans_fun_states)

  abbreviation "clock_rel \<equiv> nbn_rel (Suc n)"

  lemma [sepref_import_param]:
    "(trans_fun, trans_fun)
    \<in> location_rel \<rightarrow> \<langle>\<langle>\<langle>clock_rel, int_rel\<rangle> acconstraint_rel\<rangle> list_rel \<times>\<^sub>r Id \<times>\<^sub>r \<langle>clock_rel\<rangle> list_rel \<times>\<^sub>r location_rel\<rangle> list_rel"
  apply (rule fun_relI)
  apply simp
  subgoal premises prems for x x'
  proof -
    { fix l :: "((nat, int) acconstraint list \<times> 'a \<times> nat list \<times> 's) list"
      assume "\<forall> g a r l'. (g, a, r, l') \<in> set l \<longrightarrow> (\<forall> c \<in> collect_clks g. c \<le> n) \<and> (\<forall> c \<in> set r. c \<le> n) \<and> l' \<in> states"
      then have "(l, l) \<in> \<langle>\<langle>\<langle>nbn_rel (Suc n), int_rel\<rangle>acconstraint_rel\<rangle>list_rel \<times>\<^sub>r Id \<times>\<^sub>r \<langle>nbn_rel (Suc n)\<rangle>list_rel \<times>\<^sub>r location_rel\<rangle>list_rel"
      proof (induction l)
        case Nil then show ?case by simp
      next
        case (Cons x xs)
        then obtain g a r l' where [simp]: "x = (g, a, r, l')" by (cases x)
        from Cons.prems have r_bounds: "\<forall> c \<in> set r. c \<le> n" by auto
        from Cons.prems have "\<forall> c \<in> collect_clks g. c \<le> n" by auto
        then have "(g, g) \<in> \<langle>\<langle>nbn_rel (Suc n), int_rel\<rangle>acconstraint_rel\<rangle>list_rel"
          apply (induction g)
          apply simp
          apply simp
          subgoal for a
          apply (cases a)
          by (auto simp: acconstraint_rel_def p2rel_def rel2p_def)
        done
        moreover from r_bounds have "(r, r) \<in> \<langle>nbn_rel (Suc n)\<rangle>list_rel" by (induction r) auto
        moreover from Cons.prems have "(l', l') \<in> location_rel" by auto
        ultimately have
          "(x, x) \<in> \<langle>\<langle>nbn_rel (Suc n), int_rel\<rangle>acconstraint_rel\<rangle>list_rel \<times>\<^sub>r Id \<times>\<^sub>r \<langle>nbn_rel (Suc n)\<rangle>list_rel \<times>\<^sub>r location_rel"
        by simp
        moreover from Cons have
          "(xs, xs) \<in> \<langle>\<langle>\<langle>nbn_rel (Suc n), int_rel\<rangle>acconstraint_rel\<rangle>list_rel \<times>\<^sub>r Id \<times>\<^sub>r \<langle>nbn_rel (Suc n)\<rangle>list_rel \<times>\<^sub>r location_rel\<rangle>list_rel"
        by force
        ultimately show ?case by simp
      qed
    }
    with prems trans_fun_clock_bounds1 trans_fun_clock_bounds2 trans_fun_states show ?thesis by auto
  qed
  done

  sepref_register op_HOL_list_empty

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

  sepref_definition succs_impl is
    "RETURN o succs" :: "state_assn'\<^sup>k \<rightarrow>\<^sub>a list_assn state_assn'"
  unfolding
    comp_def succs'_succs[symmetric] succs'_def
    FW''_def[symmetric] rev_map_fold inv_of_A_def[symmetric]
  apply (rewrite "HOL_list.fold_custom_empty")
  by sepref

  end (* End sepref setup *)

  (* XXX Move to different context *)
  lemma reachable_states:
    "l \<in> states" if "op.reachable (l, M)"
    using that unfolding op.reachable_def
    by (induction "(l, M)" arbitrary: l M; force simp: a\<^sub>0_def state_set_def op.E_from_op_def)

  definition "emptiness_check \<equiv> \<lambda> (l, M). check_diag n M"

  sepref_definition emptiness_check_impl  is
    "RETURN o emptiness_check" :: "state_assn'\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    unfolding emptiness_check_def
    by sepref



  sublocale Worklist0 op.E_from_op a\<^sub>0 F_rel "subsumes n" succs "\<lambda> (l, M). check_diag n M"
    apply standard
    apply (clarsimp split: prod.split dest!: reachable_states)
    unfolding succs_def op.E_from_op_def by force thm E_alt_def

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
        a\<^sub>0_impl.refine F_impl.refine subsumes_impl.refine succs_impl.refine
        emptiness_check_impl.refine[unfolded emptiness_check_def]
        )+

  lemma state_copy:
    "RETURN \<circ> COPY = (\<lambda> (l, M). do {M' \<leftarrow> mop_mtx_copy M; RETURN (l, M')})"
    by auto

  sepref_definition state_copy_impl is
    "RETURN \<circ> COPY" :: "state_assn'\<^sup>k \<rightarrow>\<^sub>a state_assn'"
    unfolding state_copy
    by sepref


  sublocale Worklist_Map2_Impl
    op.E_from_op a\<^sub>0 F_rel "subsumes n" succs "\<lambda> (l, M). check_diag n M" subsumes'
    "\<lambda> (l, M). F l" state_assn'
    succs_impl a\<^sub>0_impl F_impl subsumes_impl emptiness_check_impl fst "return o fst" state_copy_impl
    apply standard
    unfolding PR_CONST_def
     apply sepref_to_hoare
     apply sep_auto
    by (rule state_copy_impl.refine)

  sublocale Worklist_Map2_Hashable
    op.E_from_op a\<^sub>0 F_rel "subsumes n" succs "\<lambda> (l, M). check_diag n M" subsumes' "\<lambda> (l, M). F l"
    state_assn' succs_impl a\<^sub>0_impl F_impl subsumes_impl emptiness_check_impl
    "return o fst" state_copy_impl fst by standard

  paragraph \<open>Implementation for the invariant precondition check\<close>

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

context Reachability_Problem_Impl
begin

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

sublocale Reachability_Problem_Impl_Op _ _ _ _ _ _ _ _ "PR_CONST E_op''" _ E_op''_impl
  unfolding PR_CONST_def by standard (rule E_op''_impl.refine)

lemma E_op_F_reachable:
  "op.F_reachable = E_op''.F_reachable" unfolding PR_CONST_def ..

end (* End of Reachability Problem Impl *)

datatype result = REACHABLE | UNREACHABLE | INIT_INV_ERR

context Reachability_Problem_precompiled
begin

  sublocale Defs: Reachability_Problem_Impl_Defs A 0 "PR_CONST F" m by standard

  lemma
    "(IArray xs) !! i = xs ! i"
  by auto

  text \<open>Definition of implementation auxiliaries (later connected to the automaton via proof)\<close>
  (*
  definition
    "trans_fun l \<equiv> map (\<lambda> i. label i ((IArray trans) !! l ! i)) [0..<length (trans ! l)]"
  *)

  definition
    "trans_map \<equiv> map (\<lambda> xs. map (\<lambda> i. label i (xs ! i)) [0..<length xs]) trans"

  definition
    "trans_fun l \<equiv> (IArray trans_map) !! l"

  lemma trans_fun_alt_def:
    "l < n
    \<Longrightarrow> trans_fun l = map (\<lambda> i. label i ((IArray trans) !! l ! i)) [0..<length (trans ! l)]"
  unfolding trans_fun_def trans_map_def by (auto simp: trans_length)

  lemma state_set_n[intro, simp]:
    "state_set (trans_of A) \<subseteq> {0..<n}"
  unfolding state_set_def trans_of_def A_def T_def label_def using state_set trans_length
  by (force dest: nth_mem)

  lemma trans_fun_trans_of[intro, simp]:
    "(trans_fun, trans_of A) \<in> transition_rel Defs.states"
  using state_set_n n_gt_0 unfolding transition_rel_def trans_of_def A_def T_def
  by (fastforce simp: trans_fun_alt_def)

  definition "inv_fun l \<equiv> (IArray inv) !! l"

  lemma inv_fun_inv_of[intro, simp]:
    "(inv_fun, inv_of A) \<in> inv_rel Defs.states"
  using state_set_n n_gt_0 unfolding inv_rel_def inv_fun_def[abs_def] inv_of_def A_def I_def[abs_def]
  by auto

  definition "final_fun = List.member final"

  lemma final_fun_final[intro, simp]:
    "(final_fun, F) \<in> inv_rel Defs.states"
  using state_set_n unfolding F_def final_fun_def inv_rel_def by (auto simp: in_set_member)

  lemma start_states[intro, simp]:
    "0 \<in> Defs.states"
  proof -
    obtain g r l' where "trans ! 0 ! 0 = (g, r, l')" by (metis prod_cases3)
    with start_has_trans n_gt_0 trans_length show ?thesis
    unfolding state_set_def trans_of_def A_def T_def label_def by force
  qed

  lemma iarray_k':
    "(IArray.sub (IArray (map (IArray o map int) k)), IArray o k') \<in> inv_rel Defs.states"
    unfolding inv_rel_def k'_def
    apply (clarsimp simp del: upt_Suc)
    subgoal premises prems for j
    proof -
      have "j < n" using prems n_gt_0 state_set_n by fastforce
      with k_length have "length (k ! j) = m + 1" by simp
      with k_length(2) have
        "map (\<lambda>i. if i \<le> m then k ! j ! i else 0) [0..<Suc m] = map (\<lambda>i. k ! j ! i) [0..<Suc m]"
        by simp thm strong_ball_cong
      also have "\<dots> = k ! j" using \<open>length (k ! j) = _\<close> by (simp del: upt_Suc) (metis List.map_nth)
      also show ?thesis using \<open>j < n\<close> k_length(1)
          apply simp
          apply (subst calculation[symmetric])
        by simp
    qed
    done

  (* XXX Room for optimization *)
  sublocale Reachability_Problem_Impl
    trans_fun inv_fun final_fun "IArray.sub (IArray (map (IArray o map int) k))" A 0 "PR_CONST F" m
    "\<lambda> l i. if l < n \<and> i \<le> m then k ! l ! i else 0"
    unfolding PR_CONST_def
    apply standard
    using iarray_k' by fastforce+

  lemma F_reachable_correct:
    "op.F_reachable
    \<longleftrightarrow> (\<exists> l' u u'. conv_A A \<turnstile>' \<langle>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> l' \<in> set final)"
    using E_op''.E_from_op_reachability_check reachability_check
    unfolding E_op_F_reachable E_op''.F_reachable_def E_op''.reachable_def
    unfolding F_def by auto

  definition
    "reachability_checker_wl \<equiv>
      worklist_algo2_impl subsumes_impl a\<^sub>0_impl F_impl succs_impl emptiness_check_impl"

  definition
    "reachability_checker' \<equiv>
      pw_impl
        (return o fst) state_copy_impl subsumes_impl a\<^sub>0_impl F_impl succs_impl emptiness_check_impl"

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
    <\<lambda> r. \<up>(r \<longleftrightarrow> (\<exists> l' u u'. conv_A A \<turnstile>' \<langle>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> l' \<in> set final))>\<^sub>t"
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
      "check_A \<equiv> \<exists> l' u u'. conv_A A \<turnstile>' \<langle>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> l' \<in> set final"
    define check_B where
      "check_B \<equiv> \<exists> l' u u'. conv_A A \<turnstile> \<langle>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> l' \<in> set final"
    note F_reachable_equiv' =
      F_reachable_equiv
      [unfolded F_def PR_CONST_def check_A_def[symmetric] check_B_def[symmetric]]
    show ?thesis
      unfolding reachability_checker_def
      unfolding check_A_def[symmetric] check_B_def[symmetric]
      using F_reachable_equiv'
      supply reachability_check'
        [unfolded check_A_def[symmetric], to_hnr, unfolded hn_refine_def, rule_format, sep_heap_rules]
      supply start_inv_check_impl.refine[to_hnr, unfolded hn_refine_def, rule_format, sep_heap_rules]
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
    val u3 = @{term "trans_fun"};
    val rewr3 = pull_let u3 r3;
    val mytac = fn ctxt => SELECT_GOAL (Local_Defs.unfold_tac ctxt [rewr1, rewr2, rewr3]) 1;
  \<close>

  lemma inv_fun_alt_def:
    "inv_fun i \<equiv> let I = (IArray inv) in I !! i"
  unfolding inv_fun_def by simp

  lemma inv_fun_rewr:
    "(let I0 = trans_fun; I = inv_fun; I1 = y in xx I0 I I1) \<equiv>
     (let I0 = trans_fun; I = (IArray inv); I' = \<lambda> i. I !! i; I1 = y in xx I0 I' I1)"
  unfolding inv_fun_def[abs_def] by simp

  lemma inv_fun_rewr':
    "(let I = inv_fun in xx I) \<equiv>
     (let I = (IArray inv); I' = \<lambda> i. I !! i in xx I')"
  unfolding inv_fun_def[abs_def] by simp

  schematic_goal succs_impl_alt_def':
    "succs_impl \<equiv> ?impl"
  unfolding succs_impl_def
   apply (tactic \<open>mytac @{context}\<close>)
   unfolding inv_fun_rewr' trans_fun_def[abs_def]
   apply (tactic \<open>pull_tac @{term "IArray trans_map"} @{context}\<close>)
  by (rule Pure.reflexive)

  schematic_goal succs_impl_alt_def:
    "succs_impl \<equiv> ?impl"
  unfolding succs_impl_def
   apply (tactic \<open>pull_tac @{term "IArray.sub (IArray (map (IArray o map int) k))"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "inv_fun"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "trans_fun"} @{context}\<close>)
   unfolding inv_fun_def[abs_def] trans_fun_def[abs_def]
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
        empty = emptiness_check_impl
      in pw_impl key copy sub start final succs empty"
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
   apply (tactic \<open>pull_tac @{term "trans_fun"} @{context}\<close>)
   unfolding inv_fun_def[abs_def] trans_fun_def[abs_def]
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
   apply (tactic \<open>pull_tac @{term "trans_fun"} @{context}\<close>)
   unfolding inv_fun_def[abs_def] trans_fun_def[abs_def]
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

lemmas Reachability_Problem_precompiled_defs.check_axioms[code]

lemmas Reachability_Problem_precompiled_defs.clkp_set'_def[code]

lemmas Reachability_Problem_precompiled_defs.clk_set'_def[code]

lemmas Reachability_Problem_precompiled_defs.check_pre_def[code]

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

export_code open check_and_verify checking SML_imp

end (* End of theory *)
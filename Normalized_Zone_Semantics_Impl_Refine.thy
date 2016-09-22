theory Normalized_Zone_Semantics_Impl_Refine
  imports Normalized_Zone_Semantics_Impl DBM_Operations_Impl_Refine
begin

  lemma aux1: "fold (\<lambda> x xs. f x # xs) xs zs @ ys = fold (\<lambda> x xs. f x # xs) xs (zs@ys)"
    apply (induction xs arbitrary: zs)
    apply auto
    done

  lemma aux2:
    assumes "NO_MATCH [] ys"
    shows "fold (\<lambda>x. op # (f x)) xs ys = fold (\<lambda>x. op # (f x)) xs [] @ ys"
  using aux1[where zs="[]", simplified, symmetric] by auto

  lemma "set (map f xs) = set (fold (\<lambda> x xs. f x # xs) xs [])"
    apply (induction xs)
    apply simp
    apply (simp add: aux2)
    done

  lemma rev_map_fold:
  "rev (map f xs) = fold (\<lambda> x xs. f x # xs) xs []"
  apply (induction xs)
  apply simp
  apply (simp add: aux2)
  done

  context Reachability_Problem
  begin

  definition succs where
    "succs \<equiv> \<lambda> (l, D).
      (l, norm_upd (FW' (abstr_upd (inv_of A l) (up_canonical_upd (abstr_upd (inv_of A l) D) n)) n) k' n) #
      rev (map (\<lambda> (g,a,r,l'). (l', norm_upd (FW' (abstr_upd (inv_of A l') (reset'_upd (abstr_upd g D) n r 0)) n) k' n)) (trans_fun l))"

  term nfoldli

  definition succs' where
    "succs' \<equiv> \<lambda> (l, D). do
      {
        let delay = (l, norm_upd (FW' (abstr_upd (inv_of A l) (up_canonical_upd (abstr_upd (inv_of A l) (op_mtx_copy D)) n)) n) k' n);
        xs \<leftarrow> nfoldli (trans_fun l) (\<lambda> _. True) (\<lambda> (g,a,r,l') xs. do
          {
            let reset = fold (\<lambda>c M. reset_canonical_upd M n c 0) r (abstr_upd g (op_mtx_copy D));
            let action = (l', norm_upd (FW' (abstr_upd (inv_of A l') reset) n) k' n);
            RETURN (action # xs)
          }
        ) [];
        RETURN (delay # xs)
      }"

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
    apply (rewrite in "_ = \<hole>" RETURN_split[where f = "op #"])
    apply (rewrite fold_eq_nfoldli)
    apply (simp add: reset'_upd_def)
    apply (fo_rule arg_cong fun_cong)+
    apply auto
  done

  sepref_decl_op (no_mop, no_def) n :: "nat_rel" .

  lemma n_rel[sepref_param]:
    "(n, PR_CONST n) \<in> Id"
  by simp

  sepref_decl_impl (no_mop) n_rel .
  
  lemma [sepref_import_param]: "(A, A) \<in> Id" by simp
  lemma [sepref_import_param]: "(op =, op =) \<in> Id \<rightarrow> Id \<rightarrow> Id" by simp

  sepref_register n A

  (* XXX Risky? *)
  (* lemma [sepref_opt_simps]: "UNPROTECT n = n" by simp *)

  lemmas [sepref_fr_rules] = check_diag_impl.refine

  sepref_definition check_diag_impl'' is
    "RETURN o PR_CONST (check_diag n)" :: "(mtx_assn n)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding check_diag_alt_def[abs_def] list_ex_foldli neutral[symmetric] PR_CONST_def by sepref

  lemmas [sepref_fr_rules] = check_diag_impl''.refine

  (* lemma [def_pat_rules]: "check_diag $ n $ t = PR_CONST (check_diag n) $ t" by simp *)

  (* lemma [def_pat_rules]: "check_diag $ n = PR_CONST (check_diag n)" by simp *)

  lemma [def_pat_rules]: "check_diag $ n \<equiv> PR_CONST (check_diag n)" by simp
  lemma [def_pat_rules]: "check_diag $ UNPROTECT n \<equiv> PR_CONST (check_diag n)" by simp
  lemma [def_pat_rules]: "check_diag $ n $ t \<equiv> PR_CONST (check_diag n) $ t" by simp
  lemma [def_pat_rules]: "check_diag $ UNPROTECT n $ t \<equiv> PR_CONST (check_diag n) $ t" by simp
  lemma [def_pat_rules]: "check_diag $ (Reachability_Problem.n $ A) \<equiv> PR_CONST (check_diag n)" by simp

  sepref_register "PR_CONST (check_diag n)" :: "'e DBMEntry i_mtx \<Rightarrow> bool"

  lemmas [sepref_fr_rules del] = check_diag_impl'.refine

  term check_diag term check_diag_impl term check_diag_impl'

  term dbm_subset_impl

  (* XXX Might want to apply the same "cleaning" to dbm_subset' as to check_diag *)
  
  (* XXX Remove other implementations *)
  sepref_definition dbm_subset_impl'' is
    "uncurry (RETURN oo PR_CONST (dbm_subset n))" :: "(mtx_assn n)\<^sup>k *\<^sub>a (mtx_assn n)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding
    dbm_subset_def[abs_def] dbm_subset'_def[symmetric] short_circuit_conv PR_CONST_def
  by sepref

  lemmas [sepref_fr_rules] = dbm_subset_impl''.refine

  term "PR_CONST (dbm_subset n)"

  sepref_register "PR_CONST (dbm_subset n)" :: "'e DBMEntry i_mtx \<Rightarrow> 'e DBMEntry i_mtx \<Rightarrow> bool"

  lemma [def_pat_rules]: "dbm_subset $ (Reachability_Problem.n $ A) \<equiv> PR_CONST (dbm_subset n)" by simp

  abbreviation "state_assn \<equiv> prod_assn id_assn (mtx_assn n)"

  sepref_definition subsumes_impl is
    "uncurry (RETURN oo subsumes)" :: "state_assn\<^sup>k *\<^sub>a state_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding subsumes_def by sepref

  (* XXX Somewhat peculiar use of the zero instance for DBM entries *)
  lemma init_dbm_alt_def:
    "init_dbm = op_asmtx_dfltNxN (Suc n) (Le 0)"
  unfolding init_dbm_def op_asmtx_dfltNxN_def zero_DBMEntry_def by auto

  lemma [sepref_import_param]: "(Le 0, PR_CONST (Le 0)) \<in> Id" by simp

  lemma [def_pat_rules]: "Le $ 0 \<equiv> PR_CONST (Le 0)" by simp

  sepref_register "PR_CONST (Le 0)"

  sepref_definition init_dbm_impl is
    "uncurry0 (RETURN (init_dbm :: nat \<times> nat \<Rightarrow> _))" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a (mtx_assn n)"
  unfolding init_dbm_alt_def by sepref
  
  lemmas [sepref_fr_rules] = init_dbm_impl.refine

  sepref_register l\<^sub>0

  lemma [sepref_import_param]: "(l\<^sub>0, l\<^sub>0) \<in> Id" by simp

  sepref_definition a\<^sub>0_imp is
    "uncurry0 (RETURN a\<^sub>0)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a state_assn"
  unfolding a\<^sub>0_def by sepref

  term F term F_rel

  code_thms "op \<in>" term List.member

  thm F_rel_def

  (* XXX Better implementation? *)
  lemma F_rel_alt_def:
    "F_rel = (\<lambda> (l, M). List.member F l  \<and> \<not> check_diag n M)"
  unfolding F_rel_def by (auto simp: List.member_def)

  sepref_register F

  lemma [sepref_import_param]: "(F, F) \<in> Id" by simp

  (* XXX Better implementation? *)
  lemma [sepref_import_param]: "(List.member, List.member) \<in> Id \<rightarrow> Id \<rightarrow> Id" by simp

  term check_diag_impl

  sepref_definition F_impl is
    "RETURN o F_rel" :: "state_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding F_rel_alt_def by sepref

  definition "inv_of_A = inv_of A"

  context
    notes [map_type_eqs] = map_type_eqI[of "TYPE(nat * nat \<Rightarrow> 'e)" "TYPE('e i_mtx)"]
  begin

  sepref_register trans_fun

  sepref_register abstr_upd

  sepref_register up_canonical_upd

  sepref_register reset'_upd FW' norm_upd

  sepref_register "PR_CONST (FW'' n)"

  sepref_register reset_canonical_upd

  sepref_register "PR_CONST (Reachability_Problem.inv_of_A A)"

  end

  definition "inv_map_assn B = pure (Id \<rightarrow> the_pure B)"

  lemma trans_fun_clock_bounds3:
    "\<forall> c \<in> collect_clks (inv_of A l). c \<le> n"
  using n_bounded collect_clks_inv_clk_set[of A l] unfolding X_def by auto

  lemma inv_of_rel:
    "(inv_of A l, inv_of A l) \<in> \<langle>\<langle>nbn_rel (Suc n), int_rel\<rangle>acconstraint_rel\<rangle>list_rel"
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
    with trans_fun_clock_bounds3 show ?thesis by auto
  qed

 (*
 lemma [sepref_fr_rules]:
  "inv_map_assn (list_assn (acconstraint_assn (clock_assn n) int_assn)) inv_of_A inv_of_A"
*)

 lemma [sepref_fr_rules]:
    shows "(return o inv_of_A, RETURN o PR_CONST inv_of_A) \<in> id_assn\<^sup>k \<rightarrow>\<^sub>a list_assn (acconstraint_assn (clock_assn n) int_assn)"
  using assms inv_of_rel
  apply (simp add: aconstraint_assn_pure_conv list_assn_pure_conv inv_map_assn_def inv_of_A_def)
  apply sepref_to_hoare
  apply (sep_auto simp: inv_map_assn_def pure_def)
  done
 

  term pure

  lemma [sepref_fr_rules]:
    assumes "CONSTRAINT (IS_PURE IS_BELOW_ID) B"
    shows "(return o inv_of, RETURN o inv_of) \<in> id_assn\<^sup>k \<rightarrow>\<^sub>a inv_map_assn (list_assn (acconstraint_assn (clock_assn n) int_assn))"
  using assms inv_of_rel
  apply sepref_to_hoare
  apply (sep_auto simp: IS_BELOW_ID_def IS_PURE_def inv_map_assn_def pure_def split: prod.split)
oops
(*  using assms by sepref_to_hoare (sep_auto simp: IS_BELOW_ID_def IS_PURE_def inv_map_assn_def pure_def) *)

  definition inv_map_lookup :: "('c \<Rightarrow> 'b) \<Rightarrow> _" where "inv_map_lookup M a = M a"

  lemma inv_map_lookup_fr_rule[sepref_fr_rules]:
    assumes "CONSTRAINT (IS_PURE IS_ID) B"
    shows
      "(uncurry (return oo inv_map_lookup), uncurry (RETURN oo inv_map_lookup))
      \<in> (inv_map_assn B)\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a B"
  using assms by sepref_to_hoare (sep_auto simp: IS_ID_def IS_PURE_def inv_map_assn_def pure_def)

  thm inv_map_lookup_fr_rule[to_hnr]

  term inv_of

  lemmas [sepref_fr_rules] = abstr_upd_impl.refine up_canonical_upd_impl.refine norm_upd_impl.refine

  print_statement abstr_upd_impl.refine[to_hnr]

  thm sepref_frame_normrel_eqs

  sepref_register inv_map_lookup

  term fw_impl term fw_impl'

  term "RETURN o (\<lambda> M. FW M n)"

  theorem FW_refine[sepref_fr_rules]:
    "(fw_impl n, RETURN o (\<lambda> M. FW M n)) \<in> (mtx_curry_assn n)\<^sup>d \<rightarrow>\<^sub>a mtx_curry_assn n"
  sorry

  term "(\<lambda> M. FW' M n)"

  term "\<lambda> M. RETURN (FW' M n)"

  term "(RETURN oo (\<lambda> M. FW' M n))"

  term "fw_impl n"

  theorem FW'_refine[sepref_fr_rules]:
    "(fw_impl n, \<lambda> M. RETURN (FW' M n)) \<in> (mtx_assn n)\<^sup>d \<rightarrow>\<^sub>a mtx_assn n"
  using FW_refine unfolding FW'_def sorry

  lemmas fw_impl.refine[sepref_fr_rules]

  lemmas [sepref_fr_rules] = fw_impl.refine[FCOMP fw_impl'_refine_FW'']

  lemma [def_pat_rules]: "FW'' $ (Reachability_Problem.n $ A) \<equiv> UNPROTECT (FW'' n)" by simp

  sepref_register "PR_CONST k'"

  lemma [sepref_import_param]: "(k', PR_CONST k') \<in> \<langle>Id\<rangle> list_rel" by simp

  lemma [def_pat_rules]: "(Reachability_Problem.k' $ A) \<equiv> PR_CONST k'" by simp

  term norm_upd
  thm norm_upd_impl.refine

  lemma [simp]:
    "length k' > n"
  by (simp add: k'_def)

  thm sepref_monadify_comb

  (* XXX Move to locale assumptions *)
  lemma trans_fun_clock_bounds1:
    "(g, a, r, l') \<in> set (trans_fun l) \<Longrightarrow> \<forall> c \<in> set r. c \<le> n"
  sorry

  term collect_clks

  lemma trans_fun_clock_bounds2:
    "(g, a, r, l') \<in> set (trans_fun l) \<Longrightarrow> \<forall> c \<in> collect_clks g. c \<le> n"
  sorry

  abbreviation "clock_rel \<equiv> nbn_rel (Suc n)"

  lemma [sepref_import_param]:
    "(trans_fun, trans_fun) \<in> Id \<rightarrow> \<langle>\<langle>\<langle>clock_rel, int_rel\<rangle> acconstraint_rel\<rangle> list_rel \<times>\<^sub>r Id \<times>\<^sub>r \<langle>clock_rel\<rangle> list_rel \<times>\<^sub>r Id\<rangle> list_rel"
  apply (rule fun_relI)
  apply simp
  subgoal for x x'
  proof -
    { fix l :: "((nat, int) acconstraint list \<times> 'a \<times> nat list \<times> 's) list"
      assume "\<forall> g a r l'. (g, a, r, l') \<in> set l \<longrightarrow> (\<forall> c \<in> collect_clks g. c \<le> n) \<and> (\<forall> c \<in> set r. c \<le> n)" 
      then have "(l, l) \<in> \<langle>\<langle>\<langle>nbn_rel (Suc n), int_rel\<rangle>acconstraint_rel\<rangle>list_rel \<times>\<^sub>r Id \<times>\<^sub>r \<langle>nbn_rel (Suc n)\<rangle>list_rel \<times>\<^sub>r Id\<rangle>list_rel"
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
        ultimately have "(x, x) \<in> \<langle>\<langle>nbn_rel (Suc n), int_rel\<rangle>acconstraint_rel\<rangle>list_rel \<times>\<^sub>r Id \<times>\<^sub>r \<langle>nbn_rel (Suc n)\<rangle>list_rel \<times>\<^sub>r Id" by simp
        moreover from Cons have
          "(xs, xs) \<in> \<langle>\<langle>\<langle>nbn_rel (Suc n), int_rel\<rangle>acconstraint_rel\<rangle>list_rel \<times>\<^sub>r Id \<times>\<^sub>r \<langle>nbn_rel (Suc n)\<rangle>list_rel \<times>\<^sub>r Id\<rangle>list_rel"
        by force
        ultimately show ?case by simp
      qed
    }
    from this[of "trans_fun x'"] trans_fun_clock_bounds1 trans_fun_clock_bounds2 show ?thesis by auto
  qed
  done

  lemma [sepref_fr_rules]:
    "(return o trans_fun, RETURN o trans_fun) \<in> id_assn\<^sup>k \<rightarrow>\<^sub>a list_assn (prod_assn (list_assn (acconstraint_assn (clock_assn n) int_assn)) (prod_assn id_assn (prod_assn id_assn id_assn)))"
  apply (simp add: list_assn_pure_conv)
  oops

  lemmas [sepref_fr_rules] = reset_canonical_upd_impl.refine
thm to_hnr_post(3)
  thm reset_canonical_upd_impl.refine[to_hnr]

  lemma b_rel_subtype[sepref_frame_match_rules]:
    "hn_val (b_rel P) a b \<Longrightarrow>\<^sub>t hn_val Id a b"
  by (rule enttI) (sep_auto simp: hn_ctxt_def pure_def)

  sepref_register op_HOL_list_empty

  term "a \<or>\<^sub>A b"

  lemma b_rel_subtype_merge[sepref_frame_merge_rules]:
    "hn_val (b_rel p) a b \<or>\<^sub>A hn_val Id a b \<Longrightarrow>\<^sub>t hn_val Id a b"
    "hn_val Id a b \<or>\<^sub>A hn_val (b_rel p) a b \<Longrightarrow>\<^sub>t hn_val Id a b"
  by (simp add: b_rel_subtype entt_disjE)+


  lemma [def_pat_rules]: "(Reachability_Problem.inv_of_A $ A) \<equiv> PR_CONST inv_of_A" by simp

  lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "asmtx_assn n a" for n a]

  sepref_definition succs_impl is
    "RETURN o succs" :: "state_assn\<^sup>k \<rightarrow>\<^sub>a list_assn state_assn"
  unfolding comp_def succs'_succs[symmetric] succs'_def inv_map_lookup_def[symmetric, of "inv_of A"]
  FW''_def[symmetric] rev_map_fold reset'_upd_def inv_of_A_def[symmetric]
  apply (rewrite "HOL_list.fold_custom_empty")
using [[goals_limit = 1]]
  apply sepref
done
oops
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans_keep
oops
  apply sepref_dbg_trans
  apply print_slot
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints
oops
  apply sepref_keep
  apply sepref_dbg_trans_keep
oops
  apply sepref_dbg_trans_step_keep
  apply sepref_dbg_frame
oops
  apply sepref_dbg_frame
oops
  apply sepref_dbg_trans_step_keep
oops
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_keep
  unfolding APP_def PROTECT2_def
using [[goals_limit = 1]]
  apply sepref_dbg_trans_keep
  apply sepref_dbg_trans_step_keep
  apply (tactic \<open>Sepref_Translate.side_unfold_tac @{context} 1\<close>)
  apply clarsimp
  ML_val Sepref_Translate.side_unfold_tac
  thm sepref.norm_rel_eqs
  apply sepref_dbg_frame
oops
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init

  apply sepref_dbg_id
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
oops
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
  apply sepref_dbg_id_step
oops
  apply sepref_keep

  definition dbm_subset' where
    "dbm_subset' = dbm_subset n"

  lemma subsumes_alt_def:
    "subsumes = (\<lambda> (l, M) (l', M'). l = l' \<and> dbm_subset' M M')"
  unfolding subsumes_def dbm_subset'_def by simp

  sepref_definition dbm_subset'_impl is
    "uncurry (RETURN oo PR_CONST dbm_subset')" :: "(mtx_assn n)\<^sup>k *\<^sub>a (mtx_assn n)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding dbm_subset'_def dbm_subset_alt_def[abs_def] list_all_foldli PR_CONST_def by sepref

  lemmas [sepref_fr_rules] = dbm_subset'_impl.refine

  sepref_register "PR_CONST dbm_subset'" :: "'e DBMEntry i_mtx \<Rightarrow> 'e DBMEntry i_mtx \<Rightarrow> bool"

  term n ML_val "@{term n}"

  lemma [def_pat_rules]: "Reachability_Problem.dbm_subset' $ A \<equiv> UNPROTECT dbm_subset'" by simp

  thm intf_of_assn

  sepref_definition subsumes_impl is
    "uncurry (RETURN oo subsumes)" :: "(prod_assn id_assn (mtx_assn n))\<^sup>k *\<^sub>a (prod_assn id_assn (mtx_assn n))\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding subsumes_alt_def by sepref
  apply sepref_keep
using [[goals_limit=1]]
  apply sepref_dbg_trans_keep
oops
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
oops
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints

oops
  apply sepref_keep
using [[goals_limit=3]]
  apply sepref_dbg_trans_keep
  oops
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
using [[goals_limit=3]]
  apply sepref_dbg_trans_keep
  apply sepref_dbg_tran

  sublocale Worklist1 E a\<^sub>0 F_rel subsumes succs
  apply standard
  unfolding succs_def E_def
  apply auto
  using trans_fun unfolding transition_rel_def transition_\<alpha>_def[abs_def] apply auto[]
  sorry

  sepref_definition dbm_subset_impl is
  "uncurry (RETURN oo dbm_subset n)" ::
  "mtx_assn\<^sup>k *\<^sub>a mtx_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
unfolding dbm_subset_alt_def[abs_def] list_all_foldli by sepref

end
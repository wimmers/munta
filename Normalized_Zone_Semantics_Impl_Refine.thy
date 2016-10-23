theory Normalized_Zone_Semantics_Impl_Refine
  imports
    Normalized_Zone_Semantics_Impl DBM_Operations_Impl_Refine
    "~~/src/HOL/Library/IArray"
    Code_Numeral
begin

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

  locale Reachability_Problem_Impl =
    Reachability_Problem A l\<^sub>0 F
    for A :: "('a, nat, int, 's) ta" and l\<^sub>0 :: 's and F :: "'s \<Rightarrow> bool" +

    fixes trans_fun :: "('a, nat, int, 's) transition_fun"
      and inv_fun :: "(nat, int, 's) invassn"
      and F_fun :: "'s \<Rightarrow> bool"
      and ceiling :: "int iarray"
    assumes trans_fun: "(trans_fun, trans_of A) \<in> transition_rel (state_set (trans_of A))"
        and inv_fun: "(inv_fun, inv_of A) \<in> inv_rel (state_set (trans_of A))"
        and F_fun: "(F_fun, F) \<in> inv_rel (state_set (trans_of A))"
        (* XXX *)
        and start_location_in_states[intro]: "l\<^sub>0 \<in> state_set (trans_of A)"
        and ceiling:
          "(uncurry0 (return ceiling), uncurry0 (RETURN k')) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a iarray_assn"
  begin

  lemma [sepref_fr_rules]:
    "(uncurry0 (return ceiling), uncurry0 (RETURN (PR_CONST k'))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a iarray_assn"
  using ceiling by auto

  (* XXX Should this be something different? *)
  abbreviation "states \<equiv> (state_set (trans_of A))"

  definition succs where
    "succs \<equiv> \<lambda> (l, D).
      (l, FW' (norm_upd (FW' (abstr_upd (inv_of A l) (up_canonical_upd (FW' (abstr_upd (inv_of A l) D) n) n)) n) k' n) n) #
      rev (map (\<lambda> (g,a,r,l'). (l', FW' (norm_upd (FW' (abstr_upd (inv_of A l') (reset'_upd (FW' (abstr_upd g D) n) n r 0)) n) k' n) n)) (trans_fun l))"

  definition succs' where
    "succs' \<equiv> \<lambda> (l, D). do
      {
        let delay = (l, FW' (norm_upd (FW' (abstr_upd (inv_of A l) (up_canonical_upd (FW' (abstr_upd (inv_of A l) (op_mtx_copy D)) n) n)) n) k' n) n);
        xs \<leftarrow> nfoldli (trans_fun l) (\<lambda> _. True) (\<lambda> (g,a,r,l') xs. do
          {
            let reset = fold (\<lambda>c M. reset_canonical_upd M n c 0) r (FW' (abstr_upd g (op_mtx_copy D)) n);
            let action = (l', FW' (norm_upd (FW' (abstr_upd (inv_of A l') reset) n) k' n) n);
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

  lemmas [sepref_fr_rules] = dbm_subset_impl.refine

  sepref_register "PR_CONST (dbm_subset n)" :: "'e DBMEntry i_mtx \<Rightarrow> 'e DBMEntry i_mtx \<Rightarrow> bool"

  lemma [def_pat_rules]:
    "dbm_subset $ (Reachability_Problem.n $ A) \<equiv> PR_CONST (dbm_subset n)"
  by simp

  abbreviation "location_rel \<equiv> b_rel Id (\<lambda> x. x \<in> state_set (trans_of A))"

  abbreviation "location_assn \<equiv> pure location_rel"

  abbreviation "state_assn \<equiv> prod_assn id_assn (mtx_assn n)"

  abbreviation "state_assn' \<equiv> prod_assn location_assn (mtx_assn n)"

  context
  begin

  lemma [sepref_import_param]:
    "(op =, op =) \<in> location_rel \<rightarrow> location_rel \<rightarrow> Id"
  by auto

  sepref_definition subsumes_impl is
    "uncurry (RETURN oo subsumes n)" :: "state_assn'\<^sup>k *\<^sub>a state_assn'\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding subsumes_def short_circuit_conv by sepref

  end

  (* XXX Somewhat peculiar use of the zero instance for DBM entries *)
  lemma init_dbm_alt_def:
    "init_dbm = op_amtx_dfltNxM (Suc n) (Suc n) (Le 0)"
  unfolding init_dbm_def op_amtx_dfltNxM_def zero_DBMEntry_def by auto

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
  using start_location_in_states by auto

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

  lemmas [sepref_fr_rules] = check_diag_impl.refine

  lemma [def_pat_rules]: "check_diag $ (Reachability_Problem.n $ A) \<equiv> PR_CONST (check_diag n)" by simp

  sepref_register "PR_CONST (check_diag n)" :: "'e DBMEntry i_mtx \<Rightarrow> bool"

  (* XXX Make implementation more efficient *)
  (* Check F_fun or empty diag first? *)
  sepref_definition F_impl is
    "RETURN o F_rel" :: "state_assn'\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding F_rel_alt_def short_circuit_conv by sepref

  definition "inv_of_A = inv_of A"

  context
    notes [map_type_eqs] = map_type_eqI[of "TYPE(nat * nat \<Rightarrow> 'e)" "TYPE('e i_mtx)"]
  begin

  sepref_register trans_fun

  sepref_register abstr_upd up_canonical_upd norm_upd reset'_upd reset_canonical_upd

  sepref_register "PR_CONST (FW'' n)"

  sepref_register "PR_CONST (Reachability_Problem_Impl.inv_of_A A)"

  end

  lemma trans_fun_clock_bounds3:
    "\<forall> c \<in> collect_clks (inv_of A l). c \<le> n"
  using n_bounded collect_clks_inv_clk_set[of A l] unfolding X_def by auto

  lemma inv_fun_rel:
    assumes "l \<in> state_set (trans_of A)"
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

  lemmas [sepref_fr_rules] = fw_impl.refine[FCOMP fw_impl'_refine_FW'']

  lemma [def_pat_rules]: "FW'' $ (Reachability_Problem.n $ A) \<equiv> UNPROTECT (FW'' n)" by simp

  sepref_register "PR_CONST k'"

  lemma [def_pat_rules]: "(Reachability_Problem.k' $ A) \<equiv> PR_CONST k'" by simp

  lemma [simp]:
    "length k' > n"
  by (simp add: k'_def)

  lemma trans_fun_trans_of[intro]:
    "(g, a, r, l') \<in> set (trans_fun l) \<Longrightarrow> l \<in> states \<Longrightarrow> A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"
  using trans_fun unfolding transition_rel_def by auto

  lemma trans_of_trans_fun[intro]:
    "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<Longrightarrow> l \<in> states \<Longrightarrow> (g, a, r, l') \<in> set (trans_fun l)"
  using trans_fun unfolding transition_rel_def by auto

  lemma trans_fun_clock_bounds1:
    "(g, a, r, l') \<in> set (trans_fun l) \<Longrightarrow> l \<in> states \<Longrightarrow> \<forall> c \<in> set r. c \<le> n"
  using n_bounded reset_clk_set[OF trans_fun_trans_of] unfolding X_def by fastforce

  lemma trans_fun_clock_bounds2:
    "(g, a, r, l') \<in> set (trans_fun l) \<Longrightarrow> l \<in> states \<Longrightarrow> \<forall> c \<in> collect_clks g. c \<le> n"
  using n_bounded collect_clocks_clk_set[OF trans_fun_trans_of] unfolding X_def by fastforce

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
      assume "\<forall> g a r l'. (g, a, r, l') \<in> set l \<longrightarrow> (\<forall> c \<in> collect_clks g. c \<le> n) \<and> (\<forall> c \<in> set r. c \<le> n) \<and> l' \<in> state_set (trans_of A)"
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

  lemmas [sepref_fr_rules] =
    abstr_upd_impl.refine up_canonical_upd_impl.refine norm_upd_impl.refine
    reset_canonical_upd_impl.refine

  sepref_register op_HOL_list_empty

  lemma b_rel_subtype[sepref_frame_match_rules]:
    "hn_val (b_rel R P) a b \<Longrightarrow>\<^sub>t hn_val R a b"
  by (rule enttI) (sep_auto simp: hn_ctxt_def pure_def)

  lemma b_rel_subtype_merge[sepref_frame_merge_rules]:
    "hn_val (b_rel R p) a b \<or>\<^sub>A hn_val R a b \<Longrightarrow>\<^sub>t hn_val R a b"
    "hn_val R a b \<or>\<^sub>A hn_val (b_rel R p) a b \<Longrightarrow>\<^sub>t hn_val R a b"
  by (simp add: b_rel_subtype entt_disjE)+

  lemma [def_pat_rules]: "(Reachability_Problem_Impl.inv_of_A $ A) \<equiv> PR_CONST inv_of_A" by simp

  lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "asmtx_assn n a" for n a]

  lemma n_pat: "Reachability_Problem.n $ A \<equiv> UNPROTECT n" by simp
  
  context
    notes [id_rules] = itypeI[of "PR_CONST n" "TYPE (nat)"]
      and [sepref_import_param] = IdI[of n]
      and [def_pat_rules] = n_pat
  begin

  sepref_definition succs_impl is
    "RETURN o succs" :: "state_assn'\<^sup>k \<rightarrow>\<^sub>a list_assn state_assn'"
  unfolding
    comp_def succs'_succs[symmetric] succs'_def
    FW''_def[symmetric] rev_map_fold reset'_upd_def inv_of_A_def[symmetric]
   apply (rewrite "HOL_list.fold_custom_empty")
  by sepref

  end (* End sepref setup *)

  lemma reachable_states:
    "reachable (l', M) \<Longrightarrow> l' \<in> states"
  unfolding reachable_def E_closure
  by (induction l \<equiv> l\<^sub>0 _ _ _ _ _  rule: steps_impl_induct) (auto elim: step_impl.cases)

  sublocale Worklist1 E a\<^sub>0 F_rel "subsumes n" succs
  apply standard
  apply (auto split: prod.split dest!: reachable_states)
   unfolding succs_def E_def apply (auto; fail)
  by (safe, erule step_impl.cases; force)

  sublocale Worklist2 E a\<^sub>0 F_rel "subsumes n" succs state_assn' succs_impl a\<^sub>0_impl F_impl subsumes_impl
    apply standard
    apply (unfold PR_CONST_def)
  by (rule a\<^sub>0_impl.refine F_impl.refine subsumes_impl.refine succs_impl.refine)+

end (* End of locale *)

context Reachability_Problem_precompiled
begin

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
    "(trans_fun, trans_of A) \<in> transition_rel (state_set (trans_of A))"
  using state_set_n unfolding transition_rel_def trans_of_def A_def T_def
  by (fastforce simp: trans_fun_alt_def)

  definition "inv_fun l \<equiv> (IArray inv) !! l"

  lemma inv_fun_inv_of[intro, simp]:
    "(inv_fun, inv_of A) \<in> inv_rel (state_set (trans_of A))"
  using state_set_n unfolding inv_rel_def inv_fun_def[abs_def] inv_of_def A_def I_def[abs_def]
  by auto

  definition "final_fun = List.member final"

  lemma final_fun_final[intro, simp]:
    "(final_fun, F) \<in> inv_rel (state_set (trans_of A))"
  using state_set_n unfolding F_def final_fun_def inv_rel_def by (auto simp: in_set_member)

  lemma start_states[intro, simp]:
    "0 \<in> state_set (trans_of A)"
  proof -
    obtain g r l' where "trans ! 0 ! 0 = (g, r, l')" by (metis prod_cases3)
    with start_has_trans n_gt_0 trans_length show ?thesis
    unfolding state_set_def trans_of_def A_def T_def label_def by force
  qed

  lemma num_clocks[simp]:
    "Reachability_Problem.n A = m"
  unfolding n_def X_def using clock_set by auto

  lemma fst_clkp_set'D:
    assumes "(c, d) \<in> clkp_set'"
    shows "c > 0" "c \<le> m" "d \<in> range int"
  using assms clock_set consts_nats unfolding Nats_def clk_set'_def by force+

  (* XXX Move *)
  lemma mono_nat:
    "mono nat"
  by rule auto

  lemma
    assumes "int n = y"
    shows "n = nat y"
  using assms by auto

  lemma k_ceiling':
    "\<forall>c\<in>{1..m}. k ! c = nat (Max ({d. (c, d) \<in> clkp_set'} \<union> {0}))"
  using k_ceiling by auto (* XXX *)

  lemma k_k'[intro]:
    "map int k = k'"
    apply (rule nth_equalityI)
     using k_length length_k' apply (auto; fail)
    unfolding k'_def k_def apply (simp add: clkp_set'_eq k_length default_ceiling_def del: upt_Suc)
    using k_ceiling' k_ceiling(2) apply safe
     subgoal for i by (cases "i = 0") auto
    apply (frule fst_clkp_set'D(1))
    apply clarsimp
    apply (rule cong[of nat, OF HOL.refl])
    apply (subst Max_insert)
    using finite_clkp_set_A [[simproc add: finite_Collect]]
    apply (auto intro: finite_Image simp: clkp_set'_eq; fail)
    apply (auto; fail)
    subgoal for i
     using Max_in[of "{d. (i, d) \<in> clkp_set'}"] fst_clkp_set'D(3) finite_clkp_set_A
    by (force intro: finite_Image simp: clkp_set'_eq)
    done

  lemma iarray_k'[intro]:
    "(uncurry0 (return (IArray (map int k))), uncurry0 (RETURN k')) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a iarray_assn"
  unfolding br_def by sepref_to_hoare sep_auto

  sublocale Reachability_Problem_Impl A 0 "PR_CONST F" trans_fun inv_fun final_fun "IArray k"
    apply standard
  using iarray_k' by auto

  lemma F_reachable_correct:
    "F_reachable
    \<longleftrightarrow> (\<exists> l' u u'. conv_A A \<turnstile> \<langle>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> l' \<in> set final)"
  unfolding F_reachable_def reachable_def using reachability_check unfolding F_def by auto

  definition
    "reachability_checker \<equiv> worklist_algo2 subsumes_impl a\<^sub>0_impl F_impl succs_impl"

  theorem reachability_check:
    "(uncurry0 reachability_checker,
      uncurry0 (
        RETURN (\<exists> l' u u'. conv_A A \<turnstile> \<langle>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> l' \<in> set final)
      )
     ) 
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  using hnr_F_reachable unfolding reachability_checker_def F_reachable_correct .

  corollary reachability_checker_hoare:
    "<emp> reachability_checker
    <\<lambda> r. \<up>(r \<longleftrightarrow> (\<exists> l' u u'. conv_A A \<turnstile> \<langle>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> l' \<in> set final))>\<^sub>t"
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
    val u1 = @{term "IArray (map int k)"};
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
   apply (tactic \<open>pull_tac @{term "IArray (map int k)"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "inv_fun"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "trans_fun"} @{context}\<close>)
   unfolding inv_fun_def[abs_def] trans_fun_def[abs_def]
   apply (tactic \<open>pull_tac @{term "IArray inv"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "IArray trans_map"} @{context}\<close>)
  by (rule Pure.reflexive)

  lemma reachability_checker_alt_def':
    "reachability_checker \<equiv>
      let
        sub = subsumes_impl;
        start = a\<^sub>0_impl;
        final = F_impl;
        succs = succs_impl
      in worklist_algo2 sub start final succs"
  unfolding reachability_checker_def by simp

  schematic_goal reachability_checker_alt_def:
    "reachability_checker \<equiv> ?impl"
  unfolding reachability_checker_alt_def' succs_impl_def
   apply (tactic \<open>pull_tac @{term "IArray (map int k)"} @{context}\<close>)
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
   unfolding num_clocks
  by (rule Pure.reflexive)

  schematic_goal reachability_checker_alt_def:
    "reachability_checker \<equiv> ?impl"
  unfolding succs_impl_def reachability_checker_def
   apply (tactic \<open>pull_tac @{term "IArray (map int k)"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "inv_fun"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "trans_fun"} @{context}\<close>)
   unfolding inv_fun_def[abs_def] trans_fun_def[abs_def]
   apply (tactic \<open>pull_tac @{term "IArray inv"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "IArray trans_map"} @{context}\<close>)
   unfolding num_clocks
  oops

end (* End of locale *)

subsection \<open>Check preconditions\<close>
context Reachability_Problem_precompiled_defs
begin

  abbreviation
    "check_nat_subs \<equiv> \<forall> (_, d) \<in> clkp_set'. d \<ge> 0"

  lemma check_nat_subs:
    "check_nat_subs \<longleftrightarrow> snd ` clkp_set' \<subseteq> \<nat>"
  unfolding Nats_def apply safe
  subgoal for _ _ b using rangeI[of int "nat b"] by auto
  by auto

  definition
    "check_pre \<equiv>
      length inv = n \<and> length trans = n \<and> length k = m + 1 \<and> m > 0 \<and> n > 0 \<and> trans ! 0 \<noteq> []
      \<and> k ! 0 = 0 \<and> check_nat_subs \<and> clk_set' = {1..m}
      \<and> (\<forall> xs \<in> set trans. \<forall> (_, _, l) \<in> set xs. l < n)"

  abbreviation
    "check_k_in c \<equiv> k ! c = 0 \<or> (c, k ! c) \<in> clkp_set'"

  definition
    "check_ceiling \<equiv>
      (\<forall> (c, d) \<in> clkp_set'. 0 < c \<and> c \<le> m \<longrightarrow> k ! c \<ge> d) \<and> (\<forall> c \<in> {1..m}. check_k_in c)"

  lemma finite_clkp_set'[intro, simp]:
    "finite clkp_set'"
  unfolding clkp_set'_def by auto

  lemma check_ceiling:
    "check_ceiling \<longleftrightarrow> (\<forall> c \<in> {1..m}. k ! c = Max ({d. (c, d) \<in> clkp_set'} \<union> {0 :: int}))"
  unfolding check_ceiling_def
  proof (safe, goal_cases)
    case prems: (1 c)
    then show ?case
     apply -
     apply (rule HOL.sym)
     apply (rule Max_eqI)
    using [[simproc add: finite_Collect]] by (auto intro: finite_Image)
  next
    case prems: (2 a b)
    then show ?case
      apply simp
      apply (rule Max_ge)
    using [[simproc add: finite_Collect]] by (auto intro: finite_Image)
  next
    case prems: (3 c)
    with Max_in[of "{d. (c, d) \<in> clkp_set'} \<union> {0}"] show ?case
    using [[simproc add: finite_Collect]] by (force intro: finite_Image)
  qed

  lemma check_axioms:
    "Reachability_Problem_precompiled n m k inv trans \<longleftrightarrow> check_pre \<and> check_ceiling"
  unfolding Reachability_Problem_precompiled_def check_ceiling check_pre_def check_nat_subs by auto

end

lemmas Reachability_Problem_precompiled_defs.check_axioms[code]

lemmas Reachability_Problem_precompiled_defs.clkp_set'_def[code]

lemmas Reachability_Problem_precompiled_defs.clk_set'_def[code]

lemmas Reachability_Problem_precompiled_defs.check_pre_def[code]

lemmas Reachability_Problem_precompiled_defs.check_ceiling_def[code]

export_code Reachability_Problem_precompiled in SML module_name Test

concrete_definition succs_impl' uses Reachability_Problem_precompiled.succs_impl_alt_def

thm succs_impl'_def succs_impl'.refine

concrete_definition reachability_checker_impl
  uses Reachability_Problem_precompiled.reachability_checker_alt_def

export_code reachability_checker_impl in SML_imp module_name TA

thm reachability_checker_impl_def reachability_checker_impl.refine

term Reachability_Problem_precompiled.reachability_checker

definition [code]:
  "check_and_verify n m k I T final \<equiv>
    if Reachability_Problem_precompiled n m k I T
    then reachability_checker_impl m k I T final \<bind> (\<lambda> x. return (Some x))
    else return None"

lemmas [sep_heap_rules] = Reachability_Problem_precompiled.reachability_checker_hoare

theorem reachability_check:
  "(uncurry0 (check_and_verify n m k I T final),
    uncurry0 (
       RETURN (
        if (Reachability_Problem_precompiled n m k I T)
        then Some (
          \<exists> l' u u'.
            conv_A (Reachability_Problem_precompiled_defs.A n I T) \<turnstile> \<langle>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>
            \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> l' \<in> set final
          )
        else None
        
       )
    )
   ) 
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
by sepref_to_hoare (sep_auto simp: reachability_checker_impl.refine[symmetric] check_and_verify_def)

export_code open check_and_verify checking SML_imp

end (* End of theory *)
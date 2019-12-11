theory Unreachability_Certification2
  imports
    Unreachability_Misc
    TA_Library.Abstract_Term
    "HOL-Library.Parallel"
    "HOL-ex.Sketch_and_Explore"
begin

hide_const (open) list_set_rel

lemma monadic_list_all_mono:
  "monadic_list_all P xs \<le> monadic_list_all Q ys" if "list_all2 (\<lambda> x y. P x \<le> Q y) xs ys"
proof -
  have "nfoldli xs id (\<lambda>x _. P x) a \<le> nfoldli ys id (\<lambda>x _. Q x) a" for a
    using that by (induction xs ys arbitrary: a; clarsimp; refine_mono)
  then show ?thesis
    unfolding monadic_list_all_def .
qed

lemma monadic_list_all_mono':
  "monadic_list_all P xs \<le> monadic_list_all Q ys"
  if "(xs, ys) \<in> \<langle>R\<rangle>list_rel" "\<And> x y. (x, y) \<in> R \<Longrightarrow> P x \<le> Q y"
   using that by (intro monadic_list_all_mono) (auto simp: list_all2_iff list_rel_def)

lemma monadic_list_ex_mono:
  "monadic_list_ex P xs \<le> monadic_list_ex Q ys" if "list_all2 (\<lambda> x y. P x \<le> Q y) xs ys"
proof -
  have "nfoldli xs Not (\<lambda>x _. P x) a \<le> nfoldli ys Not (\<lambda>x _. Q x) a" for a
    using that by (induction xs ys arbitrary: a; clarsimp; refine_mono)
  then show ?thesis
    unfolding monadic_list_ex_def .
qed

lemma monadic_list_ex_mono':
  "monadic_list_ex P xs \<le> monadic_list_ex Q ys"
  if "(xs, ys) \<in> \<langle>R\<rangle>list_rel" "\<And> x y. (x, y) \<in> R \<Longrightarrow> P x \<le> Q y"
  using that by (intro monadic_list_ex_mono) (auto simp: list_all2_iff list_rel_def)

lemma monadic_list_all_rule':
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> Pi x \<le> SPEC (\<lambda>r. r \<longleftrightarrow> P x)"
  shows "monadic_list_all Pi xs \<le> SPEC (\<lambda>r. r \<longleftrightarrow> list_all P xs)"
  using assms unfolding monadic_list_all_def
  by (intro nfoldli_rule[where I = "\<lambda>as bs b. b = list_all P as \<and> set (as @ bs) = set xs"]) auto

lemma case_prod_mono:
  "(case x of (a, b) \<Rightarrow> f a b) \<le> (case y of (a, b) \<Rightarrow> g a b)"
  if "(x, y) \<in> K \<times>\<^sub>r A" "\<And>ai bi a b. (ai, a) \<in> K \<Longrightarrow> (bi, b) \<in> A \<Longrightarrow> f ai bi \<le> g a b" for x y f g
  using that unfolding prod_rel_def by auto

definition list_set_rel where [to_relAPP]:
  "list_set_rel R \<equiv> \<langle>R\<rangle>list_rel O {(xs, S). set xs = S}"

lemma list_set_relE:
  assumes "(xs, zs) \<in> \<langle>R\<rangle>list_set_rel"
  obtains ys where "(xs, ys) \<in> \<langle>R\<rangle>list_rel" "set ys = zs"
  using assms unfolding list_set_rel_def by auto

lemma list_set_rel_Nil[simp, intro]:
  "([], {}) \<in> \<langle>Id\<rangle>list_set_rel"
  unfolding list_set_rel_def by auto

lemma specify_right:
  "c \<le> SPEC P \<bind> c'" if "P x" "c \<le> c' x"
  using that by (auto intro: SUP_upper2[where i = x] simp: bind_RES)

lemma res_right:
  "c \<le> RES S \<bind> c'" if "x \<in> S" "c \<le> c' x"
  using that by (auto intro: SUP_upper2[where i = x] simp: bind_RES)

lemma nres_relD:
  "c \<le> \<Down>R a" if "(c, a) \<in> \<langle>R\<rangle>nres_rel"
  using that unfolding nres_rel_def by simp

lemma list_rel_setE1:
  assumes "x \<in> set xs" "(xs, ys) \<in> \<langle>R\<rangle>list_rel"
  obtains y where "y \<in> set ys" "(x, y) \<in> R"
  using assms unfolding list_rel_def by (auto dest!: list_all2_set1)

lemma list_rel_setE2:
  assumes "y \<in> set ys" "(xs, ys) \<in> \<langle>R\<rangle>list_rel"
  obtains x where "x \<in> set xs" "(x, y) \<in> R"
  using assms unfolding list_rel_def by (auto dest!: list_all2_set2)

lemma list_of_set_impl[autoref_rules]:
  "(\<lambda>xs. RETURN xs, list_of_set) \<in> \<langle>R\<rangle>list_set_rel \<rightarrow> \<langle>\<langle>R\<rangle>list_rel\<rangle>nres_rel"
  unfolding list_of_set_def by refine_rcg (auto elim!: list_set_relE intro: RETURN_SPEC_refine)

lemma case_option_mono:
  "(case x of None \<Rightarrow> a | Some x' \<Rightarrow> f x', case y of None \<Rightarrow> b | Some x' \<Rightarrow> g x') \<in> R"
  if "(x, y) \<in> \<langle>S\<rangle>option_rel" "(a, b) \<in> R" "(f, g) \<in> S \<rightarrow> R"
  by (metis fun_relD2 param_case_option' that)

lemmas case_option_mono' =
  case_option_mono[where R = "\<langle>R\<rangle>nres_rel" for R, THEN nres_relD, THEN refine_IdD]

lemma bind_mono:
  assumes "m \<le> \<Down> R m'"
    and "\<And>x y. (x, y) \<in> R \<Longrightarrow> f x \<le> f' y"
  shows "Refine_Basic.bind m f \<le> m' \<bind> f'"
  using assms by (force simp: refine_pw_simps pw_le_iff)

lemma list_all_split:
  assumes "set xs = (\<Union>xs \<in> set split. set xs)"
  shows "list_all P xs = list_all id (map (list_all P) split)"
  unfolding list_all_iff using assms by auto

lemma list_all_default_split:
  "list_all P xs = list_all id (map P xs)"
  unfolding list_all_iff by auto


locale Reachability_Impl_pure_base =
  Reachability_Impl_pre where less_eq = less_eq and M = M
  for less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<preceq>" 50) and M :: "'k \<Rightarrow> 'a set" +
  fixes get_succs and K and A and Li and lei and Pi and Fi
    and Li_split :: "'ki list list"
  assumes K_right_unique: "single_valued K"
  assumes K_left_unique:  "single_valued (K\<inverse>)"
  assumes Li_L: "(Li, L) \<in> \<langle>K\<rangle>list_set_rel"
  assumes lei_less_eq: "(lei, less_eq) \<in> A \<rightarrow> A \<rightarrow> bool_rel"
  assumes get_succs_succs[param]:
    "(get_succs, succs) \<in> K \<rightarrow> \<langle>A\<rangle>list_set_rel \<rightarrow> \<langle>K \<times>\<^sub>r \<langle>A\<rangle>list_set_rel\<rangle>list_rel"
  assumes Pi_P'[refine,param]: "(Pi, P') \<in> K \<times>\<^sub>r A \<rightarrow> bool_rel"
  assumes Fi_F[refine]: "(Fi, F) \<in> K \<times>\<^sub>r A \<rightarrow> bool_rel"
  assumes full_split: "set Li = (\<Union>xs \<in> set Li_split. set xs)"
begin

lemma lei_refine[refine_mono]:
  \<open>RETURN (lei a b) \<le> RETURN (a' \<preceq> b')\<close> if \<open>(a, a') \<in> A\<close> \<open>(b, b') \<in> A\<close>
  using that using lei_less_eq by simp (metis pair_in_Id_conv tagged_fun_relD_both)

definition list_all_split :: "_ \<Rightarrow> 'ki list \<Rightarrow> bool" where [simp]:
  "list_all_split = list_all"

definition monadic_list_all_split :: "_ \<Rightarrow> 'ki list \<Rightarrow> bool nres" where [simp]:
  "monadic_list_all_split = monadic_list_all"

lemmas pure_unfolds =
  monadic_list_all_RETURN[where 'a = 'ki, folded monadic_list_all_split_def list_all_split_def]
  monadic_list_ex_RETURN monadic_list_all_RETURN monadic_list_ex_RETURN
  nres_monad1 option.case_distrib[where h = RETURN, symmetric]
  if_distrib[where f = RETURN, symmetric] prod.case_distrib[where h = RETURN, symmetric]

lemma list_all_split:
  "list_all_split Q Li = list_all id (Parallel.map (list_all Q) Li_split)"
  unfolding list_all_split_def list_all_split[OF full_split, symmetric] Parallel.map_def ..

end


locale Reachability_Impl_pure =
  Reachability_Impl_common where M = M +
  Reachability_Impl_pure_base where M = "\<lambda>x. case M x of None \<Rightarrow> {} | Some S \<Rightarrow> S" +
  Reachability_Impl_pre_start where M = "\<lambda>x. case M x of None \<Rightarrow> {} | Some S \<Rightarrow> S"
  for M :: "'k \<Rightarrow> 'a set option" +
  fixes Mi l\<^sub>0i s\<^sub>0i
  assumes Mi_M[param]: "(Mi, M) \<in> K \<rightarrow> \<langle>\<langle>A\<rangle>list_set_rel\<rangle>option_rel"
  assumes l\<^sub>0i_l\<^sub>0[refine,param]: "(l\<^sub>0i, l\<^sub>0) \<in> K"
      and s\<^sub>0i_s\<^sub>0[refine,param,refine_mono]: "(s\<^sub>0i, s\<^sub>0) \<in> A"
begin

paragraph \<open>Refinement\<close>

definition "check_invariant1 L' \<equiv>
do {
  monadic_list_all_split (\<lambda>l.
    case Mi l of
      None \<Rightarrow> RETURN True
    | Some as \<Rightarrow> do {
        let succs = get_succs l as;
        monadic_list_all (\<lambda>(l', xs).
        do {
          if xs = [] then RETURN True
          else do {
            case Mi l' of
              None \<Rightarrow> RETURN False
            | Some ys \<Rightarrow> monadic_list_all (\<lambda>x.
              monadic_list_ex (\<lambda>y. RETURN (lei x y)) ys
            ) xs
          }
        }
        ) succs
      }
  ) L'
}
"

lemma Mi_M_None_iff[simp]:
  "M l = None \<longleftrightarrow> Mi li = None" if "(li, l) \<in> K"
proof -
  from that have "(Mi li, M l) \<in> \<langle>\<langle>A\<rangle>list_set_rel\<rangle>option_rel"
    by parametricity
  then show ?thesis
    by auto
qed

lemma check_invariant1_refine[refine]:
  "check_invariant1 L1 \<le> check_invariant L'"
  if "(L1, L') \<in> \<langle>K\<rangle>list_rel" "L = dom M" "set L' \<subseteq> L"
  unfolding check_invariant1_def check_invariant_def Let_def monadic_list_all_split_def
  apply (refine_rcg monadic_list_all_mono' refine_IdI that)
  apply (clarsimp split: option.splits simp: succs_empty; safe)
   apply (simp flip: Mi_M_None_iff; fail)
  apply (refine_rcg monadic_list_all_mono')
   apply parametricity
  subgoal
    using Mi_M by (auto dest!: fun_relD1)
  apply (clarsimp split: option.splits; safe)
       apply (
      elim list_set_relE specify_right;
      auto simp: monadic_list_all_False intro!: res_right simp flip: Mi_M_None_iff; fail)+
  subgoal premises prems for _ _ _ _ li _ l _ S xsi
  proof -
    have *: \<open>li \<in> set Li \<longleftrightarrow> l \<in> L\<close> if \<open>(li, l) \<in> K\<close>
      using that using Li_L K_left_unique K_right_unique
      by (auto dest: single_valuedD elim: list_rel_setE1 list_rel_setE2 elim!: list_set_relE)
    have [simp]: "l \<in> L"
      using prems(6) that(2) by blast
    from prems have "(Mi li, M l) \<in> \<langle>\<langle>A\<rangle>list_set_rel\<rangle>option_rel"
      by parametricity
    with prems have "(xsi, S) \<in> \<langle>A\<rangle>list_set_rel"
      by auto
    then obtain xs where "(xsi, xs) \<in> \<langle>A\<rangle>list_rel" "set xs = S"
      by (elim list_set_relE)
    with prems show ?thesis
      apply (elim list_set_relE, elim specify_right)
      apply (clarsimp, safe)
       apply (auto; fail)
      apply (rule specify_right[where x = xs], rule HOL.refl)
      supply [refine_mono] = monadic_list_all_mono' monadic_list_ex_mono'
      apply refine_mono
      done
  qed
  done

definition check_prop1 where
  "check_prop1 L' M' = do {
  l \<leftarrow> RETURN L';
  monadic_list_all (\<lambda>l. do {
    let S = op_map_lookup l M';
    case S of None \<Rightarrow> RETURN True | Some S \<Rightarrow> do {
      xs \<leftarrow> RETURN S;
      r \<leftarrow> monadic_list_all (\<lambda>s.
        RETURN (Pi (l, s))
      ) xs;
      RETURN r
    }
    }
  ) l
  }"

lemma check_prop1_refine:
  "(check_prop1, check_prop') \<in> \<langle>K\<rangle>list_set_rel \<rightarrow> (K \<rightarrow> \<langle>\<langle>A\<rangle>list_set_rel\<rangle>option_rel) \<rightarrow> \<langle>Id\<rangle>nres_rel"
  supply [refine] =
    list_of_set_impl[THEN fun_relD, THEN nres_relD] monadic_list_all_mono' case_option_mono'
  supply [refine_mono] =
    monadic_list_all_mono' list_of_set_impl[THEN fun_relD, THEN nres_relD]
  unfolding check_prop1_def check_prop'_def list_of_set_def[symmetric] Let_def op_map_lookup_def
  apply refine_rcg
   apply assumption
  apply (refine_rcg refine_IdI, assumption)
   apply parametricity
  apply (rule bind_mono)
   apply refine_mono+
  using Pi_P'
  apply (auto simp add: prod_rel_def dest!: fun_relD)
  done

lemma [refine]:
  "(Mi l\<^sub>0i \<noteq> None, l\<^sub>0 \<in> L) \<in> bool_rel" if "L = dom M"
  using that by (auto simp: Mi_M_None_iff[symmetric, OF l\<^sub>0i_l\<^sub>0])

lemma [refine]:
  "(Pi (l\<^sub>0i, s\<^sub>0i), P' (l\<^sub>0, s\<^sub>0)) \<in> bool_rel"
  by parametricity

definition
  "check_all_pre1 \<equiv> do {
  b1 \<leftarrow> RETURN (Mi l\<^sub>0i \<noteq> None);
  b2 \<leftarrow> RETURN (Pi (l\<^sub>0i, s\<^sub>0i));
  case Mi l\<^sub>0i of
    None \<Rightarrow> RETURN False
  | Some xs \<Rightarrow> do {
    b3 \<leftarrow> monadic_list_ex (\<lambda>s. RETURN (lei s\<^sub>0i s)) xs;
    b4 \<leftarrow> check_prop1 Li Mi;
    RETURN (b1 \<and> b2 \<and> b3 \<and> b4)
  }
  }"

lemma check_all_pre1_refine[refine]:
  "(check_all_pre1, check_all_pre l\<^sub>0 s\<^sub>0) \<in> \<langle>bool_rel\<rangle>nres_rel" if "L = dom M"
proof (cases "M l\<^sub>0")
  case None
  then show ?thesis
    using that check_prop_gt_SUCCEED l\<^sub>0i_l\<^sub>0 unfolding check_all_pre1_def check_all_pre_def
    by (refine_rcg) (simp flip: Mi_M_None_iff add: bind_RES; cases "check_prop P'"; simp)
next
  case (Some S)
  have "(Mi l\<^sub>0i, M l\<^sub>0) \<in> \<langle>\<langle>A\<rangle>list_set_rel\<rangle>option_rel"
    by parametricity
  with \<open>M l\<^sub>0 = _\<close> obtain xs ys where "Mi l\<^sub>0i = Some xs" "(xs, ys) \<in> \<langle>A\<rangle>list_rel" "set ys = S"
    unfolding option_rel_def by (auto elim: list_set_relE)
  with \<open>M l\<^sub>0 = _\<close> show ?thesis
    unfolding check_all_pre1_def check_all_pre_def
    apply (refine_rcg that; simp)
    supply [refine_mono] =
      monadic_list_ex_mono' monadic_list_ex_RETURN_mono specify_right HOL.refl
      check_prop1_refine[THEN fun_relD, THEN fun_relD, THEN nres_relD, THEN refine_IdD,
        of Li L Mi M, unfolded check_prop_alt_def]
      Li_L Mi_M
    apply refine_mono
    done
qed

definition
  "check_all1 \<equiv> do {
  b \<leftarrow> check_all_pre1;
  if b
  then do {
    r \<leftarrow> check_invariant1 Li;
    PRINT_CHECK STR ''State set invariant check'' r;
    RETURN r
  }
  else RETURN False
  }
"

lemma check_all1_correct[refine]:
  "check_all1 \<le> SPEC (\<lambda>r. r \<longrightarrow> check_all_pre_spec l\<^sub>0 s\<^sub>0 \<and> check_invariant_spec L)" if "L = dom M"
proof -
  from check_all_pre1_refine[THEN nres_relD, OF that] have "check_all_pre1 \<le> check_all_pre l\<^sub>0 s\<^sub>0"
    by (rule refine_IdD)
  also note check_all_pre_correct
  finally have [refine]: "check_all_pre1 \<le> SPEC (\<lambda>r. r \<longrightarrow> check_all_pre_spec l\<^sub>0 s\<^sub>0)"
    by (rule order.trans) simp
  obtain L' where "(Li, L') \<in> \<langle>K\<rangle>list_rel" "set L' = L"
    using Li_L by (elim list_set_relE)
  note check_invariant1_refine
  also note check_invariant_correct
  also have [refine]: "check_invariant1 Li \<le> SPEC (\<lambda>r. r \<longrightarrow> check_invariant_spec L)"
    if "check_all_pre_spec l\<^sub>0 s\<^sub>0"
    apply (subst (2) \<open>_ = L\<close>[symmetric])
    apply (rule calculation)
    using Li_L \<open>(Li, L') \<in> _\<close> that unfolding check_all_pre_spec_def
    by (auto simp: \<open>_ = L\<close> \<open>L = _\<close> dest: P'_P)
  show ?thesis
    unfolding check_all1_def PRINT_CHECK_def comp_def by (refine_vcg; simp)
qed

definition
  "check_final1 L' = do {
  monadic_list_all (\<lambda>l. do {
    case op_map_lookup l Mi of None \<Rightarrow> RETURN True | Some xs \<Rightarrow> do {
      monadic_list_all (\<lambda>s.
        RETURN (\<not> PR_CONST Fi (l, s))
      ) xs
    }
    }
  ) L'
  }"

lemma check_final1_refine:
  "check_final1 Li \<le> check_final' L M"
    using Li_L apply (elim list_set_relE)
  unfolding check_final1_def check_final'_def
  apply (erule specify_right)
  supply [refine_mono] = monadic_list_all_mono'
  apply refine_mono
  apply (clarsimp split: option.splits)
  apply (refine_rcg monadic_list_all_mono')
   apply (simp flip: Mi_M_None_iff; fail)
  subgoal premises prems for _ li l xsi S
  proof -
    from \<open>(li, l) \<in> K\<close> have "(Mi li, M l) \<in> \<langle>\<langle>A\<rangle>list_set_rel\<rangle>option_rel"
      by parametricity
    with prems have "(xsi, S) \<in> \<langle>A\<rangle>list_set_rel"
      by auto
    then obtain xs where "(xsi, xs) \<in> \<langle>A\<rangle>list_rel" "set xs = S"
      by (elim list_set_relE)
    then show ?thesis
      using Fi_F \<open>(li, l) \<in> K\<close>
      by (refine_rcg monadic_list_all_mono' specify_right) (auto dest!: fun_relD)
  qed
  done

definition
  "certify_unreachable1 = do {
    b1 \<leftarrow> check_all1;
    b2 \<leftarrow> check_final1 Li;
    RETURN (b1 \<and> b2)
  }"

lemma certify_unreachable1_correct:
  "certify_unreachable1 \<le> SPEC (\<lambda>r. r \<longrightarrow> (\<nexists>s'. E\<^sup>*\<^sup>* (l\<^sub>0, s\<^sub>0) s' \<and> F s'))" if "L = dom M"
proof -
  note check_final1_refine[unfolded check_final_alt_def]
  also note check_final_correct
  finally have [refine]: "check_final1 Li \<le> SPEC (\<lambda>r. r = check_final_spec)" .
  show ?thesis
    unfolding certify_unreachable1_def
    by (refine_vcg that certify_unreachableI[THEN mp]; simp)
qed

paragraph \<open>Synthesizing a pure program via rewriting\<close>

lemma check_final1_alt_def:
  "check_final1 L' = RETURN (list_all_split
    (\<lambda>l. case op_map_lookup l Mi of None \<Rightarrow> True | Some xs \<Rightarrow> list_all (\<lambda>s. \<not> Fi (l, s)) xs) L')"
  unfolding check_final1_def
  unfolding monadic_list_all_RETURN[symmetric] list_all_split_def
  by (fo_rule arg_cong2, intro ext)
     (auto split: option.splits simp: monadic_list_all_RETURN[symmetric])

concrete_definition check_final_impl
  uses check_final1_alt_def is "_ = RETURN ?f"

schematic_goal check_prop1_alt_def:
  "check_prop1 L' M' \<equiv> RETURN ?f"
  unfolding check_prop1_def pure_unfolds Let_def .

concrete_definition check_prop_impl uses check_prop1_alt_def is "_ \<equiv> RETURN ?f"

schematic_goal check_all_pre1_alt_def:
  "check_all_pre1 \<equiv> RETURN ?f"
  unfolding check_all_pre1_def check_prop_impl.refine pure_unfolds .

concrete_definition check_all_pre_impl uses check_all_pre1_alt_def is "_ \<equiv> RETURN ?f" 

schematic_goal check_invariant1_alt_def:
  "check_invariant1 Li \<equiv> RETURN ?f"
  unfolding check_invariant1_def Let_def pure_unfolds .

concrete_definition check_invariant_impl uses check_invariant1_alt_def is "_ \<equiv> RETURN ?f"

schematic_goal certify_unreachable1_alt_def:
  "certify_unreachable1 \<equiv> RETURN ?f"
  unfolding
    certify_unreachable1_def check_all1_def check_final_impl.refine check_all_pre_impl.refine
    check_invariant_impl.refine
    pure_unfolds PRINT_CHECK_def comp_def short_circuit_conv if_bool_simps
  .

concrete_definition certify_unreachable_impl_pure1
  uses certify_unreachable1_alt_def is "_ \<equiv> RETURN ?f"

text \<open>This is where we add parallel execution:\<close>

schematic_goal certify_unreachable_impl_pure1_alt_def:
  "certify_unreachable_impl_pure1 \<equiv> ?f"
  unfolding certify_unreachable_impl_pure1_def
  apply (abstract_let check_invariant_impl check_invariant)
  apply (abstract_let "check_final_impl Li" check_final)
  apply (abstract_let check_all_pre_impl check_all_pre_impl)
  apply (time_it "STR ''Time for state set preconditions check''" check_all_pre_impl)
  apply (time_it "STR ''Time for state space invariant check''"   check_invariant_impl)
  apply (time_it "STR ''Time to check final state predicate''"    "check_final_impl Li")
  unfolding
    check_invariant_impl_def check_all_pre_impl_def
    check_prop_impl_def check_final_impl_def
    list_all_split
  apply (subst list_all_default_split[where xs = Li, folded Parallel.map_def])
  .

concrete_definition (in -) certify_unreachable_impl_pure
  uses Reachability_Impl_pure.certify_unreachable_impl_pure1_alt_def is "_ \<equiv> ?f"

theorem certify_unreachable_impl_pure_correct:
  "certify_unreachable_impl_pure get_succs Li lei Pi Fi Li_split Mi l\<^sub>0i s\<^sub>0i
  \<longrightarrow> (\<nexists>s'. E\<^sup>*\<^sup>* (l\<^sub>0, s\<^sub>0) s' \<and> F s')"
  if "L = dom M"
  using certify_unreachable1_correct that
  unfolding
    certify_unreachable_impl_pure1.refine
    certify_unreachable_impl_pure.refine[OF Reachability_Impl_pure_axioms]
  by simp

end (* Reachability_Impl_pure *)


locale Buechi_Impl_pure =
  Buechi_Impl_pre where M = "\<lambda>x. case M x of None \<Rightarrow> {} | Some S \<Rightarrow> S" +
  Reachability_Impl_pure_base where M = "\<lambda>l. fst ` (\<lambda>x. case M x of None \<Rightarrow> {} | Some S \<Rightarrow> S) l"
  for M :: "'k \<Rightarrow> ('a \<times> nat) set option" +
  fixes Mi :: "'ki \<Rightarrow> ('ai \<times> nat) list option"
  assumes Mi_M[param]: "(Mi, M) \<in> K \<rightarrow> \<langle>\<langle>A \<times>\<^sub>r Id\<rangle>list_set_rel\<rangle>option_rel"
  assumes F_mono:
    "\<And>a b. F a \<Longrightarrow> P a \<Longrightarrow> (\<lambda>(l, s) (l', s'). l' = l \<and> less_eq s s') a b \<Longrightarrow> P b \<Longrightarrow> F b"
  fixes inits :: "('k \<times> 'a) set" and initsi :: "('ki \<times> 'ai) list"
  assumes initsi_inits[param]: "(initsi, inits) \<in> \<langle>K \<times>\<^sub>r A\<rangle>list_set_rel"
begin

paragraph \<open>Refinement\<close>

definition "check_invariant_buechi' L' \<equiv>
  monadic_list_all_split (\<lambda>l.
    case Mi l of
      None \<Rightarrow> RETURN True
    | Some as \<Rightarrow> do {
      monadic_list_all (\<lambda>(x, i). do {
        let succs = get_succs l [x];
        let is_accepting = Fi (l, x);
        let cmp = (if is_accepting then (\<lambda>j. i < j) else (\<lambda>j. i \<le> j));
        monadic_list_all (\<lambda>(l', xs).
          if xs = [] then
            RETURN True
          else
            case Mi l' of
              None \<Rightarrow> RETURN False
            | Some ys \<Rightarrow>
              monadic_list_all (\<lambda>y.
                monadic_list_ex (\<lambda>(z, j). RETURN (lei y z \<and> cmp j)) ys
              ) xs
        ) succs
      }) as
    }) L'"

lemma Mi_M_None_iff[simp]:
  "M l = None \<longleftrightarrow> Mi li = None" if "(li, l) \<in> K"
proof -
  from that have "(Mi li, M l) \<in> \<langle>\<langle>A \<times>\<^sub>r Id\<rangle>list_set_rel\<rangle>option_rel"
    by parametricity
  then show ?thesis
    by auto
qed

lemma (in -) list_set_rel_singletonI[param]:
  assumes "(ai, a) \<in> A"
  shows "([ai], {a}) \<in> \<langle>A\<rangle>list_set_rel"
  unfolding list_set_rel_def
  using assms by (auto intro: relcompI[where b = "[a]"])

lemma check_invariant1_refine[refine]:
  "check_invariant_buechi' L1 \<le> check_invariant_buechi buechi_prop L'"
  if "(L1, L') \<in> \<langle>K\<rangle>list_rel" "L = dom M" "set L' \<subseteq> L"
  unfolding check_invariant_buechi'_def check_invariant_buechi_def Let_def monadic_list_all_split_def
  apply (refine_rcg monadic_list_all_mono' refine_IdI that)
  apply (clarsimp split: option.splits; safe)

    apply (simp add: RES_sng_eq_RETURN; fail)
   apply (simp flip: Mi_M_None_iff; fail)

  subgoal premises prems for ki k xs xsi
  proof -
    from prems fun_relD1[OF Mi_M] have "(Mi ki, M k) \<in> \<langle>\<langle>A \<times>\<^sub>r nat_rel\<rangle>list_set_rel\<rangle>option_rel"
      by force
    with prems have "(xsi, xs) \<in> \<langle>A \<times>\<^sub>r nat_rel\<rangle>list_set_rel"
      by force
    from list_set_relE[OF this] obtain ys where
      "(xsi, ys) \<in> \<langle>A \<times>\<^sub>r nat_rel\<rangle>list_rel" "set ys = xs" .
    then show ?thesis
      using \<open>(ki, k) \<in> _\<close>
      apply -
      apply (erule specify_right)

      apply (refine_rcg monadic_list_all_mono')
        apply assumption
       apply (parametricity, auto; fail)

      apply (clarsimp split: option.splits split del: if_split; safe)
        apply (
          elim list_set_relE specify_right;
          auto simp: monadic_list_all_False intro!: res_right simp flip: Mi_M_None_iff; fail)+
      subgoal premises prems for si s i ki' xsi' k' xs' zs zsi
      proof -
        have "k' \<in> L"
          using prems(6) that(2) by blast
        from \<open>(ki, k) \<in> K\<close> \<open>(si, s) \<in> A\<close> have Fi_F: "Fi (ki, si) \<longleftrightarrow> F (k, s)"
          using Fi_F by (force dest: fun_relD1)
        from prems fun_relD1[OF Mi_M] have "(Mi ki', M k') \<in> \<langle>\<langle>A \<times>\<^sub>r nat_rel\<rangle>list_set_rel\<rangle>option_rel"
          by force
        with prems have "(zsi, zs) \<in> \<langle>A \<times>\<^sub>r nat_rel\<rangle>list_set_rel"
          by force
        from list_set_relE[OF this] obtain ws where
          "(zsi, ws) \<in> \<langle>A \<times>\<^sub>r nat_rel\<rangle>list_rel" "set ws = zs" .
        moreover from list_set_relE[OF \<open>_ \<in> \<langle>A\<rangle>list_set_rel\<close>] obtain ys' where
          "(xsi', ys') \<in> \<langle>A\<rangle>list_rel" "set ys' = xs'" .
        ultimately show ?thesis
          using \<open>k' \<in> L\<close> lei_refine Fi_F
          unfolding buechi_prop_def
          supply [refine_mono] = monadic_list_all_mono' monadic_list_ex_mono' specify_right HOL.refl
          by (refine_mono | auto)+
      qed
      done
  qed
  done

definition check_prop1 where
  "check_prop1 L' M' = do {
  l \<leftarrow> RETURN L';
  monadic_list_all (\<lambda>l. do {
    let S = op_map_lookup l M';
    case S of None \<Rightarrow> RETURN True | Some S \<Rightarrow> do {
      xs \<leftarrow> RETURN S;
      r \<leftarrow> monadic_list_all (\<lambda>(s, _).
        RETURN (Pi (l, s))
      ) xs;
      RETURN r
    }
    }
  ) l
  }"

definition
  "check_init1 l\<^sub>0i s\<^sub>0i \<equiv> do {
  b1 \<leftarrow> RETURN (Mi l\<^sub>0i \<noteq> None);
  b2 \<leftarrow> RETURN (Pi (l\<^sub>0i, s\<^sub>0i));
  case Mi l\<^sub>0i of
    None \<Rightarrow> RETURN False
  | Some xs \<Rightarrow> do {
      b3 \<leftarrow> monadic_list_ex (\<lambda>(s, _). RETURN (lei s\<^sub>0i s)) xs;
      RETURN (b1 \<and> b2 \<and> b3)
    }
  }"

definition check_prop' where
  "check_prop' L' M' = do {
  l \<leftarrow> SPEC (\<lambda>xs. set xs = L');
  monadic_list_all (\<lambda>l. do {
    let S = op_map_lookup l M';
    case S of None \<Rightarrow> RETURN True | Some S \<Rightarrow> do {
      xs \<leftarrow> SPEC (\<lambda>xs. set xs = S);
      r \<leftarrow> monadic_list_all (\<lambda>(s, _).
        RETURN (PR_CONST P' (l, s))
      ) xs;
      RETURN r
    }
    }
  ) l
  }"

definition
  "check_all_pre1 \<equiv> do {
    b1 \<leftarrow> monadic_list_all (\<lambda>(l\<^sub>0, s\<^sub>0). check_init1 l\<^sub>0 s\<^sub>0) initsi;
    b2 \<leftarrow> check_prop1 Li Mi;
    RETURN (b1 \<and> b2)
  }"

lemma check_prop1_refine:
  "(check_prop1, check_prop')
    \<in> \<langle>K\<rangle>list_set_rel \<rightarrow> (K \<rightarrow> \<langle>\<langle>A \<times>\<^sub>r Id\<rangle>list_set_rel\<rangle>option_rel) \<rightarrow> \<langle>Id\<rangle>nres_rel"
  supply [refine] =
    list_of_set_impl[THEN fun_relD, THEN nres_relD] monadic_list_all_mono' case_option_mono'
  supply [refine_mono] =
    monadic_list_all_mono' list_of_set_impl[THEN fun_relD, THEN nres_relD]
  unfolding check_prop1_def check_prop'_def list_of_set_def[symmetric] Let_def op_map_lookup_def
  apply refine_rcg
   apply assumption
  apply (refine_rcg refine_IdI, assumption)
   apply parametricity
  apply (rule bind_mono)
   apply refine_mono+
  using Pi_P' by (auto simp add: prod_rel_def dest!: fun_relD)

lemma check_prop_gt_SUCCEED:
  "check_prop P' > SUCCEED" if "L = dom M"
  using finite that unfolding check_prop_def
  by (intro monadic_list_all_gt_SUCCEED bind_RES_gt_SUCCEED_I)
     (auto split: option.split simp: dom_def intro!: finite_list)

lemma check_prop_alt_def:
  "check_prop' L M = check_prop P'" if "L = dom M"
  unfolding check_prop_def check_prop'_def
  apply (fo_rule arg_cong2, simp, fo_rule arg_cong)
  apply (clarsimp split: option.split simp: bind_RES)
  apply (rule ext)
  apply (clarsimp split: option.split simp: bind_RES)
  apply (fo_rule arg_cong)
  unfolding pure_unfolds image_def
proof (safe; simp)
  fix l :: \<open>'k\<close> and xs:: \<open>('a \<times> nat) list\<close>
  assume \<open>M l = Some (set xs)\<close>
  show \<open>\<exists>x. set x = {y. \<exists>x\<in>set xs. y = fst x} \<and>
    list_all (\<lambda>(s, _). P' (l, s)) xs = list_all (\<lambda>s. P' (l, s)) x\<close>
    by (rule exI[where x = "map fst xs"]) (auto simp: list_all_iff)
next
  fix l :: \<open>'k\<close> and S :: \<open>('a \<times> nat) set\<close> and ys :: \<open>'a list\<close>
  assume \<open>M l = Some S\<close> and \<open>set ys = {y. \<exists>x\<in>S. y = fst x}\<close>
  with \<open>L = _\<close> finite have "finite S"
    by force
  then obtain xs where "set xs = S"
    by atomize_elim (rule finite_list)
  with \<open>set ys = _\<close> show
    \<open>\<exists>x. set x = S \<and> list_all (\<lambda>s. P' (l, s)) ys = list_all (\<lambda>(s, _). P' (l, s)) x\<close>
    by (intro exI[where x = xs]) (auto simp: list_all_iff)
qed

lemma check_init1_refine:
  "(check_init1, check_init) \<in> K \<rightarrow> A \<rightarrow> \<langle>bool_rel\<rangle>nres_rel" if "L = dom M"
proof (intro fun_relI)
  fix l\<^sub>0 l\<^sub>0i s\<^sub>0 s\<^sub>0i
  assume l\<^sub>0i_l\<^sub>0: "(l\<^sub>0i, l\<^sub>0) \<in> K" and s\<^sub>0i_s\<^sub>0: "(s\<^sub>0i, s\<^sub>0) \<in> A"
  then have [refine]:
    "(Pi (l\<^sub>0i, s\<^sub>0i), P' (l\<^sub>0, s\<^sub>0)) \<in> bool_rel"
    by parametricity
  have [refine]:
    "(Mi l\<^sub>0i \<noteq> None, l\<^sub>0 \<in> L) \<in> bool_rel"
    using that by (auto simp: Mi_M_None_iff[symmetric, OF \<open>_ \<in> K\<close>])
  show "(check_init1 l\<^sub>0i s\<^sub>0i, check_init l\<^sub>0 s\<^sub>0) \<in> \<langle>bool_rel\<rangle>nres_rel"
  proof (cases "M l\<^sub>0")
    case None
    then show ?thesis
      using that l\<^sub>0i_l\<^sub>0 unfolding check_init1_def check_init_def
      by refine_rcg (simp flip: Mi_M_None_iff add: bind_RES; simp)
  next
    case (Some S)
    from \<open>_ \<in> K\<close> have "(Mi l\<^sub>0i, M l\<^sub>0) \<in> \<langle>\<langle>A \<times>\<^sub>r Id\<rangle>list_set_rel\<rangle>option_rel"
      by parametricity
    with \<open>M l\<^sub>0 = _\<close> obtain xs ys where *:
      "Mi l\<^sub>0i = Some xs" "(xs, ys) \<in> \<langle>A \<times>\<^sub>r Id\<rangle>list_rel" "set (map fst ys) = fst ` S"
      unfolding option_rel_def by (auto elim: list_set_relE)
    then have "(xs, map fst ys) \<in> \<langle>{((x, i), y). (x, y) \<in> A}\<rangle>list_rel"
      unfolding list_rel_def by (auto elim: list_all2_induct)
    with * \<open>M l\<^sub>0 = _\<close> show ?thesis
      unfolding check_init1_def check_init_def
      apply (refine_rcg that; simp)
      supply [refine_mono] = monadic_list_ex_mono' specify_right Li_L Mi_M
      apply refine_mono
      using lei_refine s\<^sub>0i_s\<^sub>0 apply auto
      done
  qed
qed

lemma check_all_pre1_correct[refine]:
  "check_all_pre1 \<le> SPEC (\<lambda>r. r \<longrightarrow> check_all_pre_spec1 inits)"  if "L = dom M"
proof -
  note check_init1_refine[THEN fun_relD, THEN fun_relD, THEN nres_relD, OF that]
  also note check_init_correct
  finally have [refine_mono, refine]: "check_init1 l\<^sub>0i s\<^sub>0i \<le> SPEC (\<lambda>r. r = check_init_spec l\<^sub>0 s\<^sub>0)"
    if l\<^sub>0i_l\<^sub>0: "(l\<^sub>0i, l\<^sub>0) \<in> K" and s\<^sub>0i_s\<^sub>0: "(s\<^sub>0i, s\<^sub>0) \<in> A" for l\<^sub>0 l\<^sub>0i s\<^sub>0 s\<^sub>0i
    using that by (force intro: order.trans)
  from initsi_inits obtain inits' where
    "inits = set inits'" and [refine_mono]: "(initsi, inits') \<in> \<langle>K \<times>\<^sub>r A\<rangle>list_rel"
    unfolding list_set_rel_def by auto
  note [refine_mono] = case_prod_mono monadic_list_all_mono'
    (* NB: if the rhs is phrased with RETURN, refine_vcg will fail *)
  have [refine]: "monadic_list_all (\<lambda>(l\<^sub>0, s\<^sub>0). check_init1 l\<^sub>0 s\<^sub>0) initsi
    \<le> SPEC (\<lambda>r. r = list_all (\<lambda>(l\<^sub>0, s\<^sub>0). check_init_spec l\<^sub>0 s\<^sub>0) inits')"
    by (rule order.trans, refine_mono) (refine_vcg monadic_list_all_rule; auto)
  note check_prop1_refine[THEN fun_relD, THEN fun_relD, THEN nres_relD, THEN refine_IdD,
      OF Li_L Mi_M, unfolded check_prop_alt_def[OF \<open>L =  _\<close>]]
  also note check_prop_correct
  also note [refine] = calculation
  show ?thesis
    unfolding check_all_pre1_def
    apply refine_vcg
    unfolding check_all_pre_spec1_def check_init_spec_def list_all_iff \<open>inits = set inits'\<close>
    by fastforce
qed

definition
  "certify_no_buechi_run \<equiv> do {
    b \<leftarrow> check_all_pre1;
    if b
    then do {
      r \<leftarrow> check_invariant_buechi' Li;
      PRINT_CHECK STR ''State set invariant check'' r;
      RETURN r
    }
    else RETURN False
  }"

lemma check_all1_refine:
  "certify_no_buechi_run \<le> check_buechi inits" if "L = dom M"
proof -
  obtain L' where aux: "(Li, L') \<in> \<langle>K\<rangle>list_rel" "set L' = L"
    using Li_L by (elim list_set_relE)
  note check_invariant1_refine
  also note check_invariant_buechi_correct
  also note [refine] = calculation
  have [refine]:
    "check_invariant_buechi' Li \<le> SPEC (\<lambda>r. r \<longrightarrow> check_invariant_buechi_spec buechi_prop L)"
    if "\<forall>l\<in>L. \<forall>(s, _)\<in>case M l of None \<Rightarrow> {} | Some S \<Rightarrow> S. P (l, s)"
    using aux that \<open>L = dom M\<close> by refine_vcg simp+
  show ?thesis
    using P'_P that unfolding certify_no_buechi_run_def check_buechi_def PRINT_CHECK_def comp_def
    by (refine_mono; refine_vcg;
        unfold check_all_pre_spec1_def; fastforce split: prod.splits simp: check_all_pre_spec1_def)
qed


theorem certify_no_buechi_run_correct:
  "certify_no_buechi_run \<le> SPEC (\<lambda>r. r \<longrightarrow> (\<nexists>xs l\<^sub>0 s\<^sub>0.
    (l\<^sub>0, s\<^sub>0) \<in> inits \<and> Graph_Defs.run E ((l\<^sub>0, s\<^sub>0) ## xs) \<and> alw (ev (holds F)) ((l\<^sub>0, s\<^sub>0) ## xs)))"
  if "L = dom M"
  by (rule order.trans[OF check_all1_refine[OF that]], refine_vcg that check_buechi_correct)
     (auto intro: no_buechi_run)

paragraph \<open>Synthesizing a pure program via rewriting\<close>

schematic_goal check_prop1_alt_def:
  "check_prop1 L' M' \<equiv> RETURN ?f"
  unfolding check_prop1_def pure_unfolds Let_def .

concrete_definition check_prop_impl uses check_prop1_alt_def is "_ \<equiv> RETURN ?f"

schematic_goal check_all_pre1_alt_def:
  "check_all_pre1 \<equiv> RETURN ?f"
  unfolding check_all_pre1_def check_init1_def check_prop_impl.refine pure_unfolds .

concrete_definition check_all_pre_impl uses check_all_pre1_alt_def is "_ \<equiv> RETURN ?f" 

schematic_goal check_invariant_buechi'_alt_def:
  "check_invariant_buechi' Li \<equiv> RETURN ?f"
  unfolding check_invariant_buechi'_def Let_def pure_unfolds .

concrete_definition check_invariant_buechi_impl
  uses check_invariant_buechi'_alt_def is "_ \<equiv> RETURN ?f"

schematic_goal certify_no_buechi_run_alt_def:
  "certify_no_buechi_run \<equiv> RETURN ?f"
  unfolding certify_no_buechi_run_def
  unfolding
    certify_no_buechi_run_def check_all_pre_impl.refine
    check_invariant_buechi_impl.refine
    pure_unfolds PRINT_CHECK_def comp_def short_circuit_conv if_bool_simps
  .

concrete_definition certify_no_buechi_run_pure1
  uses certify_no_buechi_run_alt_def is "_ \<equiv> RETURN ?f"

text \<open>This is where we add parallel execution:\<close>

schematic_goal certify_no_buechi_run_pure1_alt_def:
  "certify_no_buechi_run_pure1 \<equiv> ?f"
  unfolding certify_no_buechi_run_pure1_def
  apply (abstract_let check_invariant_buechi_impl check_invariant)
  apply (abstract_let check_all_pre_impl check_all_pre_impl)
  apply (time_it "STR ''Time for state set preconditions check''" check_all_pre_impl)
  apply (time_it "STR ''Time for state space invariant check''"   check_invariant_buechi_impl)
  unfolding
    check_invariant_buechi_impl_def check_all_pre_impl_def
    check_prop_impl_def
    list_all_split
  apply (subst list_all_default_split[where xs = Li, folded Parallel.map_def])
  .

concrete_definition (in -) certify_no_buechi_run_pure
  uses Buechi_Impl_pure.certify_no_buechi_run_pure1_alt_def is "_ \<equiv> ?f"

theorem certify_no_buechi_run_impl_pure_correct:
  "certify_no_buechi_run_pure get_succs Li lei Pi Fi Li_split Mi initsi \<longrightarrow> (\<nexists>xs l\<^sub>0 s\<^sub>0.
    (l\<^sub>0, s\<^sub>0) \<in> inits \<and> Graph_Defs.run E ((l\<^sub>0, s\<^sub>0) ## xs) \<and> alw (ev (holds F)) ((l\<^sub>0, s\<^sub>0) ## xs))"
  if "L = dom M"
  using certify_no_buechi_run_correct that
  unfolding
    certify_no_buechi_run_pure1.refine
    certify_no_buechi_run_pure.refine[OF Buechi_Impl_pure_axioms]
  by simp

end (* Reachability_Impl_pure *)


locale Reachability_Impl_imp_to_pure_base = Reachability_Impl_base
  where K = K and A = A
  for K :: "'k \<Rightarrow> ('ki :: {hashable,heap}) \<Rightarrow> assn" and A :: "'s \<Rightarrow> ('si :: heap) \<Rightarrow> assn"
  +
  fixes to_state :: "'s1 \<Rightarrow> 'si Heap" and from_state :: "'si \<Rightarrow> 's1 Heap"
    and to_loc :: "'k1 \<Rightarrow> 'ki" and from_loc :: "'ki \<Rightarrow> 'k1"
  fixes lei
  fixes K_rel and A_rel
  fixes L_list :: "'ki list" and Li :: "'k1 list" and L' :: "'k list"
  fixes Li_split :: "'k1 list list"
  assumes Li: "(L_list, L') \<in> \<langle>the_pure K\<rangle>list_rel" "(Li, L') \<in> \<langle>K_rel\<rangle>list_rel" "set L' = L"
  assumes to_state_ht: "(s1, s) \<in> A_rel \<Longrightarrow> <emp> to_state s1 <\<lambda>si. A s si>"
  assumes from_state_ht: "<A s si> from_state si <\<lambda>s'. \<up>((s', s) \<in> A_rel)>\<^sub>t"
  assumes from_loc: "(li, l) \<in> the_pure K \<Longrightarrow> (from_loc li, l) \<in> K_rel"
  assumes to_loc: "(l1, l) \<in> K_rel \<Longrightarrow> (to_loc l1, l) \<in> the_pure K"
  assumes K_rel: "single_valued K_rel" "single_valued (K_rel\<inverse>)"
  assumes lei_less_eq: "(lei, (\<preceq>)) \<in> A_rel \<rightarrow> A_rel \<rightarrow> bool_rel"
  assumes full_split: "set Li = (\<Union>xs \<in> set Li_split. set xs)"
begin

definition
  "get_succs l xs \<equiv>
    do {
      let li = to_loc l;
      xsi \<leftarrow> Heap_Monad.fold_map to_state xs;
      r \<leftarrow> succsi li xsi;
      Heap_Monad.fold_map
        (\<lambda>(li, xsi). do {xs \<leftarrow> Heap_Monad.fold_map from_state xsi; return (from_loc li, xs)}) r
    }"

lemma get_succs:
  "(run_heap oo get_succs, succs)
  \<in> K_rel \<rightarrow> \<langle>A_rel\<rangle>list_set_rel \<rightarrow> \<langle>K_rel \<times>\<^sub>r \<langle>A_rel\<rangle>list_set_rel\<rangle>list_rel"
proof (refine_rcg, clarsimp, rule hoare_triple_run_heapD)
  fix l :: \<open>'k\<close> and l1 :: \<open>'k1\<close> and xs :: \<open>'s1 list\<close> and S :: \<open>'s set\<close>
  assume \<open>(l1, l) \<in> K_rel\<close> \<open>(xs, S) \<in> \<langle>A_rel\<rangle>list_set_rel\<close>
  then obtain ys where ys: "(xs, ys) \<in> \<langle>A_rel\<rangle>list_rel" "set ys = S"
    by (elim list_set_relE)
  have 1: "K = pure (the_pure K)"
    using pure_K by auto
  let ?li = "to_loc l1"
  show "<emp> get_succs l1 xs <\<lambda>r. \<up>((r, succs l S) \<in> \<langle>K_rel \<times>\<^sub>r \<langle>A_rel\<rangle>list_set_rel\<rangle>list_rel)>\<^sub>t"
    unfolding get_succs_def
    apply sep_auto
      (* fold_map to_state *)
     apply (rule Hoare_Triple.cons_pre_rule[rotated])
      apply (rule fold_map_ht3[where A = true and R = "pure A_rel" and Q = A and xs = ys])
    apply (sep_auto heap: to_state_ht simp: pure_def; fail)
     apply (unfold list_assn_pure_conv, sep_auto simp: pure_def ys; fail)
    apply sep_auto
      (* succsi *)
     apply (rule Hoare_Triple.cons_pre_rule[rotated], rule frame_rule[where R = true])
      apply (rule succsi[to_hnr, unfolded hn_refine_def hn_ctxt_def, simplified, of S _ l ?li])
    subgoal
      using ys \<open>(l1, l) \<in> K_rel\<close> unfolding lso_assn_def hr_comp_def br_def \<open>set ys = _\<close>[symmetric]
      by (subst 1) (sep_auto simp: pure_def to_loc)
        (* nested fold_map *)
    apply (sep_auto simp: invalid_assn_def)
    apply (rule cons_rule[rotated 2])
      apply (rule frame_rule)
      apply (rule fold_map_ht1[where
          A = true and R = "(K \<times>\<^sub>a lso_assn A)" and xs = "succs l S" and
          Q = "\<lambda>x xi. (xi, x) \<in> K_rel \<times>\<^sub>r \<langle>A_rel\<rangle>list_set_rel"
          ])
    subgoal
      unfolding lso_assn_def
      apply (subst 1, subst pure_def)
      apply (sep_auto simp: prod_assn_def hr_comp_def br_def split: prod.splits)
        (* inner fold_map *)
       apply (rule Hoare_Triple.cons_pre_rule[rotated])
        apply (rule fold_map_ht1[where A = true and R = A and Q = "\<lambda>l l1. (l1, l) \<in> A_rel"])
        apply (rule cons_rule[rotated 2], rule frame_rule, rule from_state_ht)
         apply frame_inference
        apply (sep_auto; fail)
       apply solve_entails
        (* return *)
      using list_all2_swap by (sep_auto simp: list.rel_eq list_set_rel_def from_loc list_rel_def)
     apply solve_entails
    using list_all2_swap by (sep_auto simp: list_rel_def)
qed

definition
  "to_pair \<equiv> \<lambda>(l, s). do {s \<leftarrow> to_state s; return (to_loc l, s)}"

lemma to_pair_ht:
  "<emp> to_pair a1 <\<lambda>ai. (K \<times>\<^sub>a A) a ai>" if "(a1, a) \<in> K_rel \<times>\<^sub>r A_rel"
  using that unfolding to_pair_def
  by (cases a, cases a1, subst pure_the_pure[symmetric, OF pure_K])
     (sep_auto heap: to_state_ht simp: pure_def to_loc prod_assn_def split: prod.splits)

sublocale pure:
  Reachability_Impl_pure_base
  where           
    get_succs = "run_heap oo get_succs" and
    K = K_rel and
    A = A_rel and
    lei = lei and
    Pi = "\<lambda>a. run_heap (do {a \<leftarrow> to_pair a; Pi a})" and
    Fi = "\<lambda>a. run_heap (do {a \<leftarrow> to_pair a; Fi a})" \<^cancel>\<open>and
    l\<^sub>0i = "from_loc (run_heap l\<^sub>0i)" and
    s\<^sub>0i = "run_heap (do {s \<leftarrow> s\<^sub>0i; from_state s})"\<close>
  apply standard
  subgoal
    by (rule K_rel)
  subgoal
    by (rule K_rel)
  subgoal
    using Li unfolding list_set_rel_def by auto
  subgoal
    by (rule lei_less_eq)
  subgoal
    using get_succs .
  subgoal
    apply standard
    apply (rule hoare_triple_run_heapD)
    apply (sep_auto heap: to_pair_ht simp del: prod_rel_simp prod_assn_pair_conv)
    apply (rule Hoare_Triple.cons_rule[rotated 2])
      apply (rule Pi_P'[to_hnr, unfolded hn_refine_def hn_ctxt_def, simplified], rule ent_refl)
    apply (sep_auto simp: pure_def)
    done
  subgoal
    apply standard
    apply (rule hoare_triple_run_heapD)
    apply (sep_auto heap: to_pair_ht simp del: prod_rel_simp prod_assn_pair_conv)
    apply (rule Hoare_Triple.cons_rule[rotated 2])
      apply (rule Fi_F[to_hnr, unfolded hn_refine_def hn_ctxt_def, simplified], rule ent_refl)
    apply (sep_auto simp: pure_def)
    done
  subgoal
    by (rule full_split)
  done

end

locale Reachability_Impl_imp_to_pure = Reachability_Impl where
  l\<^sub>0 = l\<^sub>0 and s\<^sub>0 = s\<^sub>0 and M = M and K = K and A = A
  + Reachability_Impl_imp_to_pure_base
  where K_rel = K_rel and A_rel = A_rel and K = K and A = A
  and M = "\<lambda>x. case M x of None \<Rightarrow> {} | Some S \<Rightarrow> S"
  for l\<^sub>0 :: 'k and s\<^sub>0 :: 'a
  and K :: "'k \<Rightarrow> ('ki :: {hashable,heap}) \<Rightarrow> assn" and A :: "'a \<Rightarrow> ('ai :: heap) \<Rightarrow> assn"
  and M and K_rel :: "('k1 \<times> 'k) set" and A_rel :: "('a1 \<times> 'a) set" +
  fixes Mi :: "'k1 \<Rightarrow> 'a1 list option"
  assumes Mi_M: "(Mi, M) \<in> K_rel \<rightarrow> \<langle>\<langle>A_rel\<rangle>list_set_rel\<rangle>option_rel"
begin

sublocale pure:
  Reachability_Impl_pure
  where           
    M = M and
    Mi = Mi and
    get_succs = "run_heap oo get_succs" and
    K = K_rel and
    A = A_rel and
    lei = lei and
    Pi = "\<lambda>a. run_heap (do {a \<leftarrow> to_pair a; Pi a})" and
    Fi = "\<lambda>a. run_heap (do {a \<leftarrow> to_pair a; Fi a})" and
    l\<^sub>0i = "from_loc (run_heap l\<^sub>0i)" and
    s\<^sub>0i = "run_heap (do {s \<leftarrow> s\<^sub>0i; from_state s})"
  apply standard
    apply (rule Mi_M)
  subgoal
    apply (rule from_loc)
    apply (rule hoare_triple_run_heapD)
    using l\<^sub>0i_l\<^sub>0[to_hnr, unfolded hn_refine_def hn_ctxt_def, simplified]
    apply (subst (asm) pure_the_pure[symmetric, OF pure_K])
    apply (sep_auto simp: pure_def elim!: cons_post_rule)
    done
  subgoal
    using s\<^sub>0i_s\<^sub>0[to_hnr, unfolded hn_refine_def hn_ctxt_def, simplified]
    by - (rule hoare_triple_run_heapD, sep_auto heap: from_state_ht)
  done

end

locale Buechi_Impl_imp_to_pure = Buechi_Impl_pre where
  M = "\<lambda>x. case M x of None \<Rightarrow> {} | Some S \<Rightarrow> S"
  + Reachability_Impl_imp_to_pure_base
  where M = "\<lambda>l. fst ` (\<lambda>x. case M x of None \<Rightarrow> {} | Some S \<Rightarrow> S) l"
  and K_rel = K_rel and A_rel = A_rel
  for M :: "'k \<Rightarrow> ('a \<times> nat) set option"
  and K_rel :: "('ki \<times> 'k) set" and A_rel :: "('ai \<times> 'a) set" +
  fixes inits initsi
  assumes initsi_inits: "(uncurry0 initsi, uncurry0 (RETURN (PR_CONST inits)))
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a list_assn (K \<times>\<^sub>a A)"
  fixes Mi :: "'ki \<Rightarrow> ('ai \<times> nat) list option"
  assumes Mi_M: "(Mi, M) \<in> K_rel \<rightarrow> \<langle>\<langle>A_rel \<times>\<^sub>r Id\<rangle>list_set_rel\<rangle>option_rel"
begin

lemma (in -) list_all2_flip:
  "list_all2 P xs ys" if "list_all2 Q ys xs" "(\<And>x y. Q y x \<Longrightarrow> P x y)"
  using that by (simp add: list_all2_conv_all_nth)

sublocale pure:
  Buechi_Impl_pure
  where
    M = M and
    Mi = Mi and
    get_succs = "run_heap oo get_succs" and
    K = K_rel and
    A = A_rel and
    lei = lei and
    Pi = "\<lambda>a. run_heap (do {a \<leftarrow> to_pair a; Pi a})" and
    Fi = "\<lambda>a. run_heap (do {a \<leftarrow> to_pair a; Fi a})" and
    inits = "set inits" and
    \<^cancel>\<open>initsi = "
      map (\<lambda>(l, s). (from_loc l, from_state s)) (run_heap initsi)"\<close>
    initsi = "
      run_heap (do {
        xs \<leftarrow> initsi;
        Heap_Monad.fold_map (\<lambda>(l, s). do {s \<leftarrow> from_state s; return (from_loc l, s)}) xs})"
  apply standard
    apply (rule Mi_M F_mono; assumption)+

  apply (rule hoare_triple_run_heapD)
  subgoal
  proof -
    have ***: "<\<up>((li, l) \<in> the_pure K) * \<up> ((s1, s) \<in> A_rel) * true> return (from_loc li, s1)
          <\<lambda>(l1, s1). \<up> ((l1, l) \<in> K_rel) * \<up>((s1, s) \<in> A_rel)>\<^sub>t" for li l s1 s
      by (sep_auto intro: from_loc)
        (* XXX Why do we need this? Could e-matching help? *)
    have 1: "(l, fst (a, b)) \<in> R" if "(l, a) \<in> R" for l a b R
      using that by auto
    have 2: "(l, snd (a, b)) \<in> R" if "(l, b) \<in> R" for l a b R
      using that by auto
        (* XXX Any way to improve this? *)
    have "
      <emp> (do {
        xs \<leftarrow> initsi;
        Heap_Monad.fold_map (\<lambda>(l, s). do {s \<leftarrow> from_state s; return (from_loc l, s)}) xs})
      <\<lambda>r. \<up> ((r, inits) \<in> \<langle>K_rel \<times>\<^sub>r A_rel\<rangle>list_rel)>\<^sub>t"
      using initsi_inits[to_hnr, unfolded hn_refine_def hn_ctxt_def, simplified]
      apply (subst (asm) pure_the_pure[symmetric, OF pure_K])

      apply (sep_auto simp: pure_def list_rel_def heap: fold_map_ht1)

        prefer 3
        apply (sep_auto elim: list_all2_flip)
       prefer 2
       apply (rule cons_post_rule)
        apply (rule ***)
       prefer 2
       apply (sep_auto heap: from_state_ht elim: 1 2)+
      done

    then show ?thesis
      by (sep_auto simp: pure_def list_set_rel_def relcomp.simps elim!: cons_post_rule)
  qed
  done

end

end
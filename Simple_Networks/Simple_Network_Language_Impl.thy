theory Simple_Network_Language_Impl
  imports
    Simple_Network_Language
    TA_Impl.Normalized_Zone_Semantics_Impl_Refine
    "HOL-Library.IArray" "HOL-Library.AList"
    "../library/More_Methods"
    TA_Impl_Misc2
    TA_More2
    "HOL-Eisbach.Eisbach_Tools"
begin

paragraph \<open>Default maps\<close>

definition default_map_of :: "'b \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b" where
  "default_map_of a xs \<equiv> FinFun.map_default a (map_of xs)"

lemma default_map_of_alt_def:
  "default_map_of a xs x = (if x \<in> dom (map_of xs) then the (map_of xs x) else a)"
  unfolding default_map_of_def map_default_def by (auto split: option.split_asm)

lemma range_default_map_of:
  "range (default_map_of x xs) \<subseteq> snd ` set xs \<union> {x}"
  unfolding default_map_of_def map_default_def
  by (auto split: option.split_asm) (meson img_snd map_of_SomeD)

lemma finite_range_default_map_of:
  "finite (range (default_map_of x m))"
proof -
  have "range (default_map_of x m) \<subseteq> the ` range (map_of m) \<union> {x}"
    unfolding default_map_of_def FinFun.map_default_def
    by (auto split: option.splits) (metis image_eqI option.sel rangeI)
  also have "finite \<dots>"
    by (blast intro: finite_range_map_of)
  finally show ?thesis .
qed

lemma map_index'_inj:
  "L = L'"
  if "length L = length L'" "map_index' n f L = map_index' n g L'" "set L \<subseteq> S" "set L' \<subseteq> T"
     "\<forall> i < length L + n. \<forall> x \<in> S. \<forall>y \<in> T. f i x = g i y \<longrightarrow> x = y"
  using that
proof (induction "length L" arbitrary: L L' n)
  case 0
  then show ?case
    by simp
next
  case (Suc x)
  from Suc.prems obtain a b L1 L1' where *:
    "length L1 = x" "length L1' = x" "L = a # L1" "L' = b # L1'"
    by (smt Suc.hyps(2) length_Suc_conv)
  show ?case
    unfolding \<open>L = _\<close> \<open>L' = _\<close>
    apply (clarsimp, rule conjI)
    subgoal
      by (smt *(3,4) Suc.hyps(2) Suc.prems Suc_less_eq add_Suc_shift less_add_Suc2 list.set_intros(1) list_tail_coinc map_index'.simps(2) set_mp)
    subgoal
      apply (rule Suc.hyps)
      using Suc.prems * by auto
    done
qed

lemma map_index_inj:
  "L = L'"
  if "map_index f L = map_index g L'" "set L \<subseteq> S" "set L' \<subseteq> T"
     "\<forall> i < length L. \<forall> x \<in> S. \<forall>y \<in> T. f i x = g i y \<longrightarrow> x = y"
  using that by - (rule map_index'_inj, auto dest: map_index_eq_imp_length_eq)

lemma (in Prod_TA_Defs) trans_broad_alt_def:
  "trans_broad =
    {((L, s), g @ concat (map gs ps), Broad a, r @ concat (map rs ps), (L', s'')) |
    L s L' s' s'' a p l g f r l' gs fs rs ls' ps.
      a \<in> broadcast  \<and>
      (l, g, Out a, f, r, l') \<in> trans (N p) \<and>
      (\<forall>p \<in> set ps. (L ! p, gs p, In a, fs p, rs p, ls' p) \<in> trans (N p)) \<and>
      (l \<in> commited (N p) \<or> (\<exists>p \<in> set ps. L ! p \<in> commited (N p))
      \<or> (\<forall>p < n_ps. L ! p \<notin> commited (N p))) \<and>
      (\<forall>q < n_ps. q \<notin> set ps \<and> p \<noteq> q \<longrightarrow> \<not> (\<exists>g f r l'. (L!q, g, In a, f, r, l') \<in> trans (N q))) \<and>
      L!p = l \<and>
      p < length L \<and> set ps \<subseteq> {0..<n_ps} \<and> p \<notin> set ps \<and> distinct ps \<and> sorted ps \<and> ps \<noteq> [] \<and>
      L' = fold (\<lambda>p L . L[p := ls' p]) ps L[p := l'] \<and> is_upd s f s' \<and> is_upds s' (map fs ps) s'' \<and>
      L \<in> states \<and> bounded bounds s \<and> bounded bounds s'' \<and>
      (\<forall>p. p\<notin>set ps \<longrightarrow> gs p = [])
    }"
  unfolding trans_broad_def
proof ((intro Collect_eqI iffI; elims add: more_elims), goal_cases)
  case prems: (1 x L s L' s' s'' a p l g f r l' gs fs rs ls' ps)
  let ?gs = "\<lambda>p. if p \<in> set ps then gs p else []"
  have *[simp]: "concat (map gs ps) = concat (map ?gs ps)"
    by (simp cong: map_cong)
  with prems show ?case
    by (inst_existentials L s L' s' s'' a p l g f r l' ?gs fs rs ls' ps; (assumption | simp))
next
  case (2 x L s L' s' s'' a p l g f r l' gs fs rs ls' ps)
  then show ?case
    by blast
qed

(* XXX Move to distribution *)
text \<open>Stronger version of @{thm Map.map_of_mapk_SomeI}\<close>
theorem map_of_mapk_SomeI:
  assumes "inj f"
    and "map_of t k = Some x"
  shows "map_of (map (\<lambda>(k, y). (f k, g y)) t) (f k) = Some (g x)"
  using assms by (induction t) (auto split: if_split_asm dest: injD)

locale Simple_Network_Impl =
  fixes automata ::
    "('s list \<times> ('a act, 's, 'c, int, 'x, int) transition list
      \<times> ('s \<times> ('c, int) cconstraint) list) list"
    and broadcast :: "'a list"
    and bounds' :: "('x \<times> (int \<times> int)) list"
    and formula :: formula \<comment> \<open>Model checking formula\<close>
begin

definition \<comment>\<open>Number of state variables\<close>
  "n_vs = length bounds'"

definition
  "conv_automaton \<equiv> \<lambda>(commited, trans, inv).
    (commited,
     map (\<lambda>(l, g, a, f, r, l'). (l, conv_cc g, a, f, r, l')) trans,
     map (\<lambda>(s, cc). (s, conv_cc cc)) inv)"

definition
  "B x \<equiv> if x \<in> dom (map_of bounds') then the (map_of bounds' x) else (0, 0)"

definition
  "automaton_of \<equiv>
    \<lambda>(commited, trans, inv). (set commited, set trans, default_map_of [] inv)"

sublocale Prod_TA_Defs
  "(set broadcast, map automaton_of automata, map_of bounds')" .

end

paragraph \<open>Mapping through the product construction\<close>

locale Simple_Network_Impl_map =
  Simple_Network_Impl automata for
  automata ::
    "('s list \<times> ('a act, 's, 'c, int, 'x, int) transition list
      \<times> ('s \<times> ('c, int) cconstraint) list) list" +
  fixes map_loc :: "nat \<Rightarrow> 's \<Rightarrow> 's1"
  fixes map_action :: "'a \<Rightarrow> 'a1"
  fixes map_clock :: "'c \<Rightarrow> 'c1"
  fixes map_var :: "'x \<Rightarrow> 'x1"
  fixes map_time :: "int \<Rightarrow> real"
begin

definition map_ac :: "('c, int) acconstraint \<Rightarrow> ('c1, real) acconstraint" where
  "map_ac \<equiv> map_acconstraint map_clock map_time"

definition map_cc :: "('c, int) cconstraint \<Rightarrow> ('c1, real) cconstraint" where
  "map_cc \<equiv> map (map_acconstraint map_clock map_time)"

definition
  "map_expr \<equiv> map (\<lambda> (x, e). (map_var x, map_exp map_var id e))"

definition map_automaton :: "nat \<Rightarrow> ('s list \<times> ('a act, 's, 'c, int, 'x, int) transition list
      \<times> ('s \<times> ('c, int) cconstraint) list) \<Rightarrow> _" where
  "map_automaton i \<equiv> \<lambda>(commited, trans, inv).
    (map (map_loc i) commited,
     map (\<lambda>(l, g, a, f, r, l').
      (map_loc i l, map_cc g, map_act map_action a, map_expr f, map map_clock r, map_loc i l')) trans,
     map (\<lambda>(s, cc). (map_loc i s, map_cc cc)) inv)"

definition
  "map_t_single i = (\<lambda>(l, g, a, f, r, l').
      (map_loc i l, map_cc g, map_act map_action a, map_expr f, map map_clock r, map_loc i l'))"

definition map_single :: "nat \<Rightarrow> ('s set \<times> ('a act, 's, 'c, int, 'x, int) transition set
      \<times> ('s \<Rightarrow> ('c, int) cconstraint)) \<Rightarrow> _" where
  "map_single i \<equiv> \<lambda>(commited, trans, inv).
    (map_loc i ` commited,
     map_t_single i ` trans,
     (\<lambda> l. if l \<in> map_loc i ` fst ` set (snd (snd (automata ! i))) then map_cc (inv (the_inv (map_loc i) l)) else []))"

sublocale map: Prod_TA_Defs
  "(map_action ` set broadcast,
    map_index (\<lambda> i a. automaton_of (map_automaton i a)) automata,
    map_of (map (\<lambda>(x, p). (map_var x, p)) bounds'))"
  .

definition
  "map_st \<equiv> \<lambda>(L, s).
    (map_index map_loc L, \<lambda> x. if x \<in> map_var ` dom s then s (the_inv map_var x) else None)"

definition "map_t \<equiv> \<lambda> (l,g,a,r,l').
  (map_st l,map_cc g,map_label map_action a,map map_clock r,map_st l')"

abbreviation "map_A \<equiv> \<lambda> (T, I). (map_t ` T, map_cc o I o the_inv map_st)"

context
  assumes map_loc_inj:    "\<forall> i. inj (map_loc i)"
      and map_var_inj:    "inj map_var"
      and map_action_inj: "inj map_action"
      and map_clock_inj:  "inj map_clock"
      and map_time_inj:   "inj map_time"
begin

lemma inj_map_st:
  "inj map_st"
  unfolding map_st_def
  apply (rule injI)
  apply (clarsimp split: prod.split_asm)
  apply intros
  subgoal for L1 s1 L2 s2
    using map_loc_inj by - (rule map_index_inj[where S = UNIV and T = UNIV], auto elim: injD)
  subgoal for L1 s1 L2 s2
    apply (rule ext)
    subgoal for x
      apply (drule cong[OF _ HOL.refl, where x = "map_var x"])
      using map_var_inj apply (auto simp add: the_inv_f_f  split: if_split_asm)
       apply (clarsimp simp: dom_def image_def; metis)+     
      done
    done
  done

lemma N_eq:
  \<open>N i = automaton_of (automata ! i)\<close> if \<open>i < n_ps\<close>
  using that unfolding N_def n_ps_def fst_conv snd_conv by (intro nth_map; simp)

lemma covn_N_eq:
  \<open>N i = automaton_of (automata ! i)\<close> if \<open>i < n_ps\<close>
  using that unfolding N_def n_ps_def fst_conv snd_conv by (intro nth_map; simp)

lemma L_len[intro, dest]:
  "length L = n_ps" if "L \<in> states"
  using that unfolding states_def by simp

context
begin

private lemma 2:
  "Simple_Network_Language.conv_A o automaton_of = (\<lambda>(commited, trans, inv).
    (set commited,
     set (map Simple_Network_Language.conv_t trans),
     default_map_of [] (map (\<lambda> (l, g). (l, conv_cc g)) inv)))"
  apply (rule ext)
  apply clarsimp
  unfolding Simple_Network_Language.conv_A_def automaton_of_def
  apply (clarsimp split: prod.split)
  unfolding default_map_of_def
  unfolding FinFun.map_default_def
  apply (rule ext)
  subgoal for xs a
    by (induction xs) auto
  done

lemma aux_4:
  "(\<lambda> l. if l \<in> map_loc i ` fst ` set inv then map_cc (default_map_of [] inv (the_inv (map_loc i) l)) else [])
= default_map_of [] (map (\<lambda> (l, g). (map_loc i l, map_cc g)) inv)"
  for inv
  unfolding default_map_of_def FinFun.map_default_def
  using map_loc_inj
  apply (intro ext)
  apply (clarsimp, safe)
   apply (auto split: option.split simp: the_inv_f_f simp: map_of_eq_None_iff)
  subgoal for a b v v'
    by (auto dest: map_of_mapk_SomeI[rotated 1, where f = "map_loc i" and g = map_cc])
  subgoal
    by (auto 4 4 dest: map_of_SomeD)
  done

(*
lemma aux_4:
  "map_cc o default_map_of [] inv o the_inv (map_loc i)
= default_map_of [] (map (\<lambda> (l, g). (map_loc i l, map_cc g)) inv)"
  for inv
unfolding default_map_of_def
  unfolding FinFun.map_default_def
  apply (rule ext)
  apply auto
  apply (auto split: option.split)
  apply (simp add: map_cc_def)
  unfolding map_of_eq_None_iff

  sorry
*)

private lemma 3:
  "map.n_ps = n_ps"
  by (simp add: Prod_TA_Defs.n_ps_def)

private lemma 4:
  "map.N i = map_single i (N i)" if "i < n_ps"
  using that unfolding n_ps_def Prod_TA_Defs.N_def fst_conv snd_conv
  apply (subst nth_map_index)
   apply simp
  apply (subst nth_map)
   apply simp
  unfolding automaton_of_def
  unfolding map_single_def map_t_single_def
  unfolding map_automaton_def
  apply (auto split: prod.split)
  unfolding comp_def
  apply (rule aux_4[symmetric])
  done

private lemma 5:
  "inv (map.N i) = (\<lambda> l. if l \<in> map_loc i ` fst ` set (snd (snd (automata ! i))) then map_cc (inv (N i) (the_inv (map_loc i) l)) else [])" if "i < n_ps"
  unfolding 4[OF that] unfolding map_single_def inv_def by (auto split: prod.split)

(*
private lemma 5:
  "inv (map.N i) = map_cc o inv (N i) o the_inv (map_loc i)" if "i < n_ps"
  unfolding 4[OF that] unfolding map_single_def inv_def by (simp split: prod.split)
*)

private lemma 6:
  "map.bounds = (\<lambda> x. if x \<in> map_var ` dom bounds then bounds (the_inv map_var x) else None)"
  unfolding map.bounds_def bounds_def comp_def
  apply (rule ext)
  apply (auto simp: map_of_mapk_SomeI[OF map_var_inj] the_inv_f_f[OF map_var_inj])
  apply (auto simp: map_of_eq_None_iff dom_map_of_conv_image_fst)
  done

private lemma 7:
  "trans (map.N i) = map_t_single i ` (trans (N i))"  if "i < n_ps"
  unfolding 4[OF that] unfolding map_single_def trans_def by (simp split: prod.split)

private lemma 71:
  "(map_loc i l, map_cc g, map_act map_action a, map_expr u, map map_clock r, map_loc i l')
  \<in> trans (map.N i)"
  if "(l, g, a, u, r, l') \<in> trans (N i)" "i < n_ps"
  using that(1) by (subst 7[OF \<open>i < n_ps\<close>]) (force simp: map_t_single_def)

lemma map_ac_inj:
  "ac = ac'" if "map_ac ac = map_ac ac'"
  using map_clock_inj map_time_inj that by (cases ac; cases ac'; auto simp: map_ac_def dest: injD)

lemma map_cc_inj:
  "cc = cc'" if "map_cc cc = map_cc cc'"
  using that unfolding map_cc_def map_ac_def[symmetric]
  by (subst (asm) inj_map_eq_map) (auto simp: map_ac_inj intro: injI)

(*
private lemma 72:
  "(map_loc i l, map_cc g, map_act map_action a, map_expr u, map map_clock r, map_loc i l')
  \<in> trans (map.N i) \<longleftrightarrow> (l, g, a, u, r, l') \<in> trans (N i)
" if "i < n_ps"
  using map_loc_inj map_expr_inj 
  apply (subst 7[OF that])
  apply (auto simp: map_t_single_def dest: map_cc_inj)
  subgoal
    apply (intros add: more_intros)
     apply assumption
    apply simp
    done
  done
*)

private lemma 73:
  "\<exists>l1 g' a' u' r' l1'.
    l = map_loc i l1 \<and> g = map_cc g' \<and> a = map_act map_action a' \<and>
    u = map_expr u' \<and> r = map map_clock r' \<and> l' = map_loc i l1' \<and>
    (l1, g', a', u', r', l1') \<in> trans (N i)"
  if "(l, g, a, u, r, l')\<in>trans (map.N i)" "i < n_ps"
  using that(1) by (subst (asm) 7[OF \<open>i < n_ps\<close>]) (force simp: map_t_single_def)

lemma f_the_inv_f:
  "f (the_inv f x) = x" if "inj f" "x \<in> range f"
  using that by (auto simp: the_inv_f_f)

lemma 8[simp]:
  "map.states = map_index map_loc ` states"
  unfolding map.states_def states_def 3
  apply safe
  subgoal for x
    apply (rule image_eqI[where x = "map_index (\<lambda>i. the_inv (map_loc i)) x"])
     apply (subst map_index'_comp)
     apply (rule sym, rule map_index_congL, subst comp_def)
     apply (intros add: allI impI)
    subgoal for p
     apply (rule f_the_inv_f)
    using map_loc_inj apply blast
    apply (simp only:)
    apply (erule allE, erule (1) impE)
    apply (subst (asm) 7, assumption)
    apply (force simp: map_t_single_def)
    done
  apply (intros add: more_intros)
  apply simp
  apply (erule allE, erule (1) impE)
apply (subst (asm) 7, assumption)
  unfolding map_t_single_def
  apply clarsimp
  apply (erule bexI[rotated])
  using map_loc_inj
  apply (auto simp: the_inv_f_f dest: injD)
  done
  apply (simp; fail)
  apply (fastforce dest!: 71)
  done

private lemma 9:
  "commited (map.N p) = map_loc p ` commited (N p)" if \<open>p < n_ps\<close>
  unfolding 4[OF that] unfolding map_single_def commited_def by (simp split: prod.split)

private lemma 10:
  "map.broadcast = map_action ` set broadcast"
  unfolding map.broadcast_def by simp

definition
  "N' p = map.N p"

lemma SilD:
  assumes "Sil a = map_act map_action a1"
  obtains a' where "a1 = Sil a'"
  using assms by (cases a1) auto

lemma map_loc_injD:
  "x = y" if "map_loc p x = map_loc p y"
  using that map_loc_inj by (blast dest: injD)

lemma bounded_mapD_aux:
  assumes "x \<in> dom (\<lambda>x. s (map_var x))"
  shows "map_var x \<in> dom s"
  using assms by auto

lemma map_var_bounds':
  assumes "map_var x \<in> dom map.bounds"
  shows "x \<in> fst ` set bounds'"
  using assms unfolding map.bounds_def by (auto dest!: map_of_SomeD injD[OF map_var_inj])

lemma map_of_domD:
  "\<exists> y. map_of xs x = Some y" if "x \<in> fst ` set xs"
  apply (fo_rule domD) using that unfolding dom_map_of_conv_image_fst .

lemma map_bounds_bounds':
  "map.bounds (map_var x) = map_of bounds' x" if "x \<in> fst ` set bounds'"
  unfolding map.bounds_def using that
  by (auto simp: Map.map_of_mapk_SomeI[OF map_var_inj] dest!: map_of_domD)

lemma bounded_mapD:
  "bounded bounds (s \<circ> map_var)" if "bounded map.bounds s"
  using that unfolding comp_def bounded_def
  apply elims
  apply intros
  subgoal premises prems
    using prems(1)
    unfolding map.bounds_def dom_map_of_conv_image_fst bounds_def fst_conv snd_conv
    by (auto 4 4 dest: injD[OF map_var_inj])
  subgoal for x
    apply (drule bounded_mapD_aux)
    apply simp
    apply (frule map_var_bounds')
    apply (drule (1) bspec)
    apply (auto simp add: bounds_def map_bounds_bounds')
    done
  subgoal for x
    apply (drule bounded_mapD_aux)
    apply simp
    apply (frule map_var_bounds')
    apply (drule (1) bspec)
    apply (auto simp add: bounds_def map_bounds_bounds')
    done
  done

inductive_cases check_bexp_elims:
  "check_bexp s (bexp.not b) bv"
  "check_bexp s (bexp.and b1 b2) bv"
  "check_bexp s (bexp.or b1 b2) bv"
  "check_bexp s (bexp.imply b1 b2) bv"
  "check_bexp s (le i x) bv"
  "check_bexp s (lt i x) bv"
  "check_bexp s (ge i x) bv"
  "check_bexp s (eq i x) bv"
  "check_bexp s (gt i x) bv"

method fprem =
  (match premises in R: _ \<Rightarrow> \<open>rule R[elim_format]\<close>, assumption)

lemma map_var_check_bexp:
  "check_bexp (\<lambda>x. s (map_var x)) b bv" if "check_bexp s (map_bexp map_var id b) bv"
  using that by (induction b arbitrary: bv) (auto intro: check_bexp.intros elim!: check_bexp_elims)

inductive_cases is_val_elims:
  "is_val s (const c) d"
  "is_val s (var x)   v"
  "is_val s (if_then_else b e1 e2) v"

lemma map_var_is_val:
  "is_val (\<lambda>x. s (map_var x)) e v" if "is_val s (map_exp map_var id e) v"
  using that
  by (induction e arbitrary: v) (auto elim!: is_val_elims map_var_check_bexp intro: is_val.intros)

lemma
  "(m(x\<mapsto>y) o f) = (m o f)(the_inv f x \<mapsto> y)" if "inj f" "x \<in> range f" for f :: "'a \<Rightarrow> 'b"
  by (rule ext) (auto simp: the_inv_f_f[OF that(1)] f_the_inv_f[OF that])

lemma is_upd_mapD:
  assumes "is_upd s (map_expr ac) s'"
  shows "is_upd (s o map_var) ac (s' o map_var)"
  using assms
  unfolding is_upd_def map_expr_def comp_def
  unfolding list_all2_map1
  apply -
  apply elims
  apply (simp split: prod.splits cong: list.rel_cong_simp add: case_prod_conv)
  subgoal for xs
    apply (inst_existentials "map (\<lambda> (x, e). (the_inv map_var x, e)) xs")
    subgoal premises prems
      using prems(1)
      apply (induction rule: list_all2_induct)
       apply simp
      apply (clarsimp split: prod.split)
      apply intros
       apply (simp add: the_inv_f_f[OF map_var_inj])
      apply (erule map_var_is_val)
      done
    subgoal premises prems
      apply (subgoal_tac "fst ` set xs \<subseteq> range map_var")
      apply (rule ext)
      apply (subst fold_map, simp add: comp_def)
      subgoal for x
        apply (induction xs arbitrary: s)
         apply simp
        apply simp
        apply (fo_rule cong)
         apply (fo_rule fold_cong)
           apply auto
        apply (rule ext)
        unfolding fun_upd_def
        apply (auto simp: the_inv_f_f[OF map_var_inj] injD[OF map_var_inj])
        done
      using prems(1)[THEN list_all2_set2]
      apply auto
      done
    done
  done

lemma bounded_domD:
  "dom s = dom bounds" if "bounded bounds s"
  using that unfolding bounded_def ..

lemma dom_map_bounds:
  "dom map.bounds = map_var ` dom bounds"
  unfolding map.bounds_def bounds_def by (force simp: dom_map_of_conv_image_fst)

lemma bounded_map_domD:
  "dom s = map_var ` dom bounds" if "bounded map.bounds s"
  using that unfolding bounded_def dom_map_bounds ..

lemma
  "fold (\<lambda>p L . L[p := ls' p]) ps L[p := l'] = fold (\<lambda>p L . L[p := ls' p]) ps (L[p := l'])"
  if "p \<notin> set ps" for ps ls' p l'
  using that by (induction ps arbitrary: L) (auto simp: list_update_swap)

lemma map_index_update:
  "map_index f (xs[i := a]) = map_index f xs[i := f i a]"
  by (rule nth_equalityI) (auto simp: nth_list_update')

lemma check_bexp_map_var:
  assumes "check_bexp s b bv"
  shows
   "check_bexp (\<lambda>x. if x \<in> map_var ` dom s then s (the_inv map_var x) else None)
    (map_bexp map_var id b) bv"
  using assms by induction (auto 4 4 intro: check_bexp.intros simp: the_inv_f_f[OF map_var_inj])

lemma is_val_map_var:
  assumes "is_val s e v"
  shows
    "is_val (\<lambda>x. if x \<in> map_var ` dom s then s (the_inv map_var x) else None)
    (map_exp map_var id e) v"
  supply [simp] = the_inv_f_f[OF map_var_inj]
  using assms
  apply induction
  subgoal
    by (auto intro!: is_val.intros)
  subgoal
    by (auto 4 3 intro!: is_val.intros)
  by (auto intro!: is_val.intros simp: id_def split del: if_split dest!: check_bexp_map_var)

lemma map_bounds_bounds:
  "the (map.bounds x) = the (bounds (the_inv map_var x))" if "x \<in> map_var ` dom bounds"
  using that unfolding map.bounds_def bounds_def
  by (auto simp: the_inv_f_f[OF map_var_inj] map_of_mapk_SomeI[OF map_var_inj])

lemma map_bounds_dom:
  "the_inv map_var x \<in> dom bounds" if "x \<in> map_var ` dom bounds"
  using that by (auto simp: the_inv_f_f[OF map_var_inj])

lemma bounded_map_boundsI:
  assumes "bounded bounds s"
  shows
    "bounded map.bounds (\<lambda>x. if x \<in> map_var ` dom s then s (the_inv map_var x) else None)"
  using assms unfolding bounded_def dom_map_bounds
  apply (elims; intros)
  subgoal premises prems
    using prems(1) by (auto split: if_split_asm) (auto simp: the_inv_f_f[OF map_var_inj])
  by (auto dest!: map_bounds_dom simp: map_bounds_bounds)

lemma is_upd_mapI:
  assumes
    "is_upd s f s'"
  shows
    "is_upd (\<lambda>x. if x \<in> map_var ` dom s then s (the_inv map_var x) else None)
          (map_expr f)
          (\<lambda>x. if x \<in> map_var ` dom s' then s' (the_inv map_var x) else None)"
  using assms
  unfolding is_upd_def
  apply elims
  subgoal for xs
    apply (inst_existentials "map (\<lambda> (x, v). (map_var x, v)) xs")
    subgoal premises prems
      using prems(1)
      by (induction rule: list_all2_induct) (auto intro: is_val_map_var simp: map_expr_def)
    subgoal premises prems
      unfolding \<open>s' = _\<close>
      apply (rule ext)
      apply auto
      subgoal for x
        apply (induction xs arbitrary: s)
         apply auto
        apply (fo_rule cong, fo_rule fold_cong, rule ext)
           apply (auto simp: the_inv_f_f[OF map_var_inj])
        done
      subgoal for x
        apply (induction xs arbitrary: s)
         apply (simp; fail)
        subgoal premises prems for a xs s
          using prems(2)
          apply simp
          apply (cases a)
          apply (subst prems(1)[of "(\<lambda>(x, v). s(x \<mapsto> v)) a"])
           apply (simp; fail)
          apply (fo_rule cong, fo_rule fold_cong, rule ext)
             apply (auto simp: the_inv_f_f[OF map_var_inj])
          done
        done
      done
    done
  done

lemma map_trans_int:
  "map.trans_int = map_t ` trans_int"
  unfolding map.trans_int_def trans_int_def
  supply [simp] = L_len
  apply standard
  subgoal
    apply (clarsimp simp: map_t_def map_t_single_def 3 7 9)
    apply (rule SilD, assumption)
    apply (drule map_loc_injD[THEN sym])
    apply simp
    apply (drule is_upd_mapD)
    apply (frule bounded_mapD, drule bounded_map_domD)
    apply (frule bounded_mapD, drule bounded_map_domD)
    apply (intros add: more_intros)
            apply solve_triv+
          apply (auto dest: map_loc_injD; fail)
         apply solve_triv+
    subgoal
      unfolding map_st_def
      by (auto 4 4 simp: the_inv_f_f[OF map_var_inj] map_index_update[symmetric] intro!: ext)
    done
  subgoal
    apply (rule subsetI, clarsimp simp: Simple_Network_Language.conv_t_def 3 7 9)
    unfolding map_t_def
    apply (simp add: map_st_def map_index_update)
    apply (drule (1) 71)
    apply (drule is_upd_mapI)
    apply (drule bounded_map_boundsI)+
    apply (intros add: more_intros)
          apply solve_triv+
        apply (auto dest: map_loc_injD simp: 9; fail)
       apply solve_triv+
    done
  done

lemma InD:
  assumes "In a = map_act map_action a1"
  obtains a' where "a1 = In a'"
  using assms by (cases a1) auto

lemma OutD:
  assumes "Out a = map_act map_action a1"
  obtains a' where "a1 = Out a'"
  using assms by (cases a1) auto

lemma map_cc_append:
  "map_cc (g1 @ g2) = map_cc g1 @ map_cc g2"
  unfolding map_cc_def by simp

lemma map_trans_bin:
  "map.trans_bin = map_t ` trans_bin"
unfolding map.trans_bin_def trans_bin_def
  supply [simp] = L_len
  apply standard
  subgoal
    apply (clarsimp simp: map_t_def map_t_single_def 3 7 9)
    apply (rule InD, assumption)
    apply (rule OutD, assumption)
    apply (drule map_loc_injD[THEN sym])
    apply (drule map_loc_injD[THEN sym])
    apply (simp add: injD[OF map_action_inj])
    apply (drule injD[OF map_action_inj])
    apply (drule is_upd_mapD)
    apply (drule is_upd_mapD)
    apply (frule bounded_mapD, drule bounded_map_domD)
    apply (frule bounded_mapD, drule bounded_map_domD)
    apply (intros add: more_intros)
                  apply solve_triv+
                apply (auto dest: map_loc_injD; fail)
                apply solve_triv+
    subgoal
      unfolding map_st_def
      by (auto 4 3
          simp: the_inv_f_f[OF map_var_inj] map_index_update[symmetric] map_cc_def intro!: ext)
      done
  subgoal
    apply (rule subsetI, clarsimp simp: Simple_Network_Language.conv_t_def 3 7 9)
    unfolding map_t_def
    apply (simp add: map_st_def map_index_update map_cc_append)
    apply (drule (1) 71)+
    apply (drule is_upd_mapI)+
    apply (drule bounded_map_boundsI)+
    apply (intros add: more_intros)
          apply solve_triv+
        apply (auto dest: map_loc_injD simp: 9; fail)
       apply solve_triv+
    done
  done

lemma n_ps_rangeD:
  "p < n_ps" if "p \<in> set ps" "set ps \<subseteq> {0..<n_ps}"
  using that by auto

lemma map_cc_concat:
  "map_cc (concat gs) = concat (map map_cc gs)"
  unfolding map_cc_def by (simp add: map_concat)

private lemma 711:
  "(map_index map_loc L ! i, map_cc g, map_act map_action a, map_expr u, map map_clock r, map_loc i l')
  \<in> trans (map.N i)"
  if "(L ! i, g, a, u, r, l') \<in> trans (N i)" "i < n_ps" "length L = n_ps"
  using 71[OF that(1,2)] that(2,3) by simp

lemma is_upds_mapI:
  assumes "is_upds s' (map fs ps) s''"
  shows
  "is_upds (\<lambda>x. if x \<in> map_var ` dom s' then s' (the_inv map_var x) else None)
        (map (\<lambda>a. map_expr (fs a)) ps)
        (\<lambda>x. if x \<in> map_var ` dom s'' then s'' (the_inv map_var x) else None)"
  sorry

lemma map_trans_broad_aux1:
  "map_index map_loc (fold (\<lambda>p L. L[p := ls' p]) ps L) =
  fold (\<lambda>p L. L[p := map_loc p (ls' p)]) ps (map_index map_loc L)"
  by (induction ps arbitrary: L) (auto simp: map_index_update)

lemma InD2:
  assumes "In (map_action a) = map_act map_action a'"
  shows "a' = In a"
  using assms by (cases a')  (auto simp: injD[OF map_action_inj])

lemma map_trans_broad:
  "map.trans_broad = map_t ` trans_broad"
  unfolding map.trans_broad_alt_def trans_broad_alt_def
  apply standard
   supply [simp] = L_len
  subgoal sorry
  subgoal
    apply (rule subsetI)
    apply (clarsimp simp:
        Simple_Network_Language.conv_t_def 3 7 9 10 map_concat broadcast_def)
    unfolding map_t_def
    apply (drule (1) 711, (simp; fail))
    apply (drule is_upd_mapI is_upds_mapI bounded_map_boundsI)+
    apply (simp add: map_st_def map_index_update map_cc_append map_cc_concat map_trans_broad_aux1)
    apply (intros add: more_intros)
                   apply solve_triv+
                  apply (simp add: map_concat; fail)
                 apply solve_triv+
               apply (drule(1) bspec, drule 711, force, simp, simp)
    subgoal premises prems for a b aa ab ac ad ba L s s' s'' aj p g f r l' gs fs rs ls' ps
      using prems(4) \<open>p < n_ps\<close> \<open>set ps \<subseteq> _\<close> \<open>L \<in> states\<close> by (force dest: map_loc_injD simp: 9)
    subgoal premises prems for a b aa ab ac ad ba L s s' s'' aj p g f r l' gs fs rs ls' ps q
      using prems(5) \<open>q < n_ps\<close> \<open>q \<notin> set ps \<and> p \<noteq> q\<close> \<open>L \<in> states\<close>
      by (auto dest!: map_loc_injD InD2 simp: map_t_single_def)
            apply solve_triv+
           apply force
          apply solve_triv+
    apply (simp add: map_cc_def)
    done

lemma map_prod_ta:
  "map.prod_ta = map_A prod_ta"
  unfolding map.prod_ta_def prod_ta_def
  unfolding map.trans_prod_def trans_prod_def
  unfolding map.prod_inv_def prod_inv_def
  unfolding map.N_def N_def 3
  apply simp
  apply (rule conjI)
  subgoal
    unfolding image_Un
    by ((fo_rule arg_cong2)+; rule map_trans_int map_trans_bin map_trans_broad)
  subgoal \<comment>\<open>Invariant\<close>
    unfolding map.N_def N_def
    by (rule ext) (auto simp: 5 map_concat intro!: map_cong arg_cong[where f = concat])
  done

end (* Injectivity *)

end (* Mapping *)



paragraph \<open>Conversion from integers to reals commutes with product construction.\<close>

sublocale conv: Prod_TA_Defs
  "(set broadcast, map (Simple_Network_Language.conv_A o automaton_of) automata, map_of bounds')" .

lemma (in -) conv_ac_inj:
  "ac = ac'" if "conv_ac ac = conv_ac ac'"
  using that by (cases ac; cases ac'; auto)

lemma (in -) conv_cc_inj:
  "cc = cc'" if "conv_cc cc = conv_cc cc'"
  using that by (subst (asm) inj_map_eq_map) (auto simp add: conv_ac_inj intro: injI)

lemma (in Prod_TA_Defs) trans_broad_alt_def:
  "trans_broad =
    {((L, s), g @ concat (map gs ps), Broad a, r @ concat (map rs ps), (L', s'')) |
    L s L' s' s'' a p l g f r l' gs fs rs ls' ps.
      a \<in> broadcast  \<and>
      (l, g, Out a, f, r, l') \<in> trans (N p) \<and>
      (\<forall>p \<in> set ps. (L ! p, gs p, In a, fs p, rs p, ls' p) \<in> trans (N p)) \<and>
      (l \<in> commited (N p) \<or> (\<exists>p \<in> set ps. L ! p \<in> commited (N p))
      \<or> (\<forall>p < n_ps. L ! p \<notin> commited (N p))) \<and>
      (\<forall>q < n_ps. q \<notin> set ps \<and> p \<noteq> q \<longrightarrow> \<not> (\<exists>g f r l'. (L!q, g, In a, f, r, l') \<in> trans (N q))) \<and>
      L!p = l \<and>
      p < length L \<and> set ps \<subseteq> {0..<n_ps} \<and> p \<notin> set ps \<and> distinct ps \<and> sorted ps \<and> ps \<noteq> [] \<and>
      L' = fold (\<lambda>p L . L[p := ls' p]) ps L[p := l'] \<and> is_upd s f s' \<and> is_upds s' (map fs ps) s'' \<and>
      L \<in> states \<and> bounded bounds s \<and> bounded bounds s'' \<and>
      (\<forall>p. p\<notin>set ps \<longrightarrow> gs p = [])
    }"
  unfolding trans_broad_def
proof ((intro Collect_eqI iffI; elims add: more_elims), goal_cases)
  case prems: (1 x L s L' s' s'' a p l g f r l' gs fs rs ls' ps)
  let ?gs = "\<lambda>p. if p \<in> set ps then gs p else []"
  have *[simp]: "concat (map gs ps) = concat (map ?gs ps)"
    by (simp cong: map_cong)
  with prems show ?case
    by (inst_existentials L s L' s' s'' a p l g f r l' ?gs fs rs ls' ps; (assumption | simp))
next
  case (2 x L s L' s' s'' a p l g f r l' gs fs rs ls' ps)
  then show ?case
    by blast
qed

lemma N_eq:
  \<open>N i = automaton_of (automata ! i)\<close> if \<open>i < n_ps\<close>
  using that unfolding N_def n_ps_def fst_conv snd_conv by (intro nth_map; simp)

lemma covn_N_eq:
  \<open>N i = automaton_of (automata ! i)\<close> if \<open>i < n_ps\<close>
  using that unfolding N_def n_ps_def fst_conv snd_conv by (intro nth_map; simp)

lemma L_len[intro, dest]:
  "length L = n_ps" if "L \<in> states"
  using that unfolding states_def by simp

context
begin

private lemma 1:
  "conv (set broadcast, map automaton_of automata, map_of bounds') =
    (set broadcast, map (Simple_Network_Language.conv_A o automaton_of) automata, map_of bounds')"
  unfolding conv_def by simp

private lemma 2:
  "Simple_Network_Language.conv_A o automaton_of = (\<lambda>(commited, trans, inv).
    (set commited,
     set (map Simple_Network_Language.conv_t trans),
     default_map_of [] (map (\<lambda> (l, g). (l, conv_cc g)) inv)))"
  apply (rule ext)
  apply clarsimp
  unfolding Simple_Network_Language.conv_A_def automaton_of_def
  apply (clarsimp split: prod.split)
  unfolding default_map_of_def
  unfolding FinFun.map_default_def
  apply (rule ext)
  subgoal for xs a
    by (induction xs) auto
  done

private lemma 3:
  "conv.n_ps = n_ps"
  by (simp add: Prod_TA_Defs.n_ps_def)

private lemma 4:
  "conv.N i = Simple_Network_Language.conv_A (N i)" if "i < n_ps"
  using that unfolding n_ps_def Prod_TA_Defs.N_def fst_conv snd_conv by (subst nth_map | simp)+

private lemma 5:
  "inv (conv.N i) = conv_cc o (inv (N i))" if "i < n_ps"
  unfolding 4[OF that] unfolding Simple_Network_Language.conv_A_def by (simp split: prod.split)

private lemma 6[simp]:
  "conv.bounds = bounds"
  unfolding conv.bounds_def bounds_def by simp

private lemma 7:
  "trans (conv.N i) = Simple_Network_Language.conv_t ` (trans (N i))"  if "i < n_ps"
  unfolding 4[OF that] unfolding Simple_Network_Language.conv_A_def by (simp split: prod.split)

private lemma 71:
  "(l, conv_cc g, a, r, u, l')\<in>Simple_Network_Language.trans (conv.N i)"
  if "(l, g, a, r, u, l')\<in>Simple_Network_Language.trans (N i)" "i < n_ps"
  using that by (force simp add: 7 Simple_Network_Language.conv_t_def)

private lemma 72:
  "(l, conv_cc g, a, r, u, l')\<in>Simple_Network_Language.trans (conv.N i)
\<longleftrightarrow> (l, g, a, r, u, l')\<in>Simple_Network_Language.trans (N i)
" if "i < n_ps"
  apply (auto simp add: 7[OF that] Simple_Network_Language.conv_t_def dest: conv_cc_inj)
  subgoal
    apply (intros add: more_intros)
     apply assumption
    apply simp
    done
  done

private lemma 73:
  "\<exists>g'. g = conv_cc g' \<and> (l, g', a, r, u, l')\<in>Simple_Network_Language.trans (N i)"
  if "(l, g, a, r, u, l')\<in>Simple_Network_Language.trans (conv.N i)" "i < n_ps"
  using that by (force simp add: 7 Simple_Network_Language.conv_t_def)

lemma 8[simp]:
  "conv.states = states"
  unfolding conv.states_def states_def 3
  by (auto simp add: 7 Simple_Network_Language.conv_t_def) (fastforce, force)

private lemma 9:
  "commited (conv.N p) = commited (N p)" if \<open>p < n_ps\<close>
  unfolding 4[OF that] unfolding Simple_Network_Language.conv_A_def by (simp split: prod.split)

private lemma 10:
  "conv.broadcast = set broadcast"
  unfolding conv.broadcast_def by simp

lemma conv_trans_int:
  "conv.trans_int = (\<lambda>(l, g, a, r, l'). (l, map conv_ac g, a, r, l')) ` trans_int"
  unfolding conv.trans_int_def trans_int_def
  supply [simp] = L_len
  apply standard
  subgoal
    by (clarsimp simp: Simple_Network_Language.conv_t_def 3 7 9)
      (intros add: more_intros, solve_triv+)
  subgoal
    by (rule subsetI, clarsimp simp: Simple_Network_Language.conv_t_def 3 7 9[symmetric])
      ((drule (1) 71)+, intros add: more_intros, solve_triv+)
  done

lemma conv_trans_bin:
  "conv.trans_bin = (\<lambda>(l, g, a, r, l'). (l, map conv_ac g, a, r, l')) ` trans_bin"
  unfolding conv.trans_bin_def trans_bin_def
  supply [simp] = L_len
  apply standard
  subgoal
    by (clarsimp simp add: Simple_Network_Language.conv_t_def 3 7 9)
      (intros add: more_intros, solve_triv+)
  subgoal
    by (rule subsetI, clarsimp simp add: Simple_Network_Language.conv_t_def 3 7 9[symmetric])
      ((drule (1) 71)+, intros add: more_intros, solve_triv+)
  done

lemma n_ps_rangeD:
  "p < n_ps" if "p \<in> set ps" "set ps \<subseteq> {0..<n_ps}"
  using that by auto

lemma conv_trans_broad:
  "conv.trans_broad = (\<lambda>(l, g, a, r, l'). (l, map conv_ac g, a, r, l')) ` trans_broad"
  unfolding conv.trans_broad_alt_def trans_broad_alt_def
  apply standard
   supply [simp] = L_len
  subgoal
  proof -
    have **: "\<exists> gs'. gs = conv_cc o gs' \<and>
          (\<forall>p\<in>set ps.(L ! p, gs' p, In a, fs p, rs p, ls' p) \<in> trans (N p))"
      if assms:
        "\<forall>p\<in>set ps. (L ! p, gs p, In a, fs p, rs p, ls' p) \<in> trans (conv.N p)"
        "set ps \<subseteq> {0..<n_ps}" "\<forall>p. p \<notin> set ps \<longrightarrow> gs p = []"
      for L ps gs a fs rs ls'
    proof -
      have *: "gs p = conv_cc (Hilbert_Choice.inv conv_cc (gs p))" if "p \<in> set ps" for p
        using that assms by (auto 4 3 simp: f_inv_into_f dest!: 73)
      show ?thesis
        apply (inst_existentials "Hilbert_Choice.inv conv_cc o gs")
        subgoal
          apply (rule ext)
          subgoal for p
            apply (cases "p \<in> set ps")
            subgoal
              by (simp, erule *)
            subgoal
              using that(3) by (auto intro: injI inv_f_eq conv_ac_inj)
            done
          done
        subgoal
          using that * by (force dest!: conv_cc_inj 73)
        done
    qed
    have *: "set ps \<subseteq> {0..<n_ps} \<longleftrightarrow> (\<forall>p \<in> set ps. p < n_ps)" for ps
      by auto
    show ?thesis
      apply (rule subsetI)
      apply (clarsimp simp add: 3 9 10 broadcast_def split: prod.split_asm)
      apply (drule (2) **)
      apply (drule (1) 73)+
      apply elims
      apply (intro image_eqI[rotated] CollectI exI conjI)
                        apply solve_triv+
      subgoal premises prems \<comment>\<open>Commited\<close>
        using prems(2) \<open>set _ \<subseteq> {0..<n_ps}\<close> by (auto dest: n_ps_rangeD simp: 9)
      subgoal premises prems for L s s' s'' ae p g f r l' gs fs rs ls' ps gs' g' \<comment>\<open>Maximal set\<close>
        using prems(3,17-) 71 by blast
      by solve_triv+ (simp split: prod.split add: map_concat)
  qed
  subgoal
    apply (rule subsetI)
    apply (clarsimp simp:
        Simple_Network_Language.conv_t_def 3 7 9[symmetric] 10 broadcast_def map_concat)
    apply (drule (1) 71)
    apply (intros add: more_intros)
                   apply solve_triv+
               apply (subst comp_def; rule 71; fast elim: n_ps_rangeD; fail)
    subgoal premises prems for L s s' s'' aj p g f r l' gs fs rs ls' ps
      using prems(3,6) 9 by fastforce
    subgoal premises prems for L s s' s'' aj p g f r l' gs fs rs ls' ps q ga fa ra l'a
      using prems(4,9-) 9 by auto
    by (solve_triv | blast)+
  done

lemma conv_prod_ta:
  "conv.prod_ta = Normalized_Zone_Semantics_Impl.conv_A prod_ta"
  unfolding conv.prod_ta_def prod_ta_def
  unfolding conv.trans_prod_def trans_prod_def
  unfolding conv.prod_inv_def prod_inv_def
  unfolding conv.N_def N_def 3
  apply simp
  apply (rule conjI)
  subgoal
    unfolding image_Un
    by ((fo_rule arg_cong2)+; rule conv_trans_int conv_trans_bin conv_trans_broad)
  subgoal \<comment>\<open>Invariant\<close>
    unfolding conv.N_def N_def
    by (rule ext) (auto simp: 5 map_concat intro!: map_cong arg_cong[where f = concat])
  done

end (* Anonymous context for private lemmas *)

paragraph \<open>Fundamentals\<close>

definition "clkp_set' \<equiv>
    (\<Union> A \<in> set automata. UNION (set (snd (snd A))) (collect_clock_pairs o snd))
  \<union> (\<Union> A \<in> set automata. \<Union> (l, g, _) \<in> set (fst (snd A)). collect_clock_pairs g)"

definition clk_set'  where
  \<open>clk_set'  =
  fst ` clkp_set' \<union>
  (\<Union> A \<in> set automata. \<Union> (_, _, _, _, r, _) \<in> set (fst (snd A)). set r)\<close>

lemma collect_clock_pairs_invsI:
  "(a, b) \<in> \<Union> ((collect_clock_pairs o snd) ` set invs)"
  if "(a, b) \<in> collect_clock_pairs (default_map_of [] invs l)"
proof -
  from that obtain x where "(a, b) = constraint_pair x" "x \<in> set (default_map_of [] invs l)"
    unfolding collect_clock_pairs_def by auto
  then have "x \<in> \<Union> (set ` range (default_map_of [] invs))"
    by auto
  then have "x \<in> \<Union> (set ` snd ` (set invs \<union> {}))"
  proof -
    have "[] \<noteq> default_map_of [] invs l"
      using that by force
    then have "default_map_of [] invs l \<in> snd ` set invs"
      by (metis (no_types) UNIV_I Un_insert_right range_default_map_of[of "[]" "invs"]
            image_eqI insertE subsetCE sup_bot.right_neutral)
    then show ?thesis
      using \<open>x \<in> set (default_map_of [] invs l)\<close> by blast
  qed
  then have "x \<in> \<Union> (set ` snd ` set invs)"
    by auto
  with \<open>(a, b) = _\<close> show ?thesis
    unfolding collect_clock_pairs_def
    by auto
qed

lemma mem_trans_N_iff:
  "t \<in> Simple_Network_Language.trans (N i) \<longleftrightarrow> t \<in> set (fst (snd (automata ! i)))" if "i < n_ps"
  unfolding N_eq[OF that] by (auto split: prod.splits simp: automaton_of_def)

lemma length_automata_eq_n_ps:
  "length automata = n_ps"
  unfolding n_ps_def by simp

lemma clkp_set'_subs:
  "Timed_Automata.clkp_set prod_ta \<subseteq> clkp_set'"
  unfolding Timed_Automata.clkp_set_def clkp_set'_def
  apply (rule union_subsetI)
  subgoal
    unfolding Timed_Automata.collect_clki_def inv_of_prod prod_inv_def
    apply (auto simp: collect_clock_pairs_concat)
    apply (subst (asm) N_eq)
     apply assumption
    subgoal for a b L i
      apply (inst_existentials "automata ! i")
      subgoal
        unfolding automaton_of_def
        by (force dest!: collect_clock_pairs_invsI split: prod.split_asm)
      unfolding n_ps_def by auto
    done
  subgoal
    apply simp
    unfolding trans_prod_def Timed_Automata.collect_clkt_def
    apply safe
    subgoal
      unfolding trans_int_def
      by (auto 4 4 simp: length_automata_eq_n_ps mem_trans_N_iff)
    subgoal
      unfolding trans_bin_def
      by (fastforce
          simp: length_automata_eq_n_ps mem_trans_N_iff
          dest!: collect_clock_pairs_append_cases)
    subgoal
      unfolding trans_broad_def
      apply (clarsimp simp: length_automata_eq_n_ps mem_trans_N_iff)
      apply (drule collect_clock_pairs_append_cases)
      unfolding collect_clock_pairs_concat
      apply auto
           apply (fastforce simp: length_automata_eq_n_ps mem_trans_N_iff)+
      done
    done
  done

lemma collect_clkvt_subs:
  "collect_clkvt (trans_of prod_ta) \<subseteq>
    (\<Union> A \<in> set automata. \<Union> (_, _, _, _, r, _) \<in> set (fst (snd A)). set r)"
  apply simp
  unfolding collect_clkvt_def
  apply auto
  unfolding trans_prod_def
  subgoal
    apply simp
    unfolding trans_prod_def Timed_Automata.collect_clkt_def
    apply safe
    subgoal
      unfolding trans_int_def
      by (fastforce
          simp: length_automata_eq_n_ps mem_trans_N_iff
          dest!: collect_clock_pairs_append_cases)
    subgoal
      unfolding trans_bin_def
      by (fastforce
          simp: length_automata_eq_n_ps mem_trans_N_iff
          dest!: collect_clock_pairs_append_cases)
    subgoal
      unfolding trans_broad_def
      apply (clarsimp simp: length_automata_eq_n_ps mem_trans_N_iff)
      unfolding collect_clock_pairs_concat
      apply safe
           apply (fastforce simp: length_automata_eq_n_ps mem_trans_N_iff)+
      done
    done
  done

lemma clk_set'_subs: "clk_set prod_ta \<subseteq> clk_set'"
  using collect_clkvt_subs clkp_set'_subs unfolding clk_set'_def by auto

end (* Simple Network Impl *)


lemma (in Prod_TA_Defs) finite_range_invI:
  "finite (range prod_inv)" if assms: "\<forall> i < n_ps. finite (range (inv (N i)))"
proof -
  let ?N = "\<Union> (range ` inv ` N ` {0..<n_ps})"
  let ?X = "{I. set I \<subseteq> ?N \<and> length I \<le> n_ps}"
  have "finite ?N"
    using assms by auto
  then have "finite ?X"
    by (rule finite_lists_length_le)
  moreover have "range prod_inv \<subseteq> concat ` ?X"
  proof
    fix x assume "x \<in> range prod_inv"
    then obtain L where L:
      "x = concat (map (\<lambda>p. (inv (N p)) (L ! p)) [0..<n_ps])"
      unfolding prod_inv_def by auto
    then show "x \<in> concat ` ?X"
      by force
  qed
  ultimately show ?thesis by - (drule finite_subset; auto)
qed

definition (in Prod_TA_Defs)
  "loc_set =
  (\<Union> {fst ` trans (N p) | p. p < n_ps} \<union>
        \<Union> {(snd o snd \<circ> snd \<circ> snd \<circ> snd) ` trans (N p) | p. p < n_ps})"

lemma (in Prod_TA_Defs) states_loc_set:
  "states \<subseteq> {L. set L \<subseteq> loc_set \<and> length L = n_ps}"
  unfolding states_def loc_set_def
  apply (intros add: more_intros)
   apply (elims add: more_elims)
   apply (drule mem_nth)
   apply simp
   apply (elims add: allE, assumption)
   apply (simp split: prod.split_asm)
   apply (erule disjE; (intros add: disjI1 disjI2 more_intros, solve_triv+); fail)
  by (elims add: more_elims)

lemma (in Prod_TA_Defs) finite_states:
  assumes finite_trans: "\<forall>p < n_ps. finite (Simple_Network_Language.trans (N p))"
  shows "finite states"
proof -
  have "states \<subseteq> {L. set L \<subseteq> loc_set \<and> length L = n_ps}"
    by (rule states_loc_set)
  also from finite_trans have "finite \<dots>"
    unfolding loc_set_def by (intro finite_intros) auto
  finally show ?thesis .
qed

context Simple_Network_Impl
begin

lemma trans_N_finite:
  assumes "p < n_ps"
  shows "finite (Simple_Network_Language.trans (N p))"
  using assms by (subst N_eq) (auto simp: automaton_of_def split: prod.split)

lemma states_finite:
  "finite states"
  by (intros add: finite_states trans_N_finite)

lemma bounded_finite:
  "finite {s. bounded bounds s}"
proof -
  let ?l = "Min {fst (the (bounds x)) | x. x \<in> dom bounds}"
  let ?u = "Max {snd (the (bounds x)) | x. x \<in> dom bounds}"
  have "finite (dom bounds)"
    unfolding bounds_def by simp
  then have "{s. bounded bounds s} \<subseteq> {s. dom s = dom bounds \<and> ran s \<subseteq> {?l..?u}}"
    unfolding bounded_def
    apply clarsimp
    apply (rule conjI)
    subgoal for s v
      unfolding ran_is_image
      apply clarsimp
      subgoal for x l u
        by (rule order.trans[where b = "fst (the (bounds x))"]; (rule Min_le)?; force)
      done
    subgoal for s v
      unfolding ran_is_image
      apply clarsimp
      subgoal for x l u
        by (rule order.trans[where b = "snd (the (bounds x))"]; (rule Max_ge)?; force)
      done
    done
  also from \<open>finite (dom bounds)\<close> have "finite \<dots>"
    by (rule finite_set_of_finite_maps) rule
  finally show ?thesis .
qed

lemma trans_prod_finite:
  "finite trans_prod"
proof -
  have "finite trans_int"
  proof -
    have "trans_int \<subseteq>
      {((L, s), g, Internal a, r, (L', s')) | L s p l g a f r l' s' L'.
        L \<in> states \<and> bounded bounds s \<and> p < n_ps \<and>
        (l, g, Sil a, f, r, l') \<in> trans (N p) \<and>
        bounded bounds s'
        \<and> L' = L[p := l']
      }"
      unfolding trans_int_def by (force simp: L_len)
    also have "finite \<dots>"
    proof -
      have "finite {(a, b, c, d, e, f). (a, b, Sil c, d, e, f) \<in> trans (N p)}"
        if "p < n_ps" for p
        using [[simproc add: finite_Collect]] that
        by (auto intro: trans_N_finite finite_vimageI injI)
      with states_finite bounded_finite show ?thesis
        by defer_ex
    qed
    finally show ?thesis .
  qed
  moreover have "finite trans_bin"
  proof -
    have "trans_bin \<subseteq>
      {((L, s), g1 @ g2, Bin a, r1 @ r2, (L', s'')) |
        L s p q l1 g1 a f1 r1 l1' l2 g2 f2 r2 l2' s'' L'.
          L \<in> states \<and> bounded bounds s \<and>
          p < n_ps \<and> q < n_ps \<and>
          (l1, g1, In a,  f1, r1, l1') \<in> trans (N p) \<and>
          (l2, g2, Out a, f2, r2, l2') \<in> trans (N q) \<and>
          bounded bounds s'' \<and>
          L' = L[p := l1', q := l2']
    }"
      unfolding trans_bin_def by (fastforce simp: L_len) (* slow *)
    also have "finite \<dots>"
    proof -
      have "finite {(a, b, c, d, e, f). (a, b, In c, d, e, f) \<in> trans (N p)}"
        if "p < n_ps" for p
        using [[simproc add: finite_Collect]] that
        by (auto intro: trans_N_finite finite_vimageI injI)
      moreover have "finite {(a, b, d, e, f). (a, b, Out c, d, e, f) \<in> trans (N p)}"
        if "p < n_ps" for p c
        using [[simproc add: finite_Collect]] that
        by (auto intro: trans_N_finite finite_vimageI injI)
      ultimately show ?thesis
        using states_finite bounded_finite by defer_ex
    qed
    finally show ?thesis .
  qed
  moreover have "finite trans_broad"
  proof -
    define P where "P ps \<equiv> set ps \<subseteq> {0..<n_ps} \<and> distinct ps" for ps
    define Q where "Q a n gs fs rs \<equiv>
      (\<forall>p < n. \<exists> q < n_ps. \<exists> l l'. (l, gs ! p, In a, fs ! p, rs ! p, l') \<in> trans (N q)) \<and>
              length gs = n \<and> length fs = n \<and> length rs = n" for a n gs fs rs
    define tag where "tag x = True" for x :: 's
    have Q_I: "Q a (length ps) (map gs ps) (map fs ps) (map rs ps)"
      if "set ps \<subseteq> {0..<n_ps}" "\<forall>p\<in>set ps. (L ! p, gs p, In a, fs p, rs p, ls' p) \<in> trans (N p)"
      for ps :: "nat list" and L a gs fs rs ls'
      using that unfolding Q_def by (auto 4 4 dest!: nth_mem)
    have "trans_broad \<subseteq>
      {((L, s), g @ concat gs, Broad a, r @ concat rs, (L', s'')) |
      L s a p l g f r l' ps gs fs rs L' s''.
        L \<in> states \<and> bounded bounds s \<and> a \<in> set broadcast \<and>
        p < n_ps \<and>
        (l, g, Out a, f, r, l') \<in> trans (N p) \<and>
        P ps \<and>
        Q a (length ps) gs fs rs \<and>
        L' \<in> states \<and>
        bounded bounds s'' \<and>
        tag l'
    }"
      unfolding trans_broad_def broadcast_def
      apply (rule subsetI)
      apply (elims add: more_elims)
      apply (intros add: more_intros)
                apply solve_triv+
            apply (simp add: L_len; fail)
           apply assumption
          apply (unfold P_def; intros; assumption)
         apply (rule Q_I; assumption)
      subgoal
        by (blast intro: state_preservation_updI state_preservation_fold_updI)
       apply assumption
      unfolding tag_def ..
    also have "finite \<dots>"
    proof -
      have "finite {(a, b, d, e, f). (a, b, Out c, d, e, f) \<in> trans (N p)}"
        if "p < n_ps" for p c
        using [[simproc add: finite_Collect]] that
        by (auto intro: trans_N_finite finite_vimageI injI)
      moreover have "finite {ps. P ps}"
        unfolding P_def by (simp add: finite_intros)
      moreover have "finite {(gs, fs, rs). Q a n gs fs rs}" (is "finite ?S") for a n
      proof -
        let ?T = "\<Union> (trans ` N ` {0..<n_ps})"
        have "?S \<subseteq> {(gs, fs, rs).
          (set gs \<subseteq> (\<lambda>(_,g,_). g) ` ?T \<and> length gs = n) \<and>
          (set fs \<subseteq> (\<lambda>(_,_,_,f,_). f) ` ?T \<and> length fs = n) \<and>
          (set rs \<subseteq> (\<lambda>(_,_,_,_,r,_). r) ` ?T \<and> length rs = n)
        }"
          unfolding Q_def
          by safe (drule mem_nth; elims; drule spec; elims; force)+
        also have "finite \<dots>"
          using trans_N_finite by (intro finite_intros more_finite_intros) auto
        finally show ?thesis .
      qed
      ultimately show ?thesis
        using states_finite bounded_finite by defer_ex
    qed
    finally show ?thesis .
  qed
  ultimately show ?thesis
    by (simp add: trans_prod_def)
qed

lemma prod_inv_finite:
  "finite (range prod_inv)"
  apply (intros add: finite_range_invI)
  unfolding length_automata_eq_n_ps[symmetric]
  unfolding N_def
  unfolding automaton_of_def
  by (auto intro: finite_range_default_map_of split: prod.split)

end (* Simple Network Impl *)

paragraph \<open>Collecting variables from expressions.\<close>

fun vars_of_bexp where
  "vars_of_bexp (not e) = vars_of_bexp e"
| "vars_of_bexp (and e1 e2) = (vars_of_bexp e1 \<union> vars_of_bexp e2)"
| "vars_of_bexp (bexp.or e1 e2) = (vars_of_bexp e1 \<union> vars_of_bexp e2)"
| "vars_of_bexp (imply e1 e2) = (vars_of_bexp e1 \<union> vars_of_bexp e2)"
| "vars_of_bexp (eq i x) = {i}"
| "vars_of_bexp (le i x) = {i}"
| "vars_of_bexp (lt i x) = {i}"
| "vars_of_bexp (ge i x) = {i}"
| "vars_of_bexp (gt i x) = {i}"

fun vars_of_exp where
  "vars_of_exp (const c) = {}"
| "vars_of_exp (var x) = {x}"
| "vars_of_exp (if_then_else b e1 e2) = vars_of_bexp b \<union> vars_of_exp e1 \<union> vars_of_exp e2"

definition (in Prod_TA_Defs)
  "var_set =
  (\<Union>S \<in> {(fst \<circ> snd \<circ> snd \<circ> snd) ` trans (N p) | p. p < n_ps}.
    \<Union>f \<in> S. \<Union> (x, e) \<in> set f. {x} \<union> vars_of_exp e)"

locale Simple_Network_Impl_nat =
  Simple_Network_Impl automata
  for automata ::
    "(nat list \<times> (nat act, nat, nat, int, nat, int) transition list
      \<times> (nat \<times> (nat, int) cconstraint) list) list" +
  fixes m :: nat and num_states :: "nat \<Rightarrow> nat" and num_actions :: nat
  assumes has_clock: "m > 0"
  assumes non_empty: "0 < length automata"
    (* assumes "length automata = length state_nums" *)
  assumes trans_num_states:
    "\<forall>i < n_ps. let (_, trans, _) = (automata ! i) in \<forall> (l, _, _, _, _, l') \<in> set trans.
      l < num_states i \<and> l' < num_states i"
    and inv_num_states:
    "\<forall>i < n_ps. let (_, _, inv) = (automata ! i) in \<forall> (x, _) \<in> set inv. x < num_states i"
  assumes var_set:
    "\<forall>(_, trans, _) \<in> set automata. \<forall>(_, _, _, f, _, _) \<in> set trans.
      \<forall>(x, upd) \<in> set f. x < n_vs \<and> (\<forall>i \<in> vars_of_exp upd. i < n_vs)"
  assumes bounds:
    "\<forall> i < n_vs. fst (bounds' ! i) = i"
  assumes action_set:
    "\<forall>a \<in> set broadcast. a < num_actions"
    "\<forall>(_, trans, _) \<in> set automata. \<forall>(_, _, a, _, _, _) \<in> set trans. pred_act (\<lambda>a. a < num_actions) a"
  assumes clock_set:
    "\<forall>(_, trans, _) \<in> set automata. \<forall>(_, g, _, _, r, _) \<in> set trans.
      (\<forall>c \<in> set r. 0 < c \<and> c < m) \<and>
      (\<forall> (c, x) \<in> collect_clock_pairs g. 0 < c \<and> c < m \<and> x \<in> \<nat>)
      "
    "\<forall>(_, _, inv) \<in> set automata. \<forall>(l, g) \<in> set inv.
      (\<forall>c \<in> set r. 0 < c \<and> c < m) \<and>
      (\<forall> (c, x) \<in> collect_clock_pairs g. 0 < c \<and> c < m \<and> x \<in> \<nat>)
      "
begin

sublocale Reachability_Problem_no_ceiling prod_ta init "\<lambda>_. False" m
proof standard
  show "finite (trans_of prod_ta)"
    using trans_prod_finite by simp
next
  show "finite (range (inv_of prod_ta))"
    using prod_inv_finite by simp
next
  from clk_set'_subs have "clk_set prod_ta \<subseteq> clk_set'" .
  also have "\<dots> \<subseteq> {1..m}"
    using clock_set unfolding clk_set'_def clkp_set'_def by force
  finally show "clk_set prod_ta \<subseteq> {1..m}" .
next
  from clock_set have "\<forall>(_, d)\<in>clkp_set'. d \<in> \<nat>"
    unfolding clkp_set'_def by force
  then show "\<forall>(_, d)\<in>Timed_Automata.clkp_set prod_ta. d \<in> \<nat>"
    by (auto dest!: subsetD[OF clkp_set'_subs])
next
  show "0 < m"
    by (rule has_clock)
qed

end (* Simple Network Impl nat *)








(*
locale TA_Renum =
  fixes A :: "('a, 'c, int, 's) ta"
    and renum_act   :: "'a \<Rightarrow> 'a1"
    and renum_clock :: "'c \<Rightarrow> 'c1"
    and renum_state :: "'s \<Rightarrow> 's1"
  assumes renum_state_inj: "inj_on renum_state (Simulation_Graphs_TA.state_set A)"
      and renum_clock_inj: "inj renum_clock"
begin

definition
  "renum_cconstraint = map (map_acconstraint renum_clock id)"

definition A' :: "('a1, 'c1, int, 's1) ta" where
   "A' \<equiv> (
    (\<lambda>(l, g, a, r, l').
      (renum_state l, renum_cconstraint g, renum_act a, map renum_clock r, renum_state l'))
    ` trans_of A,
    renum_cconstraint o inv_of A o the_inv_into (Simulation_Graphs_TA.state_set A) renum_state
  )"

definition
  "map_u u = u o the_inv renum_clock"

lemma map_u_add:
  "map_u (u \<oplus> d) = map_u u \<oplus> d"
  by (auto simp: map_u_def cval_add_def)

lemma renum_state_inv[simp]:
  "the_inv_into (Simulation_Graphs_TA.state_set A) renum_state (renum_state l) = l"
  if "l \<in> Simulation_Graphs_TA.state_set A"
  using that by (intro the_inv_into_f_f renum_state_inj)

lemma renum_state_eqD:
  assumes "renum_state l = renum_state l'"
    "l \<in> Simulation_Graphs_TA.state_set A" "l' \<in> Simulation_Graphs_TA.state_set A"
  shows "l = l'"
  using assms renum_state_inj by (meson inj_onD)

definition clk_set where "clk_set \<equiv> Timed_Automata.clk_set A"

lemma map_u_renum_clock[simp]:
  "map_u u (renum_clock c) = u c" (* if "c \<in> clk_set" *)
  using that unfolding map_u_def by (simp add: the_inv_into_f_f renum_clock_inj clk_set_def)

lemma
  assumes "u \<turnstile>\<^sub>a conv_ac ac" (* "constraint_clk ac \<in> clk_set" *)
  shows "map_u u \<turnstile>\<^sub>a conv_ac (map_acconstraint renum_clock id ac)"
  using assms by (cases ac) auto

lemma
  assumes "map_u u \<turnstile>\<^sub>a conv_ac (map_acconstraint renum_clock id ac)" "constraint_clk ac \<in> clk_set"
  shows "u \<turnstile>\<^sub>a conv_ac ac"
  using assms by (cases ac) auto

lemma clock_val_a_renum_iff:
  "map_u u \<turnstile>\<^sub>a conv_ac (map_acconstraint renum_clock id ac) = u \<turnstile>\<^sub>a conv_ac ac"
  (* if "constraint_clk ac \<in> clk_set" *)
  using that by (cases ac) auto

lemma inv_1:
  assumes
    "\<forall>x\<in>set (inv_of A l). u \<turnstile>\<^sub>a conv_ac x" "ac \<in> set (renum_cconstraint (inv_of A l))"
    (* "constraint_clk ac \<in> renum_clock ` clk_set" *)
  shows "map_u u \<turnstile>\<^sub>a conv_ac ac"
  using assms
  unfolding renum_cconstraint_def
  by (auto simp: clock_val_a_renum_iff)

lemma inv_2:
  assumes
    "\<forall>x\<in>set (renum_cconstraint (inv_of A l)). map_u u \<turnstile>\<^sub>a conv_ac x" "ac \<in> set (inv_of A l)"
    "constraint_clk ac \<in> clk_set"
  shows "u \<turnstile>\<^sub>a conv_ac ac"
  using assms unfolding renum_cconstraint_def by (auto simp: clock_val_a_renum_iff)

lemma A_unfold:
  "A = (trans_of A, inv_of A)"
  by (simp add: trans_of_def inv_of_def)

context
begin

private definition conv_A where "conv_A = Normalized_Zone_Semantics_Impl.conv_A"

lemma inv_of_unfold:
  "inv_of (conv_A B) = conv_cc o inv_of B" for B
  unfolding conv_A_def inv_of_def by (simp split: prod.split)

lemma trans_of_unfold:
  "trans_of (conv_A B) = conv_t ` trans_of B" for B
  unfolding conv_A_def trans_of_def by (simp split: prod.split)

lemma inv_of_A':
  "inv_of A' = renum_cconstraint o inv_of A o the_inv_into (Simulation_Graphs_TA.state_set A) renum_state"
  unfolding A'_def inv_of_def by simp

lemma map_u_cval_addD:
  "u' = u \<oplus> d" if "map_u u' = map_u u \<oplus> d"
  using that unfolding cval_add_def
  apply (intro ext)
  subgoal for c
    apply (drule cong[OF _ HOL.refl, where x = "renum_clock c"])
     apply auto
    done
  done

lemma map_u_cval_addD:
  "u' = u \<oplus> d" if "map_u u' = map_u u \<oplus> d" "\<forall>c. c \<notin> clk_set  \<longrightarrow> u' c = u c + d"
  using that unfolding cval_add_def
  apply (intro ext)
  subgoal for c
    apply (drule cong[OF _ HOL.refl, where x = "renum_clock c"])
    apply (cases "c \<in> clk_set")
    apply auto
    done
  oops

lemma step_t_iff[unfolded conv_A_def]:
  assumes
    "l \<in> Simulation_Graphs_TA.state_set A" "l' \<in> Simulation_Graphs_TA.state_set A"
  shows
  "conv_A A' \<turnstile> \<langle>renum_state l, map_u u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>renum_state l', map_u u'\<rangle> \<longleftrightarrow>
   conv_A A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l', u'\<rangle>"
  using assms
  apply -
  apply standard
  subgoal
apply (cases rule: step_t.cases)
     apply assumption
    apply (auto simp: inv_of_unfold inv_of_A' split: prod.split_asm dest!: renum_state_eqD map_u_cval_addD)
    apply rule
     apply (auto simp: clock_val_def list_all_iff renum_state_inj inv_of_unfold inv_of_A' dest!: map_u_cval_addD renum_state_eqD)
    apply (rule inv_2[rotated], assumption)
    subgoal
      sorry
    apply (simp add: map_u_add)
    done
  subgoal
    apply (cases rule: step_t.cases)
     apply assumption
    apply (auto simp: inv_of_unfold map_u_add split: prod.split_asm)
    apply rule
    apply (auto simp: clock_val_def list_all_iff renum_state_inj inv_of_unfold inv_of_A')
    apply (drule (1) inv_1)
    by (simp add: map_u_add)
  done

end (* Anonymous context for private definitions *)

end (* TA Renum *)
*)

locale TA_Renum =
  fixes A :: "('a, 'c, int, 's) ta"
    and renum_act   :: "'a \<Rightarrow> 'a1"
    and renum_clock :: "'c \<Rightarrow> 'c1"
    and renum_state :: "'s \<Rightarrow> 's1"
  assumes renum_state_inj: "inj renum_state"
      and renum_clock_inj: "inj renum_clock"
begin

definition
  "renum_cconstraint = map (map_acconstraint renum_clock id)"

definition A' :: "('a1, 'c1, int, 's1) ta" where
   "A' \<equiv> (
    (\<lambda>(l, g, a, r, l').
      (renum_state l, renum_cconstraint g, renum_act a, map renum_clock r, renum_state l'))
    ` trans_of A,
    renum_cconstraint o inv_of A o the_inv renum_state
  )"

definition
  "map_u u = u o the_inv renum_clock"

lemma map_u_add:
  "map_u (u \<oplus> d) = map_u u \<oplus> d"
  by (auto simp: map_u_def cval_add_def)

lemma renum_state_inv[simp]:
  "the_inv renum_state (renum_state l) = l"
  by (intro the_inv_f_f renum_state_inj)

lemma renum_state_eqD:
  assumes "renum_state l = renum_state l'"
  shows "l = l'"
  using assms renum_state_inj by (meson inj_D)

definition clk_set where "clk_set \<equiv> Timed_Automata.clk_set A"

lemma map_u_renum_clock[simp]:
  "map_u u (renum_clock c) = u c" (* if "c \<in> clk_set" *)
  using that unfolding map_u_def by (simp add: the_inv_into_f_f renum_clock_inj clk_set_def)

lemma
  assumes "u \<turnstile>\<^sub>a conv_ac ac" (* "constraint_clk ac \<in> clk_set" *)
  shows "map_u u \<turnstile>\<^sub>a conv_ac (map_acconstraint renum_clock id ac)"
  using assms by (cases ac) auto

lemma
  assumes "map_u u \<turnstile>\<^sub>a conv_ac (map_acconstraint renum_clock id ac)" "constraint_clk ac \<in> clk_set"
  shows "u \<turnstile>\<^sub>a conv_ac ac"
  using assms by (cases ac) auto

lemma clock_val_a_renum_iff:
  "map_u u \<turnstile>\<^sub>a conv_ac (map_acconstraint renum_clock id ac) = u \<turnstile>\<^sub>a conv_ac ac"
  (* if "constraint_clk ac \<in> clk_set" *)
  using that by (cases ac) auto

lemma inv_1:
  assumes
    "\<forall>x\<in>set (inv_of A l). u \<turnstile>\<^sub>a conv_ac x" "ac \<in> set (renum_cconstraint (inv_of A l))"
    (* "constraint_clk ac \<in> renum_clock ` clk_set" *)
  shows "map_u u \<turnstile>\<^sub>a conv_ac ac"
  using assms
  unfolding renum_cconstraint_def
  by (auto simp: clock_val_a_renum_iff)

lemma inv_2:
  assumes
    "\<forall>x\<in>set (renum_cconstraint (inv_of A l)). map_u u \<turnstile>\<^sub>a conv_ac x" "ac \<in> set (inv_of A l)"
    "constraint_clk ac \<in> clk_set"
  shows "u \<turnstile>\<^sub>a conv_ac ac"
  using assms unfolding renum_cconstraint_def by (auto simp: clock_val_a_renum_iff)

lemma A_unfold:
  "A = (trans_of A, inv_of A)"
  by (simp add: trans_of_def inv_of_def)

context
begin

private definition conv_A where "conv_A = Normalized_Zone_Semantics_Impl.conv_A"

lemma inv_of_unfold:
  "inv_of (conv_A B) = conv_cc o inv_of B" for B
  unfolding conv_A_def inv_of_def by (simp split: prod.split)

lemma trans_of_unfold:
  "trans_of (conv_A B) = conv_t ` trans_of B" for B
  unfolding conv_A_def trans_of_def by (simp split: prod.split)

lemma inv_of_A':
  "inv_of A' = renum_cconstraint o inv_of A o the_inv renum_state"
  unfolding A'_def inv_of_def by simp

lemma map_u_cval_addD:
  "u' = u \<oplus> d" if "map_u u' = map_u u \<oplus> d"
  using that unfolding cval_add_def
  apply (intro ext)
  subgoal for c
    apply (drule cong[OF _ HOL.refl, where x = "renum_clock c"])
     apply auto
    done
  done

lemma map_u_cval_addD:
  "u' = u \<oplus> d" if "map_u u' = map_u u \<oplus> d" "\<forall>c. c \<notin> clk_set  \<longrightarrow> u' c = u c + d"
  using that unfolding cval_add_def
  apply (intro ext)
  subgoal for c
    apply (drule cong[OF _ HOL.refl, where x = "renum_clock c"])
    apply (cases "c \<in> clk_set")
    apply auto
    done
  oops

lemma step_t_iff[unfolded conv_A_def]:
  assumes
    "l \<in> Simulation_Graphs_TA.state_set A" "l' \<in> Simulation_Graphs_TA.state_set A"
  shows
  "conv_A A' \<turnstile> \<langle>renum_state l, map_u u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>renum_state l', map_u u'\<rangle> \<longleftrightarrow>
   conv_A A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l', u'\<rangle>"
  using assms
  apply -
  apply standard
  subgoal
apply (cases rule: step_t.cases)
     apply assumption
    apply (auto simp: inv_of_unfold inv_of_A' split: prod.split_asm dest!: renum_state_eqD map_u_cval_addD)
    apply rule
     apply (auto simp: clock_val_def list_all_iff renum_state_inj inv_of_unfold inv_of_A' dest!: map_u_cval_addD renum_state_eqD)
    apply (rule inv_2[rotated], assumption)
    subgoal
      sorry
    apply (simp add: map_u_add)
    done
  subgoal
    apply (cases rule: step_t.cases)
     apply assumption
    apply (auto simp: inv_of_unfold map_u_add split: prod.split_asm)
    apply rule
    apply (auto simp: clock_val_def list_all_iff renum_state_inj inv_of_unfold inv_of_A')
    apply (drule (1) inv_1)
    by (simp add: map_u_add)
  done

end (* Anonymous context for private definitions *)

end (* TA Renum *)

no_notation
  comp2  (infixl "\<circ>\<circ>" 55) and
  comp3  (infixl "\<circ>\<circ>\<circ>" 55)

locale Simple_Network_Rename =
  Simple_Network_Impl automata for automata ::
    "('s list \<times> (('a :: countable) act, 's, 'c, int, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, int) cconstraint) list) list"
begin

context
  fixes renum_acts   :: "'a \<Rightarrow> nat"
    and renum_vars   :: "'x \<Rightarrow> nat"
    and renum_clocks :: "'c \<Rightarrow> nat"
    and renum_states :: "nat \<Rightarrow> 's \<Rightarrow> nat"
  assumes renum_states_inj:
    "\<forall>i<n_ps. \<forall>x\<in>loc_set. \<forall>y\<in>loc_set. renum_states i x = renum_states i y \<longrightarrow> x = y"
  and renum_clocks_inj:
    "inj_on renum_clocks clk_set'"
  and "inj_on renum_vars var_set"
begin

definition
  "map_cconstraint f g xs = map (map_acconstraint f g) xs"

definition
  "extend_inj (f :: ('xx :: countable) \<Rightarrow> nat) S \<equiv> let m = Max ({0} \<union> f ` S) + 1 in
    (\<lambda> x. if x \<in> S then f x else m + (SOME f. inj f) x)"

lemma extend_inj_inj:
  "inj (extend_inj f S)" if "inj_on f S" "finite S" for f :: "'b :: countable \<Rightarrow> nat"
proof -
  obtain g :: "'b \<Rightarrow> nat" where "inj g"
    by auto
  have *: "f x \<le> Max (insert 0 (f ` S))" if "x \<in> S" for x
    using that \<open>finite S\<close> by auto
  from that show ?thesis
    apply (intro injI)
    unfolding extend_inj_def
    apply (auto split: if_split_asm dest: inj_onD *)
    subgoal for x y
      by (metis from_nat_to_nat to_nat_def)
    done
qed

definition
  "renum_cconstraint = map_cconstraint (extend_inj renum_clocks clk_set') id"

definition
  "renum_act = map_act renum_acts"

definition
  "renum_exp = map_exp (extend_inj renum_vars var_set) id"

definition
  "renum_upd = map (\<lambda>(x, upd). (extend_inj renum_vars var_set x, renum_exp upd))"

definition
  "renum_reset = map (extend_inj renum_clocks clk_set')"

definition renum_automaton where
  "renum_automaton i \<equiv> \<lambda>(commited, trans, inv). let
    commited' = map (renum_states i) commited;
    trans' = map (\<lambda>(l, g, a, upd, r, l').
      (renum_states i l, renum_cconstraint g, renum_act a, renum_upd upd, renum_reset r, 
      renum_states i l')
    ) trans;
    inv' = map (\<lambda>(l, g). (renum_states i l, renum_cconstraint g)) inv
  in (commited', trans', inv')
"

interpretation renum: Simple_Network_Impl
  "map_index renum_automaton automata"
  "map renum_acts broadcast"
  "map (\<lambda>(a,b,c). (renum_vars a, b, c)) bounds'"
  "formula" .

definition
  "vars_inv \<equiv> the_inv (extend_inj renum_vars var_set)"

definition
  "map_st \<equiv> \<lambda>(L, s). (map_index ((\<lambda> r. extend_inj r loc_set) o renum_states) L, s o vars_inv)"

definition
  "clocks_inv \<equiv> the_inv (extend_inj renum_clocks clk_set')"

definition
  "map_u u = u o clocks_inv"

lemma map_u_add[simp]:
  "map_u (u \<oplus> d) = map_u u \<oplus> d"
  by (auto simp: map_u_def cval_add_def)

definition renum_label where
  "renum_label = map_label renum_acts"

lemma
  "inj (map_index renum_states)"
  apply (rule injI)
  oops

lemma states_loc_setD:
  "set L \<subseteq> loc_set" if "L \<in> states"
  using states_loc_set that by auto

lemma renum_states_inj_states:
  assumes "map_index renum_states L = map_index renum_states L'" "L \<in> states" "L' \<in> states"
  shows "L = L'"
  using assms
  apply -
  apply (rule map_index_inj[where S = loc_set and T = loc_set])
  subgoal
    apply (simp add: L_len)
    done
     apply assumption
  apply (erule states_loc_setD)
   apply (erule states_loc_setD)
  apply (simp add: L_len renum_states_inj)
  done

lemma renum_vars_inj:
  assumes
  "(s \<circ> vars_inv) = (s' \<circ> vars_inv)"
shows
  "s = s'"
  apply (rule ext)
  subgoal for x
    using assms apply -
    thm cong[OF _ HOL.refl, where x = x]
    apply (drule cong[OF _ HOL.refl, where x = "renum_vars x"])
    apply (simp add: vars_inv_def)
    sorry
  sorry

interpretation ta_renum: TA_Renum
  prod_ta
  renum_label
  "extend_inj renum_clocks clk_set'"
  map_st
  apply standard
  subgoal
    unfolding map_st_def
    apply (rule inj_onI)
    apply clarsimp
    apply (rule conjI)
    subgoal for L s L' s'
      apply (erule renum_states_inj_states)
      subgoal
        sorry
        sorry
      subgoal for L s L' s'
        by (rule renum_vars_inj)
      done
  sorry

no_notation
  comp2  (infixl "\<circ>\<circ>" 55) and
  comp3  (infixl "\<circ>\<circ>\<circ>" 55)

lemma inv_map_stD:
  assumes "the_inv map_st (L, s) = (L', s')"
  shows "map_index ((\<lambda> r. extend_inj r loc_set) o renum_states) L'  = L"
  sorry

lemma ta_renum_A'_eq:
  "ta_renum.A' = renum.prod_ta"
  unfolding ta_renum.A'_def renum.prod_ta_def
  apply rule
  apply rule
  subgoal
    unfolding renum.trans_prod_def
    sorry
  subgoal
    unfolding prod_ta_def
    print_antiquotations
    thm prod_inv_def
    unfolding renum.prod_inv_def prod_inv_def
    apply (rule ext)
    subgoal for x
      apply (cases x)
      subgoal for L s
unfolding case_prod_conv inv_of_def
  apply (simp only: )
  unfolding case_prod_conv inv_of_def fst_conv snd_conv
  unfolding comp_def
  apply (cases "the_inv map_st (L, s)")
  apply (simp only: case_prod_conv)
  unfolding ta_renum.renum_cconstraint_def
  unfolding map_concat map_map
  apply (fo_rule arg_cong)
  apply (rule map_cong)
  subgoal
    sorry
  unfolding comp_def
  unfolding renum.N_def N_def fst_conv snd_conv
  apply (drule inv_map_stD)
  unfolding map_st_def
  unfolding case_prod_conv
  apply (simp only: case_prod_conv)
apply (simp only: )


  oops
  sorry

lemma ta_renum_map_u_eq:
  "ta_renum.map_u = map_u"
  unfolding ta_renum.map_u_def map_u_def clocks_inv_def ..

lemma
  "Normalized_Zone_Semantics_Impl.conv_A prod_ta \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l', u'\<rangle>
\<longleftrightarrow> Normalized_Zone_Semantics_Impl.conv_A renum.prod_ta \<turnstile> \<langle>map_st l, map_u u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>map_st l', map_u u'\<rangle>"
  apply (subst ta_renum.step_t_iff[symmetric])

  apply (subst ta_renum_A'_eq)
  apply (simp add: ta_renum_A'_eq ta_renum_map_u_eq)
  done
  thm ta_renum.step_t_iff
  oops
proof -
  define A  where "A  \<equiv> Normalized_Zone_Semantics_Impl.conv_A prod_ta"
  define A' where "A' \<equiv> Normalized_Zone_Semantics_Impl.conv_A renum.prod_ta"
  show ?thesis
    unfolding A_def[symmetric] A'_def[symmetric]
  apply standard
   apply (erule step_t.cases)
  apply simp
  apply (rule step_t.intros)

term prod_ta

lemma
  "Bisimulation_Invariant

"



interpretation nat: Simple_Network_Impl_nat
  "map renum_acts broadcast"
  "map (\<lambda>(a,b,c). (renum_vars a, b, c)) bounds'"
  "formula"
  "map_index renum_automaton automata"
  m
  num_states
  num_actions
  apply standard


end


context Simple_Network_Impl
begin

context
  fixes renum_acts   :: "'a \<Rightarrow> nat"
    and renum_vars   :: "'x \<Rightarrow> nat"
    and renum_clocks :: "'c \<Rightarrow> nat"
    and renum_states :: "nat \<Rightarrow> 's \<Rightarrow> nat"
  assumes renum_states_inj:
    "\<forall>i<n_ps. \<forall>x\<in>loc_set. \<forall>y\<in>loc_set. renum_states i x = renum_states i y \<longrightarrow> x = y"
and "\<forall>v \<in>"
begin

definition
  "map_cconstraint f g xs = map (map_acconstraint f g) xs"

definition
  "renum_cconstraint = map_cconstraint renum_clocks id"

definition
  "renum_act = map_act renum_acts"

definition
  "renum_exp = map_exp renum_vars id"

definition
  "renum_upd = map (\<lambda>(x, upd). (renum_vars x, renum_exp upd))"

definition
  "renum_reset = map renum_clocks"

definition renum_automaton where
  "renum_automaton i \<equiv> \<lambda>(commited, trans, inv). let
    commited' = map (renum_states i) commited;
    trans' = map (\<lambda>(l, g, a, upd, r, l').
      (renum_states i l, renum_cconstraint g, renum_act a, renum_upd upd, renum_reset r, 
      renum_states i l')
    ) trans;
    inv' = map (\<lambda>(l, g). (renum_states i l, renum_cconstraint g)) inv
  in (commited', trans', inv')
"

interpretation renum: Simple_Network_Impl
  "map_index renum_automaton automata"
  "map renum_acts broadcast"
  "map (\<lambda>(a,b,c). (renum_vars a, b, c)) bounds'"
  "formula" .

definition
  "vars_inv \<equiv> the_inv renum_vars"

definition
  "map_st \<equiv> \<lambda>(L, s). (map_index renum_states L, s o vars_inv)"

definition
  "clocks_inv \<equiv> the_inv renum_clocks"

definition
  "map_u u = u o clocks_inv"

lemma map_u_add[simp]:
  "map_u (u \<oplus> d) = map_u u \<oplus> d"
  by (auto simp: map_u_def cval_add_def)

definition renum_label where
  "renum_label = map_label renum_acts"

lemma
  "inj (map_index renum_states)"
  apply (rule injI)
  oops

lemma states_loc_setD:
  "set L \<subseteq> loc_set" if "L \<in> states"
  using states_loc_set that by auto

lemma renum_states_inj_states:
  assumes "map_index renum_states L = map_index renum_states L'" "L \<in> states" "L' \<in> states"
  shows "L = L'"
  using assms
  apply -
  apply (rule map_index_inj[where S = loc_set and T = loc_set])
  subgoal
    apply (simp add: L_len)
    done
     apply assumption
  apply (erule states_loc_setD)
   apply (erule states_loc_setD)
  apply (simp add: L_len renum_states_inj)
  done

lemma renum_vars_inj:
  assumes
  "(s \<circ>\<circ> Simple_Network_Impl.vars_inv) renum_vars = (s' \<circ>\<circ> Simple_Network_Impl.vars_inv) renum_vars"
shows
  "s = s'"
  apply (rule ext)
  subgoal for x
    using assms apply -
    thm cong[OF _ HOL.refl, where x = x]
    apply (drule cong[OF _ HOL.refl, where x = "renum_vars x"])
    apply (simp add: vars_inv_def)
    sorry
  sorry

interpretation ta_renum: TA_Renum
  prod_ta
renum_label
renum_clocks
map_st
  apply standard
  subgoal
    unfolding map_st_def
    apply (rule inj_onI)
    apply clarsimp
    apply (rule conjI)
    subgoal for L s L' s'
      apply (erule renum_states_inj_states)
      subgoal
        sorry
        sorry
      subgoal for L s L' s'

    sorry
  sorry

lemma ta_renum_A'_eq:
  "ta_renum.A' = renum.prod_ta"
  sorry

lemma ta_renum_map_u_eq:
  "ta_renum.map_u = map_u"
  unfolding ta_renum.map_u_def map_u_def clocks_inv_def ..

lemma
  "Normalized_Zone_Semantics_Impl.conv_A prod_ta \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l', u'\<rangle>
\<longleftrightarrow> Normalized_Zone_Semantics_Impl.conv_A renum.prod_ta \<turnstile> \<langle>map_st l, map_u u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>map_st l', map_u u'\<rangle>"
  apply (subst ta_renum.step_t_iff[symmetric])
  apply (subst ta_renum_A'_eq)
  apply (simp add: ta_renum_A'_eq ta_renum_map_u_eq)
  done
  thm ta_renum.step_t_iff
  oops
proof -
  define A  where "A  \<equiv> Normalized_Zone_Semantics_Impl.conv_A prod_ta"
  define A' where "A' \<equiv> Normalized_Zone_Semantics_Impl.conv_A renum.prod_ta"
  show ?thesis
    unfolding A_def[symmetric] A'_def[symmetric]
  apply standard
   apply (erule step_t.cases)
  apply simp
  apply (rule step_t.intros)

term prod_ta

lemma
  "Bisimulation_Invariant

"



interpretation nat: Simple_Network_Impl_nat
  "map renum_acts broadcast"
  "map (\<lambda>(a,b,c). (renum_vars a, b, c)) bounds'"
  "formula"
  "map_index renum_automaton automata"
  m
  num_states
  num_actions
  apply standard


end

end

end (* Theory *)
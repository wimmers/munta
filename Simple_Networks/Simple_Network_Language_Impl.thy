theory Simple_Network_Language_Impl
  imports
    Simple_Network_Language
    TA_Impl.Normalized_Zone_Semantics_Impl_Refine
    "HOL-Library.IArray" "HOL-Library.AList"
    "../library/More_Methods"
    "../library/Bijective_Embedding"
    TA_Impl_Misc2
    TA_More2
    TA_Equivalences
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

lemma map_index_inj1:
  "L = L'"
  if "map_index f L = map_index g L'"
     "\<forall> i < length L. f i (L ! i) = g i (L' ! i) \<longrightarrow> L ! i = L' ! i"
proof (intros add: nth_equalityI)
  from that(1) show \<open>length L = length L'\<close>
    by (rule map_index_eq_imp_length_eq)
  fix i :: \<open>nat\<close>
  assume \<open>i < length L\<close>
  with that have "map_index f L ! i = map_index g L' ! i"
    by auto
  with \<open>i < length L\<close> \<open>length L = length L'\<close> have "f i (L ! i) = g i (L' ! i)"
    by simp
  with \<open>i < length L\<close> that(2) show \<open>L ! i = L' ! i\<close>
    by simp
qed

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
      (\<forall>p. p\<notin>set ps \<longrightarrow> gs p = []) \<and> (\<forall>p. p\<notin>set ps \<longrightarrow> fs p = []) \<and> (\<forall>p. p\<notin>set ps \<longrightarrow> rs p = [])
    }"
  unfolding trans_broad_def
proof ((intro Collect_eqI iffI; elims add: more_elims), goal_cases)
  case prems: (1 x L s L' s' s'' a p l g f r l' gs fs rs ls' ps)
  let ?f = "\<lambda>gs p. if p \<in> set ps then gs p else []"
  let ?gs = "?f gs" let ?fs = "?f fs" let ?rs = "?f rs"
  have [simp]: "map gs ps = map ?gs ps" "map rs ps = map ?rs ps" "map fs ps = map ?fs ps"
    by (simp cong: map_cong)+
  with prems show ?case
    by (inst_existentials L s L' s' s'' a p l g f r l' ?gs ?fs ?rs ls' ps; (assumption | simp))
next
  case (2 x L s L' s' s'' a p l g f r l' gs fs rs ls' ps)
  then show ?case
    by blast
qed

(* XXX Move to distribution *)
text \<open>Stronger version of @{thm Map.map_of_mapk_SomeI}\<close>
theorem map_of_mapk_SomeI':
  assumes "inj_on f (fst ` set t)"
    and "map_of t k = Some x"
  shows "map_of (map (\<lambda>(k, y). (f k, g y)) t) (f k) = Some (g x)"
  using assms
  apply (induction t)
   apply (auto split: if_split_asm)
  apply (metis DiffI imageI img_fst map_of_SomeD singletonD)
  done

theorem map_of_mapk_SomeI:
  assumes "inj f"
    and "map_of t k = Some x"
  shows "map_of (map (\<lambda>(k, y). (f k, g y)) t) (f k) = Some (g x)"
  using assms by - (rule map_of_mapk_SomeI', erule inj_on_subset, auto)

locale Simple_Network_Impl =
  fixes automata ::
    "('s list \<times> ('a act, 's, 'c, int, 'x, int) transition list
      \<times> ('s \<times> ('c, int) cconstraint) list) list"
    and broadcast :: "'a list"
    and bounds' :: "('x \<times> (int \<times> int)) list"
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

lemma L_len[intro, dest]:
  "length L = n_ps" if "L \<in> states"
  using that unfolding states_def by simp

end

paragraph \<open>Mapping through the product construction\<close>

lemma f_the_inv_f:
  "f (the_inv f x) = x" if "inj f" "x \<in> range f"
  using that by (auto simp: the_inv_f_f)

context Simple_Network_Impl
begin

lemma N_eq:
  \<open>N i = automaton_of (automata ! i)\<close> if \<open>i < n_ps\<close>
  using that unfolding N_def n_ps_def fst_conv snd_conv by (intro nth_map; simp)

(* XXX Remove? *)
lemma covn_N_eq:
  \<open>N i = automaton_of (automata ! i)\<close> if \<open>i < n_ps\<close>
  using that unfolding N_def n_ps_def fst_conv snd_conv by (intro nth_map; simp)

end

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
     (\<lambda> l. if l \<in> map_loc i ` fst ` set (snd (snd (automata ! i)))
           then map_cc (inv (the_inv (map_loc i) l))
           else [])
    )"

sublocale map: Prod_TA_Defs
  "(map_action ` set broadcast,
    map_index (\<lambda> i a. automaton_of (map_automaton i a)) automata,
    map_of (map (\<lambda>(x, p). (map_var x, p)) bounds'))"
  .

definition
  "map_st \<equiv> \<lambda>(L, s).
    (map_index map_loc L, \<lambda> x. if x \<in> map_var ` dom s then s (the_inv map_var x) else None)"

(*
definition
  "map_st \<equiv> \<lambda>(L, s).
    (if (\<forall>i < n_ps. L ! i \<in> map_loc i ` fst ` set (snd (snd (automata ! i))))
     then map_index (\<lambda> i. the_inv (map_loc i)) L else [],
     \<lambda>x. if x \<in> map_var ` dom s then s (the_inv map_var x) else None)"
*)

definition "map_t \<equiv> \<lambda> (l,g,a,r,l').
  (map_st l,map_cc g,map_label map_action a,map map_clock r,map_st l')"

(* abbreviation "map_A \<equiv> \<lambda> (T, I). (map_t ` T, map_cc o I o the_inv map_st)" *)

abbreviation map_A :: "(('s list \<times> ('x \<Rightarrow> 'b option)) \<times>
    ('c, int) acconstraint list \<times>
    'a Simple_Network_Language.label \<times>
    'c list \<times> 's list \<times> ('x \<Rightarrow> 'd option)) set \<times>
   ('s list \<times> ('x \<Rightarrow> 'e option) \<Rightarrow> ('c, int) acconstraint list)
   \<Rightarrow> (('s1 list \<times> ('x1 \<Rightarrow> 'b option)) \<times>
       ('c1, real) acconstraint list \<times>
       'a1 Simple_Network_Language.label \<times>
       'c1 list \<times> 's1 list \<times> ('x1 \<Rightarrow> 'd option)) set \<times>
      ('s1 list \<times> ('x1 \<Rightarrow> 'e option)
       \<Rightarrow> ('c1, real) acconstraint list)"
  where
"map_A \<equiv> \<lambda> (T, I).
  (map_t ` T,
   \<lambda>(L, s).
    if (\<forall>i < n_ps. L ! i \<in> map_loc i ` fst ` set (snd (snd (automata ! i))))
    then map_cc (I (map_index (\<lambda> i. the_inv (map_loc i)) L, \<lambda>_. None))
    else []
  )"

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
  "is_upds
    (\<lambda>x. if x \<in> map_var ` dom s' then s' (the_inv map_var x) else None)
    (map (\<lambda>a. map_expr (fs a)) ps)
    (\<lambda>x. if x \<in> map_var ` dom s'' then s'' (the_inv map_var x) else None)"
  using assms
  by (induction ps arbitrary: s')
     (auto 4 4 intro: is_upds.intros dest: is_upd_mapI elim: is_upds.cases)

lemma map_trans_broad_aux1:
  "map_index map_loc (fold (\<lambda>p L. L[p := ls' p]) ps L) =
  fold (\<lambda>p L. L[p := map_loc p (ls' p)]) ps (map_index map_loc L)"
  by (induction ps arbitrary: L) (auto simp: map_index_update)

lemma InD2:
  assumes "In (map_action a) = map_act map_action a'"
  shows "a' = In a"
  using assms by (cases a')  (auto simp: injD[OF map_action_inj])

lemma OutD2:
  assumes "Out (map_action a) = map_act map_action a'"
  shows "a' = Out a"
  using assms by (cases a') (auto simp: injD[OF map_action_inj])

inductive_cases is_upds_elims:
  "is_upds s [] s'"
  "is_upds s (x # xs) s'"

lemma is_upds_mapD:
  assumes "is_upds s (map map_expr cc) s'"
  shows "is_upds (s o map_var) cc (s' o map_var)"
  using assms
  by (induction cc arbitrary: s) (auto 4 3 intro: is_upd_mapD is_upds.intros elim: is_upds_elims)

lemma map_trans_broad_aux2:
  "dom (\<lambda>a. s (map_var a)) = dom bounds" if "dom s = map_var ` dom bounds"
  unfolding dom_def using that by (auto 4 4 dest: injD[OF map_var_inj] simp: dom_def)

lemma map_trans_broad_aux3:
  "fold (\<lambda>p L. L[p := ls' p]) ps (map_index map_loc x)[p := map_loc p l1'] =
    map_index map_loc (fold (\<lambda>p L. L[p := the_inv (map_loc p) (ls' p)]) ps x[p := l1'])"
  if "\<forall>p \<in> set ps. ls' p \<in> range (map_loc p)"
  using that
  apply -
  apply (rule sym)
  apply (induction ps arbitrary: x)
  using map_loc_inj by (auto simp: f_the_inv_f map_index_update)

lemma map_cc_inj':
  "inj map_cc"
  unfolding map_cc_def by (intro inj_mapI acconstraint.inj_map; fact)

lemma map_expr_inj:
  "inj map_expr"
  unfolding map_expr_def using map_var_inj exp.inj_map[of map_var id]
  by (auto 4 3 dest: injD intro: injI elim: map_injective)

lemma map_trans_broad:
  "map.trans_broad = map_t ` trans_broad"
  unfolding map.trans_broad_alt_def trans_broad_alt_def
  apply standard
   supply [simp] = L_len
  subgoal
    subgoal
    proof -
      have **:
        "\<exists> gs' fs' rs' ls1. gs = map_cc o gs' \<and> ls1 = (\<lambda> p. the_inv (map_loc p) (ls' p)) \<and>
          fs = map_expr o fs' \<and> rs = map map_clock o rs' \<and>
          (\<forall>p\<in>set ps. ls' p \<in> range (map_loc p)) \<and>
          (\<forall>p\<in>set ps.(L ! p, gs' p, In a, fs' p, rs' p, ls1 p) \<in> trans (N p))"
        if
          assms: "\<forall>p\<in>set ps.
          (map_index map_loc L ! p, gs p, In (map_action a), fs p, rs p, ls' p)
          \<in> Simple_Network_Language.trans (map.N p)"
          "set ps \<subseteq> {0..<n_ps}" "\<forall>p. p \<notin> set ps \<longrightarrow> gs p = []" "\<forall>p. p \<notin> set ps \<longrightarrow> fs p = []"
          "\<forall>p. p \<notin> set ps \<longrightarrow> rs p = []" "length L = n_ps"
        for L ps gs a fs rs ls'
      proof -
        let ?gs' = "the_inv map_cc o gs"
        let ?fs' = "Hilbert_Choice.inv map_expr o fs"
        let ?ls1 = "\<lambda> p. the_inv (map_loc p) (ls' p)"
        let ?rs' = "Hilbert_Choice.inv (map map_clock) o rs"
        have gs: "gs p = map_cc (the_inv map_cc (gs p))" if "p \<in> set ps" for p
          using that assms by (subst f_the_inv_f[OF map_cc_inj']; force dest: 73)
        have fs: "fs p = map_expr (?fs' p)" if "p \<in> set ps" for p
          using that assms by (force dest: 73 simp: f_inv_into_f[where f = map_expr])
        have rs: "rs p = map map_clock (?rs' p)" if "p \<in> set ps" for p
          using that assms by (force dest!: 73 simp: f_inv_into_f[where f = "map map_clock"])
        show ?thesis
          apply (inst_existentials ?gs' ?fs' ?rs' ?ls1)
          subgoal
            using assms
            apply (intro ext)
            subgoal for p
              apply (cases "p \<in> set ps")
               apply (subst gs; force)
              unfolding comp_def
              apply (subst f_the_inv_f[OF map_cc_inj']; simp add: map_cc_def)
              done
            done
             apply solve_triv
          subgoal
            using assms
            apply (intro ext)
            subgoal for p
              apply (cases "p \<in> set ps")
               apply (subst fs; force)
              unfolding comp_def
              apply (subst f_inv_into_f[where f = map_expr]; simp add: map_expr_def)
              done
            done
          subgoal
            using assms
            apply (intro ext)
            subgoal for p
              apply (cases "p \<in> set ps")
               apply (subst rs; force)
              unfolding comp_def
              apply (subst f_inv_into_f[where f = "map map_clock"]; simp add: map_expr_def)
              done
            done
          subgoal
            using assms(1,2) by (auto dest!: 73 bspec)
          using assms
          apply intros
          apply (drule (1) bspec)
          apply (drule 73)
           apply force
          using map_loc_inj map_cc_inj' map_expr_inj
          apply (auto simp: the_inv_f_f inv_f_f[OF map_expr_inj])
          apply (subst inv_f_f)
          using map_clock_inj
           apply (auto dest: map_loc_injD[THEN sym])
          apply (subst (asm) nth_map_index)
           apply (auto dest: map_loc_injD InD2)
          done
      qed
      have *: "set ps \<subseteq> {0..<n_ps} \<longleftrightarrow> (\<forall>p \<in> set ps. p < n_ps)" for ps
        by auto
      show ?thesis
        apply (rule subsetI)
        apply (clarsimp simp add: 3 9 10 broadcast_def split: prod.split_asm)
        apply (drule (4) **, simp)
        apply (drule (1) 73)+
        apply elims
        apply (frule OutD2)
        apply (drule map_loc_injD[THEN sym])
        apply (frule bounded_mapD, drule bounded_map_domD)
        apply (frule bounded_mapD, drule bounded_map_domD)
        apply simp
        apply (drule is_upd_mapD)
        using [[goals_limit = 1]]
        apply (intro image_eqI[rotated] CollectI exI conjI)
                            apply solve_triv+
        subgoal premises prems for s s' s'' p g f r l' gs fs rs ls' ps x L gs' l1 fs' g' rs' a' ls1 u' r' l1'
          \<comment>\<open>Commited\<close>
          using prems(2) \<open>p < n_ps\<close> \<open>set ps \<subseteq> _\<close> \<open>L \<in> states\<close> by (force dest: map_loc_injD simp: 9)
                       apply intros
        subgoal premises prems for s s' s'' p g f r l' gs fs rs ls' ps x L gs' l1 fs' g' rs' a' ls1 u' r' l1' q g''
          \<comment>\<open>Maximal set\<close>
          using prems(3) \<open>q < n_ps\<close> \<open>q \<notin> set ps \<and> p \<noteq> q\<close> \<open>L \<in> states\<close>
          by (fastforce dest!: 71 map_loc_injD InD2 simp: map_t_single_def)
                      apply solve_triv+
               apply (rule is_upds_mapD, simp add: map_map)
              apply solve_triv+
           apply (simp add: map_cc_def; fail)
          apply (simp add: map_expr_def; fail)
         apply (simp; fail)
        unfolding map_t_def
        apply clarsimp
        apply intros
        subgoal
          unfolding map_st_def
          apply clarsimp
          thm the_inv_f_f[OF map_var_inj] map_index_update[symmetric] 
          apply (rule ext)
          thm f_the_inv_f
          apply (clarsimp split: if_split)
          apply safe
               apply (simp add: the_inv_f_f[OF map_var_inj]; fail)
              apply (simp add: map_trans_broad_aux2, blast)
             apply (simp add: the_inv_f_f[OF map_var_inj]; fail)
            apply (simp add: map_trans_broad_aux2, blast)
           apply (simp add: the_inv_f_f[OF map_var_inj]; fail)
          apply (simp add: map_trans_broad_aux2, blast)
          done

          apply (simp add: map_cc_concat map_cc_append; fail)
         apply (simp add: map_map map_concat; fail)
        subgoal for s s' s'' p ls'
          unfolding map_st_def
          apply clarsimp
          apply safe
          subgoal
            by (rule map_trans_broad_aux3)
              apply (rule ext)
              apply (clarsimp split: if_split)
              apply safe
               apply (simp add: the_inv_f_f[OF map_var_inj]; fail)
              apply (simp add: map_trans_broad_aux2, blast)
             apply (rule map_trans_broad_aux3; assumption)
            apply (rule ext)
            apply (clarsimp split: if_split)
            apply safe
             apply (simp add: the_inv_f_f[OF map_var_inj]; fail)
            apply (simp add: map_trans_broad_aux2, blast)
           apply (rule map_trans_broad_aux3; assumption)
          apply (rule ext)
          apply (clarsimp split: if_split)
          apply safe
           apply (simp add: the_inv_f_f[OF map_var_inj]; fail)
          apply (simp add: map_trans_broad_aux2, blast)
          done
        done
    qed
    done
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
      apply (simp add: map_cc_def map_expr_def)+
    done
  done

lemma map_trans_prod:
  "map.trans_prod = map_t ` trans_prod"
  unfolding map.prod_ta_def prod_ta_def
  unfolding map.trans_prod_def trans_prod_def
  unfolding map.prod_inv_def prod_inv_def
  unfolding image_Un
  by ((fo_rule arg_cong2)+; rule map_trans_int map_trans_bin map_trans_broad)

lemma state_set_states:
  "state_set (trans_of prod_ta) \<subseteq> {(l, s). l \<in> states}"
  using state_set_states unfolding state_set_def Simulation_Graphs_TA.state_set_def trans_of_def .

lemma state_set_states':
  "state_set map.trans_prod \<subseteq> {map_st (l, s) | l s. l \<in> states}"
  using state_set_states
  unfolding map_trans_prod
  unfolding prod_ta_def state_set_def
  unfolding trans_of_def trans_prod_def
  unfolding map_t_def
  by fastforce

definition map_I where
  "map_I I \<equiv> map_cc o I o the_inv map_st"

(*

definition map_I2 where
  "map_I2 I \<equiv> \<lambda> (L, s). if L \<in> map.states then map_cc (I (the_inv map_st (L, s))) else []"
*)

lemma
  "map.prod_ta = map_A prod_ta"
  oops

context
  assumes trans_inv_closed':
  "\<forall>i<n_ps.
          (\<Union>(l, g, a, r, u,
                 l')\<in>Simple_Network_Language.trans (N i).
                 {l, l'})
  \<subseteq> fst ` set (snd (snd (automata ! i)))
  "
begin

lemma map_locD:
  assumes "p < n_ps" "L \<in> states"
  shows   "L ! p \<in> fst ` set (snd (snd (automata ! p)))"
proof -
  from assms have "L ! p \<in> (\<Union>(l, g, a, r, u, l') \<in> trans (N p). {l, l'})"
    unfolding states_def by auto
  with trans_inv_closed' \<open>p < n_ps\<close> show ?thesis
    by auto
qed

(*
lemma map_prod_inv:
  "map.prod_inv (map_st (L, s)) = map_I2 prod_inv (map_st (L, s))" if "L \<in> states"
  unfolding map_I2_def
  unfolding map.prod_ta_def prod_ta_def
  unfolding map.trans_prod_def trans_prod_def
  unfolding map.prod_inv_def prod_inv_def
  subgoal \<comment>\<open>Invariant\<close>
    supply [simp] = 3
    unfolding case_prod_conv
    unfolding comp_def
    unfolding map_cc_def
    apply (auto split: if_splits prod.split)
     apply (drule sym)
     back
     apply (simp add: the_inv_f_f[OF inj_map_st])
    unfolding case_prod_conv
    unfolding map_concat
     apply (subst (asm) map_st_def)
     apply simp
     apply (rule arg_cong[where f = concat])
    unfolding map_map
     apply (rule map_cong, solve_triv)
     apply auto
     apply (subst 5)
      apply simp
    unfolding comp_def
     apply (auto simp: map_cc_def)
      apply (subst the_inv_f_f)
    subgoal
      by (simp add: map_loc_inj)
    using \<open>L \<in> _\<close> apply (auto dest: map_loc_injD simp add: L_len; fail)
    using \<open>L \<in> _\<close> apply (simp add: L_len)
     apply (auto dest: map_locD)

    apply (drule sym)
    back
    using \<open>L \<in> states\<close>
    apply (simp add: the_inv_f_f[OF inj_map_st])
    done
  done

interpretation TA_Equiv
  map.prod_ta
  "(map_t ` trans_prod, map_I2 prod_inv)"
  "{map_st (l, s) | l s. l \<in> states}"
  using state_set_states'
  by - (standard,
        auto simp: map_trans_prod[symmetric] trans_of_def map.prod_ta_def inv_of_def map_prod_inv)
*)

lemma map_prod_inv:
  "map.prod_inv (map_st (L, s)) = map_I prod_inv (map_st (L, s))" if "L \<in> states"
  unfolding map_I_def
  unfolding map.prod_ta_def prod_ta_def
  unfolding map.trans_prod_def trans_prod_def
  unfolding map.prod_inv_def prod_inv_def
  subgoal \<comment>\<open>Invariant\<close>
    supply [simp] = 3
  unfolding case_prod_conv
unfolding comp_def
  unfolding map_cc_def
  apply (auto split: if_split_asm)
  apply (subst the_inv_f_f, rule inj_map_st)
  unfolding case_prod_conv
  unfolding map_concat
  apply (subst map_st_def)
  apply (simp add: \<open>L \<in> _\<close> map_concat)
      apply (rule arg_cong[where f = concat])
      unfolding map_map
      apply (rule map_cong, solve_triv)
      apply auto
      apply (subst 5)
       apply simp
      unfolding comp_def
      apply (auto simp: map_cc_def)
       apply (subst the_inv_f_f)
      subgoal
        by (simp add: map_loc_inj)
      using \<open>L \<in> _\<close> apply (auto dest: map_loc_injD simp add: L_len; fail)
      using \<open>L \<in> _\<close> apply (simp add: L_len)
      apply (auto dest: map_locD)
      done
    done

interpretation TA_Equiv
  map.prod_ta
  "(map_t ` trans_prod, map_I prod_inv)"
  "{map_st (l, s) | l s. l \<in> states}"
  using state_set_states'
  by - (standard,
        auto simp: map_trans_prod[symmetric] trans_of_def map.prod_ta_def inv_of_def map_prod_inv)

lemma
  "map.prod_ta = (\<lambda> (T, I). (map_t ` T, map_I2 I)) prod_ta"
  unfolding map.prod_ta_def prod_ta_def
  apply clarsimp
  apply standard
   apply (rule map_trans_prod)
  oops

end (* Injectivity *)

end (* Anonymous context *)

end (* Mapping *)

end (* Simple_Network_Impl_map *)

context Simple_Network_Impl
begin

paragraph \<open>Conversion from integers to reals commutes with product construction.\<close>

sublocale conv: Prod_TA_Defs
  "(set broadcast, map (Simple_Network_Language.conv_A o automaton_of) automata, map_of bounds')" .

lemma (in -) conv_ac_inj:
  "ac = ac'" if "conv_ac ac = conv_ac ac'"
  using that by (cases ac; cases ac'; auto)

lemma (in -) conv_cc_inj:
  "cc = cc'" if "conv_cc cc = conv_cc cc'"
  using that by (subst (asm) inj_map_eq_map) (auto simp add: conv_ac_inj intro: injI)

context
begin

lemma conv_alt_def:
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

lemma conv_n_ps_eq:
  "conv.n_ps = n_ps"
  by (simp add: Prod_TA_Defs.n_ps_def)

private lemma 4:
  "conv.N i = Simple_Network_Language.conv_A (N i)" if "i < n_ps"
  using that unfolding n_ps_def Prod_TA_Defs.N_def fst_conv snd_conv by (subst nth_map | simp)+

private lemma 5:
  "inv (conv.N i) = conv_cc o (inv (N i))" if "i < n_ps"
  unfolding 4[OF that] unfolding Simple_Network_Language.conv_A_def
  by (simp split: prod.split add: inv_def)

lemma trans_conv_N_eq:
  "trans (conv.N i) = Simple_Network_Language.conv_t ` (trans (N i))"  if "i < n_ps"
  unfolding 4[OF that] unfolding Simple_Network_Language.conv_A_def
  by (simp split: prod.split add: trans_def)

private lemma 71:
  "(l, conv_cc g, a, r, u, l')\<in>Simple_Network_Language.trans (conv.N i)"
  if "(l, g, a, r, u, l')\<in>Simple_Network_Language.trans (N i)" "i < n_ps"
  using that by (force simp add: trans_conv_N_eq Simple_Network_Language.conv_t_def)

private lemma 72:
  "(l, conv_cc g, a, r, u, l')\<in>Simple_Network_Language.trans (conv.N i)
\<longleftrightarrow> (l, g, a, r, u, l')\<in>Simple_Network_Language.trans (N i)" if "i < n_ps"
  by (auto simp: trans_conv_N_eq[OF that] Simple_Network_Language.conv_t_def
           dest: conv_cc_inj intro: image_eqI[rotated])

private lemma 73:
  "\<exists>g'. g = conv_cc g' \<and> (l, g', a, r, u, l')\<in>Simple_Network_Language.trans (N i)"
  if "(l, g, a, r, u, l')\<in>Simple_Network_Language.trans (conv.N i)" "i < n_ps"
  using that by (force simp: trans_conv_N_eq Simple_Network_Language.conv_t_def)

lemma conv_bounds[simp]:
  "conv.bounds = bounds"
  unfolding conv.bounds_def bounds_def by simp

lemma conv_states[simp]:
  "conv.states = states"
  unfolding conv.states_def states_def conv_n_ps_eq
  by (auto simp add: trans_conv_N_eq Simple_Network_Language.conv_t_def) (fastforce, force)

private lemma 9:
  "commited (conv.N p) = commited (N p)" if \<open>p < n_ps\<close>
  unfolding 4[OF that] unfolding Simple_Network_Language.conv_A_def
  by (simp split: prod.split add: commited_def)

private lemma 10:
  "conv.broadcast = set broadcast"
  unfolding conv.broadcast_def by simp

lemma conv_trans_int:
  "conv.trans_int = (\<lambda>(l, g, a, r, l'). (l, map conv_ac g, a, r, l')) ` trans_int"
  unfolding conv.trans_int_def trans_int_def
  supply [simp] = L_len
  apply standard
  subgoal
    by (clarsimp simp: Simple_Network_Language.conv_t_def conv_n_ps_eq trans_conv_N_eq 9)
      (intros add: more_intros, solve_triv+)
  subgoal
    by (rule subsetI,
        clarsimp simp: Simple_Network_Language.conv_t_def conv_n_ps_eq trans_conv_N_eq 9[symmetric])
      ((drule (1) 71)+, intros add: more_intros, solve_triv+)
  done

lemma conv_trans_bin:
  "conv.trans_bin = (\<lambda>(l, g, a, r, l'). (l, map conv_ac g, a, r, l')) ` trans_bin"
  unfolding conv.trans_bin_def trans_bin_def
  supply [simp] = L_len
  apply standard
  subgoal
    by (clarsimp simp add: Simple_Network_Language.conv_t_def conv_n_ps_eq trans_conv_N_eq 9)
      (intros add: more_intros, solve_triv+)
  subgoal
    by (rule subsetI,
        clarsimp simp: Simple_Network_Language.conv_t_def conv_n_ps_eq trans_conv_N_eq 9[symmetric])
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
      apply (clarsimp simp add: conv_n_ps_eq 9 10 broadcast_def split: prod.split_asm)
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
        Simple_Network_Language.conv_t_def
        conv_n_ps_eq trans_conv_N_eq 9[symmetric] 10 broadcast_def map_concat)
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
  unfolding conv.N_def N_def conv_n_ps_eq
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
  unfolding N_eq[OF that] by (auto split: prod.splits simp: automaton_of_def trans_def)

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
        by (force dest!: nth_mem collect_clock_pairs_invsI
            split: prod.split_asm simp: inv_def Prod_TA_Defs.n_ps_def)
      done
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
  moreover have "range prod_inv \<subseteq> concat ` ?X \<union> {[]}"
  proof
    fix x assume "x \<in> range prod_inv"
    then consider L where "x = concat (map (\<lambda>p. (inv (N p)) (L ! p)) [0..<n_ps])" | "x = []"
      unfolding prod_inv_def by (auto split: if_split_asm)
    then show "x \<in> concat ` ?X \<union> {[]}"
      by (cases; force)
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
  using assms by (subst N_eq) (auto simp: automaton_of_def trans_def split: prod.split)

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
  by (auto intro: finite_range_default_map_of split: prod.split simp: inv_def)

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

locale Simple_Network_Impl_nat_defs =
  Simple_Network_Impl automata
  for automata ::
    "(nat list \<times> (nat act, nat, nat, int, nat, int) transition list
      \<times> (nat \<times> (nat, int) cconstraint) list) list" +
  fixes m :: nat and num_states :: "nat \<Rightarrow> nat" and num_actions :: nat

locale Simple_Network_Impl_nat =
  Simple_Network_Impl_nat_defs +
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
  assumes broadcast_receivers:
  "\<forall>(_, trans, _) \<in> set automata. \<forall>(_, g, a, _, _, _) \<in> set trans.
      case a of In a \<Rightarrow> a \<in> set broadcast \<longrightarrow> g = [] | _ \<Rightarrow> True"
begin

lemma broadcast_receivers_unguarded:
  "\<forall>p<n_ps. \<forall>l g a f r l'.
    (l, g, In a, f, r, l') \<in> Simple_Network_Language.trans (N p) \<and> a \<in> set broadcast \<longrightarrow> g = []"
  using broadcast_receivers by (fastforce dest: nth_mem simp: n_ps_def mem_trans_N_iff)

sublocale conv: Prod_TA
  "(set broadcast, map (Simple_Network_Language.conv_A o automaton_of) automata, map_of bounds')"
  using broadcast_receivers_unguarded
  by - (standard,
 fastforce simp: conv.broadcast_def Simple_Network_Language.conv_t_def conv_n_ps_eq trans_conv_N_eq)

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

no_notation
  comp2  (infixl "\<circ>\<circ>" 55) and
  comp3  (infixl "\<circ>\<circ>\<circ>" 55)

(*
print_locale Simple_Network_Impl

context Simple_Network_Impl
begin

sublocale sem:
  Simple_Network_Impl
  "map conv_automaton automata"

end
*)

context Simple_Network_Impl
begin

abbreviation "sem \<equiv> (set broadcast, map (automaton_of o conv_automaton) automata, map_of bounds')"

sublocale sem: Prod_TA_sem sem .

lemma sem_N_eq:
  "sem.N p = automaton_of (conv_automaton (automata ! p))" if \<open>p < n_ps\<close>
  using that unfolding sem.N_def n_ps_def fst_conv snd_conv by (subst nth_map) auto

end (* Simple Network Impl *)

inductive_cases step_u_elims:
  "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Del\<^esub> \<langle>L', s', u'\<rangle>"
  "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L', s', u'\<rangle>"
  "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Bin a\<^esub> \<langle>L', s'', u'\<rangle>"
  "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Broad a\<^esub> \<langle>L', s'', u'\<rangle>"

inductive_cases step_u_elims':
  "(broadcast, N, B) \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Del\<^esub> \<langle>L', s', u'\<rangle>"
  "(broadcast, N, B) \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L', s', u'\<rangle>"
  "(broadcast, N, B) \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Bin a\<^esub> \<langle>L', s'', u'\<rangle>"
  "(broadcast, N, B) \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Broad a\<^esub> \<langle>L', s'', u'\<rangle>"

lemma (in Prod_TA_Defs) states_lengthD:
  "length L = n_ps" if "L \<in> states"
  using that unfolding states_def by simp

end (* Theory *)
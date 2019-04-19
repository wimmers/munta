theory Simple_Network_Language_Model_Checking
  imports Simple_Network_Language_Impl_Refine
    "TA_Byte_Code.UPPAAL_Model_Checking" "TA_Impl.Abstract_Term"
begin

section \<open>Product Bisimulation\<close>

no_notation State_Networks.step_sn ("_ \<turnstile> \<langle>_, _, _\<rangle> \<rightarrow>\<^bsub>_\<^esub> \<langle>_, _, _\<rangle>" [61,61,61,61,61] 61)

text \<open>
  We have proved the necessary theorems already but we need to lift it to
  the case where delay and action transitions are strictly alternating.
\<close>
inductive step_u' ::
  "('a, 's, 'c, 't :: time, 'x, 'v :: linorder) nta \<Rightarrow> 's list \<Rightarrow> ('x \<rightharpoonup> 'v) \<Rightarrow> ('c, 't) cval
  \<Rightarrow> 's list \<Rightarrow> ('x \<rightharpoonup> 'v) \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _, _\<rangle> \<rightarrow> \<langle>_, _, _\<rangle>" [61,61,61,61] 61) where
  "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L'', s'', u''\<rangle>" if
  "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Del\<^esub> \<langle>L', s', u'\<rangle>"
  "a \<noteq> Del"
  "A \<turnstile> \<langle>L', s', u'\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L'', s'', u''\<rangle>"

inductive_cases step'_elims: "A \<turnstile>' \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L', s'), u'\<rangle>"

inductive_cases step_u'_elims: "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"

theorem Bisimulation_Invariant_strong_intro:
  fixes A :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and P :: "'a \<Rightarrow> bool"
    and B :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "\<And>a b. A a b \<Longrightarrow> P a \<Longrightarrow> B a b"
    and "\<And>a b. B a b \<Longrightarrow> P a \<Longrightarrow> A a b"
    and "\<And>a b. P a \<Longrightarrow> A a b \<Longrightarrow> P b"
  shows "Bisimulation_Invariant A B (=) P P"
  apply standard
  subgoal A for a b a'
    by (blast intro: assms)
  subgoal B for a b a'
    by (blast intro: assms)
  subgoal C for a b
    by (rule assms)
  subgoal D for a b
    by (rule C, assumption) (rule assms)
  done

context Prod_TA_Defs
begin

definition
  "all_prop L s = (L \<in> states \<and> bounded bounds s)"

lemma all_prop_boundedD[dest]:
  "bounded bounds s" if "all_prop L s"
  using that unfolding all_prop_def ..

lemma all_prop_statesD[dest]:
  "L \<in> states" if "all_prop L s"
  using that unfolding all_prop_def ..

end (* Prod TA Defs *)

context Prod_TA
begin

lemma prod_action_step_not_eq_delay:
  "a \<noteq> Del" if "prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>(L', s'), u'\<rangle>"
  using that
  apply cases
  unfolding trans_of_def
  unfolding prod_ta_def trans_prod_def
  by (auto simp: trans_int_def trans_bin_def trans_broad_def)

lemma prod_all_prop_inv:
  "all_prop L' s'" if "all_prop L s" "prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L', s'), u'\<rangle>"
  using that unfolding all_prop_def
  by (auto elim: bounded_inv states_inv simp: step_iff[symmetric])

lemma prod_all_prop_inv':
  "all_prop L' s'" if "all_prop L s" "prod_ta \<turnstile>' \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L', s'), u'\<rangle>"
  using that by (auto intro: prod_all_prop_inv elim!: step'_elims)

interpretation prod_bisim:
  Bisimulation_Invariant
  "(\<lambda> (L, s, u) (L', s', u'). prod_ta \<turnstile>' \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L', s'), u'\<rangle>)"
  "(\<lambda> (L, s, u) (L', s', u'). A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)"
  "(=)"
  "(\<lambda> (L, s, u). all_prop L s)"
  "(\<lambda> (L, s, u). all_prop L s)"
  apply (rule Bisimulation_Invariant_strong_intro; clarsimp)
  subgoal
    by (auto intro: step_u'.intros simp: all_prop_def
             dest: action_sound prod_action_step_not_eq_delay delay_sound elim!: step'_elims)
  subgoal
    by (auto 4 4 dest: prod_all_prop_inv action_complete elim: delay_complete elim!: step_u'_elims)
  subgoal
    by (rule prod_all_prop_inv')
  done

lemmas prod_bisim_intro = prod_bisim.Bisimulation_Invariant_axioms

end (* Prod TA *)


section \<open>The final semantics\<close>

text \<open>State formulas\<close>
datatype ('n, 's, 'a, 'b) sexp =
  true |
  \<comment> \<open>Boolean connectives\<close>
  not "('n, 's, 'a, 'b) sexp" | "and" "('n, 's, 'a, 'b) sexp" "('n, 's, 'a, 'b) sexp" |
  or "('n, 's, 'a, 'b) sexp" "('n, 's, 'a, 'b) sexp" | imply "('n, 's, 'a, 'b) sexp" "('n, 's, 'a, 'b) sexp" |
  \<comment> \<open>Does var \<open>a\<close> equal \<open>x\<close>?\<close>
  eq 'a 'b |
  le 'a 'b |
  lt 'a 'b |
  ge 'a 'b |
  gt 'a 'b |
  \<comment> \<open>Is procces \<open>i\<close> in location \<open>l\<close>?\<close>
  loc 'n 's

datatype ('n, 's, 'a, 'b) formula =
  EX "('n, 's, 'a, 'b) sexp" | EG "('n, 's, 'a, 'b) sexp"
| AX "('n, 's, 'a, 'b) sexp" | AG "('n, 's, 'a, 'b) sexp"
| Leadsto "('n, 's, 'a, 'b) sexp" "('n, 's, 'a, 'b) sexp"

fun check_sexp :: "(nat, 's, 'a, 'b :: linorder) sexp \<Rightarrow> 's list \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "check_sexp sexp.true _ _ \<longleftrightarrow> True" |
  "check_sexp (not e) L s \<longleftrightarrow> \<not> check_sexp e L s" |
  "check_sexp (and e1 e2) L s \<longleftrightarrow> check_sexp e1 L s \<and> check_sexp e2 L s" |
  "check_sexp (sexp.or e1 e2) L s \<longleftrightarrow> check_sexp e1 L s \<or> check_sexp e2 L s" |
  "check_sexp (imply e1 e2) L s \<longleftrightarrow> check_sexp e1 L s \<longrightarrow> check_sexp e2 L s" |
  "check_sexp (eq i x) L s \<longleftrightarrow> s i = x" |
  "check_sexp (le i x) L s \<longleftrightarrow> s i \<le> x" |
  "check_sexp (lt i x) L s \<longleftrightarrow> s i < x" |
  "check_sexp (ge i x) L s \<longleftrightarrow> s i \<ge> x" |
  "check_sexp (gt i x) L s \<longleftrightarrow> s i > x" |
  "check_sexp (loc i x) L s \<longleftrightarrow> L ! i = x"

fun locs_of_sexp :: "('n, 's, 'a, 'b) sexp \<Rightarrow> 'n set" where
  "locs_of_sexp (not e) = locs_of_sexp e" |
  "locs_of_sexp (and e1 e2) = locs_of_sexp e1 \<union> locs_of_sexp e2" |
  "locs_of_sexp (sexp.or e1 e2) = locs_of_sexp e1 \<union> locs_of_sexp e2" |
  "locs_of_sexp (imply e1 e2) = locs_of_sexp e1 \<union> locs_of_sexp e2" |
  "locs_of_sexp (loc i x) = {i}" |
  "locs_of_sexp _ = {}"

fun vars_of_sexp :: "('n, 's, 'a, 'b) sexp \<Rightarrow> 'a set" where
  "vars_of_sexp (not e) = vars_of_sexp e" |
  "vars_of_sexp (and e1 e2) = vars_of_sexp e1 \<union> vars_of_sexp e2" |
  "vars_of_sexp (sexp.or e1 e2) = vars_of_sexp e1 \<union> vars_of_sexp e2" |
  "vars_of_sexp (imply e1 e2) = vars_of_sexp e1 \<union> vars_of_sexp e2" |
  "vars_of_sexp (eq i x) = {i}" |
  "vars_of_sexp (lt i x) = {i}" |
  "vars_of_sexp (le i x) = {i}" |
  "vars_of_sexp (ge i x) = {i}" |
  "vars_of_sexp (gt i x) = {i}" |
  "vars_of_sexp _ = {}"

fun locs_of_formula :: "('n, 's, 'a, 'b) formula \<Rightarrow> 'n set" where
  "locs_of_formula (formula.EX \<phi>) = locs_of_sexp \<phi>" |
  "locs_of_formula (EG \<phi>) = locs_of_sexp \<phi>" |
  "locs_of_formula (AX \<phi>) = locs_of_sexp \<phi>" |
  "locs_of_formula (AG \<phi>) = locs_of_sexp \<phi>" |
  "locs_of_formula (Leadsto \<phi> \<psi>) = locs_of_sexp \<phi> \<union> locs_of_sexp \<psi>"

fun vars_of_formula :: "('n, 's, 'a, 'b) formula \<Rightarrow> 'a set" where
  "vars_of_formula (formula.EX \<phi>) = vars_of_sexp \<phi>" |
  "vars_of_formula (EG \<phi>) = vars_of_sexp \<phi>" |
  "vars_of_formula (AX \<phi>) = vars_of_sexp \<phi>" |
  "vars_of_formula (AG \<phi>) = vars_of_sexp \<phi>" |
  "vars_of_formula (Leadsto \<phi> \<psi>) = vars_of_sexp \<phi> \<union> vars_of_sexp \<psi>"

fun hd_of_formula :: "(nat, 's, 'a, 'b) formula \<Rightarrow> 's list \<Rightarrow> ('a \<Rightarrow> 'b :: linorder) \<Rightarrow> bool" where
  "hd_of_formula (formula.EX \<phi>) L s = check_sexp \<phi> L s" |
  "hd_of_formula (EG \<phi>) L s = check_sexp \<phi> L s" |
  "hd_of_formula (AX \<phi>) L s = Not (check_sexp \<phi> L s)" |
  "hd_of_formula (AG \<phi>) L s = Not (check_sexp \<phi> L s)" |
  "hd_of_formula (Leadsto \<phi> _) L s = check_sexp \<phi> L s"

definition models ("_,_ \<Turnstile> _" [61,61] 61) where
  "A,a\<^sub>0 \<Turnstile> \<Phi> \<equiv> (case \<Phi> of
    formula.EX \<phi> \<Rightarrow>
      Graph_Defs.Ex_ev
        (\<lambda> (L, s, u) (L', s', u'). A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)
        (\<lambda> (L, s, _). check_sexp \<phi> L (the o s))
  | formula.EG \<phi> \<Rightarrow>
      Graph_Defs.Ex_alw
        (\<lambda> (L, s, u) (L', s', u'). A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)
        (\<lambda> (L, s, _). check_sexp \<phi> L (the o s))
  | formula.AX \<phi> \<Rightarrow>
      Graph_Defs.Alw_ev
        (\<lambda> (L, s, u) (L', s', u'). A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)
        (\<lambda> (L, s, _). check_sexp \<phi> L (the o s))
  | formula.AG \<phi> \<Rightarrow>
      Graph_Defs.Alw_alw
        (\<lambda> (L, s, u) (L', s', u'). A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)
        (\<lambda> (L, s, _). check_sexp \<phi> L (the o s))
  | formula.Leadsto \<phi> \<psi> \<Rightarrow>
      Graph_Defs.leadsto
        (\<lambda> (L, s, u) (L', s', u'). A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)
        (\<lambda> (L, s, _). check_sexp \<phi> L (the o s))
        (\<lambda> (L, s, _). check_sexp \<psi> L (the o s))
  ) a\<^sub>0
  "

lemmas models_iff = models_def[unfolded Graph_Defs.Ex_alw_iff Graph_Defs.Alw_alw_iff]

fun check_sexpi :: "(nat, 's, nat, int) sexp \<Rightarrow> 's list \<Rightarrow> int list \<Rightarrow> bool" where
  "check_sexpi sexp.true _ _ \<longleftrightarrow> True" |
  "check_sexpi (not e) L s \<longleftrightarrow> \<not> check_sexpi e L s" |
  "check_sexpi (and e1 e2) L s \<longleftrightarrow> check_sexpi e1 L s \<and> check_sexpi e2 L s" |
  "check_sexpi (sexp.or e1 e2) L s \<longleftrightarrow> check_sexpi e1 L s \<or> check_sexpi e2 L s" |
  "check_sexpi (imply e1 e2) L s \<longleftrightarrow> check_sexpi e1 L s \<longrightarrow> check_sexpi e2 L s" |
  "check_sexpi (eq i x) L s \<longleftrightarrow> s ! i = x" |
  "check_sexpi (le i x) L s \<longleftrightarrow> s ! i \<le> x" |
  "check_sexpi (lt i x) L s \<longleftrightarrow> s ! i < x" |
  "check_sexpi (ge i x) L s \<longleftrightarrow> s ! i \<ge> x" |
  "check_sexpi (gt i x) L s \<longleftrightarrow> s ! i > x" |
  "check_sexpi (loc i x) L s \<longleftrightarrow> L ! i = x"

fun hd_of_formulai :: "(nat, 's, nat, int) formula \<Rightarrow> 's list \<Rightarrow> int list \<Rightarrow> bool" where
  "hd_of_formulai (formula.EX \<phi>) L s = check_sexpi \<phi> L s" |
  "hd_of_formulai (EG \<phi>) L s = check_sexpi \<phi> L s" |
  "hd_of_formulai (AX \<phi>) L s = Not (check_sexpi \<phi> L s)" |
  "hd_of_formulai (AG \<phi>) L s = Not (check_sexpi \<phi> L s)" |
  "hd_of_formulai (Leadsto \<phi> _) L s = check_sexpi \<phi> L s"


section \<open>Instantiating the Model Checking Locale\<close>

text \<open>
  This locale certifies that a given local clock ceiling is correct.
  Moreover, we certify that the vector of initial locations has outgoing transitions for
  each automaton, and that all variables of the initial state are in bounds.
\<close>
locale Simple_Network_Impl_nat_ceiling_start_state =
  Simple_Network_Impl_nat +
  fixes k :: "nat list list list"
    and L\<^sub>0 :: "nat list"
    and s\<^sub>0 :: "(nat \<times> int) list"
    and formula :: "(nat, nat, nat, int) formula"
    and show_clock :: "nat \<Rightarrow> string"
    and show_state :: "nat list \<times> int list \<Rightarrow> string"
  assumes k_ceiling:
    "\<forall>i < n_ps. \<forall>(l, g) \<in> set ((snd o snd) (automata ! i)).
      \<forall>(x, m) \<in> collect_clock_pairs g. m \<le> int (k ! i ! l ! x)"
    "\<forall>i < n_ps. \<forall>(l, _, g, _) \<in> set ((fst o snd) (automata ! i)).
      (\<forall>(x, m) \<in> collect_clock_pairs g. m \<le> int (k ! i ! l ! x))"
  and k_resets:
    "\<forall>i < n_ps. \<forall> (l, b, g, a, upd, r, l') \<in> set ((fst o snd) (automata ! i)).
       \<forall>c \<in> {0..<m+1} - set r. k ! i ! l' ! c \<le> k ! i ! l ! c"
  and k_length:
    "length k = n_ps" "\<forall> i < n_ps. length (k ! i) = num_states i"
    "\<forall> xs \<in> set k. \<forall> xxs \<in> set xs. length xxs = m + 1"
  and k_0:
    "\<forall>i < n_ps. \<forall>l < num_states i. k ! i ! l ! 0 = 0"
  and inv_unambiguous:
    "\<forall>(_, _, inv) \<in> set automata. distinct (map fst inv)"
  and s\<^sub>0_bounded: "bounded bounds (map_of s\<^sub>0)"
  and L\<^sub>0_len: "length L\<^sub>0 = n_ps"
  and L\<^sub>0_has_trans: "\<forall>i < n_ps. L\<^sub>0 ! i \<in> fst ` set ((fst o snd) (automata ! i))"
  and vars_of_formula: "vars_of_formula formula \<subseteq> {0..<n_vs}"
  (* and num_states_length: "\<forall>i<n_ps. num_states i = length (fst (snd (automata ! i)))" *)
begin

text \<open>
The ceiling \<open>k\<close> is correct for each individual automaton in the network.
We now construct a ceiling for the product automaton:
\<close>
definition
  "k_fun l c \<equiv>
    if (c > 0 \<and> c \<le> m) \<and> fst l \<in> states then Max {k ! i ! (fst l ! i) ! c | i . i < n_ps} else 0"

lemma (in -) default_map_of_distinct:
  "(k, default_map_of x xs k) \<in> set xs \<union> {(k, x)}" if "distinct (map fst xs)"
  unfolding default_map_of_alt_def by clarsimp (simp add: map_of_eq_Some_iff[OF that])

lemma N_inv:
  "(L ! i, inv (N i) (L ! i)) \<in> set ((snd o snd) (automata ! i)) \<union> {(L ! i, [])}" if "i < n_ps"
  unfolding N_def comp_def fst_conv snd_conv inv_def
  using that
  apply (subst nth_map)
   apply (simp add: n_ps_def; fail)
  apply (clarsimp split: prod.split simp: automaton_of_def)
  subgoal for _ _ xs
    using default_map_of_distinct[of xs "L ! i" "[]"] inv_unambiguous that
    by (auto dest!: nth_mem simp: n_ps_def)
  done

lemma (in -) subset_nat_0_atLeastLessThan_conv:
  "S \<subseteq> {0..<n::nat} \<longleftrightarrow> (\<forall> x \<in> S. x < n)"
  by auto

lemma k_ceiling_rule:
  "m \<le> int (k ! i ! l ! x)"
  if "i < n_ps" "(l, b, g, xx) \<in> set ((fst o snd) (automata ! i))" "(x, m) \<in> collect_clock_pairs g"
  for i l x g xx
  using that k_ceiling(2) by fastforce

lemma k_ceiling_1:
  "\<forall>s. \<forall>L \<in> states. \<forall>(x,m) \<in> clkp_set prod_ta (L, s). m \<le> k_fun (L, s) x"
proof safe
  fix L s c x
  assume \<open>L \<in> states\<close> \<open>(c, x) \<in> Closure.clkp_set prod_ta (L, s)\<close>
  have "0 < c" "c \<le> m"
  proof -
    from \<open>(c, x) \<in> _\<close> have "(c, x) \<in> Timed_Automata.clkp_set prod_ta"
      unfolding TA_clkp_set_unfold by auto
    with clock_range show "0 < c" "c \<le> m"
      by auto
  qed
  with \<open>L \<in> _\<close> have "k_fun (L, s) c = Max {k ! i ! (L ! i) ! c | i . i < n_ps}"
    unfolding k_fun_def by auto
  have Max_aux: "x \<le> int (Max {k ! i ! (L ! i) ! c |i. i < n_ps})"
    if "x \<le> int (k ! p ! (L ! p) ! c)" "p < n_ps" for p
  proof -
    from \<open>p < n_ps \<close> have "k ! p ! (L ! p) ! c \<le> Max {k ! i ! (L ! i) ! c |i. i < n_ps}"
      by (intro Max_ge) auto
    with \<open>x \<le> _\<close> show ?thesis
      by simp
  qed
  from \<open>(c, x) \<in> _\<close> show \<open>x \<le> k_fun (L, s) c\<close>
    unfolding clkp_set_def
  proof safe
    assume \<open>(c, x) \<in> Closure.collect_clki (inv_of prod_ta) (L, s)\<close>
    then show \<open>x \<le> k_fun (L, s) c\<close>
      using k_ceiling(1) unfolding collect_clki_def \<open>k_fun (L, s) c = _\<close>
      by (force intro: Max_aux dest: N_inv simp: prod_inv_def collect_clock_pairs_def k_fun_def)
  next
    assume \<open>(c, x) \<in> Closure.collect_clkt (trans_of prod_ta) (L, s)\<close>
    then show \<open>x \<le> k_fun (L, s) c\<close>
      unfolding collect_clkt_def \<open>k_fun (L, s) c = _\<close>
      apply (clarsimp simp: trans_prod_def collect_clock_pairs_def k_fun_def)
      apply safe
      subgoal
        using k_ceiling(2) unfolding trans_int_def
        apply (clarsimp simp: mem_trans_N_iff L_len subset_nat_0_atLeastLessThan_conv)
        apply (fastforce intro!: Max_aux simp: collect_clock_pairs_def)
        done
      subgoal
        using k_ceiling(2) unfolding trans_bin_def
        apply (clarsimp simp: mem_trans_N_iff L_len subset_nat_0_atLeastLessThan_conv)
        apply (erule disjE)
         apply (force intro!: Max_aux simp: collect_clock_pairs_def)+
        done
      subgoal
        using k_ceiling(2) unfolding trans_broad_def
        apply (clarsimp simp: mem_trans_N_iff L_len subset_nat_0_atLeastLessThan_conv)
        apply (erule disjE)
         apply (fastforce intro!: Max_aux simp: collect_clock_pairs_def)
        apply (erule bexE)
        apply (force intro!: Max_aux simp: collect_clock_pairs_def)
        done
      done
  qed
qed

lemma k_fun_mono':
  "k_fun (L, s) c \<le> k_fun (L', s') c" if
  "\<forall>i < n_ps. k ! i ! (L ! i) ! c \<le> k ! i ! (L' ! i) ! c" "L \<in> states" "L' \<in> states"
  using that unfolding k_fun_def
  apply clarsimp
  apply (cases "n_ps = 0")
   apply (simp; fail)
  apply (rule Max.boundedI)
    apply (simp; fail)
   apply blast
  apply safe
  subgoal for _ i
    by - (rule order.trans[where b = "k ! i ! (L' ! i) ! c"], auto intro: Max_ge)
  done

lemma k_fun_mono:
  \<open>Max {k ! i ! (L ! i) ! c | i . i < n_ps} \<le> Max {k ! i ! (L' ! i) ! c | i . i < n_ps}\<close>
  if \<open>\<forall>i < n_ps. k ! i ! (L ! i) ! c \<le> k ! i ! (L' ! i) ! c\<close>
  apply (cases "n_ps = 0")
   apply (simp; fail)
  apply (rule Max.boundedI)
    apply (simp; fail)
   apply blast
  apply safe
  subgoal for _ i
    using that by - (rule order.trans[where b = "k ! i ! (L' ! i) ! c"], auto intro: Max_ge)
  done

lemma (in -) fold_upds_aux1:
  "fold (\<lambda>p L. L[p := g p]) ps xs ! i = xs ! i" if \<open>i \<notin> set ps\<close>
  using that by (induction ps arbitrary: xs) auto

lemma (in -) fold_upds_aux2:
  "fold (\<lambda>p L. L[p := g p]) ps xs ! i = g i" if \<open>distinct ps\<close> \<open>i \<in> set ps\<close> \<open>i < length xs\<close>
  using that by (induction ps arbitrary: xs) (auto simp: fold_upds_aux1)

lemma (in -) fold_upds_aux_length:
  "length (fold (\<lambda>p L. L[p := g p]) ps xs) = length xs"
  by (induction ps arbitrary: xs) auto

(* XXX Duplication *)
lemma (in -) state_set_eq[simp]:
  "Simulation_Graphs_TA.state_set A = state_set (trans_of A)"
  unfolding Simulation_Graphs_TA.state_set_def state_set_def trans_of_def ..

lemma prod_ta_step_statesD:
  assumes "prod_ta \<turnstile> (L, s) \<longrightarrow>\<^bsup>g,a,r\<^esup> (L', s')"
  shows "L \<in> states" "L' \<in> states"
  using assms state_set_states by (fastforce dest: state_setI1 state_setI2)+

lemma k_ceiling_2:
  "\<forall>l g a r l'. \<forall> c \<le> m. prod_ta \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<and> c \<notin> set r \<longrightarrow> k_fun l' c \<le> k_fun l c"
proof safe
  fix L s g a r L' s' c
  assume A: \<open>c \<le> m\<close> \<open>prod_ta \<turnstile> (L, s) \<longrightarrow>\<^bsup>g,a,r\<^esup> (L', s')\<close> \<open>c \<notin> set r\<close>
  then have "L \<in> states" "L' \<in> states"
    by - (rule prod_ta_step_statesD, assumption)+
  from A have \<open>Max {k ! i ! (L' ! i) ! c | i . i < n_ps} \<le> Max {k ! i ! (L ! i) ! c | i . i < n_ps}\<close>
    apply simp
    unfolding trans_prod_def
    apply auto
    subgoal
      using k_resets
      unfolding trans_int_def
      apply clarsimp
      apply (rule k_fun_mono)
      apply (clarsimp simp: mem_trans_N_iff L_len subset_nat_0_atLeastLessThan_conv)
      subgoal for b f p aa l' i
        by (cases "p = i"; force simp add: L_len)
      done
    subgoal
      using k_resets
      unfolding trans_bin_def
      apply clarsimp
      apply (rule k_fun_mono)
      apply (clarsimp simp: mem_trans_N_iff L_len subset_nat_0_atLeastLessThan_conv)
      subgoal for _ _ p q b1 g1 f1 r1 l1' b2 g2 f2 r2 l2' i
        by (cases "p = i"; cases "q = i"; force simp add: L_len)
      done
    subgoal
      using k_resets
      unfolding trans_broad_def
      apply clarsimp
      apply (rule k_fun_mono)
      apply (clarsimp simp: mem_trans_N_iff L_len subset_nat_0_atLeastLessThan_conv)
      subgoal premises prems for s'a aa p b ga f ra l' bs gs fs rs ls' ps i
      proof (cases "p = i")
        case True
        with \<open>p \<notin> _\<close> \<open>i < _\<close> \<open>L \<in> states\<close> have "fold (\<lambda>p L. L[p := ls' p]) ps L[p := l'] ! i = l'"
          by (simp add: L_len fold_upds_aux_length)
        with prems \<open>p = i\<close> show ?thesis
          by (fastforce simp add: L_len)
      next
        case False
        then have *: "fold (\<lambda>p L. L[p := ls' p]) ps L[p := l'] ! i
          = fold (\<lambda>p L. L[p := ls' p]) ps L ! i"
          by simp
        show ?thesis
        proof (cases "i \<in> set ps")
          case True
          then have **: "fold (\<lambda>p L. L[p := ls' p]) ps L ! i = ls' i"
            using \<open>distinct ps\<close> \<open>i < n_ps\<close> \<open>L \<in> states\<close> by (auto simp: fold_upds_aux2)
          moreover have
            "(L ! i, bs i, gs i, In aa, fs i, rs i, ls' i) \<in> set (fst (snd (automata ! i)))"
            using \<open>p \<noteq> i\<close> True prems by fast
          moreover have "c\<in>{0..<Suc m} - set (rs i)"
            using \<open>p \<noteq> i\<close> True prems by force
          ultimately show ?thesis
            using prems(2) \<open>i < n_ps\<close> by (auto 4 3 simp add: *)
        next
          case False
          with \<open>p \<noteq> i\<close> show ?thesis
            by (simp add: fold_upds_aux1)
        qed
      qed
      done
    done
  with \<open>L \<in> states\<close> \<open>L' \<in> states\<close> \<open>c \<le> m\<close> show "k_fun (L', s') c \<le> k_fun (L, s) c"
    by (auto simp: k_fun_def)
qed



abbreviation "F \<equiv> \<lambda>(L, s). hd_of_formula formula L (the o s)"
abbreviation "Fi \<equiv> \<lambda>(L, s). hd_of_formulai formula L s"

lemma (in Simple_Network_Impl_nat) check_sexp_check_sexpi:
  "check_sexp e L (the o s) \<longleftrightarrow> check_sexpi e L s'"
  if "state_rel s s'" "vars_of_sexp e \<subseteq> {0..<n_vs}"
  using that unfolding state_rel_def by (induction e) auto

lemma (in Simple_Network_Impl_nat) hd_of_formula_hd_of_formulai:
  "hd_of_formula \<phi> L (the o s) \<longleftrightarrow> hd_of_formulai \<phi> L s'"
  if "state_rel s s'" "vars_of_formula \<phi> \<subseteq> {0..<n_vs}"
  using that by (induction \<phi>) (auto simp: check_sexp_check_sexpi)

lemma F_Fi:
  "F l \<longleftrightarrow> Fi l'" if "(l', l) \<in> loc_rel"
  using vars_of_formula that unfolding loc_rel_def by clarsimp (erule hd_of_formula_hd_of_formulai)


abbreviation "l\<^sub>0 \<equiv> (L\<^sub>0, map_of s\<^sub>0)"
abbreviation "s\<^sub>0i \<equiv> map (the o map_of s\<^sub>0) [0..<n_vs]"
abbreviation "l\<^sub>0i \<equiv> (L\<^sub>0, s\<^sub>0i)"

lemma state_rel_start:
  "state_rel (map_of s\<^sub>0) s\<^sub>0i"
  using s\<^sub>0_bounded unfolding state_rel_def bounded_def dom_bounds_eq by auto

lemma statesI:
  "L \<in> states" if "length L = n_ps" "\<forall>i<n_ps. L ! i \<in> fst ` set (fst (snd (automata ! i)))"
  using that unfolding states_def by (auto 4 3 simp: mem_trans_N_iff[symmetric])

lemma L\<^sub>0_states[simp, intro]:
  "L\<^sub>0 \<in> states"
  using L\<^sub>0_has_trans L\<^sub>0_len by (auto intro: statesI)

lemma l\<^sub>0_states'[simp, intro]:
  "l\<^sub>0 \<in> states'"
  using state_rel_start s\<^sub>0_bounded unfolding states'_def state_rel_def by auto

print_locale Reachability_Problem_Defs

sublocale reach: Reachability_Problem_Defs
  prod_ta
  l\<^sub>0
  m
  k_fun
  F
  .

lemma (in -) collect_clkt_state_setI:
  assumes "(x, d) \<in> Closure.collect_clkt (trans_of A) l"
  shows "l \<in> state_set (trans_of A)" "l \<in> Simulation_Graphs_TA.state_set A"
  using assms unfolding collect_clkt_def by (auto simp: state_set_def)

lemma clkp_set_statesD:
  fixes x d
  assumes "(x, d)\<in>Closure.clkp_set prod_ta (L, s)"
  shows "L \<in> states"
  using assms
  unfolding clkp_set_def collect_clki_def
  apply safe
  subgoal
    apply simp
    unfolding prod_inv_def
    unfolding collect_clock_pairs_def
    apply auto
    done
  apply (drule collect_clkt_state_setI)
  using state_set_states by auto

sublocale reach1: Reachability_Problem
  prod_ta
  l\<^sub>0
  m
  k_fun
  F
  apply standard
  subgoal
    apply safe
    using k_ceiling_1
    subgoal for L s x m
      apply (cases "L \<in> states")
       apply blast
      apply (auto dest: clkp_set_statesD simp: k_fun_def)
      done
    done
  subgoal
    apply safe
    subgoal for L s g a r L' s' c
      apply (cases "c \<le> m")
      using k_ceiling_2
       apply force
      apply (auto simp: k_fun_def)
      done
    done
  subgoal
    by (simp add: k_fun_def)
  subgoal
    by (simp add: k_fun_def)
  done

lemma states'_superset:
  "{l\<^sub>0} \<union> Normalized_Zone_Semantics_Impl_Refine.state_set trans_prod \<subseteq> states'"
  (is "{l\<^sub>0} \<union> ?S \<subseteq> states'")
proof -
  have "?S \<subseteq> states'"
  proof clarsimp
    fix L s
    assume "(L, s) \<in> ?S"
    then have "L \<in> states"
      using state_set_states[unfolded trans_of_prod state_set_eq] by blast
    moreover have "bounded bounds s"
      using \<open>(L, s) \<in> _\<close>
      unfolding state_set_def
      unfolding trans_prod_def
      unfolding trans_int_def trans_bin_def trans_broad_def
      by auto
    ultimately show "(L, s) \<in> states'"
      by (auto simp: states'_alt_def)
  qed
  then show ?thesis
    by simp
qed



definition "k_i \<equiv> IArray (map (IArray o (map (IArray o map int))) k)"

definition
  "k_impl \<equiv> \<lambda>(l, _). IArray (map (\<lambda> c. Max {k_i !! i !! (l ! i) !! c | i. i < n_ps}) [0..<m+1])"

(* XXX Duplication with UPPAAL_State_Networks_Impl_Refine *)
lemma Max_int_commute:
  "int (Max S) = Max (int ` S)" if "finite S" "S \<noteq> {}"
  apply (rule mono_Max_commute)
    apply rule
  using that by auto

lemma (in Simple_Network_Impl_nat) n_ps_gt_0: "n_ps > 0"
  using length_automata_eq_n_ps non_empty by auto

lemma statesD:
  "L ! i \<in> fst ` set (fst (snd (automata ! i)))
 \<or> L ! i \<in> (snd o snd o snd o snd o snd o snd) ` set (fst (snd (automata ! i)))"
  if "L \<in> states" "length L = n_ps" "i < n_ps"
  using that unfolding states_def
  apply auto
  apply -
  apply (elim allE impE, assumption)
  apply auto
   apply (force simp: mem_trans_N_iff)+
  done

lemma k_impl_k_fun:
  "k_impl (L, s) = IArray (map (k_fun (L, s)) [0..<m+1])" if "L \<in> states"
proof -
  define k_i2 where "k_i2 i c = k_i !! i !! (L ! i) !! c" for i c
  have k_i2_k: "k_i2 i c = k ! i ! (L ! i) ! c" if "i < n_ps" "c \<le> m" for i c
  proof -
    have "i < length k"
      by (simp add: k_length(1) that(1))
    moreover have "L ! i < length (k ! i)"
      using L_i_len[OF _ \<open>L \<in> states\<close>] k_length(2) \<open>i < n_ps\<close> by auto
    moreover have "c < length (k ! i ! (L ! i))"
      using k_length(3) \<open>c \<le> m\<close> \<open>i < length k\<close> \<open>L ! i < length (k ! i)\<close> by (auto dest: nth_mem)
    ultimately show ?thesis
      unfolding k_i2_def k_i_def by simp
  qed
  have k_impl_alt_def: "k_impl (L, s) = IArray (map (\<lambda> c. Max {k_i2 i c | i. i < n_ps}) [0..<m+1])"
    unfolding k_impl_def k_i2_def by auto
  (* XXX more general pattern? *)
  have Max_cong: "Max {f i | i. i < n_ps} = Max {g i | i. i < n_ps}"
    if "\<And> i. i < n_ps \<Longrightarrow> f i = g i" for f g :: "nat \<Rightarrow> int"
    by (rule arg_cong[where f = Max]) (force simp: that)
  from that n_ps_gt_0 show ?thesis
    unfolding k_impl_alt_def
    unfolding k_i2_def[symmetric]
    apply (clarsimp simp: k_fun_def k_i2_k cong: Max_cong)
    apply safe
    subgoal
      by (subst Max_int_commute; force simp: setcompr_eq_image image_comp comp_def)
    subgoal
      using k_0 L_i_len[OF _ \<open>L \<in> states\<close>] by (intro linorder_class.Max_eqI) auto
    subgoal
      by (subst Max_int_commute; force simp: setcompr_eq_image image_comp comp_def)
    done
qed


sublocale impl: Reachability_Problem_Impl
  where trans_fun = trans_from
  and inv_fun = inv_fun
  and F_fun = Fi
  and ceiling = k_impl
  and A = prod_ta
  and l\<^sub>0 = l\<^sub>0
  and l\<^sub>0i = l\<^sub>0i
  and F = "PR_CONST F"
  and n = m
  and k = k_fun
  and trans_impl = trans_impl
  and states' = states'
  and loc_rel = loc_rel
  apply standard

(* trans_from *)
  subgoal
    unfolding trans_of_prod by (rule trans_from_correct)

(* trans_impl *)
  subgoal
    apply (rule trans_from_refine)
    done

(* inv_fun *)
  subgoal
    unfolding trans_of_prod
    by (rule set_mp[OF _ inv_fun_inv_of'[where R = loc_rel and S = "{(s, s'). state_rel s' s}"]])
       (auto simp: loc_rel_def)

(* state set *)
  subgoal
    using states'_superset by simp

(* loc_rel l\<^sub>0 l\<^sub>0i*)
  subgoal
    using state_rel_start unfolding loc_rel_def by auto

(* loc_rel left unique *)
  subgoal for l li li'
    unfolding trans_of_prod by (rule state_rel_left_unique)

(* loc_rel right unique *)
  subgoal for l l' li
    unfolding trans_of_prod by (rule state_rel_right_unique)

(* ceiling *)
  subgoal
    unfolding inv_rel_def using L\<^sub>0_states
    by (auto simp: loc_rel_def state_rel_def reach.k'_def k_fun_def k_impl_k_fun)

(* F_fun *)
  subgoal
    unfolding inv_rel_def by (clarsimp dest!: F_Fi)

  done

end (* Simple_Network_Impl_nat_ceiling_start_state *)

no_notation UPPAAL_Model_Checking.models ("_,_ \<Turnstile>\<^sub>_ _" [61,61] 61)


context Reachability_Problem_Impl
begin

lemma F_reachable_correct:
  "op.F_reachable
  \<longleftrightarrow> (\<exists>l'. \<forall>u\<^sub>0. (\<forall>c \<in> {1..n}. u\<^sub>0 c = 0) \<longrightarrow> (\<exists> u'. conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<^sub>0\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> F l'))"
  using E_op''.E_from_op_reachability_check[symmetric] reachability_check_new
  unfolding E_op_F_reachable E_op''.F_reachable_def E_op''.reachable_def
  unfolding F_rel_def by auto

lemma E_op''_F_reachable_correct:
  "E_op''.F_reachable
  \<longleftrightarrow> (\<exists>l'. \<forall>u\<^sub>0. (\<forall>c \<in> {1..n}. u\<^sub>0 c = 0) \<longrightarrow> (\<exists> u'. conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<^sub>0\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> F l'))"
  using E_op''.E_from_op_reachability_check[symmetric] reachability_check_new
  unfolding E_op_F_reachable E_op''.F_reachable_def E_op''.reachable_def
  unfolding F_rel_def by auto

lemma Ex_ev_impl_hnr:
  assumes "\<forall>u\<^sub>0. (\<forall>c \<in> {1..n}. u\<^sub>0 c = 0) \<longrightarrow> \<not> deadlock (l\<^sub>0, u\<^sub>0)"
  shows
    "
  (uncurry0
    (pw_impl (return \<circ> fst) state_copy_impl tracei subsumes_impl a\<^sub>0_impl F_impl succs_impl
      emptiness_check_impl),
   uncurry0 (SPEC (\<lambda>r. (r \<longleftrightarrow> (\<forall>u\<^sub>0. (\<forall>c \<in> {1..n}. u\<^sub>0 c = 0) \<longrightarrow> Ex_ev (\<lambda>(l, _). F l) (l\<^sub>0, u\<^sub>0))))))
  \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
proof -
  interpret Bisimulation_Invariant
    "(\<lambda>(l, u) (l', u'). conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)"
    "(\<lambda>(l, u) (l', u'). conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)"
    "(\<lambda>(l, u) (l', u'). l' = l \<and> (\<forall> c. c \<in> clk_set (conv_A A) \<longrightarrow> u c = u' c))"
    "(\<lambda>_. True)" "(\<lambda>_. True)"
    apply (rule ta_bisimulation)
    done
  define spec where "spec = (\<forall>u\<^sub>0. (\<forall>c \<in> {1..n}. u\<^sub>0 c = 0) \<longrightarrow> Ex_ev (\<lambda>(l, _). F l) (l\<^sub>0, u\<^sub>0))"
  have *: "E_op''.F_reachable \<longleftrightarrow> spec"
    unfolding spec_def
    unfolding E_op''_F_reachable_correct
  proof safe
    fix l' :: \<open>'s\<close> and u\<^sub>0 :: \<open>nat \<Rightarrow> real\<close>
    assume
      \<open>\<forall>u\<^sub>0. (\<forall>c\<in>{1..n}. u\<^sub>0 c = 0) \<longrightarrow> (\<exists>u'. conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<^sub>0\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> F l')\<close> and
      \<open>\<forall>c\<in>{1..n}. u\<^sub>0 c = 0\<close>
    then show \<open>Ex_ev (\<lambda>(l, _). F l) (l\<^sub>0, u\<^sub>0)\<close>
      using assms by (subst Ex_ev; unfold reaches_steps'[symmetric]) blast+
  next
    assume \<open>\<forall>u\<^sub>0. (\<forall>c\<in>{1..n}. u\<^sub>0 c = 0) \<longrightarrow> Ex_ev (\<lambda>(l, _). F l) (l\<^sub>0, u\<^sub>0)\<close>
    then have "Ex_ev (\<lambda>(l, _). F l) (l\<^sub>0, \<lambda>_. 0)"
      by auto
    then obtain l' u' where "conv_A A \<turnstile>' \<langle>l\<^sub>0, (\<lambda>_. 0)\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> F l'"
      apply (subst (asm) Ex_ev)
      using assms
      unfolding reaches_steps'[symmetric]
      by auto
    then show \<open>\<exists>l'. \<forall>u\<^sub>0. (\<forall>c\<in>{1..n}. u\<^sub>0 c = 0) \<longrightarrow> (\<exists>u'. conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<^sub>0\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> F l')\<close>
    proof (inst_existentials l', clarsimp, unfold reaches_steps'[symmetric])
      fix u\<^sub>0 :: \<open>nat \<Rightarrow> real\<close>
      assume \<open>reaches (l\<^sub>0, \<lambda>_. 0) (l', u')\<close> and \<open>F l'\<close> and \<open>\<forall>c\<in>{Suc 0..n}. u\<^sub>0 c = 0\<close>
      then have "equiv' (l\<^sub>0, \<lambda>_. 0) (l\<^sub>0, u\<^sub>0)"
        unfolding equiv'_def using clocks_I[of "\<lambda>_. 0" u\<^sub>0] by auto
      with \<open>reaches _ _\<close> show \<open>\<exists>u'. reaches (l\<^sub>0, u\<^sub>0) (l', u')\<close>
        by - (drule (1) bisim.A_B.simulation_reaches, unfold equiv'_def, auto)
    qed
  qed
  show ?thesis
    unfolding spec_def[symmetric] using pw_impl_hnr_F_reachable[to_hnr, unfolded hn_refine_def]
    by sepref_to_hoare (sep_auto simp: *)
qed

end (* Reachability Problem Impl *)











context Simple_Network_Impl_nat
begin



abbreviation "A \<equiv> (set broadcast, map automaton_of automata, map_of bounds')"

interpretation conv_eq_bisim:
  Bisimulation_Invariant
  "(\<lambda>(l, u) (l', u'). conv_A prod_ta \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)"
  "(\<lambda>(L, s, u) (L', s', u'). conv.prod_ta   \<turnstile>' \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L', s'), u'\<rangle>)"
  "(\<lambda>((L, s), u) (L', s', u'). L = L' \<and> u = u' \<and> s = s')"
  "(\<lambda>((L, s), u). conv.all_prop L s)"
  "(\<lambda>(L, s, u). conv.all_prop L s)"
proof goal_cases
  case 1
  interpret Bisimulation_Invariant
  "(\<lambda>(L, s, u) (L', s', u'). conv_A prod_ta \<turnstile>' \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L', s'), u'\<rangle>)"
  "(\<lambda>(L, s, u) (L', s', u'). conv.prod_ta   \<turnstile>' \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L', s'), u'\<rangle>)"
  "(=)"
  "(\<lambda>(L, s, u). conv.all_prop L s)"
  "(\<lambda>(L, s, u). conv.all_prop L s)"
  by (rule Bisimulation_Invariant_strong_intro)
     (auto simp: conv_prod_ta elim: conv.prod_all_prop_inv')
  show ?case
    by standard (auto simp: conv_prod_ta elim: conv.prod_all_prop_inv')
qed

interpretation Bisimulation_Invariant
  "(\<lambda>(l, u) (l', u'). conv_A prod_ta \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)"
  "(\<lambda>(L, s, u) (L', s', u'). Simple_Network_Language.conv A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)"
  "(\<lambda>((L, s), u) (L', s', u'). L = L' \<and> u = u' \<and> s = s')"
  "(\<lambda>((L, s), u). conv.all_prop L s)"
  "(\<lambda>(L, s, u). conv.all_prop L s)"
  unfolding conv_alt_def
  apply (rule Bisimulation_Invariant_sim_replace, rule Bisimulation_Invariant_composition)
    apply (rule conv_eq_bisim.Bisimulation_Invariant_axioms conv.prod_bisim_intro)+
  apply auto
  done

lemmas prod_bisim = Bisimulation_Invariant_axioms

lemmas deadlock_iff = deadlock_iff

lemma conv_all_prop:
  "conv.all_prop = all_prop"
  unfolding conv.all_prop_def all_prop_def by simp

lemma models_correct:
  "Simple_Network_Language.conv A,(L\<^sub>0, s\<^sub>0, u\<^sub>0) \<Turnstile> \<Phi> = (case \<Phi> of
    formula.EX \<phi> \<Rightarrow>
      Graph_Defs.Ex_ev
        (\<lambda> (l, u) (l', u'). conv_A prod_ta \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)
        (\<lambda> ((L, s), _). check_sexp \<phi> L (the o s))
  | formula.EG \<phi> \<Rightarrow>
      Not o Graph_Defs.Alw_ev
        (\<lambda> (l, u) (l', u'). conv_A prod_ta \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)
        (\<lambda> ((L, s), _). \<not> check_sexp \<phi> L (the o s))
  | formula.AX \<phi> \<Rightarrow>
      Graph_Defs.Alw_ev
        (\<lambda> (l, u) (l', u'). conv_A prod_ta \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)
        (\<lambda> ((L, s), _). check_sexp \<phi> L (the o s))
  | formula.AG \<phi> \<Rightarrow>
      Not o Graph_Defs.Ex_ev
        (\<lambda> (l, u) (l', u'). conv_A prod_ta \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)
        (\<lambda> ((L, s), _). \<not> check_sexp \<phi> L (the o s))
  | formula.Leadsto \<phi> \<psi> \<Rightarrow>
      Graph_Defs.leadsto
        (\<lambda> (l, u) (l', u'). conv_A prod_ta \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)
        (\<lambda> ((L, s), _). check_sexp \<phi> L (the o s))
        (\<lambda> ((L, s), _). check_sexp \<psi> L (the o s))
  ) ((L\<^sub>0, s\<^sub>0), u\<^sub>0)
  " if "L\<^sub>0 \<in> states" "Simple_Network_Language.bounded bounds s\<^sub>0"
proof -
  have all_prop_start[intro]:
  "conv.all_prop L\<^sub>0 s\<^sub>0"
  unfolding conv_all_prop all_prop_def using that ..

  have *: "((Not \<circ>\<circ> case_prod) (\<lambda>(L, s) _. check_sexp \<phi> L (the o s)))
    = (\<lambda>((L, s), _). \<not> check_sexp \<phi> L (the o s))"
    for \<phi> by (auto simp: comp_def)

  show ?thesis
    unfolding models_def
    apply (cases \<Phi>)

    subgoal for \<phi>
      by (auto intro!: Ex_ev_iff[symmetric, unfolded A_B.equiv'_def])
    subgoal for \<phi>
      apply simp
      apply (subst Ex_alw_iff[symmetric,
            where a = "((L\<^sub>0, s\<^sub>0), u\<^sub>0)" and \<phi> = "\<lambda>((L, s), _). check_sexp \<phi> L (the o s)"])
        apply (unfold A_B.equiv'_def, auto simp: Graph_Defs.Ex_alw_iff *)
      done
    subgoal for \<phi>
      apply (auto intro!: Alw_ev_iff[symmetric, unfolded A_B.equiv'_def])
      done
    subgoal for \<phi>
      apply simp
        (* XXX Rename Alw_alw_iff_strong in CTL *)
      apply (subst Alw_alw_iff_strong[symmetric,
            where a = "((L\<^sub>0, s\<^sub>0), u\<^sub>0)" and \<phi> = "\<lambda>((L, s), _). check_sexp \<phi> L (the o s)"])
        apply (unfold A_B.equiv'_def, auto simp: Graph_Defs.Alw_alw_iff *)
      done
    subgoal for \<phi> \<psi>
      apply simp
      apply (rule Leadsto_iff[symmetric])
        apply (unfold A_B.equiv'_def, auto)
      done
    done
qed

end (* Simple_Network_Impl_nat *)

context Simple_Network_Impl_nat_ceiling_start_state
begin

definition Alw_ev_checker where
  "Alw_ev_checker = dfs_map_impl'
     (impl.succs_P_impl' Fi) impl.a\<^sub>0_impl impl.subsumes_impl (return \<circ> fst)
     impl.state_copy_impl"

definition leadsto_checker where
  "leadsto_checker \<psi> = do {
      r \<leftarrow> leadsto_impl
      impl.state_copy_impl (impl.succs_P_impl' (\<lambda> (L, s). \<not> check_sexpi \<psi> L s))
      impl.a\<^sub>0_impl impl.subsumes_impl (return \<circ> fst)
      impl.succs_impl' impl.emptiness_check_impl impl.F_impl
      (impl.Q_impl (\<lambda> (L, s). \<not> check_sexpi \<psi> L s))
      impl.tracei;
      return (\<not> r)
    }"

definition
  "reachability_checker \<equiv>
     pw_impl
      (return o fst) impl.state_copy_impl impl.tracei impl.subsumes_impl impl.a\<^sub>0_impl impl.F_impl
      impl.succs_impl impl.emptiness_check_impl"

definition model_checker where
  "model_checker = (
  case formula of
    formula.EX _ \<Rightarrow> reachability_checker |
    formula.AG _ \<Rightarrow> do {
      r \<leftarrow> reachability_checker;
      return (\<not> r)
    } |
    formula.AX _ \<Rightarrow> do {
      r \<leftarrow> if PR_CONST F l\<^sub>0
      then Alw_ev_checker
      else return False;
      return (\<not> r)
    } |
    formula.EG _ \<Rightarrow>
      if PR_CONST F l\<^sub>0
      then Alw_ev_checker
      else return False |
    formula.Leadsto _ \<psi> \<Rightarrow> leadsto_checker \<psi>
  )
  "

abbreviation "u\<^sub>0 \<equiv> (\<lambda> _. 0 :: real)"

lemma all_prop_start:
  "all_prop L\<^sub>0 (map_of s\<^sub>0)"
  using L\<^sub>0_states s\<^sub>0_bounded unfolding all_prop_def ..

lemma deadlock_start_iff:
  "Graph_Defs.deadlock
   (\<lambda>(L, s, u) (L', s', u'). Simple_Network_Language.conv A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>) (L\<^sub>0, (map_of s\<^sub>0), u\<^sub>0)
  \<longleftrightarrow> reach.deadlock (l\<^sub>0, u\<^sub>0)"
  using all_prop_start by (subst deadlock_iff[symmetric]) (auto simp: conv_all_prop)

lemma F_Fi':
  "check_sexp \<psi> L (the o s) \<longleftrightarrow> check_sexpi \<psi> L' s'"
  if "((L', s'), (L, s)) \<in> loc_rel" "formula = Leadsto \<phi> \<psi>"
  using vars_of_formula that unfolding loc_rel_def by (auto elim!: check_sexp_check_sexpi)

theorem model_check':
  "(uncurry0 model_checker,
    uncurry0 (
      SPEC (\<lambda>r.
  \<not> Graph_Defs.deadlock
    (\<lambda>(L, s, u) (L', s', u').
      Simple_Network_Language.conv A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>) (L\<^sub>0, (map_of s\<^sub>0), u\<^sub>0)
      \<longrightarrow> r = (Simple_Network_Language.conv A,(L\<^sub>0, (map_of s\<^sub>0), u\<^sub>0) \<Turnstile> formula)
      )
    )
   )
  \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
proof -
  define protect where
    "protect = ((\<lambda>(l, u) (l', u'). conv_A prod_ta \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>))"

  have start: "l\<^sub>0 \<in> Normalized_Zone_Semantics_Impl_Refine.state_set trans_prod"
    if "\<not> Graph_Defs.deadlock protect (l\<^sub>0, \<lambda>_. 0)"
    using that unfolding protect_def by (rule impl.init_state_in_state_set[simplified])

  interpret ta_bisim: Bisimulation_Invariant
    "(\<lambda>(l, u) (l', u'). conv_A prod_ta \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)"
    "(\<lambda>(l, u) (l', u'). conv_A prod_ta \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)"
    "(\<lambda>(l, u) (l', u'). l' = l \<and> (\<forall> c. c \<in> clk_set (conv_A prod_ta) \<longrightarrow> u c = u' c))"
    "(\<lambda>_. True)" "(\<lambda>_. True)"
    by (rule ta_bisimulation[of "conv_A prod_ta"])

  let ?\<phi>1 = "\<lambda>\<phi>. \<lambda>(p, _). case p of (L, s) \<Rightarrow> \<not> check_sexp \<phi> L (the \<circ> s)"
  let ?\<phi>2 = "\<lambda>\<phi>. \<lambda>(p, _). case p of (L, s) \<Rightarrow> check_sexp \<phi> L (the \<circ> s)"

  have start_sim:
    "ta_bisim.A_B.equiv' (l\<^sub>0, u) (l\<^sub>0, \<lambda>_. 0)" "ta_bisim.A_B.equiv' (l\<^sub>0, \<lambda>_. 0) (l\<^sub>0, u)"
    if "\<forall>c\<in>{Suc 0..m}. u c = 0" for u
    using impl.clocks_I[of u "\<lambda>_. 0"] that unfolding ta_bisim.A_B.equiv'_def by auto

  have compatibleI: "\<phi> a = \<phi> b"
    if "ta_bisim.A_B.equiv' a b" "\<And> l u u'. \<phi> (l, u) = \<phi> (l, u')" for a b \<phi>
    using that unfolding ta_bisim.A_B.equiv'_def by auto

  have bisims:
    "(\<forall>u\<^sub>0. (\<forall>c\<in>{Suc 0..m}. u\<^sub>0 c = 0) \<longrightarrow> reach.Ex_ev (?\<phi>1 \<phi>) (l\<^sub>0, u\<^sub>0))
    \<longleftrightarrow> reach.Ex_ev (?\<phi>1 \<phi>) (l\<^sub>0, u\<^sub>0)"
    "(\<forall>u\<^sub>0. (\<forall>c\<in>{Suc 0..m}. u\<^sub>0 c = 0) \<longrightarrow> reach.Ex_ev (?\<phi>2 \<phi>) (l\<^sub>0, u\<^sub>0))
    \<longleftrightarrow> reach.Ex_ev (?\<phi>2 \<phi>) (l\<^sub>0, u\<^sub>0)"
    "(\<forall>u\<^sub>0. (\<forall>c\<in>{Suc 0..m}. u\<^sub>0 c = 0) \<longrightarrow> reach.Alw_ev (?\<phi>1 \<phi>) (l\<^sub>0, u\<^sub>0))
    \<longleftrightarrow> reach.Alw_ev (?\<phi>1 \<phi>) (l\<^sub>0, u\<^sub>0)"
    "(\<forall>u\<^sub>0. (\<forall>c\<in>{Suc 0..m}. u\<^sub>0 c = 0) \<longrightarrow> reach.Alw_ev (?\<phi>2 \<phi>) (l\<^sub>0, u\<^sub>0))
    \<longleftrightarrow> reach.Alw_ev (?\<phi>2 \<phi>) (l\<^sub>0, u\<^sub>0)"
    "(\<forall>u\<^sub>0. (\<forall>c\<in>{Suc 0..m}. u\<^sub>0 c = 0) \<longrightarrow> reach.leadsto (?\<phi>2 \<phi>) (?\<phi>2 \<psi>) (l\<^sub>0, u\<^sub>0))
    \<longleftrightarrow> reach.leadsto (?\<phi>2 \<phi>) (?\<phi>2 \<psi>) (l\<^sub>0, u\<^sub>0)"
    for \<phi> \<psi>
        apply auto
    subgoal for u
      using start_sim
      by (subst (asm) ta_bisim.Ex_ev_iff[of "?\<phi>1 \<phi>" "?\<phi>1 \<phi>"]) (erule compatibleI, auto)
    subgoal for u
      using start_sim
      by (subst (asm) ta_bisim.Ex_ev_iff[of "?\<phi>2 \<phi>" "?\<phi>2 \<phi>"]) (erule compatibleI, auto)
    subgoal for u
      using start_sim
      by (subst (asm) ta_bisim.Alw_ev_iff[of "?\<phi>1 \<phi>" "?\<phi>1 \<phi>"]) (erule compatibleI, auto)
    subgoal for u
      using start_sim
      by (subst (asm) ta_bisim.Alw_ev_iff[of "?\<phi>2 \<phi>" "?\<phi>2 \<phi>"]) (erule compatibleI, auto)
    subgoal for u
      using start_sim
      by (subst (asm) ta_bisim.Leadsto_iff[of "?\<phi>2 \<phi>" "?\<phi>2 \<phi>" "?\<phi>2 \<psi>" "?\<phi>2 \<psi>"])
        ((erule compatibleI)?; auto)+
    done

  have deadlock_bisim:
    "(\<forall>u\<^sub>0. (\<forall>c\<in>{1..m}. u\<^sub>0 c = 0) \<longrightarrow> \<not> reach.deadlock (l\<^sub>0, u\<^sub>0))
    \<longleftrightarrow> \<not> Graph_Defs.deadlock protect (l\<^sub>0, \<lambda>_. 0)"
    unfolding protect_def
    apply (safe; clarsimp)
    apply (drule start_sim(2))
    apply (subst (asm) ta_bisim.deadlock_iff)
    unfolding ta_bisim.A_B.equiv'_def
    by auto

  have *****:
    "return True = (return False \<bind> return o Not)"
    by auto

  show ?thesis
    unfolding deadlock_start_iff
    using models_correct[OF L\<^sub>0_states s\<^sub>0_bounded]
    unfolding protect_def[symmetric]
    apply (simp split del: if_split)
    apply sepref_to_hoare
    apply sep_auto
    unfolding model_checker_def Alw_ev_checker_def leadsto_checker_def reachability_checker_def
    apply (cases formula; simp)

    subgoal
      apply (cases "Graph_Defs.deadlock protect (l\<^sub>0, \<lambda>_. 0)")
      subgoal
        using impl.pw_impl_hnr_F_reachable[to_hnr, unfolded hn_refine_def]
        by (sep_auto elim!: cons_post_rule)
      subgoal
        using impl.Ex_ev_impl_hnr[unfolded deadlock_bisim, to_hnr, unfolded hn_refine_def]
        by (sep_auto simp: pure_def protect_def bisims)
      done

    subgoal premises prems for \<phi>
    proof -
      have *: "(\<lambda>(l, u). \<not> F l) = ((\<lambda>(p, _). case p of (L, s) \<Rightarrow> \<not> check_sexp \<phi> L (the \<circ> s)))"
        using prems by auto
      show ?thesis
        using impl.Alw_ev_impl_hnr[to_hnr, unfolded hn_refine_def] prems start
        unfolding PR_CONST_def * protect_def
        by (sep_auto elim!: cons_post_rule simp: pure_def bisims)
    qed

    subgoal premises prems for \<phi>
    proof -
      have *: "(\<lambda>(l, u). \<not> F l) = ((\<lambda>(p, _). case p of (L, s) \<Rightarrow> check_sexp \<phi> L (the \<circ> s)))"
        using prems by auto
      show ?thesis
        apply intros
        subgoal
          using impl.Alw_ev_impl_hnr[to_hnr, unfolded hn_refine_def] prems start
          unfolding PR_CONST_def * protect_def
          apply simp
          unfolding *****
          apply (erule bind_rule)
          apply (sep_auto simp: pure_def bisims(2-))
          done
        subgoal
          using impl.Alw_ev_impl_hnr[to_hnr, unfolded hn_refine_def] prems start
          unfolding PR_CONST_def * protect_def
          apply (sep_auto elim!: cons_post_rule simp: pure_def bisims(2-))
          done
        done
    qed

    subgoal
      apply (cases "Graph_Defs.deadlock protect (l\<^sub>0, \<lambda>_. 0)")
      subgoal
        using impl.pw_impl_hnr_F_reachable[to_hnr, unfolded hn_refine_def]
        by (sep_auto elim!: cons_post_rule)
      subgoal
        using impl.Ex_ev_impl_hnr[unfolded deadlock_bisim, to_hnr, unfolded hn_refine_def]
        apply (sep_auto simp: pure_def protect_def bisims)
        done
      done

    subgoal premises prems for \<phi> \<psi>
    proof -
      have *: "(\<lambda>(l, u). F l) = ((\<lambda>(p, _). case p of (L, s) \<Rightarrow> check_sexp \<phi> L (the \<circ> s)))"
        using prems by auto
      have **:"(\<lambda>(L, s). \<not> check_sexpi \<psi> L s, \<lambda>(L, s). \<not> check_sexp \<psi> L (the \<circ> s))
               \<in> inv_rel loc_rel states'"
        unfolding trans_of_prod using prems by (auto simp: F_Fi' inv_rel_def)
      have ****: "(\<lambda>(l, u). \<not> (case l of (L, s) \<Rightarrow> \<not> check_sexp \<psi> L (the \<circ> s)))
      = (\<lambda>(l, u). (case l of (L, s) \<Rightarrow> check_sexp \<psi> L (the \<circ> s)))"
        by auto
      show ?thesis
        apply (cases "reach.deadlock (l\<^sub>0, \<lambda>_. 0)")
        subgoal
          using impl.leadsto_impl_hnr'[OF **, to_hnr, unfolded hn_refine_def]
          unfolding protect_def \<open>formula = _\<close> by (sep_auto simp: pure_def)
        using impl.leadsto_impl_hnr[unfolded deadlock_bisim, to_hnr, unfolded hn_refine_def, OF **]
          prems start
        unfolding PR_CONST_def * protect_def by (sep_auto simp: pure_def bisims ****)
    qed
    done
qed


subsection \<open>Extracting an efficient implementation\<close>

lemma reachability_checker_alt_def':
  "reachability_checker \<equiv>
    do {
      x \<leftarrow> do {
        let key = return \<circ> fst;
        let sub = impl.subsumes_impl;
        let copy = impl.state_copy_impl;
        let start = impl.a\<^sub>0_impl;
        let final = impl.F_impl;
        let succs =  impl.succs_impl;
        let empty = impl.emptiness_check_impl;
        let trace = impl.tracei;
        pw_impl key copy trace sub start final succs empty
      };
      _ \<leftarrow> return ();
      return x
    }"
  unfolding reachability_checker_def by simp

lemma Alw_ev_checker_alt_def':
  "Alw_ev_checker \<equiv>
    do {
      x \<leftarrow> let
        key = return \<circ> fst;
        sub = impl.subsumes_impl;
        copy = impl.state_copy_impl;
        start = impl.a\<^sub>0_impl;
        succs =  impl.succs_P_impl' Fi
      in dfs_map_impl' succs start sub key copy;
      _ \<leftarrow> return ();
      return x
    }"
  unfolding Alw_ev_checker_def by simp

lemma leadsto_checker_alt_def':
  "leadsto_checker \<psi> \<equiv>
    do {
      r \<leftarrow> let
        key = return \<circ> fst;
        sub = impl.subsumes_impl;
        copy = impl.state_copy_impl;
        start = impl.a\<^sub>0_impl;
        final = impl.F_impl;
        final' = (impl.Q_impl (\<lambda>(L, s). \<not> check_sexpi \<psi> L s));
        succs =  impl.succs_P_impl' (\<lambda>(L, s). \<not> check_sexpi \<psi> L s);
        succs' =  impl.succs_impl';
        empty = impl.emptiness_check_impl;
        trace = impl.tracei
      in
        leadsto_impl copy succs start sub key succs' empty final final' trace;
      return (\<not> r)
    }"
  unfolding leadsto_checker_def by simp

theorem k_impl_alt_def:
  "k_impl = (\<lambda>(l, s). IArray (map (\<lambda>c. MAX i \<in> {0..<n_ps}. k_i !! i !! (l ! i) !! c) [0..<m + 1]))"
proof -
  have "{i. i < p} = {0..<p}" for p :: nat
    by auto
  then show ?thesis
    unfolding k_impl_def setcompr_eq_image by simp
qed

definition
  "trans_map_inner \<equiv> map (\<lambda>i. union_map_of (fst (snd (automata ! i)))) [0..<n_ps]"

lemma trans_map_alt_def:
  "trans_map = (\<lambda>i j. case (IArray trans_map_inner !! i) j of None \<Rightarrow> [] | Some xs \<Rightarrow> xs)"
  unfolding trans_map_inner_def trans_map_def
  apply auto
  apply (intro ext)
  subgoal for i j
    apply (cases "i < n_ps")
     apply (auto simp: n_ps_def)
    sorry
  done

schematic_goal succs_impl_alt_def:
  "impl.succs_impl \<equiv> ?impl"
  unfolding impl.succs_impl_def
  apply (abstract_let impl.E_op''_impl E_op''_impl)
  unfolding impl.E_op''_impl_def fw_impl'_int
  apply (abstract_let trans_impl trans_impl)
  unfolding trans_impl_def
  apply (abstract_let int_trans_impl int_trans_impl)
  apply (abstract_let bin_trans_from_impl bin_trans_impl)
  apply (abstract_let broad_trans_from_impl broad_trans_impl)
  unfolding int_trans_impl_def bin_trans_from_impl_def broad_trans_from_impl_def
  apply (abstract_let trans_in_broad_grouped trans_in_broad_grouped)
  apply (abstract_let trans_out_broad_grouped trans_out_broad_grouped)
  apply (abstract_let trans_in_map trans_in_map)
  apply (abstract_let trans_out_map trans_out_map)
  apply (abstract_let int_trans_from_all_impl int_trans_from_all_impl)
  unfolding int_trans_from_all_impl_def
  apply (abstract_let int_trans_from_vec_impl int_trans_from_vec_impl)
  unfolding int_trans_from_vec_impl_def
  apply (abstract_let int_trans_from_loc_impl int_trans_from_loc_impl)
  unfolding int_trans_from_loc_impl_def
  apply (abstract_let trans_i_map trans_i_map)
  unfolding trans_out_broad_grouped_def trans_out_broad_map_def
  unfolding trans_in_broad_grouped_def trans_in_broad_map_def
  unfolding trans_in_map_def trans_out_map_def
  unfolding trans_i_map_def
  apply (abstract_let trans_map trans_map)
  apply (abstract_let "inv_fun :: nat list \<times> int list \<Rightarrow> _" inv_fun)
  unfolding inv_fun_alt_def
  apply (abstract_let invs2 invs)
  unfolding invs2_def
  unfolding k_impl_alt_def
  apply (abstract_let k_i k_i) (* Could be killed *)
  apply (abstract_let n_ps n_ps)
  by (rule Pure.reflexive)

schematic_goal succs_P_impl_alt_def:
  "impl.succs_P_impl Pi \<equiv> ?impl"
  if "(Pi, P) \<in> inv_rel loc_rel states'"
  for P Pi
  unfolding impl.succs_P_impl_def[OF that]
  apply (abstract_let impl.E_op''_impl E_op''_impl)
  unfolding impl.E_op''_impl_def fw_impl'_int
  apply (abstract_let "trans_impl" trans_impl)
  unfolding trans_impl_def
  apply (abstract_let "int_trans_impl" int_trans_impl)
  apply (abstract_let "bin_trans_from_impl" bin_trans_impl)
  apply (abstract_let "broad_trans_from_impl" broad_trans_impl)
  unfolding int_trans_impl_def bin_trans_from_impl_def broad_trans_from_impl_def
  apply (abstract_let trans_in_broad_grouped trans_in_broad_grouped)
  apply (abstract_let trans_out_broad_grouped trans_out_broad_grouped)
  apply (abstract_let trans_in_map trans_in_map)
  apply (abstract_let trans_out_map trans_out_map)
  apply (abstract_let int_trans_from_all_impl int_trans_from_all_impl)
  unfolding int_trans_from_all_impl_def
  apply (abstract_let int_trans_from_vec_impl int_trans_from_vec_impl)
  unfolding int_trans_from_vec_impl_def
  apply (abstract_let int_trans_from_loc_impl int_trans_from_loc_impl)
  unfolding int_trans_from_loc_impl_def
  apply (abstract_let trans_i_map trans_i_map)
  unfolding trans_out_broad_grouped_def trans_out_broad_map_def
  unfolding trans_in_broad_grouped_def trans_in_broad_map_def
  unfolding trans_in_map_def trans_out_map_def
  unfolding trans_i_map_def
  apply (abstract_let trans_map trans_map)
  apply (abstract_let "inv_fun :: nat list \<times> int list \<Rightarrow> _" inv_fun)
  unfolding inv_fun_alt_def
  apply (abstract_let invs2 invs)
  unfolding invs2_def
  unfolding k_impl_alt_def
  apply (abstract_let k_i k_i) (* Could be killed *)
  apply (abstract_let n_ps n_ps)
  by (rule Pure.reflexive)


(* XXX These implementations contain unnecessary list reversals *)
lemmas succs_P'_impl_alt_def =
  impl.succs_P_impl'_def[OF impl.F_fun, unfolded succs_P_impl_alt_def[OF impl.F_fun]]

schematic_goal Alw_ev_checker_alt_def:
  "Alw_ev_checker \<equiv> ?impl"
  unfolding Alw_ev_checker_alt_def'
  unfolding succs_P'_impl_alt_def
  unfolding k_impl_alt_def k_i_def
  (* The following are just to unfold things that should have been defined in a defs locale *)
  unfolding impl.E_op''_impl_def impl.abstr_repair_impl_def impl.abstra_repair_impl_def
  unfolding
    impl.start_inv_check_impl_def impl.unbounded_dbm_impl_def
    impl.unbounded_dbm'_def
  unfolding impl.init_dbm_impl_def impl.a\<^sub>0_impl_def
  unfolding impl.F_impl_def
  unfolding impl.subsumes_impl_def
  unfolding impl.emptiness_check_impl_def
  unfolding impl.state_copy_impl_def
  by (rule Pure.reflexive)

lemma \<psi>_compatibleI:
  "(\<lambda>(L, s). \<not> check_sexpi \<psi> L s, \<lambda>(L, s). \<not> check_sexp \<psi> L (the \<circ> s)) \<in> inv_rel loc_rel states'"
  if "formula = Leadsto \<phi> \<psi>"
  using F_Fi'[OF _ that] unfolding inv_rel_def by auto

lemma Q_impl_alt_def:
  "impl.Q_impl (\<lambda>(L, s). \<not> check_sexpi \<psi> L s) \<equiv>
  \<lambda>xi. return (case xi of (a1, a2) \<Rightarrow> (\<lambda>(L, s). \<not> check_sexpi \<psi> L s) a1)"
  if "formula = Leadsto \<phi> \<psi>"
  by (intro impl.Q_impl_def[where Q = "\<lambda>(L, s). \<not> check_sexp \<psi> L (the o s)"] \<psi>_compatibleI[OF that])

schematic_goal leadsto_checker_alt_def:
  "leadsto_checker \<psi> \<equiv> ?impl" if "formula = Leadsto \<phi> \<psi>"
  unfolding leadsto_checker_alt_def'
  unfolding Q_impl_alt_def[OF that] impl.F_impl_def
  unfolding impl.succs_P_impl'_def[OF \<psi>_compatibleI[OF that]]
  unfolding succs_P_impl_alt_def[OF \<psi>_compatibleI[OF that]]
  unfolding impl.succs_impl'_def succs_impl_alt_def
  unfolding k_impl_alt_def k_i_def
  (* The following are just to unfold things that should have been defined in a defs locale *)
  unfolding impl.E_op''_impl_def impl.abstr_repair_impl_def impl.abstra_repair_impl_def
  unfolding
    impl.start_inv_check_impl_def impl.unbounded_dbm_impl_def
    impl.unbounded_dbm'_def
  unfolding impl.init_dbm_impl_def impl.a\<^sub>0_impl_def
  unfolding impl.F_impl_def
  unfolding impl.subsumes_impl_def
  unfolding impl.emptiness_check_impl_def
  unfolding impl.state_copy_impl_def
  by (rule Pure.reflexive)

schematic_goal reachability_checker_alt_def:
  "reachability_checker \<equiv> ?impl"
  unfolding reachability_checker_alt_def'
  unfolding succs_impl_alt_def
  unfolding k_impl_alt_def k_i_def
  (* The following are just to unfold things that should have been defined in a defs locale *)
  unfolding impl.E_op''_impl_def impl.abstr_repair_impl_def impl.abstra_repair_impl_def
  unfolding
    impl.start_inv_check_impl_def impl.unbounded_dbm_impl_def
    impl.unbounded_dbm'_def
  unfolding impl.init_dbm_impl_def impl.a\<^sub>0_impl_def
  unfolding impl.F_impl_def
  unfolding impl.subsumes_impl_def
  unfolding impl.emptiness_check_impl_def
  unfolding impl.state_copy_impl_def
  by (rule Pure.reflexive)

end (* Simple_Network_Impl_nat_ceiling_start_state *)

concrete_definition reachability_checker
  uses Simple_Network_Impl_nat_ceiling_start_state.reachability_checker_alt_def

concrete_definition Alw_ev_checker
  uses Simple_Network_Impl_nat_ceiling_start_state.Alw_ev_checker_alt_def

concrete_definition leadsto_checker
  uses Simple_Network_Impl_nat_ceiling_start_state.leadsto_checker_alt_def

context Simple_Network_Impl_nat_ceiling_start_state
begin

lemma model_checker_unfold_leadsto:
  "model_checker = (
  case formula of Simple_Network_Language_Model_Checking.formula.EX xa \<Rightarrow> reachability_checker
    | Simple_Network_Language_Model_Checking.formula.EG xa \<Rightarrow>
      if PR_CONST F l\<^sub>0 then Alw_ev_checker else return False
    | Simple_Network_Language_Model_Checking.formula.AX xa \<Rightarrow>
      (if PR_CONST F l\<^sub>0 then local.Alw_ev_checker else return False) \<bind> (\<lambda>r. return (\<not> r))
    | Simple_Network_Language_Model_Checking.formula.AG xa \<Rightarrow>
      reachability_checker \<bind> (\<lambda>r. return (\<not> r))
    | Simple_Network_Language_Model_Checking.formula.Leadsto \<phi> \<psi> \<Rightarrow>
      Simple_Network_Language_Model_Checking.leadsto_checker
        broadcast bounds' automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula \<psi> show_clock show_state)
"
  unfolding model_checker_def
  using leadsto_checker.refine[OF Simple_Network_Impl_nat_ceiling_start_state_axioms]
  by (simp split: formula.split)

lemmas model_checker_def_refined = model_checker_unfold_leadsto[unfolded
    reachability_checker.refine[OF Simple_Network_Impl_nat_ceiling_start_state_axioms]
    Alw_ev_checker.refine[OF Simple_Network_Impl_nat_ceiling_start_state_axioms]
  ]

end (* Simple_Network_Impl_nat_ceiling_start_state *)

concrete_definition model_checker uses
  Simple_Network_Impl_nat_ceiling_start_state.model_checker_def_refined

definition precond_mc where
  "precond_mc
    show_clock show_state broadcast bounds' automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula \<equiv>
    if Simple_Network_Impl_nat_ceiling_start_state
      broadcast bounds' automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula
    then
      model_checker
        broadcast bounds' automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula show_clock show_state
      \<bind> (\<lambda> x. return (Some x))
    else return None"


abbreviation N where
  "N broadcast automata bounds \<equiv>
  Simple_Network_Language.conv
    (set broadcast, map automaton_of automata, map_of bounds)"

definition has_deadlock where
  "has_deadlock A a\<^sub>0 \<equiv>
    Graph_Defs.deadlock (\<lambda> (L, s, u) (L', s', u'). A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>) a\<^sub>0"

theorem model_check:
  "<emp> precond_mc
    show_clock show_state broadcast bounds automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula
    <\<lambda> Some r \<Rightarrow> \<up>(
        Simple_Network_Impl_nat_ceiling_start_state
          broadcast bounds automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula \<and>
        (\<not> has_deadlock (N broadcast automata bounds) (L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<longrightarrow>
          r = N broadcast automata bounds,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<Turnstile> formula
        ))
     | None \<Rightarrow> \<up>(\<not> Simple_Network_Impl_nat_ceiling_start_state
        broadcast bounds automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula)
    >\<^sub>t"
proof -
  define A where "A \<equiv> N broadcast automata bounds"
  define check where "check \<equiv> A,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<Turnstile> formula"
  note [sep_heap_rules] =
    Simple_Network_Impl_nat_ceiling_start_state.model_check'[
      to_hnr, unfolded hn_refine_def,
      of broadcast bounds automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula,
      unfolded UPPAAL_Reachability_Problem_precompiled_defs.init_def,
      folded A_def check_def has_deadlock_def,
      simplified
      ]
  show ?thesis
    unfolding A_def[symmetric] check_def[symmetric]
    unfolding precond_mc_def
    by (sep_auto simp: model_checker.refine[symmetric] pure_def)
qed

end (* Theory *)
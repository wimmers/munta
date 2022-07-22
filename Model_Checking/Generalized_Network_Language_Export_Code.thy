subsection \<open>Code for the Model Checker Core\<close>
theory Generalized_Network_Language_Export_Code
  imports
    Generalized_Networks.Generalized_Network_Language_Renaming
    \<^cancel>\<open>Generalized_Networks.Generalized_Network_Language_Deadlock_Checking\<close>
    Shortest_SCC_Paths
    TA_Library.Error_List_Monad
begin

paragraph \<open>Checking Preconditions\<close>

abbreviation "renum_automaton \<equiv> Generalized_Network_Rename_Defs.renum_automaton"
abbreviation "renum_sync \<equiv> Generalized_Network_Rename_Defs.renum_sync"

locale Generalized_Network_Rename_Formula_String_Defs =
  Generalized_Network_Rename_Defs_int where automata = automata for automata ::
    "(String.literal list \<times> String.literal list \<times>
      (String.literal act, String.literal, String.literal, int, String.literal, int) transition list
      \<times> (String.literal \<times> (String.literal, int) cconstraint) list)
    list"
begin

definition check_renaming where "check_renaming urge \<Phi> L\<^sub>0 s\<^sub>0 \<equiv> combine [
    assert (\<forall>i<n_ps. \<forall>x\<in>loc_set. \<forall>y\<in>loc_set. renum_states i x = renum_states i y \<longrightarrow> x = y)
      STR ''Location renamings are injective'',
    assert (inj_on renum_clocks (insert urge clk_set'))
      STR ''Clock renaming is injective'',
    assert (inj_on renum_vars var_set)
      STR ''Variable renaming is injective'',
    assert (inj_on renum_acts act_set)
      STR ''Action renaming is injective'',
    assert (fst ` set bounds' = var_set)
      STR ''Bound set is exactly the variable set'',
    assert (\<Union> ((\<lambda>g. fst ` set g) ` set (map (snd o snd o snd) automata)) \<subseteq> loc_set)
      STR ''Invariant locations are contained in the location set'',
    assert (\<Union> ((set o fst) ` set automata) \<subseteq> loc_set)
      STR ''Broadcast locations are containted in the location set'',
    assert ((\<Union>x\<in>set automata. set (fst (snd x))) \<subseteq> loc_set)
      STR ''Urgent locations are containted in the location set'',
    assert (urge \<notin> clk_set')
      STR ''Urge not in clock set'',
    assert (L\<^sub>0 \<in> states)
      STR ''Initial location is in the state set'',
    assert (fst ` set s\<^sub>0 = var_set)
      STR ''Initial state has the correct domain'',
    assert (distinct (map fst s\<^sub>0))
      STR ''Initial state is unambiguous'',
    assert (set2_formula \<Phi> \<subseteq> loc_set)
      STR ''Formula locations are contained in the location set'',
    assert (locs_of_formula \<Phi> \<subseteq> {0..<n_ps})
      STR ''Formula automata are contained in the automata set'',
    assert (vars_of_formula \<Phi> \<subseteq> var_set)
      STR ''Variables of the formula are contained in the variable set''
  ]
"

end (* Generalized_Network_Rename_Formula_String_Defs *)

locale Generalized_Network_Rename_Formula_String =
  Generalized_Network_Rename_Formula_String_Defs +
  fixes urge :: String.literal
  fixes \<Phi> :: "(nat, String.literal, String.literal, int) formula"
    and s\<^sub>0 :: "(String.literal \<times> int) list"
    and L\<^sub>0 :: "String.literal list"
  assumes renum_states_inj:
    "\<forall>i<n_ps. \<forall>x\<in>loc_set. \<forall>y\<in>loc_set. renum_states i x = renum_states i y \<longrightarrow> x = y"
  and renum_clocks_inj: "inj_on renum_clocks (insert urge clk_set')"
  and renum_vars_inj:   "inj_on renum_vars var_set"
  and renum_acts_inj:   "inj_on renum_acts act_set"
  and bounds'_var_set:  "fst ` set bounds' = var_set"
  and loc_set_invs: "\<Union> ((\<lambda>g. fst ` set g) ` set (map (snd o snd o snd) automata)) \<subseteq> loc_set"
  and loc_set_syncs: "\<Union> ((set o fst) ` set automata) \<subseteq> loc_set"
  and loc_set_urgent: "\<Union> ((set o (fst o snd)) ` set automata) \<subseteq> loc_set"
  and urge_not_in_clk_set: "urge \<notin> clk_set'"
  assumes L\<^sub>0_states: "L\<^sub>0 \<in> states"
      and s\<^sub>0_dom: "fst ` set s\<^sub>0 = var_set" and s\<^sub>0_distinct: "distinct (map fst s\<^sub>0)"
  assumes formula_dom:
    "set2_formula \<Phi> \<subseteq> loc_set"
    "locs_of_formula \<Phi> \<subseteq> {0..<n_ps}"
    "vars_of_formula \<Phi> \<subseteq> var_set"
begin

interpretation Generalized_Network_Rename_Formula
  by (standard;
      rule renum_states_inj renum_clocks_inj renum_vars_inj bounds'_var_set renum_acts_inj
        loc_set_invs loc_set_syncs loc_set_urgent urge_not_in_clk_set
        infinite_literal infinite_UNIV_nat L\<^sub>0_states s\<^sub>0_dom s\<^sub>0_distinct formula_dom
     )+

lemmas Generalized_Network_Rename_intro = Generalized_Network_Rename_Formula_axioms

end

lemma is_result_assert_iff:
  "is_result (assert b m) \<longleftrightarrow> b"
  unfolding assert_def by auto

lemma is_result_combine_Cons_iff:
  "is_result (combine (x # xs)) \<longleftrightarrow> is_result x \<and> is_result (combine xs)"
  by (cases x; cases "combine xs") auto

lemma is_result_combine_iff:
  "is_result (a <|> b) \<longleftrightarrow> is_result a \<and> is_result b"
  by (cases a; cases b) (auto simp: combine2_def)

context Generalized_Network_Rename_Formula_String_Defs
begin

lemma check_renaming:
  "Generalized_Network_Rename_Formula_String
    syncs bounds'
    renum_acts renum_vars renum_clocks renum_states
    automata urge \<Phi> s\<^sub>0 L\<^sub>0 \<longleftrightarrow>
  is_result (check_renaming urge \<Phi> L\<^sub>0 s\<^sub>0)
  "
  unfolding check_renaming_def Generalized_Network_Rename_Formula_String_def
  by (simp add: is_result_combine_Cons_iff is_result_assert_iff del: combine.simps(2))

end

context Generalized_Network_Impl_nat_defs
begin

definition check_precond1 where
"check_precond1 =
  combine [
    assert (m > 0)
      (STR ''At least one clock''),
    assert (0 < length automata)
      (STR ''At least one automaton''),
    assert (\<forall>i<n_ps. let (_, _, trans, _) = (automata ! i) in \<forall> (l, _, _, _, _, _, l') \<in> set trans.
      l < num_states i \<and> l' < num_states i)
      (STR ''Number of states is correct (transitions)''),
    assert (\<forall>i < n_ps. let (_, _, _, inv) = (automata ! i) in \<forall> (x, _) \<in> set inv. x < num_states i)
      (STR ''Number of states is correct (invariants)''),
    assert (\<forall>(_, _, trans, _) \<in> set automata. \<forall>(_, _, _, _, f, _, _) \<in> set trans.
      \<forall>((x, upd), i) \<in> set f. x < n_vs \<and> (\<forall>i \<in> vars_of_exp upd. i < n_vs))
      (STR ''Variable set bounded (updates)''),
    assert (\<forall>(_, _, trans, _) \<in> set automata. \<forall>(_, b, _, _, _, _, _) \<in> set trans.
      \<forall>i \<in> vars_of_bexp b. i < n_vs)
      (STR ''Variable set bounded (guards)''),
    assert (\<forall> i < n_vs. fst (bounds' ! i) = i)
      (STR ''Bounds first index''),
    assert (\<forall>sync \<in> set syncs. \<forall>(p, a, b) \<in> set sync. p < length automata \<and> a < num_actions)
      (STR ''Synchronization vectors bounded''),
    assert (\<forall>(_, _, trans, _) \<in> set automata. \<forall>(_, _, _, a, _, _, _) \<in> set trans.
        pred_act (\<lambda>a. a < num_actions) a)
      (STR ''Actions bounded (transitions)''),
    assert (\<forall>sync \<in> set syncs. distinct (map fst sync))
      (STR ''Synchronization vectors processes distinct''),
    assert (\<forall>(_, _, trans, _) \<in> set automata. \<forall>(_, _, g, _, _, r, _) \<in> set trans.
      (\<forall>c \<in> set r. 0 < c \<and> c \<le> m) \<and>
      (\<forall> (c, x) \<in> collect_clock_pairs g. 0 < c \<and> c \<le> m \<and> x \<in> \<nat>))
      (STR ''Clock set bounded (transitions)''),
    assert (\<forall>(_, _, _, inv) \<in> set automata. \<forall>(l, g) \<in> set inv.
      (\<forall> (c, x) \<in> collect_clock_pairs g. 0 < c \<and> c \<le> m \<and> x \<in> \<nat>))
      (STR ''Clock set bounded (invariants)''),
    assert (\<forall>(_, _, trans, _) \<in> set automata. \<forall>(_, _, g, a, _, _, _) \<in> set trans. case a of
       Com a \<Rightarrow> \<forall>sync \<in> set syncs. \<forall>(p, a', b) \<in> set sync. \<not>b \<and> a = a' \<longrightarrow> g = []
      | _    \<Rightarrow> True)
      (STR ''Weak synchronization unguarded''),
    assert (\<forall>(_, U, _, _)\<in>set automata. U = [])
      STR ''Urgency was removed''
  ]
"

lemma check_precond1:
  "is_result check_precond1
  \<longleftrightarrow> Generalized_Network_Impl_nat_urge syncs bounds' automata m num_states num_actions"
  unfolding
    check_precond1_def
    Generalized_Network_Impl_nat_def Generalized_Network_Impl_nat_urge_def
    Generalized_Network_Impl_nat_urge_axioms_def
  by (simp add: is_result_combine_Cons_iff is_result_assert_iff del: combine.simps(2))

context
  fixes k :: "nat list list list"
    and L\<^sub>0 :: "nat list"
    and s\<^sub>0 :: "(nat \<times> int) list"
    and formula :: "(nat, nat, nat, int) formula"
begin

definition check_precond2 where
  "check_precond2 \<equiv>
  combine [
    assert (\<forall>i < n_ps. \<forall>(l, g) \<in> set ((snd o snd o snd) (automata ! i)).
      \<forall>(x, m) \<in> collect_clock_pairs g. m \<le> int (k ! i ! l ! x))
      (STR ''Ceiling invariants''),
    assert (\<forall>i < n_ps. \<forall>(l, _, g, _) \<in> set ((fst o snd o snd) (automata ! i)).
      (\<forall>(x, m) \<in> collect_clock_pairs g. m \<le> int (k ! i ! l ! x)))
      (STR ''Ceiling transitions''),
    assert (\<forall>i < n_ps. \<forall> (l, b, g, a, upd, r, l') \<in> set ((fst o snd o snd) (automata ! i)).
       \<forall>c \<in> {0..<m+1} - set r. k ! i ! l' ! c \<le> k ! i ! l ! c)
      (STR ''Ceiling resets''),
    assert (length k = n_ps)
      (STR ''Ceiling length''),
    assert (\<forall> i < n_ps. length (k ! i) = num_states i)
      (STR ''Ceiling length automata)''),
    assert (\<forall> xs \<in> set k. \<forall> xxs \<in> set xs. length xxs = m + 1)
      (STR ''Ceiling length clocks''),
    assert (\<forall>i < n_ps. \<forall>l < num_states i. k ! i ! l ! 0 = 0)
      (STR ''Ceiling zero clock''),
    assert (\<forall>(_, _, _, inv) \<in> set automata. distinct (map fst inv))
      (STR ''Unambiguous invariants''),
    assert (bounded bounds (map_of s\<^sub>0))
      (STR ''Initial state bounded''),
    assert (length L\<^sub>0 = n_ps)
      (STR ''Length of initial state''),
    assert (\<forall>i < n_ps. L\<^sub>0 ! i \<in> fst ` set ((fst o snd o snd) (automata ! i)))
      (STR ''Initial state has outgoing transitions''),
    assert (vars_of_formula formula \<subseteq> {0..<n_vs})
      (STR ''Variable set of formula'')
]"

lemma check_precond2:
  "is_result check_precond2 \<longleftrightarrow>
  Generalized_Network_Impl_nat_ceiling_start_state_axioms syncs bounds' automata m num_states
      k L\<^sub>0 s\<^sub>0 formula"
  unfolding check_precond2_def Generalized_Network_Impl_nat_ceiling_start_state_axioms_def
  by (simp add: is_result_combine_Cons_iff is_result_assert_iff del: combine.simps(2))

end

definition
  "check_precond k L\<^sub>0 s\<^sub>0 formula \<equiv> check_precond1 <|> check_precond2 k L\<^sub>0 s\<^sub>0 formula"

lemma check_precond:
  "Generalized_Network_Impl_nat_ceiling_start_state syncs bounds' automata m num_states
      num_actions k L\<^sub>0 s\<^sub>0 formula \<longleftrightarrow> is_result (check_precond k L\<^sub>0 s\<^sub>0 formula)"
  unfolding check_precond_def is_result_combine_iff check_precond1 check_precond2
    Generalized_Network_Impl_nat_ceiling_start_state_def
  ..

end


paragraph \<open>Show Utilities\<close>

derive "show" acconstraint act sexp formula

fun shows_exp and shows_bexp where
  "shows_exp (const c) = show c" |
  "shows_exp (var v) = show v" |
  "shows_exp (if_then_else b e1 e2) =
    shows_bexp b @ '' ? '' @ shows_exp e1 @ '' : '' @ shows_exp e2" |
  "shows_exp (binop _ e1 e2) = ''binop '' @ shows_exp e1 @ '' '' @ shows_exp e2" |
  "shows_exp (unop _ e) = ''unop '' @ shows_exp e" |
  "shows_bexp (bexp.lt a b) = shows_exp a @ '' < '' @ shows_exp b" |
  "shows_bexp (bexp.le a b) = shows_exp a @ '' <= '' @ shows_exp b" |
  "shows_bexp (bexp.eq a b) = shows_exp a @ '' = '' @ shows_exp b" |
  "shows_bexp (bexp.ge a b) = shows_exp a @ '' >= '' @ shows_exp b" |
  "shows_bexp (bexp.gt a b) = shows_exp a @ '' > '' @ shows_exp b" |
  "shows_bexp bexp.true = ''true''" |
  "shows_bexp (bexp.not b) = ''! '' @ shows_bexp b" |
  "shows_bexp (bexp.and a b) = shows_bexp a @ '' && '' @ shows_bexp b" |
  "shows_bexp (bexp.or a b) = shows_bexp a @ '' || '' @ shows_bexp b" |
  "shows_bexp (bexp.imply a b) = shows_bexp a @ '' -> '' @ shows_bexp b"

instantiation bexp :: ("show", "show") "show"
begin

definition "shows_prec p (e :: (_, _) bexp) rest = shows_bexp e @ rest" for p

definition "shows_list (es) s =
  map shows_bexp es |> intersperse '', '' |> (\<lambda>xs. ''['' @ concat xs @ '']'' @ s)"
instance
  by standard (simp_all add: shows_prec_bexp_def shows_list_bexp_def show_law_simps)

end

instantiation exp :: ("show", "show") "show"
begin

definition "shows_prec p (e :: (_, _) exp) rest = shows_exp e @ rest" for p

definition "shows_list (es) s =
  map shows_exp es |> intersperse '', '' |> (\<lambda>xs. ''['' @ concat xs @ '']'' @ s)"
instance
  by standard (simp_all add: shows_prec_exp_def shows_list_exp_def show_law_simps)

end

definition
  "show_clock inv_renum_clocks = show o inv_renum_clocks"

definition
  "show_locs inv_renum_states = show o map_index inv_renum_states"

definition
  "show_vars inv_renum_vars = show o map_index (\<lambda>i v. show (inv_renum_vars i) @ ''='' @ show v)"

definition
  "show_state inv_renum_states inv_renum_vars \<equiv> \<lambda>(L, vs).
  let L = show_locs inv_renum_states L; vs = show_vars inv_renum_vars vs in
  ''<'' @ L @ ''>, <'' @ vs @ ''>''"


definition rename_network where
  "rename_network syncs bounds' automata renum_acts renum_vars renum_clocks renum_states \<equiv>
  let
    automata = map_index (renum_automaton renum_acts renum_vars renum_clocks renum_states) automata;
    syncs = map (renum_sync renum_acts) syncs;
    bounds' = map (\<lambda>(a,b,c). (renum_vars a, b, c)) bounds'
  in
    (syncs, automata, bounds')
"

definition do_rename_mc where
  "do_rename_mc f dc syncs bounds' automata k urge L\<^sub>0 s\<^sub>0 formula
    m num_states num_actions renum_acts renum_vars renum_clocks renum_states
    inv_renum_states inv_renum_vars inv_renum_clocks
\<equiv>
let
   _ = println (STR ''Checking renaming'');
   formula = (if dc then formula.EX (not sexp.true) else formula);
   renaming_valid = Generalized_Network_Rename_Formula_String_Defs.check_renaming
      syncs bounds' renum_acts renum_vars renum_clocks renum_states automata urge formula L\<^sub>0 s\<^sub>0;
   _ = println (STR ''Renaming network'');
   (syncs, automata, bounds') = rename_network
      syncs bounds' (map (conv_urge urge) automata)
      renum_acts renum_vars renum_clocks renum_states;
   _ = trace_level 4 (\<lambda>_. return (STR ''Automata after renaming''));
   _ = map (\<lambda>a. show a |> String.implode |> (\<lambda>s. trace_level 4 (\<lambda>_. return s))) automata;
   _ = println (STR ''Renaming formula'');
   formula =
    (if dc then formula.EX (not sexp.true) else map_formula renum_states renum_vars id formula);
    _ = println (STR ''Renaming state'');
   L\<^sub>0 = map_index renum_states L\<^sub>0;
   s\<^sub>0 = map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0;
   show_clock = show o inv_renum_clocks;
   show_state = show_state inv_renum_states inv_renum_vars
in
  if is_result renaming_valid then do {
    let _ = println (STR ''Checking preconditions'');
    let r = Generalized_Network_Impl_nat_defs.check_precond
      syncs bounds' automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula;
    let _ = (case r of Result _ \<Rightarrow> ()
      | Error es \<Rightarrow>
        let
          _ = println STR '''';
          _ = println STR ''The following pre-conditions were not satisified:''
        in
          let _ = map println es in println STR '''');
    let _ = println (STR ''Running precond_mc'');
    let r = f show_clock show_state
        syncs bounds' automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula;
    Some r
  }
  else do {
    let _ = println (STR ''The following conditions on the renaming were not satisfied:'');
    let _ = the_errors renaming_valid |> map println;
    None}
"

datatype result =
  Renaming_Failed | Preconds_Unsat | Sat | Unsat

definition rename_mc where
  "rename_mc dc syncs bounds' automata k urge L\<^sub>0 s\<^sub>0 formula
    m num_states num_actions renum_acts renum_vars renum_clocks renum_states
    inv_renum_states inv_renum_vars inv_renum_clocks
\<equiv>
do {
  \<^cancel>\<open>let r = do_rename_mc (if dc then precond_dc else precond_mc)\<close>
  let r = do_rename_mc (if dc then precond_mc else precond_mc)
    dc syncs bounds' automata k urge L\<^sub>0 s\<^sub>0 formula
    m num_states num_actions renum_acts renum_vars renum_clocks renum_states
    inv_renum_states inv_renum_vars inv_renum_clocks;
  case r of Some r \<Rightarrow> do {
    r \<leftarrow> r;
    case r of
      None \<Rightarrow> return Preconds_Unsat
    | Some False \<Rightarrow> return Unsat
    | Some True \<Rightarrow> return Sat
  }
  | None \<Rightarrow> return Renaming_Failed
}
"


paragraph \<open>Main Correctness Theorems\<close>

theorem model_check_rename:
  "<emp> rename_mc False syncs bounds automata k urge L\<^sub>0 s\<^sub>0 formula
    m num_states num_actions renum_acts renum_vars renum_clocks renum_states
    inv_renum_states inv_renum_vars inv_renum_clocks
    <\<lambda> Sat \<Rightarrow> \<up>(
        (\<not> has_deadlock (N syncs automata bounds) (L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<longrightarrow>
          N syncs automata bounds,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<Turnstile> formula
        ))
     | Unsat \<Rightarrow> \<up>(
        (\<not> has_deadlock (N syncs automata bounds) (L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<longrightarrow>
          \<not> N syncs automata bounds,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<Turnstile> formula
        ))
     | Renaming_Failed \<Rightarrow> \<up>(\<not> Generalized_Network_Rename_Formula
        syncs bounds renum_acts renum_vars renum_clocks renum_states urge s\<^sub>0 L\<^sub>0 automata formula)
     | Preconds_Unsat \<Rightarrow> \<up>(\<not> Generalized_Network_Impl_nat_ceiling_start_state
        (map (renum_sync renum_acts) syncs)
        (map (\<lambda>(a,p). (renum_vars a, p)) bounds)
        (map_index (renum_automaton renum_acts renum_vars renum_clocks renum_states)
          (map (conv_urge urge) automata))
        m num_states num_actions k
        (map_index renum_states L\<^sub>0) (map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0)
        (map_formula renum_states renum_vars id formula))
    >\<^sub>t"
proof -
  have *: "
    Generalized_Network_Rename_Formula_String
        syncs bounds renum_acts renum_vars renum_clocks renum_states automata urge formula s\<^sub>0 L\<^sub>0
  = Generalized_Network_Rename_Formula
        syncs bounds renum_acts renum_vars renum_clocks renum_states urge s\<^sub>0 L\<^sub>0 automata formula
  "
    unfolding
      Generalized_Network_Rename_Formula_String_def Generalized_Network_Rename_Formula_def
      Generalized_Network_Rename_Start_def Generalized_Network_Rename_Start_axioms_def
      Generalized_Network_Rename_def Generalized_Network_Rename_Formula_axioms_def
    using infinite_literal by auto
  define A where "A \<equiv> N syncs automata bounds"
  define check where "check \<equiv> A,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<Turnstile> formula"
  define A' where "A' \<equiv> N
    (map (renum_sync renum_acts) syncs)
    (map_index (renum_automaton renum_acts renum_vars renum_clocks renum_states)
      (map (conv_urge urge) automata))
    (map (\<lambda>(a,p). (renum_vars a, p)) bounds)"
  define check' where "check' \<equiv>
    A',(map_index renum_states L\<^sub>0, map_of (map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0), \<lambda>_ . 0) \<Turnstile>
    map_formula renum_states renum_vars id formula"
  define preconds_sat where "preconds_sat \<equiv>
    Generalized_Network_Impl_nat_ceiling_start_state
      (map (renum_sync renum_acts) syncs)
      (map (\<lambda>(a,p). (renum_vars a, p)) bounds)
      (map_index (renum_automaton renum_acts renum_vars renum_clocks renum_states)
        (map (conv_urge urge) automata))
      m num_states num_actions k
      (map_index renum_states L\<^sub>0) (map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0)
      (map_formula renum_states renum_vars id formula)"
  define renaming_valid where "renaming_valid \<equiv>
    Generalized_Network_Rename_Formula
      syncs bounds renum_acts renum_vars renum_clocks renum_states urge s\<^sub>0 L\<^sub>0 automata formula
  "
  have [simp]: "check \<longleftrightarrow> check'" 
    if renaming_valid
    using that unfolding check_def check'_def A_def A'_def renaming_valid_def
    by (rule Generalized_Network_Rename_Formula.models_iff'[symmetric])
  have test[symmetric, simp]:
    "Generalized_Network_Language_Model_Checking.has_deadlock A (L\<^sub>0, map_of s\<^sub>0, \<lambda>_. 0)
  \<longleftrightarrow>Generalized_Network_Language_Model_Checking.has_deadlock A'
     (map_index renum_states L\<^sub>0, map_of (map (\<lambda>(x, y). (renum_vars x, y)) s\<^sub>0), \<lambda>_. 0)
  " if renaming_valid
    using that unfolding check_def check'_def A_def A'_def renaming_valid_def
    unfolding Generalized_Network_Rename_Formula_def
    by (elim conjE) (rule Generalized_Network_Rename_Start.has_deadlock_iff'[symmetric])
  note [sep_heap_rules] =
    model_check[
    of _ _
    "map (renum_sync renum_acts) syncs" "map (\<lambda>(a,p). (renum_vars a, p)) bounds"
    "map_index (renum_automaton renum_acts renum_vars renum_clocks renum_states)
      (map (conv_urge urge) automata)"
    m num_states num_actions k "map_index renum_states L\<^sub>0" "map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0"
    "map_formula renum_states renum_vars id formula",
    folded A'_def preconds_sat_def renaming_valid_def, folded check'_def, simplified
    ]
  show ?thesis
    unfolding rename_mc_def do_rename_mc_def rename_network_def
    unfolding if_False
    unfolding Generalized_Network_Rename_Formula_String_Defs.check_renaming[symmetric] * Let_def
    unfolding
      A_def[symmetric] check_def[symmetric]
      preconds_sat_def[symmetric] renaming_valid_def[symmetric]
    by (sep_auto simp: model_checker.refine[symmetric] split: bool.splits)
qed

\<^cancel>\<open>theorem deadlock_check_rename:
  "<emp> rename_mc True syncs bounds automata k urge L\<^sub>0 s\<^sub>0 formula
    m num_states num_actions renum_acts renum_vars renum_clocks renum_states
    inv_renum_states inv_renum_vars inv_renum_clocks
    <\<lambda> Sat   \<Rightarrow> \<up>(  has_deadlock (N syncs automata bounds) (L\<^sub>0, map_of s\<^sub>0, \<lambda>_.  0))
     | Unsat \<Rightarrow> \<up>(\<not> has_deadlock (N syncs automata bounds) (L\<^sub>0, map_of s\<^sub>0, \<lambda>_. 0))
     | Renaming_Failed \<Rightarrow> \<up>(\<not> Generalized_Network_Rename_Formula
        syncs bounds renum_acts renum_vars renum_clocks renum_states urge s\<^sub>0 L\<^sub>0 automata
        (formula.EX (not sexp.true)))
     | Preconds_Unsat \<Rightarrow> \<up>(\<not> Generalized_Network_Impl_nat_ceiling_start_state
        (map renum_acts syncs)
        (map (\<lambda>(a,p). (renum_vars a, p)) bounds)
        (map_index (renum_automaton renum_acts renum_vars renum_clocks renum_states)
          (map (conv_urge urge) automata))
        m num_states num_actions k
        (map_index renum_states L\<^sub>0) (map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0)
        (formula.EX (not sexp.true)))
    >\<^sub>t"
proof -
  have *: "
    Generalized_Network_Rename_Formula_String
        syncs bounds renum_acts renum_vars renum_clocks renum_states automata urge
        (formula.EX (not sexp.true)) s\<^sub>0 L\<^sub>0
  = Generalized_Network_Rename_Formula
        syncs bounds renum_acts renum_vars renum_clocks renum_states urge s\<^sub>0 L\<^sub>0 automata
        (formula.EX (not sexp.true))
  "
    unfolding
      Generalized_Network_Rename_Formula_String_def Generalized_Network_Rename_Formula_def
      Generalized_Network_Rename_Start_def Generalized_Network_Rename_Start_axioms_def
      Generalized_Network_Rename_def Generalized_Network_Rename_Formula_axioms_def
    using infinite_literal by auto
  define A where "A \<equiv> N syncs automata bounds"
  define A' where "A' \<equiv> N
    (map renum_acts syncs)
    (map_index (renum_automaton renum_acts renum_vars renum_clocks renum_states)
      (map (conv_urge urge) automata))
    (map (\<lambda>(a,p). (renum_vars a, p)) bounds)"
  define preconds_sat where "preconds_sat \<equiv>
    Generalized_Network_Impl_nat_ceiling_start_state
      (map renum_acts syncs)
      (map (\<lambda>(a,p). (renum_vars a, p)) bounds)
      (map_index (renum_automaton renum_acts renum_vars renum_clocks renum_states)
        (map (conv_urge urge) automata))
      m num_states num_actions k
      (map_index renum_states L\<^sub>0) (map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0)
      (formula.EX (not sexp.true))"
  define renaming_valid where "renaming_valid \<equiv>
    Generalized_Network_Rename_Formula
      syncs bounds renum_acts renum_vars renum_clocks renum_states urge s\<^sub>0 L\<^sub>0 automata
      (formula.EX (not sexp.true))"
 have test[symmetric, simp]:
    "Generalized_Network_Language_Model_Checking.has_deadlock A (L\<^sub>0, map_of s\<^sub>0, \<lambda>_. 0)
  \<longleftrightarrow>Generalized_Network_Language_Model_Checking.has_deadlock A'
     (map_index renum_states L\<^sub>0, map_of (map (\<lambda>(x, y). (renum_vars x, y)) s\<^sub>0), \<lambda>_. 0)
  " if renaming_valid
    using that unfolding check_def A_def A'_def renaming_valid_def Generalized_Network_Rename_Formula_def
    by (elim conjE) (rule Generalized_Network_Rename_Start.has_deadlock_iff'[symmetric])
  note [sep_heap_rules] =
    deadlock_check[
    of _ _
    "map renum_acts syncs" "map (\<lambda>(a,p). (renum_vars a, p)) bounds"
    "map_index (renum_automaton renum_acts renum_vars renum_clocks renum_states)
      (map (conv_urge urge) automata)"
    m num_states num_actions k "map_index renum_states L\<^sub>0" "map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0",
    folded preconds_sat_def A'_def renaming_valid_def,
    simplified
    ]
  show ?thesis
    unfolding rename_mc_def do_rename_mc_def  rename_network_def
    unfolding if_True
    unfolding Generalized_Network_Rename_Formula_String_Defs.check_renaming[symmetric] * Let_def
    unfolding A_def[symmetric] preconds_sat_def[symmetric] renaming_valid_def[symmetric]
    by (sep_auto simp: deadlock_checker.refine[symmetric] split: bool.splits)
qed\<close>


paragraph \<open>Code Setup for the Model Checker\<close>

lemmas [code] =
  reachability_checker_def
  Alw_ev_checker_def
  leadsto_checker_def
  model_checker_def[unfolded PR_CONST_def]

lemmas [code] =
  Prod_TA_Defs.n_ps_def
  Generalized_Network_Impl_Defs.n_vs_def
  automaton_of_def
  Generalized_Network_Impl_nat_defs.all_actions_from_vec_def
  Generalized_Network_Impl_nat_defs.all_actions_by_state_def
  Generalized_Network_Impl_nat_defs.actions_by_state_def
  Generalized_Network_Impl_nat_defs.check_boundedi_def
  Generalized_Network_Impl_nat_defs.get_committed_def
  Generalized_Network_Impl_nat_defs.make_combs_def
  Generalized_Network_Impl_nat_defs.trans_map_def
  Generalized_Network_Impl_nat_defs.actions_by_state'_def
  Generalized_Network_Impl_nat_defs.bounds_map_def
  mk_updsi_def
  Generalized_Network_Impl_nat_defs.select_trans_from_sync_def
  Generalized_Network_Impl_nat_defs.make_trans_from_combs_impl_def
  Generalized_Network_Impl_nat_defs.is_sync_enabled_committed_def
  Generalized_Network_Impl_nat_defs.make_combs_from_sync_def
  Generalized_Network_Impl_nat_defs.is_sync_enabled_def
  Generalized_Network_Impl_nat_defs.trans_com_map_def
  Generalized_Network_Language.act.pred_act_def

lemma (in Generalized_Network_Impl_nat_defs) bounded_s\<^sub>0_iff:
  "bounded bounds (map_of s\<^sub>0) \<longleftrightarrow> bounded (map_of bounds') (map_of s\<^sub>0)"
  unfolding bounds_def snd_conv ..

lemma int_Nat_range_iff:
  "(n :: int) \<in> \<nat> \<longleftrightarrow> n \<ge> 0" for n
  using zero_le_imp_eq_int unfolding Nats_def by auto

lemmas [code] =
  Generalized_Network_Impl_nat_ceiling_start_state_def
  Generalized_Network_Impl_nat_ceiling_start_state_axioms_def[
    unfolded Generalized_Network_Impl_nat_defs.bounded_s\<^sub>0_iff]
  Generalized_Network_Impl_nat_def[unfolded int_Nat_range_iff]
  Generalized_Network_Impl_nat_urge_def
  Generalized_Network_Impl_nat_urge_axioms_def

lemmas [code_unfold] = bounded_def dom_map_of_conv_image_fst

export_code Generalized_Network_Impl_nat_ceiling_start_state_axioms

export_code precond_mc in SML module_name Test

\<^cancel>\<open>export_code precond_dc checking SML\<close>


paragraph \<open>Code Setup for Renaming\<close>

lemmas [code] =
  Generalized_Network_Rename_Formula_String_def
  Generalized_Network_Impl.clk_set'_def
  Generalized_Network_Impl.clkp_set'_def

lemmas [code] =
  Generalized_Network_Rename_Defs.renum_automaton_def
  Generalized_Network_Rename_Defs.renum_sync_def
  Generalized_Network_Rename_Defs.renum_cconstraint_def
  Generalized_Network_Rename_Defs.map_cconstraint_def
  Generalized_Network_Rename_Defs.renum_reset_def
  Generalized_Network_Rename_Defs.renum_upd_def
  Generalized_Network_Rename_Defs.renum_act_def
  Generalized_Network_Rename_Defs.renum_exp_def
  Generalized_Network_Rename_Defs.renum_bexp_def
  Generalized_Network_Rename_Formula_String_Defs.check_renaming_def
  Generalized_Network_Impl_nat_defs.check_precond_def
  Generalized_Network_Impl_nat_defs.check_precond1_def[unfolded int_Nat_range_iff]
  Generalized_Network_Impl_nat_defs.check_precond2_def[
    unfolded Generalized_Network_Impl_nat_defs.bounded_s\<^sub>0_iff]

lemma (in Prod_TA_Defs) states_mem_iff:
  "L \<in> states \<longleftrightarrow> length L = n_ps \<and> (\<forall> i. i < n_ps \<longrightarrow>
    (\<exists> (l, b, g, a, r, u, l') \<in> fst (snd (snd (fst (snd A) ! i))). L ! i = l \<or> L ! i = l'))"
  unfolding states_def trans_def N_def by (auto split: prod.split)

lemmas [code_unfold] =
  Prod_TA_Defs.states_mem_iff
  Generalized_Network_Impl.act_set_compute
  Generalized_Network_Impl_Defs.var_set_compute
  Generalized_Network_Impl_Defs.loc_set_compute
  setcompr_eq_image
  Generalized_Network_Impl.length_automata_eq_n_ps[symmetric]

export_code rename_mc in SML module_name Test



paragraph \<open>Calculating the Clock Ceiling\<close>

context Generalized_Network_Impl_nat_defs
begin

definition "clkp_inv i l \<equiv>
  \<Union>g \<in> set (filter (\<lambda>(a, b). a = l) (snd (snd (snd (automata ! i))))). collect_clock_pairs (snd g)"

definition "clkp_set'' i l \<equiv>
    clkp_inv i l \<union> (\<Union> (l', b, g, _) \<in> set (fst (snd (snd (automata ! i)))).
      if l' = l then collect_clock_pairs g else {})"

definition
  "collect_resets i l = (\<Union> (l', b, g, a, f, r, _) \<in> set (fst (snd (snd (automata ! i)))).
    if l' = l then set r else {})"

context
  fixes q c :: nat
begin

  definition "n \<equiv> num_states q"

  definition "V \<equiv> \<lambda> v. v \<le> n"

  definition "
    bound_g l \<equiv>
      Max ({0} \<union> \<Union> ((\<lambda> (x, d). if x = c then {d} else {}) ` clkp_set'' q l))
    "

  definition "
    bound_inv l \<equiv>
      Max ({0} \<union> \<Union> ((\<lambda> (x, d). if x = c then {d} else {}) ` clkp_inv q l))
  "

  definition "
    bound l \<equiv> max (bound_g l) (bound_inv l)
  "

definition "
  resets l \<equiv>
    fold
    (\<lambda> (l1, b, g, a, f, r, l') xs. if l1 \<noteq> l \<or> l' \<in> set xs \<or> c \<in> set r then xs else (l' # xs))
    (fst (snd (snd (automata ! q))))
    []
"

text \<open>
  Edges in the direction nodes to single sink.
\<close>
definition "
  E' l \<equiv> resets l
"

text \<open>
  Turning around the edges to obtain a single source shortest paths problem.
\<close>
(* XXX Tune for efficiency *)
definition "
  E l \<equiv> if l = n then [0..<n] else filter (\<lambda> l'. l \<in> set (E' l')) [0..<n]
"

text \<open>
  Weights already turned around.
\<close>
definition "
  W l l' \<equiv> if l = n then - bound l' else 0
"

definition G where "
  G \<equiv> \<lparr> gi_V = V, gi_E = E, gi_V0 = [n], \<dots> = W \<rparr>
"

definition "
  local_ceiling_single \<equiv>
  let
    w = calc_shortest_scc_paths G n
  in
    map (\<lambda> x. case x of None \<Rightarrow> 0 | Some x \<Rightarrow> nat(-x)) w
"

end

definition "
  local_ceiling \<equiv>
    rev $
    fold
      (\<lambda> q xs.
        (\<lambda> x. rev x # xs) $
        fold
          (\<lambda> l xs.
            (\<lambda> x. (0 # rev x) # xs) $
            fold
              (\<lambda> c xs. local_ceiling_single q c ! l # xs)
              [1..<Suc m]
              []
          )
          [0..<n q]
          []
      )
      [0..<n_ps]
      []
"

end


lemmas [code] =
  Generalized_Network_Impl_nat_defs.local_ceiling_def
  Generalized_Network_Impl_nat_defs.local_ceiling_single_def
  Generalized_Network_Impl_nat_defs.n_def
  Generalized_Network_Impl_nat_defs.G_def
  Generalized_Network_Impl_nat_defs.W_def
  Generalized_Network_Impl_nat_defs.V_def
  Generalized_Network_Impl_nat_defs.E'_def
  Generalized_Network_Impl_nat_defs.E_def
  Generalized_Network_Impl_nat_defs.resets_def
  Generalized_Network_Impl_nat_defs.bound_def
  Generalized_Network_Impl_nat_defs.bound_inv_def
  Generalized_Network_Impl_nat_defs.bound_g_def
  Generalized_Network_Impl_nat_defs.collect_resets_def
  Generalized_Network_Impl_nat_defs.clkp_set''_def
  Generalized_Network_Impl_nat_defs.clkp_inv_def

export_code Generalized_Network_Impl_nat_defs.local_ceiling checking SML_imp



paragraph \<open>Calculating the Renaming\<close>

definition "mem_assoc x = list_ex (\<lambda>(y, _). x = y)"

definition failwith where
  "failwith msg \<equiv> let () = println msg in undefined"

definition "mk_renaming str xs \<equiv>
do {
  mapping \<leftarrow> fold_error
    (\<lambda>x m.
      if mem_assoc x m then Error [STR ''Duplicate name: '' + str x] else (x,length m) # m |> Result
    ) xs [];
  Result (let
    m = map_of mapping;
    f = (\<lambda>x.
      case m x of
        None \<Rightarrow> failwith (STR ''Key error: '' + str x)
      | Some v \<Rightarrow> v);
    m = map_of (map prod.swap mapping);
    f_inv = (\<lambda>x.
      case m x of
        None \<Rightarrow> failwith (STR ''Key error: '' + String.implode (show x))
      | Some v \<Rightarrow> v)
  in (f, f_inv)
  )
}"

definition
  "extend_domain m d n \<equiv>
    let
      (i, xs) = fold
        (\<lambda>x (i, xs). if x \<in> set d then (i + 1, (x, i + 1) # xs) else (i, xs)) d (n, []);
      m' = map_of xs
    in
      (\<lambda>x. if x \<in> set d then the (m' x) else m x)"

(* Unused *)
lemma [simp]:
  "is_result (make_err m e) \<longleftrightarrow> False"
  by (cases e) auto

(* Unused *)
lemma is_result_assert_msg_iff[simp]:
  "is_result (assert_msg b m r) \<longleftrightarrow> is_result r \<and> b"
  unfolding assert_msg_def by simp

(* Unused *)
lemma
  "is_result (e |> assert_msg b1 m |> assert_msg b2 m2) \<longleftrightarrow> is_result e \<and> b1 \<and> b2"
  by simp


context Generalized_Network_Impl
begin

definition action_set where
  "action_set \<equiv>
    (\<Union>(_, _, trans, _) \<in> set automata. \<Union>(_, _, _, a, _, _, _) \<in> set trans. set_act a)
    \<union> (\<Union>sync \<in> set syncs. (fst o snd) ` set sync)"

(* TODO Duplicated Definition. It seems that @{term action_set} is only used for computations. *)
lemma act_set_eq_action_set:
  "act_set = action_set"
  unfolding act_set_compute action_set_def by auto

definition loc_set' where
  "loc_set' p = (\<Union>(l, _, _, _, _, _, l')\<in>set (fst (snd (snd (automata ! p)))). {l, l'})" for p

end


definition
  "concat_str = String.implode o concat o map String.explode"


paragraph \<open>Unsafe Glue Code\<close>

definition list_of_set' :: "'a set \<Rightarrow> 'a list" where
  "list_of_set' xs = undefined"

definition list_of_set :: "'a set \<Rightarrow> 'a list" where
  "list_of_set xs = list_of_set' xs |> remdups"

\<comment> \<open>Note that this still guarantees partial correctness:\<close>
code_printing
  constant list_of_set' \<rightharpoonup> (SML) "(fn Set xs => xs) _"
       and              (OCaml) "(fun x -> match x with Set xs -> xs) _"



definition
  "mk_renaming' xs \<equiv> mk_renaming (String.implode o show) xs"

definition "make_renaming \<equiv> \<lambda> syncs automata bounds.
  let
    action_set = Generalized_Network_Impl.action_set automata syncs |> list_of_set;
    clk_set = Generalized_Network_Impl.clk_set' automata |> list_of_set;
    clk_set = clk_set @ [STR ''_urge''];
    loc_set' = (\<lambda>i. Generalized_Network_Impl.loc_set' automata i |> list_of_set);
    loc_set = Prod_TA_Defs.loc_set
      (set syncs, map automaton_of automata, map_of bounds);
    loc_set_diff = (\<lambda>i. loc_set - Generalized_Network_Impl.loc_set' automata i |> list_of_set);
    loc_set = list_of_set loc_set;
    var_set = Prod_TA_Defs.var_set
      (set syncs, map automaton_of automata, map_of bounds) |> list_of_set;
    n_ps = length automata;
    num_actions = length action_set;
    m = length (remdups clk_set);
    num_states_list = map (\<lambda>i. loc_set' i |> remdups |> length) [0..<n_ps];
    num_states = (\<lambda>i. num_states_list ! i);
    mk_renaming = mk_renaming (\<lambda>x. x)
  in do {
    ((renum_acts, _), (renum_clocks, inv_renum_clocks), (renum_vars, inv_renum_vars)) \<leftarrow>
      mk_renaming action_set <|> mk_renaming clk_set <|> mk_renaming var_set;
    let renum_clocks = Suc o renum_clocks;
    let inv_renum_clocks = (\<lambda>c. if c = 0 then STR ''0'' else inv_renum_clocks (c - 1));
    renum_states_list' \<leftarrow> combine_map (\<lambda>i. mk_renaming' (loc_set' i)) [0..<n_ps];
    let renum_states_list = map fst renum_states_list';
    let renum_states_list = map_index
      (\<lambda>i m. extend_domain m (loc_set_diff i) (length (loc_set' i))) renum_states_list;
    let renum_states = (\<lambda>i. renum_states_list ! i);
    let inv_renum_states = (\<lambda>i. map snd renum_states_list' ! i);
    assert (fst ` set bounds \<subseteq> set var_set)
      STR ''State variables are declared but do not appear in model'';
    Result (m, num_states, num_actions, renum_acts, renum_vars, renum_clocks, renum_states,
      inv_renum_states, inv_renum_vars, inv_renum_clocks)
  }"

definition "preproc_mc \<equiv> \<lambda>dc ids_to_names (syncs, automata, bounds) L\<^sub>0 s\<^sub>0 formula.
  let _ = println (STR ''Make renaming'') in
  case make_renaming syncs automata bounds of
    Error e \<Rightarrow> return (Error e)
  | Result (m, num_states, num_actions, renum_acts, renum_vars, renum_clocks, renum_states,
      inv_renum_states, inv_renum_vars, inv_renum_clocks) \<Rightarrow> do {
    let _ = println (STR ''Renaming'');
    let (syncs', automata', bounds') = rename_network
      syncs bounds automata renum_acts renum_vars renum_clocks renum_states;
    let bounds = sort_key (\<lambda>(s, _, _). renum_vars s) bounds; \<comment> \<open>XXX: add this to legacy code\<close>
    let _ = println (STR ''Calculating ceiling'');
    let k = Generalized_Network_Impl_nat_defs.local_ceiling syncs' bounds' automata' m num_states;
    let _ = println (STR ''Running model checker'');
    let inv_renum_states = (\<lambda>i. ids_to_names i o inv_renum_states i);
    r \<leftarrow> rename_mc dc syncs bounds automata k STR ''_urge'' L\<^sub>0 s\<^sub>0 formula
      m num_states num_actions renum_acts renum_vars renum_clocks renum_states
      inv_renum_states inv_renum_vars inv_renum_clocks;
    return (Result r)
  }
"

definition
  "err s = Error [s]"

definition
"do_preproc_mc \<equiv> \<lambda>dc ids_to_names (syncs, automata, bounds) L\<^sub>0 s\<^sub>0 formula. do {
  r \<leftarrow> preproc_mc dc ids_to_names (syncs, automata, bounds) L\<^sub>0 s\<^sub>0 formula;
  return (case r of
    Error es \<Rightarrow>
      intersperse (STR ''\<newline>'') es
      |> concat_str
      |> (\<lambda>e. STR ''Error during preprocessing:\<newline>'' + e)
      |> err
  | Result Renaming_Failed \<Rightarrow> STR ''Renaming failed'' |> err
  | Result Preconds_Unsat \<Rightarrow> STR ''Input invalid'' |> err
  | Result Unsat \<Rightarrow>
      (if dc then STR ''Model has no deadlock!'' else STR ''Property is not satisfied!'') |> Result
  | Result Sat \<Rightarrow>
      (if dc then STR ''Model has a deadlock!''  else STR ''Property is satisfied!'') |> Result
  )
}"

lemmas [code] =
  Generalized_Network_Impl.action_set_def
  Generalized_Network_Impl.loc_set'_def

export_code do_preproc_mc in SML module_name Main




paragraph \<open>Unsafe Glue Code for Printing\<close>

code_printing
  constant print \<rightharpoonup> (SML) "writeln _"
       and        (OCaml) "print'_string _"
code_printing
  constant println \<rightharpoonup> (SML) "writeln _"
       and          (OCaml) "print'_endline _"

code_printing
  constant failwith \<rightharpoonup> (SML) "raise Fail _"
       and           (OCaml) "failwith _"


text \<open>Eliminate Gabow statistics\<close>
code_printing
  code_module Gabow_Skeleton_Statistics \<rightharpoonup> (SML) \<open>\<close>
code_printing
  code_module AStatistics \<rightharpoonup> (SML) \<open>\<close>

text \<open>Delete ``junk''\<close>
code_printing code_module Bits_Integer \<rightharpoonup> (SML) \<open>\<close>

code_printing
  constant stat_newnode \<rightharpoonup> (SML) "(fn x => ()) _"
| constant stat_start   \<rightharpoonup> (SML) "(fn x => ()) _"
| constant stat_stop    \<rightharpoonup> (SML) "(fn x => ()) _"


(* XXX Add this fix to IArray theory *)
code_printing
  constant IArray.sub' \<rightharpoonup> (SML) "(Vector.sub o (fn (a, b) => (a, IntInf.toInt b)))"

code_thms Show_State_Defs.tracei

code_printing code_module "Logging" \<rightharpoonup> (SML)
\<open>
structure Logging : sig
  val set_level : int -> unit
  val trace : int -> (unit -> string) -> unit
  val get_trace: unit -> (int * string) list
end = struct
  val level = Unsynchronized.ref 0;
  val messages : (int * string) list ref = Unsynchronized.ref [];
  fun set_level i = level := i;
  fun get_trace () = !messages;
  fun trace i f =
    if i > !level
    then ()
    else
      let
        val s = f ();
        val _ = messages := (i, s) :: !messages;
      in () end;
end
\<close>
and (Eval) \<open>\<close>
code_reserved Eval Logging
code_reserved SML Logging


code_printing constant trace_level \<rightharpoonup> (SML)
  "Logging.trace (IntInf.toInt (integer'_of'_int _)) (_ ())"
and (Eval)
  "(fn '_ => fn s => writeln (s ())) _ (_ ())"

text \<open>To disable state tracing:\<close>
(* code_printing
  constant "Show_State_Defs.tracei" \<rightharpoonup>
      (SML)   "(fn n => fn show_state => fn show_clock => fn typ => fn x => ()) _ _ _"
  and (OCaml) "(fun n show_state show_clock ty x -> -> ()) _ _ _" *)


export_code
  do_preproc_mc Result Error
in SML module_name Model_Checker file "../ML/Generalized_Model_Checker.sml"

export_code
  do_preproc_mc Result Error String.explode int_of_integer nat_of_integer
in OCaml module_name Model_Checker

end
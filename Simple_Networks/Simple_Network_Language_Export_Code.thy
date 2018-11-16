theory Simple_Network_Language_Export_Code
  imports
    Simple_Network_Language_Renaming
    "../UPPAAL_State_Networks_Impl_Refine_Calc"
    "../library/Error_Monad"
begin

datatype result =
  Renaming_Failed | Preconds_Unsat | Sat | Unsat

abbreviation "renum_automaton \<equiv> Simple_Network_Rename_Defs.renum_automaton"

hide_const m

locale Simple_Network_Rename_Formula_String =
  Simple_Network_Rename_Defs where automata = automata for automata ::
    "(String.literal list \<times>
     (String.literal act, String.literal, String.literal, int, String.literal, int) transition list
      \<times> (String.literal \<times> (String.literal, int) cconstraint) list) list" +
  assumes renum_states_inj:
    "\<forall>i<n_ps. \<forall>x\<in>loc_set. \<forall>y\<in>loc_set. renum_states i x = renum_states i y \<longrightarrow> x = y"
  and renum_clocks_inj: "inj_on renum_clocks clk_set'"
  and renum_vars_inj:   "inj_on renum_vars var_set"
  and bounds'_var_set: "fst ` set bounds' \<subseteq> var_set"
  and loc_set_invs: "\<Union> ((\<lambda>g. fst ` set g) ` set (map (snd o snd) automata)) \<subseteq> loc_set"
  and loc_set_broadcast: "\<Union> ((set o fst) ` set automata) \<subseteq> loc_set"
  fixes \<Phi> :: "(String.literal, String.literal, int) formula"
    and s\<^sub>0 :: "(String.literal \<times> int) list"
    and L\<^sub>0 :: "String.literal list"
  assumes L\<^sub>0_states: "L\<^sub>0 \<in> states"
      and s\<^sub>0_dom: "fst ` set s\<^sub>0 = var_set" and s\<^sub>0_distinct: "distinct (map fst s\<^sub>0)"
  assumes formula_dom:
    "set1_formula \<Phi> \<subseteq> loc_set"
    "locs_of_formula \<Phi> \<subseteq> {0..<n_ps}"
    "vars_of_formula \<Phi> \<subseteq> var_set"
begin

interpretation Simple_Network_Rename_Formula
  by (standard; 
      rule renum_states_inj renum_clocks_inj renum_vars_inj bounds'_var_set
      loc_set_invs loc_set_broadcast infinite_literal
      L\<^sub>0_states s\<^sub>0_dom s\<^sub>0_distinct formula_dom)

lemmas Simple_Network_Rename_intro = Simple_Network_Rename_Formula_axioms

end

definition rename_network where
  "rename_network broadcast bounds' automata renum_acts renum_vars renum_clocks renum_states \<equiv>
  let
    automata = map_index (renum_automaton renum_acts renum_vars renum_clocks renum_states) automata;
    broadcast = map renum_acts broadcast;
    bounds' = map (\<lambda>(a,b,c). (renum_vars a, b, c)) bounds'
  in
    (broadcast, automata, bounds')
"

definition rename_mc where
  "rename_mc broadcast bounds' automata k L\<^sub>0 s\<^sub>0 formula
    m num_states num_actions renum_acts renum_vars renum_clocks renum_states
\<equiv>
let
   renaming_valid =
    Simple_Network_Rename_Formula_String
      broadcast bounds' renum_vars renum_clocks renum_states automata formula s\<^sub>0 L\<^sub>0;
   (broadcast, automata, bounds') = rename_network
      broadcast bounds' automata renum_acts renum_vars renum_clocks renum_states;
   formula = map_formula renum_states renum_vars id formula;
   L\<^sub>0 = map_index renum_states L\<^sub>0;
   s\<^sub>0 = map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0
in
  if
    renaming_valid
  then
    do {
    r \<leftarrow> precond_mc broadcast bounds' automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula;
    case r of
      None \<Rightarrow> return Preconds_Unsat
    | Some False \<Rightarrow> return Unsat
    | Some True \<Rightarrow> return Sat
    } 
  else return Renaming_Failed
"

theorem model_check_rename:
  "<emp> rename_mc broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
    m num_states num_actions renum_acts renum_vars renum_clocks renum_states
    <\<lambda> Sat \<Rightarrow> \<up>(
        (\<not> has_deadlock (N broadcast automata bounds) (L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<longrightarrow>
          N broadcast automata bounds,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<Turnstile> formula
        ))
     | Unsat \<Rightarrow> \<up>(
        (\<not> has_deadlock (N broadcast automata bounds) (L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<longrightarrow>
          \<not> N broadcast automata bounds,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<Turnstile> formula
        ))
     | Renaming_Failed \<Rightarrow> \<up>(\<not> Simple_Network_Rename_Formula
        broadcast bounds renum_vars renum_clocks renum_states automata formula s\<^sub>0 L\<^sub>0)
     | Preconds_Unsat \<Rightarrow> \<up>(\<not> Simple_Network_Impl_nat_ceiling_start_state
        (map renum_acts broadcast)
        (map (\<lambda>(a,b,c). (renum_vars a, b, c)) bounds)
        (map_index (renum_automaton renum_acts renum_vars renum_clocks renum_states) automata)
        m num_states num_actions k
        (map_index renum_states L\<^sub>0) (map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0)
        (map_formula renum_states renum_vars id formula))
    >\<^sub>t"
proof -
  have *: "
    Simple_Network_Rename_Formula_String
        broadcast bounds renum_vars renum_clocks renum_states automata formula s\<^sub>0 L\<^sub>0
  = Simple_Network_Rename_Formula
        broadcast bounds renum_vars renum_clocks renum_states automata formula s\<^sub>0 L\<^sub>0
  "
    unfolding
      Simple_Network_Rename_Formula_String_def Simple_Network_Rename_Formula_def
      Simple_Network_Rename_def Simple_Network_Rename_Formula_axioms_def
    using infinite_literal by auto
  define A where "A \<equiv> N broadcast automata bounds"
  define check where "check \<equiv> A,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<Turnstile> formula"
  define A' where "A' \<equiv> N
    (map renum_acts broadcast)
    (map_index (renum_automaton renum_acts renum_vars renum_clocks renum_states) automata)
    (map (\<lambda>(a,b,c). (renum_vars a, b, c)) bounds)"
  define check' where "check' \<equiv>
    A',(map_index renum_states L\<^sub>0, map_of (map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0), \<lambda>_ . 0) \<Turnstile>
    map_formula renum_states renum_vars id formula"
  define preconds_sat where "preconds_sat \<equiv>
    Simple_Network_Impl_nat_ceiling_start_state
      (map renum_acts broadcast)
      (map (\<lambda>(a,b,c). (renum_vars a, b, c)) bounds)
      (map_index (renum_automaton renum_acts renum_vars renum_clocks renum_states) automata)
      m num_states num_actions k
      (map_index renum_states L\<^sub>0) (map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0)
      (map_formula renum_states renum_vars id formula)"
  define renaming_valid where "renaming_valid \<equiv>
    Simple_Network_Rename_Formula
      broadcast bounds renum_vars renum_clocks renum_states automata formula s\<^sub>0 L\<^sub>0
  "
  have [simp]: "check \<longleftrightarrow> check'" 
    if renaming_valid
    using that unfolding check_def check'_def A_def A'_def renaming_valid_def
    by (rule Simple_Network_Rename_Formula.models_iff'[symmetric])
  have test[symmetric, simp]:
    "Simple_Network_Language_Model_Checking.has_deadlock A (L\<^sub>0, map_of s\<^sub>0, \<lambda>_. 0)
  \<longleftrightarrow>Simple_Network_Language_Model_Checking.has_deadlock A'
     (map_index renum_states L\<^sub>0, map_of (map (\<lambda>(x, y). (renum_vars x, y)) s\<^sub>0), \<lambda>_. 0)
  " if renaming_valid
    using that unfolding check_def check'_def A_def A'_def renaming_valid_def
    by (rule Simple_Network_Rename_Formula.has_deadlock_iff'[symmetric])
  note bla[sep_heap_rules] =
    model_check[
    of "map renum_acts broadcast" "map (\<lambda>(a,b,c). (renum_vars a, b, c)) bounds"
    "map_index (renum_automaton renum_acts renum_vars renum_clocks renum_states) automata"
    m num_states num_actions k "map_index renum_states L\<^sub>0" "map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0"
    "map_formula renum_states renum_vars id formula",
    folded A'_def check'_def preconds_sat_def renaming_valid_def,
    simplified
    ]
  show ?thesis
    unfolding rename_mc_def rename_network_def *
    unfolding
      A_def[symmetric] check_def[symmetric]
      preconds_sat_def[symmetric] renaming_valid_def[symmetric]
    by (sep_auto
          simp: model_checker.refine[symmetric] pure_def return_cons_rule split: bool.splits
       )
qed


paragraph \<open>Code Setup for the Model Checker\<close>

lemmas [code] =
  reachability_checker_def
  Alw_ev_checker_def
  leadsto_checker_def
  model_checker_def[unfolded PR_CONST_def]

lemmas [code] =
  Prod_TA_Defs.n_ps_def
  Simple_Network_Impl.n_vs_def
  Simple_Network_Impl.automaton_of_def
  Simple_Network_Impl_nat_defs.pairs_by_action_impl_def
  Simple_Network_Impl_nat_defs.all_actions_from_vec_def
  Simple_Network_Impl_nat_defs.all_actions_by_state_def
  Simple_Network_Impl_nat_defs.compute_upds_impl_def
  Simple_Network_Impl_nat_defs.actions_by_state_def
  Simple_Network_Impl_nat_defs.check_boundedi_def
  Simple_Network_Impl_nat_defs.get_commited_def
  Simple_Network_Impl_nat_defs.make_combs_def
  Simple_Network_Impl_nat_defs.trans_map_def
  Simple_Network_Impl_nat_defs.actions_by_state'_def
  Simple_Network_Impl_nat_defs.bounds_map_def
  mk_updsi_def

lemma (in Simple_Network_Impl_nat_defs) bounded_s\<^sub>0_iff:
  "bounded bounds (map_of s\<^sub>0) \<longleftrightarrow> bounded (map_of bounds') (map_of s\<^sub>0)"
  unfolding bounds_def snd_conv ..

lemmas [code] =
  Simple_Network_Impl_nat_ceiling_start_state_def
  Simple_Network_Impl_nat_ceiling_start_state_axioms_def[
    unfolded Simple_Network_Impl_nat_defs.bounded_s\<^sub>0_iff]
  Simple_Network_Impl_nat_def

lemmas [code_unfold] = bounded_def dom_map_of_conv_image_fst

export_code Simple_Network_Impl_nat_ceiling_start_state_axioms

export_code precond_mc in SML module_name Test


paragraph \<open>Code Setup for Renaming\<close>

lemmas [code] =
  Simple_Network_Rename_Formula_String_def
  Simple_Network_Impl.clk_set'_def
  Simple_Network_Impl.clkp_set'_def

lemmas [code] =
  Simple_Network_Rename_Defs.renum_automaton_def
  Simple_Network_Rename_Defs.renum_cconstraint_def
  Simple_Network_Rename_Defs.map_cconstraint_def
  Simple_Network_Rename_Defs.renum_reset_def
  Simple_Network_Rename_Defs.renum_upd_def
  Simple_Network_Rename_Defs.renum_act_def
  Simple_Network_Rename_Defs.renum_exp_def

lemma (in Prod_TA_Defs) states_mem_iff:
  "L \<in> states \<longleftrightarrow> length L = n_ps \<and>
  (\<forall> i. i < n_ps \<longrightarrow> (\<exists> (l, g, a, r, u, l') \<in> fst (snd (fst (snd A) ! i)). L ! i = l \<or> L ! i = l'))"
  unfolding states_def trans_def N_def by (auto split: prod.split)

lemmas [code_unfold] =
  Prod_TA_Defs.states_mem_iff
  Simple_Network_Impl.var_set_compute
  Simple_Network_Impl.loc_set_compute
  setcompr_eq_image
  Simple_Network_Impl.length_automata_eq_n_ps[symmetric]

export_code rename_mc in SML module_name Test



paragraph \<open>Calculating the Clock Ceiling\<close>

context Simple_Network_Impl_nat_defs
begin

definition "clkp_inv i l \<equiv>
  (UNION (set (filter (\<lambda> (a, b). a = l) (snd (snd (automata ! i))))) (collect_clock_pairs o snd))"

definition "clkp_set'' i l \<equiv>
    clkp_inv i l \<union> (\<Union> (l, g, _) \<in> set (fst (snd (automata ! i))). collect_clock_pairs g)"

definition
  "collect_resets i l = (\<Union> (l, g, a, f, r, _) \<in> set (fst (snd (automata ! i))). set r)"

context
  fixes q c :: nat
begin

  definition "n \<equiv> num_states q"

  definition "V \<equiv> \<lambda> v. v \<le> m"

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
    let reset = collect_resets q l in
    fold
    (\<lambda> (l1, g, a, f, r, l') xs. if l1 \<noteq> l \<or> l' \<in> set xs \<or> c \<in> reset then xs else (l' # xs))
    (fst (snd (automata ! q)))
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
  E l \<equiv> if l = n then [0..<n_ps] else filter (\<lambda> l'. l \<in> set (E' l')) [0..<n_ps]
"

text \<open>
  Weights already turned around.
\<close>
definition "
  W l l' \<equiv> if l = n then - bound l' else 0
"

definition "
  G \<equiv> \<lparr> gi_V = V, gi_E = E, gi_V0 = [n], \<dots> = W \<rparr>
"

definition "
  local_ceiling \<equiv>
  let
    w = calc_shortest_scc_paths G n
  in
    map (\<lambda> x. case x of None \<Rightarrow> 0 | Some x \<Rightarrow> nat(-x)) w
"

end

definition "
  k \<equiv>
    rev $
    fold
      (\<lambda> q xs.
        (\<lambda> x. rev x # xs) $
        fold
          (\<lambda> l xs.
            (\<lambda> x. (0 # rev x) # xs) $
            fold
              (\<lambda> c xs. local_ceiling q c ! l # xs)
              [1..<Suc m]
              []
          )
          [0..<n q]
          []
      )
      [0..<p]
      []
"

end


lemmas [code] =
  Simple_Network_Impl_nat_defs.k_def
  Simple_Network_Impl_nat_defs.local_ceiling_def
  Simple_Network_Impl_nat_defs.n_def
  Simple_Network_Impl_nat_defs.G_def
  Simple_Network_Impl_nat_defs.W_def
  Simple_Network_Impl_nat_defs.V_def
  Simple_Network_Impl_nat_defs.E'_def
  Simple_Network_Impl_nat_defs.E_def
  Simple_Network_Impl_nat_defs.resets_def
  Simple_Network_Impl_nat_defs.bound_def
  Simple_Network_Impl_nat_defs.bound_inv_def
  Simple_Network_Impl_nat_defs.bound_g_def
  Simple_Network_Impl_nat_defs.collect_resets_def
  Simple_Network_Impl_nat_defs.clkp_set''_def
  Simple_Network_Impl_nat_defs.clkp_inv_def

export_code Simple_Network_Impl_nat_defs.k checking SML_imp



paragraph \<open>Calculating the Renaming\<close>

definition "mem_assoc x = list_ex (\<lambda>(y, _). x = y)"

definition "mk_renaming str xs \<equiv>
do {
  mapping \<leftarrow> fold_error
    (\<lambda>x m.
      if mem_assoc x m then Error [STR ''Duplicate name:'' + str x] else (x, length m) # m |> Result
    ) xs [];
  Result (the o map_of mapping)
}"

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


context Simple_Network_Impl
begin

definition action_set where
  "action_set \<equiv>
    (\<Union>(_, trans, _) \<in> set automata. \<Union>(_, _, a, _, _, _) \<in> set trans. set_act a) \<union> set broadcast"

definition loc_set' where
  "loc_set' p = (\<Union>(l, _, _, _, _, l')\<in>set (fst (snd (automata ! p))). {l, l'})" for p

end


fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse sep (x # y # xs) = x # sep # intersperse sep (y # xs)" |
  "intersperse _ xs = xs"

definition
  "concat_str = String.implode o concat o map String.explode"


paragraph \<open>Unsafe Glue Code\<close>

definition list_of_set :: "'a set \<Rightarrow> 'a list" where
  "list_of_set xs = undefined"

code_printing
  constant list_of_set \<rightharpoonup> (SML) "(fn Set xs => xs) _"
       and              (OCaml) "(fun x -> match x with Set xs -> xs) _"

definition print :: "String.literal \<Rightarrow> unit" where
  "print x = ()"

code_printing
  constant print \<rightharpoonup> (SML) "print _"
       and        (OCaml) "print'_string _"

definition println :: "String.literal \<Rightarrow> unit" where
  "println x = print (x + STR ''\<newline>'')"

definition "make_renaming \<equiv> \<lambda> broadcast automata bounds.
  let
    action_set = Simple_Network_Impl.action_set automata broadcast |> list_of_set;
    clk_set = fst ` Simple_Network_Impl.clkp_set' automata |> list_of_set;
    loc_set = (\<lambda>i. Simple_Network_Impl.loc_set' automata i |> list_of_set);
    var_set = Prod_TA_Defs.var_set
      (set broadcast, map Simple_Network_Impl.automaton_of automata, map_of bounds) |> list_of_set;
    n_ps = length automata;
    num_actions = length (remdups action_set);
    m = length (remdups clk_set);
    num_states_list = map (\<lambda>i. loc_set i |> remdups |> length) [0..<n_ps];
    num_states = (\<lambda>i. num_states_list ! i);
    mk_renaming = mk_renaming (\<lambda>x. x)
  in do {
    (renum_acts, renum_clocks, renum_vars) \<leftarrow>
      mk_renaming action_set <|> mk_renaming clk_set <|> mk_renaming var_set;
    renum_states_list \<leftarrow> combine_map (\<lambda>i. mk_renaming (loc_set i)) [0..<n_ps];
    let renum_states = (\<lambda>i. renum_states_list ! i);
    Result (m, num_states, num_actions, renum_acts, renum_vars, renum_clocks, renum_states)
  }"

definition "preproc_mc \<equiv> \<lambda> (broadcast, automata, bounds) L\<^sub>0 s\<^sub>0 formula.
  case make_renaming broadcast automata bounds of
    Error e \<Rightarrow> return (Error e)
  | Result (m, num_states, num_actions, renum_acts, renum_vars, renum_clocks, renum_states) \<Rightarrow> do {
    let (broadcast', automata', bounds') = rename_network
      broadcast bounds automata renum_acts renum_vars renum_clocks renum_states;
    let k = Simple_Network_Impl_nat_defs.k broadcast' bounds' automata' m num_states;
    r \<leftarrow> rename_mc broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
      m num_states num_actions renum_acts renum_vars renum_clocks renum_states;
    return (Result r)
  }
"

definition
"main \<equiv> \<lambda> (broadcast, automata, bounds) L\<^sub>0 s\<^sub>0 formula. do {
  r \<leftarrow> preproc_mc (broadcast, automata, bounds) L\<^sub>0 s\<^sub>0 formula;
  return (case r of
    Error es \<Rightarrow>
      intersperse (STR ''\<newline>'') es
      |> concat_str
      |> (\<lambda>e. STR ''Error during preprocessing:\<newline>'' + e)
      |> println
  | Result Renaming_Failed \<Rightarrow> STR ''Renaming failed'' |> println
  | Result Preconds_Unsat \<Rightarrow>  STR ''Input invalid'' |> println
  | Result Unsat \<Rightarrow> STR ''Property is not satisfied!'' |> println
  | Result Sat   \<Rightarrow> STR ''Property is satisfied!'' |> println
  )
}"

lemmas [code] =
  Simple_Network_Impl.action_set_def
  Simple_Network_Impl.loc_set'_def

export_code main in SML module_name Main

end
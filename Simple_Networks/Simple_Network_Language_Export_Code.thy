theory Simple_Network_Language_Export_Code
  imports
    "../../Parser_Combinators/JSON_Parsing"
    Simple_Network_Language_Renaming
    "../UPPAAL_State_Networks_Impl_Refine_Calc"
    "../library/Error_List_Monad"
begin

datatype result =
  Renaming_Failed | Preconds_Unsat | Sat | Unsat

abbreviation "renum_automaton \<equiv> Simple_Network_Rename_Defs.renum_automaton"

hide_const m

locale Simple_Network_Rename_Formula_String =
  Simple_Network_Rename_Defs where automata = automata for automata ::
    "(nat list \<times>
     (String.literal act, nat, String.literal, int, String.literal, int) transition list
      \<times> (nat \<times> (String.literal, int) cconstraint) list) list" +
  assumes renum_states_inj:
    "\<forall>i<n_ps. \<forall>x\<in>loc_set. \<forall>y\<in>loc_set. renum_states i x = renum_states i y \<longrightarrow> x = y"
  and renum_clocks_inj: "inj_on renum_clocks clk_set'"
  and renum_vars_inj:   "inj_on renum_vars var_set"
  and bounds'_var_set: "fst ` set bounds' \<subseteq> var_set"
  and loc_set_invs: "\<Union> ((\<lambda>g. fst ` set g) ` set (map (snd o snd) automata)) \<subseteq> loc_set"
  and loc_set_broadcast: "\<Union> ((set o fst) ` set automata) \<subseteq> loc_set"
  fixes \<Phi> :: "(nat, nat, String.literal, int) formula"
    and s\<^sub>0 :: "(String.literal \<times> int) list"
    and L\<^sub>0 :: "nat list"
  assumes L\<^sub>0_states: "L\<^sub>0 \<in> states"
      and s\<^sub>0_dom: "fst ` set s\<^sub>0 = var_set" and s\<^sub>0_distinct: "distinct (map fst s\<^sub>0)"
  assumes formula_dom:
    "set2_formula \<Phi> \<subseteq> loc_set"
    "locs_of_formula \<Phi> \<subseteq> {0..<n_ps}"
    "vars_of_formula \<Phi> \<subseteq> var_set"
begin

interpretation Simple_Network_Rename_Formula
  by (standard; 
      rule renum_states_inj renum_clocks_inj renum_vars_inj bounds'_var_set
      loc_set_invs loc_set_broadcast infinite_literal infinite_UNIV_nat
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
  Simple_Network_Rename_Defs.renum_bexp_def

lemma (in Prod_TA_Defs) states_mem_iff:
  "L \<in> states \<longleftrightarrow> length L = n_ps \<and>
  (\<forall> i. i < n_ps \<longrightarrow> (\<exists> (l, b, g, a, r, u, l') \<in> fst (snd (fst (snd A) ! i)). L ! i = l \<or> L ! i = l'))"
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
    clkp_inv i l \<union> (\<Union> (l, b, g, _) \<in> set (fst (snd (automata ! i))). collect_clock_pairs g)"

definition
  "collect_resets i l = (\<Union> (l, b, g, a, f, r, _) \<in> set (fst (snd (automata ! i))). set r)"

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
    (\<lambda> (l1, b, g, a, f, r, l') xs. if l1 \<noteq> l \<or> l' \<in> set xs \<or> c \<in> reset then xs else (l' # xs))
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
    (\<Union>(_, trans, _) \<in> set automata. \<Union>(_, _, _, a, _, _, _) \<in> set trans. set_act a) \<union> set broadcast"

definition loc_set' where
  "loc_set' p = (\<Union>(l, _, _, _, _, _, l')\<in>set (fst (snd (automata ! p))). {l, l'})" for p

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



definition
  "mk_renaming' xs \<equiv> mk_renaming (String.implode o show) xs"

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
    renum_states_list \<leftarrow> combine_map (\<lambda>i. mk_renaming' (loc_set i)) [0..<n_ps];
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
  "err s = Error [s]"

definition
"do_preproc_mc \<equiv> \<lambda> (broadcast, automata, bounds) L\<^sub>0 s\<^sub>0 formula. do {
  r \<leftarrow> preproc_mc (broadcast, automata, bounds) L\<^sub>0 s\<^sub>0 formula;
  return (case r of
    Error es \<Rightarrow>
      intersperse (STR ''\<newline>'') es
      |> concat_str
      |> (\<lambda>e. STR ''Error during preprocessing:\<newline>'' + e)
      |> err
  | Result Renaming_Failed \<Rightarrow> STR ''Renaming failed'' |> err
  | Result Preconds_Unsat \<Rightarrow> STR ''Input invalid'' |> err
  | Result Unsat \<Rightarrow> STR ''Property is not satisfied!'' |> Result
  | Result Sat   \<Rightarrow> STR ''Property is satisfied!'' |> Result
  )
}"

lemmas [code] =
  Simple_Network_Impl.action_set_def
  Simple_Network_Impl.loc_set'_def

export_code do_preproc_mc in SML module_name Main

definition parse where
  "parse parser s \<equiv> case parse_all lx_ws parser s of
    Inl e \<Rightarrow> Error [e () ''Parser: '' |> String.implode]
  | Inr r \<Rightarrow> Result r"

definition get_nat :: "string \<Rightarrow> JSON \<Rightarrow> nat Error_List_Monad.result" where
  "get_nat s json \<equiv> case json of
    Object as \<Rightarrow> Error []
  | _ \<Rightarrow> Error [STR ''JSON Get: expected object'']
" for json

definition of_object :: "JSON \<Rightarrow> (string \<rightharpoonup> JSON) Error_List_Monad.result" where
  "of_object json \<equiv> case json of
    Object as \<Rightarrow> map_of as |> Result
  | _ \<Rightarrow> Error [STR ''json_to_map: expected object'']
" for json

definition get where
  "get m x \<equiv> case m x of None \<Rightarrow> Error [STR ''Get: key not found''] | Some a \<Rightarrow> Result a"

definition
  "get_default def m x \<equiv> case m x of None \<Rightarrow> def | Some a \<Rightarrow> a"

definition default where
  "default def x \<equiv> case x of Result s \<Rightarrow> s | Error e \<Rightarrow> def"

definition of_array where
  "of_array json \<equiv> case json of
    JSON.Array s \<Rightarrow> Result s
  | _ \<Rightarrow> Error [STR ''of_array: expected sequence'']
" for json

definition of_string where
  "of_string json \<equiv> case json of
    JSON.String s \<Rightarrow> Result (String.implode s)
  | _ \<Rightarrow> Error [STR ''of_array: expected sequence'']
" for json

definition of_nat where
  "of_nat json \<equiv> case json of
    JSON.Nat n \<Rightarrow> Result n
  | _ \<Rightarrow> Error [STR ''of_nat: expected natural number'']
" for json

definition of_int where
  "of_int json \<equiv> case json of
    JSON.Int n \<Rightarrow> Result n
  | _ \<Rightarrow> Error [STR ''of_int: expected integral number'']
" for json

definition [consuming]:
  "lx_underscore = exactly ''_'' with (\<lambda>_. CHR ''_'')"

definition [consuming]:
  "lx_hyphen = exactly ''-'' with (\<lambda>_. CHR ''-'')"

definition [consuming]:
  "ta_var_ident \<equiv>
    (lx_alphanum \<parallel> lx_underscore)
    -- Parser_Combinator.repeat (lx_alphanum \<parallel> lx_underscore \<parallel> lx_hyphen)
    with uncurry (#)
  "

definition [consuming]:
  "parse_bound \<equiv> ta_var_ident --
    exactly ''['' *-- lx_int -- exactly '':'' *-- lx_int --* exactly '']''"

definition "parse_bounds \<equiv> parse_list (lx_ws *-- parse_bound with (\<lambda>(s,p). (String.implode s, p)))"

value [code] "parse parse_bounds (STR ''id[-1:2], id[-1:0]'')"

definition [consuming]:
  "scan_var = ta_var_ident"

abbreviation seq_ignore_left_ws (infixr "**--" 60)
  where "p **-- q \<equiv> token p *-- q" for p q

abbreviation seq_ignore_right_ws (infixr "--**" 60)
  where "p --** q \<equiv> token p --* q" for p q

abbreviation seq_ws (infixr "---" 60)
  where "seq_ws p q \<equiv> token p -- q" for p q

definition scan_acconstraint where [unfolded Let_def, consuming]:
  "scan_acconstraint \<equiv>
    let scan =
      (\<lambda>s c. scan_var --- exactly s **-- token lx_int with (\<lambda>(x, y). c (String.implode x) y)) in
  (
    scan ''<''  lt \<parallel>
    scan ''<='' le \<parallel>
    scan ''=''  eq \<parallel>
    scan ''>='' ge \<parallel>
    scan ''>''  gt
  )
"

definition [consuming]:
  "scan_parens lparen rparen inner \<equiv> exactly lparen **-- inner --** token (exactly rparen)"

definition [consuming]: "scan_loc \<equiv>
  (scan_var --- (exactly ''.'' *-- scan_var))
  with (\<lambda> (p, s). loc (String.implode p) (String.implode s))"

definition [consuming]: "scan_bexp_elem \<equiv> scan_acconstraint \<parallel> scan_loc"

abbreviation "scan_parens' \<equiv> scan_parens ''('' '')''"

definition [consuming]: "scan_infix_pair a b s \<equiv> a --- exactly s **-- token b"

lemma [fundef_cong]:
  assumes "\<And>l2. ll_fuel l2 \<le> ll_fuel l' \<Longrightarrow> A l2 = A' l2"
  assumes "\<And>l2. ll_fuel l2 + (if length s > 0 then 1 else 0) \<le> ll_fuel l' \<Longrightarrow> B l2 = B' l2"
  assumes "s = s'" "l=l'"
  shows "scan_infix_pair A B s l = scan_infix_pair A' B' s' l'"
  using assms unfolding scan_infix_pair_def gen_token_def
  by (cases s; intro Parser_Combinator.bind_cong repeat_cong assms) auto

lemma [fundef_cong]:
  assumes "\<And>l2. ll_fuel l2 < ll_fuel l \<Longrightarrow> A l2 = A' l2" "l = l'"
  shows "scan_parens' A l = scan_parens' A' l'"
  using assms unfolding scan_parens_def gen_token_def
  by (intro Parser_Combinator.bind_cong repeat_cong assms) auto

fun scan_7 and scan_6 and scan_0 where
  "scan_7 ::=
    scan_infix_pair scan_6 scan_7 ''->'' with uncurry imply \<parallel>
    scan_infix_pair scan_6 scan_7 ''||'' with uncurry sexp.or \<parallel>
    scan_6" |
  "scan_6 ::=
    scan_infix_pair scan_0 scan_6 ''&&'' with uncurry and \<parallel> scan_0" |
  "scan_0 ::=
    exactly ''~'' **-- scan_parens' scan_7 with not \<parallel>
    scan_bexp_elem \<parallel>
    scan_parens' scan_7"

abbreviation "scan_bexp \<equiv> scan_7"

value [code] "parse scan_bexp (STR ''a < 3 && b>=2 || ~ (c <= 4)'')"

definition [consuming]: "scan_prefix p head = exactly head **-- p" for p

lemma is_cparser_token[parser_rules]:
  "is_cparser (token a)" if "is_cparser a"
  using that unfolding gen_token_def by simp

lemma is_cparser_scan_parens'[parser_rules]:
  "is_cparser (scan_parens' a)"
  unfolding scan_parens_def by simp

lemma [parser_rules]:
  "is_cparser scan_0"
  by (simp add: scan_0.simps[abs_def])

lemma [parser_rules]:
  "is_cparser scan_6"
  by (subst scan_6.simps[abs_def]) simp

lemma [parser_rules]:
  "is_cparser scan_bexp"
  by (subst scan_7.simps[abs_def]) simp

definition [consuming]: "scan_formula \<equiv>
  scan_prefix scan_bexp ''E<>'' with formula.EX \<parallel>
  scan_prefix scan_bexp ''E[]'' with EG \<parallel>
  scan_prefix scan_bexp ''A<>'' with AX \<parallel>
  scan_prefix scan_bexp ''A[]'' with AG \<parallel>
  scan_infix_pair scan_bexp scan_bexp ''-->'' with uncurry Leadsto"

definition [consuming]:
  "scan_update \<equiv> scan_infix_pair scan_var lx_nat ''='' with (\<lambda>(s, x). (String.implode s, x))"

abbreviation "scan_updates \<equiv> parse_list scan_update"

definition [consuming]: "scan_action \<equiv>
  (scan_var --* exactly ''?'') with In o String.implode \<parallel>
  (scan_var --* exactly ''!'') with Out o String.implode \<parallel>
  scan_var with Sil o String.implode"

abbreviation orelse (infix "orelse" 58) where
  "a orelse b \<equiv> default b a"

definition
  "parse_action s \<equiv> parse scan_action s orelse Sil (STR '''')"

(* let scan_edge_label = scan_action <|> str "" ^^ fun _ -> Internal "" *)
definition assert where "assert b m = (if b then Result () else Error [m])"

fun chop_sexp where
  "chop_sexp clocks (and a b) (cs, es) =
    chop_sexp clocks a (cs, es) |> chop_sexp clocks b" |
  "chop_sexp clocks (eq a b) (cs, es) =
    (if a \<in> set clocks then (eq a b # cs, es) else (cs, eq a b # es))" |
  "chop_sexp clocks (le a b) (cs, es) =
    (if a \<in> set clocks then (lt a b # cs, es) else (cs, eq a b # es))" |
  "chop_sexp clocks (lt a b) (cs, es) =
    (if a \<in> set clocks then (eq a b # cs, es) else (cs, eq a b # es))" |
  "chop_sexp clocks (ge a b) (cs, es) =
    (if a \<in> set clocks then (eq a b # cs, es) else (cs, eq a b # es))" |
  "chop_sexp clocks (gt a b) (cs, es) =
    (if a \<in> set clocks then (eq a b # cs, es) else (cs, eq a b # es))" |
  "chop_sexp clocks a (cs, es) = (cs, a # es)"

fun sexp_to_acconstraint :: "(String.literal, String.literal, String.literal, int) sexp \<Rightarrow> _" where
  "sexp_to_acconstraint (lt a (b :: int)) = acconstraint.LT a b" |
  "sexp_to_acconstraint (le a b) = acconstraint.LE a b" |
  "sexp_to_acconstraint (eq a b) = acconstraint.EQ a b" |
  "sexp_to_acconstraint (ge a b) = acconstraint.GE a b" |
  "sexp_to_acconstraint (gt a b) = acconstraint.GT a b"

no_notation top_assn ("true")

fun sexp_to_bexp :: "(String.literal, String.literal, String.literal, int) sexp \<Rightarrow> _" where
  "sexp_to_bexp (lt a (b :: int)) = bexp.lt a b |> Result" |
  "sexp_to_bexp (le a b) = bexp.le a b |> Result" |
  "sexp_to_bexp (eq a b) = bexp.eq a b |> Result" |
  "sexp_to_bexp (ge a b) = bexp.ge a b |> Result" |
  "sexp_to_bexp (gt a b) = bexp.gt a b |> Result" |
  "sexp_to_bexp (and a b) =
    do {a \<leftarrow> sexp_to_bexp a; b \<leftarrow> sexp_to_bexp b; bexp.and a b |> Result}" |
  "sexp_to_bexp (sexp.or a b) =
    do {a \<leftarrow> sexp_to_bexp a; b \<leftarrow> sexp_to_bexp b; bexp.or a b |> Result}" |
  "sexp_to_bexp (imply a b) =
    do {a \<leftarrow> sexp_to_bexp a; b \<leftarrow> sexp_to_bexp b; bexp.imply a b |> Result}" |
  "sexp_to_bexp x        = Error [STR ''Illegal construct in binary operation'']"

(*
definition true where "true \<equiv> sexp.or (gt (STR ''a'') 1) (le (STR ''a'') 1)"
*)

derive "show" bexp

instantiation String.literal :: "show"
begin

definition "shows_prec p (s::String.literal) rest = String.explode s @ rest" for p
definition "shows_list (cs::String.literal list) s = concat (map String.explode cs) @ s"
instance
  by standard (simp_all add: shows_prec_literal_def shows_list_literal_def show_law_simps)

end

definition compile_invariant where
  "compile_invariant clocks vars inv \<equiv>
    let
      (cs, es) = chop_sexp clocks inv ([], []);
      g = map sexp_to_acconstraint cs
    in
      if es = []
      then Result (g, bexp.true)
      else do {
        let e = fold (and) (tl es) (hd es);
        b \<leftarrow> sexp_to_bexp e;
        assert (set1_bexp b \<subseteq> set vars) (String.implode (''Unknown variable in bexp: '' @ show b));
        Result (g, b)
      }" for inv

definition compile_invariant' where
  "compile_invariant' clocks vars inv \<equiv>
  if inv = STR '''' then
    Result ([], bexp.true)
  else do {
    inv \<leftarrow> parse scan_bexp inv |> err_msg (STR ''Failed to parse guard in '' + inv);
    compile_invariant clocks vars inv
  }
" for inv

definition convert_node where
  "convert_node clocks vars n \<equiv> do {
    n \<leftarrow>  of_object n;
    ID \<leftarrow> get n ''id'' \<bind> of_nat;
    name \<leftarrow> get n ''name'' \<bind> of_string;
    inv \<leftarrow> get n ''invariant'' \<bind> of_string;
    (inv, inv_vars) \<leftarrow>
      compile_invariant' clocks vars inv |> err_msg (STR ''Failed to parse invariant!'');
    assert (inv_vars = bexp.true) (STR ''State invariants on nodes are not supported'');
    Result ((name, ID), inv)
  }"

definition convert_edge where
  "convert_edge clocks vars e \<equiv> do {
    e \<leftarrow> of_object e;
    source \<leftarrow> get e ''source'' \<bind> of_nat;
    target \<leftarrow> get e ''target'' \<bind> of_nat;
    guard  \<leftarrow> get e ''guard''  \<bind> of_string;
    label  \<leftarrow> get e ''label''  \<bind> of_string;
    update \<leftarrow> get e ''update'' \<bind> of_string;
    label  \<leftarrow> if label = STR '''' then STR '''' |> Sil |> Result else
      parse scan_action label |> err_msg (STR ''Failed to parse label in '' + label);
    (g, check)  \<leftarrow> compile_invariant' clocks vars guard |> err_msg (STR ''Failed to parse guard!'');
    update \<leftarrow> parse scan_updates update |> err_msg (STR ''Failed to parse update in '' + update);
    let resets = filter (\<lambda>x. fst x \<in> set clocks) update;
    assert
      (list_all (\<lambda>(_, d). d = 0) resets)
      (STR ''Clock resets to values different from zero are not supported'');
    let resets = map fst resets;
    let upds = filter (\<lambda>x. fst x \<notin> set clocks) update;
    assert
      (list_all (\<lambda>(x, _). x \<in> set vars) upds)
      (STR ''Unknown variable in update'');
    let upds = map (\<lambda>(x, d). (x, (exp.const (int d) :: (String.literal, int) exp))) upds;
    Result (source, check, g, label, upds, resets, target)
  }"

definition convert_automaton where
  "convert_automaton clocks vars a \<equiv> do {
    nodes \<leftarrow> get a ''nodes'' \<bind> of_array;
    edges \<leftarrow> get a ''edges'' \<bind> of_array;
    nodes \<leftarrow> combine_map (convert_node clocks vars) nodes;
    let invs = map (\<lambda> ((_, n), g). (n, g)) nodes;
    let names_to_ids = map fst nodes;
    assert (map fst names_to_ids |> filter (\<lambda>s. s \<noteq> STR '''') |> distinct)
      (STR ''Node names are ambiguous'' + (show (map fst names_to_ids) |> String.implode));
    assert (map snd names_to_ids |> distinct) (STR ''Duplicate node id'');
    let names_to_ids = map_of names_to_ids;
    let commited = default (STR '''') (get a ''commited'' \<bind> of_string);
    commited \<leftarrow> if commited = STR '''' then Result [] else
      parse (parse_list (token ta_var_ident with String.implode)) commited
      |> err_msg (STR ''Failed to parse commited locations'');
    commited \<leftarrow> combine_map (get names_to_ids) commited;
    edges \<leftarrow> combine_map (convert_edge clocks vars) edges;
    Result (names_to_ids, (commited, edges, invs))
  }"

fun rename_locs_sexp where
  "rename_locs_sexp f (not a) =
    do {a \<leftarrow> rename_locs_sexp f a; not a |> Result}" |
  "rename_locs_sexp f (imply a b) =
    do {a \<leftarrow> rename_locs_sexp f a; b \<leftarrow> rename_locs_sexp f b; imply a b |> Result}" |
  "rename_locs_sexp f (sexp.or a b) =
    do {a \<leftarrow> rename_locs_sexp f a; b \<leftarrow> rename_locs_sexp f b; sexp.or a b |> Result}" |
  "rename_locs_sexp f (and a b) =
    do {a \<leftarrow> rename_locs_sexp f a; b \<leftarrow> rename_locs_sexp f b; and a b |> Result}" |
  "rename_locs_sexp f (loc n x) = do {x \<leftarrow> f n x; loc n x |> Result}" |
  "rename_locs_sexp f (eq a b) = Result (eq a b)" |
  "rename_locs_sexp f (lt a b) = Result (lt a b)" |
  "rename_locs_sexp f (le a b) = Result (le a b)" |
  "rename_locs_sexp f (ge a b) = Result (ge a b)" |
  "rename_locs_sexp f (gt a b) = Result (gt a b)"

fun rename_locs_formula where
  "rename_locs_formula f (formula.EX \<phi>) = rename_locs_sexp f \<phi> \<bind> Result o formula.EX" |
  "rename_locs_formula f (EG \<phi>) = rename_locs_sexp f \<phi> \<bind> Result o EG" |
  "rename_locs_formula f (AX \<phi>) = rename_locs_sexp f \<phi> \<bind> Result o AX" |
  "rename_locs_formula f (AG \<phi>) = rename_locs_sexp f \<phi> \<bind> Result o AG" |
  "rename_locs_formula f (Leadsto \<phi> \<psi>) =
    do {\<phi> \<leftarrow> rename_locs_sexp f \<phi>; \<psi> \<leftarrow> rename_locs_sexp f \<psi>; Leadsto \<phi> \<psi> |> Result}"

definition convert :: "JSON \<Rightarrow>
  (String.literal list \<times>
    (nat list \<times>
     (String.literal act, nat, String.literal, int, String.literal, int) transition list
      \<times> (nat \<times> (String.literal, int) cconstraint) list) list \<times>
   (String.literal \<times> int \<times> int) list \<times> (nat, nat, String.literal, int) formula
  ) Error_List_Monad.result" where
  "convert json \<equiv> do {
    all \<leftarrow> of_object json;
    automata \<leftarrow> get all ''automata'';
    automata \<leftarrow> of_array automata;
    let broadcast = default [] (do {
      x \<leftarrow> get all ''broadcast''; of_array x}
    );
    broadcast \<leftarrow> combine_map of_string broadcast;
    let bounds = default (STR '''') (do {
      x \<leftarrow> get all ''vars''; of_string x}
    );
    bounds \<leftarrow> parse parse_bounds bounds |> err_msg (STR ''Failed to parse bounds'');
    clocks \<leftarrow> get all ''clocks'';
    clocks \<leftarrow> of_string clocks;
    clocks \<leftarrow> parse (parse_list (lx_ws *-- ta_var_ident with String.implode)) clocks
       |> err_msg (STR ''Failed to parse clocks'');
    formula \<leftarrow> get all ''formula'';
    formula \<leftarrow> of_string formula;
    formula \<leftarrow> parse scan_formula formula |> err_msg (STR ''Failed to parse formula'');
    automata \<leftarrow> combine_map of_object automata;
    process_names \<leftarrow> combine_map (\<lambda>a. get a ''name'' \<bind> of_string) automata;
    assert (distinct process_names) (STR ''Process names are ambiguous'');
    let process_names_to_index = List_Index.index process_names;
    init_locs \<leftarrow> combine_map
      (\<lambda>a. do {x \<leftarrow> get a ''initial''; x \<leftarrow> of_nat x; show x |> String.implode |> Result})
      automata;
    let formula = formula.map_formula process_names_to_index id id id formula;
    let vars = map fst bounds;
    names_automata \<leftarrow> combine_map (convert_automaton clocks vars) automata;
    let automata = map snd names_automata;
    let names    = map fst names_automata;
    formula \<leftarrow> rename_locs_formula (\<lambda>i. get (names ! i)) formula;
    Result (broadcast, automata, bounds, formula)
}" for json



paragraph \<open>Unsafe Glue Code for Printing\<close>

definition print :: "String.literal \<Rightarrow> unit" where
  "print x = ()"

code_printing
  constant print \<rightharpoonup> (SML) "print _"
       and        (OCaml) "print'_string _"

definition println :: "String.literal \<Rightarrow> unit" where
  "println x = print (x + STR ''\<newline>'')"

definition "print_err = print"
definition "println_err x = print_err (x + STR ''\<newline>'')"

definition parse_convert_run_print where
  "parse_convert_run_print s \<equiv>
   case parse json s \<bind> convert of
     Error es \<Rightarrow> do {let _ = map println es; return ()}
   | Result (broadcast, automata, bounds, formula) \<Rightarrow> do {
      r \<leftarrow> do_preproc_mc (broadcast, automata, bounds) [] [] formula;
      case r of
        Error es \<Rightarrow> do {let _ = map println es; return ()}
      | Result s \<Rightarrow> do {let _ = println s; return ()}
  }"

(* export_code do_preproc_mc checking SML *)

export_code parse_convert_run_print in SML_imp module_name Test

text \<open>A small test of parsing + conversion:\<close>
definition "parse_convert_run s \<equiv> parse json s \<bind> convert"

ML \<open>
  fun test file =
  let
    val s = file_to_string file;
    val _ = writeln s;
  in
    @{code parse_convert_run} s end
\<close>

ML_val \<open>test "benchmarks/HDDI_02.muntax"\<close>

end
theory Simple_Network_Language_Export_Code
  imports Simple_Network_Language_Renaming
begin

datatype result =
  Renaming_Failed | Preconds_Unsat | Sat | Unsat

abbreviation "renum_automaton \<equiv> Simple_Network_Rename_Defs.renum_automaton"

definition rename_mc where
  "rename_mc broadcast bounds' automata k L\<^sub>0 s\<^sub>0 formula
    m num_states num_actions renum_acts renum_vars renum_clocks renum_states
\<equiv>
let
   renaming_valid =
    Simple_Network_Rename_Formula
      broadcast bounds' renum_vars renum_clocks renum_states automata formula s\<^sub>0 L\<^sub>0;
   automata = map_index (renum_automaton renum_acts renum_vars renum_clocks renum_states) automata;
   broadcast = map renum_acts broadcast;
   bounds' = map (\<lambda>(a,b,c). (renum_vars a, b, c)) bounds';
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
  define A where "A \<equiv> N broadcast automata bounds"
  define check where "check \<equiv> A,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<Turnstile> formula"
  define A' where "A' \<equiv> N
    (map renum_acts broadcast)
    (map_index (renum_automaton renum_acts renum_vars renum_clocks renum_states) automata)
    (map (\<lambda>(a,b,c). (renum_vars a, b, c)) bounds)
  "
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
    unfolding rename_mc_def
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
  Simple_Network_Rename_def
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

lemmas [code] =
  Simple_Network_Rename_Formula_def
  Simple_Network_Rename_Formula_axioms_def


export_code rename_mc in SML module_name Test

end
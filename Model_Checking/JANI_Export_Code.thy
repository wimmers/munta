subsection \<open>Exporting Code for the JANI Model Checker\<close>
theory JANI_Export_Code
  imports JANI.JANI JANI.JANI_Embedding
    Simple_Networks.Expression_Simplification
    Generalized_Network_Language_Export_Code
    TA_Library.OCaml_Diff_Array_Impl TA_Library.OCaml_Code_Printings
begin

paragraph \<open>Misc\<close>

lemma prod_cong:
  "(a1, b1) = (a2, b2)" if "a1 = a2" "b1 = b2"
  using that by simp

lemma map_filter_subseq_mapI:
  "subseq (List.map_filter f xs) (map h xs)" if "\<forall>y. \<forall>x \<in> set xs. f x = Some y \<longrightarrow> h x = y"
  using that by (induction xs, auto split: option.split)

lemma the_default_alt_def:
  "the_default d v_opt = (case v_opt of None \<Rightarrow> d | Some v \<Rightarrow> v)"
  by (simp split: option.split)

\<comment> \<open>Utility for obtaining tags for facts of a large precondition checks in the error monad.\<close>
lemma is_result_assert_iff_tag:
  "is_result (assert b s) \<longleftrightarrow> TAG s b"
  unfolding is_result_assert_iff TAG_def ..

(* XXX Duplicated? *)
fun bexp_to_acconstraint :: "(_, _) bexp \<Rightarrow> _" where
  "bexp_to_acconstraint (bexp.lt (var a) (const (b :: int))) = acconstraint.LT a b" |
  "bexp_to_acconstraint (bexp.le (var a) (const b)) = acconstraint.LE a b" |
  "bexp_to_acconstraint (bexp.eq (var a) (const b)) = acconstraint.EQ a b" |
  "bexp_to_acconstraint (bexp.ge (var a) (const b)) = acconstraint.GE a b" |
  "bexp_to_acconstraint (bexp.gt (var a) (const b)) = acconstraint.GT a b"

definition is_true where
  "is_true e = (e = bexp.true)"

lemma is_true_code [code]:
  "is_true e = (case e of bexp.true \<Rightarrow> True | _ \<Rightarrow> False)"
  unfolding is_true_def by (cases e) auto

lemmas [code_unfold] = is_true_def [symmetric]


paragraph \<open>Implementable JANI Embedding\<close>

text \<open>The locale @{locale JANI_Embed_Defs} already contains a description of an embedding of
JANI models in the Generalized Network Language (GNL).
The correctness proof is in @{locale JANI_Embed}.
Here, we first need to give a description of this embedding,
which the GNL model checker code can work on.
Next, we prove the equivalence of the two embeddings.
\<close>

context JANI
begin

text \<open>We first choose a concrete embedding.\<close>

definition mk_conj where
  "mk_conj \<equiv> \<lambda>[] \<Rightarrow> bexp.true | x # xs \<Rightarrow> fold (bexp.and) xs x"

definition "get_cond e = (case dest_conj e of
  None \<Rightarrow> undefined
| Some xs \<Rightarrow> mk_conj (filter (Not o is_atom' clks vars) xs)
)"

definition "get_cconstr e = (case dest_conj e of
  None \<Rightarrow> []
| Some xs \<Rightarrow> filter (\<lambda>e. is_atom' clks vars e \<and> e \<noteq> bexp.true) xs |> map bexp_to_acconstraint
)"

interpretation embed: JANI_Embed_Defs where
  get_cconstr = get_cconstr and
  get_cond = get_cond
  .


text \<open>Now we define the computable description.\<close>

definition inv' where
  "inv' i \<equiv> map (\<lambda>loc. (location.name loc, time_progress loc)) (locations (N i))"

definition
  "mk_automaton' p A \<equiv>
    ([],
     [],
     map embed.mk_edge (edges A),
     map (\<lambda>(name, cond). (name, case cond of None \<Rightarrow> [] | Some cond \<Rightarrow> get_cconstr cond)) (inv' p)
    )"

definition
  "N_G' \<equiv> map (\<lambda>p. mk_automaton' p (N p)) [0..<n_ps]"

definition "B_G' =
  List.map_filter (\<lambda>decl. case variable_declaration.type decl of
      TBounded b \<Rightarrow> Some (variable_declaration.name decl, (lower_bound b, upper_bound b))
    | _ \<Rightarrow> None
    )
    (variables model)"

definition
  "systemG' \<equiv> (
    embed.syncsG,
    N_G',
    B_G'
  )
"

\<comment> \<open>This is what the model checker for GNL will work on.\<close>
interpretation impl: Generalized_Network_Impl_Defs N_G' embed.syncsG B_G' .

\<comment> \<open>This is the canonical description of the system given to the GNL model checker.\<close>
definition
  "systemG_nta \<equiv> (set embed.syncsG, map automaton_of N_G', map_of B_G') :: (_, _, _, _, _, _) nta"

\<comment> \<open>We can use existing GNL code to compute its state set, for instance.\<close>
term "Prod_TA_Defs.states systemG_nta"


text \<open>Next we define the preconditions for the embedding to be valid in a computable way.\<close>

lemma is_splittableI:
  "dest_conj b \<noteq> None \<Longrightarrow> embed.is_splittable b"
  using check_bexp_dest_conj_iff[of b]
  unfolding embed.is_splittable_def
  sorry

\<comment> \<open>Not directly computable\<close>
lemma invs_splittable:
  "\<forall>p<n_ps. \<forall>l \<in> set (locations (N p)). case time_progress l of
    Some cc \<Rightarrow> embed.is_splittable cc | _ \<Rightarrow> True" if
  "\<forall>p<n_ps. \<forall>l \<in> set (locations (N p)). case time_progress l of
    Some cc \<Rightarrow> dest_conj cc \<noteq> None | _ \<Rightarrow> True"
  using that by (auto split: option.splits intro: is_splittableI)

lemma guards_splittable:
  "\<forall>p<n_ps. \<forall>e \<in> set (edges (N p)). embed.is_splittable (guard e)" if
  "\<forall>p<n_ps. \<forall>e \<in> set (edges (N p)). dest_conj (guard e) \<noteq> None"
  using that by (auto split: option.splits intro: is_splittableI)

\<comment> \<open>Computable\<close>
lemma get_cond_time_progress:
  "\<forall>p<n_ps. \<forall>l \<in> set (locations (N p)). \<forall>g. time_progress l = Some g \<longrightarrow> get_cond g = bexp.true"
  oops

\<comment> \<open>Computable\<close>
lemma get_cconstr_true:
    "get_cconstr bexp.true = []"
  unfolding get_cconstr_def by simp

definition check_jani_embed_preconds where
"check_jani_embed_preconds \<equiv> combine [
 assert (distinct
     (map variable_declaration.name (model.variables model)))
  (STR ''Declared variables have distinct names''),
  assert (\<forall>x \<in> set (model.variables model).
          case initial_value x of
          Some (exp.const c) \<Rightarrow> True | _ \<Rightarrow> False)
  (STR ''All variables are initalized''),
 assert (\<forall>decl \<in> set (model.variables model).
       transient decl \<longrightarrow>
       (case variable_declaration.type decl of
        TBounded bounds \<Rightarrow> True | _ \<Rightarrow> False))
  (STR ''All transient variables are bounded''),
 assert (\<forall>p<n_ps.
       distinct (map location.name (locations (N p))))
  (STR ''All location names are distinct (per automaton)''),
 assert (\<forall>p<n_ps.
       \<forall>e\<in>set (edges (N p)).
          length (destinations e) = 1)
  (STR ''Destinations are deterministic''),
 assert (transient_vars_upds = [] \<or>
    (\<forall>sync\<in>set (syncs (system model)).
        \<exists>p<n_ps.
           case synchronise sync ! p of
             Some a \<Rightarrow> \<not> is_weak p a
           | _ \<Rightarrow> False))
  (STR ''No transient variables or at least one strong sync per vector''),
 assert (\<forall>sync\<in>set (syncs (system model)).
       length (synchronise sync) = n_ps)
  (STR ''Sync vectors have the right length''),
 assert (\<forall>p<n_ps.
       \<forall>e\<in>set (edges (N p)).
          \<forall>destination\<in>set (destinations e).
             (\<forall>updi\<in>set (get_upds destination). case updi of ((x, e), i) \<Rightarrow>
                 x \<in> vars) \<and>
             (\<exists>l\<in>set (locations (N p)).
                 location.name l =
                 destination.location destination))
  (STR ''Destinations''),
 assert (\<forall>p<n_ps. \<forall>l \<in> set (locations (N p)). case time_progress l of
    Some cc \<Rightarrow> dest_conj cc \<noteq> None | _ \<Rightarrow> True)
  (STR ''Invariants are splittable''),
 assert (\<forall>p<n_ps. \<forall>e \<in> set (edges (N p)). dest_conj (guard e) \<noteq> None)
  (STR ''Guards are splittable''),
 assert (\<forall>p<n_ps. \<forall>l \<in> set (locations (N p)).
  case time_progress l of
    Some g \<Rightarrow> is_true (get_cond g)
  | _ \<Rightarrow> False)
  (STR ''Time progress conditions are clock constraints'')
]
"

end


paragraph \<open>Correcntess of the Preconditions Check\<close>

locale JANI_Impl = JANI +
  assumes embed_preconds: "is_result check_jani_embed_preconds"
begin

sublocale embed: JANI_Embed where
  get_cconstr = get_cconstr and
  get_cond = get_cond
  using embed_preconds
  unfolding check_jani_embed_preconds_def is_result_combine_Cons_iff is_result_assert_iff_tag
    is_true_def
  apply (elim conjE)
  apply standard
  apply (tag, fastforce split: option.split_asm type.split_asm exp.split_asm
      intro!: invs_splittable guards_splittable get_cconstr_true)+
  done

lemmas step_embed_iff = embed.step_embed_iff


paragraph \<open>Equivalence of the Embeddings\<close>

lemma (in JANI_Embed) type_of_eq_SomeI:
  "type_of (variable_declaration.name x) = Some (variable_declaration.type x)"
  if "x \<in> set (model.variables model)"
  unfolding type_of_def apply clarsimp
  using that variable_declarations_names_distinct unfolding find_Some_iff in_set_conv_nth
  by (smt (verit, best) distinct_idx le_antisym le_trans less_or_eq_imp_le nat_neq_iff)

lemma (in JANI) type_of_eq_SomeE:
  fixes name
  assumes "type_of name = Some typ"
  obtains decl where
    "decl \<in> set (variables model)" "variable_declaration.type decl = typ"
    "variable_declaration.name decl = name"
  using assms unfolding type_of_def by (auto dest: find_SomeD)

lemma (in JANI_Embed) inv'_locations_distinct:
  "distinct (map fst (inv' i))" if "i < n_ps"
  using that unfolding inv'_def by (auto dest: locations_distinct cong: map_cong)

lemma (in JANI_Embed) map_of_inv'_eq_SomeD:
  assumes "map_of (inv' i) l = Some cond_opt" "i < n_ps"
  shows "inv i l = the_default bexp.true cond_opt"
  using assms inv'_locations_distinct
  by (subst (asm) map_of_eq_Some_iff) (auto simp: inv'_def inv_def find_location)

lemma (in JANI_Embed) inv_neq_trueD:
  assumes "inv i l \<noteq> bexp.true" "i < n_ps"
  shows "map_of (inv' i) l = Some (Some (inv i l))"
  using assms
  by (subst map_of_eq_Some_iff, intro inv'_locations_distinct)
     (auto simp: inv'_def inv_def the_default_alt_def 
        split: option.split bind_split_asm dest: find_SomeD)

lemma (in JANI_Embed) inv'_eq_inv:
  "Generalized_Network_Language_Impl.default_map_of []
     (map (\<lambda>(name, cond). (name, case cond of None \<Rightarrow> [] | Some x \<Rightarrow> get_cconstr x))
       (inv' i)) =
    (\<lambda>l. get_cconstr (inv i l))" if "i < n_ps" for i
  apply (rule ext)
  apply (subst default_map_of_map_2[where x = None and y = "[]"])
  apply (auto split: option.split)
  unfolding default_map_of_alt_def using that apply -
  subgoal default_map_of_eq_None
    by (clarsimp split: if_split_asm simp: map_of_inv'_eq_SomeD)
       (auto simp: get_cconstr_true dest!: inv_neq_trueD[rotated])
  subgoal default_map_of_eq_Some
    by (clarsimp split: if_split_asm simp: map_of_inv'_eq_SomeD)
  done

theorem implementation_embedding_correct:
  "systemG_nta = embed.systemG"
  unfolding systemG_nta_def
  apply (intro prod_cong)
    apply (simp; fail)
  subgoal N_G
    unfolding embed.N_G_def N_G'_def
    unfolding Generalized_Network_Language_Impl.automaton_of_def
    unfolding embed.mk_automaton_def mk_automaton'_def
    by (simp add: embed.inv'_eq_inv)
  subgoal B_G
    unfolding embed.B_G_def
    apply (rule ext)
    apply (clarsimp split: option.split type.split; safe)
    subgoal None
      unfolding B_G'_def map_of_eq_None_iff set_map_filter
      by (auto split: type.split_asm simp: embed.type_of_eq_SomeI)
    subgoal Some_TBounded
      unfolding B_G'_def
      apply (subst map_of_eq_Some_iff)
      subgoal distinct
        using embed.variable_declarations_names_distinct unfolding map_map_filter
        by (force split: type.splits intro: map_filter_subseq_mapI intro: subseq_distinct)
      unfolding set_map_filter by (force elim!: type_of_eq_SomeE)
    subgoal Some_TClock
      unfolding B_G'_def map_of_eq_None_iff set_map_filter
      by (auto split: type.split_asm simp: embed.type_of_eq_SomeI)
    done
  done

end


paragraph \<open>Code Equations\<close>

lemma (in JANI) vars_code:
  "vars = variable_declaration.name ` set (filter
    (\<lambda>decl.
      case variable_declaration.type decl of
        TBounded bounds \<Rightarrow> True
      | _ \<Rightarrow> False
    )
    (variables model))"
  unfolding vars_def by (fastforce split: type.splits)

lemma (in JANI) clks_code:
  "clks = variable_declaration.name ` set (filter
    (\<lambda>decl.
      case variable_declaration.type decl of
        TClock \<Rightarrow> True
      | _ \<Rightarrow> False
    )
    (variables model))"
  unfolding clks_def by (fastforce split: type.splits)

lemma (in JANI) get_upds_code:
  "get_upds destination \<equiv> let assignments = JANI.assignments destination in
    map (\<lambda>a. ((ref a, value a), JANI.index a))
      (filter (\<lambda>a. case type_of (ref a) of Some (TBounded bounds) \<Rightarrow> True | _ \<Rightarrow> False) assignments)"
  unfolding get_upds_def
  by simp (intro eq_reflection map_cong filter_cong; fastforce split: option.splits type.splits)

lemma (in JANI) get_cconstr_code:
  "get_cconstr e = (case dest_conj e of
    None \<Rightarrow> []
  | Some xs \<Rightarrow> filter (\<lambda>e. is_atom' clks vars e \<and> \<not> is_true e) xs
    |> map bexp_to_acconstraint
  )"
  unfolding get_cconstr_def is_true_def by simp

lemmas [code] =
  JANI.check_jani_embed_preconds_def
  JANI.n_ps_def
  JANI.N_def
  JANI.get_cond_def
  JANI.mk_conj_def
  JANI.transient_vars_upds_def
  JANI.is_weak_def
  JANI.get_upds_code
  JANI.type_of_def
  JANI.vars_code
  JANI.clks_code
  JANI.get_cconstr_code

export_code JANI.check_jani_embed_preconds JANI.get_cconstr in SML


paragraph \<open>Completing The Model Checker Setup\<close>

context JANI
begin

definition L\<^sub>0 where
  "L\<^sub>0 = List.map (\<lambda>automaton. hd (initial_locations automaton)) (automata model)"

definition s\<^sub>0 where
  "s\<^sub>0 = List.map_filter
    (\<lambda>decl.
      case variable_declaration.type decl of
        TBounded _ \<Rightarrow> Some (
          variable_declaration.name decl,
          case initial_value decl of Some (const i) \<Rightarrow> i
        )
      | _ \<Rightarrow> None
    )
    (variables model)"

definition ids_to_names where
  "ids_to_names p l = (let name = automaton.name (N p) in name + l)"

end

definition
"do_preproc_mc_jani \<equiv> \<lambda>dc ids_to_names jani L\<^sub>0 s\<^sub>0 formula. do {
  r \<leftarrow> do {
    case JANI.check_jani_embed_preconds jani of
      Result _ \<Rightarrow>
      let model = JANI.systemG' jani in
      preproc_mc dc ids_to_names model L\<^sub>0 s\<^sub>0 formula
    | Error es \<Rightarrow> return (Error es)
  };
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

definition do_preproc_mc_jani1 where
"do_preproc_mc_jani1 jani formula = do {
  let L\<^sub>0 = JANI.L\<^sub>0 jani;
  let s\<^sub>0 = JANI.s\<^sub>0 jani;
  let dc = False;
  let ids_to_names = JANI.ids_to_names jani;
  do_preproc_mc_jani dc ids_to_names jani L\<^sub>0 s\<^sub>0 formula
}
"


paragraph \<open>Convenience Functions\<close>

definition op_and_bool :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "op_and_bool a b = (a \<and> b)"

definition op_or_bool :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "op_or_bool a b = (a \<or> b)"

definition op_not_bool :: "bool \<Rightarrow> bool" where
  "op_not_bool a = (\<not> a)"

definition op_plus_int :: "int \<Rightarrow> int \<Rightarrow> int" where
  "op_plus_int a b \<equiv> a + b"

definition op_minus_int :: "int \<Rightarrow> int \<Rightarrow> int" where
  "op_minus_int a b \<equiv> a - b"

definition op_mul_int :: "int \<Rightarrow> int \<Rightarrow> int" where
  "op_mul_int a b \<equiv> a * b"

definition op_div_int :: "int \<Rightarrow> int \<Rightarrow> int" where
  "op_div_int a b \<equiv> a div b"

definition op_neg_int :: "int \<Rightarrow> int" where
  "op_neg_int a \<equiv> a"

lemmas [code] =
  JANI.N_G'_def
  JANI.B_G'_def
  JANI.systemG'_def
  JANI.mk_automaton'_def
  JANI.inv'_def
  JANI.get_resets_def
  JANI_Embed_Defs.max_idx_def
  JANI_Embed_Defs.idxs_of_edge_def
  JANI_Embed_Defs.mk_edge_def
  JANI_Embed_Defs.mk_transient_resets_def
  JANI_Embed_Defs.get_destination_def
  JANI_Embed_Defs.mk_action_def
  JANI_Embed_Defs.syncsG_def
  JANI_Embed_Defs.mk_sync_def
  do_preproc_mc_jani_def
  JANI.L\<^sub>0_def
  JANI.s\<^sub>0_def
  JANI.ids_to_names_def
  do_preproc_mc_jani1_def


paragraph \<open>Code Export\<close>

export_code do_preproc_mc_jani Result Error
  JANI.model_ext JANI.automaton_ext
  JANI.edge_ext JANI.location_ext
  JANI.element_ext JANI.sync_ext JANI.composition_ext
  JANI.bounded_type_ext JANI.action_ext JANI.transient_value_ext
  JANI.assignment_ext JANI.destination_ext JANI.variable_declaration_ext
  TBounded
  JANI.L\<^sub>0 JANI.s\<^sub>0 JANI.ids_to_names do_preproc_mc_jani1
  formula.EX sexp.true
  op_plus_int op_minus_int op_mul_int op_div_int op_neg_int
  op_and_bool op_or_bool op_not_bool
in SML module_name Model_Checker file "../ML/JANI_Model_Checker.sml"

export_code
  do_preproc_mc_jani Result Error String.explode
  int_of_integer integer_of_int nat_of_integer integer_of_nat
  JANI.model_ext JANI.automaton_ext
  JANI.edge_ext JANI.location_ext
  JANI.element_ext JANI.sync_ext JANI.composition_ext
  JANI.bounded_type_ext TBounded JANI.action_ext JANI.transient_value_ext
  JANI.assignment_ext JANI.destination_ext JANI.variable_declaration_ext
  JANI.L\<^sub>0 JANI.s\<^sub>0 JANI.ids_to_names do_preproc_mc_jani1
  formula.EX sexp.true bexp.true
  op_plus_int op_minus_int op_mul_int op_div_int op_neg_int
  op_and_bool op_or_bool op_not_bool
  JANI.vars JANI.clks list_of_set
  JANI.L\<^sub>0 JANI.s\<^sub>0
in OCaml module_name Model_Checker file "../OCaml/lib/JANI_Model_Checker.ml"

end
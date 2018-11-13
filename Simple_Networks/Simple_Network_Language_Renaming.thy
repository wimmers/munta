theory Simple_Network_Language_Renaming
  imports Simple_Network_Language_Impl
begin

context Simple_Network_Impl
begin

lemma N_p_trans_eq:
  "Simple_Network_Language.trans (N p) = set (fst (snd (automata ! p)))" if "p < n_ps"
  using mem_trans_N_iff[OF that] by auto

lemma loc_set_compute:
  "loc_set = \<Union> ((\<lambda>(_, t, _). \<Union> ((\<lambda>(l, _, _, _, _, l'). {l, l'}) ` set t)) ` set automata)"
  unfolding loc_set_def setcompr_eq_image
  apply (auto simp: N_p_trans_eq n_ps_def)
     apply (drule nth_mem, erule bexI[rotated], force)+
   apply (drule mem_nth, force)+
  done

lemma var_set_compute:
  "var_set =
  (\<Union>S \<in> (\<lambda>t. (fst \<circ> snd \<circ> snd \<circ> snd) ` set t) ` ((\<lambda>(_, t, _). t) `  set automata).
    \<Union>f \<in> S. \<Union> (x, e) \<in> set f. {x} \<union> vars_of_exp e)"
  unfolding var_set_def setcompr_eq_image
  apply (auto simp: N_p_trans_eq n_ps_def)
  apply (drule nth_mem, erule bexI[rotated],
      metis (no_types, lifting) insert_iff mem_case_prodI prod.collapse)+
   apply (drule mem_nth, force)+
  done

lemma states_loc_setD:
  "set L \<subseteq> loc_set" if "L \<in> states"
  using states_loc_set that by auto

end (* Simple Network Impl *)


locale Simple_Network_Rename_Defs =
  Simple_Network_Impl automata for automata ::
    "('s list \<times> (('a :: countable) act, 's, 'c, int, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, int) cconstraint) list) list" +
  fixes renum_acts   :: "'a \<Rightarrow> nat"
    and renum_vars   :: "'x \<Rightarrow> nat"
    and renum_clocks :: "'c \<Rightarrow> nat"
    and renum_states :: "nat \<Rightarrow> 's \<Rightarrow> nat"
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

sublocale renum: Simple_Network_Impl
  "map_index renum_automaton automata"
  "map renum_acts broadcast"
  "map (\<lambda>(a,b,c). (renum_vars a, b, c)) bounds'"
  .

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

lemma renum_n_ps_simp[simp]:
  "renum.n_ps = n_ps"
  unfolding n_ps_def renum.n_ps_def by simp

lemma n_ps_eq[simp]:
  "sem.n_ps = n_ps"
  unfolding n_ps_def sem.n_ps_def by auto

lemma dom_bounds: "dom bounds = fst ` set bounds'"
  unfolding bounds_def by (simp add: dom_map_of_conv_image_fst)

lemma sem_bounds_eq: "sem.bounds = bounds"
  unfolding sem.bounds_def bounds_def by simp

lemma sem_loc_set_eq:
  "sem.loc_set = loc_set"
  unfolding sem.loc_set_def loc_set_def n_ps_eq setcompr_eq_image
  apply (simp add: sem_N_eq N_eq)
  apply (rule arg_cong2[where f = "(\<union>)"])
   apply (auto;
      force split: prod.splits
            simp:  renum.conv_automaton_def trans_def renum.automaton_of_def n_ps_def)+
  done

end (* Simple Network Rename Defs *)

lemma
  fixes f :: "'b :: countable \<Rightarrow> nat"
  assumes "inj_on f S" "finite S" "infinite (UNIV :: 'b set)"
  shows extend_bij_inj: "inj (extend_bij f S)" and extend_bij_surj: "surj (extend_bij f S)"
    and extend_bij_extends: "\<forall>x \<in> S. extend_bij f S x = f x"
proof -
  have "infinite (\<nat> :: nat set)"
    unfolding Nats_def by simp
  from assms this have "bij (extend_bij f S)"
    by (intro extend_bij_bij) auto
  then show "inj (extend_bij f S)" and "surj (extend_bij f S)"
    unfolding bij_def by fast+
  from assms \<open>infinite \<nat>\<close> show "\<forall>x \<in> S. extend_bij f S x = f x"
    by (intro extend_bij_extends) auto
qed

lemma default_map_of_map:
  "default_map_of y (map (\<lambda>(a, b). (f a, g b)) xs) (f a) = g (default_map_of x xs a)"
  if "inj f" "y = g x"
  using that unfolding default_map_of_alt_def
  by (auto 4 4 dest: injD[OF that(1)] map_of_SomeD simp: map_of_eq_None_iff map_of_mapk_SomeI)

lemma default_map_of_map_2:
  "default_map_of y (map (\<lambda>(a, b). (a, g b)) xs) a = g (default_map_of x xs a)" if "y = g x"
  unfolding default_map_of_alt_def using that by (auto simp: map_of_map)

lemma dom_map_of_map:
  "dom (map_of (map (\<lambda> (a, b). (f a, g b)) xs)) = f ` fst ` set xs"
  unfolding dom_map_of_conv_image_fst by (auto 4 3)

lemma inj_image_eqI:
  "S = T" if "inj f" "f ` S = f ` T"
  using that by (meson inj_image_eq_iff)

(* XXX Add this *)
lemmas [finite_intros] = finite_set

locale Simple_Network_Rename' =
  Simple_Network_Impl automata for automata ::
    "('s list \<times> (('a :: countable) act, 's, 'c, int, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, int) cconstraint) list) list" +
  fixes renum_acts   :: "'a \<Rightarrow> nat"
    and renum_vars   :: "'x \<Rightarrow> nat"
    and renum_clocks :: "'c \<Rightarrow> nat"
    and renum_states :: "nat \<Rightarrow> 's \<Rightarrow> nat"
  assumes inj_extend_renum_clocks: "inj renum_clocks"
      and renum_states_inj: "\<forall>p<n_ps. inj (renum_states p)"
      and bij_renum_vars: "bij renum_vars"
      and bounds'_var_set: "fst ` set bounds' \<subseteq> var_set"
begin

sublocale Simple_Network_Rename_Defs
  broadcast bounds' automata renum_acts renum_vars renum_clocks renum_states .

lemma aux_1:
  "(\<lambda>x. case case x of
          (l, g) \<Rightarrow> (renum_states p l, renum_cconstraint g) of
     (s, cc) \<Rightarrow> (s, map conv_ac cc))
  = (\<lambda> (l, g). (renum_states p l, map conv_ac (renum_cconstraint g)))
"
  by auto

lemma clocks_inv_inv:
  "clocks_inv (renum_clocks a) = a"
  unfolding clocks_inv_def by (subst the_inv_f_f; rule inj_extend_renum_clocks HOL.refl)

lemma map_u_renum_cconstraint_clock_valI:
  "map_u u \<turnstile> map conv_ac (renum_cconstraint cc)" if "u \<turnstile> map conv_ac cc"
  using that
  unfolding clock_val_def list_all_length
  apply auto
  unfolding renum_cconstraint_def map_cconstraint_def
  apply simp
  unfolding map_u_def
  subgoal for n
    apply (elim allE impE, assumption)
    apply (cases "cc ! n")
        apply (auto simp add: clocks_inv_inv)
    done
  done

lemma map_u_renum_cconstraint_clock_valD:
  "u \<turnstile> map conv_ac cc" if "map_u u \<turnstile> map conv_ac (renum_cconstraint cc)"
  using that
  unfolding clock_val_def list_all_length
  apply auto
  unfolding renum_cconstraint_def map_cconstraint_def
  apply simp
  unfolding map_u_def
  subgoal for n
    apply (elim allE impE, assumption)
    apply (cases "cc ! n")
        apply (auto simp add: clocks_inv_inv)
    done
  done

lemma map_u_renum_cconstraint_clock_val_iff:
  "u \<turnstile> map conv_ac cc \<longleftrightarrow> map_u u \<turnstile> map conv_ac (renum_cconstraint cc)"
  unfolding clock_val_def list_all_length
  apply auto
  unfolding renum_cconstraint_def map_cconstraint_def
  apply simp_all
  unfolding map_u_def
  subgoal for n
    apply (elim allE impE, assumption)
    apply (cases "cc ! n")
        apply (auto simp add: clocks_inv_inv)
    done
  subgoal for n
    apply (elim allE impE, assumption)
    apply (cases "cc ! n")
        apply (auto simp add: clocks_inv_inv)
    done
  done

lemma inj_renum_states: "inj (renum_states p)" if "p < n_ps"
  using renum_states_inj \<open>p < n_ps\<close> by blast

lemma inv_renum_sem_I:
  assumes
    "u \<turnstile> Simple_Network_Language.inv (sem.N p) l"
    "p < n_ps" "l \<in> loc_set"
  shows
    "map_u u \<turnstile> Simple_Network_Language.inv (renum.sem.N p) (renum_states p l)"
proof -
  show ?thesis
    using assms
    unfolding inv_def
    apply -
    apply (subst (asm) sem_N_eq, assumption)
    apply (subst renum.sem_N_eq, subst renum_n_ps_simp, assumption)
    apply (subst nth_map_index, simp add: n_ps_def)
    unfolding conv_automaton_def renum.automaton_of_def
    apply (auto split: prod.split_asm simp: renum_automaton_def comp_def)
    unfolding aux_1
    apply (subst default_map_of_map[where x = "[]"])
    subgoal
      by (intro inj_renum_states \<open>p < n_ps\<close>)
     apply (simp add: renum_cconstraint_def map_cconstraint_def; fail)
    apply (subst (asm) default_map_of_map_2[where x = "[]"])
     apply simp
    apply (erule map_u_renum_cconstraint_clock_valI)
    done
qed

lemma inv_renum_sem_D:
  assumes
    "map_u u \<turnstile> Simple_Network_Language.inv (renum.sem.N p) (renum_states p l)"
    "p < n_ps" "l \<in> loc_set"
  shows
    "u \<turnstile> Simple_Network_Language.inv (sem.N p) l"
proof -
  show ?thesis
    using assms
    unfolding inv_def
    apply -
    apply (subst sem_N_eq, assumption)
    apply (subst (asm) renum.sem_N_eq, subst renum_n_ps_simp, assumption)
    apply (subst (asm) nth_map_index, simp add: n_ps_def)
    unfolding conv_automaton_def renum.automaton_of_def
    apply (auto split: prod.split simp: renum_automaton_def comp_def)
    unfolding aux_1
    apply (subst (asm) default_map_of_map[where x = "[]"])
    subgoal
      by (intro inj_renum_states \<open>p < n_ps\<close>)
     apply (simp add: renum_cconstraint_def map_cconstraint_def; fail)
    apply (subst default_map_of_map_2[where x = "[]"])
     apply simp
    unfolding map_u_renum_cconstraint_clock_val_iff .
qed

lemma dom_the_inv_comp:
  "dom (m o the_inv f) = f ` dom m" if "inj f" "range f = UNIV"
  unfolding dom_def
  apply auto
  subgoal for x y
    apply (subgoal_tac "f (the_inv f x) = x")
     apply force
    using that by (auto intro: f_the_inv_f)
  subgoal for x y
    using that by (auto simp: the_inv_f_f)
  done

lemma inj_renum_vars:
  "inj renum_vars"
  using bij_renum_vars unfolding bij_def ..

lemma surj_renum_vars:
  "surj renum_vars"
  using bij_renum_vars unfolding bij_def ..

lemma map_of_inv_map:
  "map_of xs (the_inv f x) = map_of (map (\<lambda> (a, b). (f a, b)) xs) x"
  if "inj f" "surj f" "the_inv f x \<in> dom (map_of xs)"
  apply (subgoal_tac "x = f (the_inv f x)")
  subgoal premises prems
    using domD[OF that(3)] \<open>inj f\<close>
    apply (subst (2) prems)
    apply safe
    apply (subst map_of_mapk_SomeI; assumption)
    done
  subgoal
    apply (rule sym, rule f_the_inv_f)
    using that by auto
  done

lemma bounded_renumI:
  assumes "bounded (map_of bounds') s"
  shows
    "bounded
       (map_of (map (\<lambda>(a, y). (renum_vars a, y)) bounds'))
       (s o vars_inv)"
  using assms
  unfolding bounded_def
  apply elims
  apply intros
  subgoal
    unfolding dom_map_of_conv_image_fst
    unfolding vars_inv_def
    apply (subst dom_the_inv_comp, rule inj_renum_vars, rule surj_renum_vars)
    apply simp
    unfolding image_comp
    apply (rule image_cong, rule HOL.refl)
    by auto
  subgoal for x
    unfolding vars_inv_def
    apply (subst (asm) dom_the_inv_comp, rule inj_renum_vars, rule surj_renum_vars)
    apply (subgoal_tac "the_inv renum_vars x \<in> dom s")
     apply (drule bspec, assumption)
     apply (drule conjunct1)
     apply simp
     apply (subst (asm) map_of_inv_map, rule inj_renum_vars, rule surj_renum_vars)
     apply (simp; fail)
    subgoal
      by auto
    subgoal
      apply (erule imageE)
      apply simp
      apply (subst the_inv_f_f, rule inj_renum_vars, assumption)
      done
    done
  subgoal
    sorry
  done

lemma bounded_renumD:
  assumes
    "Simple_Network_Language.bounded
     (map_of (map (\<lambda>(a, y). (renum_vars a, y)) bounds')) (s o vars_inv)"
      and "dom s \<subseteq> var_set"
  shows "Simple_Network_Language.bounded (map_of bounds') s"
proof -
  show ?thesis
  using assms(1)
  unfolding bounded_def
  apply elims
  apply intros
  subgoal
    unfolding vars_inv_def
    apply (subst (asm) dom_the_inv_comp, rule inj_renum_vars, rule surj_renum_vars)
    apply (subst (asm) dom_map_of_map)
    unfolding dom_map_of_conv_image_fst
    apply (rule inj_image_eqI[OF inj_renum_vars], simp)
    done
  subgoal for x
    apply (rotate_tac)
    unfolding vars_inv_def
    apply (subst (asm) dom_the_inv_comp, rule inj_renum_vars, rule surj_renum_vars)
    apply (drule bspec)
     apply (rule imageI, assumption)
    apply (drule conjunct1)
    apply (subgoal_tac "map_of (map (\<lambda>(a, y). (renum_vars a, y)) bounds')
               (renum_vars x) = map_of bounds' x",
          (simp add: the_inv_f_f[OF inj_renum_vars]; fail))
    subgoal premises prems
    proof -
      have *:
        "map (\<lambda>(a, y). (renum_vars a, y)) bounds' = map (\<lambda>(a, y). (renum_vars a, y)) bounds'"
        by auto
      have "x \<in> dom (map_of bounds')"
        unfolding dom_map_of_conv_image_fst
        using prems(1,2)
        apply -
        apply (subst (asm) dom_the_inv_comp, rule inj_renum_vars, rule surj_renum_vars)
        apply (subst (asm) dom_map_of_map)
        apply auto
        apply (subst (asm) inj_on_image_eq_iff[OF inj_renum_vars])
        using \<open>dom s \<subseteq> _\<close> by auto
      then obtain y where "map_of bounds' x = Some y"
        by auto
      then show ?thesis
        by (subst map_of_mapk_SomeI) (auto intro: inj_renum_vars)
    qed
    done
  subgoal for x
    sorry
  done
qed

lemma dom_bounds_var_set: "dom sem.bounds \<subseteq> var_set"
  unfolding dom_bounds sem_bounds_eq using bounds'_var_set .

interpretation Bisimulation_Invariant
  "\<lambda>(L, s, u) (L', s', u'). \<exists> a. step_u sem L s u a L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). \<exists> a. step_u renum.sem L s u a L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). L' = map_index renum_states L \<and> s' = s o vars_inv \<and> u' = map_u u"
  "\<lambda> (L, s, u). L \<in> sem.states \<and> dom s \<subseteq> var_set" "\<lambda>_. True"
proof (-, goal_cases)
  case 1
  have *: "L ! p \<in> loc_set" if "p < length automata" "L \<in> sem.states" for L p
    using that sem_loc_set_eq sem.states_loc_set by (force simp: n_ps_def)
  show ?case
    apply standard
       apply clarsimp
    subgoal for L s u L' s' u' a
      apply (inst_existentials "renum_label a")
      apply (cases a)
      subgoal
        apply (simp add: renum_label_def)
        apply (erule step_u_elims')
        apply simp
        apply (rule step_u.intros)
        subgoal
          apply simp
          apply (intros)
          apply (elim allE impE, assumption)
          apply (frule sem.states_lengthD)
          apply (drule inv_renum_sem_I[OF _ _ *]; simp add: n_ps_def; fail)
          done
        subgoal
          by assumption
        subgoal
          by (rule bounded_renumI)
        done
      sorry
      apply clarsimp
    subgoal for L s u L' s' u' a
      apply (cases a)
      subgoal
        apply (simp add: renum_label_def)
        apply (erule step_u_elims')
        subgoal for d
          apply (inst_existentials L s  "u \<oplus> d" "Del :: 'a Simple_Network_Language.label")
             apply simp_all
          apply (rule step_u.intros)
          subgoal
            by (auto 4 3 simp: n_ps_def intro: inv_renum_sem_D dest: sem.states_lengthD *)
          subgoal
            by assumption
          subgoal
            apply (rule bounded_renumD; simp add: comp_def)
            done
          done
        done
      sorry
    subgoal
      apply (auto intro: sem.states_inv)
      apply (drule sem.bounded_inv)
      unfolding bounded_def using dom_bounds_var_set by blast
    subgoal
      .
    done
qed

lemmas renum_bisim = Bisimulation_Invariant_axioms

end (* Simple Network Rename' *)

print_locale Simple_Network_Rename'

locale Simple_Network_Rename =
  Simple_Network_Rename_Defs where automata = automata for automata ::
    "('s list \<times> (('a :: countable) act, 's, 'c, int, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, int) cconstraint) list) list" +
  assumes renum_states_inj:
    "\<forall>i<n_ps. \<forall>x\<in>loc_set. \<forall>y\<in>loc_set. renum_states i x = renum_states i y \<longrightarrow> x = y"
  and renum_clocks_inj: "inj_on renum_clocks clk_set'"
  and renum_vars_inj:   "inj_on renum_vars var_set"
  and infinite_types:
    "infinite (UNIV :: 'c set)" "infinite (UNIV :: 'x set)" "infinite (UNIV :: 's set)"
  and bounds'_var_set: "fst ` set bounds' \<subseteq> var_set"
  and loc_set_invs: "\<Union> ((\<lambda>g. fst ` set g) ` set (map (snd o snd) automata)) \<subseteq> loc_set"
  and loc_set_broadcast: "\<Union> ((set o fst) ` set automata) \<subseteq> loc_set"
begin

lemma clk_set'_finite:
  "finite clk_set'"
  unfolding clk_set'_def unfolding clkp_set'_def by (intro finite_intros) auto

(* XXX Move *)
lemma vars_of_bexp_finite[finite_intros]:
  "finite (vars_of_bexp b)"
  by (induction b) auto

(* XXX Move *)
lemma vars_of_exp_finite[finite_intros]:
  "finite (vars_of_exp e)"
  by (induction e) (auto intro: vars_of_bexp_finite)

(* XXX Move *)
lemmas [finite_intros] = trans_N_finite

lemma loc_set_finite:
  "finite loc_set"
  unfolding loc_set_def by (auto intro!: finite_intros)

(* XXX Move *)
lemma var_set_finite[finite_intros]:
  "finite var_set"
  unfolding var_set_def by (auto intro!: finite_intros)

lemma inj_extend_bij_renum_clocks:
  "inj (extend_bij renum_clocks clk_set')"
  by (intro extend_bij_inj renum_clocks_inj clk_set'_finite infinite_types)

lemma renum_vars_bij_extends[simp]:
  "extend_bij renum_vars var_set x = renum_vars x" if "x \<in> var_set"
  by (intro extend_bij_extends[rule_format] renum_vars_inj var_set_finite infinite_types that)

lemma bij_extend_bij_renum_states:
  "bij (extend_bij renum_vars var_set)"
  by (intro extend_bij_bij renum_vars_inj var_set_finite infinite_types) simp

lemma inj_extend_bij_renum_states: "inj (extend_bij (renum_states p) loc_set)" if "p < n_ps"
  using renum_states_inj infinite_types loc_set_finite \<open>p < n_ps\<close>
  by (intro extend_bij_inj) (auto intro!: inj_onI)

lemma renum_states_extend:
  "extend_bij (renum_states p) loc_set l = renum_states p l" if "l \<in> loc_set" "p < n_ps"
  using renum_states_inj infinite_types loc_set_finite \<open>p < n_ps\<close> \<open>l \<in> loc_set\<close>
  by (intro extend_bij_extends[rule_format]) (auto intro!: inj_onI)

sublocale rename: Simple_Network_Rename'
  broadcast bounds' automata
  renum_acts
  "extend_bij renum_vars var_set"
  "extend_bij renum_clocks clk_set'"
  "\<lambda>p. extend_bij (renum_states p) loc_set"
  by (standard;
      intro allI impI inj_extend_bij_renum_clocks inj_extend_bij_renum_states
           bij_extend_bij_renum_states bounds'_var_set)

definition
  "renum_upd' = map (\<lambda>(x, upd). (renum_vars x, map_exp renum_vars id upd))"

definition
  "renum_reset' = map renum_clocks"

definition renum_automaton' where
  "renum_automaton' i \<equiv> \<lambda>(commited, trans, inv). let
    commited' = map (renum_states i) commited;
    trans' = map (\<lambda>(l, g, a, upd, r, l').
      (renum_states i l,
      map_cconstraint renum_clocks id g, renum_act a, renum_upd' upd, map renum_clocks r, 
      renum_states i l')
    ) trans;
    inv' = map (\<lambda>(l, g). (renum_states i l, map_cconstraint renum_clocks id g)) inv
  in (commited', trans', inv')
"

lemmas renum_automaton'_alt_def = renum_automaton'_def[unfolded
  renum_reset'_def renum_upd'_def map_cconstraint_def renum_act_def
  ]

lemma set1_acconstraint_elim:
  assumes "c \<in> set1_acconstraint ac"
  obtains x where "(c, x) = constraint_pair ac"
  using assms by (cases ac) auto

lemma set1_bexp_vars_of_bexp:
  "set1_bexp b = vars_of_bexp b"
  by (induction b) auto

lemma set1_exp_vars_of_exp:
  "set1_exp e = vars_of_exp e"
  by (induction e) (auto simp: set1_bexp_vars_of_bexp)

lemma renum_automaton_eq:
  "rename.renum_automaton p (automata ! p) = renum_automaton p (automata ! p)"
  if "p < n_ps"
proof -
  have renum_clocks: "extend_bij renum_clocks clk_set' c = renum_clocks c" if "c \<in> clk_set'" for c
    apply (rule extend_bij_extends[rule_format])
       apply (rule renum_clocks_inj clk_set'_finite infinite_types)+
    using that
    apply auto
    done
  have renum_cconstraint: "rename.renum_cconstraint g = renum_cconstraint g"
    if "\<Union> (set1_acconstraint ` (set g)) \<subseteq> clk_set'" for g
    unfolding rename.renum_cconstraint_def renum_cconstraint_def map_cconstraint_def
    apply (rule map_cong, rule HOL.refl)
    apply (rule acconstraint.map_cong_pred, rule HOL.refl)
    using that
    apply (auto intro: renum_clocks simp: pred_acconstraint_def)
    done
  show ?thesis
    using that[folded length_automata_eq_n_ps]
    unfolding rename.renum_automaton_def renum_automaton_def
    apply (clarsimp split: prod.split)
    apply safe
    subgoal commited
      using loc_set_broadcast
      by (subst renum_states_extend; (simp add: n_ps_def)?) (fastforce dest: nth_mem)
    subgoal start_locs
      by (subst renum_states_extend; (simp add: n_ps_def)?)
         (fastforce dest: nth_mem simp: loc_set_compute)
    subgoal guards
      apply (rule renum_cconstraint)
      unfolding clk_set'_def clkp_set'_def collect_clock_pairs_def
      apply (fastforce dest: nth_mem elim: set1_acconstraint_elim)
      done
    subgoal upds
      unfolding renum_upd_def rename.renum_upd_def rename.renum_exp_def renum_exp_def
      apply (rule map_cong, rule HOL.refl)
      apply clarsimp
      apply (rule conjI)
      subgoal
        by (rule renum_vars_bij_extends) (fastforce dest: nth_mem simp: var_set_compute)
      apply (rule exp.map_cong_pred, rule HOL.refl)
      apply (clarsimp simp: pred_exp_def)
      apply (subst renum_vars_bij_extends)
       apply (fastforce dest: nth_mem simp: set1_exp_vars_of_exp var_set_compute)+
      done
    subgoal clock_resets
      unfolding rename.renum_reset_def renum_reset_def
      apply (rule map_cong, rule HOL.refl)
      apply (rule renum_clocks)
      unfolding clk_set'_def
      apply (fastforce dest: nth_mem)
      done
    subgoal dest_locs
      by (subst renum_states_extend; (simp add: n_ps_def)?)
         (fastforce dest: nth_mem simp: loc_set_compute)
    subgoal inv_locs
      using loc_set_invs
      by (subst renum_states_extend; (simp add: n_ps_def)?) (force dest: nth_mem)
    subgoal renum_clocks
      apply (rule renum_cconstraint)
      unfolding clk_set'_def clkp_set'_def collect_clock_pairs_def
      apply clarsimp
      apply (erule set1_acconstraint_elim)
      apply standard
      apply (rule UnI1)
      apply clarsimp
      apply (drule nth_mem)
      apply (erule bexI[rotated])
      apply simp
      apply (erule bexI[rotated])
      apply force
      done
    done
qed

lemma rename_sem_eq:
  "rename.renum.sem = renum.sem"
  apply clarsimp
  apply (rule conjI)
  subgoal
    by (rule map_index_cong) (auto simp: renum_automaton_eq[folded length_automata_eq_n_ps])
  subgoal
    using bounds'_var_set by - (fo_rule arg_cong, auto)
  done

thm rename.renum_bisim[unfolded rename_sem_eq]

lemma
  assumes "L \<in> sem.states" "dom s \<subseteq> var_set"
  shows "map_index (\<lambda>p. extend_bij (renum_states p) loc_set) L = map_index renum_states L"
    and "(s oo Simple_Network_Rename_Defs.vars_inv) (extend_bij renum_vars var_set) = s o (the_inv_into var_set renum_vars)"
    and "rename.map_u u = map_u u"
  subgoal
    apply (intros add: map_index_cong)
    apply (rule renum_states_extend)
    using assms unfolding sem.states_def
    sorry
  subgoal
    apply (intro ext)
    apply (simp add: rename.vars_inv_def vars_inv_def)
    subgoal for x
      apply (cases "x \<in> renum_vars ` var_set")
      subgoal
        apply (fo_rule arg_cong)
        apply auto
        apply (subst the_inv_into_f_f)
          prefer 3
          apply (subst renum_vars_bij_extends[symmetric])
          defer
          apply (subst the_inv_f_f)
        sorry
      subgoal
        sorry
      done
    done
  subgoal
    unfolding rename.map_u_def map_u_def
    apply (simp add: Simple_Network_Rename_Defs.clocks_inv_def)
    apply (rule ext)
    apply (auto simp: comp_def)
    oops



interpretation Bisimulation_Invariant
  "\<lambda>(L, s, u) (L', s', u'). \<exists> a. step_u sem L s u a L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). \<exists> a. step_u renum.sem L s u a L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). L' = map_index renum_states L \<and> s' = s o vars_inv \<and> u' = map_u u"
  "\<lambda> (L, s, u). L \<in> sem.states \<and> dom s \<subseteq> var_set" "\<lambda>_. True"
  thm Bisimulation_Invariant_simulation_strengthen rename.renum_bisim[unfolded rename_sem_eq]
  oops

end (* Simple_Network_Rename *)


lemmas [code] =
  Simple_Network_Rename_def
  [unfolded
    Simple_Network_Impl.var_set_compute
    Simple_Network_Impl.loc_set_compute
    Simple_Network_Impl.length_automata_eq_n_ps[symmetric]
  ]
 Simple_Network_Impl.clk_set'_def
 Simple_Network_Impl.clkp_set'_def
 Simple_Network_Rename.renum_automaton'_def

export_code Simple_Network_Rename in SML

concrete_definition renum_automaton' uses Simple_Network_Rename.renum_automaton'_alt_def

export_code renum_automaton' in SML

lemmas [code] =
  Simple_Network_Rename_Defs.renum_automaton_def
  Simple_Network_Rename_Defs.renum_cconstraint_def
  Simple_Network_Rename_Defs.map_cconstraint_def
  Simple_Network_Rename_Defs.renum_reset_def
  Simple_Network_Rename_Defs.renum_upd_def
  Simple_Network_Rename_Defs.renum_act_def
  Simple_Network_Rename_Defs.renum_exp_def

export_code Simple_Network_Rename_Defs.renum_automaton in SML

concrete_definition renum_automaton uses Simple_Network_Rename_Defs.renum_automaton_def

end (* Theory *)
theory Simple_Network_Language_Renaming
  imports Simple_Network_Language_Model_Checking
begin

context Simple_Network_Impl
begin

lemma N_p_trans_eq:
  "Simple_Network_Language.trans (N p) = set (fst (snd (automata ! p)))" if "p < n_ps"
  using mem_trans_N_iff[OF that] by auto

lemma loc_set_compute:
  "loc_set = \<Union> ((\<lambda>(_, t, _). \<Union> ((\<lambda>(l, _, _, _, _, _, l'). {l, l'}) ` set t)) ` set automata)"
  unfolding loc_set_def setcompr_eq_image
  apply (auto simp: N_p_trans_eq n_ps_def)
     apply (drule nth_mem, erule bexI[rotated], force)+
   apply (drule mem_nth, force)+
  done

lemma var_set_compute:
  "var_set =
  (\<Union>S \<in> (\<lambda>t. (fst \<circ> snd) ` set t) ` ((\<lambda>(_, t, _). t) `  set automata). \<Union>b \<in> S. vars_of_bexp b) \<union>
  (\<Union>S \<in> (\<lambda>t. (fst \<circ> snd o snd \<circ> snd \<circ> snd) ` set t) ` ((\<lambda>(_, t, _). t) `  set automata).
    \<Union>f \<in> S. \<Union> (x, e) \<in> set f. {x} \<union> vars_of_exp e)"
  unfolding var_set_def setcompr_eq_image
  by (rule arg_cong2[where f = "(\<union>)"]; auto simp: N_p_trans_eq n_ps_def,
     (drule nth_mem, erule bexI[rotated],
      metis (no_types, lifting) insert_iff mem_case_prodI prod.collapse)+,
      (drule mem_nth, force)+)

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
  "renum_bexp = map_bexp renum_vars id"

definition
  "renum_exp = map_exp renum_vars id"

definition
  "renum_upd = map (\<lambda>(x, upd). (renum_vars x, renum_exp upd))"

definition
  "renum_reset = map renum_clocks"

definition renum_automaton where
  "renum_automaton i \<equiv> \<lambda>(commited, trans, inv). let
    commited' = map (renum_states i) commited;
    trans' = map (\<lambda>(l, b, g, a, upd, r, l').
      (renum_states i l, renum_bexp b, renum_cconstraint g, renum_act a, renum_upd upd,
       renum_reset r,  renum_states i l')
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

lemma sem_states_eq:
  "sem.states = states"
  unfolding sem.states_def states_def n_ps_eq setcompr_eq_image
  by (auto simp: sem_N_eq N_eq;
      force simp:  renum.conv_automaton_def trans_def renum.automaton_of_def n_ps_def
            split: prod.splits)+

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

lemma map_of_NoneI:
  "map_of xs x = None" if "x \<notin> fst ` set xs"
  by (simp add: map_of_eq_None_iff that)


fun map_sexp ::
  "(nat \<Rightarrow> 's \<Rightarrow> 's1) \<Rightarrow> ('a \<Rightarrow> 'a1) \<Rightarrow> ('b \<Rightarrow> 'b1) \<Rightarrow> (nat, 's, 'a, 'b) sexp
    \<Rightarrow> (nat, 's1, 'a1, 'b1) sexp"
where
  "map_sexp f g h (not e) = not (map_sexp f g h e)" |
  "map_sexp f g h (and e1 e2) = and (map_sexp f g h e1) (map_sexp f g h e2)" |
  "map_sexp f g h (sexp.or e1 e2) = sexp.or (map_sexp f g h e1) (map_sexp f g h e2)" |
  "map_sexp f g h (imply e1 e2) = imply (map_sexp f g h e1) (map_sexp f g h e2)" |
  "map_sexp f g h (eq i x) = eq (g i) (h x)" |
  "map_sexp f g h (lt i x) = lt (g i) (h x)" |
  "map_sexp f g h (le i x) = le (g i) (h x)" |
  "map_sexp f g h (ge i x) = ge (g i) (h x)" |
  "map_sexp f g h (gt i x) = gt (g i) (h x)" |
  "map_sexp f g h (loc i x) = loc i (f i x)"

fun map_formula ::
  "(nat \<Rightarrow> 's \<Rightarrow> 's1) \<Rightarrow> ('a \<Rightarrow> 'a1) \<Rightarrow> ('b \<Rightarrow> 'b1)
  \<Rightarrow> (nat, 's, 'a, 'b) formula \<Rightarrow> (nat, 's1, 'a1, 'b1) formula"
where
  "map_formula f g h (formula.EX \<phi>) = formula.EX (map_sexp f g h \<phi>)" |
  "map_formula f g h (EG \<phi>) = EG (map_sexp f g h \<phi>)" |
  "map_formula f g h (AX \<phi>) = AX (map_sexp f g h \<phi>)" |
  "map_formula f g h (AG \<phi>) = AG (map_sexp f g h \<phi>)" |
  "map_formula f g h (Leadsto \<phi> \<psi>) = Leadsto (map_sexp f g h \<phi>) (map_sexp f g h \<psi>)"




locale Simple_Network_Rename' =
  Simple_Network_Rename_Defs where automata = automata for automata ::
    "('s list \<times> (('a :: countable) act, 's, 'c, int, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, int) cconstraint) list) list" +
  assumes inj_extend_renum_clocks: "inj renum_clocks"
      and renum_states_inj: "\<forall>p<n_ps. inj (renum_states p)"
      and bij_renum_vars: "bij renum_vars"
      and bounds'_var_set: "fst ` set bounds' \<subseteq> var_set"
begin

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

interpretation single: Bisimulation_Invariant
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

interpretation Bisimulation_Invariant
  "\<lambda>(L, s, u) (L', s', u'). step_u' sem L s u L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). step_u' renum.sem L s u L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). L' = map_index renum_states L \<and> s' = s o vars_inv \<and> u' = map_u u"
  "\<lambda> (L, s, u). L \<in> sem.states \<and> dom s \<subseteq> var_set" "\<lambda>_. True"
  sorry

lemmas renum_bisim = Bisimulation_Invariant_axioms

context
  fixes \<Phi> :: "(nat, 's, 'x, int) formula"
    and s\<^sub>0 :: "('x \<times> int) list"
    and L\<^sub>0 :: "'s list"
begin

definition \<Phi>' where
  "\<Phi>' = map_formula renum_states renum_vars id \<Phi>"

definition a\<^sub>0 where
  "a\<^sub>0 = (L\<^sub>0, map_of s\<^sub>0, \<lambda>_. 0)"

definition a\<^sub>0' where
  "a\<^sub>0' = (map_index renum_states L\<^sub>0, map_of (map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0), \<lambda>_. 0)"

context
  assumes L\<^sub>0_states: "L\<^sub>0 \<in> states"
  assumes s\<^sub>0_dom: "fst ` set s\<^sub>0 = var_set" and s\<^sub>0_distinct: "distinct (map fst s\<^sub>0)"
begin

(* Refine to subset of var_set? *)
lemma state_eq_aux:
  assumes "x \<notin> renum_vars ` var_set"
  shows "vars_inv x \<notin> var_set"
  unfolding vars_inv_def
proof clarsimp
  assume "the_inv renum_vars x \<in> var_set"
  then have "renum_vars (the_inv renum_vars x) = x"
    by (intro f_the_inv_f inj_renum_vars) (simp add: surj_renum_vars)
  with assms \<open>_ \<in> var_set\<close> show False
    by force
qed

lemma state_eq:
  assumes "fst ` set s\<^sub>0 = var_set" "distinct (map fst s\<^sub>0)"
  shows "map_of (map (\<lambda>(x, y). (renum_vars x, y)) s\<^sub>0) = (map_of s\<^sub>0 \<circ>\<circ>\<circ> the_inv_into) UNIV renum_vars"
    (is "?l = ?r")
proof (rule ext)
  fix x
  show "?l x = ?r x"
  proof (cases "x \<in> renum_vars ` fst ` set s\<^sub>0")
    case True
    then show ?thesis
      apply clarsimp
      apply (subst map_of_mapk_SomeI')
      subgoal
        using inj_renum_vars by (auto intro: inj_on_subset)
       apply (rule map_of_is_SomeI, rule assms, assumption)
      apply (simp add: the_inv_f_f[OF inj_renum_vars] s\<^sub>0_distinct)
      done
  next
    case False
    then have "vars_inv x \<notin> fst ` set s\<^sub>0"
      using state_eq_aux assms(1) unfolding vars_inv_def by auto
    with False show ?thesis
      apply -
      apply (frule map_of_NoneI)
      apply (simp add: vars_inv_def)
      apply (auto simp: map_of_eq_None_iff)
      done
  qed
qed

lemma start_equiv:
  "A_B.equiv' a\<^sub>0 a\<^sub>0'"
  unfolding A_B.equiv'_def a\<^sub>0_def a\<^sub>0'_def
  apply (clarsimp simp: vars_inv_def, intro conjI)
  subgoal
    by (intro state_eq s\<^sub>0_dom s\<^sub>0_distinct)
  subgoal
    unfolding map_u_def by auto
  subgoal
    unfolding sem_states_eq by (rule L\<^sub>0_states)
  subgoal
    using s\<^sub>0_dom dom_map_of_conv_image_fst[of s\<^sub>0] by fastforce
  done

lemma check_sexp_equiv:
  assumes "A_B.equiv' (L, s, u) (L', s', u')" "locs_of_sexp e \<subseteq> {0..<n_ps}"
  shows
  "check_sexp e L (the \<circ> s) \<longleftrightarrow>
   check_sexp (map_sexp renum_states renum_vars id e) L' (the \<circ> s')"
  using assms unfolding A_B.equiv'_def
  by (induction e)
     (simp add:
       inj_eq sem.states_lengthD renum_states_inj vars_inv_def the_inv_f_f[OF inj_renum_vars])+

lemma models_iff:
  "sem,a\<^sub>0 \<Turnstile> \<Phi> = renum.sem,a\<^sub>0' \<Turnstile> \<Phi>'" if "locs_of_formula \<Phi> \<subseteq> {0..<n_ps}"
proof (cases \<Phi>)
  case (EX x1)
  show ?thesis
    using that check_sexp_equiv start_equiv unfolding models_def \<Phi>'_def
    by (simp only: map_formula.simps EX formula.case) (rule Ex_ev_iff, auto)
next
  case (EG x2)
  show ?thesis
    using that check_sexp_equiv start_equiv unfolding models_def \<Phi>'_def
    by (simp only: map_formula.simps EG formula.case Graph_Defs.Ex_alw_iff Not_eq_iff)
       (rule Alw_ev_iff, auto)
next
  case (AX x3)
  show ?thesis
    using that check_sexp_equiv start_equiv unfolding models_def \<Phi>'_def
    by (simp only: map_formula.simps AX formula.case) (rule Alw_ev_iff, auto)
next
  case (AG x4)
  show ?thesis
    using that check_sexp_equiv start_equiv unfolding models_def \<Phi>'_def
    by (simp only: map_formula.simps AG formula.case Graph_Defs.Alw_alw_iff Not_eq_iff)
       (rule Ex_ev_iff, auto)
next
  case (Leadsto x51 x52)
  show ?thesis
    using that check_sexp_equiv start_equiv unfolding models_def \<Phi>'_def
    by (simp only: map_formula.simps Leadsto formula.case) (rule Leadsto_iff, auto)
qed

lemma has_deadlock_iff:
  "has_deadlock sem a\<^sub>0 \<longleftrightarrow> has_deadlock renum.sem a\<^sub>0'"
  unfolding has_deadlock_def using start_equiv by (intro deadlock_iff, unfold A_B.equiv'_def) auto

end (* Context for assumptions *)

end (* Context for formula *)

end (* Simple Network Rename' *)

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
  broadcast bounds'
  renum_acts
  "extend_bij renum_vars var_set"
  "extend_bij renum_clocks clk_set'"
  "\<lambda>p. extend_bij (renum_states p) loc_set"
  automata
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
    subgoal state
      unfolding rename.renum_bexp_def renum_bexp_def
      apply (rule bexp.map_cong_pred, rule HOL.refl, clarsimp simp: pred_bexp_def)
      apply (subst renum_vars_bij_extends)
       apply (fastforce dest: nth_mem simp: var_set_compute set1_bexp_vars_of_bexp)+
      done
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

end (* Simple_Network_Rename *)

locale Simple_Network_Rename_Formula =
  Simple_Network_Rename where automata = automata for automata ::
    "('s list \<times> (('a :: countable) act, 's, 'c, int, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, int) cconstraint) list) list" +
  fixes \<Phi> :: "(nat, 's, 'x, int) formula"
    and s\<^sub>0 :: "('x \<times> int) list"
    and L\<^sub>0 :: "'s list"
  assumes L\<^sub>0_states: "L\<^sub>0 \<in> states"
      and s\<^sub>0_dom: "fst ` set s\<^sub>0 = var_set" and s\<^sub>0_distinct: "distinct (map fst s\<^sub>0)"
  assumes formula_dom:
    "set2_formula \<Phi> \<subseteq> loc_set"
    "locs_of_formula \<Phi> \<subseteq> {0..<n_ps}"
    "vars_of_formula \<Phi> \<subseteq> var_set"
begin

definition \<Phi>' where
  "\<Phi>' = map_formula renum_states renum_vars id \<Phi>"

definition a\<^sub>0 where
  "a\<^sub>0 = (L\<^sub>0, map_of s\<^sub>0, \<lambda>_. 0)"

definition a\<^sub>0' where
  "a\<^sub>0' = (map_index renum_states L\<^sub>0, map_of (map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0), \<lambda>_. 0)"

lemma sexp_eq:
  assumes
    \<open>vars_of_sexp e \<subseteq> var_set\<close>
    \<open>set2_sexp e \<subseteq> loc_set\<close>
    \<open>locs_of_sexp e \<subseteq> {0..<n_ps}\<close>
  shows \<open>map_sexp (\<lambda>p. extend_bij (renum_states p) loc_set) (extend_bij renum_vars var_set) id e =
         map_sexp renum_states renum_vars id e\<close>
  using assms by (induction e; clarsimp simp: renum_states_extend)

lemma formula_eq:
  "rename.\<Phi>' \<Phi> = \<Phi>'"
  using formula_dom unfolding rename.\<Phi>'_def \<Phi>'_def by (induction \<Phi>; clarsimp simp: sexp_eq)

lemma a\<^sub>0_eq:
  "rename.a\<^sub>0 s\<^sub>0 L\<^sub>0 = a\<^sub>0"
  unfolding a\<^sub>0_def rename.a\<^sub>0_def ..

lemma state_eq:
  "map_of (map (\<lambda>(x, y). (extend_bij renum_vars var_set x, y)) s\<^sub>0) =
    map_of (map (\<lambda>(x, y). (renum_vars x, y)) s\<^sub>0)"
  using s\<^sub>0_dom by - (rule arg_cong, auto intro: renum_vars_bij_extends)

lemma L\<^sub>0_dom:
  "length L\<^sub>0 = n_ps" "set L\<^sub>0 \<subseteq> loc_set"
  using L\<^sub>0_states by (auto intro!: states_loc_setD)

lemma rename_a\<^sub>0'_eq:
  "rename.a\<^sub>0' s\<^sub>0 L\<^sub>0 = a\<^sub>0'"
  unfolding a\<^sub>0'_def rename.a\<^sub>0'_def
  apply (clarsimp, rule conjI)
  subgoal
    using L\<^sub>0_dom by (auto intro!: map_index_cong renum_states_extend)
  subgoal
    unfolding vars_inv_def using s\<^sub>0_dom s\<^sub>0_distinct
    by (auto simp: state_eq Simple_Network_Rename_Defs.vars_inv_def)
  done

lemma models_iff:
  "renum.sem,a\<^sub>0' \<Turnstile> \<Phi>' \<longleftrightarrow> sem,a\<^sub>0 \<Turnstile> \<Phi>"
  by (rule sym)
     (intro
      rename.models_iff[of L\<^sub>0 s\<^sub>0 \<Phi>, unfolded rename_sem_eq formula_eq a\<^sub>0_eq rename_a\<^sub>0'_eq]
      formula_dom L\<^sub>0_states s\<^sub>0_distinct, simp add: s\<^sub>0_dom
      )

lemma has_deadlock_iff:
  "has_deadlock renum.sem a\<^sub>0' \<longleftrightarrow> has_deadlock sem a\<^sub>0"
  by (rule sym)
     (intro
      rename.has_deadlock_iff[of L\<^sub>0 s\<^sub>0, unfolded rename_sem_eq formula_eq a\<^sub>0_eq rename_a\<^sub>0'_eq]
      formula_dom L\<^sub>0_states s\<^sub>0_distinct, simp add: s\<^sub>0_dom
     )

lemma (in Simple_Network_Rename_Defs) conv_automaton_of:
  "Simple_Network_Language.conv_A (renum.automaton_of A) =
   renum.automaton_of (renum.conv_automaton A)"
  unfolding renum.automaton_of_def renum.conv_automaton_def
    Simple_Network_Language.conv_A_def
  by (force
      simp: default_map_of_alt_def map_of_map Simple_Network_Language.conv_t_def split: prod.splits
     )

lemma N_eq_sem:
  "Simple_Network_Language_Model_Checking.N broadcast automata bounds' = sem"
  unfolding conv_alt_def
  by safe (rule nth_equalityI; simp add: conv_N_eq N_eq sem_N_eq conv_automaton_of n_ps_def)

lemma rename_N_eq_sem:
  "Simple_Network_Language_Model_Checking.N
  (map renum_acts broadcast)
  (map_index renum_automaton automata)
  (map (\<lambda>(a,b,c). (renum_vars a, b, c)) bounds')
  = renum.sem"
  unfolding renum.conv_alt_def
  by safe (rule nth_equalityI; simp add: conv_N_eq N_eq sem_N_eq conv_automaton_of n_ps_def)

lemmas models_iff' = models_iff[folded rename_N_eq_sem N_eq_sem,unfolded a\<^sub>0_def a\<^sub>0'_def \<Phi>'_def]

lemmas has_deadlock_iff' =
  has_deadlock_iff[folded rename_N_eq_sem N_eq_sem,unfolded a\<^sub>0_def a\<^sub>0'_def \<Phi>'_def]

end (* Simple_Network_Rename_Formula *)

end (* Theory *)
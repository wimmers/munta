theory Simple_Network_Language_Renaming
  imports Simple_Network_Language_Model_Checking
begin

(* XXX This is missing from the standard library *)
lemma image_cong_simp:
  fixes N :: "'b set"
  assumes "M = N" and "\<And>x. x \<in> N =simp=> f x = g x"
  shows "f ` M = g ` N"
  using assms by (simp cong: image_cong add: simp_implies_def)

(* XXX All this stuff is duplicated *)
context Simple_Network_Impl_Defs
begin

lemma N_eq:
  \<open>N i = automaton_of (automata ! i)\<close> if \<open>i < n_ps\<close>
  using that unfolding N_def n_ps_def fst_conv snd_conv by (intro nth_map; simp)

(* XXX Remove? *)
lemma covn_N_eq:
  \<open>N i = automaton_of (automata ! i)\<close> if \<open>i < n_ps\<close>
  using that unfolding N_def n_ps_def fst_conv snd_conv by (intro nth_map; simp)

end

context Simple_Network_Impl_Defs
begin

lemma dom_bounds: "dom bounds = fst ` set bounds'"
  unfolding bounds_def by (simp add: dom_map_of_conv_image_fst)

lemma mem_trans_N_iff:
  "t \<in> Simple_Network_Language.trans (N i) \<longleftrightarrow> t \<in> set (fst (snd (automata ! i)))" if "i < n_ps"
  unfolding N_eq[OF that] by (auto split: prod.splits simp: automaton_of_def trans_def)

lemma length_automata_eq_n_ps:
  "length automata = n_ps"
  unfolding n_ps_def by simp

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

end (* Simple Network Impl Defs *)


context Simple_Network_Impl
begin

lemma sem_bounds_eq: "sem.bounds = bounds"
  unfolding sem.bounds_def bounds_def unfolding sem_def by simp

lemma n_ps_eq[simp]:
  "sem.n_ps = n_ps"
  unfolding n_ps_def sem.n_ps_def unfolding sem_def by auto

lemma sem_loc_set_eq:
  "sem.loc_set = loc_set"
  unfolding sem.loc_set_def loc_set_def n_ps_eq setcompr_eq_image
  apply (simp add: sem_N_eq N_eq)
  apply (rule arg_cong2[where f = "(\<union>)"])
   apply (auto;
      force split: prod.splits simp:  conv_automaton_def trans_def automaton_of_def n_ps_def)+
  done

lemma sem_states_eq:
  "sem.states = states"
  unfolding sem.states_def states_def n_ps_eq setcompr_eq_image
  by (auto simp: sem_N_eq N_eq;
      force simp:  conv_automaton_def trans_def automaton_of_def n_ps_def split: prod.splits)+

end (* Simple Network Impl *)


locale Simple_Network_Rename_Defs =
  Simple_Network_Impl_Defs automata broadcast bounds' for automata ::
    "('s list \<times> (('a :: countable) act, 's, 'c, 't, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, 't) cconstraint) list) list"
    and broadcast bounds' +
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
  "renum_bexp = map_bexp renum_vars"

definition
  "renum_exp = map_exp renum_vars"

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

sublocale renum: Simple_Network_Impl_Defs
  "map_index renum_automaton automata"
  "map renum_acts broadcast"
  "map (\<lambda>(a,p). (renum_vars a, p)) bounds'"
  .

lemma renum_n_ps_simp[simp]:
  "renum.n_ps = n_ps"
  unfolding n_ps_def renum.n_ps_def by simp

end (* Simple Network Rename Defs' *)


locale Simple_Network_Rename_Defs_int =
  Simple_Network_Rename_Defs automata +
  Simple_Network_Impl automata
  for automata ::
    "('s list \<times> (('a :: countable) act, 's, 'c, int, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, int) cconstraint) list) list"
begin

sublocale renum: Simple_Network_Impl
  "map_index renum_automaton automata"
  "map renum_acts broadcast"
  "map (\<lambda>(a,p). (renum_vars a, p)) bounds'"
  .

end (* Simple Network Rename Defs int *)

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

lemma bij_f_the_inv_f:
  "f (the_inv f x) = x" if "bij f"
  using that f_the_inv_f unfolding bij_def by (simp add: f_the_inv_f)


fun map_sexp ::
  "(nat \<Rightarrow> 's \<Rightarrow> 's1) \<Rightarrow> ('a \<Rightarrow> 'a1) \<Rightarrow> ('b \<Rightarrow> 'b1) \<Rightarrow> (nat, 's, 'a, 'b) sexp
    \<Rightarrow> (nat, 's1, 'a1, 'b1) sexp"
  where
  "map_sexp _ _ _ sexp.true = sexp.true" |
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


locale Simple_Network_Impl_real =
  fixes automata ::
    "('s list \<times> ('a act, 's, 'c, real, 'x, int) transition list
      \<times> ('s \<times> ('c, real) cconstraint) list) list"
    and broadcast :: "'a list"
    and bounds' :: "('x \<times> (int \<times> int)) list"
begin

sublocale Simple_Network_Impl_Defs automata broadcast bounds' .

definition "sem \<equiv> (set broadcast, map automaton_of automata, map_of bounds')"

sublocale sem: Prod_TA_sem sem .

lemma sem_N_eq:
  "sem.N p = automaton_of (automata ! p)" if \<open>p < n_ps\<close>
  using that unfolding sem.N_def n_ps_def unfolding sem_def fst_conv snd_conv
  by (subst nth_map) auto

lemma sem_bounds_eq: "sem.bounds = bounds"
  unfolding sem.bounds_def bounds_def unfolding sem_def by simp

lemma n_ps_eq[simp]:
  "sem.n_ps = n_ps"
  unfolding n_ps_def sem.n_ps_def unfolding sem_def by auto

lemma sem_loc_set_eq:
  "sem.loc_set = loc_set"
  unfolding sem.loc_set_def loc_set_def n_ps_eq setcompr_eq_image by (simp add: sem_N_eq N_eq)

lemma sem_states_eq:
  "sem.states = states"
  unfolding sem.states_def states_def n_ps_eq setcompr_eq_image
  by (auto simp: sem_N_eq N_eq;
      force simp:  conv_automaton_def trans_def automaton_of_def n_ps_def split: prod.splits)+

lemma sem_state_guard_eq:
  "(fst \<circ> snd) ` trans (sem.N p) = (fst \<circ> snd) ` trans (N p)" if "p < n_ps"
  unfolding sem_N_eq[OF \<open>p < n_ps\<close>] N_eq[OF \<open>p < n_ps\<close>]
  unfolding automaton_of_def conv_automaton_def trans_def
  by (force split: prod.splits)

lemma sem_state_update_eq:
  "(fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd) ` trans (sem.N p) = (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd) ` trans (N p)"
  if "p < n_ps"
  unfolding sem_N_eq[OF \<open>p < n_ps\<close>] N_eq[OF \<open>p < n_ps\<close>]
  unfolding automaton_of_def conv_automaton_def trans_def
  by (force split: prod.splits)

lemma sem_var_set_eq:
  "sem.var_set = var_set"
  unfolding sem.var_set_def var_set_def n_ps_eq using sem_state_guard_eq sem_state_update_eq
  by (simp cong: image_cong_simp add: setcompr_eq_image)

end

context Simple_Network_Impl
begin

lemma sem_state_guard_eq:
  "(fst \<circ> snd) ` trans (sem.N p) = (fst \<circ> snd) ` trans (N p)" if "p < n_ps"
  unfolding sem_N_eq[OF \<open>p < n_ps\<close>] N_eq[OF \<open>p < n_ps\<close>]
  unfolding automaton_of_def conv_automaton_def trans_def
  by (force split: prod.splits)

lemma sem_state_update_eq:
  "(fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd) ` trans (sem.N p) = (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd) ` trans (N p)"
  if "p < n_ps"
  unfolding sem_N_eq[OF \<open>p < n_ps\<close>] N_eq[OF \<open>p < n_ps\<close>]
  unfolding automaton_of_def conv_automaton_def trans_def
  by (force split: prod.splits)

lemma sem_var_set_eq:
  "sem.var_set = var_set"
  unfolding sem.var_set_def var_set_def n_ps_eq using sem_state_guard_eq sem_state_update_eq
  by (simp cong: image_cong_simp add: setcompr_eq_image)

end

locale Simple_Network_Rename_Defs_real =
  Simple_Network_Rename_Defs automata +
  Simple_Network_Impl_real automata
  for automata ::
    "('s list \<times> (('a :: countable) act, 's, 'c, real, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, real) cconstraint) list) list"
begin

sublocale renum: Simple_Network_Impl_real
  "map_index renum_automaton automata"
  "map renum_acts broadcast"
  "map (\<lambda>(a,p). (renum_vars a, p)) bounds'"
  .

end (* Simple Network Rename Defs *)

locale Simple_Network_Rename' =
  Simple_Network_Rename_Defs where automata = automata for automata ::
    "('s list \<times> (('a :: countable) act, 's, 'c, 't, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, 't) cconstraint) list) list" +
  assumes bij_renum_clocks: "bij renum_clocks"
      and renum_states_inj: "\<forall>p<n_ps. inj (renum_states p)"
      and bij_renum_vars: "bij renum_vars"
      and bounds'_var_set: "fst ` set bounds' = var_set"
      and inj_renum_acts: "inj renum_acts"

locale Simple_Network_Rename_real =
  Simple_Network_Rename_Defs_real where automata = automata +
  Simple_Network_Rename' where automata = automata
  for automata ::
    "('s list \<times> (('a :: countable) act, 's, 'c, real, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, real) cconstraint) list) list"
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
  unfolding clocks_inv_def by (subst the_inv_f_f; rule bij_renum_clocks[THEN bij_is_inj] HOL.refl)

lemma map_u_renum_cconstraint_clock_valI:
  "map_u u \<turnstile> renum_cconstraint cc" if "u \<turnstile> cc"
  using that
  unfolding clock_val_def list_all_length
  unfolding renum_cconstraint_def map_cconstraint_def
  unfolding map_u_def
  apply clarsimp
  subgoal for n
    by (cases "cc ! n") (auto 4 4 simp: clocks_inv_inv split: acconstraint.split)
  done

(*
lemma map_u_conv_renum_cconstraint_clock_valI:
  "map_u u \<turnstile> map conv_ac (renum_cconstraint cc)" if "u \<turnstile> map conv_ac cc"
  using map_u_renum_cconstraint_clock_valI[OF that]
  by (simp add: renum_cconstraint_def map_cconstraint_def acconstraint.map_comp comp_def)
*)

lemma map_u_renum_cconstraint_clock_valD:
  "u \<turnstile> cc" if "map_u u \<turnstile> renum_cconstraint cc"
  using that
  unfolding clock_val_def list_all_length
  unfolding renum_cconstraint_def map_cconstraint_def
  unfolding map_u_def
  apply clarsimp
  subgoal for n
    by (cases "cc ! n") (auto 4 4 simp: clocks_inv_inv split: acconstraint.split)
  done

(*
lemma map_u_conv_renum_cconstraint_clock_valD:
  "u \<turnstile> map conv_ac cc" if "map_u u \<turnstile> map conv_ac (renum_cconstraint cc)"
  using map_u_renum_cconstraint_clock_valD[of u "map conv_ac cc"] that
  by (simp add: renum_cconstraint_def map_cconstraint_def acconstraint.map_comp comp_def)
*)

(*
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
*)

lemma inj_renum_states: "inj (renum_states p)" if "p < n_ps"
  using renum_states_inj \<open>p < n_ps\<close> by blast

lemma inv_renum_sem_I:
  assumes
    "u \<turnstile> Simple_Network_Language.inv (sem.N p) l" "p < n_ps" "l \<in> loc_set"
  shows
    "map_u u \<turnstile> Simple_Network_Language.inv (renum.sem.N p) (renum_states p l)"
  using assms
  unfolding inv_def
  apply -
  apply (subst (asm) sem_N_eq, assumption)
  apply (subst renum.sem_N_eq, subst renum_n_ps_simp, assumption)
  apply (subst nth_map_index, simp add: n_ps_def)
  unfolding conv_automaton_def automaton_of_def
  apply (auto split: prod.split_asm simp: renum_automaton_def comp_def)
  unfolding aux_1
  apply (subst default_map_of_map[where x = "[]"])
  subgoal
    by (intro inj_renum_states \<open>p < n_ps\<close>)
   apply (simp add: renum_cconstraint_def map_cconstraint_def; fail)
  apply (erule map_u_renum_cconstraint_clock_valI)
  done

lemma inv_renum_sem_D:
  assumes
    "map_u u \<turnstile> Simple_Network_Language.inv (renum.sem.N p) (renum_states p l)"
    "p < n_ps" "l \<in> loc_set"
  shows
    "u \<turnstile> Simple_Network_Language.inv (sem.N p) l"
  using assms
  unfolding inv_def
  apply -
  apply (subst sem_N_eq, assumption)
  apply (subst (asm) renum.sem_N_eq, subst renum_n_ps_simp, assumption)
  apply (subst (asm) nth_map_index, simp add: n_ps_def)
  unfolding conv_automaton_def automaton_of_def
  apply (auto split: prod.split simp: renum_automaton_def comp_def)
  unfolding aux_1
  apply (subst (asm) default_map_of_map[where x = "[]"])
  subgoal
    by (intro inj_renum_states \<open>p < n_ps\<close>)
   apply (simp add: renum_cconstraint_def map_cconstraint_def; fail)
  apply (erule map_u_renum_cconstraint_clock_valD)
  done

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

lemma dom_vars_invD:
  assumes "x \<in> dom (s \<circ> vars_inv)"
  shows "x \<in> renum_vars ` dom s" (is ?A) and "the_inv renum_vars x \<in> dom s" (is ?B)
proof -
  show ?A
    using assms unfolding vars_inv_def dom_the_inv_comp[OF inj_renum_vars surj_renum_vars] .
  then show ?B
    apply (elim imageE)
    apply simp
    apply (subst the_inv_f_f, rule inj_renum_vars, assumption)
    done
qed

lemma bounded_renumI:
  assumes "bounded (map_of bounds') s"
  shows "bounded (map_of (map (\<lambda>(a, y). (renum_vars a, y)) bounds')) (s o vars_inv)"
  using assms unfolding bounded_def
  apply elims
  apply intros
  subgoal
    unfolding dom_map_of_conv_image_fst vars_inv_def
    by (auto intro!: image_cong simp: dom_the_inv_comp[OF inj_renum_vars surj_renum_vars] image_comp)
  subgoal for x
    apply (frule dom_vars_invD)
    apply (frule dom_vars_invD(2))
    apply (drule bspec, assumption)
    apply (auto simp: map_of_inv_map[OF inj_renum_vars surj_renum_vars] vars_inv_def)
    done
  subgoal for x
    apply (frule dom_vars_invD)
    apply (frule dom_vars_invD(2))
    apply (drule bspec, assumption)
    apply (auto simp: map_of_inv_map[OF inj_renum_vars surj_renum_vars] vars_inv_def)
    done
  done

lemma map_of_renum_vars_simp:
  assumes
    "dom (s o vars_inv)
     = dom (map_of (map (\<lambda>(a, y). (renum_vars a, y)) bounds'))"
    "x \<in> dom s" "dom s \<subseteq> var_set"
  shows "map_of (map (\<lambda>(a, y). (renum_vars a, y)) bounds') (renum_vars x) = map_of bounds' x"
proof -
  have *:
    "map (\<lambda>(a, y). (renum_vars a, y)) bounds' = map (\<lambda>(a, y). (renum_vars a, y)) bounds'"
    by auto
  have "x \<in> dom (map_of bounds')"
    unfolding dom_map_of_conv_image_fst
    using assms
    unfolding vars_inv_def
    apply -
    apply (subst (asm) dom_the_inv_comp, rule inj_renum_vars, rule surj_renum_vars)
    apply (subst (asm) dom_map_of_map)
    apply auto
    apply (subst (asm) inj_on_image_eq_iff[OF inj_renum_vars])
    by auto
  then obtain y where "map_of bounds' x = Some y"
    by auto
  then show ?thesis
    by (subst map_of_mapk_SomeI) (auto intro: inj_renum_vars)
qed

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
      apply (subst (asm) dom_the_inv_comp[OF inj_renum_vars surj_renum_vars])
      apply (subst (asm) dom_map_of_map)
      apply (rule inj_image_eqI[OF inj_renum_vars], simp add: dom_map_of_conv_image_fst)
      done
    subgoal for x
      using assms(2) unfolding vars_inv_def
      apply (subst (asm) (2) dom_the_inv_comp[OF inj_renum_vars surj_renum_vars])
      apply (drule bspec, erule imageI)
      apply (simp add: the_inv_f_f[OF inj_renum_vars] map_of_renum_vars_simp[unfolded vars_inv_def])
      done
    subgoal for x
      using assms(2) unfolding vars_inv_def
      apply (subst (asm) (2) dom_the_inv_comp[OF inj_renum_vars surj_renum_vars])
      apply (drule bspec, erule imageI)
      apply (simp add: the_inv_f_f[OF inj_renum_vars] map_of_renum_vars_simp[unfolded vars_inv_def])
      done
    done
qed

lemma dom_bounds_var_set: "dom sem.bounds = var_set"
  unfolding dom_bounds sem_bounds_eq using bounds'_var_set by blast

lemma sem_states_loc_setD: "L ! p \<in> loc_set" if "p < length automata" "L \<in> sem.states" for L p
  using that sem_loc_set_eq sem.states_loc_set by (force simp: n_ps_def)

lemma trans_N_renumD:
  assumes "(l, b, g, a, f, r, l') \<in> Simple_Network_Language.trans (N p)" "p < n_ps"
  shows "(renum_states p l, renum_bexp b, renum_cconstraint g, renum_act a, renum_upd f, renum_reset r, renum_states p l')
  \<in> Simple_Network_Language.trans (renum.N p)"
  using assms
  unfolding mem_trans_N_iff[OF assms(2)] renum.mem_trans_N_iff[unfolded renum_n_ps_simp, OF assms(2)]
  by (force split: prod.split simp: renum_automaton_def n_ps_def)

lemma match_assumption2:
  assumes "P a1 b1" "a1 = a" "b1 = b" shows "P a b"
  using assms by auto

lemma inj_pair:
  assumes "inj f" "inj g"
  shows "inj (\<lambda>(a, b). (f a, g b))"
  using assms unfolding inj_on_def by auto

lemma injective_functions:
  "inj renum_reset" "inj renum_upd" "inj renum_act" "inj renum_cconstraint" "inj renum_bexp"
  "\<And>p. p < length automata \<Longrightarrow> inj (renum_states p)"
  subgoal
    unfolding renum_reset_def using bij_renum_clocks[THEN bij_is_inj] by simp
  subgoal
    unfolding renum_upd_def renum_exp_def using bij_renum_vars[THEN bij_is_inj]
    by (intro inj_pair exp.inj_map inj_mapI)
  subgoal
    unfolding renum_act_def using inj_renum_acts by (rule act.inj_map)
  subgoal
    unfolding renum_cconstraint_def map_cconstraint_def
    by (intro inj_mapI acconstraint.inj_map bij_renum_clocks bij_is_inj bij_id)
  subgoal
    unfolding renum_bexp_def by (intro bexp.inj_map inj_renum_vars)
  subgoal
    by (rule inj_renum_states, simp add: n_ps_def)
  done

lemma trans_N_renumI:
  assumes "(renum_states p l, renum_bexp b, renum_cconstraint g, renum_act a, renum_upd f, renum_reset r, renum_states p l')
  \<in> Simple_Network_Language.trans (renum.N p)"  "p < n_ps"
  shows "(l, b, g, a, f, r, l') \<in> Simple_Network_Language.trans (N p)"
  using assms
  unfolding mem_trans_N_iff[OF assms(2)] renum.mem_trans_N_iff[unfolded renum_n_ps_simp, OF assms(2)]
  apply (clarsimp split: prod.split_asm simp: renum_automaton_def n_ps_def)
  apply (fo_rule match_assumption2, assumption)
   apply (auto elim!: injD[rotated, THEN sym] intro: injective_functions)
  done

lemma trans_sem_N_renumD:
  assumes "(l, b, g, a, f, r, l') \<in> Simple_Network_Language.trans (sem.N p)" "p < n_ps"
  shows "(renum_states p l, renum_bexp b, renum_cconstraint g, renum_act a, renum_upd f, renum_reset r, renum_states p l')
  \<in> Simple_Network_Language.trans (renum.sem.N p)"
  using assms(1)
  unfolding sem_N_eq[OF assms(2)] renum.sem_N_eq[unfolded renum_n_ps_simp, OF assms(2)]
  using \<open>p < n_ps\<close>
  apply (simp only: N_eq[symmetric])
  apply (drule (1) trans_N_renumD)
  apply (subst renum.N_eq[symmetric])
   apply (subst renum_n_ps_simp; assumption)
  .

lemma renum_acconstraint_eq_convD:
  assumes "map_acconstraint renum_clocks id g = conv_ac g'"
  obtains g1 where "g = conv_ac g1" "g' = map_acconstraint renum_clocks id g1"
  subgoal premises
    using assms
    apply (cases g'; cases g; clarsimp)
    subgoal for m c
      by (rule that[of "acconstraint.LT c m"]; simp)
    subgoal for m c
      by (rule that[of "acconstraint.LE c m"]; simp)
    subgoal for m c
      by (rule that[of "acconstraint.EQ c m"]; simp)
    subgoal for m c
      by (rule that[of "acconstraint.GT c m"]; simp)
    subgoal for m c
      by (rule that[of "acconstraint.GE c m"]; simp)
    done
  done

lemma renum_cconstraint_eq_convD:
  assumes "renum_cconstraint g = conv_cc g'"
  obtains g1 where "g = conv_cc g1" "g' = renum_cconstraint g1"
proof -
  let ?f = "\<lambda>(ac, ac'). SOME ac1. ac = conv_ac ac1 \<and> ac' = map_acconstraint renum_clocks id ac1"
  let ?g = "map ?f (zip g g')"
  from assms have "length g = length g'"
    unfolding renum_cconstraint_def map_cconstraint_def by -(drule arg_cong[where f = length], simp)
  then have "g = conv_cc ?g \<and> g' = renum_cconstraint ?g"
    using assms
    by (simp add: comp_def renum_cconstraint_def map_cconstraint_def)
       (induction rule: list_induct2; simp; elim conjE renum_acconstraint_eq_convD; smt someI)
  then show ?thesis
    by (blast intro: that)
qed

lemma trans_sem_N_renumI:
  assumes "(renum_states p l, renum_bexp b, renum_cconstraint g, renum_act a, renum_upd f, renum_reset r, renum_states p l')
  \<in> Simple_Network_Language.trans (renum.sem.N p)" "p < n_ps"
  shows "(l, b, g, a, f, r, l') \<in> Simple_Network_Language.trans (sem.N p)"
  using assms(1) \<open>p < n_ps\<close>
  unfolding sem_N_eq[OF assms(2)] renum.sem_N_eq[unfolded renum_n_ps_simp, OF assms(2)]
  by (simp add: N_eq[symmetric] renum.N_eq[symmetric, unfolded renum_n_ps_simp] trans_N_renumI)

lemma trans_sem_N_renumI':
  assumes "(renum_states p l, b, g, a, f, r, l')
  \<in> Simple_Network_Language.trans (renum.sem.N p)" "p < n_ps"
  shows "\<exists> b' g' a' f' r' l1.
    (l, b', g', a', f', r', l1) \<in> Simple_Network_Language.trans (sem.N p)
    \<and> b = renum_bexp b' \<and> g = renum_cconstraint g' \<and> a = renum_act a' \<and> f = renum_upd f'
    \<and> r = renum_reset r' \<and> l' = renum_states p l1"
proof -
  obtain b' g' a' f' r' l1 where "b = renum_bexp b'" "g = renum_cconstraint g'" "f = renum_upd f'"
    "a = renum_act a'" "r = renum_reset r'" "l' = renum_states p l1"
    using assms
    unfolding sem_N_eq[OF assms(2)] renum.sem_N_eq[unfolded renum_n_ps_simp, OF assms(2)]
    apply (subst (asm) nth_map_index)
    subgoal
      by (simp add: n_ps_def)
    unfolding renum_automaton_def automaton_of_def trans_def by (auto split: prod.split_asm)
  with assms show ?thesis
    by (fastforce dest!: trans_sem_N_renumI)
qed

lemma fold_sem_N:
  "map automaton_of automata ! p = sem.N p"
  by (simp add: sem_def)

lemma fold_renum_sem_N:
  "map automaton_of (map_index renum_automaton automata) ! p = renum.sem.N p"
  by (simp add: renum.sem_def)

lemma fold_inv_sem_N:
  "inv (automaton_of (automata ! p)) l = inv (sem.N p) l" if "p < length automata"
  using that unfolding sem.N_def unfolding sem_def automaton_of_def by simp

lemma fold_inv_renum_sem_N:
  "inv (automaton_of (renum_automaton p (automata ! p))) l = inv (renum.sem.N p) l"
  if "p < length automata"
  using that unfolding renum.sem.N_def unfolding renum.sem_def automaton_of_def by simp

lemma commited_renum_eq:
  "commited (renum.sem.N p) = renum_states p ` commited (sem.N p)" if "p < n_ps"
  unfolding
    commited_def sem_N_eq[OF \<open>p < n_ps\<close>] renum.sem_N_eq[unfolded renum_n_ps_simp, OF \<open>p < n_ps\<close>]
  apply (subst nth_map_index)
  subgoal
    using \<open>p < n_ps\<close> by (simp add: n_ps_def)
  unfolding automaton_of_def conv_automaton_def renum_automaton_def by (simp split: prod.split)

lemma renum_sem_n_ps_eq:
  "renum.sem.n_ps = n_ps"
  unfolding renum.n_ps_eq renum_n_ps_simp ..

lemma check_bexp_renumD:
  "check_bexp s b bv \<Longrightarrow> check_bexp (s o vars_inv) (renum_bexp b) bv"
and is_val_renumD:
  "is_val s e v \<Longrightarrow> is_val (s o vars_inv) (renum_exp e) v"
  apply (induction rule: check_bexp_is_val.inducts)
  apply (auto
      intro: check_bexp_is_val.intros
      simp: renum_bexp_def renum_exp_def vars_inv_def the_inv_f_f[OF inj_renum_vars])
  using is_val.simps apply fastforce+
  done

method solve_case =
  auto 
    intro: check_bexp_is_val.intros
    simp: renum_bexp_def renum_exp_def vars_inv_def the_inv_f_f[OF inj_renum_vars];
  fail
| use is_val.simps in fastforce

lemma check_bexp_renumI:
  "check_bexp (s o vars_inv) (renum_bexp b) bv \<Longrightarrow> check_bexp s b bv"
  and is_val_renumI:
  "is_val (s o vars_inv) (renum_exp e) v \<Longrightarrow> is_val s e v"
  apply (induction
      "s o vars_inv" "renum_bexp b" bv and "s o vars_inv" "renum_exp e" _
      arbitrary: b and e rule: check_bexp_is_val.inducts)
  subgoal for b
    by (cases b; solve_case)
  subgoal for e bv b
    by (cases b; solve_case)
  subgoal for e1 a e2 bv b
    by (cases b; solve_case)
  subgoal for e1 a e2 bv b
    by (cases b; solve_case)
  subgoal for e1 a e2 bv b
    by (cases b; solve_case)
  subgoal for a v bv x b
    by (cases b; solve_case)
  subgoal for a v bv x b
    by (cases b; solve_case)
  subgoal for a v bv x b
    by (cases b; solve_case)
  subgoal for a v bv x b
    by (cases b; solve_case)
  subgoal for a v bv x b
    by (cases b; solve_case)
  subgoal for c e
    by (cases e; solve_case)
  subgoal for x v e
    by (cases e; solve_case)
  subgoal for e1 v1 e2 v2 b bv e
    by (auto simp: renum_bexp_def renum_exp_def; cases e; solve_case)
  subgoal for e1 v1 e2 v2 f e
    by (auto simp: renum_bexp_def renum_exp_def; cases e; solve_case)
  subgoal for e1 v f e
    by (cases e; solve_case)
  done

lemma renum_reset_map_u:
  "[renum_reset r\<rightarrow>0]map_u u = map_u ([r\<rightarrow>0]u)"
  unfolding map_u_def
  apply (rule ext)
  subgoal for x
    apply (cases "clocks_inv x \<in> set r"; simp add: clocks_inv_def)
    subgoal
      using bij_renum_clocks[THEN bij_is_surj]
      by (auto
            simp: renum_reset_def f_the_inv_f[OF bij_is_inj, OF bij_renum_clocks]
            dest: imageI[where f = renum_clocks]
         )
    subgoal
      by (subst clock_set_id)
         (auto simp: renum_reset_def the_inv_f_f[OF bij_is_inj, OF bij_renum_clocks])
    done
  done

lemma bounded_renumI':
  assumes "bounded sem.bounds s'"
  shows "bounded renum.sem.bounds (s' o vars_inv)"
  using assms unfolding renum.sem_bounds_eq renum.bounds_def sem_bounds_eq bounds_def
  by (simp add: bounded_renumI)

lemma bounded_renumD':
  assumes "bounded renum.sem.bounds (s' o vars_inv)" "dom s' \<subseteq> var_set"
  shows "bounded sem.bounds s'"
  using assms unfolding renum.sem_bounds_eq renum.bounds_def sem_bounds_eq bounds_def
  by (simp add: bounded_renumD)

lemma is_upd_renumD:
  assumes "is_upd s f s'"
  shows "is_upd (s o vars_inv) (renum_upd f) (s' o vars_inv)"
  using assms
  unfolding is_upd_def
  apply clarsimp
  subgoal for xs
    apply (inst_existentials "map (\<lambda>(x,v). (renum_vars x, v)) xs")
     apply (clarsimp elim!: list_all2_mono is_val_renumD simp: list.rel_map renum_upd_def; fail)
    apply (rule ext)
    subgoal premises prems for a
      apply (induction xs arbitrary: s)
       apply (simp; fail)
      apply simp
      apply (fo_rule arg_cong2)
       apply (auto 4 4
          simp: bij_f_the_inv_f[OF bij_renum_vars] the_inv_f_f[OF inj_renum_vars] vars_inv_def)
      done
    done
  done

lemma is_upds_renumD:
  assumes "is_upds s1 ps s'"
  shows "is_upds (s1 o vars_inv) (map renum_upd ps) (s' o vars_inv)"
  using assms by induction (auto intro: is_upds.intros simp: comp_def dest!: is_upd_renumD)

lemma Ball_mono:
  assumes "\<forall>x \<in> S. P x" "\<And>x. x \<in> S \<Longrightarrow> P x \<Longrightarrow> Q x"
  shows "\<forall>x \<in> S. Q x"
  using assms by blast

lemma atLeastLessThan_upperD:
  assumes "S \<subseteq> {l..<u}" "x \<in> S"
  shows "x < u"
  using assms by auto

lemma imp_mono_rule:
  assumes "P1 \<longrightarrow> P2"
    and "Q1 \<Longrightarrow> P1"
    and "Q1 \<Longrightarrow> P2 \<Longrightarrow> Q2"
  shows "Q1 \<longrightarrow> Q2"
  using assms by blast

lemma inj_id:
  "inj id"
  by auto

lemma step_single_renumD:
  assumes "step_u sem L s u a L' s' u'" "L \<in> sem.states" "dom s \<subseteq> var_set"
  shows "step_u renum.sem
    (map_index renum_states L) (s o vars_inv) (map_u u)
    (renum_label a)
    (map_index renum_states L') (s' o vars_inv) (map_u u')"
  using assms(1-3)
  apply (cases a)

(* Delay *)
  subgoal
    supply [simp] = length_automata_eq_n_ps L_len renum_sem_n_ps_eq
    unfolding sem_states_eq
    apply (subst (asm) sem.A_split)
    apply (subst renum.sem.A_split)
    apply (simp only: renum_label_def label.map renum_n_ps_simp renum.n_ps_eq)
    apply (erule step_u_elims')
    apply simp
    apply (rule step_u.intros)

    subgoal
      by (auto 4 3 simp: sem_states_eq dest: inv_renum_sem_I[OF _ _ sem_states_loc_setD])
    subgoal
      by assumption
    subgoal
      by (rule bounded_renumI')
    done

(* Internal *)
  subgoal for a'
    supply [simp] = length_automata_eq_n_ps L_len renum_sem_n_ps_eq
    unfolding sem_states_eq
    apply (subst (asm) sem.A_split)
    apply (subst renum.sem.A_split)
    apply (simp only: renum_label_def label.map renum_n_ps_simp renum.n_ps_eq)
    apply (erule step_u_elims')
    apply simp
    apply (rule step_u.intros)

              apply (drule (1) trans_sem_N_renumD, subst nth_map, (simp add: renum_act_def)+; fail)
    subgoal
      by (auto simp: commited_renum_eq dest!: inj_renum_states[THEN injD, rotated])
    subgoal
      by (erule check_bexp_renumD)
    subgoal
      by (rule map_u_renum_cconstraint_clock_valI)
    subgoal
      apply clarsimp
      apply (rule inv_renum_sem_I[OF _ _ sem_states_loc_setD[OF _ sem.state_preservation_updI]])
          apply (fastforce simp add: sem_states_eq)+
      done
         apply (simp; fail)
        apply (simp; fail)
       apply (rule map_index_update; fail)
      apply (simp add: renum_reset_map_u; fail)
    subgoal
      by (erule is_upd_renumD)
    subgoal
      apply (erule bounded_renumI'; fail)
      done
    done

(* Binary *)
  subgoal for a'
    supply [simp] = length_automata_eq_n_ps L_len renum_sem_n_ps_eq
    unfolding sem_states_eq
    apply (subst (asm) sem.A_split)
    apply (subst renum.sem.A_split)
    apply (simp only: renum_label_def label.map renum_n_ps_simp renum.n_ps_eq)
    apply (erule step_u_elims')
    apply simp
    apply (rule step_u.intros)
    subgoal
      unfolding renum.sem.broadcast_def
      unfolding renum.sem_def
      apply clarsimp
      apply (drule injD[OF inj_renum_acts])
      apply (subst (asm) sem.broadcast_def, subst (asm) sem_def, simp)
      done

                     apply (drule (1) trans_sem_N_renumD, subst nth_map, (simp add: renum_act_def)+; fail)
                    apply (drule (1) trans_sem_N_renumD, subst nth_map, (simp add: renum_act_def)+; fail)

    subgoal
      by (auto simp: commited_renum_eq dest!: inj_renum_states[THEN injD, rotated])

    subgoal
      by (erule check_bexp_renumD)

    subgoal
      by (erule check_bexp_renumD)

    subgoal
      by (rule map_u_renum_cconstraint_clock_valI)

    subgoal
      by (rule map_u_renum_cconstraint_clock_valI)

    subgoal
      apply clarsimp
      apply (rule inv_renum_sem_I[OF _ _ sem_states_loc_setD[OF _ sem.state_preservation_updI]])
          apply (fastforce simp add: sem_states_eq intro!: sem.state_preservation_updI[unfolded sem_states_eq])+
      done
             apply (simp; fail)+
        apply (simp add: map_index_update; fail)
       apply (simp add: renum_reset_map_u[symmetric] renum_reset_def; fail)
      apply (erule is_upd_renumD; fail)
     apply (erule is_upd_renumD; fail)
    apply (erule bounded_renumI'; fail)
    done


(* Broadcast *)
  subgoal for a'
    supply [simp] = length_automata_eq_n_ps L_len renum_sem_n_ps_eq
    unfolding sem_states_eq
    apply (subst (asm) sem.A_split)
    apply (subst renum.sem.A_split)
    apply (simp only: renum_label_def label.map renum_n_ps_simp renum.n_ps_eq)
    apply (erule step_u_elims')
    apply simp

    apply (rule step_u.intros)

(* Action is broadcast *)
    subgoal
      unfolding renum.sem.broadcast_def unfolding renum.sem_def
      by (subst (asm) sem.broadcast_def, subst (asm) sem_def, simp)

                       apply (drule (1) trans_sem_N_renumD, subst nth_map, (simp add: renum_act_def)+; fail)

                      apply (auto dest!: trans_sem_N_renumD simp add: renum_act_def atLeastLessThan_upperD; fail)

(* Condition for commited locations *)
    subgoal
      apply (simp add: commited_renum_eq)
      apply (erule disj_mono[rule_format, rotated 2], (simp; fail))
      apply (erule disj_mono[rule_format, rotated 2])
      subgoal
        apply clarify
        apply (rule rev_bexI, assumption)
        apply (auto simp: commited_renum_eq)
        done
      apply (auto simp: commited_renum_eq dest!: inj_renum_states[THEN injD, rotated]; fail)
      done

                    apply (erule check_bexp_renumD; fail)
                   apply (auto elim: check_bexp_renumD; fail)
                  apply (erule map_u_renum_cconstraint_clock_valI; fail)
                 apply (auto elim: map_u_renum_cconstraint_clock_valI; fail)

(* Set of broadcast receivers is maximal *)
    subgoal
      apply simp
      apply (erule all_mono[THEN mp, OF impI, rotated])
      apply (erule (1) imp_mono_rule)
      apply (erule (1) imp_mono_rule)
      apply clarify
      apply (drule trans_sem_N_renumI', assumption)
      apply (clarsimp simp: renum_act_def)
      apply (drule check_bexp_renumI)
      apply (drule Simple_Network_Impl_map.InD2[rotated -1, where map_time = real_of_int])
           apply (intros?, rule inj_id inj_renum_acts real_of_int_inj)+
      apply simp
      apply (drule map_u_renum_cconstraint_clock_valD)
      apply blast
      done

(* Target invariant *)
    subgoal for b g f r l' p ps bs gs fs rs ls' s'
      apply (subgoal_tac "fold (\<lambda>p L. L[p := ls' p]) ps L \<in> sem.states")
      subgoal
        apply simp
        apply (drule map_u_renum_cconstraint_clock_valI)+
        apply (erule all_mono[THEN mp, OF impI, rotated], erule (1) imp_mono_rule, drule (1) inv_renum_sem_I)
        subgoal
          apply (rule sem_states_loc_setD, simp)
          apply (rule sem.state_preservation_updI)
          subgoal
            by blast
          .
        subgoal
          apply (fo_rule match_assumption2[where P = clock_val], assumption, rule HOL.refl)
          apply (drule sem.states_lengthD, simp)
          done
        done
      subgoal
        apply (rule sem.state_preservation_fold_updI)
         apply (erule Ball_mono)
         apply (simp add: atLeastLessThan_upperD; blast)
        by (simp add: sem_states_eq)
      done
              apply (simp; fail)+
        apply (simp add: Simple_Network_Impl_map.map_trans_broad_aux1[symmetric] map_index_update; fail)
       apply (simp add: renum_reset_map_u[symmetric] renum_reset_def map_concat comp_def; fail)
      apply (erule is_upd_renumD; fail)
     apply (drule is_upds_renumD, simp add: comp_def; fail)
    apply (erule bounded_renumI'; fail)
    done
  done

lemma inj_the_inv:
  "inj (the_inv f)" if "bij f"
  by (auto simp: bij_f_the_inv_f[OF that] dest: arg_cong[where f = f] intro!: injI)

lemma inj_vars_inv:
  "inj vars_inv"
  using bij_renum_vars unfolding vars_inv_def by (rule inj_the_inv)

lemma comp_vars_inv_upd_commute:
  "(s o vars_inv)(x \<mapsto> y) = s(vars_inv x \<mapsto> y) o vars_inv"
  by (intro ext) (auto dest: injD[OF inj_vars_inv])

lemma is_upd_renumI:
  assumes "is_upd (s o vars_inv) (renum_upd f) s'"
  shows "is_upd s f (s' o renum_vars)"
  using assms
  unfolding is_upd_def
  apply clarsimp
  subgoal for xs
    apply (inst_existentials "map (\<lambda>(x,v). (vars_inv x, v)) xs")
     apply (clarsimp elim!: list_all2_mono dest!: is_val_renumI simp: list.rel_map renum_upd_def,
            simp add: the_inv_f_f[OF inj_renum_vars] vars_inv_def; fail)
    apply (rule ext)
    subgoal premises prems for a
      apply (induction xs arbitrary: s)
       apply (simp add: the_inv_f_f[OF inj_renum_vars] vars_inv_def; fail)
      apply (auto simp: comp_vars_inv_upd_commute)
      done
    done
  done

lemma is_upd_renumI':
  assumes "is_upd (s o vars_inv) (renum_upd f) s'"
  obtains s1 where "is_upd s f s1" "s1 = s' o renum_vars"
  by (simp add: assms is_upd_renumI)

lemma is_upd_renumI'':
  assumes "is_upd s (renum_upd f) s'"
  shows "is_upd (s o renum_vars) f (s' o renum_vars)"
proof -
  have "s = (s o renum_vars) o vars_inv"
    by (intro ext) (auto simp: bij_f_the_inv_f[OF bij_renum_vars] vars_inv_def)
  with assms  show ?thesis
    by (intro is_upd_renumI) simp
qed

lemma is_upds_renumI:
  assumes "is_upds (s o vars_inv) (map renum_upd upds) s'"
  shows "\<exists>s1. is_upds s upds s1 \<and> s1 = s' o renum_vars"
  using assms apply (induction "s o vars_inv" "map renum_upd upds" s' arbitrary: upds s)
  subgoal for upds s
    apply auto
    apply (subgoal_tac "s o vars_inv o renum_vars = s")
     apply (auto intro: is_upds.intros simp: comp_def)
    apply (rule ext)
    apply (simp add: vars_inv_def the_inv_f_f[OF inj_renum_vars])
    done

  apply clarsimp
  apply (erule is_upd_renumI')
  apply (auto simp: vars_inv_def bij_f_the_inv_f[OF bij_renum_vars] comp_def intro!: is_upds.intros)
  done

lemma is_upds_renumI'':
  assumes "is_upds s (map renum_upd ps) s'"
  shows "is_upds (s o renum_vars) ps (s' o renum_vars)"
  using assms
  by (induction "map renum_upd ps" s' arbitrary: ps) (auto intro: is_upd_renumI'' is_upds.intros)

lemma bounded_renumD1:
  assumes "bounded renum.sem.bounds s'" "dom (s' \<circ> renum_vars) \<subseteq> var_set"
  shows "bounded sem.bounds (s' o renum_vars)"
  using assms
  by (intro bounded_renumD') (auto simp: vars_inv_def bij_f_the_inv_f[OF bij_renum_vars] comp_def)

lemma renum_reset_append:
  "renum_reset xs @ renum_reset ys = renum_reset (xs @ ys)"
  unfolding renum_reset_def by simp

lemma if_eq_distrib:
  "(if i = j then f i a else f j b) = (f j (if i = j then a else b))"
  by auto

lemma dom_comp_eq_vimage:
  "dom (s o f) = f -` dom s"
  unfolding dom_def by auto

lemma dom_comp_vars_inv_eqD:
  assumes "dom s' = dom (s o vars_inv)"
  shows "dom (s' o renum_vars) = dom s"
  using assms inj_renum_vars surj_renum_vars unfolding vars_inv_def
  by (subst (asm) dom_the_inv_comp) (auto simp: dom_comp_eq_vimage dest: injD)

lemma sem_trans_upd_domD:
  assumes "(L ! p, b, g', a, f, r, l1) \<in> trans (sem.N p)" "p < n_ps"
  shows "fst ` set f \<subseteq> var_set"
proof -
  from assms have "fst ` set f \<subseteq> sem.var_set"
    unfolding sem.var_set_def
    apply -
    apply (rule semilattice_sup_class.sup.coboundedI2)
    apply clarsimp
    apply (inst_existentials "(fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd) ` trans (sem.N p)" p)
      apply force+
    done
  then show ?thesis
    unfolding sem_var_set_eq .
qed

lemma SilD:
  fixes map_action
  assumes "Sil a = map_act map_action a1"
  obtains a' where "a1 = Sil a'" "a = map_action a'"
  using assms by (cases a1) auto

lemma InD:
  fixes map_action
  assumes "In a = map_act map_action a1"
  obtains a' where "a1 = In a'" "a = map_action a'"
  using assms by (cases a1) auto

lemma OutD:
  fixes map_action
  assumes "Out a = map_act map_action a1"
  obtains a' where "a1 = Out a'" "a = map_action a'"
  using assms by (cases a1) auto

lemma In_OutD:
  assumes "In a = renum_act a1" "Out a = renum_act a2"
  obtains a' where "a = renum_acts a'" "a1 = In a'" "a2 = Out a'"
  using assms unfolding renum_act_def by (elim InD OutD) (auto simp: injD[OF inj_renum_acts])

lemma renum_sem_broadcast_eq:
  "renum.sem.broadcast = renum_acts ` sem.broadcast"
  unfolding renum.sem.broadcast_def sem.broadcast_def unfolding sem_def renum.sem_def by simp

lemma inj_eq_iff:
  "f x = f y \<longleftrightarrow> x = y" if "inj f"
  using that unfolding inj_def by auto

lemma trans_sem_N_renum_broadcastI:
  assumes
    "\<forall>p\<in>set ps. (renum_states p (L ! p), bs p, gs p, In a, fs p, rs p, ls p) \<in> trans (renum.sem.N p)"
    "set ps \<subseteq> {0..<n_ps}"
  obtains bs' gs' fs' rs' ls' a' where
    "\<forall>p\<in>set ps. (L ! p, bs' p, gs' p, In a', fs' p, rs' p, ls' p) \<in> trans (sem.N p)"
    "\<forall>p\<in>set ps. bs p = renum_bexp (bs' p)"
    "\<forall>p\<in>set ps. gs p = renum_cconstraint (gs' p)"
    "ps \<noteq> [] \<longrightarrow> a = renum_acts a'"
    "\<forall>p\<in>set ps. fs p = renum_upd (fs' p)"
    "\<forall>p\<in>set ps. rs p = renum_reset (rs' p)"
    "\<forall>p\<in>set ps. ls p = renum_states p (ls' p)"
proof -
  define t where
    "t p \<equiv> SOME (b', g', a', f', r', l1). (L ! p, b', g', a', f', r', l1) \<in> trans (sem.N p)
    \<and> bs p = renum_bexp b' \<and> gs p = renum_cconstraint g' \<and> In a = renum_act a' \<and> fs p = renum_upd f'
    \<and> rs p = renum_reset r' \<and> ls p = renum_states p l1" for p
  define bs' where "bs' p \<equiv> case t p of (b', g', a', f', r', l1) \<Rightarrow> b'" for p
  define gs' where "gs' p \<equiv> case t p of (b', g', a', f', r', l1) \<Rightarrow> g'" for p
  define as' where "as' p \<equiv> case t p of (b', g', a', f', r', l1) \<Rightarrow> a'" for p
  define fs' where "fs' p \<equiv> case t p of (b', g', a', f', r', l1) \<Rightarrow> f'" for p
  define rs' where "rs' p \<equiv> case t p of (b', g', a', f', r', l1) \<Rightarrow> r'" for p
  define ls' where "ls' p \<equiv> case t p of (b', g', a', f', r', l1) \<Rightarrow> l1" for p

  have *: "case t p of (b', g', a', f', r', l1) \<Rightarrow>
    (L ! p, b', g', a', f', r', l1) \<in> trans (sem.N p)
    \<and> bs p = renum_bexp b' \<and> gs p = renum_cconstraint g' \<and> In a = renum_act a' \<and> fs p = renum_upd f'
    \<and> rs p = renum_reset r' \<and> ls p = renum_states p l1" if "p \<in> set ps" for p
    using assms(1)
    apply -
    apply (drule bspec[OF _ that])
    apply (drule trans_sem_N_renumI')
    subgoal
      using assms(2) that by auto
    unfolding t_def by (elims, fo_rule someI, auto)

  show ?thesis
  proof (cases "ps")
    case Nil
    then show ?thesis
      by (auto intro: that)
  next
    case (Cons p ps')
    then have "p \<in> set ps"
      by auto
    define a' where "a' = as' p"
    have 1: "as' q = a'" and "In a = renum_act a'" if "q \<in> set ps" for q
      unfolding as'_def a'_def using *[OF that] *[OF \<open>p \<in> set ps\<close>]
      by (auto dest: injD[OF injective_functions(3)])
    then obtain a1 where "a' = In a1" "a = renum_acts a1"
      using \<open>p \<in> set ps\<close> unfolding renum_act_def by (auto elim!: InD)
    then show ?thesis
      apply -
      apply (rule that[of bs' gs' a1 fs' rs' ls'])
      unfolding bs'_def gs'_def fs'_def rs'_def ls'_def
            apply ((intros, frule *)?, auto simp: as'_def dest: 1; fail)+
      done
  qed
qed

lemmas all_mono_rule = all_mono[THEN mp, OF impI, rotated]

method prop_monos =
  erule all_mono_rule
  | erule (1) imp_mono_rule
  | erule disj_mono[rule_format, rotated 2]

lemma inv_sem_N_renum_broadcastI:
  assumes
"\<forall>pa<n_ps.
  [renum_reset r @ concat (map rs ps)\<rightarrow>0]map_u u
    \<turnstile> inv (renum.sem.N pa)
        (fold (\<lambda>p L. L[p := ls p]) ps (map_index renum_states L) [p := renum_states p l1] ! pa)"
"\<forall>p\<in>set ps. rs p = renum_reset (rs' p)"
"\<forall>p\<in>set ps. ls p = renum_states p (ls' p)"
"\<forall>p\<in>set ps. ls' p \<in> (\<Union>(l, b, g, a, r, u, l') \<in> trans (sem.N p). {l, l'})"
"l1 \<in> (\<Union>(l, b, g, a, r, u, l') \<in> trans (sem.N p). {l, l'})"
"L \<in> sem.states"
shows
"\<forall>pa<n_ps.
  [r @ concat (map rs' ps)\<rightarrow>0]u \<turnstile> inv (sem.N pa) (fold (\<lambda>p L. L[p := ls' p]) ps L [p := l1] ! pa)"
proof -
  have [simp]: "renum_reset r @ concat (map rs ps) = renum_reset (r @ concat (map rs' ps))"
    using assms(2) by (simp cong: map_cong add: map_concat renum_reset_def)
  have [simp]: "length L = n_ps"
    using \<open>L \<in> sem.states\<close> by (auto dest: sem.states_lengthD)
  have [simp]: "(fold (\<lambda>p L. L[p := ls p]) ps (map_index renum_states L) [p := renum_states p l1] ! q)
    = renum_states q (fold (\<lambda>p L. L[p := ls' p]) ps L [p := l1] ! q)"
    if "q < n_ps" for q
    using assms(4-) that
    thm map_index_update Simple_Network_Impl_map.map_trans_broad_aux1[symmetric]
    apply (cases "p = q")
     apply (simp add: fold_upds_aux_length)
    apply (simp
        add: assms(3) Simple_Network_Impl_map.map_trans_broad_aux1[symmetric] fold_upds_aux_length
        cong: fold_cong)
    done
  have "fold (\<lambda>p L. L[p := ls' p]) ps L[p := l1] ! q \<in> loc_set" if "q < n_ps" for q
    using assms(4-)
    apply (intro sem_states_loc_setD)
    subgoal
      using that by (simp add: n_ps_def)
    apply (erule sem.state_preservation_updI)
    by (rule sem.state_preservation_fold_updI)
  then show ?thesis
    using assms by (auto dest: inv_renum_sem_D simp: renum_reset_map_u)
qed

method solve_triv =
  assumption
  | erule (1) bounded_renumD'; fail
  | rule inv_renum_sem_D[OF _ _ sem_states_loc_setD]; simp; fail
  | rule check_bexp_renumI; simp; fail
  | rule map_u_renum_cconstraint_clock_valD; simp; fail
  | rule is_upd_renumI is_upd_renumI'' is_upds_renumI'', simp; fail
  | simp; fail
  | simp add:
      vars_inv_def bij_f_the_inv_f[OF bij_renum_vars] renum_reset_map_u[symmetric] map_index_update
      renum_reset_append;
    fail
  | subst nth_map, (simp; fail)+; fail
  | (rule sem.state_preservation_updI, blast)+, simp; fail

lemma trans_sem_upd_domI:
  assumes "(L ! p, b', g', a, f', r', l1) \<in> trans (sem.N p)" "dom s = var_set" "p < n_ps"
  shows "\<forall>(x, _)\<in>set (renum_upd f'). x \<in> dom (s o vars_inv)"
  unfolding renum_upd_def using assms
  by (auto simp: dom_comp_eq_vimage vars_inv_def the_inv_f_f[OF inj_renum_vars]
           dest!: sem_trans_upd_domD)

lemma step_single_renumI:
  assumes
    "step_u renum.sem
      (map_index renum_states L) (s o vars_inv) (map_u u) a L' s' u'"
    "L \<in> sem.states" "dom s \<subseteq> var_set" "dom s = var_set"
  shows "\<exists> a1 L1 s1 u1. step_u sem L s u a1 L1 s1 u1 \<and> renum_label a1 = a \<and>
    L' = map_index renum_states L1 \<and> s' = s1 o vars_inv \<and> u' = map_u u1"
  using assms(1-3)
  supply [simp] = length_automata_eq_n_ps L_len renum_sem_n_ps_eq sem_states_eq
  unfolding sem_states_eq
  apply (subst sem.A_split)
  apply (subst (asm) renum.sem.A_split)
  apply (simp only: renum_label_def label.map renum_n_ps_simp renum.n_ps_eq)

  using [[goals_limit=2]]

  apply (cases a)

(* Delay *)
  subgoal
    apply (simp only:)
    apply (erule step_u_elims')
    apply intros
        apply (rule step_u.intros)
          apply simp
          apply prop_monos+
          apply solve_triv+
    done

(* Internal *)
  subgoal for a'
    apply (simp only:)
    apply (erule step_u_elims')
    apply simp
    apply (drule (1) trans_sem_N_renumI')
    apply elims
    unfolding renum_act_def
    apply (rule SilD, assumption)

    apply intros
        apply (rule step_u.intros(2))
                  apply solve_triv

                 apply (prop_monos; auto simp: commited_renum_eq dest: injD[OF inj_renum_states]; fail)

                apply solve_triv
               apply solve_triv

(* Target invariant is satisified *)
              apply (simp add: map_index_update[symmetric] renum_reset_map_u, prop_monos+, rule inv_renum_sem_D[OF _ _ sem_states_loc_setD], solve_triv+; fail)

             apply solve_triv+

(* Resulting state is bounded *)
        apply (erule bounded_renumD1)
    subgoal
      apply (drule is_upd_dom)
      subgoal
        apply (simp add: dom_comp_eq_vimage)
        unfolding renum_upd_def
        apply (clarsimp simp: vars_inv_def the_inv_f_f[OF inj_renum_vars])
        apply (drule (1) sem_trans_upd_domD)
        using assms(4)
        apply auto
        done
      apply (drule dom_comp_vars_inv_eqD, simp)
      done

       apply solve_triv

      apply solve_triv

(* or: auto *)
     apply (rule ext)
     apply solve_triv+
    done


(* Binary *)
  subgoal for a'
    apply (simp only:)
    apply (erule step_u_elims')
    apply simp
    apply (drule (1) trans_sem_N_renumI')
    apply (drule (1) trans_sem_N_renumI')
    apply elims
    apply (rule In_OutD, assumption, assumption)

    apply intros
        apply (rule step_u.intros(3))

                        prefer 2
                        apply solve_triv

                        apply (clarsimp simp: renum_sem_broadcast_eq; fail)

                        apply solve_triv

    subgoal
      by (auto simp: commited_renum_eq inj_eq_iff[OF inj_renum_states])

                      apply solve_triv+

(* Target invariant is satisified *)
                  apply (simp add: map_index_update[symmetric] renum_reset_map_u renum_reset_append, prop_monos+, rule inv_renum_sem_D[OF _ _ sem_states_loc_setD], solve_triv+; fail)

                 apply solve_triv+

(* Resulting state is bounded *)
        apply (erule bounded_renumD1)
    subgoal premises prems
      using prems(2,13-)
      apply -
      apply (drule is_upd_dom)
      subgoal
        using assms(4) by - (drule trans_sem_upd_domI; simp split: prod.splits)
      apply (drule is_upd_dom)
      subgoal
        using assms(4) by - (drule trans_sem_upd_domI; simp split: prod.splits)
      apply (simp, drule dom_comp_vars_inv_eqD, simp)
      done

       apply solve_triv+
     apply (rule ext)
     apply solve_triv+
    done

(* Broadcast *)
  subgoal for a'
    apply (simp only:)
    apply (erule step_u_elims')
    apply simp
    apply (frule (1) trans_sem_N_renumI')
    apply elims
    subgoal for b g f r l' p ps bs gs fs rs ls' s'a b' g' a'a f' r' l1
      unfolding renum_act_def
      apply (rule OutD, assumption)

      apply (simp add: atLeastLessThan_upperD)
      apply (erule (1) trans_sem_N_renum_broadcastI)
      apply (subgoal_tac "map fs ps = map renum_upd (map fs' ps)")
       defer
       apply (simp; fail)

      subgoal for a1 bs' gs' fs' rs' ls1 a2

        apply intros
            apply (rule step_u.intros(4)[where ps = ps])

                            prefer 2
                            apply solve_triv

                            apply (clarsimp simp: renum_sem_broadcast_eq inj_eq_iff[OF inj_renum_acts]; fail)
                            apply (cases "ps = []"; simp add: atLeastLessThan_upperD inj_eq_iff[OF inj_renum_acts]; fail)

                            apply prop_monos

        subgoal
          by (auto simp: commited_renum_eq inj_eq_iff[OF inj_renum_states])

                            apply prop_monos

        subgoal
          by (clarsimp simp: commited_renum_eq inj_eq_iff[OF inj_renum_states] atLeastLessThan_upperD, fast)

        subgoal
          by (auto simp: commited_renum_eq inj_eq_iff[OF inj_renum_states] atLeastLessThan_upperD)

                            apply solve_triv

                           apply (erule Ball_mono, solve_triv; fail)

                          apply solve_triv

                         apply (erule Ball_mono, solve_triv)

(* Set of broadcast receivers is maximal *)
        subgoal
          apply simp
          apply prop_monos+
          subgoal premises prems
            using prems(30-)
            apply clarify
            apply (drule (1) trans_sem_N_renumD)
            apply (simp add: renum_act_def)
            apply (drule check_bexp_renumD)
            apply (drule map_u_renum_cconstraint_clock_valI)
            apply blast
            done
          done

                       apply (simp add: atLeastLessThan_upperD)

(* Target invariant is satisified *)
                       apply (erule (2) inv_sem_N_renum_broadcastI, blast, fast, solve_triv; fail)

                      apply solve_triv+

        subgoal
          (* Resulting state is bounded *)
          apply (erule bounded_renumD1)

          apply (drule is_upd_dom)
          subgoal
            using assms(4) by (intro trans_sem_upd_domI)

          apply (drule is_upds_dom)
          subgoal
            using assms(4) apply -
            apply simp
            apply (drule trans_sem_upd_domI, assumption, assumption)
            apply (erule Ball_mono, drule trans_sem_upd_domI, assumption, (simp add: atLeastLessThan_upperD; fail))
            apply simp
            done
          apply (simp, drule dom_comp_vars_inv_eqD, simp)
          done

           apply solve_triv

          apply (simp add: Simple_Network_Impl_map.map_trans_broad_aux1 map_index_update cong: fold_cong; fail)

         apply (auto simp: vars_inv_def bij_f_the_inv_f[OF bij_renum_vars]; fail)

        apply (simp add: renum_reset_map_u[symmetric] renum_reset_def map_concat comp_def cong: map_cong; fail)
        done
      done
    done
  done

lemma step_u_var_set_invariant:
  assumes "step_u sem L s u a L' s' u'" "dom s = var_set"
  shows "dom s' = var_set"
  using assms dom_bounds_var_set by (auto 4 4 dest!: sem.bounded_inv simp: bounded_def)

lemmas step_u_invariants = sem.states_inv step_u_var_set_invariant

interpretation single: Bisimulation_Invariant
  "\<lambda>(L, s, u) (L', s', u'). \<exists> a. step_u sem L s u a L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). \<exists> a. step_u renum.sem L s u a L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). L' = map_index renum_states L \<and> s' = s o vars_inv \<and> u' = map_u u"
  "\<lambda> (L, s, u). L \<in> sem.states \<and> dom s = var_set" "\<lambda>_. True"
  apply standard
     apply clarsimp
  subgoal for L s u L' s' u' a
    by (drule (1) step_single_renumD, auto)
  subgoal
    by clarsimp (drule step_single_renumI[rotated]; blast)
  subgoal
    by clarsimp (intro conjI; elim step_u_invariants)
  subgoal
    .
  done

interpretation Bisimulation_Invariant
  "\<lambda>(L, s, u) (L', s', u'). step_u' sem L s u L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). step_u' renum.sem L s u L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). L' = map_index renum_states L \<and> s' = s o vars_inv \<and> u' = map_u u"
  "\<lambda> (L, s, u). L \<in> sem.states \<and> dom s = var_set" "\<lambda>_. True"
proof -
  define rsem where "rsem = renum.sem"
  note step_single_renumD = step_single_renumD[folded rsem_def]
  show "Bisimulation_Invariant
     (\<lambda>(L, s, u) (L', s', u'). sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)
     (\<lambda>(L, s, u) (L', s', u'). renum.sem \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)
     (\<lambda>(L, s, u) (L', s', u').
         L' = map_index renum_states L \<and>
         s' = (s o vars_inv) \<and>
         u' = map_u u)
     (\<lambda>(L, s, u). L \<in> sem.states \<and> dom s = var_set) (\<lambda>_. True)"
    unfolding rsem_def[symmetric]
  proof ((standard; clarsimp split: prod.splits), goal_cases)
    case (1 L s u L' s' u')
    from 1(1) guess L1 s1 u1 a
      by (elim step_u'_elims)
    with 1(2-) show ?case
      apply -
      apply (rule step_u'.intros[where a = "renum_label a"])
        apply (erule (1) step_single_renumD[where a = Del, unfolded renum_label_def, simplified], blast)
       apply (cases a; simp add: renum_label_def; fail)
      apply (erule step_single_renumD)
       apply (blast dest: step_u_invariants)+
      done
  next
    case (2 L s u L' s' u')
    from 2(3) guess L1 s1 u1 a
      by (elim step_u'_elims)
    with 2(1,2) show ?case
      apply -
      apply (drule (1) step_single_renumI[folded rsem_def], blast)
      apply safe
      subgoal for a1
        apply (drule step_single_renumI[folded rsem_def])
          apply (blast dest: step_u_invariants)+
        apply (subgoal_tac "a1 = Del")
         apply clarsimp
         apply intros
            apply (erule step_u'.intros)
             apply auto
        apply (cases a1; simp add: renum_label_def)
        done
      done
  next
    case (3 x1 x1a x2a x1b x1c x2c)
    then show ?case
      by (elim step_u'_elims) (auto 4 4 dest: step_u_invariants)
  qed
qed

lemmas renum_bisim = Bisimulation_Invariant_axioms

end

locale Simple_Network_Impl_Formula_real =
  Simple_Network_Rename_real where automata = automata
  for automata ::
    "('s list \<times> (('a :: countable) act, 's, 'c, real, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, real) cconstraint) list) list" +
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

interpretation Bisimulation_Invariant
  "\<lambda>(L, s, u) (L', s', u'). step_u' sem L s u L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). step_u' renum.sem L s u L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). L' = map_index renum_states L \<and> s' = s o vars_inv \<and> u' = map_u u"
  "\<lambda> (L, s, u). L \<in> sem.states \<and> dom s = var_set" "\<lambda>_. True"
  by (rule renum_bisim)

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

end (* Simple Network Rename real *)


(* XXX Move *)
lemma Bisimulation_Invariants_Bisimulation_Invariant:
  assumes "Bisimulation_Invariants A B sim PA PA PB PB"
  shows "Bisimulation_Invariant A B sim PA PB"
proof -
  interpret Bisimulation_Invariants A B sim PA PA PB PB
    by (rule assms)
  show ?thesis
    by (standard; blast intro: A_B_step B_A_step)
qed

(* XXX Move *)
lemma Bisimulation_Invariants_Bisimulation_Invariant_iff:
  "Bisimulation_Invariants A B sim PA PA PB PB \<longleftrightarrow> Bisimulation_Invariant A B sim PA PB"
  using
    Bisimulation_Invariants_Bisimulation_Invariant Bisimulation_Invariant_Bisimulation_Invariants
  by blast

lemmas Bisimulation_Invariant_composition =
  Bisimulation_Invariant_Invariants_composition[
    THEN Bisimulation_Invariants_Bisimulation_Invariant,
    OF _ Bisimulation_Invariant_Bisimulation_Invariants]

lemma Bisimulation_Invariant_refl:
  "Bisimulation_Invariant A A (=) P P" if "\<And>a b. P a \<Longrightarrow> A a b \<Longrightarrow> P b"
  by (rule Bisimulation_Invariant.intro) (auto intro: that)


locale Simple_Network_Rename_int =
  Simple_Network_Rename_Defs_int where automata = automata +
  Simple_Network_Rename' where automata = automata
  for automata ::
    "('s list \<times> (('a :: countable) act, 's, 'c, int, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, int) cconstraint) list) list"
begin

lemma n_ps_eq1:
  "Prod_TA_Defs.n_ps
        (set broadcast, map automaton_of (map conv_automaton automata),
         map_of bounds') = n_ps"
  unfolding n_ps_def Prod_TA_Defs.n_ps_def by simp

lemma var_set_eq1:
  "Prod_TA_Defs.var_set
     (set broadcast, map automaton_of (map conv_automaton automata),
      map_of bounds') = var_set"
  unfolding sem_def sem_var_set_eq[symmetric] by simp

sublocale real: Simple_Network_Rename_real where automata = "map conv_automaton automata"
  apply standard
  unfolding n_ps_eq1 var_set_eq1
      apply (rule bij_renum_clocks renum_states_inj bij_renum_vars bounds'_var_set inj_renum_acts)+
  done

lemma sem_unfold1:
  "real.sem = sem"
  unfolding real.sem_def sem_def by simp

lemma var_set_eq:
  "real.var_set = sem.var_set"
  unfolding sem_unfold1[symmetric] real.sem_var_set_eq oops

lemma map_acconstraint_conv_ac_commute:
  "map_acconstraint renum_clocks id (conv_ac ac) = conv_ac (map_acconstraint renum_clocks id ac)"
  by (cases ac; simp)

lemma map_ccconstraint_conv_cc_commute:
  "renum_cconstraint (conv_cc g) = conv_cc (renum_cconstraint g)"
  unfolding renum_cconstraint_def map_cconstraint_def by (simp add: map_acconstraint_conv_ac_commute)

lemma rename_conv_automaton_commute:
  "real.renum_automaton n (conv_automaton x) = conv_automaton (real.renum_automaton n x)"
  unfolding real.renum_automaton_def conv_automaton_def
  by (clarsimp split: prod.split simp: map_ccconstraint_conv_cc_commute)

lemma sem_unfold2:
  "real.renum.sem = renum.sem"
  unfolding real.renum.sem_def renum.sem_def sem_unfold1[symmetric]
  by (simp add: rename_conv_automaton_commute)

interpretation Bisimulation_Invariant
  "\<lambda>(L, s, u) (L', s', u'). step_u' sem L s u L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). step_u' renum.sem L s u L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). L' = map_index renum_states L \<and> s' = s o vars_inv \<and> u' = map_u u"
  "\<lambda> (L, s, u). L \<in> sem.states \<and> dom s = var_set" "\<lambda>_. True"
  apply (rule Bisimulation_Invariant_sim_replace)
   apply (rule Bisimulation_Invariant_composition)
    apply (rule real.renum_bisim[unfolded sem_unfold1 var_set_eq1])
  unfolding sem_unfold2
   apply (rule Bisimulation_Invariant_refl)
   apply auto
  done

lemmas renum_bisim = Bisimulation_Invariant_axioms

end

locale Simple_Network_Rename_Formula_int =
  Simple_Network_Rename_int where automata = automata
  for automata ::
    "('s list \<times> (('a :: countable) act, 's, 'c, int, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, int) cconstraint) list) list" +
  fixes \<Phi> :: "(nat, 's, 'x, int) formula"
    and s\<^sub>0 :: "('x \<times> int) list"
    and L\<^sub>0 :: "'s list"
  assumes L\<^sub>0_states: "L\<^sub>0 \<in> states"
  assumes s\<^sub>0_dom: "fst ` set s\<^sub>0 = var_set" and s\<^sub>0_distinct: "distinct (map fst s\<^sub>0)"
begin

definition \<Phi>' where
  "\<Phi>' = map_formula renum_states renum_vars id \<Phi>"

definition a\<^sub>0 where
  "a\<^sub>0 = (L\<^sub>0, map_of s\<^sub>0, \<lambda>_. 0)"

definition a\<^sub>0' where
  "a\<^sub>0' = (map_index renum_states L\<^sub>0, map_of (map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0), \<lambda>_. 0)"

(* Refine to subset of var_set? *)
lemma state_eq_aux:
  assumes "x \<notin> renum_vars ` var_set"
  shows "vars_inv x \<notin> var_set"
  unfolding vars_inv_def
proof clarsimp
  assume "the_inv renum_vars x \<in> var_set"
  then have "renum_vars (the_inv renum_vars x) = x"
    by (intro f_the_inv_f real.inj_renum_vars) (simp add: real.surj_renum_vars)
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
        using real.inj_renum_vars by (auto intro: inj_on_subset)
       apply (rule map_of_is_SomeI, rule assms, assumption)
      apply (simp add: the_inv_f_f[OF real.inj_renum_vars] s\<^sub>0_distinct)
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

interpretation Bisimulation_Invariant
  "\<lambda>(L, s, u) (L', s', u'). step_u' sem L s u L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). step_u' renum.sem L s u L' s' u'"
  "\<lambda>(L, s, u) (L', s', u'). L' = map_index renum_states L \<and> s' = s o vars_inv \<and> u' = map_u u"
  "\<lambda> (L, s, u). L \<in> sem.states \<and> dom s = var_set" "\<lambda>_. True"
  by (rule renum_bisim)

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
       inj_eq sem.states_lengthD renum_states_inj vars_inv_def the_inv_f_f[OF real.inj_renum_vars])+

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

end (* Simple Network Rename' *)



(* XXX Move *)
lemma vars_of_bexp_finite[finite_intros]:
  "finite (vars_of_bexp (b::('a, 'b) bexp))"
and vars_of_exp_finite[finite_intros]:
  "finite (vars_of_exp (e::('a, 'b) exp))"
  by (induction b and e) auto

lemma set_bexp_vars_of_bexp:
  "set_bexp (b::('a, 'b) bexp) = vars_of_bexp b"
and set_exp_vars_of_exp:
  "set_exp (e::('a, 'b) exp) = vars_of_exp e"
  by (induction b and e) auto

definition (in Prod_TA_Defs)
  "act_set \<equiv> (\<Union> p \<in> {0..<n_ps}. \<Union> (l, e, g, a, _) \<in> trans (N p). act.set_act a) \<union> broadcast"

lemma (in Simple_Network_Impl) act_set_compute:
  "act_set =
  \<Union> ((\<lambda>(_, t, _). \<Union> ((\<lambda>(l, e, g, a, _). act.set_act a) ` set t)) ` set automata) \<union> set broadcast"
  unfolding act_set_def
  apply (fo_rule arg_cong2)
  apply (auto simp: N_p_trans_eq n_ps_def act_set_def broadcast_def)
     apply (drule nth_mem, erule bexI[rotated], force)+
   apply (drule mem_nth, force)+
  done

locale Simple_Network_Rename =
  Simple_Network_Rename_Defs_int where automata = automata for automata ::
    "('s list \<times> (('a :: countable) act, 's, 'c, int, 'x :: countable, int) transition list
      \<times> (('s :: countable) \<times> ('c :: countable, int) cconstraint) list) list" +
  assumes renum_states_inj:
    "\<forall>i<n_ps. \<forall>x\<in>loc_set. \<forall>y\<in>loc_set. renum_states i x = renum_states i y \<longrightarrow> x = y"
  and renum_clocks_inj: "inj_on renum_clocks clk_set'"
  and renum_vars_inj:   "inj_on renum_vars var_set"
  and renum_acts_inj: "inj_on renum_acts act_set"
  and infinite_types:
    "infinite (UNIV :: 'c set)" "infinite (UNIV :: 'x set)" "infinite (UNIV :: 's set)"
    "infinite (UNIV :: 'a set)"
  and bounds'_var_set: "fst ` set bounds' = var_set"
  and loc_set_invs: "\<Union> ((\<lambda>g. fst ` set g) ` set (map (snd o snd) automata)) \<subseteq> loc_set"
  and loc_set_broadcast: "\<Union> ((set o fst) ` set automata) \<subseteq> loc_set"
begin

lemma clk_set'_finite:
  "finite clk_set'"
  unfolding clk_set'_def unfolding clkp_set'_def by (intro finite_intros) auto

(* XXX Move *)
lemmas [finite_intros] = trans_N_finite

lemma set_act_finite[finite_intros]:
  "finite (set_act a)"
  by (cases a) auto

lemma loc_set_finite:
  "finite loc_set"
  unfolding loc_set_def by (auto intro!: finite_intros)

(* XXX Move *)
lemma var_set_finite[finite_intros]:
  "finite var_set"
  unfolding var_set_def by (auto intro!: finite_intros)

lemma act_set_finite:
  "finite act_set"
  unfolding act_set_def broadcast_def by (auto intro!: finite_intros)

lemma bij_extend_bij_renum_clocks:
  "bij (extend_bij renum_clocks clk_set')"
  by (intro extend_bij_bij renum_clocks_inj clk_set'_finite infinite_types) simp

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

lemma renum_acts_bij_extends[simp]:
  "extend_bij renum_acts act_set x = renum_acts x" if "x \<in> act_set"
  by (intro extend_bij_extends[rule_format] renum_acts_inj act_set_finite infinite_types that)

lemma inj_extend_bij_renum_acts: "inj (extend_bij renum_acts act_set)"
  using renum_acts_inj infinite_types act_set_finite by (intro extend_bij_inj) auto

sublocale rename: Simple_Network_Rename_int
  broadcast bounds'
  "extend_bij renum_acts act_set"
  "extend_bij renum_vars var_set"
  "extend_bij renum_clocks clk_set'"
  "\<lambda>p. extend_bij (renum_states p) loc_set"
  automata
  by (standard;
      intro allI impI bij_extend_bij_renum_clocks inj_extend_bij_renum_states
           inj_extend_bij_renum_acts bij_extend_bij_renum_states bounds'_var_set)

definition
  "renum_upd' = map (\<lambda>(x, upd). (renum_vars x, map_exp renum_vars upd))"

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
       apply (fastforce dest: nth_mem simp: var_set_compute set_bexp_vars_of_bexp)+
      done
    subgoal guards
      apply (rule renum_cconstraint)
      unfolding clk_set'_def clkp_set'_def collect_clock_pairs_def
      apply (fastforce dest: nth_mem elim: set1_acconstraint_elim)
      done
    subgoal actions
      unfolding rename.renum_act_def renum_act_def
      apply (fo_rule act.map_cong_pred, (simp; fail))
      apply (clarsimp simp: pred_act_def)
      apply (rule renum_acts_bij_extends)
      apply (auto 4 4 simp: act_set_compute dest: nth_mem)
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
       apply (fastforce dest: nth_mem simp: set_exp_vars_of_exp var_set_compute)+
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

lemma rename_renum_sem_eq:
  "rename.renum.sem = renum.sem"
  unfolding renum.sem_def rename.renum.sem_def
  apply clarsimp
  apply (intro conjI)
  subgoal
    by (rule image_cong; intro HOL.refl renum_acts_bij_extends; simp add: act_set_def broadcast_def)
  subgoal
    by (rule map_index_cong) (auto simp: renum_automaton_eq[folded length_automata_eq_n_ps])
  subgoal
    using bounds'_var_set by - (fo_rule arg_cong, auto intro: renum_vars_bij_extends)
  done

end (* Simple_Network_Rename *)


locale Simple_Network_Rename_Formula =
  Simple_Network_Rename where automata = automata
  for automata ::
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

sublocale rename: Simple_Network_Rename_Formula_int
  broadcast bounds'
  "extend_bij renum_acts act_set"
  "extend_bij renum_vars var_set"
  "extend_bij renum_clocks clk_set'"
  "\<lambda>p. extend_bij (renum_states p) loc_set"
  automata
  by (standard; rule L\<^sub>0_states s\<^sub>0_dom s\<^sub>0_distinct)

lemma sexp_eq:
  assumes
    \<open>vars_of_sexp e \<subseteq> var_set\<close>
    \<open>set2_sexp e \<subseteq> loc_set\<close>
    \<open>locs_of_sexp e \<subseteq> {0..<n_ps}\<close>
  shows \<open>map_sexp (\<lambda>p. extend_bij (renum_states p) loc_set) (extend_bij renum_vars var_set) id e =
         map_sexp renum_states renum_vars id e\<close>
  using assms by (induction e; clarsimp simp: renum_states_extend)

lemma state_eq:
  "map_of (map (\<lambda>(x, y). (extend_bij renum_vars var_set x, y)) s\<^sub>0) =
    map_of (map (\<lambda>(x, y). (renum_vars x, y)) s\<^sub>0)"
  using s\<^sub>0_dom by - (rule arg_cong, auto intro: renum_vars_bij_extends)

lemma L\<^sub>0_dom:
  "length L\<^sub>0 = n_ps" "set L\<^sub>0 \<subseteq> loc_set"
  using L\<^sub>0_states by (auto intro!: states_loc_setD)

definition
  "a\<^sub>0 = (L\<^sub>0, map_of s\<^sub>0, \<lambda>_. 0)"

definition
  "a\<^sub>0' = (
    map_index (\<lambda>p. renum_states p) L\<^sub>0,
    map_of (map (\<lambda>(x, y). (renum_vars x, y)) s\<^sub>0),
    \<lambda>_. 0)"

definition
  "\<Phi>' = map_formula (\<lambda>p. renum_states p) renum_vars id \<Phi>"

lemma rename_a\<^sub>0_eq:
  "rename.a\<^sub>0 = a\<^sub>0"
  unfolding rename.a\<^sub>0_def a\<^sub>0_def ..

lemma rename_a\<^sub>0'_eq:
  "rename.a\<^sub>0' = a\<^sub>0'"
  unfolding a\<^sub>0'_def rename.a\<^sub>0'_def
  apply (clarsimp, rule conjI)
  subgoal
    using L\<^sub>0_dom by (auto intro!: map_index_cong renum_states_extend)
  subgoal
    unfolding vars_inv_def using s\<^sub>0_dom s\<^sub>0_distinct
    by (auto simp: state_eq Simple_Network_Rename_Defs.vars_inv_def)
  done

lemma rename_\<Phi>'_eq:
  "rename.\<Phi>' = \<Phi>'"
  using formula_dom unfolding rename.\<Phi>'_def \<Phi>'_def by (induction \<Phi>; clarsimp simp: sexp_eq)

lemma models_iff:
  "renum.sem,a\<^sub>0' \<Turnstile> \<Phi>' \<longleftrightarrow> sem,a\<^sub>0 \<Turnstile> \<Phi>"
  by (rule sym)
     (intro rename.models_iff[unfolded rename_a\<^sub>0_eq rename_a\<^sub>0'_eq rename_\<Phi>'_eq rename_renum_sem_eq]
       formula_dom)

lemma has_deadlock_iff:
  "has_deadlock renum.sem a\<^sub>0' \<longleftrightarrow> has_deadlock sem a\<^sub>0"
  apply (rule sym)
  apply (rule rename.has_deadlock_iff[unfolded rename_a\<^sub>0_eq rename_a\<^sub>0'_eq rename_\<Phi>'_eq rename_renum_sem_eq])
  done

lemma (in Simple_Network_Rename_Defs) conv_automaton_of:
  "Simple_Network_Language.conv_A (automaton_of A) = automaton_of (conv_automaton A)"
  unfolding automaton_of_def conv_automaton_def
    Simple_Network_Language.conv_A_def
  by (force
      simp: default_map_of_alt_def map_of_map Simple_Network_Language.conv_t_def split: prod.splits
     )

lemma N_eq_sem:
  "Simple_Network_Language_Model_Checking.N broadcast automata bounds' = sem"
  unfolding conv_alt_def sem_def
  by safe (rule nth_equalityI; simp add: conv_N_eq N_eq sem_N_eq conv_automaton_of n_ps_def)

lemma rename_N_eq_sem:
  "Simple_Network_Language_Model_Checking.N
    (map renum_acts broadcast)
    (map_index renum_automaton automata)
    (map (\<lambda>(a,p). (renum_vars a,p)) bounds')
  = renum.sem"
  unfolding renum.sem_def renum.conv_alt_def
  by safe (rule nth_equalityI; simp add: conv_N_eq N_eq sem_N_eq conv_automaton_of n_ps_def)

lemmas models_iff' = models_iff[folded rename_N_eq_sem N_eq_sem,unfolded a\<^sub>0_def a\<^sub>0'_def \<Phi>'_def]

lemmas has_deadlock_iff' =
  has_deadlock_iff[folded rename_N_eq_sem N_eq_sem,unfolded a\<^sub>0_def a\<^sub>0'_def \<Phi>'_def]

end (* Simple_Network_Rename_Formula *)

end (* Theory *)
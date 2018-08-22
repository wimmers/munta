theory Simple_Network_Language_Impl
  imports
    Simple_Network_Language
    TA_Impl.Normalized_Zone_Semantics_Impl_Refine
    "HOL-Library.IArray" "HOL-Library.AList"
    "../library/More_Methods"
    TA_Impl_Misc2
    TA_More2
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

locale Simple_Network_Impl =
  fixes automata ::
    "('s list \<times> ('a act, 's, 'c, int, 'x, int) transition list
      \<times> ('s \<times> ('c, int) cconstraint) list) list"
    and broadcast :: "'a list"
    and bounds' :: "('x \<times> (int \<times> int)) list"
    and formula :: formula \<comment> \<open>Model checking formula\<close>
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
  "automaton_of \<equiv> \<lambda>(commited, trans, inv).
  (set commited, set trans, default_map_of [] inv)
  "

sublocale Prod_TA_Defs
  "(set broadcast, map automaton_of automata, map_of bounds')" .

definition "clkp_set' \<equiv>
    (\<Union> A \<in> set automata. UNION (set (snd (snd A))) (collect_clock_pairs o snd))
  \<union> (\<Union> A \<in> set automata. \<Union> (l, g, _) \<in> set (fst (snd A)). collect_clock_pairs g)"

definition clk_set'  where
  \<open>clk_set'  =
  fst ` clkp_set' \<union>
  (\<Union> A \<in> set automata. \<Union> (_, _, _, _, r, _) \<in> set (fst (snd A)). set r)\<close>

lemma N_eq:
  \<open>N i = automaton_of (automata ! i)\<close> if \<open>i < n_ps\<close>
  using that unfolding N_def n_ps_def fst_conv snd_conv by (intro nth_map; simp)

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
  unfolding N_eq[OF that] by (auto split: prod.splits simp: automaton_of_def)

paragraph \<open>Fundamentals\<close>

lemma length_automata_eq_n_ps:
  "length automata = n_ps"
  unfolding n_ps_def by simp

lemma L_len[intro, dest]:
  "length L = n_ps" if "L \<in> states"
  using that unfolding states_def by simp

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
        by (force dest!: collect_clock_pairs_invsI split: prod.split_asm)
      unfolding n_ps_def by auto
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
  moreover have "range prod_inv \<subseteq> concat ` ?X"
  proof
    fix x assume "x \<in> range prod_inv"
    then obtain L where L:
      "x = concat (map (\<lambda>p. (inv (N p)) (L ! p)) [0..<n_ps])"
      unfolding prod_inv_def by auto
    then show "x \<in> concat ` ?X"
      by force
  qed
  ultimately show ?thesis by - (drule finite_subset; auto)
qed

lemma (in Prod_TA_Defs) finite_states:
  assumes finite_trans: "\<forall>p < n_ps. finite (Simple_Network_Language.trans (N p))"
  shows "finite states"
proof -
  have "states \<subseteq> {L.
      set L \<subseteq>
        (\<Union> {fst ` trans (N p) | p. p < n_ps} \<union>
        \<Union> {(snd o snd \<circ> snd \<circ> snd \<circ> snd) ` trans (N p) | p. p < n_ps})
        \<and> length L = n_ps}"
    unfolding states_def
    apply (intros add: more_intros)
    apply (elims add: more_elims)
     apply (drule mem_nth)
     apply simp
     apply (elims add: allE, assumption)
     apply (simp split: prod.split_asm)
     apply (erule disjE; (intros add: disjI1 disjI2 more_intros, solve_triv+); fail)
    by (elims add: more_elims)
  also from finite_trans have "finite \<dots>"
    by (intro finite_intros) auto
  finally show ?thesis .
qed

context Simple_Network_Impl
begin

lemma trans_N_finite:
  assumes "p < n_ps"
  shows "finite (Simple_Network_Language.trans (N p))"
  using assms by (subst N_eq) (auto simp: automaton_of_def split: prod.split)

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
  by (auto intro: finite_range_default_map_of split: prod.split)

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

locale Simple_Network_Impl_nat =
  Simple_Network_Impl automata
  for automata ::
    "(nat list \<times> (nat act, nat, nat, int, nat, int) transition list
      \<times> (nat \<times> (nat, int) cconstraint) list) list" +
  fixes m :: nat and num_states :: "nat \<Rightarrow> nat" and num_actions :: nat
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
      \<forall>(x, upd) \<in> set f. x < n_vs \<and> (\<forall> i \<in> vars_of_exp upd. i < n_vs)"
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
begin

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

end (* Theory *)
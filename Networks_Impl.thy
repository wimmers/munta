theory Networks_Impl
  imports Normalized_Zone_Semantics_Impl Networks
begin

abbreviation "repeat x n \<equiv> map (\<lambda> _. x) [0..<n]"

subsection \<open>Pre-compiled networks with states and clocks as natural numbers\<close>
  locale Network_Reachability_Problem_precompiled_defs =
      fixes p :: nat -- "Number of processes"
      and n :: nat -- "Number of states. States are 0 through n - 1"
      and m :: nat -- "Number of clocks"
      and k :: "nat list" -- "Clock ceiling. Maximal constant appearing in automaton for each state"
      and inv :: "(nat, int) cconstraint list list" -- "Clock invariants on states per process"
      and trans :: "((nat, int) cconstraint * nat act * nat list * nat) list list list"
          -- "Transitions between states per process"
      and final :: "nat list list" -- "Final states per process. Initial location is 0"
  begin
    definition "clkp_set' \<equiv> \<Union>
      (collect_clock_pairs ` set (concat inv)
      \<union> (\<lambda> (g, _). collect_clock_pairs g) ` set (concat (concat trans)))"
    definition clk_set'_def: "clk_set' =
      (fst ` clkp_set' \<union> \<Union> ((\<lambda> (_, _, r, _). set r) ` set (concat (concat trans))))"

    text \<open>Definition of the corresponding network\<close>
    definition "label a \<equiv> \<lambda> (g, r, l'). (g, a, r, l')"
    definition "I i l \<equiv> if l < n then inv ! i ! l else []"
    definition "T i \<equiv> {(l, trans ! i ! l ! j) | l j. l < n \<and> j < length (trans ! i ! l)}"
    definition N :: "(nat, nat, int, nat) nta" where "N \<equiv> map (\<lambda> i. (T i, I i)) [0..<p]"
    definition "init \<equiv> repeat (0::nat) p"
    definition "F s \<equiv> \<exists> i < length s. s ! i \<in> set (final ! i)"

    sublocale product: Product_TA_Defs N .

    abbreviation "A \<equiv> product.product_ta"
  end

  lemma snd_comp[simp]:
    "snd o (\<lambda> i. (f i, g i)) = g"
  by auto

  locale Network_Reachability_Problem_precompiled = Network_Reachability_Problem_precompiled_defs +
    assumes process_length: "length inv = p" "length trans = p"
        and inv_length: "\<forall> I \<in> set inv. length I = n"
        and trans_length: "\<forall> T \<in> set trans. length T = n"
        and state_set: "\<forall> T \<in> set trans. \<forall> xs \<in> set T. \<forall> (_, _, _, l) \<in> set xs. l < n"
        and k_length: "length k = m + 1" -- "Zero entry is just a dummy for the zero clock"
        (* XXX Make this an abbreviation? *)
        assumes k_ceiling:
          "\<forall> c \<in> {1..m}. k ! c = Max ({d. (c, d) \<in> clkp_set'} \<union> {0})" "k ! 0 = 0"
        assumes consts_nats: "snd ` clkp_set' \<subseteq> \<nat>"
        assumes clock_set: "clk_set' = {1..m}"
        and p_gt_0: "p > 0"
        and m_gt_0: "m > 0"
        and n_gt_0: "n > 0" and start_has_trans: "\<forall> q < p. trans ! q ! 0 \<noteq> []" -- \<open>Necessary for refinement\<close>
        and trans_complete:
          "\<forall> q1 < p. \<forall> t1 \<in> T q1. case t1 of (l1, g1, In a, r1, l1') \<Rightarrow> \<exists> q2 < p. \<exists> l2 g2 r2 l2'.
            q1 \<noteq> q2 \<and> (l2, g2, Out a, r2, l2') \<in> T q2 | _ \<Rightarrow> True"
          "\<forall> q1 < p. \<forall> t1 \<in> T q1. case t1 of (l1, g1, Out a, r1, l1') \<Rightarrow> \<exists> q2 < p. \<exists> l2 g2 r2 l2'.
            q1 \<noteq> q2 \<and> (l2, g2, In a, r2, l2') \<in> T q2 | _ \<Rightarrow> True"
  begin

    lemma consts_nats':
      "\<forall> I \<in> set inv. \<forall> cc \<in> set I. \<forall> (c, d) \<in> collect_clock_pairs cc. d \<in> \<nat>"
      "\<forall> T \<in> set trans. \<forall> xs \<in> set T. \<forall> (g, _) \<in> set xs. \<forall> (c, d) \<in> collect_clock_pairs g. d \<in> \<nat>"
    using consts_nats unfolding clkp_set'_def by fastforce+

    lemma clkp_set_simp_1:
      "\<Union> (collect_clock_pairs ` set (concat inv)) = collect_clki (inv_of A)"
      apply (simp add: product.product_ta_def inv_of_def product.collect_clki_product_invariant)
      unfolding inv_of_def collect_clki_alt_def I_def[abs_def] N_def I_def
      using inv_length process_length
      apply (simp add: image_Union inv_of_def)
      apply safe
      apply (fastforce dest!: aux)
    by (fastforce dest!: nth_mem)

    lemma init_states:
      "init \<in> product.states"
      unfolding product.states_def
      unfolding N_def trans_of_def T_def init_def using n_gt_0 p_gt_0 start_has_trans by fastforce

    lemma states_not_empty:
      "product.states \<noteq> {}"
      using init_states by blast

    lemma length_prod_T [simp]: "length product.T = p"
      unfolding N_def by auto

    lemma length_N [simp]: "length N = p"
      unfolding N_def by auto

    lemma trans_length_simp:
      assumes "xs \<in> set trans"
      shows "n = length xs"
      using assms trans_length by auto

    lemma clk_set_simp_2:
      "\<Union> ((\<lambda> (g, _, r, _). set r) ` set (concat (concat trans))) = collect_clkvt (trans_of A)"
      apply (simp add: product.product_ta_def trans_of_def)
      apply (subst product.collect_clkvt_product_trans)
        apply (rule states_not_empty)
      using trans_complete unfolding length_prod_T length_N unfolding N_def trans_of_def
       apply (fastforce split: act.split)

      unfolding collect_clkvt_alt_def T_def[abs_def] using process_length(2)
      apply (simp add: image_Union)
      apply safe
        using trans_length apply (fastforce dest!: aux)
      by (fastforce dest!: nth_mem simp: trans_length_simp elim: bexI[rotated])

    lemma clkp_set_simp_3:
      "\<Union> ((\<lambda> (g, _). collect_clock_pairs g) ` set (concat (concat trans))) = collect_clkt (trans_of A)"
      apply (simp add: product.product_ta_def trans_of_def)
      apply (subst product.collect_clkt_product_trans)
        apply (rule states_not_empty)
      using trans_complete unfolding length_prod_T length_N unfolding N_def trans_of_def
       apply (fastforce split: act.split)

      unfolding collect_clkt_alt_def T_def[abs_def] using process_length(2)
      apply (simp add: image_Union)
      apply safe
       using trans_length apply (fastforce dest!: aux)
      by (fastforce dest!: nth_mem simp: trans_length_simp elim: bexI[rotated])

    lemma clkp_set'_eq:
      "clkp_set A = clkp_set'"
    by (simp add: clkp_set'_def clkp_set_def image_Un image_Union
      clkp_set_simp_1[symmetric] clkp_set_simp_3[symmetric] del: product.inv_of_product
      ) fastforce

    lemma clk_set'_eq[simp]:
      "clk_set A = clk_set'"
    by (auto simp: clkp_set'_eq clk_set'_def clk_set_simp_2[symmetric])

    (* XXX Interesting for finiteness *)
    (* XXX Move *)
    lemma Collect_fold_pair:
      "{f a b | a b. P a b} = (\<lambda> (a, b). f a b) ` {(a, b). P a b}"
      by auto

    (* XXX Interesting case of proving finiteness *)
    lemma finite_T[intro, simp]:
      "finite (trans_of A)"
      apply (rule product.finite_trans_of_product)
      apply rule
    proof -
      fix A assume A: "A \<in> set N"
      have
        "{(l, j). l < n \<and> j < length (trans ! i ! l)}
        = \<Union> ((\<lambda> l. {(l, j) | j. j < length (trans ! i ! l)}) ` {l. l < n})" for i
      by auto
    then show "finite (trans_of A)" using A unfolding N_def T_def trans_of_def
      by (fastforce simp: Collect_fold_pair)
    qed

    (* XXX *)
    lemma
      "clk_set' \<noteq> {}"
    using clock_set m_gt_0 by auto

    lemma has_clock[intro]:
      "clk_set A \<noteq> {}"
    using clock_set m_gt_0 by simp

    lemma clk_set:
      "clk_set A = {1..m}"
    using clock_set m_gt_0 by auto

    lemma clk_set_eq:
      "clk_set A = {1..card (clk_set A)}"
    using clk_set by auto

    lemma
      "\<forall>c\<in>clk_set A. c \<le> card (clk_set A) \<and> c \<noteq> 0"
    using clock_set by auto

    lemma
      "\<forall>(_, d)\<in>clkp_set A. d \<in> \<int>"
    unfolding Ints_def by auto

    lemma clkp_set_consts_nat:
      "\<forall>(_, d)\<in>clkp_set A. d \<in> \<nat>"
      unfolding clkp_set'_eq clkp_set'_def using consts_nats' inv_length trans_length by force

    lemma finite_range_inv_of_A[intro, simp]:
      "finite (range (inv_of A))"
      apply (rule product.finite_invariant_of_product)
      unfolding N_def inv_of_def I_def by (auto intro: finite_subset[where B = "{[]}"])

    lemma finite_clkp_set_A[intro, simp]:
      "finite (clkp_set A)"
    unfolding clkp_set_def collect_clki_alt_def collect_clkt_alt_def by fast

    lemma finite_ta_A[intro, simp]:
      "finite_ta A"
    unfolding finite_ta_def using clock_set m_gt_0 clkp_set_consts_nat
    by auto (force simp: clk_set_simp_2[symmetric])+

    sublocale Reachability_Problem A init "PR_CONST F"
      using has_clock clkp_set_consts_nat clk_set_eq by - (standard; blast)

  end (* End of locale *)

end (* End of theory *)
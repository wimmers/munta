theory State_Networks_Impl
  imports Normalized_Zone_Semantics_Impl State_Networks
begin

(* XXX Move *)
lemma finite_lists_length_eq:
  "finite {s. length s = r \<and> set s \<subseteq> S}" if "finite S"
  by (rule finite_lists_length_le[OF that, THEN finite_subset[rotated], where n1 = r]) auto

 (* XXX Move *)
lemma finite_lists_boundedI:
  assumes "\<forall> i < r. finite (S i)"
    shows "finite {s. length s = r \<and> (\<forall>i<r. s ! i \<in> S i)}" (is "finite ?R")
proof -
  let ?S = "\<Union> {S i | i. i < r}"
  have "?R \<subseteq> {s. length s = r \<and> set s \<subseteq> ?S}"
    by (auto dest!: aux)
  moreover have "finite \<dots>" by (rule finite_lists_length_eq) (use assms in auto)
  ultimately show ?thesis by (rule finite_subset)
qed

abbreviation "repeat x n \<equiv> map (\<lambda> _. x) [0..<n]"

subsection \<open>Pre-compiled networks with states and clocks as natural numbers\<close>
locale Network_Reachability_Problem_precompiled_defs =
  fixes p :: nat -- "Number of processes"
    and m :: nat -- "Number of clocks"
    and k :: "nat list" -- "Clock ceiling. Maximal constant appearing in automaton for each state"
    and inv :: "(nat, int) cconstraint list list" -- "Clock invariants on states per process"
    and pred :: "('st \<Rightarrow> bool) list list" -- "Clock invariants on states per process"
    and trans ::
    "((nat, int) cconstraint * ('st \<Rightarrow> bool) * nat act * nat list * ('st \<Rightarrow> 'st) * nat) list list list"
    -- "Transitions between states per process"
    and final :: "nat list list" -- "Final states per process. Initial location is 0"
begin
  definition "clkp_set' \<equiv> \<Union>
    (collect_clock_pairs ` set (concat inv)
    \<union> (\<lambda> (g, _). collect_clock_pairs g) ` set (concat (concat trans)))"
  definition clk_set'_def: "clk_set' =
    (fst ` clkp_set' \<union> \<Union> ((\<lambda> (_, _, _, r, _). set r) ` set (concat (concat trans))))"
  
  text \<open>Definition of the corresponding network\<close>
  definition "make_trans \<equiv> \<lambda> (g, c, a, r, m, l'). (g, (a, (c, m)), r, l')"
  definition "I i l \<equiv> if l < length (inv ! i) then inv ! i ! l else []"
  definition "T i \<equiv> 
    {(l, make_trans (trans ! i ! l ! j)) | l j. l < length (trans ! i) \<and> j < length (trans ! i ! l)}"
  definition "P \<equiv> map (\<lambda> P l. P ! l) pred"
  definition N :: "(nat, nat, int, nat, 'st) snta" where
    "N \<equiv> (map (\<lambda> i. (T i, I i)) [0..<p], P)"
  definition "init \<equiv> repeat (0::nat) p"
  definition "F s \<equiv> \<exists> i < length s. s ! i \<in> set (final ! i)"
  
  sublocale product: Prod_TA_Defs N .
  
abbreviation "A \<equiv> product.prod_ta"

term state_set
end

  lemma snd_comp[simp]:
    "snd o (\<lambda> i. (f i, g i)) = g"
  by auto

locale Network_Reachability_Problem_precompiled_raw =
  Network_Reachability_Problem_precompiled_defs +
  assumes process_length: "length inv = p" "length trans = p" "length pred = p"
    and processes_have_trans: "\<forall> i < p. trans ! i \<noteq> []"
    and lengths:
    "\<forall> i < p. length (pred ! i) = length (trans ! i) \<and> length (inv ! i) = length (trans ! i)"
    and state_set: "\<forall> T \<in> set trans. \<forall> xs \<in> set T. \<forall> (_, _, _, _, _, l) \<in> set xs. l < length T"
    and k_length: "length k = m + 1" -- "Zero entry is just a dummy for the zero clock"
    (* XXX Make this an abbreviation? *)
  assumes k_ceiling:
    "\<forall> c \<in> {1..m}. k ! c = Max ({d. (c, d) \<in> clkp_set'} \<union> {0})" "k ! 0 = 0"
  assumes consts_nats: "snd ` clkp_set' \<subseteq> \<nat>"
  assumes clock_set: "clk_set' = {1..m}"
    and p_gt_0: "p > 0"
    and m_gt_0: "m > 0"
    and start_has_trans: "\<forall> q < p. trans ! q ! 0 \<noteq> []" -- \<open>Necessary for refinement\<close>

locale Network_Reachability_Problem_precompiled = Network_Reachability_Problem_precompiled_raw +
  assumes discrete_state_finite: "\<forall> i < p. \<forall> l < length (trans ! i). finite {s. (pred ! i ! l) s}"
begin
  
  lemma consts_nats':
    "\<forall> I \<in> set inv. \<forall> cc \<in> set I. \<forall> (c, d) \<in> collect_clock_pairs cc. d \<in> \<nat>"
    "\<forall> T \<in> set trans. \<forall> xs \<in> set T. \<forall> (g, _) \<in> set xs. \<forall> (c, d) \<in> collect_clock_pairs g. d \<in> \<nat>"
    using consts_nats unfolding clkp_set'_def by fastforce+
  
  lemma clkp_set_simp_1:
    "\<Union> (collect_clock_pairs ` set (concat inv)) = collect_clki (inv_of A)"
    apply (simp add:
        product.prod_ta_def inv_of_def product.collect_clki_prod_invariant
        product.collect_clki_product_invariant
        )
    unfolding inv_of_def collect_clki_alt_def I_def[abs_def] N_def I_def
    using process_length(1)
    apply (simp add: image_Union inv_of_def)
    apply safe
     apply (fastforce dest!: aux)
    by (fastforce dest!: nth_mem)

  (* XXX Unused *)
lemma processes_have_trans_alt:
  "\<forall> i < p. length (trans ! i) > 0"
  using processes_have_trans by auto
  
  lemma init_states:
    "init \<in> Product_TA_Defs.states (fst N)"
    unfolding Product_TA_Defs.states_def
    unfolding N_def trans_of_def T_def init_def using processes_have_trans p_gt_0 start_has_trans
    by force
  
  lemma states_not_empty:
    "Product_TA_Defs.states (fst N) \<noteq> {}"
    using init_states by blast
  
  lemma length_prod_T [simp]: "length product.T = p"
    unfolding N_def by auto
  
  lemma length_N [simp]: "length (fst N) = p"
    unfolding N_def by auto
  
  lemma length_P [simp]: "length P = p"
    unfolding N_def P_def using process_length(3) by auto

(*  
  lemma trans_length_simp:
    assumes "xs \<in> set trans"
    shows "n = length xs"
    using assms trans_length by auto
*)
  
  lemma [simp]:
    "fst A = product.prod_trans"
    unfolding product.prod_ta_def by simp
  
  lemma [simp]:
    "product.T' = product.product_trans"
    unfolding product.product_ta_def trans_of_def by simp
  
  lemma clk_set_simp_2:
    "\<Union> ((\<lambda> (g, _, _, r, _). set r) ` set (concat (concat trans))) \<supseteq> collect_clkvt (trans_of A)"
    apply (simp add: product.product_ta_def trans_of_def)
    apply (rule subset_trans)
     apply (rule product.collect_clkvt_prod_trans_subs)
    apply simp
    apply (rule subset_trans)
     apply (rule product.collect_clkvt_product_trans_subs)
    unfolding collect_clkvt_alt_def trans_of_def N_def T_def make_trans_def
    using process_length(2)
    by (fastforce dest!: nth_mem elim: bexI[rotated]) (* XXX Magic *)
  
  lemma clkp_set_simp_3:
    "\<Union> ((\<lambda> (g, _). collect_clock_pairs g) ` set (concat (concat trans))) \<supseteq> collect_clkt (trans_of A)"
    apply (simp add: product.product_ta_def trans_of_def)
    apply (rule subset_trans)
     apply (rule product.collect_clkt_prod_trans_subs)
    apply simp
    apply (rule subset_trans)
     apply (rule product.collect_clkt_product_trans_subs)
    unfolding collect_clkt_alt_def trans_of_def N_def T_def make_trans_def
    using process_length(2)
    by (fastforce dest!: nth_mem elim: bexI[rotated]) (* XXX Magic *)
  
  lemma clkp_set'_subs:
    "clkp_set A \<subseteq> clkp_set'"
    using clkp_set_simp_1 clkp_set_simp_3 by (fastforce simp add: clkp_set'_def clkp_set_def)
  
  lemma clk_set'_subs:
    "clk_set A \<subseteq> clk_set'"
    using clkp_set'_subs clk_set_simp_2 by (auto simp: clk_set'_def)
  
      (* XXX Interesting for finiteness *)
      (* XXX Move *)
  lemma Collect_fold_pair:
    "{f a b | a b. P a b} = (\<lambda> (a, b). f a b) ` {(a, b). P a b}" for P
    by auto
  
  lemma [simp]:
    "product.p = p"
    unfolding product.p_def by simp
  
      (* XXX Interesting case of proving finiteness *)
  lemma finite_T[intro, simp]:
    "finite (trans_of A)"
    unfolding product.prod_ta_def trans_of_def
  proof (simp, rule product.finite_prod_trans, goal_cases)
    case 1
    have *: "l < length (trans ! q)" if "l \<in> state_set (trans_of (product.N ! q))" "q < p" for l q
      using that state_set
      unfolding trans_of_def apply simp
      apply (erule disjE)
      unfolding N_def
       apply simp
      unfolding T_def
       apply force
      unfolding make_trans_def
      apply clarsimp
      using process_length(2)
      apply (fastforce dest!: nth_mem split: prod.split_asm)
      done
    with process_length(3) discrete_state_finite show ?case by simp (auto simp: N_def P_def)
  next
    case 2
    show ?case
    proof
      fix A assume A: "A \<in> set product.N"
      have
        "{(l, j). l < length (trans ! i) \<and> j < length (trans ! i ! l)}
        = \<Union> ((\<lambda> l. {(l, j) | j. j < length (trans ! i ! l)}) ` {l. l < length (trans ! i)})" for i
        by auto
      then show "finite (trans_of A)" using A unfolding N_def T_def trans_of_def
        by (fastforce simp: Collect_fold_pair)
    qed
  next
    case 3
    then show ?case unfolding product.p_def unfolding N_def using p_gt_0 by simp
  qed
  
    (* XXX *)
  lemma
    "clk_set' \<noteq> {}"
    using clock_set m_gt_0 by auto
  
  lemma clk_set:
    "clk_set A \<subseteq> {1..m}"
    using clock_set m_gt_0 clk_set'_subs by auto
  
  lemma
    "\<forall>(_, d)\<in>clkp_set A. d \<in> \<int>"
    unfolding Ints_def by auto
  
  lemma clkp_set_consts_nat:
    "\<forall>(_, d)\<in>clkp_set A. d \<in> \<nat>"
    using clkp_set'_subs consts_nats' unfolding clkp_set'_def by force
  
  lemma finite_range_I':
    "finite (range product.I')"
    apply (rule product.finite_invariant_of_product)
    unfolding N_def inv_of_def I_def by (auto intro: finite_subset[where B = "{[]}"])
    
  lemma finite_range_inv_of_A[intro, simp]:
    "finite (range (inv_of A))"
  proof -
    have "range (inv_of A) \<subseteq> range (product.I')" by (auto simp: product.inv_of_simp)
    then show ?thesis by (rule finite_subset) (rule finite_range_I')
  qed
  
  lemma finite_clkp_set_A[intro, simp]:
    "finite (clkp_set A)"
    unfolding clkp_set_def collect_clki_alt_def collect_clkt_alt_def by fast
  
  sublocale Reachability_Problem A "(init, start)" "PR_CONST (\<lambda> (l, s). F l)" m
    using clkp_set_consts_nat clk_set m_gt_0 by - (standard; blast)
  
  lemma [simp]:
    "fst ` (\<lambda>(l, g, a, r, l'). (l, map conv_ac g, a, r, l')) ` S = fst ` S"
    by force
  
  lemma [simp]:
    "(snd \<circ> snd \<circ> snd \<circ> snd) ` (\<lambda>(l, g, a, r, l'). (l, map conv_ac g, a, r, l')) ` S
    = (snd \<circ> snd \<circ> snd \<circ> snd) ` S"
    by force
  
  lemma map_trans_of:
    "map trans_of (map conv_A (fst N)) = map (op ` conv_t) (map trans_of (fst N))"
    by (simp add: trans_of_def split: prod.split)
  
  lemma [simp]:
    "Product_TA_Defs.states (map conv_A (fst N)) = Product_TA_Defs.states (fst N)"
    unfolding Product_TA_Defs.states_def map_trans_of by simp
  
  sublocale product': Product_TA "map conv_A (fst N)" init by standard (simp add: init_states)
  
end (* End of locale *)

datatype ('c, 't) constr =
  lt 'c 't |
  le 'c 't |
  eq 'c 't |
  gt 'c 't |
  ge 'c 't

type_synonym int_var_constr = "(nat, int) cconstraint"

definition check :: "int_var_constr \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> bool" where
  "check c x \<equiv> list_all (clock_val_a x) c"

datatype ('c, 't) upd =
  upd 'c 't |
  inc 'c |
  dec 'c

type_synonym int_var_upd = "(nat, int) upd"

fun modify :: "(nat, int) upd \<Rightarrow> int list \<Rightarrow> int list" where
  "modify (upd i x) s = s[i := x]"
| "modify (inc i) s = s[i := s ! i + 1]"
| "modify (dec i) s = s[i := s ! i - 1]"

locale Network_Reachability_Problem_precompiled_int_vars_defs =
  fixes p :: nat -- "Number of processes"
    and m :: nat -- "Number of clocks"
    and k :: "nat list" -- "Clock ceiling. Maximal constant appearing in automaton for each state"
    and inv :: "(nat, int) cconstraint list list" -- "Clock invariants on states per process"
    and pred :: "int_var_constr list list" -- "Clock invariants on states per process"
    and trans ::
    "((nat, int) cconstraint * int_var_constr * nat act * nat list * int_var_upd * nat) list list list"
    -- "Transitions between states per process"
    and final :: "nat list list" -- "Final states per process. Initial location is 0"
  fixes r :: nat -- "Number of integer variables"
    and bounds :: "(int \<times> int) list" -- "Lower and upper bounds for the variables"
begin

  definition
    "checkb c s \<equiv>
    check c (op ! s) \<and> length s = r \<and> (\<forall> i < r. fst (bounds ! i) < s ! i \<and> s ! i < snd (bounds ! i))"

  definition pred' where "pred' = map (map checkb) pred"
  definition trans' where "trans' =
    map (map (map (\<lambda> (g, c, a, r, m, l). (g, \<lambda> s. check c (op ! s), a, r, modify m, l)))) trans"

end

locale Network_Reachability_Problem_precompiled_int_vars =
  Network_Reachability_Problem_precompiled_int_vars_defs p m k inv pred trans final r bounds +
  Network_Reachability_Problem_precompiled_raw p m k inv pred' trans' final
  for p m k inv pred trans final r bounds
begin

  lemma trans'_length:
    "length trans' = length trans"
    unfolding trans'_def by simp
  
  lemma trans'_lengths:
    "length (trans' ! i) = length (trans ! i)" if "i < p"
    unfolding trans'_def using process_length(2)[unfolded trans'_length] that by simp
  
  lemma pred'_length:
    "length pred' = length pred"
    unfolding pred'_def by simp
  
  lemma pred'_lengths:
    "length (pred' ! i) = length (pred ! i)" if "i < p"
    unfolding pred'_def using process_length(3)[unfolded pred'_length] that by simp
  
  lemma trans'_length_pred:
    "length (trans' ! i) = length (pred ! i)" if "i < p"
    using pred'_lengths lengths that by simp

  lemma
    "finite {s. length s = r \<and> (\<forall>i<r. fst (bounds ! i) < s ! i \<and> s ! i < snd (bounds ! i))}"
    using finite_lists_boundedI by force

  sublocale Network_Reachability_Problem_precompiled p m k inv pred' trans' final
    apply standard
    apply safe
    apply (simp only: trans'_length_pred)
    unfolding pred'_def trans'_def checkb_def
    using process_length(3)[unfolded pred'_length] finite_lists_boundedI by force (* XXX Slow *)

end

end (* End of theory *)
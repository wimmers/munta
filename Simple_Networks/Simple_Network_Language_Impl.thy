theory Simple_Network_Language_Impl
  imports
    Simple_Network_Language
    TA_Impl.Normalized_Zone_Semantics_Impl_Refine
    "HOL-Library.IArray" "HOL-Library.AList"
    "../library/More_Methods"
    "HOL-Eisbach.Eisbach_Tools"
begin

definition default_map_of :: "'b \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b" where
  "default_map_of a xs \<equiv> FinFun.map_default a (map_of xs)"

lemma default_map_of_alt_def:
  "default_map_of a xs x = (if x \<in> dom (map_of xs) then the (map_of xs x) else a)"
  unfolding default_map_of_def map_default_def by (auto split: option.split_asm)

locale Simple_Network_Impl =
  (* fixes p :: nat \<comment> \<open>Number of processes\<close>
    and m :: nat \<comment> \<open>Number of clocks\<close> *)
  (*
    and k :: "nat list list"
      -- "Clock ceiling. Maximal constant appearing in automaton for each state"
    *)
  fixes automata ::
    "('s list \<times> ('a act, 's, 'c, int, 'x, int) transition list \<times> ('s \<times> ('c, int) cconstraint) list) list"
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

term "map conv_automaton automata"

definition
  "B x \<equiv> if x \<in> dom (map_of bounds') then the (map_of bounds' x) else (0, 0)"

definition
  "automaton_of \<equiv> \<lambda>(commited, trans, inv).
  (set commited, set trans, default_map_of [] inv)
  "

(*
definition
  "automaton_of A \<equiv>
  \<^cancel>\<open>let (commited, trans, inv) = conv_automaton A in\<close>
  case A of (commited, trans, inv) \<Rightarrow>
  (set commited, set trans, default_map_of [] inv)
  "
*)

sublocale Prod_TA_Defs
  "(set broadcast, map automaton_of automata, default_map_of (0,0) bounds')" .

definition "clkp_set' \<equiv>
    (\<Union> A \<in> set automata. UNION (set (snd (snd A))) (collect_clock_pairs o snd))
  \<union> (\<Union> A \<in> set automata. \<Union> (l, g, _) \<in> set (fst (snd A)). collect_clock_pairs g)"

definition clk_set'  where
  \<open>clk_set'  =
  fst ` clkp_set' \<union>
  (\<Union> A \<in> set automata. \<Union> (_, _, _, _, r, _) \<in> set (fst (snd A)). set r)\<close>

lemma (in -) union_subsetI:
  "A \<union> B \<subseteq> C \<union> D" if "A \<subseteq> C" "B \<subseteq> D"
  using that by blast

lemma (in -) range_default_map_of:
  "range (default_map_of x xs) \<subseteq> snd ` set xs \<union> {x}"
  unfolding default_map_of_def map_default_def
  by (auto split: option.split_asm) (meson img_snd map_of_SomeD)

lemma collect_clock_pairs_concat:
  "collect_clock_pairs (concat xxs) = (\<Union> x \<in> set xxs. collect_clock_pairs x)"
  unfolding collect_clock_pairs_def by auto

lemma N_eq:
  \<open>N i = automaton_of (automata ! i)\<close> if \<open>i < n_ps\<close>
  using that unfolding N_def n_ps_def fst_conv snd_conv by (intro nth_map; simp)

lemma collect_clock_pairs_invsI:
  "(a, b) \<in> \<Union> ((collect_clock_pairs o snd) ` set invs)" if "(a, b) \<in> collect_clock_pairs (default_map_of [] invs l)"
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
      by (metis (no_types) UNIV_I Un_insert_right range_default_map_of[of "[]" "invs"] image_eqI insertE subsetCE sup_bot.right_neutral)
    then show ?thesis
      using \<open>x \<in> set (default_map_of [] invs l)\<close> by blast
  qed
  then have "x \<in> \<Union> (set ` snd ` set invs)"
    by auto
  with \<open>(a, b) = _\<close> show ?thesis
    unfolding collect_clock_pairs_def
    by auto
qed

lemma clkp_set'_subs:
  "Timed_Automata.clkp_set prod_ta \<subseteq> clkp_set'"
  unfolding Timed_Automata.clkp_set_def
  unfolding clkp_set'_def
  apply (rule union_subsetI)
  subgoal
    unfolding
      Timed_Automata.collect_clki_def
    unfolding inv_of_prod
    unfolding prod_inv_def
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
  sorry

end (* Simple Network Impl *)


no_notation Ref.update ("_ := _" 62)
no_notation Stream.snth (infixl "!!" 100)
no_notation Bits.bits_class.test_bit (infixl "!!" 100)

paragraph \<open>Misc\<close>

named_theorems intros
named_theorems elims

lemmas [intros] =
  allI ballI exI bexI[rotated] conjI impI
and [elims] =
  bexE exE bexE conjE impE

method intros uses add = (intro add intros)
method elims  uses add  = (elim  add elims)

lemma all_mp:
  "\<forall> x. P x \<longrightarrow> R x" if "\<forall> x. P x \<longrightarrow> Q x" "\<And> x. P x \<Longrightarrow> Q x \<Longrightarrow> R x"
  using that by (intros; elims add: allE)

method (in -) rprem =
  (match premises in R: _ \<Rightarrow> \<open>rule R\<close>)

text \<open>Test case for @{method rprem}.\<close>
lemma
  "A \<Longrightarrow> (A \<Longrightarrow> C) \<Longrightarrow> (A \<Longrightarrow> B) \<Longrightarrow> B"
  by rprem


lemma filter_eqI:
  assumes
    "subseq ys xs" "\<forall>x \<in> set ys. P x"
    "\<forall>zs. subseq zs xs \<and> length zs > length ys \<longrightarrow> (\<exists> x \<in> set zs. \<not> P x)"
  shows "filter P xs = ys"
  using assms
proof (induction xs arbitrary: ys rule: list.induct)
  case Nil
  then show ?case
    by - (cases ys; simp)
next
  case (Cons x xs)
  show ?case
  proof (cases "P x")
    case True
    show ?thesis
    proof (cases ys)
      case Nil
      have "subseq [x] (x # xs)"
        by auto
      with Cons.prems Nil \<open>P x\<close> show ?thesis
        by fastforce
    next
      case (Cons y ys')
      have "x = y"
      proof (rule ccontr)
        assume "x \<noteq> y"
        with \<open>subseq ys (x # xs)\<close> \<open>ys = _\<close> have "subseq (x # ys) (x # xs)"
          by simp
        with Cons.prems(2-) \<open>P x\<close> show False
          by fastforce
      qed
      have "\<exists>x\<in>set zs. \<not> P x" if "subseq zs xs" and "length ys' < length zs" for zs
      proof -
        from \<open>subseq zs xs\<close> have "subseq (x # zs) (x # xs)"
          by simp
        with \<open>length ys' < length zs\<close> Cons.prems(3) \<open>ys = _\<close> have "\<exists>x\<in>set (x # zs). \<not> P x"
          by (intro Cons.prems(3)[rule_format]; simp)
        with \<open>P x\<close> show ?thesis
          by auto
      qed
      with Cons.prems \<open>P x\<close> \<open>ys = _\<close> \<open>x = y\<close> show ?thesis
        by (auto intro!: Cons.IH)
    qed
  next
    case False
    with Cons.prems show ?thesis
      by (cases ys) (auto split: if_split_asm intro!: Cons.IH)
  qed
qed

lemma filter_greatest_subseqD:
  "\<exists> x \<in> set zs. \<not> P x" if "subseq zs xs" "length zs > length (filter P xs)"
  using that by (metis filter_id_conv not_subseq_length subseq_filter)

lemma filter_eq_iff_greatest_subseq:
  "filter P xs = ys \<longleftrightarrow>
  subseq ys xs \<and> (\<forall>x \<in> set ys. P x) \<and>
  (\<forall>zs. subseq zs xs \<and> length zs > length ys \<longrightarrow> (\<exists> x \<in> set zs. \<not> P x))"
  using filter_greatest_subseqD filter_eqI by auto

lemma subseq_subsetD:
  "set xs \<subseteq> set ys" if "subseq xs ys"
  using that
  by (intro subsetI) (unfold subseq_singleton_left[symmetric], erule subseq_order.order.trans)

lemma subseq_distinct:
  "distinct xs" if "distinct ys" "subseq xs ys"
  using subseqs_distinctD that by simp

(* XXX Move *)
lemma filter_distinct_eqI:
  assumes
    "subseq ys xs" "\<forall>x \<in> set ys. P x" "\<forall>x \<in> set xs. x \<notin> set ys \<longrightarrow> \<not> P x" "distinct xs"
  shows "filter P xs = ys"
proof (intro filter_eqI, safe)
  fix zs assume prems: "subseq zs xs" "length ys < length zs"
  obtain x where "x \<in> set zs" "x \<notin> set ys"
  proof (atomize_elim, rule ccontr)
    assume "\<nexists>x. x \<in> set zs \<and> x \<notin> set ys"
    then have "set zs \<subseteq> set ys"
      by auto
    moreover from prems assms have "distinct zs" "distinct ys"
      by (blast intro: subseq_distinct)+
    ultimately show False
      using \<open>length ys < length zs\<close>
      by (auto dest: card_mono[rotated] simp: distinct_card[symmetric])
  qed
  with prems assms show "\<exists>x\<in>set zs. \<not> P x"
    by (auto 4 3 dest: subseq_subsetD)
qed (use assms in blast)+

lemma subseq_sorted_wrt:
  "sorted_wrt R xs" if "sorted_wrt R ys" "subseq xs ys"
  using that
  by (induction xs arbitrary: ys)
     (auto 0 4 dest: subseq_subsetD list_emb_ConsD subseq_Cons' simp: sorted_wrt_append)

lemma subseq_sorted:
  "sorted xs" if "sorted ys" "subseq xs ys"
  using that unfolding sorted_sorted_wrt by (rule subseq_sorted_wrt)

lemma sorted_distinct_subset_subseqI:
  assumes "sorted xs" "distinct xs" "sorted ys" "set xs \<subseteq> set ys"
  shows "subseq xs ys"
  using assms
proof (induction ys arbitrary: xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons y ys xs)
  from Cons.prems show ?case
    by (cases xs; simp) (safe; rule Cons.IH; auto 4 4)
qed

lemma sorted_distinct_subseq_iff:
  assumes "sorted ys" "distinct ys"
  shows "subseq xs ys \<longleftrightarrow> (sorted xs \<and> distinct xs \<and> set xs \<subseteq> set ys)"
  using assms
  by safe
     (erule
       subseq_subsetD[THEN subsetD] sorted_distinct_subset_subseqI subseq_distinct subseq_sorted;
       assumption
     )+

lemma list_all2_map_fst_aux:
  assumes "list_all2 (\<lambda>x y. x \<in> Pair y ` (zs y)) xs ys"
  shows "list_all2 (=) (map fst xs) ys"
  using assms by (smt fstI imageE list.rel_mono_strong list_all2_map1)

lemma map_eq_imageD:
  "f ` set xs = set ys" if "map f xs = ys"
  using that by auto

lemma if_contract:
  "(if a then x else if b then x else y) = (if a \<or> b then x else y)" for a x b y
  by (rule SMT.z3_rule)


paragraph \<open>Misc\<close>

lemma fold_evD2:
  assumes
    "P y (fold f xs acc)" "\<not> P y acc"
    "\<And> acc x. \<not> P y acc \<Longrightarrow> Q acc \<Longrightarrow> P y (f x acc) \<Longrightarrow> x \<in> set xs \<Longrightarrow> x = y"
    "Q acc" "\<And> acc x. Q acc \<Longrightarrow> Q (f x acc)" "\<And> acc x. \<not> P y acc \<Longrightarrow> Q acc \<Longrightarrow> P y (f x acc) \<Longrightarrow> R y"
  shows "\<exists> ys zs. xs = ys @ y # zs \<and> \<not> P y (fold f ys acc) \<and> P y (f y (fold f ys acc)) \<and> R y"
proof -
  from fold_evD'[OF assms(2,1)] obtain x ys zs where *:
    "xs = ys @ x # zs" "\<not> P y (fold f ys acc)" "P y (f x (fold f ys acc))"
    by auto
  moreover from assms(4-) have "Q (fold f ys acc)" by (auto intro: fold_acc_preserv)
  moreover from \<open>xs = _\<close> have "x \<in> set xs"
    by auto
  ultimately show ?thesis using assms(3,6) by auto
qed

lemmas fold_evD2' = fold_evD2[where R = "\<lambda> _. True", simplified]

lemma distinct_map_filterI:
  "distinct (List.map_filter f xs)"
  if "\<forall>x \<in> set xs. \<forall>y \<in> set xs. \<forall>a. f x = Some a \<and> f y = Some a \<longrightarrow> x = y" "distinct xs"
  using that by (induction xs) (auto simp: map_filter_simps set_map_filter split: option.split)


paragraph \<open>Implementation auxiliaries\<close>

definition
  "union_map_of xs =
    fold (\<lambda> (x, y) m. case m x of None \<Rightarrow> m(x \<mapsto> [y]) | Some ys \<Rightarrow> m(x \<mapsto> y # ys)) xs Map.empty"

lemma union_map_of_alt_def:
  "union_map_of xs x = (let
    ys = rev (map snd (filter (\<lambda> (x', y). x' = x) xs))
   in if ys = [] then None else Some ys)"
proof -
  have "fold (\<lambda> (x, y) m. case m x of None \<Rightarrow> m(x \<mapsto> [y]) | Some ys \<Rightarrow> m(x \<mapsto> y # ys)) xs m x
  = (let
      ys = rev (map snd (filter (\<lambda> (x', y). x' = x) xs))
    in
    case m x of None \<Rightarrow> if ys = [] then None else Some ys | Some zs \<Rightarrow> Some (ys @ zs))" for x m
    by (induction xs arbitrary: m; clarsimp split: option.split)
  then show ?thesis
    unfolding union_map_of_def by simp
qed

lemma in_union_map_ofI:
  "\<exists> ys. union_map_of xs x = Some ys \<and> y \<in> set ys" if "(x, y) \<in> set xs"
  unfolding union_map_of_alt_def Let_def
  using that apply auto
  using set_filter[of "\<lambda>(x', y). x' = x" xs] apply auto
  done

lemma in_union_map_ofD:
  "(x, y) \<in> set xs" if "union_map_of xs x = Some ys" "y \<in> set ys"
  using that unfolding union_map_of_alt_def by (auto split: if_split_asm)



paragraph \<open>Expression evaluation\<close>

fun bval :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'b :: linorder) bexp \<Rightarrow> bool" where
  "bval s (not e) \<longleftrightarrow> \<not> bval s e" |
  "bval s (and e1 e2) \<longleftrightarrow> bval s e1 \<and> bval s e2" |
  "bval s (bexp.or e1 e2) \<longleftrightarrow> bval s e1 \<or> bval s e2" |
  "bval s (imply e1 e2) \<longleftrightarrow> bval s e1 \<longrightarrow> bval s e2" |
  "bval s (eq i x) \<longleftrightarrow> s i = x" |
  "bval s (le i x) \<longleftrightarrow> s i \<le> x" |
  "bval s (lt i x) \<longleftrightarrow> s i < x" |
  "bval s (ge i x) \<longleftrightarrow> s i \<ge> x" |
  "bval s (gt i x) \<longleftrightarrow> s i > x"

fun eval where
  "eval s (const c) = c"
| "eval s (var x)   = s x"
| "eval s (if_then_else b e1 e2) = (if bval s b then eval s e1 else eval s e2)"

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



lemma check_bexp_determ:
  "b1 = b2" if "check_bexp s e b1" "check_bexp s e b2"
  using that
  by (induction e arbitrary: b1 b2)
     (erule check_bexp.cases; erule check_bexp.cases; simp; blast)+

lemma is_val_determ:
  "v1 = v2" if "is_val s e v1" "is_val s e v2"
  using that by (induction e arbitrary: v1 v2) (auto 4 4 dest: check_bexp_determ elim: is_val.cases)

lemma is_upd_determ:
  "s1 = s2" if "is_upd s f s1" "is_upd s f s2"
  using that
  unfolding is_upd_def
  apply auto
  apply (fo_rule fun_cong)
  apply (fo_rule arg_cong)
  by (smt case_prodE case_prodE' case_prod_conv is_val_determ list.rel_eq list_all2_swap list_all2_trans)

lemma is_upds_determ:
  "s1 = s2" if "is_upds s fs s1" "is_upds s fs s2"
  using that
  by (induction fs arbitrary: s) (auto 4 4 elim: is_upds.cases dest: is_upd_determ)

lemma check_bexp_bval:
  "check_bexp s e (bval (the o s) e)" if "\<forall>x \<in> vars_of_bexp e. x \<in> dom s"
  using that
  by (induction e) (simp; (subst eq_commute)?; rule check_bexp.intros; simp add: dom_def)+

lemma is_val_eval:
  "is_val s e (eval (the o s) e)" if "\<forall>x \<in> vars_of_exp e. x \<in> dom s"
  using that
  apply (induction e)
  subgoal
    by (subst eval.simps, rule is_val.intros) (auto intro: check_bexp_bval)
  by (auto intro: is_val.intros)

lemma is_upd_dom:
  "dom s' = dom s" if "is_upd s upds s'" "\<forall> (x, _) \<in> set upds. x \<in> dom s"
proof -
  have *: "dom (fold (\<lambda>(l, r) s. s(l \<mapsto> r)) xs s) = dom s" if "\<forall>(x, _) \<in> set xs. x \<in> dom s" for xs
  using that
  proof (induction xs arbitrary: s)
    case Nil
    then show ?case 
      by simp
  next
    case (Cons x xs)
    from Cons.prems show ?case
      by simp (subst Cons.IH[simplified], auto split: if_split_asm simp: Cons.IH[simplified])
  qed
  from that show ?thesis
    unfolding is_upd_def by (fastforce dest: list_all2_set2 intro!: *)
qed

lemma is_upds_dom:
  "dom s' = dom s"
  if
  "is_upds s upds s'"
  "\<forall>upd \<in> set upds. \<forall> (x, e) \<in> set upd. x \<in> dom s"
  using that
  by (induction upds arbitrary: s) (erule is_upds.cases; auto simp: is_upd_dom)+

definition mk_upds ::
  "('a \<Rightarrow> ('b :: linorder) option) \<Rightarrow> ('a \<times> ('a, 'b) exp) list \<Rightarrow> ('a \<Rightarrow> 'b option)" where
  "mk_upds s upds = fold (\<lambda>(x, upd) s'. s'(x \<mapsto> eval (the o s) upd)) upds s"

lemma is_upd_make_updI:
  "is_upd s upds (mk_upds s upds)" if "\<forall> (_, e) \<in> set upds. \<forall>x \<in> vars_of_exp e. x \<in> dom s"
  unfolding mk_upds_def
  unfolding is_upd_def
  apply (inst_existentials "map (\<lambda> (x, e). (x, eval (the o s) e)) upds")
  subgoal
    using that by (intro list_all2_all_nthI) (auto 4 3 dest!: nth_mem intro: is_val_eval)
  subgoal
    apply (subst fold_map)
    apply (fo_rule fun_cong)
    apply (fo_rule fun_cong)
    apply (fo_rule arg_cong)
    apply auto
    done
  done

lemma is_upds_make_updsI:
  \<open>is_upds s upds (fold (\<lambda>upd s. mk_upds s upd) upds s)\<close>
  if "\<forall>upd \<in> set upds. \<forall> (_, e) \<in> set upd. \<forall>x \<in> vars_of_exp e. x \<in> dom s"
     "\<forall>upd \<in> set upds. \<forall> (x, e) \<in> set upd. x \<in> dom s"
  using that
  apply (induction upds arbitrary: s)
  apply (auto 4 4 intro: is_upds.intros)
  apply (rule is_upds.intros)
  prefer 2
  apply rprem
  prefer 3
  apply (rule is_upd_make_updI)
  apply force
  subgoal for a upds s
  apply (subst is_upd_dom)
  apply (rule is_upd_make_updI)
  apply force+
  done
  by (subst is_upd_dom) (auto intro: is_upd_make_updI)


locale Simple_Network_Impl_nat =
  Simple_Network_Impl automata
  for automata :: "(nat list \<times> (nat act, nat, nat, int, nat, int) transition list \<times> (nat \<times> (nat, int) cconstraint) list) list" +
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
  assumes action_set:
    "\<forall>a \<in> set broadcast. a < num_actions"
    "\<forall>(_, trans, _) \<in> set automata. \<forall>(_, _, a, _, _, _) \<in> set trans. pred_act (\<lambda>a. a < num_actions) a"
begin

sublocale Reachability_Problem_no_ceiling prod_ta init "\<lambda>_. False" m
proof standard
  show "finite (trans_of prod_ta)"
    apply simp
    unfolding trans_prod_def
    apply safe
    subgoal
      unfolding trans_int_def
      apply auto
      sorry
    sorry
next
  show "finite (range (inv_of prod_ta))"
    apply simp
    unfolding prod_inv_def
    find_theorems Simple_Network_Language.inv map
    unfolding N_def n_ps_def
    apply simp
    sorry
next
  show "clk_set prod_ta \<subseteq> {1..m}"
    sorry
next
  show "\<forall>(_, d)\<in>Timed_Automata.clkp_set prod_ta. d \<in> \<nat>"
    sorry
next
  show "0 < m"
    by (rule has_clock)
qed

paragraph \<open>Fundamentals\<close>

lemma length_automata_eq_n_ps:
  "length automata = n_ps"
  unfolding n_ps_def by simp

lemma mem_trans_N_iff:
  \<open>t \<in> Simple_Network_Language.trans (N i) \<longleftrightarrow> t \<in> set (fst (snd (automata ! i)))\<close> if "i < n_ps"
  unfolding N_def fst_conv snd_conv
  unfolding automaton_of_def
  using that by (cases "automata ! i") (auto simp: length_automata_eq_n_ps)

lemma L_i_len:
  \<open>L ! i < num_states i\<close> if "i < n_ps" "L \<in> states"
  using trans_num_states that
  unfolding states_def by (auto 4 4 simp: mem_trans_N_iff)

lemma L_i_simp:
  \<open>[0..<num_states i] ! (L ! i) = L ! i\<close>
  if "i < n_ps" "L \<in> states"
  using L_i_len[OF that] by simp

lemma L_len[intro, dest]:
  "length L = n_ps" if "L \<in> states"
  using that unfolding states_def by simp

lemma action_setD:
  \<open>pred_act (\<lambda>a'. a' < num_actions) a\<close>
  if \<open>(l, g, a, f, r, l') \<in> Simple_Network_Language.trans (N p)\<close> \<open>p < n_ps\<close>
using that action_set
by (cases "automata ! p")
   (subst (asm) mem_trans_N_iff; force dest!: nth_mem simp flip: length_automata_eq_n_ps)

paragraph \<open>More precise state sets\<close>

definition
  "states' \<equiv> {(L, s). L \<in> states \<and> dom s = {0..<n_vs}}"

lemma states'_states[intro, dest]:
  "L \<in> states" if "(L, s) \<in> states'"
  using that unfolding states'_def by auto

lemma states'_dom[intro, dest]:
  "dom s = {0..<n_vs}" if "(L, s) \<in> states'"
  using that unfolding states'_def by auto

paragraph \<open>Implementation of invariants\<close>

definition
  "invs i \<equiv> let m = default_map_of [] (snd (snd (automata ! i)));
    m' = map (\<lambda> j. m j) [0..<num_states i]
  in m'"

definition
  "invs1 \<equiv> map (\<lambda> i. let m = default_map_of [] (snd (snd (automata ! i)));
    m' = map (\<lambda> j. m j) [0..<num_states i]
  in m') [0..<n_ps]"

definition
  "invs2 \<equiv> IArray (map (\<lambda> i. let m = default_map_of [] (snd (snd (automata ! i)));
    m' = IArray (map (\<lambda> j. m j) [0..<num_states i])
  in m') [0..<n_ps])"

lemma refine_invs2:
  "invs2 !! i !! j = invs1 ! i ! j" if "i < n_ps"
  using that unfolding invs2_def invs1_def by simp

definition
  "inv_fun \<equiv> \<lambda>(L, _).
    concat (map (\<lambda>i. invs1 ! i ! (L ! i)) [0..<n_ps])"

lemma refine_invs1:
  \<open>invs1 ! i = invs i\<close> if \<open>i < n_ps\<close>
  using that unfolding invs_def invs1_def by simp

lemma invs_simp:
  "invs1 ! i ! (L ! i) = Simple_Network_Language.inv (N i) (L ! i)"
  if "i < n_ps" "L \<in> states"
  using that unfolding refine_invs1[OF \<open>i < _\<close>] invs_def N_def fst_conv snd_conv
  by (subst nth_map;
      clarsimp split: prod.split simp: automaton_of_def length_automata_eq_n_ps L_i_len)

lemma inv_fun_inv_of':
  "(inv_fun, inv_of prod_ta) \<in> inv_rel states'"
  unfolding inv_rel_def
  unfolding inv_fun_def
  unfolding inv_of_prod prod_inv_def
  apply clarsimp
  apply (rule arg_cong[where f = concat])
  apply (simp add: invs_simp states'_def cong: map_cong)
  done

lemma inv_fun_alt_def:
  "inv_fun = (\<lambda>(L, _). concat (map (\<lambda>i. invs2 !! i !! (L ! i)) [0..<n_ps]))"
  unfolding inv_fun_def
  apply (intro ext)
  apply (clarsimp simp del: IArray.sub_def)
  apply (fo_rule arg_cong)
  apply (simp add: refine_invs2 del: IArray.sub_def)
  done


paragraph \<open>Implementation of transitions\<close>

definition
  "bounds_map \<equiv> default_map_of (0, 0) bounds'"

definition
  "check_bounded s = bounded bounds_map s"

definition
  "get_commited L =
    List.map_filter (\<lambda>p.
    let l = L ! p in
    if l \<in> set (fst (automata ! p)) then Some (p, l) else None) [0..<n_ps]"

definition
  "trans_map \<equiv>
  let f = (\<lambda>i.
    let m = union_map_of (fst (snd (automata ! i))) in (\<lambda>j.
      case m j of
        None \<Rightarrow> []
      | Some xs \<Rightarrow> xs
    ))
  in f"

definition
  "trans_i_map i j \<equiv>
    List.map_filter
      (\<lambda> (g, a, m, l'). case a of Sil a \<Rightarrow> Some (g, a, m, l') | _ \<Rightarrow> None)
    (trans_map i j)"

definition
  "int_trans_from_loc p l L s \<equiv>
    let trans = trans_i_map p l
    in
    List.map_filter (\<lambda> (g, a, f, r, l').
      let s' = mk_upds s f in
        if check_bounded s' then Some (g, Internal a, r, (L[p := l'], s'))
        else None
    ) trans"

definition
  "int_trans_from_vec pairs L s \<equiv>
    concat (map (\<lambda>(p, l). int_trans_from_loc p l L s) pairs)"

definition
  "int_trans_from_all L s \<equiv>
    concat (map (\<lambda>p. int_trans_from_loc p (L ! p) L s) [0..<n_ps])"

definition
  "int_trans_from \<equiv> \<lambda> (L, s).
    let pairs = get_commited L in
    if pairs = []
    then int_trans_from_all L s
    else int_trans_from_vec pairs L s
  "

definition
  "actions_by_state i \<equiv> fold (\<lambda> t acc. acc[fst (snd t) := (i, t) # (acc ! fst (snd t))])"

definition
  "all_actions_by_state t L \<equiv>
    fold (\<lambda> i. actions_by_state i (t i (L ! i))) [0..<n_ps] (repeat [] num_actions)"

definition
  "all_actions_from_vec t vec \<equiv>
    fold (\<lambda>(p, l). actions_by_state p (t p l)) vec (repeat [] num_actions)"

definition
  "pairs_by_action L s OUT IN \<equiv>
  concat (
    map (\<lambda> (p, g1, a1, f1, r1, l1).
      List.map_filter (\<lambda> (q, g2, a2, f2, r2, l2).
        if p = q then None else
          let s' = mk_upds (mk_upds s f1) f2 in
          if check_bounded s' then Some (g1 @ g2, Bin a1, r1 @ r2, (L[p := l1, q := l2], s'))
          else None
    ) OUT) IN)
  "

definition
  "trans_in_map i j \<equiv>
    List.map_filter
      (\<lambda> (g, a, m, l'). case a of In a \<Rightarrow> Some (g, a, m, l') | _ \<Rightarrow> None)
    (trans_map i j)"

definition
  "trans_out_map i j \<equiv>
    List.map_filter
      (\<lambda> (g, a, m, l'). case a of Out a \<Rightarrow> Some (g, a, m, l') | _ \<Rightarrow> None)
    (trans_map i j)"

definition
  "bin_trans_from \<equiv> \<lambda>(L, s).
    let
      pairs = get_commited L;
      In =  all_actions_by_state trans_in_map L;
      Out = all_actions_by_state trans_out_map L
    in
    if pairs = [] then
      concat (map (\<lambda>a. pairs_by_action L s (Out ! a) (In ! a)) [0..<num_actions])
    else
      let
        In2  = all_actions_from_vec trans_in_map pairs;
        Out2 = all_actions_from_vec trans_out_map pairs
      in
        concat (map (\<lambda>a. pairs_by_action L s (Out ! a) (In2 ! a)) [0..<num_actions])
      @ concat (map (\<lambda>a. pairs_by_action L s (Out2 ! a) (In ! a)) [0..<num_actions])
    "

definition
  "trans_in_broad_map i j \<equiv>
    List.map_filter
      (\<lambda> (g, a, m, l').
      case a of In a \<Rightarrow> if a \<in> set broadcast then Some (g, a, m, l') else None | _ \<Rightarrow> None)
    (trans_map i j)"

definition
  "trans_out_broad_map i j \<equiv>
    List.map_filter
      (\<lambda> (g, a, m, l').
      case a of Out a \<Rightarrow> if a \<in> set broadcast then Some (g, a, m, l') else None | _ \<Rightarrow> None)
    (trans_map i j)"

definition
  "actions_by_state' xs \<equiv>
    fold (\<lambda> t acc. acc[fst (snd t) := t # (acc ! fst (snd t))]) xs (repeat [] num_actions)"

definition
  "trans_out_broad_grouped i j \<equiv> actions_by_state' (trans_out_broad_map i j)"

definition
  "trans_in_broad_grouped i j \<equiv> actions_by_state' (trans_in_broad_map i j)"

definition
  "pair_by_action OUT IN \<equiv>
  concat (
    map (\<lambda>(g1, a, r1, (L, s)).
      List.map (\<lambda>(q, g2, a2, f2, r2, l2).
          (g1 @ g2, a, r1 @ r2, (L[q := l2], mk_upds s f2))
    ) OUT) IN)
  "

definition make_combs where
  "make_combs p a xs \<equiv>
    let
      ys = List.map_filter
        (\<lambda>i.
          if i = p then None
          else if xs ! i ! a = [] then None
          else Some (map (\<lambda>t. (i, t)) (xs ! i ! a))
        )
        [0..<n_ps]
    in if ys = [] then [] else product_lists ys
  "

definition make_combs_from_pairs where
  "make_combs_from_pairs p a pairs xs \<equiv>
    let
      ys = List.map_filter
        (\<lambda>i.
          if i = p then None
          else if xs ! i ! a = [] then None
          else Some (map (\<lambda>t. (i, t)) (xs ! i ! a))
        )
        [0..<n_ps]
    in if ys = [] then [] else product_lists ys
  "

term List.find
term list_ex

term "a \<and> b"

definition
  "broad_trans_from \<equiv> \<lambda>(L, s).
    let
      pairs = get_commited L;
      In  = map (\<lambda>p. trans_in_broad_grouped p (L ! p)) [0..<n_ps];
      Out = map (\<lambda>p. trans_out_broad_grouped p (L ! p)) [0..<n_ps]
    in
    if pairs = [] then
      concat (
        map (\<lambda>a.
          concat (map (\<lambda>p.
            let
              outs = Out ! p ! a
            in if outs = [] then []
            else
              let
                combs = make_combs p a In;
                outs = map (\<lambda>t. (p, t)) outs;
                combs = concat (map (\<lambda>x. map (\<lambda>xs. x # xs) combs) outs);
                init = ([], Broad a, [], (L, s))
              in
              List.map_filter (\<lambda>comb.
                let (g, a, r, L', s) =
                  fold
                    (\<lambda>(q, g2, a2, f2, r2, l2) (g1, a, r1, (L, s)).
                      (g1 @ g2, a, r1 @ r2, (L[q := l2], mk_upds s f2))
                    )
                    comb
                    init
                in if check_bounded s then Some (g, a, r, L', s) else None
              ) combs
          )
          [0..<n_ps])
        )
      [0..<num_actions])
      (* concat (map (\<lambda>a. pairs_by_action L s (Out ! a) (In ! a)) [0..<num_actions]) *)
    else
      concat (
        map (\<lambda>a.
          let
            ins_commited = List.map_filter (\<lambda>(p, _). if In ! p ! a \<noteq> [] then Some p else None) pairs;
            always_commited = (length ins_commited > 1)
          in
          concat (map (\<lambda>p.
            let
              outs = Out ! p ! a
            in if outs = [] then []
            else if
              \<not> always_commited \<and> (ins_commited = [p] \<or> ins_commited = [])
              \<and> \<not> list_ex (\<lambda> (q, _). q = p) pairs
            then []
            else
              let
                combs = make_combs p a In;
                outs = map (\<lambda>t. (p, t)) outs;
                combs = concat (map (\<lambda>x. map (\<lambda>xs. x # xs) combs) outs);
                init = ([], Broad a, [], (L, s))
              in
              List.map_filter (\<lambda>comb.
                let (g, a, r, L', s) =
                  fold
                    (\<lambda>(q, g2, a2, f2, r2, l2) (g1, a, r1, (L, s)).
                      (g1 @ g2, a, r1 @ r2, (L[q := l2], mk_upds s f2))
                    )
                    comb
                    init
                in if check_bounded s then Some (g, a, r, L', s) else None
              ) combs
          )
          [0..<n_ps])
        )
      [0..<num_actions])
    "

lemma
  "List.map_filter f xs = map the (List.filter (\<lambda> x. x \<noteq> None) (map f xs))"
  oops

lemma filter_map_map_filter:
  "filter P (map f xs) = List.map_filter (\<lambda> x. let y = f x in if P y then Some y else None) xs"
  by (induction xs; simp add: Let_def List.map_filter_simps)

lemma broad_trans_from_alt_def:
  "broad_trans_from \<equiv> \<lambda>(L, s).
    let
      pairs = get_commited L;
      In  = map (\<lambda>p. trans_in_broad_grouped p (L ! p)) [0..<n_ps];
      Out = map (\<lambda>p. trans_out_broad_grouped p (L ! p)) [0..<n_ps]
    in
    if pairs = [] then
      concat (
        map (\<lambda>a.
          concat (map (\<lambda>p.
            let
              outs = Out ! p ! a
            in if outs = [] then []
            else
              let
                combs = make_combs p a In;
                outs = map (\<lambda>t. (p, t)) outs;
                combs = concat (map (\<lambda>x. map (\<lambda> xs. x # xs) combs) outs);
                init = ([], Broad a, [], (L, s))
              in
              filter (\<lambda> (g, a, r, L, s). check_bounded s) (
                map (\<lambda>comb.
                    fold
                      (\<lambda>(q, g2, a2, f2, r2, l2) (g1, a, r1, (L, s)).
                        (g1 @ g2, a, r1 @ r2, (L[q := l2], mk_upds s f2))
                      )
                      comb
                      init
                ) combs)
          )
          [0..<n_ps])
        )
      [0..<num_actions])
      (* concat (map (\<lambda>a. pairs_by_action L s (Out ! a) (In ! a)) [0..<num_actions]) *)
    else
      concat (
        map (\<lambda>a.
          let
            ins_commited = List.map_filter (\<lambda>(p, _). if In ! p ! a \<noteq> [] then Some p else None) pairs
          in
          concat (map (\<lambda>p.
            let
              outs = Out ! p ! a
            in if outs = [] then []
            else if
              (ins_commited = [p] \<or> ins_commited = []) \<and> \<not> list_ex (\<lambda>(q, _). q = p) pairs
            then []
            else
              let
                combs = make_combs p a In;
                outs = map (\<lambda>t. (p, t)) outs;
                combs = concat (map (\<lambda>x. map (\<lambda>xs. x # xs) combs) outs);
                init = ([], Broad a, [], (L, s))
              in
              filter (\<lambda> (g, a, r, L, s). check_bounded s) (
                map (\<lambda>comb.
                    fold
                      (\<lambda>(q, g2, a2, f2, r2, l2) (g1, a, r1, (L, s)).
                        (g1 @ g2, a, r1 @ r2, (L[q := l2], mk_upds s f2))
                      )
                      comb
                      init
                ) combs)
          )
          [0..<n_ps])
        )
      [0..<num_actions])
    "
  apply (rule eq_reflection)
  unfolding broad_trans_from_def
  unfolding filter_map_map_filter
  unfolding Let_def
  by (fo_rule
      arg_cong2[where f = map] arg_cong2[where f = List.map_filter] arg_cong HOL.refl |
      rule if_cong ext | auto split: if_split_asm)+

lemma bounds_bounds_map:
  "bounds = bounds_map"
  unfolding bounds_def bounds_map_def by simp

lemma check_bounded_iff:
  "Simple_Network_Language.bounded bounds s \<longleftrightarrow> check_bounded s"
  unfolding check_bounded_def Simple_Network_Language.bounded_def bounds_bounds_map ..

lemma get_commited_mem_iff:
  "(p, l) \<in> set (get_commited L) \<longleftrightarrow> (l = L ! p \<and> l \<in> commited (N p) \<and> p < n_ps)"
  unfolding get_commited_def
  unfolding set_map_filter Let_def
  apply clarsimp
  unfolding N_def fst_conv snd_conv
  by safe
    ((subst nth_map | subst (asm) nth_map);
      auto split: prod.splits simp: automaton_of_def length_automata_eq_n_ps
    )+

lemma get_commited_empty_iff:
  "(\<forall>p < n_ps. L ! p \<notin> commited (N p)) \<longleftrightarrow> get_commited L = []"
  apply safe
  subgoal
    apply (rule ccontr)
  proof -
    assume prems:
      "\<forall>p<n_ps. L ! p \<notin> commited (N p)" and
      "get_commited L \<noteq> []"
    then obtain p l where "(p, l) \<in> set (get_commited L)"
      by (metis length_greater_0_conv nth_mem old.prod.exhaust)
    from this[unfolded get_commited_mem_iff] prems(1)
    show "False"
      by auto
  qed
  subgoal for p
    using get_commited_mem_iff[of p "L ! p" L]
    by auto
  done

lemma is_upd_make_updI2:
  "is_upd s upds (mk_upds s upds)"
  if "(l, g, a, upds, r, l') \<in> Simple_Network_Language.trans (N p)" "p < n_ps"
  "dom s = {0..<n_vs}"
  apply (rule is_upd_make_updI)
  using that using var_set
  by (subst (asm) mem_trans_N_iff) (auto 4 5 simp flip: length_automata_eq_n_ps dest!: nth_mem)

lemma is_upd_dom2:
  "dom s' = {0..<n_vs}" if "is_upd s f s'"
  "(l, g, a, f, r, l') \<in> Simple_Network_Language.trans (N p)" "p < n_ps"
  "dom s = {0..<n_vs}"
unfolding that(4)[symmetric]
using that(2,3,4) var_set
apply (cases "automata ! p")
apply (rule is_upd_dom, rule that)
apply (subst (asm) mem_trans_N_iff)
apply (auto simp flip: length_automata_eq_n_ps)
apply (drule nth_mem)
apply (auto 0 5)
done

lemma is_updD:
  "s' = mk_upds s f" if "is_upd s f s'"
  "(l, g, a, f, r, l') \<in> Simple_Network_Language.trans (N p)" "p < n_ps"
  "dom s = {0..<n_vs}"
proof -
  from is_upd_make_updI2[OF that(2-)] have "is_upd s f (mk_upds s f)" .
  from is_upd_determ[OF that(1) this] show ?thesis .
qed

lemma is_upds_make_updsI2:
  "is_upds s upds (fold (\<lambda>upd s. mk_upds s upd) upds s)"
  if "\<forall>upd \<in> set upds. \<exists>p < n_ps. \<exists>l g a r l'. (l, g, a, upd, r, l') \<in> Simple_Network_Language.trans (N p)"
  "dom s = {0..<n_vs}"
  apply (rule is_upds_make_updsI)
  subgoal
  using that using var_set
  apply intros
  apply (drule bspec)
  apply assumption
  apply elims
  apply (auto 4 5 simp flip: length_automata_eq_n_ps simp add: mem_trans_N_iff dest!: nth_mem)
  done
  subgoal
  using that using var_set
  apply intros
  apply (drule bspec)
  apply assumption
  apply elims
  apply (auto 4 5 simp flip: length_automata_eq_n_ps simp add: mem_trans_N_iff dest!: nth_mem)
  done
  done

lemma is_updsD:
  assumes 
    "dom s = {0..<n_vs}" and
    "\<forall>p\<in>set ps.
        (ls p, gs p, a, fs p, rs p, ls' p)
        \<in> Simple_Network_Language.trans (N p)" and
    "set ps \<subseteq> {0..<n_ps}" and
    "is_upds s (map fs ps) s'"
  shows "s' = fold (\<lambda>p s. mk_upds s (fs p)) ps s"
proof -
  let ?upds = "map fs ps"
  have "is_upds s ?upds (fold (\<lambda>upd s. mk_upds s upd) ?upds s)"
    using assms(1-3) by (intro is_upds_make_updsI2; force)
  from is_upds_determ[OF assms(4) this] show ?thesis
    by (simp add: fold_map comp_def)
qed



context
  notes [simp] = length_automata_eq_n_ps
begin

lemma trans_mapI:
  assumes
    "(L ! p, g, a, f, r, l') \<in> Simple_Network_Language.trans (N p)"
    "p < n_ps"
  shows
    "(g, a, f, r, l') \<in> set (trans_map p (L ! p))"
  using assms unfolding trans_map_def N_def fst_conv snd_conv
  by (subst (asm) nth_map) (auto dest: in_union_map_ofI split: prod.split_asm simp: automaton_of_def)

lemma trans_i_mapI:
  assumes
    "(L ! p, g, Sil a', f, r, l') \<in> Simple_Network_Language.trans (N p)"
    "p < n_ps"
  shows
    "(g, a', f, r, l') \<in> set (trans_i_map p (L ! p))"
  using assms unfolding trans_i_map_def set_map_filter by (fastforce dest: trans_mapI)

lemma trans_mapI':
  assumes
    "(l, g, a, f, r, l') \<in> Simple_Network_Language.trans (N p)"
    "p < n_ps"
  shows
    "(g, a, f, r, l') \<in> set (trans_map p l)"
  using assms unfolding trans_map_def N_def fst_conv snd_conv
  by (subst (asm) nth_map) (auto dest: in_union_map_ofI split: prod.split_asm simp: automaton_of_def)

lemma trans_mapD:
  assumes
    "(g, a, f, r, l') \<in> set (trans_map p l)"
    "p < n_ps"
  shows
    "(l, g, a, f, r, l') \<in> Simple_Network_Language.trans (N p)"
  using assms unfolding trans_map_def N_def fst_conv snd_conv
  by (subst nth_map) (auto split: prod.split elim: in_union_map_ofD[rotated] simp: automaton_of_def)

lemma trans_map_iff:
  assumes
    "p < n_ps"
  shows
    "(g, a, f, r, l') \<in> set (trans_map p l)
 \<longleftrightarrow> (l, g, a, f, r, l') \<in> Simple_Network_Language.trans (N p)"
    using trans_mapD trans_mapI' \<open>p < n_ps\<close> by auto

lemma trans_i_mapD:
  assumes
    "(g, a', f, r, l') \<in> set (trans_i_map p (L ! p))"
    "p < n_ps"
  shows
    "(L ! p, g, Sil a', f, r, l') \<in> Simple_Network_Language.trans (N p)"
  using assms unfolding trans_i_map_def set_map_filter
  by (force split: act.split_asm intro: trans_mapD)

lemma int_trans_from_correct:
  "(int_trans_from, trans_int) \<in> transition_rel states'"
  unfolding transition_rel_def
  apply clarsimp
  subgoal for L s g a r L' s'
  proof -
    assume "(L, s) \<in> states'"
    then have "L \<in> states" "dom s = {0..<n_vs}"
      by auto
    then have [simp]: "length L = n_ps"
      by auto
    show "(((L, s), g, a, r, L', s') \<in> trans_int) = ((g, a, r, L', s') \<in> set (int_trans_from (L, s)))"
    proof (cases "get_commited L = []")
      case True
      then have *: "((L, s), g, a, r, L', s') \<in> trans_int \<longleftrightarrow>
      ((L, s), g, a, r, L', s') \<in> {((L, s), g, Internal a, r, (L', s')) | L s l g f p a r l' L' s'.
        (l, g, Sil a, f, r, l') \<in> trans (N p) \<and>
        (\<forall>p < n_ps. L ! p \<notin> commited (N p)) \<and>
        L!p = l \<and> p < length L \<and> L' = L[p := l'] \<and> is_upd s f s' \<and>
        bounded bounds s' \<and> L \<in> states
      }"
        unfolding get_commited_empty_iff[symmetric]
        unfolding trans_int_def
        by blast
      from True have **: "int_trans_from (L, s) = int_trans_from_all L s"
        unfolding int_trans_from_def by simp
      from \<open>dom s = _\<close> show ?thesis
        unfolding * **
        apply clarsimp
        unfolding int_trans_from_all_def
        apply clarsimp
        unfolding int_trans_from_loc_def Let_def set_map_filter
        apply clarsimp
        apply safe
        subgoal for f p a' l'
          by (fastforce intro: trans_i_mapI simp: check_bounded_iff dest!: is_updD)
        subgoal for p _ a' upds l'
          apply mini_ex
          apply (intros)
                apply solve_triv
               defer
               defer
               apply solve_triv
          unfolding check_bounded_iff
              apply (rule is_upd_make_updI2[OF trans_i_mapD])
                 apply solve_triv+
            apply (rule \<open>L \<in> states\<close>)
           apply (erule trans_i_mapD, assumption)
          using True[folded get_commited_empty_iff]
          by auto
        done
    next
      case False
      then have *: "((L, s), g, a, r, L', s') \<in> trans_int \<longleftrightarrow>
      ((L, s), g, a, r, L', s') \<in> {((L, s), g, Internal a, r, (L', s')) | L s l g f p a r l' L' s'.
        (l, g, Sil a, f, r, l') \<in> trans (N p) \<and>
        l \<in> commited (N p) \<and>
        L!p = l \<and> p < length L \<and> L' = L[p := l'] \<and> is_upd s f s' \<and>
        bounded bounds s' \<and> L \<in> states
      }"
        unfolding get_commited_empty_iff[symmetric]
        unfolding trans_int_def
        by blast
      from False have **: "int_trans_from (L, s) = int_trans_from_vec (get_commited L) L s"
        unfolding int_trans_from_def by simp
      from \<open>dom s = _\<close> \<open>L \<in> states\<close> show ?thesis
        unfolding * **
        apply clarsimp
        unfolding int_trans_from_vec_def
        apply clarsimp
        unfolding int_trans_from_loc_def Let_def set_map_filter
        apply clarsimp
        apply safe
        subgoal for f p a' l'
          unfolding check_bounded_iff
          apply mini_ex
          apply (intros add: bexI)
          unfolding get_commited_mem_iff
                 apply (drule is_updD)
                 apply simp
                apply solve_triv+
               apply (rule trans_i_mapI, assumption)
               apply solve_triv+
           apply (drule is_updD, simp, solve_triv+)
          unfolding get_commited_mem_iff
          apply simp
          done
        subgoal for p _ a' upds l'
          apply mini_ex
          apply (intros)
               apply solve_triv
              apply (rule trans_i_mapD)
          unfolding get_commited_mem_iff
               apply simp
              apply solve_triv+
             apply blast
            apply solve_triv+
           apply (rule is_upd_make_updI2[OF trans_i_mapD])
              apply solve_triv+
          unfolding check_bounded_iff .
        done
    qed
  qed
  done


paragraph \<open>Mostly copied\<close>

lemma in_actions_by_stateI:
  assumes
    "(g1, a, r1) \<in> set xs" "a < length acc"
  shows
    "(q, g1, a, r1) \<in> set (actions_by_state q xs acc ! a)
    \<and> a < length (actions_by_state q xs acc)"
  using assms unfolding actions_by_state_def
  apply (induction xs arbitrary: acc)
    apply (simp; fail)
  apply simp
  apply (erule disjE)
    apply (rule fold_acc_preserv
      [where P = "\<lambda> acc. (q, g1, a, r1) \<in> set (acc ! a) \<and> a < length acc"]
      )
    apply (subst list_update_nth_split; auto)
  by auto

lemma in_actions_by_state'I:
  assumes
    "(g1, a, r1) \<in> set xs" "a < num_actions"
  shows
    "(g1, a, r1) \<in> set (actions_by_state' xs ! a)
    \<and> a < length (actions_by_state' xs)"
proof -
  let ?f = "(\<lambda>t acc. acc[fst (snd t) := t # acc ! fst (snd t)])"
  have "(g1, a, r1) \<in> set (fold ?f xs acc ! a)
    \<and> a < length (fold ?f xs acc)" if "a < length acc" for acc
    using assms(1) that
    apply (induction xs arbitrary: acc)
      apply (simp; fail)
    apply simp
    apply (erule disjE)
      apply (rule fold_acc_preserv
        [where P = "\<lambda> acc. (g1, a, r1) \<in> set (acc ! a) \<and> a < length acc"]
        )
      apply (subst list_update_nth_split; auto)
    by auto
  with \<open>a < _\<close> show ?thesis
    unfolding actions_by_state'_def by simp
qed

  lemma in_actions_by_state_preserv:
    assumes
      "(q, g1, a, r1) \<in> set (acc ! a)" "a < length acc"
    shows
      "(q, g1, a, r1) \<in> set (actions_by_state y xs acc ! a)
      \<and> a < length (actions_by_state y xs acc)"
    using assms unfolding actions_by_state_def
    apply -
    apply (rule fold_acc_preserv
        [where P = "\<lambda> acc. (q, g1, a, r1) \<in> set (acc ! a) \<and> a < length acc"]
        )
    apply (subst list_update_nth_split; auto)
    by auto

  lemma length_actions_by_state_preserv[simp]:
    shows "length (actions_by_state y xs acc) = length acc"
    unfolding actions_by_state_def by (auto intro: fold_acc_preserv simp: list_update_nth_split)

  lemma in_all_actions_by_stateI:
    assumes
      "a < num_actions" "q < n_ps" "(g1, a, r1) \<in> set (M q (L ! q))"
    shows
      "(q, g1, a, r1) \<in> set (all_actions_by_state M L ! a)"
    unfolding all_actions_by_state_def
    apply (rule fold_acc_ev_preserv
        [where P = "\<lambda> acc. (q, g1, a, r1) \<in> set (acc ! a)" and Q = "\<lambda> acc. a < length acc",
          THEN conjunct1]
        )
        apply (rule in_actions_by_state_preserv[THEN conjunct1])
    using assms by (auto intro: in_actions_by_stateI[THEN conjunct1])

  lemma in_all_actions_from_vecI:
    assumes
      "a < num_actions" "(g1, a, r1) \<in> set (M q l)" "(q, l) \<in> set pairs"
    shows
      "(q, g1, a, r1) \<in> set (all_actions_from_vec M pairs ! a)"
    unfolding all_actions_from_vec_def using assms
    by (intro fold_acc_ev_preserv
        [where P = "\<lambda> acc. (q, g1, a, r1) \<in> set (acc ! a)" and Q = "\<lambda> acc. a < length acc",
          THEN conjunct1])
      (auto intro: in_actions_by_stateI[THEN conjunct1] in_actions_by_state_preserv[THEN conjunct1])

  lemma actions_by_state_inj:
    assumes "j < length acc"
    shows "\<forall> (q, a) \<in> set (actions_by_state i xs acc ! j). (q, a) \<notin> set (acc ! j) \<longrightarrow> i = q"
    unfolding actions_by_state_def
    apply (rule fold_acc_preserv
        [where P =
          "\<lambda> acc'. (\<forall> (q, a) \<in> set (acc' ! j). (q, a) \<notin> set (acc ! j) \<longrightarrow> i = q) \<and> j < length acc'",
          THEN conjunct1])
    subgoal for x acc
      by (cases "fst (snd x) = j"; simp)
    using assms by auto

  lemma actions_by_state_inj':
    assumes "j < length acc" "(q, a) \<notin> set (acc ! j)" "(q, a) \<in> set (actions_by_state i xs acc ! j)"
    shows "i = q"
    using actions_by_state_inj[OF assms(1)] assms(2-) by fast

  lemma in_actions_by_stateD:
    assumes
      "(q, g, a, t) \<in> set (actions_by_state i xs acc ! j)" "(q, g, a, t) \<notin> set (acc ! j)"
      "j < length acc"
    shows
      "(g, a, t) \<in> set xs \<and> j = a"
    using assms unfolding actions_by_state_def
    apply -
    apply (drule fold_evD
        [where y = "(g, a, t)" and Q = "\<lambda> acc'. length acc' = length acc"
          and R = "\<lambda> (_, a', t). a' = j"]
        )
         apply assumption
      (* XXX Define asm split rule *)
        apply (subst (asm) list_update_nth_split[of j]; force)
       apply simp+
     apply (subst (asm) list_update_nth_split[of j]; force)
    by auto

lemma in_actions_by_state'D:
  assumes
    "(g, a, r) \<in> set (actions_by_state' xs ! a')" "a' < num_actions"
  shows
    "(g, a, r) \<in> set xs \<and> a' = a"
proof -
  let ?f = "(\<lambda>t acc. acc[fst (snd t) := t # acc ! fst (snd t)])"
  have "(g, a, r) \<in> set xs \<and> a' = a"
    if "(g, a, r) \<in> set (fold ?f xs acc ! a')" "(g, a, r) \<notin> set (acc ! a')" "a' < length acc" for acc
    using that
      apply -
      apply (drule fold_evD
        [where y = "(g, a, r)" and Q = "\<lambda> acc'. length acc' = length acc"
          and R = "\<lambda> (_, a, t). a = a'"]
        )
      apply ((subst (asm) list_update_nth_split[where j = a'])?; auto; fail)+
      done
  with assms show ?thesis
    unfolding actions_by_state'_def by auto
qed

  lemma in_all_actions_by_stateD:
    assumes
      "(q, g1, a, r1) \<in> set (all_actions_by_state M L ! a')" "a' < num_actions"
    shows
      "(g1, a, r1) \<in> set (M q (L ! q)) \<and> q < n_ps \<and> a' = a"
    using assms
    unfolding all_actions_by_state_def
    apply -
    apply (drule fold_evD''[where y = q and Q = "\<lambda> acc. length acc = num_actions"])
        apply (simp; fail)
       apply (drule actions_by_state_inj'[rotated])
         apply (simp; fail)+
    apply safe
      apply (drule in_actions_by_stateD)
        apply assumption
       apply (rule fold_acc_preserv)
        apply (simp; fail)+
    subgoal premises prems
    proof -
      from prems(2) have "q \<in> set [0..<n_ps]" by auto
      then show ?thesis by simp
    qed
    by (auto intro: fold_acc_preserv dest!: in_actions_by_stateD)

  lemma length_all_actions_by_state_preserv:
    "length (all_actions_by_state M L) = num_actions"
    unfolding all_actions_by_state_def by (auto intro: fold_acc_preserv)
  
lemma all_actions_from_vecD:
  assumes
    "(q, g1, a, r1) \<in> set (all_actions_from_vec M pairs ! a')" "a' < num_actions"
    "distinct (map fst pairs)"
  shows
    "\<exists> l. (q, l) \<in> set pairs \<and> (g1, a, r1) \<in> set (M q l) \<and> a' = a"
    using assms(1,2)
    unfolding all_actions_from_vec_def
    apply -
    apply (drule fold_evD2'[where
      y = "(q, SOME l. (q, l) \<in> set pairs)"
      and Q = "\<lambda> acc. length acc = num_actions"])
      apply (clarsimp; fail)
      apply clarsimp
      apply (drule actions_by_state_inj'[rotated])
      apply assumption
      apply assumption
      apply simp
      subgoal
      using assms(3) by (meson distinct_map_fstD someI_ex)
      apply (auto intro: fold_acc_preserv dest!: in_actions_by_stateD)
      subgoal premises prems for ys zs
      using prems(4) by (subst \<open>pairs = _\<close>) auto
    done

  lemma all_actions_from_vecD2:
    assumes
      "(q, g1, a, r1) \<in> set (all_actions_from_vec M pairs ! a')" "a' < num_actions"
      "(q, l) \<in> set pairs" "distinct (map fst pairs)"
    shows
      "(g1, a, r1) \<in> set (M q l) \<and> a' = a"
    using assms(1,2,3)
    unfolding all_actions_from_vec_def
    apply -
    apply (drule fold_evD2'[where y = "(q, l)" and Q = "\<lambda> acc. length acc = num_actions"])
        apply (clarsimp; fail)
        apply clarsimp
       apply (drule actions_by_state_inj'[rotated])
       apply assumption
       apply assumption
       apply simp
       subgoal
       using assms(4) by (meson distinct_map_fstD)
       by (auto intro: fold_acc_preserv dest!: in_actions_by_stateD)

lemma bin_trans_from_correct:
  "(bin_trans_from, trans_bin) \<in> transition_rel states'"
  unfolding transition_rel_def
  apply clarsimp
  subgoal for L s g a r L' s'
  proof -
    assume "(L, s) \<in> states'"
    then have "L \<in> states" "dom s = {0..<n_vs}"
      by auto
    then have [simp]: "length L = n_ps"
      by auto
    define IN where "IN =  all_actions_by_state trans_in_map L"
    define OUT where "OUT =  all_actions_by_state trans_out_map L"
    have IN_I:
      "(p, g, a', f, r, l') \<in> set (IN ! a')"
      if "(L ! p, g, In a', f, r, l') \<in> Simple_Network_Language.trans (N p)"
        "p < n_ps" "a' < num_actions"
      for p g a' f r l'
    proof -
      from trans_mapI[OF that(1,2)] have "(g, In a', f, r, l') \<in> set (trans_map p (L ! p))"
        by auto
      then have "(g, a', f, r, l') \<in> set (trans_in_map p (L ! p))"
        unfolding trans_in_map_def set_map_filter by (auto 4 6)
      with \<open>p < _\<close> \<open>a' < _\<close> show ?thesis
        unfolding IN_def by (intro in_all_actions_by_stateI)
    qed
    have OUT_I:
      "(p, g, a', f, r, l') \<in> set (OUT ! a')"
      if "(L ! p, g, Out a', f, r, l') \<in> Simple_Network_Language.trans (N p)"
        "p < n_ps" "a' < num_actions"
      for p g a' f r l'
    proof -
      from trans_mapI[OF that(1,2)] have "(g, Out a', f, r, l') \<in> set (trans_map p (L ! p))"
        by auto
      then have "(g, a', f, r, l') \<in> set (trans_out_map p (L ! p))"
        unfolding trans_out_map_def set_map_filter by (auto 4 6)
      with \<open>p < _\<close> \<open>a' < _\<close> show ?thesis
        unfolding OUT_def by (intro in_all_actions_by_stateI)
    qed
    have IN_D:
      "(L ! p, g, In a', f, r, l') \<in> Simple_Network_Language.trans (N p) \<and> p < n_ps \<and> a' = a1"
      if "(p, g, a', f, r, l') \<in> set (IN ! a1)" "a1 < num_actions"
      for p g a' f r l' a1
      using that
      unfolding IN_def
      apply -
      apply (drule in_all_actions_by_stateD)
       apply assumption
      unfolding trans_in_map_def set_map_filter
      apply (auto split: option.split_asm)
      apply (auto split: act.split_asm dest: trans_mapD)
      done
    have OUT_D:
      "(L ! p, g, Out a1, f, r, l') \<in> Simple_Network_Language.trans (N p) \<and> p < n_ps"
      if "(p, g, a', f, r, l') \<in> set (OUT ! a1)" "a1 < num_actions"
      for p g a' f r l' a1
      using that
      unfolding OUT_def
      apply -
      apply (drule in_all_actions_by_stateD)
       apply assumption
      unfolding trans_out_map_def set_map_filter
      apply (auto split: option.split_asm)
      apply (auto split: act.split_asm dest: trans_mapD)
      done
    have IN_p_num:
      "p < n_ps"
      if "(p, g, a', f, r, l') \<in> set (IN ! a1)" "a1 < num_actions"
      for p g a' f r l' a1
      using that
      unfolding IN_def
      apply -
      apply (drule in_all_actions_by_stateD)
       apply assumption
      by (auto split: option.split_asm)
    have OUT_p_num:
      "p < n_ps"
      if "(p, g, a', f, r, l') \<in> set (OUT ! a1)" "a1 < num_actions"
      for p g a' f r l' a1
      using that
      unfolding OUT_def
      apply -
      apply (drule in_all_actions_by_stateD)
       apply assumption
      by (auto split: option.split_asm)
    have actions_unique:
      "a' = a1"
      if "(p, g, a', f, r, l') \<in> set (IN ! a1)" "a1 < num_actions"
      for p g a' f r l' a1
      using that
      unfolding IN_def
      apply -
      apply (drule in_all_actions_by_stateD)
       apply assumption
      unfolding trans_in_map_def set_map_filter
      by (auto split: option.split_asm)
    show "(((L, s), g, a, r, L', s') \<in> trans_bin) =
        ((g, a, r, L', s') \<in> set (bin_trans_from (L, s)))"
    proof (cases "get_commited L = []")
      case True
      with get_commited_empty_iff[of L] have "\<forall>p<n_ps. L ! p \<notin> commited (N p)"
        by simp
      then have *: "((L, s), g, a, r, L', s') \<in> trans_bin \<longleftrightarrow> ((L, s), g, a, r, L', s') \<in>
      {((L, s), g1 @ g2, Bin a, r1 @ r2, (L', s'')) |
        L s L' s' s'' a p q l1 g1 f1 r1 l1' l2 g2 f2 r2 l2'.
        (l1, g1, In a,  f1, r1, l1') \<in> trans (N p) \<and>
        (l2, g2, Out a, f2, r2, l2') \<in> trans (N q) \<and>
        L!p = l1 \<and> L!q = l2 \<and> p < length L \<and> q < length L \<and> p \<noteq> q \<and>
        L' = L[p := l1', q := l2'] \<and> is_upd s f1 s' \<and> is_upd s' f2 s'' \<and> bounded bounds s''
        \<and> L \<in> states
      }
    "
        unfolding trans_bin_def by blast
      from True have **:
        "bin_trans_from (L, s)
      = concat (map (\<lambda>a. pairs_by_action L s (OUT ! a) (IN ! a)) [0..<num_actions])"
        unfolding bin_trans_from_def IN_def OUT_def by simp
      from \<open>dom s = _\<close> \<open>L \<in> _\<close> show ?thesis
        unfolding * **
        apply clarsimp
        unfolding pairs_by_action_def
        apply (clarsimp simp: set_map_filter Let_def)
        apply safe
        subgoal for _ s'' _ a' p q l1 g1 f1 r1 l1' l2 g2 f2 r2 l2'
          apply clarsimp
          apply (inst_existentials a')
          subgoal
            apply (frule IN_I)
              apply solve_triv+
             apply (drule action_setD; simp)
            apply (rule bexI[rotated], assumption)
            apply (frule (3) is_upd_dom2)
            apply (drule (3) is_updD)
            apply (drule (3) is_updD)
            unfolding check_bounded_iff
            apply intros
                    apply solve_triv+
                 apply (erule OUT_I)
                  apply solve_triv+
                 apply (drule action_setD; simp)
                apply solve_triv+
            done
          subgoal
            by (auto dest: action_setD)
          done
        subgoal
          apply mini_ex
          apply (drule IN_D, assumption)
          apply (drule OUT_D, assumption)
          apply elims
          apply intros
                       apply solve_triv+
            apply (rule is_upd_dom2 is_upd_make_updI2, (assumption+)?)+
          unfolding check_bounded_iff
          apply simp
          done
        done
    next
      case False
      with get_commited_empty_iff[of L] have "\<exists>p<n_ps. L ! p \<in> commited (N p)"
        by simp
      then have *: "((L, s), g, a, r, L', s') \<in> trans_bin \<longleftrightarrow> ((L, s), g, a, r, L', s') \<in>
      {((L, s), g1 @ g2, Bin a, r1 @ r2, (L', s'')) |
        L s L' s' s'' a p q l1 g1 f1 r1 l1' l2 g2 f2 r2 l2'.
        (l1, g1, In a,  f1, r1, l1') \<in> trans (N p) \<and>
        (l2, g2, Out a, f2, r2, l2') \<in> trans (N q) \<and>
        (l1 \<in> commited (N p) \<or> l2 \<in> commited (N q)) \<and>
        L!p = l1 \<and> L!q = l2 \<and> p < length L \<and> q < length L \<and> p \<noteq> q \<and>
        L' = L[p := l1', q := l2'] \<and> is_upd s f1 s' \<and> is_upd s' f2 s'' \<and> bounded bounds s''
        \<and> L \<in> states
      }"
        unfolding trans_bin_def by blast
      let ?S1 =
        "{((L, s), g1 @ g2, Bin a, r1 @ r2, (L', s'')) |
        L s L' s' s'' a p q l1 g1 f1 r1 l1' l2 g2 f2 r2 l2'.
          (l1, g1, In a,  f1, r1, l1') \<in> trans (N p) \<and>
          (l2, g2, Out a, f2, r2, l2') \<in> trans (N q) \<and>
          l1 \<in> commited (N p) \<and>
          L!p = l1 \<and> L!q = l2 \<and> p < length L \<and> q < length L \<and> p \<noteq> q \<and>
          L' = L[p := l1', q := l2'] \<and> is_upd s f1 s' \<and> is_upd s' f2 s'' \<and> bounded bounds s''
          \<and> L \<in> states
      }"
      let ?S2 =
        "{((L, s), g1 @ g2, Bin a, r1 @ r2, (L', s'')) |
        L s L' s' s'' a p q l1 g1 f1 r1 l1' l2 g2 f2 r2 l2'.
          (l1, g1, In a,  f1, r1, l1') \<in> trans (N p) \<and>
          (l2, g2, Out a, f2, r2, l2') \<in> trans (N q) \<and>
          l2 \<in> commited (N q) \<and>
          L!p = l1 \<and> L!q = l2 \<and>
          p < length L \<and> q < length L \<and> p \<noteq> q \<and>
          L' = L[p := l1', q := l2'] \<and>
          is_upd s f1 s' \<and> is_upd s' f2 s'' \<and> bounded bounds s''
          \<and> L \<in> states
      }"
      have *: "((L, s), g, a, r, L', s') \<in> trans_bin \<longleftrightarrow>
      ((L, s), g, a, r, L', s') \<in> ?S1 \<or> ((L, s), g, a, r, L', s') \<in> ?S2"
        unfolding * by clarsimp (rule iffI; elims add: disjE; intros add: disjI1 disjI2 HOL.refl)
      define pairs where "pairs = get_commited L"
      define In2 where "In2  = all_actions_from_vec trans_in_map pairs"
      define Out2 where "Out2 = all_actions_from_vec trans_out_map pairs"
      have In2_I:
        "(p, g, a', f, r, l') \<in> set (In2 ! a')"
        if "(L ! p, g, In a', f, r, l') \<in> Simple_Network_Language.trans (N p)"
          "p < n_ps" "a' < num_actions" "L ! p \<in> commited (N p)"
        for p g a' f r l'
      proof -
        from \<open>L ! p \<in> commited (N p)\<close> \<open>p < n_ps\<close> have "(p, L ! p) \<in> set pairs"
          unfolding pairs_def get_commited_mem_iff by blast
        from trans_mapI[OF that(1,2)] have "(g, In a', f, r, l') \<in> set (trans_map p (L ! p))"
          by auto
        then have "(g, a', f, r, l') \<in> set (trans_in_map p (L ! p))"
          unfolding trans_in_map_def set_map_filter by (auto 4 6)
        with \<open>p < _\<close> \<open>a' < _\<close> \<open>_ \<in> set pairs\<close> show ?thesis
          unfolding In2_def by (intro in_all_actions_from_vecI)
      qed
      have Out2_I:
        "(p, g, a', f, r, l') \<in> set (Out2 ! a')"
        if "(L ! p, g, Out a', f, r, l') \<in> Simple_Network_Language.trans (N p)"
          "p < n_ps" "a' < num_actions" "L ! p \<in> commited (N p)"
        for p g a' f r l'
      proof -
        from \<open>L ! p \<in> commited (N p)\<close> \<open>p < n_ps\<close> have "(p, L ! p) \<in> set pairs"
          unfolding pairs_def get_commited_mem_iff by blast
        from trans_mapI[OF that(1,2)] have "(g, Out a', f, r, l') \<in> set (trans_map p (L ! p))"
          by auto
        then have "(g, a', f, r, l') \<in> set (trans_out_map p (L ! p))"
          unfolding trans_out_map_def set_map_filter by (auto 4 6)
        with \<open>p < _\<close> \<open>a' < _\<close> \<open>_ \<in> set pairs\<close> show ?thesis
          unfolding Out2_def by (intro in_all_actions_from_vecI)
      qed
      have "distinct (map fst pairs)"
        unfolding pairs_def get_commited_def distinct_map inj_on_def Let_def
        by (auto simp: set_map_filter intro!: distinct_map_filterI split: if_split_asm)
      have in_pairsD: "p < n_ps" "l = L ! p" "L ! p \<in> commited (N p)"
        if "(p, l) \<in> set pairs" for p l
        using that using get_commited_mem_iff pairs_def by auto
      have In2_D:
        "(L ! p, g, In a', f, r, l') \<in> Simple_Network_Language.trans (N p) \<and>
      p < n_ps \<and> a' = a1 \<and> L ! p \<in> commited (N p)"
        if "(p, g, a', f, r, l') \<in> set (In2 ! a1)" "a1 < num_actions"
        for p g a' f r l' a1
        using that
        unfolding In2_def
        apply -
        apply (drule all_actions_from_vecD)
          apply assumption
         apply (rule \<open>distinct _\<close>)
        unfolding trans_in_map_def set_map_filter
        apply (auto split: option.split_asm)
          apply (auto dest: in_pairsD trans_mapD split: act.split_asm)
        done
      have Out2_D:
        "(L ! p, g, Out a', f, r, l') \<in> Simple_Network_Language.trans (N p)
      \<and> p < n_ps \<and> a' = a1 \<and> L ! p \<in> commited (N p)"
        if "(p, g, a', f, r, l') \<in> set (Out2 ! a1)" "a1 < num_actions"
        for p g a' f r l' a1
        using that
        unfolding Out2_def
        apply -
        apply (drule all_actions_from_vecD)
          apply assumption
         apply (rule \<open>distinct _\<close>)
        unfolding trans_out_map_def set_map_filter
        apply (auto split: option.split_asm)
          apply (auto dest: in_pairsD trans_mapD split: act.split_asm)
        done
      from False have **: "bin_trans_from (L, s) =
        concat (map (\<lambda>a. pairs_by_action L s (OUT ! a) (In2 ! a)) [0..<num_actions])
      @ concat (map (\<lambda>a. pairs_by_action L s (Out2 ! a) (IN ! a)) [0..<num_actions])"
        unfolding bin_trans_from_def IN_def OUT_def In2_def Out2_def pairs_def
        by (simp add: Let_def)
      from \<open>dom s = _\<close> \<open>L \<in> _\<close> have "
      ((L, s), g, a, r, L', s') \<in> ?S1 \<longleftrightarrow> (g, a, r, L', s') \<in>
      set (concat (map (\<lambda>a. pairs_by_action L s (OUT ! a) (In2 ! a)) [0..<num_actions]))"
        apply clarsimp
        unfolding pairs_by_action_def
        apply (clarsimp simp: set_map_filter Let_def)
        apply safe
        subgoal for _ s'' _ a' p q l1 g1 f1 r1 l1' l2 g2 f2 r2 l2'
          apply clarsimp
          apply (inst_existentials a')
          subgoal
            apply (frule In2_I)
               apply solve_triv+
              apply (drule action_setD; simp)
             apply assumption
            apply (rule bexI[rotated], assumption)
            apply (frule (3) is_upd_dom2)
            apply (drule (3) is_updD)
            apply (drule (3) is_updD)
            unfolding check_bounded_iff
            apply intros
                    apply solve_triv+
                 apply (erule OUT_I)
                  apply solve_triv+
                 apply (drule action_setD; simp)
                apply solve_triv+
            done
          subgoal
            by (auto dest: action_setD)
          done
        subgoal
          apply mini_ex
          apply (drule In2_D, assumption)
          apply (drule OUT_D, assumption)
          apply elims
          apply intros
                        apply solve_triv+
            apply (rule is_upd_dom2 is_upd_make_updI2, (assumption+)?)+
          unfolding check_bounded_iff
          apply simp
          done
        done
      moreover from \<open>dom s = _\<close> \<open>L \<in> _\<close> have "
      ((L, s), g, a, r, L', s') \<in> ?S2 \<longleftrightarrow> (g, a, r, L', s')
      \<in> set (concat (map (\<lambda>a. pairs_by_action L s (Out2 ! a) (IN ! a)) [0..<num_actions]))"
        apply clarsimp
        unfolding pairs_by_action_def
        apply (clarsimp simp: set_map_filter Let_def)
        apply safe
        subgoal for _ s'' _ a' p q l1 g1 f1 r1 l1' l2 g2 f2 r2 l2'
          apply clarsimp
          apply (inst_existentials a')
          subgoal
            apply (frule action_setD; simp)
            apply (frule IN_I)
              apply solve_triv+
            apply (frule Out2_I)
               apply solve_triv+
            apply (rule bexI[rotated], assumption)
            apply (frule (3) is_upd_dom2)
            apply (drule (3) is_updD)
            apply (drule (3) is_updD)
            unfolding check_bounded_iff
            apply intros
                    apply solve_triv+
            done
          subgoal
            by (auto dest: action_setD)
          done
        subgoal
          apply mini_ex
          apply (drule Out2_D, assumption)
          apply (drule IN_D, assumption)
          apply elims
          apply intros
                        apply solve_triv+
            apply (rule is_upd_dom2 is_upd_make_updI2, (assumption+)?)+
          unfolding check_bounded_iff
          apply simp
          done
        done
      ultimately show ?thesis
        unfolding * ** by simp
    qed
  qed
  done

lemma get_commited_distinct: "distinct (get_commited L)"
  unfolding get_commited_def by (rule distinct_map_filterI) (auto simp: Let_def)

lemma make_combs_alt_def:
  "make_combs p a xs \<equiv>
    let
      ys = 
        map (\<lambda> i. map (\<lambda>t. (i, t)) (xs ! i ! a))
        (filter
          (\<lambda>i. xs ! i ! a \<noteq> [] \<and> i \<noteq> p)
          [0..<n_ps])
    in if ys = [] then [] else product_lists ys"
  apply (rule eq_reflection)
  unfolding make_combs_def
  apply (simp add: map_filter_def comp_def if_distrib[where f = the])
  apply intros
  apply (fo_rule arg_cong)
  apply auto
  done

lemma broad_trans_from_correct:
  "(broad_trans_from, trans_broad) \<in> transition_rel states'"
  unfolding transition_rel_def
  apply clarsimp
  subgoal for L s g a r L' s'
  proof -
    assume "(L, s) \<in> states'"
    then have "L \<in> states" "dom s = {0..<n_vs}"
      by auto
    then have [simp]: "length L = n_ps"
      by auto
    define IN  where "IN  = map (\<lambda>p. trans_in_broad_grouped p (L ! p)) [0..<n_ps]"
    define OUT where "OUT = map (\<lambda>p. trans_out_broad_grouped p (L ! p)) [0..<n_ps]"
    have IN_I:
      "(g, a', f, r, l') \<in> set (IN ! p ! a')"
      if "(L ! p, g, In a', f, r, l') \<in> Simple_Network_Language.trans (N p)"
        "p < n_ps" "a' < num_actions" "a' \<in> set broadcast"
      for p g a' f r l'
    proof -
      from trans_mapI[OF that(1,2)] \<open>a' \<in> _\<close> have
        "(g, a', f, r, l') \<in> set (trans_in_broad_map p (L ! p))"
        unfolding trans_in_broad_map_def set_map_filter by (auto 4 6)
      with \<open>a' < _\<close> have "(g, a', f, r, l') \<in> set (trans_in_broad_grouped p (L ! p) ! a')"
        unfolding trans_in_broad_grouped_def by (auto dest: in_actions_by_state'I)
      with \<open>p < _\<close> show ?thesis
        unfolding IN_def by auto
    qed
    have OUT_I:
      "(g, a', f, r, l') \<in> set (OUT ! p ! a')"
      if "(L ! p, g, Out a', f, r, l') \<in> Simple_Network_Language.trans (N p)"
        "p < n_ps" "a' < num_actions" "a' \<in> set broadcast"
      for p g a' f r l'
    proof -
      from trans_mapI[OF that(1,2)] \<open>a' \<in> _\<close> have
        "(g, a', f, r, l') \<in> set (trans_out_broad_map p (L ! p))"
        unfolding trans_out_broad_map_def set_map_filter by (auto 4 6)
      with \<open>a' < _\<close> have "(g, a', f, r, l') \<in> set (trans_out_broad_grouped p (L ! p) ! a')"
        unfolding trans_out_broad_grouped_def by (auto dest: in_actions_by_state'I)
      with \<open>p < _\<close> show ?thesis
        unfolding OUT_def by auto
    qed
    have IN_D:
      "(L ! p, g, In a', f, r, l') \<in> Simple_Network_Language.trans (N p)
     \<and> a' = a1 \<and> a1 \<in> set broadcast"
      if "(g, a', f, r, l') \<in> set (IN ! p ! a1)" "a1 < num_actions" "p < n_ps"
      for p g a' f r l' a1
      using that unfolding IN_def trans_in_broad_grouped_def
      apply simp
      apply (drule in_actions_by_state'D)
      unfolding trans_in_broad_map_def set_map_filter
      by (auto split: option.split_asm) (auto split: act.split_asm if_split_asm dest: trans_mapD)
    have OUT_D:
      "(L ! p, g, Out a', f, r, l') \<in> Simple_Network_Language.trans (N p)
     \<and> a' = a1 \<and> a1 \<in> set broadcast"
      if "(g, a', f, r, l') \<in> set (OUT ! p ! a1)" "a1 < num_actions" "p < n_ps"
      for p g a' f r l' a1
      using that unfolding OUT_def trans_out_broad_grouped_def
      apply simp
      apply (drule in_actions_by_state'D)
      unfolding trans_out_broad_map_def set_map_filter
      by (auto split: option.split_asm) (auto split: act.split_asm if_split_asm dest: trans_mapD)
    define make_trans where "make_trans a p \<equiv>
      let
        outs = OUT ! p ! a
      in if outs = [] then []
      else
        let
          combs = make_combs p a IN;
          outs = map (\<lambda>t. (p, t)) outs;
          combs = concat (map (\<lambda>x. map (\<lambda> xs. x # xs) combs) outs);
          init = ([], Broad a, [], (L, s))
        in
        filter (\<lambda> (g, a, r, L, s). check_bounded s) (
          map (\<lambda>comb.
              fold
                (\<lambda>(q, g2, a2, f2, r2, l2) (g1, a, r1, (L, s)).
                  (g1 @ g2, a, r1 @ r2, (L[q := l2], mk_upds s f2))
                )
                comb
                init
          ) combs)" for a p
    have make_combsD:
      "map (\<lambda>p. (p, gs p, a', fs p, rs p, ls' p)) ps \<in> set (make_combs p a' IN)"
      if
        "\<forall>p\<in>set ps.
          (L ! p, gs p, In a', fs p, rs p, ls' p) \<in> Simple_Network_Language.trans (N p)"
        "\<forall>q<n_ps. q \<notin> set ps \<and> p \<noteq> q \<longrightarrow>
          (\<forall>g f r l'. (L ! q, g, In a', f, r, l') \<notin> Simple_Network_Language.trans (N q))"
        "p < n_ps" "set ps \<subseteq> {0..<n_ps}" "p \<notin> set ps" "distinct ps" "sorted ps" "ps \<noteq> []"
        "a' < num_actions" "a' \<in> set broadcast"
      for p ps gs a' fs rs ls'
    proof -
      define ys where "ys = List.map_filter
        (\<lambda> i.
          if i = p then None
          else if IN ! i ! a' = [] then None
          else Some (map (\<lambda>t. (i, t)) (IN ! i ! a'))
        )
        [0..<n_ps]"
      have "filter (\<lambda>i. IN ! i ! a' \<noteq> [] \<and> i \<noteq> p) [0..<n_ps] = ps"
        apply (rule filter_distinct_eqI)
        subgoal
          using that(4-) by (simp add: sorted_distinct_subseq_iff)
        subgoal
          using that(1,3-) by (auto 4 3 dest!: IN_I)
        subgoal
          using that(1,2,4,9-)
          apply -
          apply (rule ccontr)
          apply simp
          apply elims
          apply (drule hd_in_set)
          subgoal for x
            by (cases "hd (IN ! x ! a')") (auto 4 4 dest!: IN_D)
          done
        by auto
      then have "length ys = length ps"
        unfolding ys_def map_filter_def by simp
      from \<open>_ = ps\<close> \<open>ps \<noteq> []\<close> have "ys \<noteq> []"
        unfolding ys_def map_filter_def by simp
      from that(1,3-) have
        "\<forall>i<length ps. let p = ps ! i in (p, gs p, a', fs p, rs p, ls' p) \<in> set (ys ! i)"
        unfolding ys_def Let_def map_filter_def
        apply (simp add: comp_def if_distrib[where f = the])
        apply (subst (2) map_cong)
          apply (rule HOL.refl)
         apply (simp; fail)
        apply (simp add: \<open>_ = ps\<close>)
        by (intros add: image_eqI[OF HOL.refl] IN_I; simp add: subset_code(1))
      with \<open>ys \<noteq> []\<close> show ?thesis
        unfolding make_combs_def ys_def[symmetric] Let_def
        by (auto simp: \<open>length ys = _\<close> product_lists_set intro:list_all2_all_nthI)
    qed
    have make_combsI:
      "\<exists> ps gs fs rs ls'.
      (\<forall>p\<in>set ps.
       (L ! p, gs p, In a', fs p, rs p, ls' p) \<in> Simple_Network_Language.trans (N p)) \<and>
      (\<forall>q<n_ps. q \<notin> set ps \<and> p \<noteq> q \<longrightarrow>
       (\<forall>g f r l'. (L ! q, g, In a', f, r, l') \<notin> Simple_Network_Language.trans (N q))) \<and>
      set ps \<subseteq> {0..<n_ps} \<and> p \<notin> set ps \<and> distinct ps \<and> sorted ps \<and> ps \<noteq> [] \<and> a' \<in> set broadcast
      \<and> xs = map (\<lambda> p. (p, gs p, a', fs p, rs p, ls' p)) ps
      \<and> filter (\<lambda>i. IN ! i ! a' \<noteq> [] \<and> i \<noteq> p) [0..<n_ps] = ps"
      if "xs \<in> set (make_combs p a' IN)" "p < n_ps" "a' < num_actions"
      for xs p a'
    proof -
      define ps gs fs rs ls' where defs:
        "ps  = map fst xs"
        "gs  = (\<lambda>i. case the (map_of xs i) of (g, a, f, r, l') \<Rightarrow> g)"
        "fs  = (\<lambda>i. case the (map_of xs i) of (g, a, f, r, l') \<Rightarrow> f)"
        "rs  = (\<lambda>i. case the (map_of xs i) of (g, a, f, r, l') \<Rightarrow> r)"
        "ls' = (\<lambda>i. case the (map_of xs i) of (g, a, f, r, l') \<Rightarrow> l')"
      have "filter (\<lambda>i. IN ! i ! a' \<noteq> [] \<and> i \<noteq> p) [0..<n_ps] = ps"
        apply (rule filter_distinct_eqI)
        subgoal
          using that
          unfolding defs make_combs_alt_def Let_def
          by (auto simp: set_map_filter product_lists_set list_all2_map2 list.rel_eq
              dest: list_all2_map_fst_aux split: if_split_asm)
        subgoal
          using that unfolding defs make_combs_alt_def Let_def
          by (auto simp: set_map_filter product_lists_set dest!: list_all2_set1 split: if_split_asm)
        subgoal
          using that
          unfolding defs make_combs_alt_def Let_def
          by (auto
              simp: set_map_filter product_lists_set list_all2_map2 list.rel_eq
              dest!: map_eq_imageD list_all2_map_fst_aux split: if_split_asm)
        subgoal
          by simp
        done
      then have "set ps \<subseteq> {0..<n_ps}" "p \<notin> set ps" "distinct ps" "sorted ps"
        by (auto intro: sorted_filter')
      have to_map: "a' = a" "the (map_of xs q) = (g, a, r, f, l')"
        if "(q, g, a, r, f, l') \<in> set xs" for q g a r f l'
        using that
         apply -
        subgoal
          using \<open>set ps \<subseteq> _\<close> \<open>a' < _\<close> \<open>xs \<in> _\<close>
          by
            (simp 
              add: make_combs_alt_def product_lists_set \<open>_ = ps\<close> list_all2_map2
              split: if_split_asm
              ) (auto 4 3 dest!: IN_D list_all2_set1)
        subgoal
          using \<open>distinct ps\<close>
          by (subst (asm) map_of_eq_Some_iff[of xs q, symmetric]) (auto simp: defs)
        done
      from that have "\<forall>p\<in>set ps.
       (L ! p, gs p, In a', fs p, rs p, ls' p) \<in> Simple_Network_Language.trans (N p)"
        unfolding make_combs_alt_def \<open>_ = ps\<close>
        apply (auto simp: set_map_filter product_lists_set split: if_split_asm)
        using \<open>set ps \<subseteq> _\<close> unfolding defs
        by (auto simp: comp_def list_all2_map2 list_all2_same to_map
                 elim!: IN_D[THEN conjunct1, rotated]
           )
      from that have "ps \<noteq> []" "a' \<in> set broadcast"
        apply (auto simp: make_combs_alt_def set_map_filter product_lists_set split: if_split_asm)
        using \<open>_ = ps\<close> \<open>set ps \<subseteq> {0..<n_ps}\<close> by (cases xs; auto dest: IN_D simp: list_all2_Cons1)+
      with that have "\<forall>q<n_ps. q \<notin> set ps \<and> p \<noteq> q \<longrightarrow>
       (\<forall>g f r l'. (L ! q, g, In a', f, r, l') \<notin> Simple_Network_Language.trans (N q))"
        unfolding make_combs_alt_def
        by (auto 4 3 dest!: list_all2_set2 IN_I
            simp: defs set_map_filter product_lists_set split: if_split_asm)
      have "xs = map (\<lambda> p. (p, gs p, a', fs p, rs p, ls' p)) ps"
        apply (intro nth_equalityI)
         apply (simp add: defs; fail)
        apply intros
        subgoal for i
          by (cases "xs ! i") (auto 4 4 simp: defs dest: to_map nth_mem)
        done
      show ?thesis
        by (inst_existentials ps gs fs rs ls'; fact)
    qed
    let ?f = "\<lambda>(q, g2, a2, f2, r2, l2) (g1, a, r1, L, s).
                  (g1 @ g2, a, r1 @ r2, L[q := l2], mk_upds s f2)"
    have ***: "
    fold ?f (map (\<lambda>p. (p, gs p, a', fs p, rs p, ls' p)) ps) (g, a, r, L, s)
    = (g @ concat (map gs ps), a, r @ concat (map rs ps),
        fold (\<lambda>p L. L[p := ls' p]) ps L, fold (\<lambda>p s. mk_upds s (fs p)) ps s)
    " for ps gs a' fs rs ls' g a r L s
      by (induction ps arbitrary: g a r L s; simp)
    have upd_swap:
      "fold (\<lambda>p L . L[p := ls' p]) ps L[p := l'] = fold (\<lambda>p L . L[p := ls' p]) ps (L[p := l'])"
      if "p \<notin> set ps" for ps ls' p l'
      using that by (induction ps arbitrary: L) (auto simp: list_update_swap)
    have make_transI:
      "a' < num_actions \<and> p < n_ps \<and>
       (g1 @ concat (map gs ps), Broad a', r1 @ concat (map rs ps),
        fold (\<lambda>p L. L[p := ls' p]) ps L[p := l'], s') \<in> set (make_trans a' p)"
      if 
        "dom s = {0..<n_vs}" and
        "L \<in> states" and
        "g = g1 @ concat (map gs ps)" and
        "a = Broad a'" and
        "r = r1 @ concat (map rs ps)" and
        "L' = fold (\<lambda>p L. L[p := ls' p]) ps L[p := l']" and
        "a' \<in> set broadcast" and
        "(L ! p, g1, Out a', f1, r1, l') \<in> Simple_Network_Language.trans (N p)" and
        "\<forall>p\<in>set ps. (L ! p, gs p, In a', fs p, rs p, ls' p) \<in> Simple_Network_Language.trans (N p)"
        and
        "\<forall>q<n_ps. q \<notin> set ps \<and> p \<noteq> q
        \<longrightarrow> (\<forall>g f r l'. (L ! q, g, In a', f, r, l') \<notin> Simple_Network_Language.trans (N q))" and
        "p < n_ps" and
        "set ps \<subseteq> {0..<n_ps}" and
        "p \<notin> set ps" and
        "distinct ps" and
        "sorted ps" and
        "ps \<noteq> []" and
        "is_upd s f1 s''" and
        "is_upds s'' (map fs ps) s'" and
        "Simple_Network_Language.bounded bounds s'"
      for a' p g1 gs ps r1 rs ls' l' f1 s'' fs
      using that
      unfolding make_trans_def
      apply (clarsimp simp: set_map_filter Let_def split: prod.split)
      apply (frule action_setD; simp)
      apply (frule OUT_I)
         apply solve_triv+
      apply (frule make_combsD, assumption+)
      apply (inst_existentials p)
        apply (auto; fail)
       apply (rule image_eqI[rotated])
        apply (solve_triv | rule UN_I image_eqI[rotated])+
       apply (simp add: ***)
       apply intros
      subgoal
        by (simp add: upd_swap)
       apply (rule is_updsD)
      subgoal
        using is_upd_dom2 is_updD by auto
         apply assumption+
      subgoal
        by (drule is_updD; solve_triv)
      subgoal
        unfolding check_bounded_iff .
      done
    have make_transD:
      "\<exists>s'' ga f ra l' gs fs rs ls' ps.
         g = ga @ concat (map gs ps) \<and>
         a = Broad a' \<and>
         r = ra @ concat (map rs ps) \<and>
         L' = fold (\<lambda>p L. L[p := ls' p]) ps L[p := l'] \<and>
         a' \<in> set broadcast \<and>
         (L ! p, ga, Out a', f, ra, l') \<in> Simple_Network_Language.trans (N p) \<and>
         (\<forall>p\<in>set ps. (L ! p, gs p, In a', fs p, rs p, ls' p) \<in> Simple_Network_Language.trans (N p)) \<and>
         (\<forall>q<n_ps.
             q \<notin> set ps \<and> p \<noteq> q \<longrightarrow>
             (\<forall>g f r l'. (L ! q, g, In a', f, r, l') \<notin> Simple_Network_Language.trans (N q))) \<and>
         p < n_ps \<and>
         set ps \<subseteq> {0..<n_ps} \<and>
         p \<notin> set ps \<and>
         distinct ps \<and>
         sorted ps \<and>
         ps \<noteq> [] \<and> is_upd s f s'' \<and> is_upds s'' (map fs ps) s' \<and>
         Simple_Network_Language.bounded bounds s' \<and>
         filter (\<lambda>i. IN ! i ! a' \<noteq> [] \<and> i \<noteq> p) [0..<n_ps] = ps"
      if
        "dom s = {0..<n_vs}" and
        "L \<in> states" and
        "a' < num_actions" and
        "p < n_ps" and
        "(g, a, r, L', s') \<in> set (make_trans a' p)"
      for a' p
      using that
      unfolding make_trans_def
      apply mini_ex
      apply (clarsimp simp: set_map_filter Let_def split: prod.split if_split_asm)
      subgoal for g1 a1 r1 f1 l1' xs
        apply (drule make_combsI, assumption+)
        apply elims
        apply (drule OUT_D, assumption+)
        apply elims
        apply (simp add: ***)
        apply intros
                      apply solve_triv+
                    apply (rule upd_swap[symmetric])
                    apply solve_triv+
                  apply (erule bspec; assumption)
                 apply (elims add: allE; intros?; assumption)
                apply solve_triv+
           apply (rule is_upd_make_updI2)
             apply solve_triv+
        subgoal for ps gs fs rs ls'
          apply (rule is_upds_make_updsI2[where upds = "map fs ps", simplified fold_map comp_def])
          subgoal
            apply simp
            apply intros
            prefer 2
             apply (erule bspec, assumption)
            apply (drule subsetD, assumption)
            apply (clarsimp; fail)
            done
          subgoal
            by (rule is_upd_dom2 is_upd_make_updI2)+
          done
        unfolding check_bounded_iff
         apply solve_triv+
        done
      done
    have make_trans_iff: "
      (\<exists>s'' aa p ga f ra l' gs fs rs ls' ps.
          g = ga @ concat (map gs ps) \<and>
          a = Broad aa \<and>
          r = ra @ concat (map rs ps) \<and>
          L' = fold (\<lambda>p L. L[p := ls' p]) ps L[p := l'] \<and>
          aa \<in> set broadcast \<and>
          (L ! p, ga, Out aa, f, ra, l') \<in> Simple_Network_Language.trans (N p) \<and>
          (\<forall>p\<in>set ps.
              (L ! p, gs p, In aa, fs p, rs p, ls' p)
              \<in> Simple_Network_Language.trans (N p)) \<and>
          (\<forall>q<n_ps.
              q \<notin> set ps \<and> p \<noteq> q \<longrightarrow>
              (\<forall>g f r l'.
                  (L ! q, g, In aa, f, r, l')
                  \<notin> Simple_Network_Language.trans (N q))) \<and>
          p < n_ps \<and>
          set ps \<subseteq> {0..<n_ps} \<and>
          p \<notin> set ps \<and>
          distinct ps \<and>
          sorted ps \<and>
          ps \<noteq> [] \<and>
          is_upd s f s'' \<and>
          is_upds s'' (map fs ps) s' \<and> Simple_Network_Language.bounded bounds s') =
      (\<exists>a'\<in>{0..<num_actions}.
          \<exists>p\<in>{0..<n_ps}. (g, a, r, L', s') \<in> set (make_trans a' p))" (is "?l \<longleftrightarrow> ?r")
      if "dom s = {0..<n_vs}" "L \<in> states"
    proof (intro iffI)
      assume ?l
      with that show ?r
        by elims (drule make_transI; (elims; intros)?; solve_triv)
    next
      assume ?r
      with that show ?l
        apply elims
        subgoal for a' p
          apply simp
          apply (drule make_transD)
              apply assumption+
          apply elims
          apply intros
                          apply assumption+
                    apply (erule bspec; assumption) (* or blast *)
                   apply (elims add: allE; intros?; assumption) (* or blast *)
                  apply assumption+
          done
        done
    qed
    show "(((L, s), g, a, r, L', s') \<in> trans_broad) =
        ((g, a, r, L', s') \<in> set (broad_trans_from (L, s)))"
    proof (cases "get_commited L = []")
      case True
      with get_commited_empty_iff[of L] have "\<forall>p<n_ps. L ! p \<notin> commited (N p)"
        by simp
      then have *: "((L, s), g, a, r, L', s') \<in> trans_broad \<longleftrightarrow> ((L, s), g, a, r, L', s') \<in>
      {((L, s), g @ concat (map gs ps), Broad a, r @ concat (map rs ps), (L', s'')) |
        L s L' s' s'' a p l g f r l' gs fs rs ls' ps.
        a \<in> set broadcast \<and>
        (l, g, Out a, f, r, l') \<in> trans (N p) \<and>
        (\<forall>p \<in> set ps. (L ! p, gs p, In a, fs p, rs p, ls' p) \<in> trans (N p)) \<and>
        (\<forall>q < n_ps. q \<notin> set ps \<and> p \<noteq> q \<longrightarrow>
          \<not> (\<exists>g f r l'. (L ! q, g, In a, f, r, l') \<in> trans (N q))) \<and>
        L!p = l \<and>
        p < length L \<and> set ps \<subseteq> {0..<n_ps} \<and> p \<notin> set ps \<and> distinct ps \<and> sorted ps \<and> ps \<noteq> [] \<and>
        L' = fold (\<lambda>p L . L[p := ls' p]) ps L[p := l'] \<and>
        is_upd s f s' \<and> is_upds s' (map fs ps) s'' \<and>
        bounded bounds s'' \<and> L \<in> states
      }
    "
        unfolding trans_broad_def broadcast_def[simplified] by blast
      from True have **:
        "broad_trans_from (L, s)
      =  concat (
           map (\<lambda>a.
             concat (map (\<lambda>p. make_trans a p) [0..<n_ps])
           )
           [0..<num_actions]
         )"
        unfolding broad_trans_from_alt_def IN_def OUT_def make_trans_def by simp
      from \<open>dom s = _\<close> \<open>L \<in> _\<close> show ?thesis
        unfolding * ** by (simp add: make_trans_iff)
    next
      case False
      with get_commited_empty_iff[of L] have "\<not> (\<forall>p<n_ps. L ! p \<notin> commited (N p))"
        by simp
      then have *: "((L, s), g, a, r, L', s') \<in> trans_broad \<longleftrightarrow> ((L, s), g, a, r, L', s') \<in>
      {((L, s), g @ concat (map gs ps), Broad a, r @ concat (map rs ps), (L', s'')) |
        L s L' s' s'' a p l g f r l' gs fs rs ls' ps.
        a \<in> set broadcast \<and>
        (l, g, Out a, f, r, l') \<in> trans (N p) \<and>
        (\<forall>p \<in> set ps. (L ! p, gs p, In a, fs p, rs p, ls' p) \<in> trans (N p)) \<and>
        (l \<in> commited (N p) \<or> (\<exists>p \<in> set ps. L ! p \<in> commited (N p))) \<and>
        (\<forall>q < n_ps. q \<notin> set ps \<and> p \<noteq> q \<longrightarrow>
          \<not> (\<exists>g f r l'. (L ! q, g, In a, f, r, l') \<in> trans (N q))) \<and>
        L!p = l \<and>
        p < length L \<and> set ps \<subseteq> {0..<n_ps} \<and> p \<notin> set ps \<and> distinct ps \<and> sorted ps \<and> ps \<noteq> [] \<and>
        L' = fold (\<lambda>p L . L[p := ls' p]) ps L[p := l'] \<and> is_upd s f s' \<and> is_upds s' (map fs ps) s'' \<and>
        bounded bounds s'' \<and> L \<in> states
      }"
        unfolding trans_broad_def broadcast_def[simplified] by blast
      have commited_iff: "
      List.map_filter (\<lambda>(p, _). if IN ! p ! a' = [] then None else Some p) (get_commited L) \<noteq> [p] \<and>
      List.map_filter (\<lambda>(p, _). if IN ! p ! a' = [] then None else Some p) (get_commited L) \<noteq> []
    \<longleftrightarrow> (\<exists>q<n_ps. IN ! q ! a' \<noteq> [] \<and> q \<noteq> p \<and> L ! q \<in> commited (N q))"
        for p a'
      proof -
        have *: "xs \<noteq> [p] \<and> xs \<noteq> [] \<longleftrightarrow> (\<exists>x \<in> set xs. x \<noteq> p)" if "distinct xs" for xs
          using that by auto (metis distinct.simps(2) distinct_length_2_or_more revg.elims)
        show ?thesis
          by (subst *)
            (auto
              intro: distinct_map_filterI get_commited_distinct
              simp: set_map_filter get_commited_mem_iff split: if_split_asm
              )
      qed
      from False have **:
        "broad_trans_from (L, s)
      = concat (
        map (\<lambda>a.
          let
            ins_commited =
              List.map_filter (\<lambda>(p, _). if IN ! p ! a \<noteq> [] then Some p else None) (get_commited L)
          in
          concat (map (\<lambda>p.
            if
              (ins_commited = [p] \<or> ins_commited = [])
              \<and> \<not> list_ex (\<lambda> (q, _). q = p) (get_commited L)
            then []
            else
              make_trans a p
          )
          [0..<n_ps])
        )
      [0..<num_actions])
      "
        unfolding broad_trans_from_alt_def IN_def OUT_def make_trans_def
        unfolding Let_def if_contract
        apply simp
        apply (fo_rule if_cong arg_cong2[where f = map] arg_cong[where f = concat] | rule ext)+
            apply blast+
        done
      from \<open>dom s = _\<close> \<open>L \<in> _\<close> show ?thesis
        unfolding * **
        apply (simp add: make_trans_iff)
        apply (intro iffI; elims)
        subgoal for s'a aa p ga f ra l' gs fs rs ls' ps \<comment> \<open>?l \<open>\<longrightarrow>\<close> ?r\<close>
          apply (frule make_transI)
                            apply assumption+
          apply elims
          apply intros
           apply (simp; fail)
          apply (simp add: Let_def)
          apply (erule disjE)
          subgoal \<comment> \<open>The process with the outgoing action label is commited\<close>
            using get_commited_mem_iff[of p "L ! p" L, simplified, symmetric]
            by (inst_existentials p) (auto simp add: list_ex_iff)
          apply (erule bexE)
          subgoal for q \<comment> \<open>One of the processes with an ingoing action label is commited\<close>
            apply (inst_existentials p)
             apply assumption
            apply (rule IntI)
             apply (simp; fail)
            apply simp
            unfolding commited_iff
            apply (rule disjI1; inst_existentials q; force dest!: IN_I)
            done
          done
        subgoal for a' \<comment> \<open>?r \<open>\<longrightarrow>\<close> ?l\<close>
          apply (clarsimp split: if_split_asm simp: Let_def)
          apply (drule make_transD[rotated 4])
              apply assumption+
          apply elims
          apply intros
                           apply assumption+
                     apply (erule bspec; assumption)
          subgoal for p s'' g' f r' l' gs fs rs ls' ps
            unfolding commited_iff by (auto simp: get_commited_mem_iff list_ex_iff)
                   apply (elims add: allE; intros?; assumption) (* or blast *)
                  apply assumption+
          done
        done
    qed
  qed
  done

end (* Simple Network Impl *)

end
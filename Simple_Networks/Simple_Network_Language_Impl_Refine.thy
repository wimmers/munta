theory Simple_Network_Language_Impl_Refine
  imports Simple_Network_Language_Impl
begin

paragraph \<open>Notation\<close>

no_notation Ref.update ("_ := _" 62)
no_notation Stream.snth (infixl "!!" 100)
no_notation Bits.bits_class.test_bit (infixl "!!" 100)

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
  by (smt
      case_prodE case_prodE' case_prod_conv is_val_determ
      list.rel_eq list_all2_swap list_all2_trans)

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
  "dom s' = dom s" if "is_upds s upds s'" "\<forall>upd \<in> set upds. \<forall> (x, e) \<in> set upd. x \<in> dom s"
  using that by (induction upds arbitrary: s) (erule is_upds.cases; auto simp: is_upd_dom)+

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
  "is_upds s upds (fold (\<lambda>upd s. mk_upds s upd) upds s)"
  if "\<forall>upd \<in> set upds. \<forall> (_, e) \<in> set upd. \<forall>x \<in> vars_of_exp e. x \<in> dom s"
    "\<forall>upd \<in> set upds. \<forall> (x, e) \<in> set upd. x \<in> dom s"
  using that
proof (induction upds arbitrary: s)
  case Nil
  then show ?case
    by (auto intro: is_upds.intros)
next
  case (Cons a upds)
  show ?case
    apply (rule is_upds.intros)
     apply (rule is_upd_make_updI)
    subgoal
      using Cons.prems by auto
    apply simp
    apply (rule Cons.IH)
    subgoal
      using Cons.prems by intros (subst is_upd_dom, auto 4 4 intro: is_upd_make_updI)
    subgoal
      using Cons.prems by intros (subst is_upd_dom, auto 4 4 intro: is_upd_make_updI)
    done
qed


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

context Simple_Network_Impl_nat
begin

paragraph \<open>Fundamentals\<close>

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

lemma action_setD:
  \<open>pred_act (\<lambda>a'. a' < num_actions) a\<close>
  if \<open>(l, g, a, f, r, l') \<in> Simple_Network_Language.trans (N p)\<close> \<open>p < n_ps\<close>
  using that action_set
  by (cases "automata ! p")
    (subst (asm) mem_trans_N_iff; force dest!: nth_mem simp flip: length_automata_eq_n_ps)

paragraph \<open>More precise state sets\<close>

definition
  "states' \<equiv> {(L, s). L \<in> states \<and> dom s = {0..<n_vs} \<and> bounded bounds s}"

lemma states'_states[intro, dest]:
  "L \<in> states" if "(L, s) \<in> states'"
  using that unfolding states'_def by auto

lemma states'_dom[intro, dest]:
  "dom s = {0..<n_vs}" if "(L, s) \<in> states'"
  using that unfolding states'_def by auto

lemma states'_bounded[intro, dest]:
  "bounded bounds s" if "(L, s) \<in> states'"
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
  "bounds_map \<equiv> the o map_of bounds'"

definition
  "check_bounded s =
    (\<forall>x \<in> dom s. fst (bounds_map x) < the (s x) \<and> the (s x) < snd (bounds_map x))"

text \<open>Compute pairs of processes with committed initial locations from location vector.\<close>
definition
  "get_commited L =
    List.map_filter (\<lambda>p.
    let l = L ! p in
    if l \<in> set (fst (automata ! p)) then Some (p, l) else None) [0..<n_ps]"

text \<open>Given a process and a location, return the corresponding transitions.\<close>
definition
  "trans_map \<equiv>
  let f = (\<lambda>i.
    let m = union_map_of (fst (snd (automata ! i))) in (\<lambda>j.
      case m j of None \<Rightarrow> [] | Some xs \<Rightarrow> xs))
  in f"

text \<open>Filter for internal transitions.\<close>
definition
  "trans_i_map i j \<equiv>
    List.map_filter
      (\<lambda> (g, a, m, l'). case a of Sil a \<Rightarrow> Some (g, a, m, l') | _ \<Rightarrow> None)
    (trans_map i j)"

text \<open>Compute valid internal successors given:
  \<^item> a process \<open>p\<close>,
  \<^item> initial location \<open>l\<close>,
  \<^item> location vector \<open>L\<close>,
  \<^item> and initial state \<open>s\<close>.
\<close>
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
            ins_commited =
              List.map_filter (\<lambda>(p, _). if In ! p ! a \<noteq> [] then Some p else None) pairs;
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
            ins_commited =
              List.map_filter (\<lambda>(p, _). if In ! p ! a \<noteq> [] then Some p else None) pairs
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

paragraph \<open>Correctness for implementations of primitives\<close>

lemma dom_bounds_eq:
  "dom bounds = {0..<n_vs}"
  using bounds unfolding bounds_def
  apply simp
  unfolding n_vs_def dom_map_of_conv_image_fst
  apply safe
   apply (force dest: mem_nth; fail)
  apply (force dest: nth_mem; fail)
  done

lemma check_bounded_iff:
  "Simple_Network_Language.bounded bounds s \<longleftrightarrow> check_bounded s" if "dom s = {0..<n_vs}"
  using that
  unfolding dom_bounds_eq[symmetric]
  unfolding check_bounded_def Simple_Network_Language.bounded_def bounds_map_def bounds_def
  by auto

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
  proof (rule ccontr)
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
    using get_commited_mem_iff[of p "L ! p" L] by auto
  done

lemma get_commited_distinct: "distinct (get_commited L)"
  unfolding get_commited_def by (rule distinct_map_filterI) (auto simp: Let_def)

lemma is_upd_make_updI2:
  "is_upd s upds (mk_upds s upds)"
  if "(l, g, a, upds, r, l') \<in> Simple_Network_Language.trans (N p)" "p < n_ps"
    "dom s = {0..<n_vs}"
  using that var_set
  by (intro is_upd_make_updI, subst (asm) mem_trans_N_iff)
     (auto 4 5 simp flip: length_automata_eq_n_ps dest!: nth_mem)

lemma var_setD:
  "\<forall>(x, upd)\<in>set f. x < n_vs \<and> (\<forall>i\<in>vars_of_exp upd. i < n_vs)"
  if "(l, g, a, f, r, l') \<in> Simple_Network_Language.trans (N p)" "p < n_ps"
  using var_set that
  by (force dest: nth_mem simp flip: length_automata_eq_n_ps simp: mem_trans_N_iff)+

lemma is_upd_dom2:
  "dom s' = {0..<n_vs}" if "is_upd s f s'"
  "(l, g, a, f, r, l') \<in> Simple_Network_Language.trans (N p)" "p < n_ps"
  "dom s = {0..<n_vs}"
  unfolding that(4)[symmetric] using that by - (drule (1) var_setD, erule is_upd_dom, auto)

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
  if "dom s = {0..<n_vs}" 
    "\<forall>upd \<in> set upds. \<exists>p < n_ps. \<exists>l g a r l'.
        (l, g, a, upd, r, l') \<in> Simple_Network_Language.trans (N p)"
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

lemma is_upds_dom2:
  assumes "is_upds s upds s'"
    and "\<forall>f \<in> set upds. \<exists> p < n_ps. \<exists> l g a r l'.
      (l, g, a, f, r, l') \<in> Simple_Network_Language.trans (N p)"
    and "dom s = {0..<n_vs}"
  shows "dom s' = dom s"
  using assms by (elim is_upds_dom) (auto dest!: var_setD)

lemma is_upds_dom3:
  assumes "is_upds s (map fs ps) s'"
    and "\<forall>p\<in>set ps. (L ! p, gs p, a, fs p, rs p, ls' p) \<in> trans (N p)"
    and "set ps \<subseteq> {0..<n_ps}"
    and "dom s = {0..<n_vs}"
  shows "dom s' = dom s"
  using assms by (elim is_upds_dom2; force)

lemma is_upds_make_updsI3:
  "is_upds s (map fs ps) (fold (\<lambda>upd s. mk_upds s upd) (map fs ps) s)"
  if "dom s = {0..<n_vs}" 
    and "\<forall>p\<in>set ps. (L ! p, gs p, a, fs p, rs p, ls' p) \<in> trans (N p)"
    and "set ps \<subseteq> {0..<n_ps}"
  for s :: "nat \<Rightarrow> int option"
  using that by (elim is_upds_make_updsI2) force

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

paragraph \<open>An additional brute force method for forward-chaining of facts\<close>

method frules_all =
  frules, rotate_tac,
  frules, rotate_tac,
  frules, rotate_tac,
  frules, rotate_tac,
  frules, rotate_tac,

  frules, rotate_tac,
  frules, rotate_tac,
  frules, rotate_tac,
  frules, rotate_tac,
  frules, rotate_tac,

  frules, rotate_tac,
  frules, rotate_tac,
  frules, rotate_tac,
  frules, rotate_tac,
  frules, rotate_tac,

  frules, rotate_tac,
  frules, rotate_tac,
  frules, rotate_tac,
  frules, rotate_tac,
  frules, rotate_tac,
  dedup_prems

paragraph \<open>Internal transitions\<close>

lemma get_commited_memI:
  "(p, L ! p) \<in> set (get_commited L)" if "L ! p  \<in> commited (N p)" "p < n_ps"
  using that unfolding get_commited_mem_iff by simp

lemmas [forward2] =
  trans_i_mapD
  trans_i_mapI
  get_commited_memI
lemmas [forward3] =
  is_upd_make_updI2
lemmas [forward4] =
  is_updD
  is_upd_dom2

lemma int_trans_from_correct:
  "(int_trans_from, trans_int) \<in> transition_rel states'"
  unfolding transition_rel_def
proof clarsimp
  note [more_elims] = allE
  fix L s g a r L' s' assume "(L, s) \<in> states'"
  then have "L \<in> states" "dom s = {0..<n_vs}" "bounded bounds s"
    by auto
  then have [simp]: "length L = n_ps" "check_bounded s"
    by (auto simp: check_bounded_iff)
  show "(((L, s), g, a, r, L', s') \<in> trans_int)
    \<longleftrightarrow> ((g, a, r, L', s') \<in> set (int_trans_from (L, s)))"
  proof (cases "get_commited L = []")
    case True
    then have *: "((L, s), g, a, r, L', s') \<in> trans_int \<longleftrightarrow>
      ((L, s), g, a, r, L', s') \<in> {((L, s), g, Internal a, r, (L', s')) | L s l g f p a r l' L' s'.
        (l, g, Sil a, f, r, l') \<in> trans (N p) \<and>
        (\<forall>p < n_ps. L ! p \<notin> commited (N p)) \<and>
        L!p = l \<and> p < length L \<and> L' = L[p := l'] \<and> is_upd s f s' \<and>
        L \<in> states \<and> bounded bounds s \<and> bounded bounds s'
      }"
      unfolding get_commited_empty_iff[symmetric] trans_int_def by blast
    from True have **: "int_trans_from (L, s) = int_trans_from_all L s"
      unfolding int_trans_from_def by simp
    from \<open>dom s = _\<close> show ?thesis
      unfolding * ** int_trans_from_all_def
      apply clarsimp
      unfolding int_trans_from_loc_def Let_def set_map_filter
      apply clarsimp
      apply safe
      subgoal for f p a' l'
        apply frules
        unfolding check_bounded_iff by (intros; solve_triv)
      subgoal for p _ a' upds l'
        apply simp
        apply frules
        using \<open>L \<in> states\<close> \<open>check_bounded s\<close> True[folded get_commited_empty_iff]
        unfolding check_bounded_iff by (intros; simp)
      done
  next
    case False
    then have *: "((L, s), g, a, r, L', s') \<in> trans_int \<longleftrightarrow>
      ((L, s), g, a, r, L', s') \<in> {((L, s), g, Internal a, r, (L', s')) | L s l g f p a r l' L' s'.
        (l, g, Sil a, f, r, l') \<in> trans (N p) \<and>
        l \<in> commited (N p) \<and>
        L!p = l \<and> p < length L \<and> L' = L[p := l'] \<and> is_upd s f s' \<and>
        L \<in> states \<and> bounded bounds s \<and> bounded bounds s'
      }"
      unfolding get_commited_empty_iff[symmetric] trans_int_def by blast
    from False have **: "int_trans_from (L, s) = int_trans_from_vec (get_commited L) L s"
      unfolding int_trans_from_def by simp
    from \<open>dom s = _\<close> \<open>L \<in> states\<close> show ?thesis
      unfolding * ** int_trans_from_vec_def
      apply clarsimp
      unfolding int_trans_from_loc_def Let_def set_map_filter
      apply clarsimp
      apply safe
      subgoal for f p a' l'
        apply frules
        unfolding check_bounded_iff by (intros; solve_triv)
      subgoal for p _ a' upds l'
        unfolding get_commited_mem_iff
        apply (elims; simp)
        apply frules
        unfolding check_bounded_iff by (intros; solve_triv)
      done
  qed
qed


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
    if "(g, a, r) \<in> set (fold ?f xs acc ! a')" "(g, a, r) \<notin> set (acc ! a')" "a' < length acc"
    for acc
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

paragraph \<open>Binary transitions\<close>

lemma bin_trans_from_correct:
  "(bin_trans_from, trans_bin) \<in> transition_rel states'"
  unfolding transition_rel_def
proof clarsimp
  fix L s g a r L' s' assume "(L, s) \<in> states'"
  then have "L \<in> states" "dom s = {0..<n_vs}" "bounded bounds s"
    by auto
  then have [simp]: "length L = n_ps"
    by auto
  define IN where  "IN  = all_actions_by_state trans_in_map L"
  define OUT where "OUT = all_actions_by_state trans_out_map L"
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
    using that unfolding IN_def by (auto dest: in_all_actions_by_stateD split: option.split_asm)
  have OUT_p_num:
    "p < n_ps"
    if "(p, g, a', f, r, l') \<in> set (OUT ! a1)" "a1 < num_actions"
    for p g a' f r l' a1
    using that unfolding OUT_def by (auto dest: in_all_actions_by_stateD split: option.split_asm)
  have actions_unique:
    "a' = a1"
    if "(p, g, a', f, r, l') \<in> set (IN ! a1)" "a1 < num_actions"
    for p g a' f r l' a1
    using that unfolding IN_def trans_in_map_def set_map_filter
    by (auto dest: in_all_actions_by_stateD split: option.split_asm)
(*
  note [forward3] = OUT_I IN_I
  note [forward2] = action_setD IN_D OUT_D
*)
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
        L' = L[p := l1', q := l2'] \<and> is_upd s f1 s' \<and> is_upd s' f2 s''
        \<and> L \<in> states \<and> bounded bounds s \<and> bounded bounds s''
      }
    "
      unfolding trans_bin_def by blast
    from True have **:
      "bin_trans_from (L, s)
      = concat (map (\<lambda>a. pairs_by_action L s (OUT ! a) (IN ! a)) [0..<num_actions])"
      unfolding bin_trans_from_def IN_def OUT_def by simp
    note [forward3] = OUT_I IN_I
    note [forward2] = action_setD IN_D OUT_D
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
          apply frules
          apply simp
          apply frules_all
          unfolding check_bounded_iff by (intros; solve_triv)
        subgoal
          by (simp; frules; simp)
        done
      subgoal
        apply simp
        apply frules
        apply elims
        apply frules_all
        apply frules_all
        apply elims
        apply intros
        using \<open>bounded bounds s\<close> unfolding check_bounded_iff[symmetric] by solve_triv+
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
        L' = L[p := l1', q := l2'] \<and> is_upd s f1 s' \<and> is_upd s' f2 s'' \<and>
        L \<in> states \<and> bounded bounds s \<and> bounded bounds s''
      }"
      unfolding trans_bin_def by blast
    let ?S1 =
      "{((L, s), g1 @ g2, Bin a, r1 @ r2, (L', s'')) |
        L s L' s' s'' a p q l1 g1 f1 r1 l1' l2 g2 f2 r2 l2'.
          (l1, g1, In a,  f1, r1, l1') \<in> trans (N p) \<and>
          (l2, g2, Out a, f2, r2, l2') \<in> trans (N q) \<and>
          l1 \<in> commited (N p) \<and>
          L!p = l1 \<and> L!q = l2 \<and> p < length L \<and> q < length L \<and> p \<noteq> q \<and>
          L' = L[p := l1', q := l2'] \<and> is_upd s f1 s' \<and> is_upd s' f2 s'' \<and>
          L \<in> states \<and> bounded bounds s \<and> bounded bounds s''
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
          is_upd s f1 s' \<and> is_upd s' f2 s'' \<and>
          L \<in> states \<and> bounded bounds s \<and> bounded bounds s''
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
    note [forward2] = action_setD
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
          supply [forward4] = In2_I
          supply [forward3] = OUT_I
          apply frules_all
          apply simp
          apply frules_all
          unfolding check_bounded_iff by (intros; solve_triv)
        subgoal
          by (simp; frules; simp)
        done
      subgoal
        supply [forward2] = In2_D
        supply [forward2] = OUT_D
        apply simp
        apply frules_all
        apply elims
        apply frules_all
        apply elims
        apply simp
        apply frules_all
        using \<open>bounded bounds s\<close> unfolding check_bounded_iff[symmetric] by (intros; solve_triv)
      done
    moreover from \<open>dom s = _\<close> \<open>L \<in> _\<close> have "
      ((L, s), g, a, r, L', s') \<in> ?S2 \<longleftrightarrow> (g, a, r, L', s')
      \<in> set (concat (map (\<lambda>a. pairs_by_action L s (Out2 ! a) (IN ! a)) [0..<num_actions]))"
      supply [forward3] = OUT_I IN_I
      supply [forward2] = action_setD IN_D OUT_D
      apply clarsimp
      unfolding pairs_by_action_def
      apply (clarsimp simp: set_map_filter Let_def)
      apply safe
      subgoal for _ s'' _ a' p q l1 g1 f1 r1 l1' l2 g2 f2 r2 l2'
        apply clarsimp
        apply (inst_existentials a')
        subgoal
          supply [forward4] = Out2_I
          apply frules_all
          apply simp
          apply frules_all
          unfolding check_bounded_iff by (intros; solve_triv)
        subgoal
          by (auto dest: action_setD)
        done
      subgoal
        supply [forward2] = Out2_D
        apply simp
        apply frules_all
        apply elims
        apply frules_all
        apply elims
        apply simp
        apply frules_all
        using \<open>bounded bounds s\<close> unfolding check_bounded_iff[symmetric] by (intros; solve_triv)
      done
    ultimately show ?thesis
      unfolding * ** by simp
  qed
qed

paragraph \<open>Broadcast transitions\<close>

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
proof clarsimp
  fix L s g a r L' s' assume "(L, s) \<in> states'"
  then have "L \<in> states" "dom s = {0..<n_vs}" "bounded bounds s"
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
    supply [forward2] = action_setD
    supply [forward4] = is_upd_dom2 is_upds_dom3 is_updsD[rotated 3] OUT_I
    apply frule2
    apply simp
    apply (frule make_combsD, assumption+)
    apply frules_all
    apply simp
    apply (inst_existentials p)
      apply (auto; fail)
     apply (intros add: more_intros)
      apply (solve_triv | intros add: more_intros UN_I)+
     apply (simp add: *** upd_swap; fail)
    unfolding check_bounded_iff[symmetric] .
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
    supply [forward2] = action_setD
    supply [forward3] = is_upds_make_updsI3[rotated] OUT_D
    supply [forward4] = is_upd_dom2 is_upds_dom3 is_updsD[rotated 3] OUT_I
    using that
    unfolding make_trans_def
    apply mini_ex
    apply (clarsimp simp: set_map_filter Let_def split: prod.split if_split_asm)
    subgoal for g1 a1 r1 f1 l1' xs
      apply (drule make_combsI, assumption+)
      apply frules
      apply elims
      apply dedup_prems
      apply frules_all
      apply (simp add: ***)
      apply intros
                    apply solve_triv+
                  apply (erule upd_swap[symmetric]; fail)
                 apply solve_triv+
                apply (erule bspec; assumption)
               apply (elims add: allE; intros?; assumption)
              apply solve_triv+
      subgoal for ps gs fs rs ls'
        by frules_all simp
      subgoal for ps gs fs rs ls'
        apply (subst check_bounded_iff)
        subgoal
          apply (subst is_upds_dom3)
             apply (simp add: fold_map comp_def; fail)
            apply assumption+
          done
        subgoal
          by simp
        done
      apply solve_triv
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
          is_upds s'' (map fs ps) s' \<and>
          bounded bounds s') =
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
        L \<in> states \<and> bounded bounds s \<and> bounded bounds s''
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
    from \<open>dom s = _\<close> \<open>L \<in> _\<close> \<open>bounded bounds s\<close> show ?thesis
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
        L \<in> states \<and> bounded bounds s \<and> bounded bounds s''
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
    from \<open>dom s = _\<close> \<open>L \<in> _\<close> \<open>bounded bounds s\<close> show ?thesis
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

end (* Anonymous context for simp setup *)

end (* Simple Network Impl nat *)

end (* Theory *)
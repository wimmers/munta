theory Simple_Network_Language_Impl_Refine
  imports Simple_Network_Language_Impl
begin

paragraph \<open>Notation\<close>

no_notation Ref.update ("_ := _" 62)
no_notation Stream.snth (infixl "!!" 100)
no_notation Bits.bits_class.test_bit (infixl "!!" 100)

paragraph \<open>Expression evaluation\<close>

fun bval :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'b :: linorder) bexp \<Rightarrow> bool" where
  "bval _ bexp.true \<longleftrightarrow> True" |
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
| "eval s (binop f e1 e2) = f (eval s e1) (eval s e2)"
| "eval s (unop f e) = f (eval s e)"

lemma check_bexp_determ:
  "b1 = b2" if "check_bexp s e b1" "check_bexp s e b2"
  using that
  by (induction e arbitrary: b1 b2)
    (erule check_bexp.cases; erule check_bexp.cases; simp; blast)+

lemma is_val_determ:
  "v1 = v2" if "is_val s e v1" "is_val s e v2"
  using that by (induction e arbitrary: v1 v2) (auto dest: check_bexp_determ elim!: is_val_elims)

lemma is_upd_determ:
  "s1 = s2" if "is_upd s f s1" "is_upd s f s2"
  using that
  unfolding is_upd_def
  apply auto
  apply (fo_rule fun_cong)
  apply (fo_rule arg_cong)
  by (smt
      case_prodE case_prodE' case_prod_conv is_val_determ list.rel_eq list_all2_swap list_all2_trans
     )

lemma is_upds_determ:
  "s1 = s2" if "is_upds s fs s1" "is_upds s fs s2"
  using that
  by (induction fs arbitrary: s) (auto 4 4 elim: is_upds.cases dest: is_upd_determ)

lemma check_bexp_bval:
  "check_bexp s e (bval (the o s) e)" if "\<forall>x \<in> vars_of_bexp e. x \<in> dom s"
  using that by (induction e)(simp; (subst eq_commute)?; rule check_bexp.intros; simp add: dom_def)+

lemma is_val_eval:
  "is_val s e (eval (the o s) e)" if "\<forall>x \<in> vars_of_exp e. x \<in> dom s"
  using that by (induction e) (subst eval.simps; rule is_val.intros; auto intro: check_bexp_bval)+

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
  unfolding trans_def
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
  if \<open>(l, b, g, a, f, r, l') \<in> Simple_Network_Language.trans (N p)\<close> \<open>p < n_ps\<close>
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

definition (in Simple_Network_Impl_nat_defs)
  "invs i \<equiv> let m = default_map_of [] (snd (snd (automata ! i)));
    m' = map (\<lambda> j. m j) [0..<num_states i]
  in m'"

definition (in Simple_Network_Impl_nat_defs)
  "invs1 \<equiv> map (\<lambda> i. let m = default_map_of [] (snd (snd (automata ! i)));
    m' = map (\<lambda> j. m j) [0..<num_states i]
  in m') [0..<n_ps]"

definition (in Simple_Network_Impl_nat_defs)
  "invs2 \<equiv> IArray (map (\<lambda> i. let m = default_map_of [] (snd (snd (automata ! i)));
    m' = IArray (map (\<lambda> j. m j) [0..<num_states i])
  in m') [0..<n_ps])"

lemma refine_invs2:
  "invs2 !! i !! j = invs1 ! i ! j" if "i < n_ps"
  using that unfolding invs2_def invs1_def by simp

definition (in Simple_Network_Impl_nat_defs)
  "inv_fun \<equiv> \<lambda>(L, _).
    concat (map (\<lambda>i. invs1 ! i ! (L ! i)) [0..<n_ps])"

lemma refine_invs1:
  \<open>invs1 ! i = invs i\<close> if \<open>i < n_ps\<close>
  using that unfolding invs_def invs1_def by simp

lemma invs_simp:
  "invs1 ! i ! (L ! i) = Simple_Network_Language.inv (N i) (L ! i)"
  if "i < n_ps" "L \<in> states"
  using that unfolding refine_invs1[OF \<open>i < _\<close>] invs_def N_def fst_conv snd_conv
  unfolding inv_def
  by (subst nth_map;
      clarsimp split: prod.split simp: automaton_of_def length_automata_eq_n_ps L_i_len)

lemma inv_fun_inv_of':
  "(inv_fun, inv_of prod_ta) \<in> inv_rel R states'" if "R \<subseteq> Id \<times>\<^sub>r S"
  using that
  unfolding inv_rel_def
  unfolding inv_fun_def
  unfolding inv_of_prod prod_inv_def
  apply (clarsimp simp: states'_def)
  apply (rule arg_cong[where f = concat])
  apply (auto simp add: invs_simp cong: map_cong)
  done

lemma inv_fun_alt_def:
  "inv_fun = (\<lambda>(L, _). concat (map (\<lambda>i. invs2 !! i !! (L ! i)) [0..<n_ps]))"
  unfolding inv_fun_def
  apply (intro ext)
  apply (clarsimp simp del: IArray.sub_def)
  apply (fo_rule arg_cong)
  apply (simp add: refine_invs2 del: IArray.sub_def)
  done

end (* Simple Network Impl nat *)

paragraph \<open>Implementation of transitions\<close>

context Simple_Network_Impl_nat_defs
begin

definition
  "bounds_map \<equiv> the o map_of bounds'"

definition
  "check_bounded s =
    (\<forall>x \<in> dom s. fst (bounds_map x) \<le> the (s x) \<and> the (s x) \<le> snd (bounds_map x))"

text \<open>Compute pairs of processes with committed initial locations from location vector.\<close>
definition
  "get_commited L =
    List.map_filter (\<lambda>p.
    let l = L ! p in
    if l \<in> set (fst (automata ! p)) then Some (p, l) else None) [0..<n_ps]"

text \<open>Given a process and a location, return the corresponding transitions.\<close>
definition
  "trans_map i \<equiv>
    let m = union_map_of (fst (snd (automata ! i))) in (\<lambda>j.
      case m j of None \<Rightarrow> [] | Some xs \<Rightarrow> xs)"

text \<open>Filter for internal transitions.\<close>
definition
  "trans_i_map i j \<equiv>
    List.map_filter
      (\<lambda> (b, g, a, m, l'). case a of Sil a \<Rightarrow> Some (b, g, a, m, l') | _ \<Rightarrow> None)
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
    List.map_filter (\<lambda> (b, g, a, f, r, l').
      let s' = mk_upds s f in
        if bval (the o s) b \<and> check_bounded s' then Some (g, Internal a, r, (L[p := l'], s'))
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
  "actions_by_state i \<equiv>
   fold (\<lambda> t acc. acc[fst (snd (snd t)) := (i, t) # (acc ! fst (snd (snd t)))])"

definition
  "all_actions_by_state t L \<equiv>
    fold (\<lambda> i. actions_by_state i (t i (L ! i))) [0..<n_ps] (repeat [] num_actions)"

definition
  "all_actions_from_vec t vec \<equiv>
    fold (\<lambda>(p, l). actions_by_state p (t p l)) vec (repeat [] num_actions)"


definition
  "pairs_by_action L s OUT IN \<equiv>
  concat (
    map (\<lambda> (p, b1, g1, a1, f1, r1, l1).
      List.map_filter (\<lambda> (q, b2, g2, a2, f2, r2, l2).
        if p = q then None else
          let s' = mk_upds (mk_upds s f1) f2 in
          if bval (the o s) b1 \<and> bval (the o s) b2 \<and> check_bounded s'
          then Some (g1 @ g2, Bin a1, r1 @ r2, (L[p := l1, q := l2], s'))
          else None
    ) OUT) IN)
  "

definition
  "trans_in_map i j \<equiv>
    List.map_filter
      (\<lambda> (b, g, a, m, l'). case a of In a \<Rightarrow> Some (b, g, a, m, l') | _ \<Rightarrow> None)
    (trans_map i j)"

definition
  "trans_out_map i j \<equiv>
    List.map_filter
      (\<lambda> (b, g, a, m, l'). case a of Out a \<Rightarrow> Some (b, g, a, m, l') | _ \<Rightarrow> None)
    (trans_map i j)"

definition
  "bin_actions = filter (\<lambda>a. a \<notin> set broadcast) [0..<num_actions]"

lemma mem_bin_actions_iff:
  "a \<in> set bin_actions \<longleftrightarrow> a \<notin> local.broadcast \<and> a < num_actions "
  unfolding bin_actions_def broadcast_def by auto

definition
  "bin_trans_from \<equiv> \<lambda>(L, s).
    let
      pairs = get_commited L;
      In =  all_actions_by_state trans_in_map L;
      Out = all_actions_by_state trans_out_map L
    in
    if pairs = [] then
      concat (map (\<lambda>a. pairs_by_action L s (Out ! a) (In ! a)) bin_actions)
    else
      let
        In2  = all_actions_from_vec trans_in_map pairs;
        Out2 = all_actions_from_vec trans_out_map pairs
      in
        concat (map (\<lambda>a. pairs_by_action L s (Out ! a) (In2 ! a)) bin_actions)
      @ concat (map (\<lambda>a. pairs_by_action L s (Out2 ! a) (In ! a)) bin_actions)
    "

definition
  "trans_in_broad_map i j \<equiv>
    List.map_filter
      (\<lambda> (b, g, a, m, l').
      case a of In a \<Rightarrow> if a \<in> set broadcast then Some (b, g, a, m, l') else None | _ \<Rightarrow> None)
    (trans_map i j)"

definition
  "trans_out_broad_map i j \<equiv>
    List.map_filter
      (\<lambda> (b, g, a, m, l').
      case a of Out a \<Rightarrow> if a \<in> set broadcast then Some (b, g, a, m, l') else None | _ \<Rightarrow> None)
    (trans_map i j)"

definition
  "actions_by_state' xs \<equiv>
    fold (\<lambda> t acc. acc[fst (snd (snd t)) := t # (acc ! fst (snd (snd t)))])
      xs (repeat [] num_actions)"

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
      Out = map (\<lambda>p. trans_out_broad_grouped p (L ! p)) [0..<n_ps];
      In  = map (map (filter (\<lambda> (b, _). bval (the o s) b))) In;
      Out = map (map (filter (\<lambda> (b, _). bval (the o s) b))) Out
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
                combs = (
                  if combs = [] then [[x]. x \<leftarrow> outs]
                  else concat (map (\<lambda>x. map (\<lambda>xs. x # xs) combs) outs));
                init = ([], Broad a, [], (L, s))
              in
              List.map_filter (\<lambda>comb.
                let (g, a, r, L', s) =
                  fold
                    (\<lambda>(q, _, g2, a2, f2, r2, l2) (g1, a, r1, (L, s)).
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
                combs = (
                  if combs = [] then [[x]. x \<leftarrow> outs]
                  else concat (map (\<lambda>x. map (\<lambda>xs. x # xs) combs) outs));
                init = ([], Broad a, [], (L, s))
              in
              List.map_filter (\<lambda>comb.
                let (g, a, r, L', s) =
                  fold
                    (\<lambda>(q, _, g2, a2, f2, r2, l2) (g1, a, r1, (L, s)).
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

end (* Simple Network Impl nat defs *)

(* XXX Move *)
lemma product_lists_empty: "product_lists xss = [] \<longleftrightarrow> (\<exists>xs \<in> set xss. xs = [])" for xss
  by (induction xss) auto

context Simple_Network_Impl_nat
begin

lemma broad_trans_from_alt_def:
  "broad_trans_from \<equiv> \<lambda>(L, s).
    let
      pairs = get_commited L;
      In  = map (\<lambda>p. trans_in_broad_grouped p (L ! p)) [0..<n_ps];
      Out = map (\<lambda>p. trans_out_broad_grouped p (L ! p)) [0..<n_ps];
      In  = map (map (filter (\<lambda> (b, _). bval (the o s) b))) In;
      Out = map (map (filter (\<lambda> (b, _). bval (the o s) b))) Out
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
                combs = (
                  if combs = [] then [[x]. x \<leftarrow> outs]
                  else concat (map (\<lambda>x. map (\<lambda>xs. x # xs) combs) outs));
                init = ([], Broad a, [], (L, s))
              in
              filter (\<lambda> (g, a, r, L, s). check_bounded s) (
                map (\<lambda>comb.
                    fold
                      (\<lambda>(q, _, g2, a2, f2, r2, l2) (g1, a, r1, (L, s)).
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
                combs = (
                  if combs = [] then [[x]. x \<leftarrow> outs]
                  else concat (map (\<lambda>x. map (\<lambda>xs. x # xs) combs) outs));
                init = ([], Broad a, [], (L, s))
              in
              filter (\<lambda> (g, a, r, L, s). check_bounded s) (
                map (\<lambda>comb.
                    fold
                      (\<lambda>(q, _, g2, a2, f2, r2, l2) (g1, a, r1, (L, s)).
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
  unfolding commited_def
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
  if "(l, b, g, a, upds, r, l') \<in> Simple_Network_Language.trans (N p)" "p < n_ps"
    "dom s = {0..<n_vs}"
  using that var_set
  by (intro is_upd_make_updI, subst (asm) mem_trans_N_iff)
     (auto 4 5 simp flip: length_automata_eq_n_ps dest!: nth_mem)

lemma var_setD:
  "\<forall>(x, upd)\<in>set f. x < n_vs \<and> (\<forall>i\<in>vars_of_exp upd. i < n_vs)"
  if "(l, b, g, a, f, r, l') \<in> Simple_Network_Language.trans (N p)" "p < n_ps"
  using var_set that
  by (force dest: nth_mem simp flip: length_automata_eq_n_ps simp: mem_trans_N_iff)+

lemma var_setD2:
  "\<forall>i\<in>vars_of_bexp b. i < n_vs"
  if "(l, b, g, a, f, r, l') \<in> Simple_Network_Language.trans (N p)" "p < n_ps"
  using var_set that
  by (force dest: nth_mem simp flip: length_automata_eq_n_ps simp: mem_trans_N_iff)+

lemma is_upd_dom2:
  "dom s' = {0..<n_vs}" if "is_upd s f s'"
  "(l, b, g, a, f, r, l') \<in> Simple_Network_Language.trans (N p)" "p < n_ps"
  "dom s = {0..<n_vs}"
  unfolding that(4)[symmetric] using that by - (drule (1) var_setD, erule is_upd_dom, auto)

lemma is_updD:
  "s' = mk_upds s f" if "is_upd s f s'"
  "(l, b, g, a, f, r, l') \<in> Simple_Network_Language.trans (N p)" "p < n_ps"
  "dom s = {0..<n_vs}"
proof -
  from is_upd_make_updI2[OF that(2-)] have "is_upd s f (mk_upds s f)" .
  from is_upd_determ[OF that(1) this] show ?thesis .
qed

lemma is_upds_make_updsI2:
  "is_upds s upds (fold (\<lambda>upd s. mk_upds s upd) upds s)"
  if "dom s = {0..<n_vs}" 
    "\<forall>upd \<in> set upds. \<exists>p < n_ps. \<exists>l b g a r l'.
        (l, b, g, a, upd, r, l') \<in> Simple_Network_Language.trans (N p)"
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
    and "\<forall>f \<in> set upds. \<exists> p < n_ps. \<exists> l b g a r l'.
      (l, b, g, a, f, r, l') \<in> Simple_Network_Language.trans (N p)"
    and "dom s = {0..<n_vs}"
  shows "dom s' = dom s"
  using assms by (elim is_upds_dom) (auto dest!: var_setD)

lemma is_upds_dom3:
  assumes "is_upds s (map fs ps) s'"
    and "\<forall>p\<in>set ps. (L ! p, bs p, gs p, a, fs p, rs p, ls' p) \<in> trans (N p)"
    and "set ps \<subseteq> {0..<n_ps}"
    and "dom s = {0..<n_vs}"
  shows "dom s' = dom s"
  using assms by (elim is_upds_dom2; force)

lemma is_upds_make_updsI3:
  "is_upds s (map fs ps) (fold (\<lambda>upd s. mk_upds s upd) (map fs ps) s)"
  if "dom s = {0..<n_vs}" 
    and "\<forall>p\<in>set ps. (L ! p, bs p, gs p, a, fs p, rs p, ls' p) \<in> trans (N p)"
    and "set ps \<subseteq> {0..<n_ps}"
  for s :: "nat \<Rightarrow> int option"
  using that by (elim is_upds_make_updsI2) force

lemma is_updsD:
  assumes 
    "dom s = {0..<n_vs}" and
    "\<forall>p\<in>set ps.
        (ls p, bs p, gs p, a, fs p, rs p, ls' p)
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
  using assms unfolding trans_map_def N_def fst_conv snd_conv trans_def
  by (subst (asm) nth_map) (auto dest: in_union_map_ofI split: prod.split_asm simp: automaton_of_def)

lemma trans_i_mapI:
  assumes
    "(L ! p, b, g, Sil a', f, r, l') \<in> Simple_Network_Language.trans (N p)"
    "p < n_ps"
  shows
    "(b, g, a', f, r, l') \<in> set (trans_i_map p (L ! p))"
  using assms unfolding trans_i_map_def set_map_filter by (fastforce dest: trans_mapI)

lemma trans_mapI':
  assumes
    "(l, b, g, a, f, r, l') \<in> Simple_Network_Language.trans (N p)"
    "p < n_ps"
  shows
    "(b, g, a, f, r, l') \<in> set (trans_map p l)"
  using assms unfolding trans_map_def N_def fst_conv snd_conv trans_def
  by (subst (asm) nth_map) (auto dest: in_union_map_ofI split: prod.split_asm simp: automaton_of_def)

lemma trans_mapD:
  assumes
    "(b, g, a, f, r, l') \<in> set (trans_map p l)"
    "p < n_ps"
  shows
    "(l, b, g, a, f, r, l') \<in> Simple_Network_Language.trans (N p)"
  using assms unfolding trans_map_def N_def fst_conv snd_conv trans_def
  by (subst nth_map) (auto split: prod.split elim: in_union_map_ofD[rotated] simp: automaton_of_def)

lemma trans_map_iff:
  assumes
    "p < n_ps"
  shows
    "(b, g, a, f, r, l') \<in> set (trans_map p l)
 \<longleftrightarrow> (l, b, g, a, f, r, l') \<in> Simple_Network_Language.trans (N p)"
  using trans_mapD trans_mapI' \<open>p < n_ps\<close> by auto

lemma trans_i_mapD:
  assumes
    "(b, g, a', f, r, l') \<in> set (trans_i_map p (L ! p))"
    "p < n_ps"
  shows
    "(L ! p, b, g, Sil a', f, r, l') \<in> Simple_Network_Language.trans (N p)"
  using assms unfolding trans_i_map_def set_map_filter
  by (force split: act.split_asm intro: trans_mapD)

paragraph \<open>An additional brute force method for forward-chaining of facts\<close>

method frules_all =
  repeat_rotate \<open>frules\<close>, dedup_prems

paragraph \<open>Internal transitions\<close>

lemma get_commited_memI:
  "(p, L ! p) \<in> set (get_commited L)" if "L ! p  \<in> commited (N p)" "p < n_ps"
  using that unfolding get_commited_mem_iff by simp

lemma check_bexp_bvalI:
  "bval (the o s) b" if "check_bexp s b True"
  "(l, b, g, a, f, r, l') \<in> Simple_Network_Language.trans (N p)" "p < n_ps"
  "dom s = {0..<n_vs}"
proof -
  from var_setD2[OF that(2,3)] \<open>dom s = {0..<n_vs}\<close> have "check_bexp s b (bval (the o s) b)"
    by (intro check_bexp_bval, simp)
  with check_bexp_determ that(1) show ?thesis
    by auto
qed

lemma check_bexp_bvalD:
  "check_bexp s b True" if "bval (the o s) b"
  "(l, b, g, a, f, r, l') \<in> Simple_Network_Language.trans (N p)" "p < n_ps"
  "dom s = {0..<n_vs}"
proof -
  from var_setD2[OF that(2,3)] \<open>dom s = {0..<n_vs}\<close> have "check_bexp s b (bval (the o s) b)"
    by (intro check_bexp_bval, simp)
  with check_bexp_determ that(1) show ?thesis
    by auto
qed

lemmas [forward2] =
  trans_i_mapD
  trans_i_mapI
  get_commited_memI
lemmas [forward3] =
  is_upd_make_updI2
lemmas [forward4] =
  is_updD
  is_upd_dom2
  check_bexp_bvalI
  check_bexp_bvalD

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
      ((L, s), g, a, r, L', s') \<in> {((L, s), g, Internal a, r, (L', s')) | L s l b g f p a r l' L' s'.
        (l, b, g, Sil a, f, r, l') \<in> trans (N p) \<and>
        (\<forall>p < n_ps. L ! p \<notin> commited (N p)) \<and>
        check_bexp s b True \<and>
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
      subgoal for b f p a' l'
        apply frules
        unfolding check_bounded_iff by (intros; solve_triv)
      subgoal for p _ a' upds l'
        apply simp
        apply frules
        using \<open>L \<in> states\<close> \<open>check_bounded s\<close> True[folded get_commited_empty_iff]
        unfolding check_bounded_iff by (intros; solve_triv)
      done
  next
    case False
    then have *: "((L, s), g, a, r, L', s') \<in> trans_int \<longleftrightarrow>
      ((L, s), g, a, r, L', s') \<in> {((L, s), g, Internal a, r, (L', s')) | L s l b g f p a r l' L' s'.
        (l, b, g, Sil a, f, r, l') \<in> trans (N p) \<and>
        l \<in> commited (N p) \<and>
        L!p = l \<and> p < length L \<and> check_bexp s b True \<and> L' = L[p := l'] \<and> is_upd s f s' \<and>
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
    "(b1, g1, a, r1) \<in> set xs" "a < length acc"
  shows
    "(q, b1, g1, a, r1) \<in> set (actions_by_state q xs acc ! a)
    \<and> a < length (actions_by_state q xs acc)"
  using assms unfolding actions_by_state_def
  apply (induction xs arbitrary: acc)
   apply (simp; fail)
  apply simp
  apply (erule disjE)
   apply (rule fold_acc_preserv
      [where P = "\<lambda> acc. (q, b1, g1, a, r1) \<in> set (acc ! a) \<and> a < length acc"]
      )
    apply (subst list_update_nth_split; auto)
  by auto

lemma in_actions_by_state'I:
  assumes
    "(b1, g1, a, r1) \<in> set xs" "a < num_actions"
  shows
    "(b1, g1, a, r1) \<in> set (actions_by_state' xs ! a)
    \<and> a < length (actions_by_state' xs)"
proof -
  let ?f = "(\<lambda>t acc. acc[fst (snd (snd t)) := t # acc ! fst (snd (snd t))])"
  have "(b1, g1, a, r1) \<in> set (fold ?f xs acc ! a)
    \<and> a < length (fold ?f xs acc)" if "a < length acc" for acc
    using assms(1) that
    apply (induction xs arbitrary: acc)
     apply (simp; fail)
    apply simp
    apply (erule disjE)
     apply (rule fold_acc_preserv
        [where P = "\<lambda> acc. (b1, g1, a, r1) \<in> set (acc ! a) \<and> a < length acc"]
        )
      apply (subst list_update_nth_split; auto)
    by auto
  with \<open>a < _\<close> show ?thesis
    unfolding actions_by_state'_def by simp
qed

lemma in_actions_by_state_preserv:
  assumes
    "(q, b1, g1, a, r1) \<in> set (acc ! a)" "a < length acc"
  shows
    "(q, b1, g1, a, r1) \<in> set (actions_by_state y xs acc ! a)
    \<and> a < length (actions_by_state y xs acc)"
  using assms unfolding actions_by_state_def
  apply -
  apply (rule fold_acc_preserv
      [where P = "\<lambda> acc. (q, b1, g1, a, r1) \<in> set (acc ! a) \<and> a < length acc"]
      )
   apply (subst list_update_nth_split; auto)
  by auto

lemma length_actions_by_state_preserv[simp]:
  shows "length (actions_by_state y xs acc) = length acc"
  unfolding actions_by_state_def by (auto intro: fold_acc_preserv simp: list_update_nth_split)

lemma in_all_actions_by_stateI:
  assumes
    "a < num_actions" "q < n_ps" "(b1, g1, a, r1) \<in> set (M q (L ! q))"
  shows
    "(q, b1, g1, a, r1) \<in> set (all_actions_by_state M L ! a)"
  unfolding all_actions_by_state_def
  apply (rule fold_acc_ev_preserv
      [where P = "\<lambda> acc. (q, b1, g1, a, r1) \<in> set (acc ! a)" and Q = "\<lambda> acc. a < length acc",
        THEN conjunct1]
      )
      apply (rule in_actions_by_state_preserv[THEN conjunct1])
  using assms by (auto intro: in_actions_by_stateI[THEN conjunct1])

lemma in_all_actions_from_vecI:
  assumes
    "a < num_actions" "(b1, g1, a, r1) \<in> set (M q l)" "(q, l) \<in> set pairs"
  shows
    "(q, b1, g1, a, r1) \<in> set (all_actions_from_vec M pairs ! a)"
  unfolding all_actions_from_vec_def using assms
  by (intro fold_acc_ev_preserv
      [where P = "\<lambda> acc. (q, b1, g1, a, r1) \<in> set (acc ! a)" and Q = "\<lambda> acc. a < length acc",
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
    by (cases "fst (snd (snd x)) = j"; simp)
  using assms by auto

lemma actions_by_state_inj':
  assumes "j < length acc" "(q, a) \<notin> set (acc ! j)" "(q, a) \<in> set (actions_by_state i xs acc ! j)"
  shows "i = q"
  using actions_by_state_inj[OF assms(1)] assms(2-) by fast

lemma in_actions_by_stateD:
  assumes
    "(q, b, g, a, t) \<in> set (actions_by_state i xs acc ! j)" "(q, b, g, a, t) \<notin> set (acc ! j)"
    "j < length acc"
  shows
    "(b, g, a, t) \<in> set xs \<and> j = a"
  using assms unfolding actions_by_state_def
  apply -
  apply (drule fold_evD
      [where y = "(b, g, a, t)" and Q = "\<lambda> acc'. length acc' = length acc"
        and R = "\<lambda> (_, _, a', t). a' = j"]
      )
       apply assumption
    (* XXX Define asm split rule *)
      apply (subst (asm) list_update_nth_split[of j]; force)
     apply simp+
   apply (subst (asm) list_update_nth_split[of j]; force)
  by auto

lemma in_actions_by_state'D:
  assumes
    "(b, g, a, r) \<in> set (actions_by_state' xs ! a')" "a' < num_actions"
  shows
    "(b, g, a, r) \<in> set xs \<and> a' = a"
proof -
  let ?f = "(\<lambda>t acc. acc[fst (snd (snd t)) := t # acc ! fst (snd (snd t))])"
  have "(b, g, a, r) \<in> set xs \<and> a' = a"
    if "(b, g, a, r) \<in> set (fold ?f xs acc ! a')" "(b, g, a, r) \<notin> set (acc ! a')" "a' < length acc"
    for acc
    using that
    apply -
    apply (drule fold_evD
        [where y = "(b, g, a, r)" and Q = "\<lambda> acc'. length acc' = length acc"
          and R = "\<lambda> (_, _, a, t). a = a'"]
        )
         apply ((subst (asm) list_update_nth_split[where j = a'])?; auto; fail)+
    done
  with assms show ?thesis
    unfolding actions_by_state'_def by auto
qed

lemma in_all_actions_by_stateD:
  assumes
    "(q, b1, g1, a, r1) \<in> set (all_actions_by_state M L ! a')" "a' < num_actions"
  shows
    "(b1, g1, a, r1) \<in> set (M q (L ! q)) \<and> q < n_ps \<and> a' = a"
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

lemma length_actions_by_state'_preserv:
  "length (actions_by_state' xs) = num_actions"
  unfolding actions_by_state'_def by (rule fold_acc_preserv; simp)

lemma all_actions_from_vecD:
  assumes
    "(q, b1, g1, a, r1) \<in> set (all_actions_from_vec M pairs ! a')" "a' < num_actions"
    "distinct (map fst pairs)"
  shows
    "\<exists> l. (q, l) \<in> set pairs \<and> (b1, g1, a, r1) \<in> set (M q l) \<and> a' = a"
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
    "(q, b1, g1, a, r1) \<in> set (all_actions_from_vec M pairs ! a')" "a' < num_actions"
    "(q, l) \<in> set pairs" "distinct (map fst pairs)"
  shows
    "(b1, g1, a, r1) \<in> set (M q l) \<and> a' = a"
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
    "(p, b, g, a', f, r, l') \<in> set (IN ! a')"
    if "(L ! p, b, g, In a', f, r, l') \<in> Simple_Network_Language.trans (N p)"
      "p < n_ps" "a' < num_actions"
    for p b g a' f r l'
  proof -
    from trans_mapI[OF that(1,2)] have "(b, g, In a', f, r, l') \<in> set (trans_map p (L ! p))"
      by auto
    then have "(b, g, a', f, r, l') \<in> set (trans_in_map p (L ! p))"
      unfolding trans_in_map_def set_map_filter by (auto 4 7)
    with \<open>p < _\<close> \<open>a' < _\<close> show ?thesis
      unfolding IN_def by (intro in_all_actions_by_stateI)
  qed
  have OUT_I:
    "(p, b, g, a', f, r, l') \<in> set (OUT ! a')"
    if "(L ! p, b, g, Out a', f, r, l') \<in> Simple_Network_Language.trans (N p)"
      "p < n_ps" "a' < num_actions"
    for p b g a' f r l'
  proof -
    from trans_mapI[OF that(1,2)] have "(b, g, Out a', f, r, l') \<in> set (trans_map p (L ! p))"
      by auto
    then have "(b, g, a', f, r, l') \<in> set (trans_out_map p (L ! p))"
      unfolding trans_out_map_def set_map_filter by (auto 4 7)
    with \<open>p < _\<close> \<open>a' < _\<close> show ?thesis
      unfolding OUT_def by (intro in_all_actions_by_stateI)
  qed
  have IN_D:
    "(L ! p, b, g, In a', f, r, l') \<in> Simple_Network_Language.trans (N p) \<and> p < n_ps \<and> a' = a1"
    if "(p, b, g, a', f, r, l') \<in> set (IN ! a1)" "a1 < num_actions"
    for p b g a' f r l' a1
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
    "(L ! p, b, g, Out a1, f, r, l') \<in> Simple_Network_Language.trans (N p) \<and> p < n_ps"
    if "(p, b, g, a', f, r, l') \<in> set (OUT ! a1)" "a1 < num_actions"
    for p b g a' f r l' a1
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
    if "(p, b, g, a', f, r, l') \<in> set (IN ! a1)" "a1 < num_actions"
    for p b g a' f r l' a1
    using that unfolding IN_def by (auto dest: in_all_actions_by_stateD split: option.split_asm)
  have OUT_p_num:
    "p < n_ps"
    if "(p, b, g, a', f, r, l') \<in> set (OUT ! a1)" "a1 < num_actions"
    for p b g a' f r l' a1
    using that unfolding OUT_def by (auto dest: in_all_actions_by_stateD split: option.split_asm)
  have actions_unique:
    "a' = a1"
    if "(p, b, g, a', f, r, l') \<in> set (IN ! a1)" "a1 < num_actions"
    for p b g a' f r l' a1
    using that unfolding IN_def trans_in_map_def set_map_filter
    by (auto dest: in_all_actions_by_stateD split: option.split_asm)
  note [forward3] = OUT_I IN_I
  note [forward2] = action_setD IN_D OUT_D
  show "(((L, s), g, a, r, L', s') \<in> trans_bin) =
        ((g, a, r, L', s') \<in> set (bin_trans_from (L, s)))"
  proof (cases "get_commited L = []")
    case True
    with get_commited_empty_iff[of L] have "\<forall>p<n_ps. L ! p \<notin> commited (N p)"
      by simp
    then have *: "((L, s), g, a, r, L', s') \<in> trans_bin \<longleftrightarrow> ((L, s), g, a, r, L', s') \<in>
      {((L, s), g1 @ g2, Bin a, r1 @ r2, (L', s'')) |
        L s L' s' s'' a p q l1 b1 g1 f1 r1 l1' l2 b2 g2 f2 r2 l2'.
        a \<notin> local.broadcast \<and>
        (l1, b1, g1, In a,  f1, r1, l1') \<in> trans (N p) \<and>
        (l2, b2, g2, Out a, f2, r2, l2') \<in> trans (N q) \<and>
        L!p = l1 \<and> L!q = l2 \<and> p < length L \<and> q < length L \<and> p \<noteq> q \<and>
        check_bexp s b1 True \<and> check_bexp s b2 True \<and>
        L' = L[p := l1', q := l2'] \<and> is_upd s f1 s' \<and> is_upd s' f2 s''
        \<and> L \<in> states \<and> bounded bounds s \<and> bounded bounds s''
      }
    "
      unfolding trans_bin_def by blast
    from True have **:
      "bin_trans_from (L, s)
      = concat (map (\<lambda>a. pairs_by_action L s (OUT ! a) (IN ! a)) bin_actions)"
      unfolding bin_trans_from_def IN_def OUT_def by simp
    from \<open>dom s = _\<close> \<open>L \<in> _\<close> show ?thesis
      unfolding * **
      apply clarsimp
      unfolding pairs_by_action_def
      apply (clarsimp simp: set_map_filter Let_def)
      apply safe
      subgoal for _ s'' _ a' p q l1 b1 g1 f1 r1 l1' l2 b2 g2 f2 r2 l2'
        apply clarsimp
        apply (inst_existentials a')
        subgoal
          apply frules
          apply simp
          apply frules_all
          unfolding check_bounded_iff by (intros; solve_triv)
        subgoal
          by (simp add: mem_bin_actions_iff; frules; simp)
        done
      subgoal
        unfolding mem_bin_actions_iff
        apply simp
        apply (erule conjE)
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
        L s L' s' s'' a p q l1 b1 g1 f1 r1 l1' l2 b2 g2 f2 r2 l2'.
        a \<notin> local.broadcast \<and>
        (l1, b1, g1, In a,  f1, r1, l1') \<in> trans (N p) \<and>
        (l2, b2, g2, Out a, f2, r2, l2') \<in> trans (N q) \<and>
        (l1 \<in> commited (N p) \<or> l2 \<in> commited (N q)) \<and>
        L!p = l1 \<and> L!q = l2 \<and> p < length L \<and> q < length L \<and> p \<noteq> q \<and>
        check_bexp s b1 True \<and> check_bexp s b2 True \<and>
        L' = L[p := l1', q := l2'] \<and> is_upd s f1 s' \<and> is_upd s' f2 s'' \<and>
        L \<in> states \<and> bounded bounds s \<and> bounded bounds s''
      }"
      unfolding trans_bin_def
      by - (rule iffI; elims add: CollectE; intros add: CollectI; blast)
    let ?S1 =
      "{((L, s), g1 @ g2, Bin a, r1 @ r2, (L', s'')) |
        L s L' s' s'' a p q l1 b1 g1 f1 r1 l1' l2 b2 g2 f2 r2 l2'.
          a \<notin> local.broadcast \<and>
          (l1, b1, g1, In a,  f1, r1, l1') \<in> trans (N p) \<and>
          (l2, b2, g2, Out a, f2, r2, l2') \<in> trans (N q) \<and>
          l1 \<in> commited (N p) \<and>
          L!p = l1 \<and> L!q = l2 \<and> p < length L \<and> q < length L \<and> p \<noteq> q \<and>
          check_bexp s b1 True \<and> check_bexp s b2 True \<and>
          L' = L[p := l1', q := l2'] \<and> is_upd s f1 s' \<and> is_upd s' f2 s'' \<and>
          L \<in> states \<and> bounded bounds s \<and> bounded bounds s''
      }"
    let ?S2 =
      "{((L, s), g1 @ g2, Bin a, r1 @ r2, (L', s'')) |
        L s L' s' s'' a p q l1 b1 g1 f1 r1 l1' l2 b2 g2 f2 r2 l2'.
          a \<notin> local.broadcast \<and>
          (l1, b1, g1, In a,  f1, r1, l1') \<in> trans (N p) \<and>
          (l2, b2, g2, Out a, f2, r2, l2') \<in> trans (N q) \<and>
          l2 \<in> commited (N q) \<and>
          L!p = l1 \<and> L!q = l2 \<and>
          p < length L \<and> q < length L \<and> p \<noteq> q \<and>
          check_bexp s b1 True \<and> check_bexp s b2 True \<and>
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
      "(p, b, g, a', f, r, l') \<in> set (In2 ! a')"
      if "(L ! p, b, g, In a', f, r, l') \<in> Simple_Network_Language.trans (N p)"
        "p < n_ps" "a' < num_actions" "L ! p \<in> commited (N p)"
      for p b g a' f r l'
    proof -
      from \<open>L ! p \<in> commited (N p)\<close> \<open>p < n_ps\<close> have "(p, L ! p) \<in> set pairs"
        unfolding pairs_def get_commited_mem_iff by blast
      from trans_mapI[OF that(1,2)] have "(b, g, In a', f, r, l') \<in> set (trans_map p (L ! p))"
        by auto
      then have "(b, g, a', f, r, l') \<in> set (trans_in_map p (L ! p))"
        unfolding trans_in_map_def set_map_filter by (auto 4 7)
      with \<open>p < _\<close> \<open>a' < _\<close> \<open>_ \<in> set pairs\<close> show ?thesis
        unfolding In2_def by (intro in_all_actions_from_vecI)
    qed
    have Out2_I:
      "(p, b, g, a', f, r, l') \<in> set (Out2 ! a')"
      if "(L ! p, b, g, Out a', f, r, l') \<in> Simple_Network_Language.trans (N p)"
        "p < n_ps" "a' < num_actions" "L ! p \<in> commited (N p)"
      for p b g a' f r l'
    proof -
      from \<open>L ! p \<in> commited (N p)\<close> \<open>p < n_ps\<close> have "(p, L ! p) \<in> set pairs"
        unfolding pairs_def get_commited_mem_iff by blast
      from trans_mapI[OF that(1,2)] have "(b, g, Out a', f, r, l') \<in> set (trans_map p (L ! p))"
        by auto
      then have "(b, g, a', f, r, l') \<in> set (trans_out_map p (L ! p))"
        unfolding trans_out_map_def set_map_filter by (auto 4 7)
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
      "(L ! p, b, g, In a', f, r, l') \<in> Simple_Network_Language.trans (N p) \<and>
      p < n_ps \<and> a' = a1 \<and> L ! p \<in> commited (N p)"
      if "(p, b, g, a', f, r, l') \<in> set (In2 ! a1)" "a1 < num_actions"
      for p b g a' f r l' a1
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
      "(L ! p, b, g, Out a', f, r, l') \<in> Simple_Network_Language.trans (N p)
      \<and> p < n_ps \<and> a' = a1 \<and> L ! p \<in> commited (N p)"
      if "(p, b, g, a', f, r, l') \<in> set (Out2 ! a1)" "a1 < num_actions"
      for p b g a' f r l' a1
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
        concat (map (\<lambda>a. pairs_by_action L s (OUT ! a) (In2 ! a)) bin_actions)
      @ concat (map (\<lambda>a. pairs_by_action L s (Out2 ! a) (IN ! a)) bin_actions)"
      unfolding bin_trans_from_def IN_def OUT_def In2_def Out2_def pairs_def
      by (simp add: Let_def)
    from \<open>dom s = _\<close> \<open>L \<in> _\<close> have "
      ((L, s), g, a, r, L', s') \<in> ?S1 \<longleftrightarrow> (g, a, r, L', s') \<in>
      set (concat (map (\<lambda>a. pairs_by_action L s (OUT ! a) (In2 ! a)) bin_actions))"
      apply clarsimp
      unfolding pairs_by_action_def
      apply (clarsimp simp: set_map_filter Let_def)
      apply safe
      subgoal for _ s'' _ a' p q l1 b1 g1 f1 r1 l1' l2 b2 g2 f2 r2 l2'
        apply clarsimp
        apply (inst_existentials a')
        subgoal
          supply [forward4] = In2_I
          apply frules_all
          apply simp
          apply frules_all
          unfolding check_bounded_iff by (intros; solve_triv)
        subgoal
          by (simp add: mem_bin_actions_iff; frules; simp)
        done
      subgoal
        supply [forward2] = In2_D OUT_D
        apply simp
        unfolding mem_bin_actions_iff
        apply (erule conjE)
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
      \<in> set (concat (map (\<lambda>a. pairs_by_action L s (Out2 ! a) (IN ! a)) bin_actions))"
      supply [forward2] = Out2_D In2_D
      supply [forward4] = Out2_I
      apply clarsimp
      unfolding pairs_by_action_def
      apply (clarsimp simp: set_map_filter Let_def)
      apply safe
      subgoal for _ s'' _ a' p q l1 b1 g1 f1 r1 l1' l2 b2 g2 f2 r2 l2'
        apply clarsimp
        apply (inst_existentials a')
        subgoal
          apply frules_all
          apply simp
          apply frules_all
          unfolding check_bounded_iff by (intros; solve_triv)
        subgoal
          unfolding mem_bin_actions_iff by frules_all simp
        done
      subgoal
        apply simp
        unfolding mem_bin_actions_iff
        apply (erule conjE)
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

lemma list_all2_fst_aux:
  "map fst xs = ys" if "list_all2 (\<lambda>x y. fst x = y) xs ys"
  using that by (induction) auto

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
  define IN' where "IN' = map (map (filter (\<lambda> (b, _). bval (the o s) b))) IN"
  define OUT' where "OUT' = map (map (filter (\<lambda> (b, _). bval (the o s) b))) OUT"
  have IN_I:
    "(b, g, a', f, r, l') \<in> set (IN ! p ! a')"
    if "(L ! p, b, g, In a', f, r, l') \<in> Simple_Network_Language.trans (N p)"
      "p < n_ps" "a' < num_actions" "a' \<in> set broadcast"
    for p b g a' f r l'
  proof -
    from trans_mapI[OF that(1,2)] \<open>a' \<in> _\<close> have
      "(b, g, a', f, r, l') \<in> set (trans_in_broad_map p (L ! p))"
      unfolding trans_in_broad_map_def set_map_filter by (auto 4 7)
    with \<open>a' < _\<close> have "(b, g, a', f, r, l') \<in> set (trans_in_broad_grouped p (L ! p) ! a')"
      unfolding trans_in_broad_grouped_def by (auto dest: in_actions_by_state'I)
    with \<open>p < _\<close> show ?thesis
      unfolding IN_def by auto
  qed
  have OUT_I:
    "(b, g, a', f, r, l') \<in> set (OUT ! p ! a')"
    if "(L ! p, b, g, Out a', f, r, l') \<in> Simple_Network_Language.trans (N p)"
      "p < n_ps" "a' < num_actions" "a' \<in> set broadcast"
    for p b g a' f r l'
  proof -
    from trans_mapI[OF that(1,2)] \<open>a' \<in> _\<close> have
      "(b, g, a', f, r, l') \<in> set (trans_out_broad_map p (L ! p))"
      unfolding trans_out_broad_map_def set_map_filter by (auto 4 7)
    with \<open>a' < _\<close> have "(b, g, a', f, r, l') \<in> set (trans_out_broad_grouped p (L ! p) ! a')"
      unfolding trans_out_broad_grouped_def by (auto dest: in_actions_by_state'I)
    with \<open>p < _\<close> show ?thesis
      unfolding OUT_def by auto
  qed
  have IN_D:
    "(L ! p, b, g, In a', f, r, l') \<in> Simple_Network_Language.trans (N p)
     \<and> a' = a1 \<and> a1 \<in> set broadcast"
    if "(b, g, a', f, r, l') \<in> set (IN ! p ! a1)" "a1 < num_actions" "p < n_ps"
    for p b g a' f r l' a1
    using that unfolding IN_def trans_in_broad_grouped_def
    apply simp
    apply (drule in_actions_by_state'D)
    unfolding trans_in_broad_map_def set_map_filter
    by (auto split: option.split_asm) (auto split: act.split_asm if_split_asm dest: trans_mapD)
  have [simp]: "length IN = n_ps" "length OUT = n_ps"
    unfolding IN_def OUT_def by simp+
  have [simp]: "length (IN ! p) = num_actions" "length (OUT ! p) = num_actions" if "p < n_ps" for p
    using that by (simp add:
      length_actions_by_state'_preserv trans_in_broad_grouped_def trans_out_broad_grouped_def
      IN_def OUT_def)+
  have OUT_D:
    "(L ! p, b, g, Out a', f, r, l') \<in> Simple_Network_Language.trans (N p)
     \<and> a' = a1 \<and> a1 \<in> set broadcast"
    if "(b, g, a', f, r, l') \<in> set (OUT ! p ! a1)" "a1 < num_actions" "p < n_ps"
    for p b g a' f r l' a1
    using that unfolding OUT_def trans_out_broad_grouped_def
    apply simp
    apply (drule in_actions_by_state'D)
    unfolding trans_out_broad_map_def set_map_filter
    by (auto split: option.split_asm) (auto split: act.split_asm if_split_asm dest: trans_mapD)
  have IN'_I:
    "(b, g, a', f, r, l') \<in> set (IN' ! p ! a')"
    if "(b, g, a', f, r, l') \<in> set (IN ! p ! a')" "p < n_ps" "a' < num_actions"
       "check_bexp s b True" for p b g a' f r l'
    using that \<open>dom s = {0..<n_vs}\<close> unfolding IN'_def
    by (auto dest!: IN_D[THEN conjunct1] elim: check_bexp_bvalI)
  have IN'_D:
    "(L ! p, b, g, In a', f, r, l') \<in> Simple_Network_Language.trans (N p)
     \<and> a' = a1 \<and> a1 \<in> set broadcast \<and> check_bexp s b True"
    if "(b, g, a', f, r, l') \<in> set (IN' ! p ! a1)" "a1 < num_actions" "p < n_ps"
    for p b g a' f r l' a1
    using that \<open>dom s = {0..<n_vs}\<close> unfolding IN'_def by (auto dest!: IN_D elim: check_bexp_bvalD)
  have OUT'_I:
    "(b, g, a', f, r, l') \<in> set (OUT' ! p ! a')"
    if "(b, g, a', f, r, l') \<in> set (OUT ! p ! a')" "p < n_ps" "a' < num_actions"
       "check_bexp s b True" for p b g a' f r l'
    using that \<open>dom s = {0..<n_vs}\<close> unfolding OUT'_def
    by (auto dest!: OUT_D[THEN conjunct1] elim: check_bexp_bvalI)
  have OUT'_D:
    "(L ! p, b, g, Out a', f, r, l') \<in> Simple_Network_Language.trans (N p)
     \<and> a' = a1 \<and> a1 \<in> set broadcast \<and> check_bexp s b True"
    if "(b, g, a', f, r, l') \<in> set (OUT' ! p ! a1)" "a1 < num_actions" "p < n_ps"
    for p b g a' f r l' a1
    using that \<open>dom s = {0..<n_vs}\<close> unfolding OUT'_def by (auto dest!: OUT_D elim: check_bexp_bvalD)
  define make_trans where "make_trans a p \<equiv>
      let
        outs = OUT' ! p ! a
      in if outs = [] then []
      else
        let
          combs = make_combs p a IN';
          outs = map (\<lambda>t. (p, t)) outs;
          combs = (
                  if combs = [] then [[x]. x \<leftarrow> outs]
                  else concat (map (\<lambda>x. map (\<lambda>xs. x # xs) combs) outs));
          init = ([], Broad a, [], (L, s))
        in
        filter (\<lambda> (g, a, r, L, s). check_bounded s) (
          map (\<lambda>comb.
              fold
                (\<lambda>(q, b2, g2, a2, f2, r2, l2) (g1, a, r1, (L, s)).
                  (g1 @ g2, a, r1 @ r2, (L[q := l2], mk_upds s f2))
                )
                comb
                init
          ) combs)" for a p
  {
    fix p ps bs gs a' fs rs ls'
    assume assms:
      "\<forall>p\<in>set ps.
          (L ! p, bs p, gs p, In a', fs p, rs p, ls' p) \<in> trans (N p)"
      "\<forall>q<n_ps. q \<notin> set ps \<and> p \<noteq> q \<longrightarrow>
          (\<forall>b g f r l'. (L ! q, b, g, In a', f, r, l') \<notin> trans (N q) \<or> \<not> check_bexp s b True)"
      "p < n_ps" "set ps \<subseteq> {0..<n_ps}" "p \<notin> set ps" "distinct ps" "sorted ps"
      "a' < num_actions" "a' \<in> set broadcast" "\<forall>p \<in> set ps. check_bexp s (bs p) True"
    define ys where "ys = List.map_filter
        (\<lambda> i.
          if i = p then None
          else if IN' ! i ! a' = [] then None
          else Some (map (\<lambda>t. (i, t)) (IN' ! i ! a'))
        )
        [0..<n_ps]"
    have "filter (\<lambda>i. IN' ! i ! a' \<noteq> [] \<and> i \<noteq> p) [0..<n_ps] = ps"
      apply (rule filter_distinct_eqI)
      subgoal
        using assms(4-) by (simp add: sorted_distinct_subseq_iff)
      subgoal
        using assms(1,3-) by (auto 4 3 dest!: IN_I IN'_I)
      subgoal
        using assms(1,2,4,8-)
        apply -
        apply (rule ccontr)
        apply simp
        apply elims
        apply (drule hd_in_set)
        subgoal for x
          by (cases "hd (IN' ! x ! a')") (fastforce dest!: IN'_D)
        done
      by auto
    then have "length ys = length ps"
      unfolding ys_def map_filter_def by simp
    have non_empty: "ys \<noteq> []" if "ps \<noteq> []"
      using \<open>_ = ps\<close> \<open>ps \<noteq> []\<close> unfolding ys_def map_filter_def by simp
    have make_combsD:
      "map (\<lambda>p. (p, bs p, gs p, a', fs p, rs p, ls' p)) ps \<in> set (make_combs p a' IN')"
      if "ps \<noteq> []"
    proof -
      from assms(1,3-) have
        "\<forall>i<length ps. let p = ps ! i in (p, bs p, gs p, a', fs p, rs p, ls' p) \<in> set (ys ! i)"
        unfolding ys_def Let_def map_filter_def
        apply (simp add: comp_def if_distrib[where f = the])
        apply (subst (2) map_cong)
          apply (rule HOL.refl)
         apply (simp; fail)
        apply (simp add: \<open>_ = ps\<close>)
        by (intros add: image_eqI[OF HOL.refl] IN_I IN'_I; simp add: subset_code(1))
      with non_empty[OF that] show ?thesis
        unfolding make_combs_def ys_def[symmetric] Let_def
        by (auto simp: \<open>length ys = _\<close> product_lists_set intro:list_all2_all_nthI)
    qed
    have make_combs_empty:
      "make_combs p a' IN' = [] \<longleftrightarrow> ps = []"
    proof (cases "ps = []")
      case True
      then show ?thesis
        using \<open>length ys = length ps\<close> unfolding make_combs_def ys_def[symmetric] Let_def by auto
    next
      case False
      then show ?thesis
        using make_combsD by auto
    qed
    note make_combsD make_combs_empty
  } note make_combsD = this(1) and make_combs_empty = this(2)
  have make_combs_emptyD: "filter (\<lambda>i. IN' ! i ! a' \<noteq> [] \<and> i \<noteq> p) [0..<n_ps] = []"
    if "make_combs p a' IN' = []" for xs p a'
    apply (rule filter_distinct_eqI)
    subgoal
      by auto
      subgoal
        by auto
      subgoal
        using that unfolding make_combs_alt_def
        by (auto simp: filter_empty_conv product_lists_empty split: if_split_asm)
      subgoal
        by simp
      done
  have make_combsI:
    "\<exists> ps bs gs fs rs ls'.
      (\<forall>p\<in>set ps.
       (L ! p, bs p, gs p, In a', fs p, rs p, ls' p) \<in> trans (N p)) \<and>
      (\<forall>q<n_ps. q \<notin> set ps \<and> p \<noteq> q \<longrightarrow>
       (\<forall>b g f r l'. (L ! q, b, g, In a', f, r, l') \<notin> trans (N q) \<or> \<not> check_bexp s b True)) \<and>
      set ps \<subseteq> {0..<n_ps} \<and> p \<notin> set ps \<and> distinct ps \<and> sorted ps \<and> ps \<noteq> [] \<and> a' \<in> set broadcast
      \<and> (\<forall>p \<in> set ps. check_bexp s (bs p) True)
      \<and> xs = map (\<lambda> p. (p, bs p, gs p, a', fs p, rs p, ls' p)) ps
      \<and> filter (\<lambda>i. IN' ! i ! a' \<noteq> [] \<and> i \<noteq> p) [0..<n_ps] = ps"
    if "xs \<in> set (make_combs p a' IN')" "p < n_ps" "a' < num_actions"
    for xs p a'
  proof -
    define ps bs gs fs rs ls' where defs:
      "ps  = map fst xs"
      "bs  = (\<lambda>i. case the (map_of xs i) of (b, g, a, f, r, l') \<Rightarrow> b)"
      "gs  = (\<lambda>i. case the (map_of xs i) of (b, g, a, f, r, l') \<Rightarrow> g)"
      "fs  = (\<lambda>i. case the (map_of xs i) of (b, g, a, f, r, l') \<Rightarrow> f)"
      "rs  = (\<lambda>i. case the (map_of xs i) of (b, g, a, f, r, l') \<Rightarrow> r)"
      "ls' = (\<lambda>i. case the (map_of xs i) of (b, g, a, f, r, l') \<Rightarrow> l')"
    have "filter (\<lambda>i. IN' ! i ! a' \<noteq> [] \<and> i \<noteq> p) [0..<n_ps] = ps"
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
    have to_map: "a' = a" "the (map_of xs q) = (b, g, a, r, f, l')"
      if "(q, b, g, a, r, f, l') \<in> set xs" for b q g a r f l'
      using that
       apply -
      subgoal
        using \<open>set ps \<subseteq> _\<close> \<open>a' < _\<close> \<open>xs \<in> _\<close>
        by
          (simp 
            add: make_combs_alt_def product_lists_set \<open>_ = ps\<close> list_all2_map2
            split: if_split_asm
            ) (auto 4 3 dest!: IN'_D list_all2_set1)
      subgoal
        using \<open>distinct ps\<close>
        by (subst (asm) map_of_eq_Some_iff[of xs q, symmetric]) (auto simp: defs)
      done
    from that have *: "\<forall>p\<in>set ps.
       (L ! p, bs p, gs p, In a', fs p, rs p, ls' p) \<in> Simple_Network_Language.trans (N p)"
      unfolding make_combs_alt_def \<open>_ = ps\<close>
      apply (auto simp: set_map_filter product_lists_set split: if_split_asm)
      using \<open>set ps \<subseteq> _\<close> unfolding defs
      by (auto simp: comp_def list_all2_map2 list_all2_same to_map
          elim!: IN'_D[THEN conjunct1, rotated]
          )
    from that have "ps \<noteq> []" "a' \<in> set broadcast"
       apply (auto simp: make_combs_alt_def set_map_filter product_lists_set split: if_split_asm)
      using \<open>_ = ps\<close> \<open>set ps \<subseteq> {0..<n_ps}\<close> by (cases xs; auto dest: IN'_D simp: list_all2_Cons1)+
    with that have "\<forall>q<n_ps. q \<notin> set ps \<and> p \<noteq> q \<longrightarrow>
       (\<forall>b g f r l'. (L ! q, b, g, In a', f, r, l') \<notin> trans (N q) \<or> \<not> check_bexp s b True)"
      unfolding make_combs_alt_def
      by (auto 4 3 dest!: list_all2_set2 IN_I IN'_I
          simp: defs set_map_filter product_lists_set split: if_split_asm)
    have "xs = map (\<lambda> p. (p, bs p, gs p, a', fs p, rs p, ls' p)) ps"
      apply (intro nth_equalityI)
       apply (simp add: defs; fail)
      apply intros
      subgoal for i
        by (cases "xs ! i") (auto 4 4 simp: defs dest: to_map nth_mem)
      done
    have "\<forall>p\<in>set ps. check_bexp s (bs p) True"
    proof
      fix q assume "q \<in> set ps"
      from \<open>xs \<in> _\<close> have "distinct (map fst xs)"
        unfolding make_combs_alt_def
        by (auto simp: product_lists_set list_all2_map2 to_map
                 dest!: list_all2_fst_aux[OF list_all2_mono]
                 split: if_split_asm)
      from \<open>q \<in> set ps\<close> \<open>_ = ps\<close> have "IN' ! q ! a' \<noteq> []" "q \<noteq> p" "q < n_ps"
        by auto
      with that have "the (map_of xs q) \<in> set (IN' ! q ! a')"
        using set_map_of_compr[OF \<open>distinct (map _ _)\<close>] unfolding make_combs_alt_def
        apply (auto simp: set_map_filter product_lists_set split: if_split_asm)
        apply (drule list_all2_set2)
        apply auto
        done
      then obtain a where "(bs q, gs q, a, fs q, rs q, ls' q) \<in> set (IN' ! q ! a')"
        unfolding defs by atomize_elim (auto split!: prod.splits)
      then show "check_bexp s (bs q) True"
        using IN'_D \<open>a' <  _\<close> \<open>set ps \<subseteq> _\<close> \<open>q \<in> set ps\<close> by auto
    qed
    show ?thesis
      by (inst_existentials ps bs gs fs rs ls'; fact)
  qed
  let ?f = "\<lambda>(q, b2, g2, a2, f2, r2, l2) (g1, a, r1, L, s).
                  (g1 @ g2, a, r1 @ r2, L[q := l2], mk_upds s f2)"
  have ***: "
    fold ?f (map (\<lambda>p. (p, bs p, gs p, a', fs p, rs p, ls' p)) ps) (g, a, r, L, s)
    = (g @ concat (map gs ps), a, r @ concat (map rs ps),
        fold (\<lambda>p L. L[p := ls' p]) ps L, fold (\<lambda>p s. mk_upds s (fs p)) ps s)
    " for ps bs gs a' fs rs ls' g a r L s
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
      "L \<in> states" and
      "g = g1 @ concat (map gs ps)" and
      "a = Broad a'" and
      "r = r1 @ concat (map rs ps)" and
      "L' = fold (\<lambda>p L. L[p := ls' p]) ps L[p := l']" and
      "a' \<in> set broadcast" and
      "(L ! p, b1, g1, Out a', f1, r1, l') \<in> trans (N p)" and
      "\<forall>p\<in>set ps. (L ! p, bs p, gs p, In a', fs p, rs p, ls' p) \<in> trans (N p)"
      and
      "\<forall>q<n_ps. q \<notin> set ps \<and> p \<noteq> q
        \<longrightarrow> (\<forall>b g f r l'. (L ! q, b, g, In a', f, r, l') \<notin> trans (N q) \<or> \<not> check_bexp s b True)" and
      "p < n_ps" and
      "set ps \<subseteq> {0..<n_ps}" and
      "p \<notin> set ps" and
      "distinct ps" and
      "sorted ps" and
      "check_bexp s b1 True" and
      "\<forall>p\<in>set ps. check_bexp s (bs p) True" and
      "is_upd s f1 s''" and
      "is_upds s'' (map fs ps) s'" and
      "Simple_Network_Language.bounded bounds s'"
    for a' p b1 g1 bs gs ps r1 rs ls' l' f1 s'' fs
    using that \<open>dom s = {0..<n_vs}\<close>
    unfolding make_trans_def
    apply (clarsimp simp: set_map_filter Let_def split: prod.split)
    supply [forward2] = action_setD
    supply [forward4] = is_upd_dom2 is_upds_dom3 is_updsD[rotated 3] OUT_I OUT'_I
    apply frule2
    apply simp
    apply (rule conjI, rule impI)
    subgoal
      apply (subst (asm) make_combs_empty, (assumption | simp)+)
      apply frules_all
      apply (intro conjI)
        apply (auto; fail)
       apply (intros add: more_intros)
         apply (solve_triv | intros add: more_intros UN_I)+
      subgoal
        unfolding comp_def by (auto elim!: is_upds.cases)
      by (auto elim!: is_upds.cases simp: check_bounded_iff[symmetric])
    apply (rule impI)
    apply (frule make_combsD, simp, assumption+)
    subgoal
      by (subst (asm) make_combs_empty) (assumption | simp)+
    apply frules_all
    apply simp
    apply (intro conjI)
      apply (auto; fail)
     apply (intros add: more_intros)
      apply (solve_triv | intros add: more_intros UN_I)+
     apply (simp add: *** upd_swap; fail)
    unfolding check_bounded_iff[symmetric] .
  have make_transD:
    "\<exists>s'' b ga f ra l' bs gs fs rs ls' ps.
         g = ga @ concat (map gs ps) \<and>
         a = Broad a' \<and>
         r = ra @ concat (map rs ps) \<and>
         L' = fold (\<lambda>p L. L[p := ls' p]) ps L[p := l'] \<and>
         a' \<in> set broadcast \<and>
         (L ! p, b, ga, Out a', f, ra, l') \<in> trans (N p) \<and>
         (\<forall>p\<in>set ps. (L ! p, bs p, gs p, In a', fs p, rs p, ls' p) \<in> trans (N p)) \<and>
         (\<forall>q<n_ps.
             q \<notin> set ps \<and> p \<noteq> q \<longrightarrow>
             (\<forall>b g f r l'. (L ! q, b, g, In a', f, r, l') \<notin> trans (N q) \<or> \<not> check_bexp s b True)) \<and>
         p < n_ps \<and>
         set ps \<subseteq> {0..<n_ps} \<and>
         p \<notin> set ps \<and>
         distinct ps \<and>
         sorted ps \<and>
         check_bexp s b True \<and> (\<forall>p\<in>set ps. check_bexp s (bs p) True) \<and>
         is_upd s f s'' \<and> is_upds s'' (map fs ps) s' \<and>
         bounded bounds s' \<and>
         filter (\<lambda>i. IN' ! i ! a' \<noteq> [] \<and> i \<noteq> p) [0..<n_ps] = ps"
    if
      "L \<in> states" and
      "a' < num_actions" and
      "p < n_ps" and
      "(g, a, r, L', s') \<in> set (make_trans a' p)"
    for a' p
    supply [forward2] = action_setD
    supply [forward3] = is_upds_make_updsI3[rotated] OUT'_D
    supply [forward4] = is_upd_dom2 is_upds_dom3 is_updsD[rotated 3] OUT_I OUT'_I
    using that \<open>dom s = {0..<n_vs}\<close>
    unfolding make_trans_def
    apply mini_ex
    apply (clarsimp simp: set_map_filter Let_def split: prod.split if_split_asm)
    subgoal for b a1 f l'
      apply (inst_existentials
      "b :: (nat, int) bexp"
      "g :: (nat, int) acconstraint list"
      "f :: (nat \<times> (nat, int) exp) list"
      "r :: nat list"
      l'
      "undefined :: nat \<Rightarrow> (nat, int) Simple_Network_Language.bexp"
      "undefined :: nat \<Rightarrow> (nat, int) acconstraint list"
      "undefined :: nat \<Rightarrow> (nat \<times> (nat, int) exp) list"
      "undefined :: nat \<Rightarrow> nat list"
      "undefined :: nat \<Rightarrow> nat"
      "[] :: nat list")
                   apply (auto dest: OUT'_D; fail)+
      subgoal
        by (auto 4 3 simp: filter_empty_conv dest: bspec dest!: make_combs_emptyD OUT'_D IN_I IN'_I)
            apply (auto dest: OUT'_D; fail)+
      subgoal
        apply (inst_existentials s')
        subgoal is_upd
          by (auto intro: is_upd_make_updI2 dest: OUT'_D)
        subgoal
          by simp (rule is_upds.intros)
        subgoal
          by (subst check_bounded_iff) (metis OUT'_D is_upd_dom2 is_upd)+
        subgoal
          by (rule make_combs_emptyD)
        done
      done
    subgoal for b1 g1 a1 r1 f1 l1' xs
      apply (drule make_combsI, assumption+)
      apply frules
      apply elims
      apply dedup_prems
      apply frules_all
      apply (simp add: *** )
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
      (\<exists>s'' aa p b ga f ra l' bs gs fs rs ls' ps.
          g = ga @ concat (map gs ps) \<and>
          a = Broad aa \<and>
          r = ra @ concat (map rs ps) \<and>
          L' = fold (\<lambda>p L. L[p := ls' p]) ps L[p := l'] \<and>
          aa \<in> set broadcast \<and>
          (L ! p, b, ga, Out aa, f, ra, l') \<in> Simple_Network_Language.trans (N p) \<and>
          (\<forall>p\<in>set ps.
              (L ! p, bs p, gs p, In aa, fs p, rs p, ls' p)
              \<in> Simple_Network_Language.trans (N p)) \<and>
          (\<forall>q<n_ps.
              q \<notin> set ps \<and> p \<noteq> q \<longrightarrow>
              (\<forall>b g f r l'.
                  (L ! q, b, g, In aa, f, r, l') \<notin> trans (N q) \<or> \<not> check_bexp s b True)) \<and>
          p < n_ps \<and>
          set ps \<subseteq> {0..<n_ps} \<and>
          p \<notin> set ps \<and>
          distinct ps \<and>
          sorted ps \<and>
          check_bexp s b True \<and> (\<forall>p\<in>set ps. check_bexp s (bs p) True) \<and>
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
        apply blast+
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
        L s L' s' s'' a p l b g f r l' bs gs fs rs ls' ps.
        a \<in> set broadcast \<and>
        (l, b, g, Out a, f, r, l') \<in> trans (N p) \<and>
        (\<forall>p \<in> set ps. (L ! p, bs p, gs p, In a, fs p, rs p, ls' p) \<in> trans (N p)) \<and>
        (\<forall>q < n_ps. q \<notin> set ps \<and> p \<noteq> q \<longrightarrow>
          \<not> (\<exists>b g f r l'. (L ! q, b, g, In a, f, r, l') \<in> trans (N q) \<and> check_bexp s b True)) \<and>
        L!p = l \<and>
        p < length L \<and> set ps \<subseteq> {0..<n_ps} \<and> p \<notin> set ps \<and> distinct ps \<and> sorted ps \<and>
        check_bexp s b True \<and> (\<forall>p \<in> set ps. check_bexp s (bs p) True) \<and>
        L' = fold (\<lambda>p L . L[p := ls' p]) ps L[p := l'] \<and>
        is_upd s f s' \<and> is_upds s' (map fs ps) s'' \<and>
        L \<in> states \<and> bounded bounds s \<and> bounded bounds s''
      }
    "
      unfolding trans_broad_def broadcast_def[simplified]
      by (intro iffI; elims add: CollectE; intros add: CollectI) blast+
    from True have **:
      "broad_trans_from (L, s)
      =  concat (
           map (\<lambda>a.
             concat (map (\<lambda>p. make_trans a p) [0..<n_ps])
           )
           [0..<num_actions]
         )"
      unfolding broad_trans_from_alt_def IN_def OUT_def IN'_def OUT'_def Let_def make_trans_def
      by simp
    from \<open>dom s = _\<close> \<open>L \<in> _\<close> \<open>bounded bounds s\<close> show ?thesis
      unfolding * **
      apply simp
      apply (subst make_trans_iff[symmetric])
        apply simp+
      apply (intro iffI; elims; intros)
                          apply (solve_triv | blast)+
      done
  next
    case False
    with get_commited_empty_iff[of L] have "\<not> (\<forall>p<n_ps. L ! p \<notin> commited (N p))"
      by simp
    then have *: "((L, s), g, a, r, L', s') \<in> trans_broad \<longleftrightarrow> ((L, s), g, a, r, L', s') \<in>
      {((L, s), g @ concat (map gs ps), Broad a, r @ concat (map rs ps), (L', s'')) |
        L s L' s' s'' a p l b g f r l' bs gs fs rs ls' ps.
        a \<in> set broadcast \<and>
        (l, b, g, Out a, f, r, l') \<in> trans (N p) \<and>
        (\<forall>p \<in> set ps. (L ! p, bs p, gs p, In a, fs p, rs p, ls' p) \<in> trans (N p)) \<and>
        (l \<in> commited (N p) \<or> (\<exists>p \<in> set ps. L ! p \<in> commited (N p))) \<and>
        (\<forall>q < n_ps. q \<notin> set ps \<and> p \<noteq> q \<longrightarrow>
          \<not> (\<exists>b g f r l'. (L ! q, b, g, In a, f, r, l') \<in> trans (N q) \<and> check_bexp s b True)) \<and>
        L!p = l \<and>
        p < length L \<and> set ps \<subseteq> {0..<n_ps} \<and> p \<notin> set ps \<and> distinct ps \<and> sorted ps \<and>
        check_bexp s b True \<and> (\<forall>p \<in> set ps. check_bexp s (bs p) True) \<and>
        L' = fold (\<lambda>p L . L[p := ls' p]) ps L[p := l'] \<and> is_upd s f s' \<and> is_upds s' (map fs ps) s'' \<and>
        L \<in> states \<and> bounded bounds s \<and> bounded bounds s''
      }"
      unfolding trans_broad_def broadcast_def[simplified]
      by (intro iffI; elims add: CollectE; intros add: CollectI) blast+
    have commited_iff: "
      List.map_filter (\<lambda>(p, _). if IN' ! p ! a' = [] then None else Some p) (get_commited L) \<noteq> [p] \<and>
      List.map_filter (\<lambda>(p, _). if IN' ! p ! a' = [] then None else Some p) (get_commited L) \<noteq> []
    \<longleftrightarrow> (\<exists>q<n_ps. IN' ! q ! a' \<noteq> [] \<and> q \<noteq> p \<and> L ! q \<in> commited (N q))"
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
              List.map_filter (\<lambda>(p, _). if IN' ! p ! a \<noteq> [] then Some p else None) (get_commited L)
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
      unfolding broad_trans_from_alt_def IN_def OUT_def IN'_def OUT'_def make_trans_def
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
                            apply (assumption | blast)+
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
          apply (rule disjI1; inst_existentials q; force dest!: IN_I IN'_I)
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
        apply blast+
        done
      done
  qed
qed


paragraph \<open>Refinement of the State Implementation\<close>

definition state_rel :: "(nat \<rightharpoonup> int) \<Rightarrow> int list \<Rightarrow> bool"
  where
  "state_rel s xs \<equiv> length xs = n_vs \<and> dom s = {0..<n_vs} \<and> (\<forall>i < n_vs. xs ! i = the (s i))"

definition loc_rel where
  "loc_rel \<equiv> {((L', s'), (L, s)) | L s L' s'. L' = L \<and> length L = n_ps \<and> state_rel s s'}"

lemma state_rel_left_unique:
  "l \<in> states' \<Longrightarrow> (li, l) \<in> loc_rel \<Longrightarrow> (li', l) \<in> loc_rel \<Longrightarrow> li' = li"
  unfolding loc_rel_def state_rel_def by (auto intro: nth_equalityI)

lemma state_rel_right_unique:
  "l \<in> states' \<Longrightarrow> l' \<in> states' \<Longrightarrow> (li, l) \<in> loc_rel \<Longrightarrow> (li, l') \<in> loc_rel \<Longrightarrow> l' = l"
  unfolding loc_rel_def state_rel_def
  apply clarsimp
  apply (rule ext)
  subgoal premises prems for L s s'1 s'2 x
  proof -
    show "s'1 x = s x"
    proof (cases "x < n_vs")
      case True
      then have "x \<in> dom s'1" "x \<in> dom s"
        using prems by auto
      with \<open>x < n_vs\<close> show ?thesis
        using prems(9) by auto
    next
      case False
      then have "x \<notin> dom s'1" "x \<notin> dom s"
        using prems by auto
      then show ?thesis
        by (auto simp: dom_def)
    qed
  qed
  done

end (* Anonymous context for simp setup *)

end (* Simple Network Impl nat *)

fun bvali :: "_ \<Rightarrow> (nat, 'b :: linorder) bexp \<Rightarrow> bool" where
  "bvali s bexp.true = True" |
  "bvali s (not e) \<longleftrightarrow> \<not> bvali s e" |
  "bvali s (and e1 e2) \<longleftrightarrow> bvali s e1 \<and> bvali s e2" |
  "bvali s (bexp.or e1 e2) \<longleftrightarrow> bvali s e1 \<or> bvali s e2" |
  "bvali s (imply e1 e2) \<longleftrightarrow> bvali s e1 \<longrightarrow> bvali s e2" |
  "bvali s (eq i x) \<longleftrightarrow> s ! i = x" |
  "bvali s (le i x) \<longleftrightarrow> s ! i \<le> x" |
  "bvali s (lt i x) \<longleftrightarrow> s ! i < x" |
  "bvali s (ge i x) \<longleftrightarrow> s ! i \<ge> x" |
  "bvali s (gt i x) \<longleftrightarrow> s ! i > x"

fun evali where
  "evali s (const c) = c"
| "evali s (var x)   = s ! x"
| "evali s (if_then_else b e1 e2) = (if bvali s b then evali s e1 else evali s e2)"
| "evali s (binop f e1 e2) = f (evali s e1) (evali s e2)"
| "evali s (unop f e) = f (evali s e)"

definition mk_updsi ::
  "int list \<Rightarrow> (nat \<times> (nat, int) exp) list \<Rightarrow> int list" where
  "mk_updsi s upds = fold (\<lambda>(x, upd) s'. s'[x := evali s upd]) upds s"

context Simple_Network_Impl_nat_defs
begin

definition
  "check_boundedi s =
    (\<forall>x < length s. fst (bounds_map x) \<le> s ! x \<and> s ! x \<le> snd (bounds_map x))"

definition
  "int_trans_from_loc_impl p l L s \<equiv>
    let trans = trans_i_map p l
    in
    List.map_filter (\<lambda> (b, g, a, f, r, l').
      let s' = mk_updsi s f in
        if bvali s b \<and> check_boundedi s' then Some (g, Internal a, r, (L[p := l'], s'))
        else None
    ) trans"

definition
  "int_trans_from_vec_impl pairs L s \<equiv>
    concat (map (\<lambda>(p, l). int_trans_from_loc_impl p l L s) pairs)"

definition
  "int_trans_from_all_impl L s \<equiv>
    concat (map (\<lambda>p. int_trans_from_loc_impl p (L ! p) L s) [0..<n_ps])"

definition
  "int_trans_impl \<equiv> \<lambda> (L, s).
    let pairs = get_commited L in
    if pairs = []
    then int_trans_from_all_impl L s
    else int_trans_from_vec_impl pairs L s
  "

definition
  "pairs_by_action_impl L s OUT IN \<equiv>
  concat (
    map (\<lambda> (p, b1, g1, a1, f1, r1, l1).
      List.map_filter (\<lambda> (q, b2, g2, a2, f2, r2, l2).
        if p = q then None else
          let s' = mk_updsi (mk_updsi s f1) f2 in
          if bvali s b1 \<and> bvali s b2 \<and> check_boundedi s'
          then Some (g1 @ g2, Bin a1, r1 @ r2, (L[p := l1, q := l2], s'))
          else None
    ) OUT) IN)
  "

definition
  "bin_trans_from_impl \<equiv> \<lambda>(L, s).
    let
      pairs = get_commited L;
      In =  all_actions_by_state trans_in_map L;
      Out = all_actions_by_state trans_out_map L
    in
    if pairs = [] then
      concat (map (\<lambda>a. pairs_by_action_impl L s (Out ! a) (In ! a)) bin_actions)
    else
      let
        In2  = all_actions_from_vec trans_in_map pairs;
        Out2 = all_actions_from_vec trans_out_map pairs
      in
        concat (map (\<lambda>a. pairs_by_action_impl L s (Out ! a) (In2 ! a)) bin_actions)
      @ concat (map (\<lambda>a. pairs_by_action_impl L s (Out2 ! a) (In ! a)) bin_actions)
    "

definition
  "compute_upds init \<equiv> List.map_filter (\<lambda>comb.
  let (g, a, r, L', s) =
    fold
      (\<lambda>(q, b2, g2, a2, f2, r2, l2) (g1, a, r1, (L, s)).
        (g1 @ g2, a, r1 @ r2, (L[q := l2], mk_upds s f2))
      )
      comb
      init
  in if check_bounded s then Some (g, a, r, L', s) else None
)"

definition
  "compute_upds_impl init \<equiv> List.map_filter (\<lambda>comb.
  let (g, a, r, L', s) =
    fold
      (\<lambda>(q, b2, g2, a2, f2, r2, l2) (g1, a, r1, (L, s)).
        (g1 @ g2, a, r1 @ r2, (L[q := l2], mk_updsi s f2))
      )
      comb
      init
  in if check_boundedi s then Some (g, a, r, L', s) else None
)"

definition trans_from where
  "trans_from st = int_trans_from st @ bin_trans_from st @ broad_trans_from st"

definition
  "broad_trans_from_impl \<equiv> \<lambda>(L, s).
    let
      pairs = get_commited L;
      In  = map (\<lambda>p. trans_in_broad_grouped p (L ! p)) [0..<n_ps];
      Out = map (\<lambda>p. trans_out_broad_grouped p (L ! p)) [0..<n_ps];
      In  = map (map (filter (\<lambda>(b, _). bvali s b))) In;
      Out = map (map (filter (\<lambda>(b, _). bvali s b))) Out
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
                combs = (
                  if combs = [] then [[x]. x \<leftarrow> outs]
                  else concat (map (\<lambda>x. map (\<lambda>xs. x # xs) combs) outs));
                init = ([], Broad a, [], (L, s))
              in
                compute_upds_impl init combs
          )
          [0..<n_ps])
        )
      [0..<num_actions])
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
                combs = (
                  if combs = [] then [[x]. x \<leftarrow> outs]
                  else concat (map (\<lambda>x. map (\<lambda>xs. x # xs) combs) outs));
                init = ([], Broad a, [], (L, s))
              in
                compute_upds_impl init combs
          )
          [0..<n_ps])
        )
      [0..<num_actions])
    "

definition trans_impl where
  "trans_impl st = int_trans_impl st @ bin_trans_from_impl st @ broad_trans_from_impl st"

end (* Simple Network Impl nat defs *)


context Simple_Network_Impl_nat
begin

lemma bval_bvali:
  "bval (the o s) e = bvali si e" if "state_rel s si" "\<forall>x \<in> vars_of_bexp e. x \<in> dom s"
  using that by (induction e) (auto simp: state_rel_def)

lemma eval_evali:
  "eval (the o s) e = evali si e" if "state_rel s si" "\<forall>x \<in> vars_of_exp e. x \<in> dom s"
  using that by (induction e) (auto simp: state_rel_def bval_bvali)

lemma mk_upds_mk_updsi:
  "state_rel (mk_upds s upds) (mk_updsi si upds)"
  if assms: "state_rel s si" "\<forall> (_, e) \<in> set upds. \<forall>x \<in> vars_of_exp e. x < n_vs"
    "\<forall> (x, e) \<in> set upds. x < n_vs"
proof -
  have upd_stepI: "state_rel (s'(x \<mapsto> eval (the o s) e)) (si'[x := evali si e])"
    if "state_rel s' si'" "\<forall>x \<in> vars_of_exp e. x < n_vs" "x < n_vs"
    for s' si' x e
    using that assms unfolding state_rel_def by (auto simp: state_rel_def eval_evali)
  have "state_rel
        (fold (\<lambda>(x, upd) s'. s'(x \<mapsto> eval (the o s) upd)) upds s')
        (fold (\<lambda>(x, upd) s'. s'[x := evali si upd]) upds si')"
    if "state_rel s' si'" for s' si'
    using assms that
  proof (induction upds arbitrary: s' si')
    case Nil
    then show ?case
      by simp
  next
    case (Cons upd upds)
    obtain x e where "upd = (x, e)"
      by (cases upd) auto
    from Cons.prems have "state_rel (s'(x \<mapsto> eval (the o s) e)) (si'[x := evali si e])"
      unfolding \<open>upd = _\<close> by (intro upd_stepI) auto
    from Cons.IH[OF _ _ _ this] Cons.prems show ?case
      unfolding \<open>upd = _\<close> by (auto simp: fun_upd_def comp_def)
  qed
  from this[OF \<open>state_rel s si\<close>] show ?thesis
    unfolding mk_upds_def mk_updsi_def .
qed

lemma check_bounded_check_boundedi:
  "check_bounded s = check_boundedi si" if "state_rel s si"
  using that unfolding check_bounded_def check_boundedi_def state_rel_def by auto

definition
  "valid_upd \<equiv> \<lambda>(x, e). x < n_vs \<and> (\<forall>x \<in> vars_of_exp e. x < n_vs)"

definition
  "valid_check b \<equiv> (\<forall>x \<in> vars_of_bexp b. x < n_vs)"

context includes lifting_syntax begin
notation rel_prod (infixr "\<times>\<^sub>R" 56)

(* XXX Move *)
definition is_at_least_equality where
  "is_at_least_equality R \<equiv> \<forall>x y. R x y \<longrightarrow> x = y" for R

named_theorems is_at_least_equality

lemma [is_at_least_equality]:
  "is_at_least_equality (=)"
  by (simp add: is_at_least_equality_def)

lemma [is_at_least_equality]:
  "is_at_least_equality R" if "is_equality R" for R
  using that by (simp add: is_at_least_equality_def is_equality_def)

lemma [is_at_least_equality]:
  "is_at_least_equality (eq_onp P)"
  by (simp add: is_at_least_equality_def eq_onp_def)

lemma is_at_least_equality_list_all2[is_at_least_equality]:
  "is_at_least_equality (list_all2 R)" if "is_at_least_equality R" for R
  using that unfolding is_at_least_equality_def
  by (auto simp: list.rel_eq dest: list_all2_mono[where Q = "(=)"])

lemma is_at_least_equality_rel_prod[is_at_least_equality]:
  "is_at_least_equality (R1 \<times>\<^sub>R R2)"
  if "is_at_least_equality R1" "is_at_least_equality R2" for R1 R2
  using that unfolding is_at_least_equality_def by auto

lemma is_at_least_equality_cong1:
  "(S1 ===> (=)) f f" if "is_at_least_equality S1" "is_at_least_equality S2" for S1 f
  using that unfolding is_at_least_equality_def by (intro rel_funI) auto

lemma is_at_least_equality_cong2:
  "(S1 ===> S2 ===> (=)) f f" if "is_at_least_equality S1" "is_at_least_equality S2" for S1 S2 f
  using that unfolding is_at_least_equality_def by (intro rel_funI) auto

lemma is_at_least_equality_cong3:
  "(S1 ===> S2 ===> S3 ===> (=)) f f"
  if "is_at_least_equality S1" "is_at_least_equality S2" "is_at_least_equality S3" for S1 S2 S3 f
  using that unfolding is_at_least_equality_def by (intro rel_funI) force

lemma is_at_least_equality_Let:
  "(S ===> ((=) ===> R) ===> R) Let Let" if "is_at_least_equality S" for R
  using that unfolding is_at_least_equality_def
  by (intro rel_funI) (erule Let_transfer[THEN rel_funD, THEN rel_funD, rotated], auto)

lemma map_transfer_length:
  fixes R S n
  shows
    "((R ===> S)
      ===> (\<lambda>x y. list_all2 R x y \<and> length x = n)
      ===> (\<lambda>x y. list_all2 S x y \<and> length x = n))
    map map"
  apply (intro rel_funI conjI)
  apply (erule list.map_transfer[THEN rel_funD, THEN rel_funD], erule conjunct1)
  apply simp
  done

lemma upt_0_transfer:
  "(eq_onp (\<lambda>x. x = 0) ===> eq_onp (\<lambda>x. x = n) ===> list_all2 (eq_onp (\<lambda>x. x < n))) upt upt" for n
  apply (intro rel_funI upt_transfer_upper_bound[THEN rel_funD, THEN rel_funD])
   apply (assumption | erule eq_onp_to_eq)+
  done

lemma upt_length_transfer:
  "(eq_onp (\<lambda>x. x = 0) ===> eq_onp (\<lambda>x. x = n)
    ===> (\<lambda> x y. list_all2 (eq_onp (\<lambda>x. x < n)) x y \<and> length x = n)) upt upt" for n
  apply (intro rel_funI conjI upt_0_transfer[THEN rel_funD, THEN rel_funD], assumption+)
  apply (simp add: eq_onp_def)
  done

lemma case_prod_transfer_strong:
  fixes A B C
  assumes "\<And> x y. A1 x y \<Longrightarrow> A x y" "\<And> x y. B1 x y \<Longrightarrow> B x y"
  shows "((A ===> B ===> C) ===> A1 \<times>\<^sub>R B1 ===> C) case_prod case_prod"
  apply (intro rel_funI)
  apply clarsimp
  apply (drule assms)+
  apply (drule (1) rel_funD)+
  apply assumption
  done

lemma concat_transfer_strong:
  fixes A B C
  assumes "\<And>x y. A x y \<Longrightarrow> B x y" "\<And> x y. C x y \<Longrightarrow> list_all2 (list_all2 A) x y"
  shows "(C ===> list_all2 B) concat concat"
  apply (intro rel_funI concat_transfer[THEN rel_funD])
  apply (drule assms)
  apply (erule list_all2_mono)
  apply (erule list_all2_mono)
  apply (erule assms)
  done

lemma map_transfer_strong:
  fixes A B C
  assumes "\<And>xs ys. C xs ys \<Longrightarrow> list_all2 A xs ys"
  shows "((A ===> B) ===> C ===> list_all2 B) map map"
  apply (intro rel_funI)
  apply (erule list.map_transfer[THEN rel_funD, THEN rel_funD])
  apply (erule assms)
  done

lemma list_update_transfer':
  fixes A :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  shows "(list_all2 A ===> eq_onp (\<lambda>i. i<n_ps) ===> A ===> list_all2 A) list_update list_update"
  apply (intro rel_funI)
  apply (rule list_update_transfer[THEN rel_funD, THEN rel_funD, THEN rel_funD])
    apply (auto simp: eq_onp_def)
  done

lemma list_update_transfer'':
  fixes A :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and n
  shows "((\<lambda> x y. list_all2 A x y \<and> length x = n) ===> eq_onp (\<lambda>i. i<n) ===> A
    ===> (\<lambda> x y. list_all2 A x y \<and> length x = n)) list_update list_update"
  apply (intro rel_funI conjI)
  subgoal
    apply (erule conjE)
    apply (rule List.list_update_transfer[THEN rel_funD, THEN rel_funD, THEN rel_funD])
    apply (assumption | elim eq_onp_to_eq)+
    done
  apply simp
  done

lemma list_update_transfer''':
  fixes A :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and n
  shows "((\<lambda> x y. list_all2 A x y \<and> length x = n) ===> (=) ===> A
    ===> (\<lambda> x y. list_all2 A x y \<and> length x = n)) list_update list_update"
  apply (intro rel_funI conjI)
  subgoal
    apply (erule conjE)
    apply (rule List.list_update_transfer[THEN rel_funD, THEN rel_funD, THEN rel_funD])
    apply (assumption | elim eq_onp_to_eq)+
    done
  apply simp
  done

lemma fold_transfer_strong:
  fixes A B
  assumes "\<And>x y. A1 x y \<Longrightarrow> A x y" "\<And>x y. B1 x y \<Longrightarrow> B x y" "\<And>x y. B x y \<Longrightarrow> B2 x y"
    "\<And>x y. B x y \<Longrightarrow> B3 x y"
  shows "((A ===> B2 ===> B1) ===> list_all2 A1 ===> B ===> B3) fold fold"
  apply (intro rel_funI, rule assms)
  apply (rule fold_transfer[THEN rel_funD, THEN rel_funD, THEN rel_funD])
    apply (intro rel_funI)
    apply (drule rel_funD, erule assms)
    apply (drule rel_funD, erule assms, erule assms)
   apply assumption+
  done

lemma bval_bvali_transfer[transfer_rule]:
  "(state_rel ===> eq_onp valid_check ===> (=)) (\<lambda> s. bval (the o s)) bvali"
  by (intro rel_funI) (auto simp: eq_onp_def valid_check_def state_rel_def intro!: bval_bvali)

lemma mk_upds_mk_updsi_transfer[transfer_rule]:
  "(state_rel ===> list_all2 (eq_onp valid_upd) ===> state_rel) mk_upds mk_updsi"
  apply (intro rel_funI)
  subgoal for x y upds upds'
    apply (subgoal_tac "upds' = upds")
     apply auto
     apply (rule mk_upds_mk_updsi)
       apply assumption
    subgoal
      by (smt case_prodI2 case_prod_conv eq_onp_def list_all2_same valid_upd_def)
    subgoal
      by (smt case_prodE case_prod_conv eq_onp_def list_all2_same valid_upd_def)
    subgoal
      by (metis eq_onp_to_eq list.rel_eq_onp)
    done
  done

lemma check_bounded_transfer[transfer_rule]:
  "(state_rel ===> (=)) check_bounded check_boundedi"
  by (simp add: check_bounded_check_boundedi rel_funI)

lemma trans_map_transfer:
  "(eq_onp (\<lambda>i. i<n_ps) ===> (=) ===>
    list_all2 (
      eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (pred_act (\<lambda>x. x < num_actions))
      \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=)
   )) trans_map trans_map"
  apply (intro rel_funI, simp add: eq_onp_def, intro list.rel_refl_strong)
  apply clarsimp
  apply (auto 4 4 dest!: trans_mapD dest: action_setD var_setD var_setD2 intro: list.rel_refl_strong
                  simp: valid_upd_def valid_check_def
        )
  done

lemma trans_map_transfer':
  "(eq_onp (\<lambda>i. i<n_ps) ===> (=) ===>
    list_all2 (eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=))
  ) trans_map trans_map"
  apply (intro rel_funI, simp add: eq_onp_def, intro list.rel_refl_strong)
  apply clarsimp
  apply (intro conjI list.rel_refl_strong)
    apply (auto 4 4 dest: var_setD trans_mapD var_setD2 simp: valid_upd_def valid_check_def)
  done

lemma map_filter_transfer[transfer_rule]:
  "((S ===> rel_option R) ===> list_all2 S ===> list_all2 R) List.map_filter List.map_filter"
  unfolding map_filter_def
  apply (auto intro!: rel_funI)
  subgoal for f g xs ys
  apply (rule list.map_transfer[THEN rel_funD, THEN rel_funD, of "\<lambda> x y. f x \<noteq> None \<and> S x y"])
   apply (rule rel_funI)
  subgoal for a b
    apply (cases "f a")
    apply (auto simp: option_rel_Some1 option_rel_Some2 dest!: rel_funD)
    done
  subgoal
    apply rotate_tac
    apply (induction rule: list_all2_induct)
     apply (auto dest: rel_funD)
    done
  done
  done

lemma trans_i_map_transfer[transfer_rule]:
  "(eq_onp (\<lambda>i. i<n_ps) ===> (=) ===>
    list_all2 (eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=))
   ) trans_i_map trans_i_map"
  supply [transfer_rule] = trans_map_transfer'
  unfolding trans_i_map_def by transfer_prover

lemma int_trans_from_loc_transfer[transfer_rule]:
  "(eq_onp (\<lambda>i. i<n_ps) ===> (=) ===> (\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) ===> state_rel
    ===> list_all2((=) \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R (\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel))
  int_trans_from_loc int_trans_from_loc_impl"
  supply [transfer_rule] = list_update_transfer''
  unfolding int_trans_from_loc_def int_trans_from_loc_impl_def Let_def by transfer_prover

lemma n_ps_transfer:
  "eq_onp (\<lambda>x. x = n_ps) n_ps n_ps"
  by (simp add: eq_onp_def)

lemma zero_nat_transfer:
  "(=) 0 (0::nat)"
  ..

lemma int_trans_from_all_transfer[transfer_rule]:
  "((\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) ===> state_rel
    ===> list_all2((=) \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R (\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel))
  int_trans_from_all int_trans_from_all_impl"
  supply [transfer_rule] = zero_nat_transfer n_ps_transfer
  unfolding int_trans_from_all_def int_trans_from_all_impl_def Let_def
  by transfer_prover

lemma int_trans_from_vec_transfer[transfer_rule]:
  "(list_all2 (eq_onp (\<lambda>x. x < n_ps) \<times>\<^sub>R (=)) ===> (\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps)
    ===> state_rel
    ===> list_all2((=) \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R (\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel))
  int_trans_from_vec int_trans_from_vec_impl"
  unfolding int_trans_from_vec_def int_trans_from_vec_impl_def Let_def
  by transfer_prover

private definition R where "R \<equiv> (\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps)"

lemma get_commited_transfer[transfer_rule]:
  "((\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) ===> list_all2 (eq_onp (\<lambda>x. x < n_ps) \<times>\<^sub>R (=)))
    get_commited get_commited"
proof -
  have [transfer_rule]:
    "R automata automata"
    unfolding R_def by (simp add: n_ps_def list.rel_eq)
  show ?thesis
  supply [transfer_rule] = zero_nat_transfer n_ps_transfer
  unfolding get_commited_def
  unfolding Let_def
  apply transfer_prover_start
  using [[goals_limit=15]]
  prefer 8
  apply transfer_step
                prefer 8
  unfolding R_def
       apply transfer_step+
  apply transfer_prover
  done
qed

lemma eq_transfer:
  "(list_all2 (eq_onp (\<lambda>x. x < n_ps) \<times>\<^sub>R (=)) ===> list_all2 (=) ===> (=)) (=) (=)"
  unfolding eq_onp_def
  apply (intro rel_funI)
  apply (drule list_all2_mono[where Q = "(=)"])
   apply (auto simp add: list.rel_eq rel_prod.simps)
  done

lemma int_trans_from_transfer:
  "((\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel
  ===> list_all2 ((=) \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R ((\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel)))
  int_trans_from int_trans_impl"
  supply [transfer_rule] = eq_transfer
  unfolding int_trans_impl_def int_trans_from_def Let_def
  by transfer_prover

lemma pairs_by_action_transfer[transfer_rule]:
  "((\<lambda>x y. list_all2 (=) x y \<and> length x = n) ===> state_rel ===>
    list_all2 ((=) \<times>\<^sub>R eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=) \<times>\<^sub>R (=))
    ===>
    list_all2 ((=) \<times>\<^sub>R eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=) \<times>\<^sub>R (=))
    ===>
    list_all2 ((=) \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R (\<lambda>x y. list_all2 (=) x y \<and> length x = n) \<times>\<^sub>R state_rel))
   pairs_by_action pairs_by_action_impl"
  supply [transfer_rule] = list_update_transfer'''
  unfolding pairs_by_action_def pairs_by_action_impl_def by transfer_prover

lemmas rel_elims =
  rel_prod.cases
  rel_funD

lemmas rel_intros =
  rel_funI

lemma pairs_by_action_transfer':
  "((\<lambda>x y. list_all2 (=) x y \<and> length x = n) ===> state_rel ===>
    list_all2 (B \<times>\<^sub>R eq_onp valid_check \<times>\<^sub>R C \<times>\<^sub>R D \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R E \<times>\<^sub>R F) ===>
    list_all2 (B \<times>\<^sub>R eq_onp valid_check \<times>\<^sub>R C \<times>\<^sub>R D \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R E \<times>\<^sub>R F) ===>
    list_all2 ((=) \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R (\<lambda>x y. list_all2 (=) x y \<and> length x = n) \<times>\<^sub>R state_rel))
   pairs_by_action pairs_by_action_impl"
  if "\<And>x y. B x y \<Longrightarrow> x = y"
    "\<And>x y. C x y \<Longrightarrow> x = y" "\<And>x y. D x y \<Longrightarrow> x = y"
    "\<And>x y. E x y \<Longrightarrow> x = y" "\<And>x y. F x y \<Longrightarrow> x = y"
  for B C D E F
  apply (intro rel_funI)
  apply (rule pairs_by_action_transfer[THEN rel_funD, THEN rel_funD, THEN rel_funD, THEN rel_funD])
     apply (assumption | erule that list_all2_mono prod.rel_mono_strong)+
  done

lemma trans_in_map_transfer[transfer_rule]:
  "(eq_onp (\<lambda>i. i<n_ps) ===> (=)
    ===> list_all2 (
    eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>a. a < num_actions) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=))
   ) trans_in_map trans_in_map"
  supply [transfer_rule] = trans_map_transfer[folded act.rel_eq_onp]
  unfolding trans_in_map_def by transfer_prover

lemma trans_in_map_transfer[transfer_rule]:
  "(eq_onp (\<lambda>i. i<n_ps) ===> (=)
    ===> list_all2 (eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=))
   ) trans_in_map trans_in_map"
  unfolding trans_in_map_def oops

lemma trans_out_map_transfer[transfer_rule]:
  "(eq_onp (\<lambda>i. i<n_ps) ===> (=)
    ===> list_all2 (
    eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>a. a < num_actions) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=)
   )) trans_out_map trans_out_map"
  supply [transfer_rule] = trans_map_transfer[folded act.rel_eq_onp]
  unfolding trans_out_map_def by transfer_prover

lemma trans_out_map_transfer[transfer_rule]:
  "(eq_onp (\<lambda>i. i<n_ps) ===> (=) ===> list_all2 (
    eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=)))
  trans_out_map trans_out_map"
  unfolding trans_out_map_def oops

lemma actions_by_state_transfer[transfer_rule]:
  "(eq_onp (\<lambda>i. i < n_ps) ===>
    list_all2 ((=) \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>i. i < n) \<times>\<^sub>R (=)) ===>
    (\<lambda> x y. list_all2 (list_all2 (eq_onp (\<lambda>i. i<n_ps) \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>x. x < n) \<times>\<^sub>R (=))) x y \<and> length x = n) ===>
    (\<lambda> x y. list_all2 (list_all2 (eq_onp (\<lambda>i. i<n_ps) \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>x. x < n) \<times>\<^sub>R (=))) x y \<and> length x = n)
  )
  actions_by_state actions_by_state" for n
  supply [transfer_rule] = list_update_transfer''
  unfolding actions_by_state_def by transfer_prover

lemma actions_by_state_transfer'[transfer_rule]:
  "(
    eq_onp (\<lambda>i. i < n_ps) ===>
    list_all2 (eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>i. i < n) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=)) ===>
    (\<lambda> x y. list_all2 (list_all2 (
        eq_onp (\<lambda>i. i<n_ps) \<times>\<^sub>R eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>x. x < n)
        \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=))) x y \<and> length x = n) ===>
    (\<lambda> x y. list_all2 (list_all2 (
        eq_onp (\<lambda>i. i<n_ps) \<times>\<^sub>R eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>x. x < n)
        \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=))) x y \<and> length x = n)
  )
  actions_by_state actions_by_state"
  for n
  supply [transfer_rule] = list_update_transfer''
  unfolding actions_by_state_def by transfer_prover

lemma transfer_consts:
  "(eq_onp (\<lambda>x. x = num_actions)) num_actions num_actions" "(eq_onp (\<lambda>x. x = 0)) (0::nat) 0"
  "(eq_onp (\<lambda>x. x = n_ps)) n_ps n_ps" 
  by (auto simp: eq_onp_def)

lemma all_actions_by_state_transfer[transfer_rule]:
  "
  (
    (eq_onp (\<lambda>i. i<n_ps) ===> (=) ===> list_all2 (eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>i. i < num_actions) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=)))
    ===>
    (\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps)
    ===>
    (\<lambda> x y. list_all2 (list_all2 (eq_onp (\<lambda>i. i<n_ps) \<times>\<^sub>R eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>i. i<num_actions) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=))) x y \<and> length x = num_actions)
  )
  all_actions_by_state all_actions_by_state"
  supply [transfer_rule] = map_transfer_length upt_0_transfer upt_length_transfer transfer_consts
    n_ps_transfer
  unfolding all_actions_by_state_def by transfer_prover

lemma all_actions_from_vec_transfer[transfer_rule]:
  "
  (
    (eq_onp (\<lambda>i. i<n_ps) ===> (=) ===> list_all2 (eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>i. i < num_actions) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=)))
    ===>
    list_all2 (eq_onp (\<lambda>i. i < n_ps) \<times>\<^sub>R (=))
    ===>
    (\<lambda> x y. list_all2 (list_all2 (eq_onp (\<lambda>i. i<n_ps) \<times>\<^sub>R eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>i. i<num_actions) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=))) x y \<and> length x = num_actions)
  )
  all_actions_from_vec all_actions_from_vec"
  supply [transfer_rule] = map_transfer_length upt_length_transfer transfer_consts
  unfolding all_actions_from_vec_def all_actions_from_vec_def by transfer_prover

lemma bin_actions_transfer[transfer_rule]:
  "(list_all2 (eq_onp (\<lambda>x. x < num_actions))) bin_actions bin_actions"
proof -
  have *: "list_all2 (eq_onp (\<lambda>x. x < num_actions)) [0..<num_actions] [0..<num_actions]"
    by (rule list.rel_refl_strong) (auto simp: eq_onp_def)
  show ?thesis
    unfolding bin_actions_def
    by (rule filter_transfer[THEN rel_funD, THEN rel_funD, OF _ *]) (auto simp: eq_onp_def)
qed

lemma Let_transfer_bin_aux:
  "((\<lambda>x y. list_all2 (list_all2
    (eq_onp (\<lambda>i. i < n_ps) \<times>\<^sub>R eq_onp valid_check \<times>\<^sub>R list_all2 (rel_acconstraint (=) (=)) \<times>\<^sub>R
         eq_onp (\<lambda>i. i < num_actions) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R list_all2 (=) \<times>\<^sub>R (=))) x y
    \<and> length x = num_actions) ===>
   ((\<lambda>x y. list_all2 (list_all2
    ((=) \<times>\<^sub>R eq_onp valid_check \<times>\<^sub>R list_all2 (rel_acconstraint (=) (=)) \<times>\<^sub>R
         (=) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R list_all2 (=) \<times>\<^sub>R (=))) x y
    \<and> length x = num_actions) ===>
   list_all2
    (list_all2 (rel_acconstraint (=) (=)) \<times>\<^sub>R rel_label (=) \<times>\<^sub>R
     list_all2 (=) \<times>\<^sub>R (\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel)) ===>
  list_all2
    (list_all2 (rel_acconstraint (=) (=)) \<times>\<^sub>R rel_label (=) \<times>\<^sub>R
     list_all2 (=) \<times>\<^sub>R (\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel))
  Let Let"
  unfolding Let_def
  by (intro rel_funI, drule rel_funD)
     (auto simp: eq_onp_def elim!: list_all2_mono prod.rel_mono_strong)

lemma bin_trans_from_transfer:
  "((\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel
  ===> list_all2 ((=) \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R ((\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel)))
  bin_trans_from bin_trans_from_impl"
  unfolding bin_trans_from_impl_def bin_trans_from_def
  supply [transfer_rule] =
    map_transfer_length upt_length_transfer transfer_consts eq_transfer Let_transfer_bin_aux
  by transfer_prover

(*
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
*)

(*
definition
  "actions_by_state' xs \<equiv>
    fold (\<lambda> t acc. acc[fst (snd t) := t # (acc ! fst (snd t))]) xs (repeat [] num_actions)"
*)

lemma trans_map_transfer'':
  "((=) ===> (=) ===>
  list_all2 (eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (pred_act (\<lambda>x. x < num_actions)) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=)))
  trans_map trans_map"
  apply (intro rel_funI, simp add: eq_onp_def, intro list.rel_refl_strong)
  apply clarsimp
  thm trans_mapD
  apply (auto 4 4 dest!: trans_mapD dest: action_setD var_setD intro: list.rel_refl_strong simp: valid_upd_def)
  oops

lemma compute_upds_transfer:
  "(
  (list_all2 (=) \<times>\<^sub>R (=) \<times>\<^sub>R list_all2 (=) \<times>\<^sub>R (\<lambda>x y. list_all2 (=) x y \<and> length x = n) \<times>\<^sub>R state_rel)
  ===> list_all2 (list_all2
        ((=) \<times>\<^sub>R eq_onp valid_check \<times>\<^sub>R list_all2 (=) \<times>\<^sub>R (=) \<times>\<^sub>R list_all2 (eq_onp valid_upd)
        \<times>\<^sub>R list_all2 (=) \<times>\<^sub>R (=))) ===>
  list_all2 (
    list_all2 (=) \<times>\<^sub>R (=) \<times>\<^sub>R list_all2 (=) \<times>\<^sub>R (\<lambda>x y. list_all2 (=) x y \<and> length x = n) \<times>\<^sub>R state_rel
  )) compute_upds compute_upds_impl"
  supply [transfer_rule] = list_update_transfer'''
  unfolding compute_upds_def compute_upds_impl_def by transfer_prover

lemma in_transfer:
  "(eq_onp (\<lambda>x. x < num_actions) ===> (=) ===> (=)) (\<in>) (\<in>)"
  by (intro rel_funI, rule member_transfer[of "(=)", THEN rel_funD, THEN rel_funD])
     (auto simp: eq_onp_def rel_set_eq intro: bi_unique_eq)

lemma trans_in_broad_map_transfer[transfer_rule]:
  "(eq_onp (\<lambda>i. i<n_ps) ===> (=) ===> list_all2 (eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>x. x < num_actions) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=)))
  trans_in_broad_map trans_in_broad_map"
  supply [transfer_rule] = trans_map_transfer[folded act.rel_eq_onp] in_transfer
  unfolding trans_in_broad_map_def by transfer_prover

lemma trans_out_broad_map_transfer[transfer_rule]:
  "(eq_onp (\<lambda>i. i<n_ps) ===> (=) ===> list_all2 (eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>x. x < num_actions) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=)))
  trans_out_broad_map trans_out_broad_map"
  supply [transfer_rule] = trans_map_transfer[folded act.rel_eq_onp] in_transfer
  unfolding trans_out_broad_map_def by transfer_prover

text \<open>We are using the ``equality version'' of parametricty for @{term "(!)"} here.\<close>
lemma actions_by_state'_transfer[transfer_rule]:
  "(list_all2 (eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>x. x < num_actions) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=))
  ===> (\<lambda> x y. list_all2 (
    list_all2 (eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>x. x < num_actions) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=))) x y
    \<and> length x = num_actions
  ))
  actions_by_state' actions_by_state'"
  supply [transfer_rule] = transfer_consts
    upt_length_transfer
    map_transfer_length
    list_update_transfer''
  unfolding actions_by_state'_def by transfer_prover

lemma trans_in_broad_grouped_transfer[transfer_rule]:
  "(eq_onp (\<lambda>i. i<n_ps) ===> (=)
  ===> (\<lambda> x y. list_all2 (
    list_all2 (eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>x. x < num_actions) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=))) x y
    \<and> length x = num_actions
  )) trans_in_broad_grouped trans_in_broad_grouped"
  unfolding trans_in_broad_grouped_def by transfer_prover

lemma trans_out_broad_grouped_transfer[transfer_rule]:
  "(eq_onp (\<lambda>i. i<n_ps) ===> (=)
  ===> (\<lambda> x y. list_all2 (
    list_all2 (eq_onp valid_check \<times>\<^sub>R (=) \<times>\<^sub>R eq_onp (\<lambda>x. x < num_actions) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R (=))) x y
    \<and> length x = num_actions
  )) trans_out_broad_grouped trans_out_broad_grouped"
  unfolding trans_out_broad_grouped_def by transfer_prover

lemma make_combs_transfer:
  fixes R
  assumes "\<And>x y. R x y \<Longrightarrow> x = y"
  shows
    "(eq_onp (\<lambda>x. x < n_ps)
  ===> eq_onp (\<lambda>x. x < num_actions)
  ===> (\<lambda>x y. list_all2 (\<lambda>x y. list_all2 (list_all2 R) x y \<and> length x = num_actions) x y
        \<and> length x = n_ps)
  ===> list_all2 (list_all2 (eq_onp (\<lambda>x. x < n_ps) \<times>\<^sub>R R)))
  make_combs make_combs"
proof -
  have [transfer_rule]:
    "(eq_onp (\<lambda>x. x < n_ps) ===> eq_onp (\<lambda>x. x < n_ps) ===> (=)) (=) (=)"
    "(list_all2 R ===> list_all2 R ===> (=)) (=) (=)"
    "(list_all2 (list_all2 (eq_onp (\<lambda>x. x < n_ps) \<times>\<^sub>R R))
      ===> list_all2 (list_all2 (eq_onp (\<lambda>x. x < n_ps) \<times>\<^sub>R R)) ===> (=)) (=) (=)"
      apply (auto simp: eq_onp_def)
    subgoal
      by (smt assms list.rel_eq list_all2_mono rel_funI)
    subgoal
      by (smt assms fun.rel_eq list_all2_eq list_all2_mono rel_fun_mono rel_prod.cases)
    done
  show ?thesis
    supply [transfer_rule] = upt_0_transfer transfer_consts
    unfolding make_combs_def by transfer_prover
qed

lemma broad_trans_from_alt_def2:
  "broad_trans_from = (\<lambda>(L, s).
    let
      pairs = get_commited L;
      In  = map (\<lambda>p. trans_in_broad_grouped p (L ! p)) [0..<n_ps];
      Out = map (\<lambda>p. trans_out_broad_grouped p (L ! p)) [0..<n_ps];
      In = map (map (filter (\<lambda>(b, _). bval (the \<circ> s) b))) In;
      Out = map (map (filter (\<lambda>(b, _). bval (the \<circ> s) b))) Out
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
                combs = (
                  if combs = [] then [[x]. x \<leftarrow> outs]
                  else concat (map (\<lambda>x. map (\<lambda>xs. x # xs) combs) outs));
                init = ([], Broad a, [], (L, s))
              in
                compute_upds init combs
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
                combs = (
                  if combs = [] then [[x]. x \<leftarrow> outs]
                  else concat (map (\<lambda>x. map (\<lambda>xs. x # xs) combs) outs));
                init = ([], Broad a, [], (L, s))
              in
                compute_upds init combs
          )
          [0..<n_ps])
        )
      [0..<num_actions])
    )
    "
  unfolding broad_trans_from_def compute_upds_def
  apply (rule HOL.refl)
  done

lemma concat_length_transfer:
  "((\<lambda> x y. list_all2 (list_all2 A) x y \<and> length x = n) ===> list_all2 A) concat concat" for A n
  by (intro rel_funI concat_transfer[THEN rel_funD], elim conjunct1)

lemma broad_trans_from_transfer:
  "((\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel
  ===> list_all2 ((=) \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R ((\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel)))
  broad_trans_from broad_trans_from_impl"
proof -

  have compute_upds_impl_transfer[transfer_rule]: "
    (list_all2 (=) \<times>\<^sub>R
      rel_label (eq_onp (\<lambda>x. x < num_actions)) \<times>\<^sub>R
      list_all2 (=) \<times>\<^sub>R
      (\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel ===>
      list_all2
       (list_all2
         (eq_onp (\<lambda>x. x < n_ps) \<times>\<^sub>R
          eq_onp valid_check \<times>\<^sub>R
          list_all2 (rel_acconstraint (=) (=)) \<times>\<^sub>R
          eq_onp (\<lambda>x. x < num_actions) \<times>\<^sub>R
          list_all2 (eq_onp valid_upd) \<times>\<^sub>R list_all2 (=) \<times>\<^sub>R (=))) ===>
      list_all2
       (list_all2 (=) \<times>\<^sub>R
        (=) \<times>\<^sub>R
        list_all2 (=) \<times>\<^sub>R (\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel))
     compute_upds compute_upds_impl"
    apply (intro rel_funI)
    apply (rule compute_upds_transfer[THEN rel_funD, THEN rel_funD])
     apply (elim rel_prod.cases)
     apply (simp only:)
     apply (intro rel_prod.intros)
         apply assumption
    subgoal
      by (drule label.rel_mono_strong[of _ _ _ "(=)"]; simp add: eq_onp_def label.rel_eq)
       apply (simp; fail)+
    apply (elim list_all2_mono rel_prod.cases)
    apply (simp only:)
    apply (intro rel_prod.intros)
          apply (assumption | simp add: eq_onp_def acconstraint.rel_eq)+
    done

  have [is_at_least_equality]: "is_equality (rel_acconstraint (=) (=))"
    by (tactic \<open>Transfer.eq_tac @{context} 1\<close>)
    (* by (simp add: acconstraint.rel_eq list.rel_eq is_equality_def) *)

  have eq_transfer1:
    "(list_all2
      (eq_onp valid_check \<times>\<^sub>R  list_all2 (rel_acconstraint (=) (=)) \<times>\<^sub>R eq_onp (\<lambda>x. x < num_actions) \<times>\<^sub>R
         list_all2 (eq_onp valid_upd) \<times>\<^sub>R list_all2 (=) \<times>\<^sub>R (=)) ===>
    list_all2
      (eq_onp valid_check \<times>\<^sub>R list_all2 (rel_acconstraint (=) (=)) \<times>\<^sub>R eq_onp (\<lambda>x. x < num_actions) \<times>\<^sub>R
         list_all2 (eq_onp valid_upd) \<times>\<^sub>R list_all2 (=) \<times>\<^sub>R (=))
    ===> (=)) (=) (=)
    "
    by (intro is_at_least_equality_cong2 is_at_least_equality)

  let ?R = "(eq_onp (\<lambda>x. x < n_ps) \<times>\<^sub>R eq_onp valid_check \<times>\<^sub>R
         list_all2 (rel_acconstraint (=) (=)) \<times>\<^sub>R
         eq_onp (\<lambda>x. x < num_actions) \<times>\<^sub>R list_all2 (eq_onp valid_upd) \<times>\<^sub>R list_all2 (=) \<times>\<^sub>R (=))"

  have eq_transfer5:
    "(list_all2 (list_all2 ?R) ===> list_all2 (list_all2 ?R) ===> (=)) (=) (=)"
    by (intro is_at_least_equality_cong2 is_at_least_equality)

  have eq_transfer2:
    "(list_all2 (eq_onp (\<lambda>x. x < n_ps)) ===> list_all2 (eq_onp (\<lambda>x. x < n_ps)) ===> (=)) (=) (=)"
    by (intro is_at_least_equality_cong2 is_at_least_equality)

  have eq_transfer3:
    "(eq_onp (\<lambda>x. x < n_ps) ===> eq_onp (\<lambda>x. x < n_ps) ===> (=)) (=) (=)"
    by (intro is_at_least_equality_cong2 is_at_least_equality)

  have eq_transfer4:
    "(list_all2 (eq_onp (\<lambda>x. x < n_ps) \<times>\<^sub>R (=)) ===>
      list_all2 (eq_onp (\<lambda>x. x < n_ps) \<times>\<^sub>R (=)) ===> (=)) (=) (=)"
    by (intro is_at_least_equality_cong2 is_at_least_equality)

  have make_combs_transfer: "
    (eq_onp (\<lambda>x. x < n_ps) ===>
        eq_onp (\<lambda>x. x < num_actions) ===>
        (\<lambda>x y. list_all2 (\<lambda>x y. list_all2 (list_all2
          (eq_onp valid_check \<times>\<^sub>R list_all2 (rel_acconstraint (=) (=)) \<times>\<^sub>R eq_onp (\<lambda>x. x < num_actions) \<times>\<^sub>R
           list_all2 (eq_onp valid_upd) \<times>\<^sub>R list_all2 (=) \<times>\<^sub>R (=)))
          x y \<and> length x = num_actions) x y \<and> length x = n_ps) ===>
        list_all2 (list_all2 (eq_onp (\<lambda>x. x < n_ps) \<times>\<^sub>R
          eq_onp valid_check \<times>\<^sub>R list_all2 (rel_acconstraint (=) (=)) \<times>\<^sub>R eq_onp (\<lambda>x. x < num_actions) \<times>\<^sub>R
          list_all2 (eq_onp valid_upd) \<times>\<^sub>R list_all2 (=) \<times>\<^sub>R (=))
        )
    ) make_combs make_combs"
    apply (intro rel_funI)
    apply (rule make_combs_transfer[THEN rel_funD, THEN rel_funD, THEN rel_funD])
    subgoal
      apply (simp add: acconstraint.rel_eq list.rel_eq prod.rel_eq)
      apply (drule prod.rel_mono_strong[of _ _ _ _ "(=)" "(=)"], erule eq_onp_to_eq)
       apply (drule prod.rel_mono_strong[of _ _ _ _ "(=)" "(=)"])
         apply assumption
        apply (drule prod.rel_mono_strong[of _ _ _ _ "(=)" "(=)"], erule eq_onp_to_eq)
         apply (drule prod.rel_mono_strong[of _ _ _ _ "(=)" "(=)"])
           apply (drule list_all2_mono[of _ _ _ "(=)"], erule eq_onp_to_eq, simp only: list.rel_eq)
          apply assumption
         apply (drule (2) prod.rel_mono_strong[of _ _ _ _ "(=)" "(=)"];
                simp add: acconstraint.rel_eq list.rel_eq prod.rel_eq)+
      done
      apply (simp add: prod.rel_eq)+
    done
  have "
  ((\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel
    ===> list_all2 (
          (=) \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R ((\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel)))
  (
  \<lambda>(L, s).
      let
        pairs = [];
        In  = map (\<lambda>p. trans_in_broad_grouped p (L ! p)) [0..<n_ps];
        Out = map (\<lambda>p. trans_out_broad_grouped p (L ! p)) [0..<n_ps]
      in
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
                  combs = (
                    if combs = [] then [[x]. x \<leftarrow> outs]
                    else concat (map (\<lambda>x. map (\<lambda>xs. x # xs) combs) outs));
                  init = ([], Broad a, [], (L, s))
                in
                  compute_upds init combs
            )
            [0..<n_ps])
          )
        [0..<num_actions])
  ) (
  \<lambda>(L, s).
      let
        pairs = [];
        In  = map (\<lambda>p. trans_in_broad_grouped p (L ! p)) [0..<n_ps];
        Out = map (\<lambda>p. trans_out_broad_grouped p (L ! p)) [0..<n_ps]
      in
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
                  combs = (
                    if combs = [] then [[x]. x \<leftarrow> outs]
                    else concat (map (\<lambda>x. map (\<lambda>xs. x # xs) combs) outs));
                  init = ([], Broad a, [], (L, s))
                in
                  compute_upds_impl init combs
            )
            [0..<n_ps])
          )
        [0..<num_actions]))
  "
    supply [transfer_rule] =
      transfer_consts
      upt_0_transfer
      map_transfer_length
      upt_length_transfer
      make_combs_transfer
      compute_upds_transfer
      concat_length_transfer
      eq_transfer1
      eq_transfer2
      eq_transfer3
      eq_transfer5
    unfolding Let_def by transfer_prover
  have "
  ((\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel
    ===> list_all2 (
          (=) \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R ((\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel)))
  (
  \<lambda>(L, s).
      let
        pairs = get_commited L;
        In  = map (\<lambda>p. trans_in_broad_grouped p (L ! p)) [0..<n_ps];
        Out = map (\<lambda>p. trans_out_broad_grouped p (L ! p)) [0..<n_ps]
      in
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
                  combs = (
                    if combs = [] then [[x]. x \<leftarrow> outs]
                    else concat (map (\<lambda>x. map (\<lambda>xs. x # xs) combs) outs));
                  init = ([], Broad a, [], (L, s))
                in
                  compute_upds init combs
            )
            [0..<n_ps])
          )
        [0..<num_actions])
  )
  (
  \<lambda>(L, s).
      let
        pairs = get_commited L;
        In  = map (\<lambda>p. trans_in_broad_grouped p (L ! p)) [0..<n_ps];
        Out = map (\<lambda>p. trans_out_broad_grouped p (L ! p)) [0..<n_ps]
      in
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
                  combs = (
                    if combs = [] then [[x]. x \<leftarrow> outs]
                    else concat (map (\<lambda>x. map (\<lambda>xs. x # xs) combs) outs));
                  init = ([], Broad a, [], (L, s))
                in
                  compute_upds_impl init combs
            )
            [0..<n_ps])
          )
        [0..<num_actions])
  )"
    supply [transfer_rule] =
      transfer_consts
      upt_0_transfer
      map_transfer_length
      upt_length_transfer
      make_combs_transfer
      compute_upds_transfer
      concat_length_transfer
      eq_transfer1
      eq_transfer2
      eq_transfer3
      eq_transfer5
    unfolding Let_def by transfer_prover

  show ?thesis
    supply [transfer_rule] =
      transfer_consts
      upt_0_transfer
      map_transfer_length
      upt_length_transfer
      make_combs_transfer
      compute_upds_transfer
      concat_length_transfer
      eq_transfer1
      eq_transfer2
      eq_transfer3
      eq_transfer4
      eq_transfer5
    unfolding broad_trans_from_alt_def2 broad_trans_from_impl_def Let_def by transfer_prover
qed

lemma trans_from_transfer:
  "((\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel
  ===> list_all2 ((=) \<times>\<^sub>R (=) \<times>\<^sub>R (=) \<times>\<^sub>R ((\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel)))
  trans_from trans_impl"
  supply [transfer_rule] = int_trans_from_transfer bin_trans_from_transfer broad_trans_from_transfer
  unfolding trans_from_def trans_impl_def by transfer_prover

lemma list_all2_swap:
  "list_all2 S ys xs" if "list_all2 R xs ys" "S = (\<lambda>x y. R y x)" for R S
  using list_all2_swap that by blast

lemma swap_rel_prod: "(\<lambda> x y. (R \<times>\<^sub>R S) y x) = (\<lambda>x y. R y x) \<times>\<^sub>R (\<lambda>x y. S y x)" for R S
  by (intro ext) auto

lemma swap_eq:
  "(\<lambda>x y. y = x) = (=)"
  by auto

lemma trans_from_refine:
  "(trans_impl, trans_from) \<in> fun_rel_syn
    loc_rel
    (list_rel (Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r loc_rel))"
proof -
  have [rel2p]: "rel2p loc_rel = (\<lambda> x y. ((\<lambda>x y. list_all2 (=) x y \<and> length x = n_ps) \<times>\<^sub>R state_rel) y x)"
    unfolding loc_rel_def rel2p_def by (intro ext) (auto simp: list.rel_eq)
  have "rel2p (fun_rel_syn
      {((L', s'), L, s) |L s L' s'. L' = L \<and> length L = n_ps \<and> state_rel s s'}
      (\<langle>Id \<times>\<^sub>r Id \<times>\<^sub>r Id \<times>\<^sub>r loc_rel\<rangle>list_rel))
    trans_impl trans_from"
    unfolding rel2p rel2p_def state_rel_def
    by (intro rel_funI trans_from_transfer[THEN rel_funD, THEN list_all2_swap])
       (auto simp: list.rel_eq state_rel_def swap_rel_prod swap_eq)
  then show ?thesis
    unfolding rel2p_def relAPP_def loc_rel_def .
qed

lemma trans_from_correct:
  "(trans_from, trans_prod) \<in> transition_rel states'"
  using int_trans_from_correct bin_trans_from_correct broad_trans_from_correct
  unfolding trans_from_def trans_prod_def transition_rel_def by auto

end (* Lfiting Syntax *)

end (* Simple Network Impl nat *)

end (* Theory *)
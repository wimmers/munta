theory Simple_Network_Language_Embedding
  imports
    Generalized_Network_Language
    Simple_Networks.TA_Impl_Misc2
    Simple_Networks.Tagging Simple_Networks.Tag_Explorer Simple_Networks.Tagging_Cases
begin

paragraph \<open>More Tagging\<close>

ML \<open>
fun dest_tag trm = case trm of
  \<^Const>\<open>ANY _ for x\<close>   => SOME ("ANY", x)
| \<^Const>\<open>TRANS _ for x\<close> => SOME ("TRANS", x)
| \<^Const>\<open>SEL _ for x\<close>   => SOME ("SEL", x)
| \<^Const>\<open>SEND _ for x\<close>  => SOME ("SEND", x)
| \<^Const>\<open>RECV _ for x\<close>  => SOME ("RECV", x)
| _ => NONE
fun invent_tag_name ctxt trm = case dest_tag trm of
  SOME (tag, trm) => (case invent_name ctxt trm of
    SOME name => SOME (tag ^ " " ^ name)
  | NONE => NONE
  )
| NONE => invent_name ctxt trm
\<close>

method_setup tagged_cases =
  \<open>tagged_cases_gen invent_tag_name\<close> "Like goal_cases but try to infer case names from tag"


paragraph \<open>Setup\<close>

hide_const (open) Generalized_Network_Language.act.Sil

no_notation Generalized_Network_Language.step_u ("_ \<turnstile> \<langle>_, _, _\<rangle> \<rightarrow>\<^bsub>_\<^esub> \<langle>_, _, _\<rangle>" [61,61,61,61,61] 61)
no_notation Simple_Network_Language.step_u ("_ \<turnstile> \<langle>_, _, _\<rangle> \<rightarrow>\<^bsub>_\<^esub> \<langle>_, _, _\<rangle>" [61,61,61,61,61] 61)

notation Generalized_Network_Language.step_u ("_ \<turnstile>\<^sub>t \<langle>_, _, _\<rangle> \<rightarrow>\<^bsub>_\<^esub> \<langle>_, _, _\<rangle>" [61,61,61,61,61] 61)
notation Simple_Network_Language.step_u ("_ \<turnstile>\<^sub>s \<langle>_, _, _\<rangle> \<rightarrow>\<^bsub>_\<^esub> \<langle>_, _, _\<rangle>" [61,61,61,61,61] 61)


paragraph \<open>Library\<close>

lemma subseq_upt_split:
  "subseq ([l..<i] @ [j..<u]) [l..<u]" if "l \<le> i" "i \<le> j" "i \<le> u"
proof (cases "j \<le> u")
  case True
  then have "[l..<u] = [l..<i] @ [i..<j] @ [j..<u]"
    using that by auto
  then show ?thesis
    by (auto simp: subseq_append')
next
  case False
  then have "[l..<u] = [l..<i] @ [i..<u]" "[j..<u] = []"
    using that by auto
  then show ?thesis
    by (simp del: \<comment> \<open>XXX: horrible\<close> upt_eq_Nil_conv add: subseq_append' subseq_rev_drop_many)
qed

lemma list_emb_drop_many_right:
  assumes "list_emb P xs (ys @ zs)" "\<And>y. y \<in> set ys \<Longrightarrow> \<not> P (hd xs) y"
  shows "list_emb P xs zs"
  using assms
proof (induction ys)
  case Nil
  then show ?case by simp
next
  case (Cons a ys)
  then show ?case
    by (cases xs; simp)
qed

lemma subseq_nil_iff:
  "subseq xs [] \<longleftrightarrow> xs = []"
  by auto

lemma subseq_Cons_right_conv:
  "subseq xs (y # ys) \<longleftrightarrow> (\<exists>zs. xs = y # zs \<and> subseq zs ys) \<or> subseq xs ys"
  by (cases xs) (auto intro: subseq_Cons')

lemma subseq_binD:
  "subseq ps [p, q] \<Longrightarrow> p \<noteq> q \<Longrightarrow> p \<in> set ps \<Longrightarrow> q \<in> set ps \<Longrightarrow> ps = [p, q]"
  by (auto simp add: subseq_Cons_right_conv subseq_nil_iff)

lemma subseqI:
  assumes "set ps \<subseteq> {0..<n}" "p \<notin> set ps" "distinct ps" "sorted ps"
  shows   "subseq ps ([0..<p] @ [Suc p..<n])"
  using assms
  by - (rule sorted_distinct_subset_subseqI,
        auto simp: sorted_append subset_code(1), metis Suc_leI linorder_neqE_nat)


paragraph \<open>Definitions\<close>

definition
  "mk_bin_sync n a p q \<equiv> [(p, In a, True), (q, Out a, True)]"

definition
  "mk_broadcast_sync n a p \<equiv> (p, Out a, True) # map (\<lambda>p. (p, In a, False)) ([0..<p] @ [p+1..<n])"

definition
  "mk_syncs n broadcast actions =
    {mk_bin_sync n a p q | p q a. p < n \<and> q < n \<and> p \<noteq> q \<and> a \<notin> broadcast \<and> a \<in> actions}
  \<union> {mk_broadcast_sync n a p | p a. p < n \<and> a \<in> broadcast}"

definition actions :: "(_, 's, 'c, 't, 'x, 'v) Simple_Network_Language.sta \<Rightarrow> 'a set" where
  "actions A = {a. \<exists>l b g f r l'.
      (l,b,g,In a,f,r,l') \<in> Simple_Network_Language.trans A
    \<or> (l,b,g,Out a,f,r,l') \<in> Simple_Network_Language.trans A}"

\<comment> \<open>Clone of @{term Simple_Network_Language.conv_t}\<close>
definition t_to_s_a where "t_to_s_a a \<equiv> case a of
  In a'  \<Rightarrow> Com (In a')
| Out a' \<Rightarrow> Com (Out a')
| Sil a' \<Rightarrow> act.Sil (Sil a')
"

definition t_to_s_f where
  "t_to_s_f \<equiv> map (\<lambda>upd. (upd, 0))"

definition t_to_s_t where "t_to_s_t \<equiv> \<lambda> (l,b,g,a,f,r,l'). (l,b,g,t_to_s_a a,t_to_s_f f,r,l')"

\<comment> \<open>Clone of @{term Simple_Network_Language.conv_A}\<close>
definition t_to_s_A where "t_to_s_A \<equiv> \<lambda> (C, U, T, I). (C, U, t_to_s_t ` T, I)"

definition t_to_s ::
  "('a, 's, 'c, 't, 'x, 'v) Simple_Network_Language.nta
  \<Rightarrow> ('a Networks.act, 's, 'c, 't, 'x, 'v) nta" where
  "t_to_s \<equiv> \<lambda>(broadcast, automata, bounds).
  (
    mk_syncs (length automata) broadcast (\<Union>A \<in> set automata. actions A),
    map t_to_s_A automata,
    bounds
  )"

definition conv_action :: "nat \<Rightarrow> 'a Networks.act label \<Rightarrow> 'a Simple_Network_Language.label option"
  where
  "conv_action n a \<equiv> case a of
    Generalized_Network_Language.Del \<Rightarrow> Some Simple_Network_Language.Del
  | Generalized_Network_Language.Internal (Sil a) \<Rightarrow> Some (Simple_Network_Language.Internal a)
  | Generalized_Network_Language.Sync sync \<Rightarrow>
      if (\<exists>p q a. mk_bin_sync n a p q = sync \<and> p \<noteq> q \<and> p < n \<and> q < n) then
        Some (Simple_Network_Language.Bin (SOME a. \<exists>p q. mk_bin_sync n a p q = sync))
      else if (\<exists>p a. mk_broadcast_sync n a p = sync \<and> p < n) then
        Some (Simple_Network_Language.Broad (SOME a. \<exists>p. mk_broadcast_sync n a p = sync))
    else None
  | _ \<Rightarrow> None
  "


paragraph \<open>Proofs\<close>

lemma mk_broadcast_sync_not_internal:
  "(i, Sil a', b) \<notin> set (mk_broadcast_sync n a p)"
  unfolding mk_broadcast_sync_def by auto

lemma mk_bin_sync_not_internal:
  "(i, Sil a', b) \<notin> set (mk_bin_sync n a p q)"
  unfolding mk_bin_sync_def by auto

lemma mk_syncs_not_internal:
  "(i, Sil a, b) \<notin> set v" if "v \<in> mk_syncs n broadcast S"
  using that mk_broadcast_sync_not_internal mk_bin_sync_not_internal
  unfolding mk_syncs_def by fastforce

lemma mk_broadcast_sync_strongD:
  assumes "(i, a, True) \<in> set (mk_broadcast_sync n a' p)"
  shows "i = p" "a = Out a'"
  using assms unfolding mk_broadcast_sync_def by auto

lemma length_mk_bin_sync:
  "length (mk_bin_sync n a'' p q) = 2"
  unfolding mk_bin_sync_def by simp

lemma length_mk_broadcast_sync [simp]:
  "length (mk_broadcast_sync n a p) = n" if "p < n"
  using that unfolding mk_broadcast_sync_def by simp

lemma mk_bin_sync_inj:
  assumes "mk_bin_sync n a1 p1 q1 = mk_bin_sync n a2 p2 q2"
  shows "a1 = a2"
  using assms unfolding mk_bin_sync_def by simp

lemma mk_broadcast_sync_inj:
  assumes "mk_broadcast_sync n a1 p1 = mk_broadcast_sync n a2 p2"
  shows "a1 = a2"
  using assms unfolding mk_broadcast_sync_def by simp

lemma mk_bin_sync_neq_mk_broadcast_sync:
  assumes "mk_bin_sync n a1 p1 q1 = mk_broadcast_sync n a2 p2"
  shows False
  using assms unfolding mk_bin_sync_def mk_broadcast_sync_def by simp

lemma mk_sync_simps:
  "mk_bin_sync n a1 p1 q1 = mk_bin_sync n a2 p2 q2 \<longleftrightarrow> a1 = a2 \<and> p1 = p2 \<and> q1 = q2"
  "mk_broadcast_sync n a1 p1 = mk_broadcast_sync n a2 p2 \<longleftrightarrow> a1 = a2 \<and> p1 = p2"
  "mk_bin_sync n a1 p1 q1 = mk_broadcast_sync n a2 p2 \<longleftrightarrow> False"
  "mk_broadcast_sync n a2 p2 = mk_bin_sync n a1 p1 q1 \<longleftrightarrow> False"
  unfolding mk_bin_sync_def mk_broadcast_sync_def by auto

lemma inv_t_to_s_A_id [simp]:
  "inv (t_to_s_A N) = Simple_Network_Language.inv N"
  unfolding t_to_s_A_def inv_def Simple_Network_Language.inv_def by (simp split: prod.split)

lemma urgent_t_to_s_A_id [simp]:
  "urgent (t_to_s_A A) = Simple_Network_Language.urgent A"
  unfolding t_to_s_A_def Simple_Network_Language.urgent_def  urgent_def by (simp split: prod.split)

lemma committed_t_to_s_A_id [simp]:
  "committed (t_to_s_A A) = Simple_Network_Language.committed A"
  unfolding t_to_s_A_def committed_def Simple_Network_Language.committed_def
  by (simp split: prod.split)

lemma t_to_s_a_inj:
  "a = a'" if "t_to_s_a a = t_to_s_a a'"
  using that unfolding t_to_s_a_def by (cases a; cases a'; simp)

lemmas trans_defs = trans_def Simple_Network_Language.trans_def

lemmas t_to_s_defs = t_to_s_A_def t_to_s_t_def t_to_s_f_def

lemma trans_t_to_s_A_iff:
  "(l, b, g, a, f, r, l') \<in> Simple_Network_Language.trans A
  \<longleftrightarrow> (l, b, g, t_to_s_a a, t_to_s_f f, r, l') \<in> trans (t_to_s_A A)"
  by (auto split: prod.split simp: t_to_s_defs trans_defs image_def dest: t_to_s_a_inj)

lemma trans_t_to_s_A_E:
  assumes "(l, b, g, a, f, r, l') \<in> trans (t_to_s_A A)"
  obtains a' f' where
    "(l, b, g, a', f', r, l') \<in> Simple_Network_Language.trans A"
   "a = t_to_s_a a'" "f = t_to_s_f f'"
  using assms by (auto split: prod.split_asm simp: t_to_s_defs trans_defs)

lemma sort_upds_t_to_s_f_eq:
  "sort_upds (t_to_s_f f) = f"
proof -
  have "sort_key snd (t_to_s_f f) = t_to_s_f f"
    using sort_key_stable[where f = snd and k = 0 and xs = "t_to_s_f f"]
    unfolding t_to_s_f_def by simp
  moreover have "map fst \<dots> = f"
    unfolding t_to_s_f_def by (simp add: comp_def)
  ultimately show ?thesis
    unfolding sort_upds_def by metis
qed

lemma is_upds_idxs_t_to_s_f_iff:
  "is_upd_idxs s (t_to_s_f f) s' \<longleftrightarrow> is_upds s f s'"
  unfolding sort_upds_t_to_s_f_eq is_upd_idxs_def by auto

lemma t_to_s_f_append:
  "t_to_s_f f1 @ t_to_s_f f2 = t_to_s_f (f1 @ f2)"
  unfolding t_to_s_f_def by simp

lemma sort_upds_aux:
  "sort_upds (concat_map t_to_s_f fs) = concat fs"
  by (metis map_concat sort_upds_t_to_s_f_eq t_to_s_defs(3))

lemma is_upds_idxs_binI:
  assumes \<open>is_upds s f1 s1\<close> \<open>is_upds s1 f2 s2\<close>
  shows \<open>is_upds_idxs s [t_to_s_f f1, t_to_s_f f2] s2\<close>
  unfolding is_upds_idxs_def using assms
  by (auto intro: is_upds_appendI simp: sort_upds_aux[of "[f1, f2]", simplified])

lemma is_upds_idxs_concatI:
  assumes "is_upds s (concat fs) s'"
  shows "is_upds_idxs s (map t_to_s_f fs) s'"
  using assms unfolding is_upds_idxs_def sort_upds_aux .

lemma action_eqs: "t_to_s_a (In a) = Com (In a)" "t_to_s_a (Out a) = Com (Out a)"
  unfolding t_to_s_a_def by auto

lemmas trans_t_to_s_A_iff' =
  trans_t_to_s_A_iff[where a = "In a" for a, symmetric, unfolded action_eqs]
  trans_t_to_s_A_iff[where a = "Out a" for a, symmetric, unfolded action_eqs]

lemma s_to_t:
  fixes N n
  assumes lengths: "length L = n" "length (fst (snd N)) = n"
  defines "N' \<equiv> t_to_s N"
  assumes step: \<open>N \<turnstile>\<^sub>s \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>\<close>
  obtains a' where \<open>conv_action n a' = Some a\<close> \<open>N' \<turnstile>\<^sub>t \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a'\<^esub> \<langle>L', s', u'\<rangle>\<close>
proof -
  note thesisI = that
  from step show ?thesis
proof cases
  case (step_t N d B broadcast)
  have "conv_action n Del = Some a"
    unfolding conv_action_def \<open>a = _\<close> by simp
  with step_t show ?thesis
    by (elim thesisI) (simp add: N'_def t_to_s_def, rule step_u.step_t; simp; simp cong: ex_cong)
next
  case [tagged]: (step_int l b g a'' f r l' As p B broadcast)
  from \<open>a = _\<close> have "conv_action n (Internal (Sil a'')) = Some a"
    by (simp add: conv_action_def)
  moreover have *: "t_to_s_a (Sil a'') = act.Sil (Sil a'')"
    unfolding t_to_s_a_def by simp
  \<^cancel>\<open>moreover have "t_to_s_f f = ()"\<close>
  ultimately show ?thesis
    using \<open>N = _\<close> lengths usingT \<open>''range''\<close>
    apply (elim thesisI, simp add: N'_def t_to_s_def, intro step_u.step_int[where p = p])
              apply   (tag; simp add: trans_t_to_s_A_iff * is_upds_idxs_t_to_s_f_iff)+
    done
next
  case [tagged]: (step_bin a'' broadcast l1 b1 g1 f1 r1 l1' As p l2 b2 g2 f2 r2 l2' q s' B)
  from assms(2) \<open>N = _\<close> have \<open>length As = n\<close>
    by simp
  note lengths = \<open>length L = n\<close> \<open>length As = n\<close>
  from \<open>a = _\<close> have sync:
    "conv_action n (Sync (mk_bin_sync n a'' p q)) = Some a"
    by (tag \<open>SEND ''range''\<close> \<open>RECV ''range''\<close> \<open>''different''\<close>)
       (simp add: conv_action_def lengths mk_sync_simps)
  note the_rule = step_u.step_sync[
      where ps = "[p, q]"
        and as = "\<lambda>i. if i = p then In a'' else Out a''"
        and bs = "\<lambda>i. if i = p then b1 else b2"
        and gs = "\<lambda>i. if i = p then g1 else g2"
        and fs = "\<lambda>i. if i = p then t_to_s_f f1 else t_to_s_f f2"
        and rs = "\<lambda>i. if i = p then r1 else r2"
        and ls' = "\<lambda>i. if i = p then l1' else l2'"
        ]
  from step_bin have "a'' \<in> \<Union> (actions ` set As)"
    unfolding actions_def
    by (tag \<open>''not broadcast''\<close> \<open>SEND ''range''\<close> \<open>RECV ''range''\<close> \<open>TRANS _\<close>)
       (auto, metis lengths nth_mem)
  from sync \<open>N = _\<close> show ?thesis
    apply (elim thesisI)
    unfolding N'_def t_to_s_def
    apply simp
    apply (rule the_rule)
                    apply (all \<open>(tag, assumption)?\<close>)
    preferT \<open>''sync''\<close> subgoal sync
      by (tag "''not broadcast''" "SEND ''range''" "RECV ''range''" "''different''")
         (simp add: mk_syncs_def lengths, use \<open>a'' \<in> _\<close> in fast)
    subgoal enabled
      by (tag, auto simp: mk_bin_sync_def lengths nth_list_update' split: if_split_asm)
    subgoal only_syncs
      by (tag, auto simp: mk_bin_sync_def)
    subgoal actions
      by (tag \<open>''different''\<close>, auto simp: mk_bin_sync_def)
    subgoal sync
      by (tag "TRANS _" "SEND _" "RECV _", auto simp: lengths trans_t_to_s_A_iff')
    subgoal committed
      by (tag "SEND _" "RECV _", auto simp: lengths)
    subgoal bexp
      by (tag, auto)
    subgoal guard
      by (tag, auto)
    subgoal maximal
      by (tag, auto simp: mk_bin_sync_def lengths)
    subgoal range
      by (tag "SEND ''range''" "RECV ''range''", auto simp: lengths)
    subgoal distinct
      by (tag "''different''" "SEND ''range''" "RECV ''range''", auto simp: lengths)
    subgoal sublist
      by (tag, auto simp: mk_bin_sync_def)
    subgoal new_loc
      by (tag "''different''", auto simp: list_update_swap)
    subgoal new_valuation
      by (tag "''different''", auto)
    subgoal upds
      by (tag "''different''" "''upd''", clarsimp simp: sort_upds_t_to_s_f_eq)
         (rule is_upds_idxs_binI)
    done
next
  case [tagged, untagged]:
    (step_broad a'' broadcast l b g f r l' As p ps bs gs fs rs ls' s1 B)
  from assms(2) \<open>N = _\<close> have \<open>length As = n\<close>
    by simp
  note lengths = \<open>length L = n\<close> \<open>length As = n\<close>
  from \<open>a = _\<close> \<open>p < _\<close> have sync:
    "conv_action n (Sync (mk_broadcast_sync n a'' p)) = Some a"
    by (simp add: lengths conv_action_def mk_sync_simps)
  let ?fs = "\<lambda>q. t_to_s_f ((fs(p := f)) q)"
  note the_rule = step_u.step_sync[
      where ps = "p # ps"
        and as = "\<lambda>i. if i = p then Out a'' else In a''"
        and bs = "bs(p := b)"
        and gs = "gs(p := g)"
        and rs = "rs(p := r)"
        and fs = "\<lambda>q. t_to_s_f ((fs(p := f)) q)"
        and ls'= "ls'(p := l')"]
  have upds_simp: "concat (map ?fs (p # ps)) = concat_map t_to_s_f (map (fs(p := f)) (p # ps))"
    by (simp add: comp_def)
  from \<open>N = _\<close> \<open>a = _\<close> sync show ?thesis
    apply (elim thesisI)
    unfolding N'_def t_to_s_def
    apply simp
    apply (rule the_rule)
    preferT \<open>''sync''\<close> subgoal
      by (tag "''broadcast''" "SEND ''range''", simp add: lengths mk_syncs_def, fast)
    preferT \<open>''enabled''\<close> subgoal
      by (tag, auto dest: mk_broadcast_sync_strongD(1) simp: lengths)
    preferT \<open>''only syncs''\<close> subgoal
      by (tag \<open>SEL ''range''\<close>, fastforce simp: mk_broadcast_sync_def lengths)
    preferT \<open>''actions''\<close> subgoal
      by (tag, auto simp: mk_broadcast_sync_def lengths)
    preferT \<open>TRANS ''sync''\<close> subgoal
      by (tag "TRANS _" "SEND _" "SEL ''range''", auto simp: lengths trans_t_to_s_A_iff')
    preferT \<open>''committed''\<close> subgoal
      by (tag "SEND _" "SEL ''range''", auto simp: lengths subset_code(1))
    preferT \<open>''bexp''\<close> subgoal
      by (tag, auto)
    preferT \<open>''guard''\<close> subgoal
      by (tag, auto)
   preferT \<open>''maximal''\<close> subgoal
      by (tag, clarsimp simp: lengths mk_broadcast_sync_def, erule trans_t_to_s_A_E)
         (simp add: t_to_s_f_def t_to_s_a_def split: Networks.act.splits, fast)
    preferT \<open>''target invariant''\<close> subgoal
      by (tag, simp)
    preferT \<open>SEL ''range''\<close> subgoal
      by (tag "SEND ''range''", simp add: lengths)
    preferT \<open>SEL ''sublist''\<close> subgoal
      by (tag "SEL _", simp add: mk_broadcast_sync_def comp_def lengths subseqI)
    preferT \<open>''new loc''\<close> subgoal
      by (tag "SEL _" "''new loc''", simp, rule fold_commute_apply)
         (auto simp: comp_def intro!: list_update_swap)
    preferT \<open>''new valuation''\<close> subgoal
      by (tag "SEL _" "''new valuation''", auto)
    preferT \<open>''upds''\<close> subgoal
      by (tag "SEL _" "''upds''" "''upd''", unfold is_upds_idxs_def sort_upds_aux upds_simp)
         (auto intro: is_upds_appendI)
    preferT \<open>''bounded''\<close> subgoal
      by tag
    done
qed
qed

lemma mk_syncs_Out:
  assumes "a \<in> actions (As ! p)" "p < length As" "q < length As" "p \<noteq> q"
  obtains v b where
    "(p, Out a, b) \<in> set v"
    "v \<in> mk_syncs (length As) broadcast (\<Union> (actions ` set As))"
proof (cases "a \<in> broadcast")
  case True
  with assms show ?thesis
    by (intro that[where v = "mk_broadcast_sync (length As) a p" and ?b = True])
       (auto simp: mk_syncs_def mk_broadcast_sync_def)
next
  case False
  with assms show ?thesis
    by (intro that[where v = "mk_bin_sync (length As) a q p" and ?b = True])
       (fastforce simp: mk_syncs_def mk_bin_sync_def)+
qed

lemma mk_syncs_In:
  assumes "a \<in> actions (As ! p)" "p < length As" "q < length As" "p \<noteq> q"
  obtains v b where
    "(p, In a, b) \<in> set v"
    "v \<in> mk_syncs (length As) broadcast (\<Union> (actions ` set As))"
proof (cases "a \<in> broadcast")
  case True
  with assms show ?thesis
    by (intro that[where v = "mk_broadcast_sync (length As) a q" and ?b = False])
       (fastforce simp: mk_syncs_def mk_broadcast_sync_def)+
next
  case False
  with assms show ?thesis
    by (intro that[where v = "mk_bin_sync (length As) a p q" and ?b = True])
       (fastforce simp: mk_syncs_def mk_bin_sync_def)+
qed

lemma t_to_s:
  fixes N n
  assumes "length L = n" "length (fst (snd N)) = n"
  defines "N' \<equiv> t_to_s N"
  assumes step: \<open>N' \<turnstile>\<^sub>t \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a'\<^esub> \<langle>L', s', u'\<rangle>\<close>
  obtains a where \<open>conv_action n a' = Some a\<close> \<open>N \<turnstile>\<^sub>s \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>\<close>
proof -
  note thesisI = that
  obtain As broadcast B where "N = (broadcast, As, B)"
    by (metis prod.collapse)
  let ?syncs = "mk_syncs (length As) broadcast (\<Union>A \<in> set As. actions A)"
  from \<open>N = _\<close> have "N' = (?syncs, map t_to_s_A As, B)"
    unfolding N'_def t_to_s_def by simp
  from assms(2) have "length As = n"
    by (simp add: \<open>N = _\<close>)
  note lengths [simp] = \<open>length L = n\<close> \<open>length As = n\<close>
  from step[unfolded \<open>N' = _\<close>] show ?thesis
  proof cases
    case [tagged]: (step_t d)
    from \<open>a' = _\<close> have "conv_action n a' = Some Simple_Network_Language.label.Del"
      by (simp add: conv_action_def)
    then show ?thesis
      apply (elim thesisI)
      apply (simp only: \<open>N = _\<close> step_t)
      apply (rule Simple_Network_Language.step_u.intros)
      apply (tag; auto)+
      done
  next
    case [tagged]: (step_int l b g a'' f r l' p)
    obtain a1 f1 where trans:
      "a'' = Sil a1" "f = t_to_s_f f1"
      "(l, b, g, Sil a1, f1, r, l') \<in> Simple_Network_Language.trans (As ! p)"
      usingT \<open>TRANS _\<close> \<open>''range''\<close>
      by (auto elim!: trans_t_to_s_A_E simp: t_to_s_a_def split: Networks.act.split_asm)
    with \<open>a' = _\<close> have
      "conv_action n a' = Some (Simple_Network_Language.label.Internal a1)"
      by (auto simp: conv_action_def)
    then show ?thesis
      apply (rule thesisI)
      apply (simp only: \<open>N = _\<close>)
      apply (rule Simple_Network_Language.step_u.step_int)
      preferT \<open>TRANS ''silent''\<close> apply (untag, rule trans(3))
      usingT \<open>''range''\<close> apply (tag, simp add: is_upds_idxs_t_to_s_f_iff \<open>f = _\<close>; fail)+
      done
  next
    case [tagged, untagged]: (step_sync sync ps as bs gs fs rs ls')
    have fs_from_t_to_s_f: "\<exists>f. fs p = t_to_s_f f" if "p \<in> set ps" for p
      usingT- \<open>TRANS _\<close> using that \<open>set ps \<subseteq> _\<close> by (fastforce elim: trans_t_to_s_A_E)
    from fs_from_t_to_s_f obtain fs' where fs_eq:
      "fs p = t_to_s_f (fs' p)" if "p \<in> set ps" for p
      using that by metis
    then have "map t_to_s_f (map fs' ps) = map fs ps"
      by simp
    then have sort_upds_eq: "sort_upds (concat_map fs ps) = concat_map fs' ps"
      using sort_upds_aux[of "map fs' ps"] by metis
    from \<open>sync \<in> ?syncs\<close> consider
      (bin) a p q t where
        "sync = [(p, In a, True), (q, Out a, True)]"
        "p < n" "q < n" "p \<noteq> q" "a \<notin> broadcast" "t\<in>set As" "a \<in> actions t" |
      (broadcast) a p where
        "sync = mk_broadcast_sync n a p"
        "p < n" "a \<in> broadcast"
      unfolding mk_syncs_def mk_bin_sync_def by auto
    then show ?thesis
    proof cases
      case bin
      then have "ps = [p, q]"
        using \<open>a' = _\<close> usingT \<open>''enabled''\<close> by (tag "SEL _") (simp add: subseq_binD)
      with \<open>ps = _\<close> obtain s1 where
        [tag \<open>''upd''\<close>]: \<open>is_upds s (fs' p) s1\<close> \<open>is_upds s1 (fs' q) s'\<close>
        usingT \<open>''upds''\<close> unfolding is_upds_idxs_def sort_upds_eq by (auto elim: is_upds_appendE)
      from \<open>ps = _\<close> \<open>sync = _\<close> have
        [tag \<open>TRANS ''in''\<close>]: "as p = In a" and [tag \<open>TRANS ''out''\<close>]: "as q = Out a"
        by - (tag "''actions''", simp add: mk_bin_sync_def)+
      from bin \<open>a' = _\<close> have
        "conv_action n a' = Some (Simple_Network_Language.label.Bin a)"
        by (simp add: conv_action_def mk_bin_sync_def)
      then show ?thesis
        using bin \<open>a' = _\<close> \<open>ps = _\<close>
        apply (elim thesisI)
        apply simp
        unfolding \<open>N = _\<close>
        apply (rule step_u.step_bin)
        preferT \<open>''not broadcast''\<close> apply (tag, assumption)
        preferT \<open>TRANS ''in''\<close>
          apply (tag \<open>TRANS ''sync''\<close>, simp add: trans_t_to_s_A_iff t_to_s_a_def fs_eq, fast)
        preferT \<open>TRANS ''out''\<close>
          apply (tag \<open>TRANS ''sync''\<close>, simp add: trans_t_to_s_A_iff t_to_s_a_def fs_eq, fast)
        apply (tag, simp; fail)+
        done
    next
      case broadcast
      from broadcast \<open>a' = _\<close> have
        "conv_action n a' = Some (Simple_Network_Language.label.Broad a)"
        by (auto simp: conv_action_def mk_sync_simps)
      have *: "set ps \<subseteq> {0..<n}" "subseq ps (p # [0..<p] @ [Suc p..<n])" "p \<in> set ps"
        using \<open>sync = _\<close> usingT- \<open>SEL _\<close> \<open>''enabled''\<close> by (auto simp: mk_broadcast_sync_def comp_def)
      then obtain ps' where [simp]: "ps = p # ps'"
        by (cases ps) (auto split: if_split_asm elim: list_emb_set)
      from * \<open>ps = _\<close> have "subseq ps' ([0..<p] @ [Suc p..<n])"
        by simp
      then have "set ps' \<subseteq> set ([0..<p] @ [Suc p..<n])"
        by (metis (mono_tags, lifting) list_emb_set subset_code(1))
      then have "p \<notin> set ps'"
        by auto
      have all_sync_ingoing: "(q, In a, False) \<in> set sync" if "q < n" "q \<noteq> p" for q
        using \<open>sync = _\<close> that by (cases "q < p"; auto simp: mk_broadcast_sync_def)
      then have all_actions_ingoing: "\<forall>q < n. q \<noteq> p \<longrightarrow> as q = In a"
        usingT \<open>''actions''\<close> by fastforce
      with \<open>set ps' \<subseteq> _\<close> \<open>p \<notin> _\<close> \<open>p < n\<close> have [tag "TRANS ''in''"]: "\<forall>q \<in> set ps'. as q = In a"
        by untag auto
      from \<open>sync = _\<close> have [tag "TRANS ''out''"]: "as p = Out a"
        usingT \<open>''actions''\<close> by (untag, auto simp: mk_broadcast_sync_def)
      have [tag "SEL ''distinct''"]: "distinct ps'"
        using \<open>subseq ps' _\<close> by (untag, rule subseq_distinct[rotated], simp)
      from \<open>p < n\<close> have "sorted ([0..<p] @ [Suc p..<n])"
        by - (rule subseq_sorted[where ys = "[0..<n]"], auto intro!: subseq_upt_split)
      then have [tag "SEL ''sorted''"]: "sorted ps'"
        using \<open>subseq ps' _\<close> by (untag, rule subseq_sorted)
      with \<open>ps = _\<close> obtain s1 where [tag \<open>''upd''\<close>]: \<open>is_upds s (fs' p) s1\<close>
        and [tag \<open>''upds''\<close>]: \<open>is_upds s1 (concat_map fs' ps') s'\<close>
        usingT \<open>''upds''\<close> unfolding is_upds_idxs_def sort_upds_eq by (auto elim: is_upds_appendE)
      note [simp] = subset_code(1) trans_t_to_s_A_iff t_to_s_a_def
      note the_rule = step_u.step_broad[where
          ps = "ps'" and bs = bs and gs = gs and fs = fs' and rs = rs and ls' = ls']
      show ?thesis
        using \<open>conv_action n a' = _\<close> *(1)
        apply (elim thesisI)
        unfolding \<open>N = _\<close>
        apply (rule the_rule)
        preferT \<open>TRANS ''out''\<close>
          apply (tag \<open>TRANS ''sync''\<close>, simp add: fs_eq; fast)
        preferT \<open>TRANS ''in''\<close>
          apply (tag \<open>TRANS ''sync''\<close>, simp add: fs_eq; fail)
        preferT \<open>''maximal''\<close>
        subgoal
          apply (tag, simp)
          using all_actions_ingoing all_sync_ingoing by metis
        preferT \<open>''broadcast''\<close>
          apply (untag, rule broadcast)
        preferT \<open>SEL ''not sender''\<close>
          apply (untag, rule \<open>p \<notin> set ps'\<close>)
        preferT \<open>''new loc''\<close>
          apply (tag, simp, rule fold_commute_apply[symmetric],
                 auto simp: comp_def intro!: list_update_swap; fail)
        apply (tag; simp; fail)+
        done
    qed
  qed
qed

theorem t_sim_s:
  fixes N n
  assumes "length L = n" "length (fst (snd N)) = n"
  defines "N' \<equiv> t_to_s N"
  shows \<open>(\<exists>a. N \<turnstile>\<^sub>s \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>) \<longleftrightarrow> (\<exists>a'. N' \<turnstile>\<^sub>t \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a'\<^esub> \<langle>L', s', u'\<rangle>)\<close>
  using t_to_s[OF assms(1,2)] s_to_t[OF assms(1,2)] unfolding N'_def by metis

end

theory Simple_Network_Language_Embedding
  imports TChecker_Network_Language Tagging "~/Code/explorer/Explorer"
begin

no_notation TChecker_Network_Language.step_u ("_ \<turnstile> \<langle>_, _, _\<rangle> \<rightarrow>\<^bsub>_\<^esub> \<langle>_, _, _\<rangle>" [61,61,61,61,61] 61)
no_notation Simple_Network_Language.step_u ("_ \<turnstile> \<langle>_, _, _\<rangle> \<rightarrow>\<^bsub>_\<^esub> \<langle>_, _, _\<rangle>" [61,61,61,61,61] 61)

notation TChecker_Network_Language.step_u ("_ \<turnstile>\<^sub>t \<langle>_, _, _\<rangle> \<rightarrow>\<^bsub>_\<^esub> \<langle>_, _, _\<rangle>" [61,61,61,61,61] 61)
notation Simple_Network_Language.step_u ("_ \<turnstile>\<^sub>s \<langle>_, _, _\<rangle> \<rightarrow>\<^bsub>_\<^esub> \<langle>_, _, _\<rangle>" [61,61,61,61,61] 61)

definition
  "mk_bin_sync n a p q \<equiv> (replicate n None)[p := Some (In a, True), q := Some (Out a, True)]"

definition
  "mk_broadcast_sync n a p \<equiv> (replicate n (Some (In a, False)))[p := Some (Out a, True)]"

definition
  "mk_syncs n broadcast actions =
    {mk_bin_sync n a p q | p q a. p < n \<and> q < n \<and> p \<noteq> q \<and> a \<notin> broadcast \<and> a \<in> actions}
  \<union> {mk_broadcast_sync n a p | p a. p < n \<and> a \<in> broadcast}"

definition actions :: "('a act, 's, 'c, 't, 'x, 'v) Simple_Network_Language.sta \<Rightarrow> 'a set" where
  "actions A = {a. \<exists>l b g f r l'. (l,b,g,In a,f,r,l') \<in> trans A \<or> (l,b,g,Out a,f,r,l') \<in> trans A}"

definition t_to_s ::
  "('a, 's, 'c, 't, 'x, 'v) Simple_Network_Language.nta
  \<Rightarrow> ('a act, 's, 'c, 't, 'x, 'v) nta" where
  "t_to_s \<equiv> \<lambda>(broadcast, automata, bounds).
  (
    mk_syncs (length automata) broadcast (\<Union>A \<in> set automata. actions A),
    automata,
    bounds
  )"


definition conv_action :: "nat \<Rightarrow> 'a act label \<Rightarrow> 'a Simple_Network_Language.label option" where
  "conv_action n a \<equiv> case a of
    TChecker_Network_Language.Del \<Rightarrow> Some Simple_Network_Language.Del
  | TChecker_Network_Language.Internal (Sil a) \<Rightarrow> Some (Simple_Network_Language.Internal a)
  | TChecker_Network_Language.Sync sync \<Rightarrow>
    if length sync = n then
      if (\<exists>p q a. mk_bin_sync n a p q = sync \<and> p \<noteq> q \<and> p < n \<and> q < n) then
        Some (Simple_Network_Language.Bin (SOME a. \<exists>p q. mk_bin_sync n a p q = sync))
      else if (\<exists>p a. mk_broadcast_sync n a p = sync \<and> p < n) then
        Some (Simple_Network_Language.Broad (SOME a. \<exists>p. mk_broadcast_sync n a p = sync))
      else
        None
    else None
  | _ \<Rightarrow> None
  "

lemma mk_broadcast_sync_not_internal:
  "mk_broadcast_sync n a p ! i \<noteq> Some (Sil a', b)" if "i < n"
  unfolding mk_broadcast_sync_def using that by (auto split: if_split_asm simp: nth_list_update')

lemma mk_bin_sync_not_internal:
  "mk_bin_sync n a p q ! i \<noteq> Some (Sil a', b)" if "i < n"
  unfolding mk_bin_sync_def using that by (auto split: if_split_asm simp: nth_list_update')

lemma mk_syncs_not_internal:
  "v ! i \<noteq> Some (Sil a, b)" if "v \<in> mk_syncs n broadcast S" "i < n"
  using that mk_broadcast_sync_not_internal mk_bin_sync_not_internal
  unfolding mk_syncs_def by fastforce

lemma mk_broadcast_sync_strongD:
  assumes "mk_broadcast_sync n a' p ! i = Some (a, True)" "i < n"
  shows "i = p" "a = Out a'"
  using assms unfolding mk_broadcast_sync_def by (auto simp: nth_list_update' split: if_split_asm)

lemma length_mk_bin_sync [simp]:
  "length (mk_bin_sync n a'' p q) = n"
  unfolding mk_bin_sync_def by simp

lemma length_mk_broadcast_sync [simp]:
  "length (mk_broadcast_sync n a p) = n"
  unfolding mk_broadcast_sync_def by simp

lemma mk_bin_sync_inj:
  assumes "mk_bin_sync n a1 p1 q1 = mk_bin_sync n a2 p2 q2" "p1 < n"
  shows "a1 = a2"
proof -
  from assms have "mk_bin_sync n a1 p1 q1 ! p1 = mk_bin_sync n a2 p2 q2 ! p1"
    by simp
  with \<open>p1 < n\<close> show ?thesis
    unfolding mk_bin_sync_def nth_list_update' by (auto split: if_split_asm)
qed

lemma mk_broadcast_sync_inj:
  assumes "mk_broadcast_sync n a1 p1 = mk_broadcast_sync n a2 p2" "p1 < n"
  shows "a1 = a2"
  by (metis assms act.inject(2) length_replicate mk_broadcast_sync_def
      mk_broadcast_sync_strongD(2) nth_list_update_eq)

lemma mk_bin_sync_neq_mk_broadcast_sync:
  assumes "mk_bin_sync n a1 p1 q1 = mk_broadcast_sync n a2 p2" "p1 < n" "p1 \<noteq> q1"
  shows False
proof -
  from assms have "mk_bin_sync n a1 p1 q1 ! p1 = mk_broadcast_sync n a2 p2 ! p1"
    by simp
  with \<open>p1 < n\<close> \<open>p1 \<noteq> q1\<close> show ?thesis
    unfolding mk_bin_sync_def mk_broadcast_sync_def nth_list_update' by (auto split: if_split_asm)
qed

lemma s_to_t:
  fixes N n
  assumes "length L = n" "length (fst (snd N)) = n"
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
    by (elim thesisI) (simp add: N'_def t_to_s_def, rule step_u.step_t)
next
  case (step_int l b g a'' f r l' As p B broadcast)
  from assms(2) \<open>N = _\<close> have \<open>length As = n\<close>
    by simp
  from \<open>a = _\<close> have "conv_action n (Internal (Sil a'')) = Some a"
    by (simp add: conv_action_def)
  moreover have "''internal'' \<bar> Sil a'' \<notin> syncs_of (fst N') p"
    using \<open>N = _\<close> step_int(9) mk_syncs_not_internal
    unfolding N'_def syncs_of_def t_to_s_def TAG_def
    by (fastforce simp: \<open>length As = n\<close> \<open>length L = n\<close>)
  ultimately show ?thesis
    using step_int by (elim thesisI) (simp add: N'_def t_to_s_def, rule step_u.step_int)
next
  case (step_bin a'' broadcast l1 b1 g1 f1 r1 l1' As p l2 b2 g2 f2 r2 l2' q s' B)
  from assms(2) \<open>N = _\<close> have \<open>length As = n\<close>
    by simp
  note lengths = \<open>length L = n\<close> \<open>length As = n\<close>
  from step_bin have sync:
    "conv_action n (Sync (mk_bin_sync n a'' p q)) = Some a"
    by (tag \<open>SEND ''range''\<close> \<open>RECV ''range''\<close> \<open>''different''\<close>)
       (simp add: conv_action_def lengths, smt (verit) mk_bin_sync_inj some_equality)
  note the_rule = step_u.step_sync[
      where ps = "sort [p, q]"
        and as = "\<lambda>i. if i = p then In a'' else Out a''"
        and bs = "\<lambda>i. if i = p then b1 else b2"
        and gs = "\<lambda>i. if i = p then g1 else g2"
        and fs = "\<lambda>i. if i = p then f1 else f2"
        and rs = "\<lambda>i. if i = p then r1 else r2"
        and ls' = "\<lambda>i. if i = p then l1' else l2'"
        ]
  from step_bin have "a'' \<in> \<Union> (actions ` set As)"
    unfolding actions_def
    by (tag \<open>''not broadcast''\<close> \<open>SEND ''range''\<close> \<open>RECV ''range''\<close> \<open>TRANS _\<close>)
       (auto, metis lengths nth_mem)
  from sync step_bin sync show ?thesis
    apply (elim thesisI)
    unfolding N'_def t_to_s_def
    apply simp
    apply (rule the_rule)
                   apply (all \<open>assumption?\<close>)
    preferT \<open>''sync''\<close> subgoal sync
      by (tag "''not broadcast''" "SEND ''range''" "RECV ''range''" "''different''")
         (simp add: mk_syncs_def lengths, use \<open>a'' \<in> _\<close> in fast)
    subgoal enabled
      by (tag, auto simp: mk_bin_sync_def lengths nth_list_update' split: if_split_asm)
    subgoal only_syncs
      by (tag, auto simp: mk_bin_sync_def lengths nth_list_update')
    subgoal actions
      by (tag \<open>''different''\<close>, auto simp: mk_bin_sync_def lengths nth_list_update')
    subgoal sync
      by (tag "TRANS _" "SEND ''loc''" "RECV ''loc''", auto)
    subgoal committed
      by (tag "''committed''" "SEND ''loc''" "RECV ''loc''", auto)
    subgoal bexp
      by (tag "''bexp''", auto)
    subgoal guard
      by (tag "''guard''", auto)
    subgoal maximal
      by (tag, auto simp: mk_bin_sync_def lengths nth_list_update' split: if_split_asm)
    subgoal range
      by (tag "SEND ''range''" "RECV ''range''", auto simp: lengths)
    subgoal distinct
      by (tag "''different''", auto)
    subgoal sorted
      by (tag, auto simp: sorted_insort)
    subgoal new_loc
      by (tag "''different''" "''new loc''", auto simp: list_update_swap)
    subgoal new_valuation
      apply (tag "''different''" "''new valuation''", auto)
        \<comment> \<open>provable\<close>
      sorry
    subgoal upds
      apply (tag "''different''" "''upds''" "''upd''", auto, blast intro: is_upds.intros)
        \<comment> \<open>Not provable, see explanation below\<close>
      sorry
    done
next
  case (step_broad a'' broadcast l b g f r l' As p ps bs gs fs rs ls' s' B)
  from assms(2) \<open>N = _\<close> have \<open>length As = n\<close>
    by simp
  note lengths = \<open>length L = n\<close> \<open>length As = n\<close>
  from step_broad have sync:
    "conv_action n (Sync (mk_broadcast_sync n a'' p)) = Some a"
    apply (tag "SEND ''range''")
    apply (auto simp: conv_action_def lengths elim: mk_bin_sync_neq_mk_broadcast_sync)
    apply (smt (verit) mk_broadcast_sync_inj some_equality)
    done
  let ?ps = "insort p ps"
  have [simp]: "set ?ps = insert p (set ps)"
    by (simp add: set_insort_key)
  note the_rule = step_u.step_sync[
      where ps = ?ps
        and as = "\<lambda>i. if i = p then Out a'' else In a''"
        and bs = "bs(p := b)"
        and gs = "gs(p := g)"
        and rs = "rs(p := r)"
        and fs = "fs(p := f)"
        and ls'= "ls'(p := l')"]
  from step_broad sync show ?thesis
    apply (elim thesisI)
    unfolding N'_def t_to_s_def
    apply simp
    apply (rule the_rule)
                   apply (all \<open>assumption?\<close>)
    subgoal sync
      by (tag  "''broadcast''" "SEND ''range''", simp add: lengths mk_syncs_def, fast)
    subgoal enabled
      by (tag, auto dest: mk_broadcast_sync_strongD(1) simp: lengths)
    subgoal only_syncs
      by (tag, auto simp: mk_broadcast_sync_def lengths nth_list_update')
    subgoal actions
      by (tag, auto simp: mk_broadcast_sync_def lengths)
    subgoal sync
      by (tag "TRANS _" "SEND ''loc''", auto)
    subgoal committed
      by (tag "''committed''" "SEND ''loc''", auto)
    subgoal bexp
      by (tag, auto)
    subgoal guard
      by (tag, auto)
    subgoal maximal
      by (tag, simp, blast)
    subgoal range
      by (tag "SEND ''range''" "SEL ''range''", auto simp: lengths)
    subgoal distinct
      by (tag "SEL _", auto simp: distinct_insort)
    subgoal sorted
      by (tag "SEL _" "''sorted''", auto simp: sorted_insort)
    subgoal new_loc
      apply (tag "SEL _" "''new loc''", auto)
        \<comment> \<open>provable\<close>
      sorry
    subgoal new_valuation
      apply (tag "SEL _" "''new valuation''", auto)
        \<comment> \<open>provable\<close>
      sorry
    subgoal upds
      apply (tag "SEL _" "''upds''" "''upd''", auto)
      text \<open>
  Here we have an apparent conflict between two requirements:
  \<^item> the processes need to be sorted
  \<^item> the updates of a broadcast explicitly apply the outgoing update first
  
  Possible solutions:
  \<^item> allow indexing of assignments, then the original order can be enforced
  \<^item> change semantics such that assignments are always done in process order?
  \<^item> add assumption that updates can be reordered
\<close>
      sorry
    done
qed
qed

lemma mk_syncs_Out:
  assumes "a \<in> actions (As ! p)" "p < length As" "q < length As" "p \<noteq> q"
  obtains v b where
    "v ! p = Some (Out a, b)"
    "v \<in> mk_syncs (length As) broadcast (\<Union> (actions ` set As))"
proof (cases "a \<in> broadcast")
  case True
  with assms show ?thesis
    apply -
    apply (rule that[where v = "mk_broadcast_sync (length As) a p" and ?b = True])
    apply (simp add: mk_broadcast_sync_def; fail)
    apply (auto simp: mk_syncs_def)
    done
next
  case False
  with assms show ?thesis
    apply -
    apply (rule that[where v = "mk_bin_sync (length As) a q p" and ?b = True])
    apply (simp add: mk_bin_sync_def; fail)
    apply (fastforce simp: mk_syncs_def)
    done
qed

lemma mk_syncs_In:
  assumes "a \<in> actions (As ! p)" "p < length As" "q < length As" "p \<noteq> q"
  obtains v b where
    "v ! p = Some (In a, b)"
    "v \<in> mk_syncs (length As) broadcast (\<Union> (actions ` set As))"
proof (cases "a \<in> broadcast")
  case True
  with assms show ?thesis
    apply -
    apply (rule that[where v = "mk_broadcast_sync (length As) a q" and ?b = False])
    apply (simp add: mk_broadcast_sync_def; fail)
    apply (auto simp: mk_syncs_def)
    done
next
  case False
  with assms show ?thesis
    apply -
    apply (rule that[where v = "mk_bin_sync (length As) a p q" and ?b = True])
    apply (simp add: mk_bin_sync_def; fail)
    apply (fastforce simp: mk_syncs_def)
    done
qed

lemma t_to_s:
  fixes N n
  assumes "length L = n" "length (fst (snd N)) = n"
  defines "N' \<equiv> t_to_s N"
  assumes step: \<open>N' \<turnstile>\<^sub>t \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a'\<^esub> \<langle>L', s', u'\<rangle>\<close>
  obtains a where \<open>conv_action n a' = Some a\<close> \<open>N \<turnstile>\<^sub>s \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>\<close>
proof -
  note thesisI = that
  from step show ?thesis
  proof cases
    case (step_t N d B syncs)
    from \<open>a' = _\<close> have "conv_action n a' = Some Simple_Network_Language.label.Del"
      by (simp add: conv_action_def)
    with step_t show ?thesis
      by (elim thesisI) (simp add: N'_def t_to_s_def split: prod.split_asm, rule)
  next
    case (step_int a'' syncs p l b g f r l' As B)
    note [tagged] = step_int(3-)
    from assms(2) \<open>N' = _\<close> have lengths: "length As = n"
      by (simp add: N'_def t_to_s_def split: prod.split_asm)
    from step_int have "a'' \<notin> syncs_of syncs p"
      unfolding TAG_def by simp
    have "p < n"
      using assms(1) by (tag \<open>''range''\<close>, simp only:)
    moreover have "n \<noteq> 1"
      sorry
    ultimately obtain q where q: "p \<noteq> q" "q < n"
      by atomize_elim presburger
    obtain a1 where
      "a'' = Sil a1"
    proof -
      let ?t = thesis
      from that consider ?t | a1 where "a'' = In a1 \<or> a'' = Out a1"
        by (cases a'') auto
      then show thesis
      proof cases
        case 1
        then show ?thesis .
      next
        case 2
        then have "a1 \<in> actions (As ! p)"
          by (tag \<open>TRANS ''silent''\<close>, force simp: actions_def)
        from 2 have "a'' \<in> syncs_of syncs p"
          apply standard
          subgoal
            using \<open>a1 \<in> _\<close> q \<open>p < n\<close> \<open>N' = _\<close> unfolding syncs_of_def N'_def t_to_s_def
            by (auto elim!: mk_syncs_In simp: lengths split: prod.split_asm)
         subgoal
            using \<open>a1 \<in> _\<close> q \<open>p < n\<close> \<open>N' = _\<close> unfolding syncs_of_def N'_def t_to_s_def
            by (auto elim!: mk_syncs_Out simp: lengths split: prod.split_asm)
          done
        with step_int show ?thesis
          by (tag "''internal''", simp)
      qed
    qed
    with \<open>a' = _\<close> have act:
      "conv_action n a' = Some (Simple_Network_Language.label.Internal a1)"
      by (auto simp: conv_action_def)
    note the_rule = Simple_Network_Language.step_u.step_int
    from act \<open>a'' = _\<close> step_int show ?thesis
      by (elim thesisI) (simp add: N'_def t_to_s_def split: prod.split_asm, rule the_rule)
  next
    case (step_sync sync syncs As ps as bs gs fs rs ls' B)
    note [tagged] = step_sync(3-)
    from \<open>N' = _\<close> assms(1-2) have lengths: "length As = n" "length L = n"
      by (simp add: N'_def t_to_s_def split: prod.split_asm)+
    have "sync \<in> syncs"
      by (tag "''sync''")
    with \<open>N' = _\<close> consider
      (bin) broadcast a p q t where
        "N = (broadcast, As, B)"
        "sync = mk_bin_sync (length As) a p q"
        "p < length As"
        "q < length As"
        "p \<noteq> q" "a \<notin> broadcast" "t\<in>set As" "a \<in> actions t" |
      (broadcast) broadcast a p where
        "N = (broadcast, As, B)"
        "sync  = mk_broadcast_sync (length As) a p"
        "p < length As" "a \<in> broadcast"
      unfolding N'_def t_to_s_def mk_syncs_def by (auto split: prod.split_asm)
    then show ?thesis
    proof cases
      case bin
      then have "p \<in> set ps" "q \<in> set ps"
         by (tag "''enabled''", simp add: mk_bin_sync_def)+
      moreover from bin have "i \<notin> set ps" if "i \<noteq> p" "i \<noteq> q" "i < n" for i
        using that by (tag "''only syncs''", simp add: mk_bin_sync_def lengths)
      ultimately have "set ps = {p, q}"
        by (tag "SEL ''range''", force simp: lengths)
      moreover from bin \<open>a' = _\<close> have
        "conv_action n a' = Some (Simple_Network_Language.label.Bin a)"
        apply (auto simp: conv_action_def lengths)
         apply (metis mk_bin_sync_neq_mk_broadcast_sync)
        by (smt (z3) mk_bin_sync_inj some_equality)
      moreover from \<open>set ps = {p, q}\<close> \<open>sync = _\<close> \<open>p \<noteq> q\<close> have "as p = In a" "as q = Out a"
        by - (tag "''actions''", tag "SEL ''range''", tag "SEL ''distinct''",
              force simp add: mk_bin_sync_def)+
      ultimately show ?thesis
        using bin \<open>set ps = {p, q}\<close>
        apply -
        apply (elim thesisI)
        apply simp
        apply (rule step_u.step_bin)
                          apply (all \<open>assumption?\<close>)
                          preferT \<open>''not broadcast''\<close> apply (tag, assumption)
                         apply (tag \<open>TRANS ''sync''\<close> \<open>SEL ''range''\<close>, fastforce)
                        apply (tag \<open>TRANS ''sync''\<close> \<open>SEL ''range''\<close>, fastforce)
                       apply (tag, fastforce)
                      apply (tag, fastforce)
                     apply (tag, fastforce)
                    apply (tag, fastforce)
                   apply (tag, fastforce)
                  apply (tag, fastforce)
                 apply (tag, fastforce)
                apply (tag, fastforce)
               apply (tag, simp add: lengths; fail)
              apply (tag, simp add: lengths; fail)
             apply (tag, simp add: lengths; fail)
            preferT \<open>''bounded''\<close> apply (tag, assumption)
        subgoal new_loc
          apply tag \<comment> \<open>provable, consider possible orderings of \<open>p, q\<close>\<close>
          sorry
        subgoal new_valuation
          apply tag \<comment> \<open>provable, consider possible orderings of \<open>p, q\<close>\<close>
          sorry
        \<comment> \<open>The remaining two goals again expose the trouble with ordering updates.\<close>
        sorry
    next
      case broadcast
      note the_rule = step_u.step_broad[where
          ps = "remove1 p ps" and bs = bs and gs = gs and fs = fs and rs = rs and ls' = ls']
      from broadcast have "p \<in> set ps"
        by (tag "''enabled''", simp add: mk_broadcast_sync_def)
      moreover from broadcast \<open>a' = _\<close> have
        "conv_action n a' = Some (Simple_Network_Language.label.Broad a)"
        apply (auto simp: conv_action_def lengths)
         apply (metis mk_bin_sync_neq_mk_broadcast_sync)
        by (smt (z3) mk_broadcast_sync_inj some_equality)
      moreover from \<open>p \<in> set ps\<close> \<open>sync = _\<close> have "as p = Out a" "\<forall>q < n. q \<noteq> p \<longrightarrow> as q = In a"
          "\<forall>q < n. q \<noteq> p \<longrightarrow> sync ! q = Some (In a, False)"
        by - (tag \<open>''actions''\<close> \<open>SEL ''range''\<close>, force simp: mk_broadcast_sync_def lengths)+
      ultimately show ?thesis
        using broadcast
        apply (elim thesisI)
        apply simp
        apply (rule the_rule)
                            apply (all \<open>assumption?\<close>)
                            apply (tag, assumption)
                           preferT \<open>TRANS ''out''\<close> apply (tag \<open>TRANS ''sync''\<close>, fastforce)
                          preferT \<open>TRANS ''in''\<close>
                            apply (tag \<open>TRANS ''sync''\<close> \<open>SEL ''range''\<close> \<open>SEL ''distinct''\<close>, force simp: lengths)
                         preferT \<open>''committed''\<close> apply (tag \<open>SEL ''distinct''\<close>, fastforce)
                        apply (tag, fastforce)
                       apply (tag, fastforce)
                      apply (tag, fastforce)
                     apply (tag, fastforce)
        preferT \<open>''maximal''\<close>
                    apply (tag \<open>SEL ''distinct''\<close> \<open>''only syncs''\<close>, simp, simp only: lengths, metis)
                   apply (tag, fastforce)
                  apply (tag, fastforce)
                 preferT \<open>SEND ''range''\<close> apply (tag, simp add: lengths; fail)
                apply (tag \<open>SEL ''distinct''\<close>, simp, blast)
               apply (tag \<open>SEL ''distinct''\<close>, simp; fail)
              apply (tag \<open>SEL ''distinct''\<close>, simp; fail)
        apply (tag \<open>SEL ''distinct''\<close>, erule sorted_remove1; fail)
        preferT \<open>''bounded''\<close> apply (tag, assumption)
        subgoal new_loc
          apply tag \<comment> \<open>provable, consider possible orderings of \<open>p, q\<close>\<close>
          sorry
        subgoal new_valuation
          apply tag \<comment> \<open>provable, consider possible orderings of \<open>p, q\<close>\<close>
          sorry
        \<comment> \<open>The remaining two goals again expose the trouble with ordering updates.\<close>
        sorry
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
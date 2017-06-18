theory Stream_More
  imports
    "~~/src/HOL/Library/Stream"
    "~~/src/HOL/Library/Linear_Temporal_Logic_on_Streams"
    "~~/src/HOL/Library/Rewrite"
    "Instantiate_Existentials"
    "Sequence"
begin

section \<open>Additional Theorems on Stream and LTL\<close>

subsection \<open>stake, sdrop\<close>
lemma set_sset_stake[intro]:
  "set (stake n xs) \<subseteq> sset xs"
  by (rewrite in \<open>_ \<subseteq> \<hole>\<close> stake_sdrop[of n, symmetric]; simp del: stake_sdrop)

(* XXX Unused here, move to distribution? *)
lemma sset_sdrop:
  "sset (sdrop n xs) \<subseteq> sset xs"
  by (rewrite in \<open>_ \<subseteq> \<hole>\<close> stake_sdrop[of n, symmetric]; simp del: stake_sdrop)

lemma stream_all_coinduct[consumes 1, case_names step, coinduct pred: stream_all]:
  assumes "P xs" "\<And> xs. P xs \<Longrightarrow> R (shd xs) \<and> P (stl xs)"
  shows "stream_all R xs"
  unfolding stream_all_def
  apply (rule allI)
  subgoal for n
    using assms(1)
    by (induction n arbitrary: xs) (auto dest: assms(2))
  done

lemma set_stake_snth:
  "\<exists> n' < n. xs !! n' = x" if "x \<in> set (stake n xs)"
  using that unfolding in_set_conv_nth by auto

lemma list_all_stake_least:
  "list_all (Not \<circ> P) (stake (LEAST n. P (xs !! n)) xs)" (is "?G") if "\<exists> n. P (xs !! n)"
proof (rule ccontr)
  let ?n = "LEAST n. P (xs !! n)"
  assume "\<not> ?G"
  then have "\<exists> x \<in> set (stake ?n xs). P x" unfolding list_all_iff by auto
  then obtain n' where "n' < ?n" "P (xs !! n')" by (auto dest: set_stake_snth)
  with Least_le[of "\<lambda> n. P (xs !! n)" n'] show False by auto
qed


subsection \<open>@{term stream_all}/@{term pred_stream}, @{term stream_all2}, @{term sset}\<close>

lemma stream_all2_Cons1:
  "stream_all2 P (y ## ys) xs \<longleftrightarrow> (\<exists> x xs'. xs = x ## xs' \<and> P y x \<and> stream_all2 P ys xs')"
  by (cases xs) auto

lemma stream_all2_Cons2:
  "stream_all2 P xs (y ## ys) \<longleftrightarrow> (\<exists> x xs'. xs = x ## xs' \<and> P x y \<and> stream_all2 P xs' ys)"
  by (cases xs) auto

lemma stream_all2_tail:
  "stream_all2 P xs2 ys2" if "stream_all2 P (xs1 @- xs2) (ys1 @- ys2)" "length xs1 = length ys1"
  using that proof (induction xs1 arbitrary: ys1)
  case Nil
  then show ?case by simp
next
  case (Cons a xs1 ys1)
  then show ?case by (cases ys1) auto
qed

lemma stream_all2_stlD:
  "stream_all2 P (stl xs) (stl ys)" if "stream_all2 P xs ys"
  using that stream.rel_sel by blast

lemma alw_stream_all2_mono:
  assumes "stream_all2 P xs ys" "alw Q xs" "\<And> xs ys. stream_all2 P xs ys \<Longrightarrow> Q xs \<Longrightarrow> R ys"
  shows "alw R ys"
  using assms by (coinduction arbitrary: xs ys) (auto dest: stream_all2_stlD)

lemma stream_all2_sset1:
  "\<forall> x \<in> sset xs. \<exists> a \<in> sset as. P x a" if "stream_all2 P xs as"
  using that proof -
  have "pred_stream (\<lambda> x. \<exists> a \<in> S. P x a) xs" if "sset as \<subseteq> S" for S
    using that \<open>stream_all2 P xs as\<close>
  proof (coinduction arbitrary: xs as)
    case (stream_pred x ys xs as)
    then show ?case by (cases as) auto
  qed
  then show ?thesis unfolding stream.pred_set by auto
qed

lemma stream_all2_sset2:
  "\<forall> a \<in> sset as. \<exists> x \<in> sset xs. P x a" if "stream_all2 P xs as"
  using that proof -
  have "pred_stream (\<lambda> a. \<exists> x \<in> S. P x a) as" if "sset xs \<subseteq> S" for S
    using that \<open>stream_all2 P xs as\<close>
  proof (coinduction arbitrary: xs as)
    case (stream_pred x ys xs as)
    then show ?case by (cases xs) auto
  qed
  then show ?thesis unfolding stream.pred_set by auto
qed

lemma pred_stream_flat_coinduct[case_names pred_stream_flat, consumes 1]:
  assumes "R ws" and "\<And> w ws. R (w ## ws) \<Longrightarrow> w \<noteq> [] \<and> list_all P w \<and> R ws"
  shows "pred_stream P (flat ws)"
  using assms(1)
proof (coinduction arbitrary: ws rule: stream_pred_coinduct_shift)
  case (stream_pred ws)
  then show ?case by (cases ws) (auto 4 4 dest!: assms(2))
qed

lemma stream_all_eq_pred_stream:
  "stream_all = pred_stream"
  unfolding stream_pred_snth stream_all_def ..

lemma alw_holds_pred_stream_iff:
  "alw (holds P) xs \<longleftrightarrow> pred_stream P xs"
  by (simp add: alw_iff_sdrop stream_pred_snth)



subsection \<open>Büchi properties\<close>

abbreviation "alw_ev P \<equiv> alw (ev P)"

lemma alw_ev_coinduct[case_names alw_ev, consumes 1, coinduct pred: alw_ev]:
  assumes "R w" and "\<And> w. R w \<Longrightarrow> \<exists> u v. w = u @- v \<and> u \<noteq> [] \<and> P v \<and> R v"
  shows "alw_ev P w"
proof -
  from \<open>R w\<close> have "\<exists> u v. w = u @- v \<and> R v" by (inst_existentials "[] :: 'a list") auto
  then show ?thesis proof (coinduction arbitrary: w)
    case (alw w)
    then obtain u v where "w = u @- v" "R v" by auto
    from assms(2)[OF \<open>R v\<close>] obtain v1 v2 where "v = v1 @- v2" "v1 \<noteq> []" "P v2" "R v2"
      by auto
    with \<open>w = _\<close> have "ev P w" by (auto intro: ev_shift)
    with \<open>R v2\<close> show ?case
      apply (inst_existentials w)
        apply simp+
      apply (rule disjI1)
      apply (inst_existentials "tl (u @ v1)" v2)
      unfolding \<open>w = _\<close> \<open>v = _\<close> using \<open>v1 \<noteq> []\<close> by auto
  qed
qed

lemma alw_ev_flat_coinduct[case_names alw_ev_flat, consumes 1]:
  assumes "R xss" and "\<And> xs xss. R (xs ## xss) \<Longrightarrow> (\<exists> x \<in> set xs. P x) \<and> R xss"
  shows "alw (ev (holds P)) (flat xss)"
proof -
  from assms have "R (stl xss)" by (metis stream.exhaust_sel)
  moreover from assms have "shd xss \<noteq> []" by (cases xss) fastforce+
  ultimately show ?thesis
  proof (coinduction arbitrary: xss)
    case (alw_ev xss)
    obtain xs yss where "stl xss = xs ## yss" by (metis stream.exhaust)
    with assms(2) \<open>R (stl xss)\<close> obtain x where "x \<in> set xs" "P x" "R yss" by auto
    from \<open>x \<in> set xs\<close> obtain xs1 xs2 where "xs = xs1 @ [x] @ xs2"
      by atomize_elim (simp add: split_list)
    with \<open>P x\<close> \<open>stl xss = _\<close> \<open>stl xss = _\<close> \<open>shd xss \<noteq> []\<close> \<open>R yss\<close> show ?case
      apply (inst_existentials "shd xss @ xs1" "(x # xs2) @- flat yss")
         apply (rewrite in \<open>flat xss\<close> stream.collapse[symmetric])
         apply (cases "shd xss"; simp; fail)
        apply (simp; fail)
       apply (simp; fail)
      apply (inst_existentials "(x # xs2) ## yss")
      by auto
  qed
qed

lemma alw_ev_HLD_cycle:
  "alw_ev (HLD a) xs" if "stream_all2 op \<in> xs (cycle as)" "a \<in> set as"
  using that
  unfolding HLD_def proof (coinduction arbitrary: xs as)
  case prems: (alw_ev xs as)
  from this(2) obtain as1 as2 where "as = as1 @ a # as2" by (auto simp: in_set_conv_decomp)
  then have "sdrop (length as) (cycle as) = cycle as"
    by (subst cycle_decomp) (auto simp: sdrop_shift)
  moreover have "sdrop (length as1) (cycle as) = cycle (a # as2 @ as1)"
    unfolding \<open>as = _\<close>
    apply (subst sdrop_cycle)
     apply (simp; fail)
    by (subst rotate_drop_take, simp)
  ultimately have "sdrop (length as + length as1) (cycle as) = cycle (a # as2 @ as1)"
    unfolding sdrop_add[symmetric] by simp
  with prems have "stream_all2 op \<in> (sdrop (length as + length as1) xs) (cycle (a # as2 @ as1))"
    apply (subst (asm) stake_sdrop[symmetric, of _ "length as + length as1"])
    apply (rewrite at \<open>cycle as\<close> in asm stake_sdrop[symmetric, of _ "length as + length as1"])
    by (drule stream_all2_tail; simp)
  with prems show ?case
    apply (inst_existentials "stake (length as + length as1) xs" "sdrop (length as + length as1) xs")
       apply simp
      apply force
     apply (subst (asm) cycle_Cons, simp only: stream_all2_Cons2)
    by force+
qed

lemma alw_ev_mono:
  assumes "alw_ev \<phi> xs" and "\<And> xs. \<phi> xs \<Longrightarrow> \<psi> xs"
  shows "alw_ev \<psi> xs"
  by (rule alw_mp[OF assms(1)]) (auto intro: ev_mono assms(2) simp: alw_iff_sdrop)

lemma finite_sset_decomp:
  assumes "finite (sset xs)"
  obtains x ws ys zs where "xs = ws @- x ## ys @- x ## zs"
proof -
  let ?n = "card (sset xs) + 1"
  let ?ys = "stake ?n xs"
  have "set ?ys \<subseteq> sset xs" ..
  then have "card (set ?ys) \<le> card (sset xs)"
    using assms card_mono by blast
  then have "card (set ?ys) < ?n" by auto
  also have "?n = length ?ys" by auto
  finally have "\<not> distinct ?ys"
    using distinct_card by fastforce
  then obtain x ws ys zs where "?ys = ws @ x # ys @ x # zs"
    using not_distinct_decomp by fastforce
  from this[symmetric] have "xs = \<dots> @- sdrop ?n xs"
    by (simp only: stake_sdrop)
  then show ?thesis
    by (auto intro: that)
qed


subsection \<open>sfilter, wait, nxt\<close>

lemma nxt_holds_iff_snth: "(nxt ^^ y) (holds P) xs \<longleftrightarrow> P (xs !! y)"
  by (induction y arbitrary: xs; simp)

lemma wait_LEAST:
  "wait (holds P) xs = (LEAST n. P (xs !! n))" unfolding wait_def nxt_holds_iff_snth ..

lemma filter_list_all_iff:
  "filter P xs = [] \<longleftrightarrow> list_all (Not \<circ> P) xs"
  by (induction xs) auto

lemma sfilter_SCons_decomp:
  assumes "sfilter P xs = x ## zs" "ev (holds P) xs"
  shows "\<exists> ys' zs'. xs = ys' @- x ## zs' \<and> list_all (Not o P) ys' \<and> P x \<and> sfilter P zs' = zs"
proof -
  from ev_imp_shift[OF assms(2)] obtain as bs where "xs = as @- bs" "holds P bs"
    by auto
  then have "P (shd bs)" by auto
  with \<open>xs = _\<close> have "\<exists> n. P (xs !! n)" using assms(2) sdrop_wait by fastforce
  from sdrop_while_sdrop_LEAST[OF this] have *:
    "sdrop_while (Not \<circ> P) xs = sdrop (LEAST n. P (xs !! n)) xs" .
  let ?xs = "sdrop_while (Not \<circ> P) xs" let ?n = "LEAST n. P (xs !! n)"
  from assms(1) have "x = shd ?xs" "zs = sfilter P (stl ?xs)"
    by (subst (asm) sfilter.ctr; simp)+
  have "xs = stake ?n xs @- sdrop ?n xs" by (simp add: stake_sdrop)
  moreover have "P x" using assms(1) unfolding sfilter_eq[OF assms(2)] ..
  moreover from \<open>\<exists> n. P _\<close> have "list_all (Not o P) (stake ?n xs)" by (rule list_all_stake_least)
  ultimately show ?thesis
    using \<open>x = _\<close> \<open>zs = _\<close> *[symmetric] by (inst_existentials "stake ?n xs" "stl ?xs") auto
qed

lemma sfilter_SCons_decomp':
  assumes "sfilter P xs = x ## zs" "ev (holds P) xs"
  shows
    "list_all (Not o P) (stake (wait (holds P) xs) xs)" (is "?G1")
    "P x"
    "\<exists> zs'. xs = stake (wait (holds P) xs) xs @- x ## zs' \<and> sfilter P zs' = zs" (is "?G2")
proof -
  from ev_imp_shift[OF assms(2)] obtain as bs where "xs = as @- bs" "holds P bs"
    by auto
  then have "P (shd bs)" by auto
  with \<open>xs = _\<close> have "\<exists> n. P (xs !! n)" using assms(2) sdrop_wait by fastforce thm sdrop_wait
  from sdrop_while_sdrop_LEAST[OF this] have *:
    "sdrop_while (Not \<circ> P) xs = sdrop (LEAST n. P (xs !! n)) xs" .
  let ?xs = "sdrop_while (Not \<circ> P) xs" let ?n = "wait (holds P) xs"
  from assms(1) have "x = shd ?xs" "zs = sfilter P (stl ?xs)"
    by (subst (asm) sfilter.ctr; simp)+
  have "xs = stake ?n xs @- sdrop ?n xs" by (simp add: stake_sdrop)
  moreover show "P x" using assms(1) unfolding sfilter_eq[OF assms(2)] ..
  moreover from \<open>\<exists> n. P _\<close> show "list_all (Not o P) (stake ?n xs)"
    by (auto intro: list_all_stake_least simp: wait_LEAST)
  ultimately show ?G2
    using \<open>x = _\<close> \<open>zs = _\<close> *[symmetric] by (inst_existentials "stl ?xs") (auto simp: wait_LEAST)
qed

lemma sfilter_shift_decomp:
  assumes "sfilter P xs = ys @- zs" "alw (ev (holds P)) xs"
  shows "\<exists> ys' zs'. xs = ys' @- zs' \<and> filter P ys' = ys \<and> sfilter P zs' = zs"
  using assms(1,2)
proof (induction ys arbitrary: xs)
  case Nil
  then show ?case by (inst_existentials "[] :: 'a list" xs; simp)
next
  case (Cons y ys)
  from alw_ev_imp_ev_alw[OF \<open>alw (ev _) xs\<close>] have "ev (holds P) xs"
    by (auto elim: ev_mono)
  with Cons.prems(1) sfilter_SCons_decomp[of P xs y "ys @- zs"] guess ys' zs' by clarsimp
  note guessed = this
  then have "sfilter P zs' = ys @- zs" by auto
  from \<open>alw (ev _) xs\<close> \<open>xs = _\<close> have "alw (ev (holds P)) zs'"
    by (metis ev.intros(2) ev_shift not_alw_iff stream.sel(2))
  from Cons.IH[OF \<open>sfilter P zs' = _\<close> this] guess zs1 zs2 by clarsimp
  with guessed show ?case
    by (inst_existentials "ys' @ y # zs1" zs2; simp add: filter_list_all_iff)
qed

lemma finite_sset_sfilter_decomp:
  assumes "finite (sset (sfilter P xs))" "alw (ev (holds P)) xs"
  obtains x ws ys zs where "xs = ws @- x ## ys @- x ## zs" "P x"
proof atomize_elim
  let ?xs = "sfilter P xs"
  from finite_sset_decomp[OF assms(1)] guess x ws ys zs .
  note guessed1 = this
  from sfilter_shift_decomp[OF this assms(2)] guess ys' zs' by clarsimp
  note guessed2 = this
  then have "ev (holds P) zs'" using alw_shift assms(2) by blast
  from sfilter_SCons_decomp[OF guessed2(2) this] guess zs1 zs2 by clarsimp
  note guessed3 = this
  have "alw (ev (holds P)) zs2"
    by (metis alw_ev_stl alw_shift assms(2) guessed2(1) guessed3(1) stream.sel(2))
  from sfilter_shift_decomp[OF guessed3(4) this] guess zs3 zs4 by clarsimp
  note guessed4 = this
  have "ev (holds P) zs4"
    using \<open>alw (ev (holds P)) zs2\<close> alw_shift guessed4(1) by blast
  from sfilter_SCons_decomp[OF guessed4(2) this] guess zs5 zs6 by clarsimp
  with guessed1 guessed2 guessed3 guessed4 show "\<exists>ws x ys zs. xs = ws @- x ## ys @- x ## zs \<and> P x"
    by (inst_existentials "ys' @ zs1" x "zs3 @ zs5" zs6; simp)
qed

lemma sfilter_shd_LEAST:
  "shd (sfilter P xs) = xs !! (LEAST n. P (xs !! n))" if "ev (holds P) xs"
proof -
  from sdrop_wait[OF \<open>ev _ xs\<close>] have "\<exists> n. P (xs !! n)" by auto
  from sdrop_while_sdrop_LEAST[OF this] show ?thesis by simp
qed

lemma alw_nxt_holds_cong:
  "(nxt ^^ n) (holds (\<lambda>x. P x \<and> Q x)) xs = (nxt ^^ n) (holds Q) xs" if "alw (holds P) xs"
  using that unfolding nxt_holds_iff_snth alw_iff_sdrop by simp

lemma alw_wait_holds_cong:
  "wait (holds (\<lambda>x. P x \<and> Q x)) xs = wait (holds Q) xs" if "alw (holds P) xs"
  unfolding wait_def alw_nxt_holds_cong[OF that] ..

lemma alw_sfilter:
  "sfilter (\<lambda> x. P x \<and> Q x) xs = sfilter Q xs" if "alw (holds P) xs" "alw (ev (holds Q)) xs"
  using that
proof (coinduction arbitrary: xs)
  case prems: stream_eq
  from prems(3,4) have ev_one: "ev (holds (\<lambda>x. P x \<and> Q x)) xs"
    by (subst ev_cong[of _ _ _ "holds Q"]) (assumption | auto)+
  from prems have "a = shd (sfilter (\<lambda>x. P x \<and> Q x) xs)" "b = shd (sfilter Q xs)"
    by (metis stream.sel(1))+
  with prems(3,4) have
    "a = xs !! (LEAST n. P (xs !! n) \<and> Q (xs !! n))" "b = xs !! (LEAST n. Q (xs !! n))"
    using ev_one by (auto 4 3 dest: sfilter_shd_LEAST)
  with alw_wait_holds_cong[unfolded wait_LEAST, OF \<open>alw (holds P) xs\<close>] have "a = b" by simp
  from sfilter_SCons_decomp'[OF prems(1)[symmetric], OF ev_one] guess u2 by clarsimp
  note guessed_a = this
  have "ev (holds Q) xs" using prems(4) by blast
  from sfilter_SCons_decomp'[OF prems(2)[symmetric], OF this] guess v2 by clarsimp
  with guessed_a \<open>a = b\<close> show ?case
    apply (intro conjI exI)
        apply assumption+
      apply (simp add: alw_wait_holds_cong[OF prems(3)], metis shift_left_inj stream.inject)
    by (metis alw.cases alw_shift prems(3,4) stream.sel(2))+
qed

lemma alw_ev_holds_mp:
  "alw (holds P) xs \<Longrightarrow> ev (holds Q) xs \<Longrightarrow> ev (holds (\<lambda>x. P x \<and> Q x)) xs"
  by (subst ev_cong, assumption) auto

lemma alw_ev_conjI:
  "alw_ev (holds (\<lambda> x. P x \<and> Q x)) xs" if "alw (holds P) xs" "alw (ev (holds Q)) xs"
  using that(2,1) by - (erule alw_mp, coinduction arbitrary: xs, auto intro: alw_ev_holds_mp)

lemma append_single_shift:
  "(xs @ [x]) @- ys = xs @- x ## ys"
  by simp

lemma alw_ev_sfilter_mono:
  assumes alw_ev: "alw (ev (holds P)) xs"
    and mono: "\<And> x. P x \<Longrightarrow> Q x"
  shows "stream_all Q (sfilter P xs)"
  using alw_ev
proof (coinduction arbitrary: xs)
  case (step xs)
  then have "ev (holds P) xs" by auto
  have "sfilter P xs = shd (sfilter P xs) ## stl (sfilter P xs)"
    by (cases "sfilter P xs") auto
  from sfilter_SCons_decomp[OF this \<open>ev (holds P) xs\<close>] guess ys' zs' by clarsimp
  then show ?case
    by (inst_existentials zs') (auto intro: mono, metis alw_shift append_single_shift local.step)
qed

lemma sset_sfilter:
  "sset (sfilter P xs) \<subseteq> sset xs" if "alw_ev (holds P) xs"
proof -
  have "alw (holds (\<lambda> x. x \<in> sset xs)) xs" by (simp add: alw_iff_sdrop)
  with \<open>alw_ev _ _\<close> alw_sfilter[OF this \<open>alw_ev _ _\<close>, symmetric] have
    "\<forall> x \<in> sset (sfilter P xs). x \<in> sset xs"
    unfolding stream_all_iff[symmetric]
    by (simp only:) (rule alw_ev_sfilter_mono; auto intro: alw_ev_conjI)
  then show ?thesis by blast
qed


subsection \<open>More stuff for Cava/Sequence\<close>

lemma infs_cycle:
  "infs (set xs) (cycle xs)" if "xs \<noteq> []"
  by (rule infs_sset) (simp add: that)


subsection \<open>New definitions\<close>

abbreviation "sgenerate f x xs \<equiv> x ## sscan (\<lambda> x y. f y x) xs x"

end (* Theory *)
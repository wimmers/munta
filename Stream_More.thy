theory Stream_More
  imports
    "~~/src/HOL/Library/Stream"
    "~~/src/HOL/Library/Linear_Temporal_Logic_on_Streams"
    "~~/src/HOL/Library/Rewrite"
    Instantiate_Existentials
begin

lemma stream_all_coinduct[consumes 1, case_names step, coinduct pred: stream_all]:
  assumes "P xs" "\<And> xs. P xs \<Longrightarrow> R (shd xs) \<and> P (stl xs)"
  shows "stream_all R xs"
  unfolding stream_all_def
  apply (rule allI)
  subgoal for n
    using assms(1)
    by (induction n arbitrary: xs) (auto dest: assms(2))
  done

lemma set_sset_stake[intro]:
  "set (stake n xs) \<subseteq> sset xs"
  by (rewrite in \<open>_ \<subseteq> \<hole>\<close> stake_sdrop[of n, symmetric]) auto

(* XXX Unused here, move to distribution? *)
lemma sset_sdrop:
  "sset (sdrop n xs) \<subseteq> sset xs"
  by (rewrite in \<open>_ \<subseteq> \<hole>\<close> stake_sdrop[of n, symmetric]) auto

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

lemma nxt_holds_iff_snth: "(nxt ^^ y) (holds P) xs \<longleftrightarrow> P (xs !! y)"
  by (induction y arbitrary: xs; simp)

lemma wait_LEAST:
  "wait (holds P) xs = (LEAST n. P (xs !! n))" unfolding wait_def nxt_holds_iff_snth ..

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

lemma filter_list_all_iff:
  "filter P xs = [] \<longleftrightarrow> list_all (Not \<circ> P) xs"
  by (induction xs) auto

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

lemma append_single_shift:
  "(xs @ [x]) @- ys = xs @- x ## ys"
  by simp

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

primcorec sgenerate where
  "shd (sgenerate f x ys) = x"
| "stl (sgenerate f x ys) = sgenerate f (f x (shd ys)) (stl ys)"

lemma sgenerate_Cons:
  "sgenerate f x (y ## ys) = x ## sgenerate f (f x y) ys"
  by (subst sgenerate.ctr) simp

end (* Theory *)
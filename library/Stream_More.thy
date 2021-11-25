theory Stream_More
imports
  Transition_Systems_and_Automata.Sequence_LTL
  Instantiate_Existentials
  "HOL-Library.Rewrite"
begin

lemma list_all_stake_least:
  "list_all (Not \<circ> P) (stake (LEAST n. P (xs !! n)) xs)" (is "?G") if "\<exists> n. P (xs !! n)"
proof (rule ccontr)
  let ?n = "LEAST n. P (xs !! n)"
  assume "\<not> ?G"
  then have "\<exists> x \<in> set (stake ?n xs). P x" unfolding list_all_iff by auto
  then obtain n' where "n' < ?n" "P (xs !! n')" using set_stake_snth by metis
  with Least_le[of "\<lambda> n. P (xs !! n)" n'] show False by auto
qed

lemma alw_stream_all2_mono:
  assumes "stream_all2 P xs ys" "alw Q xs" "\<And> xs ys. stream_all2 P xs ys \<Longrightarrow> Q xs \<Longrightarrow> R ys"
  shows "alw R ys"
  using assms stream.rel_sel by (coinduction arbitrary: xs ys) (blast)

lemma alw_ev_HLD_cycle:
  assumes "stream_all2 (\<in>) xs (cycle as)" "a \<in> set as"
  shows "infs (\<lambda>x. x \<in> a) xs"
using assms(1)
proof (coinduct rule: infs_coinduct_shift)
  case (infs xs)
  have 1: "as \<noteq> []" using assms(2) by auto
  have 2:
    "list_all2 (\<in>) (stake (length as) xs) (stake (length as) (cycle as))"
    "stream_all2 (\<in>) (sdrop (length as) xs) (sdrop (length as) (cycle as))"
    using infs stream_rel_shift stake_sdrop length_stake by metis+
  have 3: "stake (length as) (cycle as) = as" using 1 by simp
  have 4: "sdrop (length as) (cycle as) = cycle as" using sdrop_cycle_eq 1 by this
  have 5: "set (stake (length as) xs) \<inter> a \<noteq> {}"
    using assms(2) 2(1) unfolding list.in_rel 3
    by (auto) (metis IntI empty_iff mem_Collect_eq set_zip_leftD split_conv subsetCE zip_map_fst_snd)
  show ?case using 2 5 unfolding 4
    by force
qed

lemma alw_ev_mono:
  assumes "alw (ev \<phi>) xs" and "\<And> xs. \<phi> xs \<Longrightarrow> \<psi> xs"
  shows "alw (ev \<psi>) xs"
  by (rule alw_mp[OF assms(1)]) (auto intro: ev_mono assms(2) simp: alw_iff_sdrop)

lemma alw_ev_lockstep:
  assumes
    "alw (ev (holds P)) xs" "stream_all2 Q xs as"
    "\<And> x a. P x \<Longrightarrow> Q x a \<Longrightarrow> R a"
  shows
    "alw (ev (holds R)) as"
  using assms(1,2)
  apply (coinduction arbitrary: xs as rule: alw.coinduct)
  apply auto
  subgoal
    by (metis alw.cases assms(3) ev_holds_sset stream_all2_sset1)
  subgoal
    by (meson alw.cases stream.rel_sel)
  done

subsection \<open>sfilter, wait, nxt\<close>

text \<open>Useful?\<close>
lemma nxt_holds_iff_snth: "(nxt ^^ i) (holds P) xs \<longleftrightarrow> P (xs !! i)"
  by (induction i arbitrary: xs; simp add: holds.simps)

text \<open>Useful?\<close>
lemma wait_LEAST:
  "wait (holds P) xs = (LEAST n. P (xs !! n))" unfolding wait_def nxt_holds_iff_snth ..

lemma sfilter_SCons_decomp:
  assumes "sfilter P xs = x ## zs" "ev (holds P) xs"
  shows "\<exists> ys' zs'. xs = ys' @- x ## zs' \<and> list_all (Not o P) ys' \<and> P x \<and> sfilter P zs' = zs"
proof -
  note [simp] = holds.simps
  from ev_imp_shift[OF assms(2)] obtain as bs where "xs = as @- bs" "holds P bs"
    by auto
  then have "P (shd bs)" by auto
  with \<open>xs = _\<close> have "\<exists> n. P (xs !! n)" using assms(2) sdrop_wait by fastforce
  from sdrop_while_sdrop_LEAST[OF this] have *:
    "sdrop_while (Not \<circ> P) xs = sdrop (LEAST n. P (xs !! n)) xs" .
  let ?xs = "sdrop_while (Not \<circ> P) xs" let ?n = "LEAST n. P (xs !! n)"
  from assms(1) have "x = shd ?xs" "zs = sfilter P (stl ?xs)"
    by (subst (asm) sfilter.ctr; simp)+
  have "xs = stake ?n xs @- sdrop ?n xs" by simp
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
  note [simp] = holds.simps
  from ev_imp_shift[OF assms(2)] obtain as bs where "xs = as @- bs" "holds P bs"
    by auto
  then have "P (shd bs)" by auto
  with \<open>xs = _\<close> have "\<exists> n. P (xs !! n)" using assms(2) sdrop_wait by fastforce thm sdrop_wait
  from sdrop_while_sdrop_LEAST[OF this] have *:
    "sdrop_while (Not \<circ> P) xs = sdrop (LEAST n. P (xs !! n)) xs" .
  let ?xs = "sdrop_while (Not \<circ> P) xs" let ?n = "wait (holds P) xs"
  from assms(1) have "x = shd ?xs" "zs = sfilter P (stl ?xs)"
    by (subst (asm) sfilter.ctr; simp)+
  have "xs = stake ?n xs @- sdrop ?n xs" by simp
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
  with Cons.prems(1) sfilter_SCons_decomp[of P xs y "ys @- zs"] obtain ys' zs' where decomp:
    "xs = ys' @- y ## zs'" "list_all (Not \<circ> P) ys'" "P y" "sfilter P zs' = ys @- zs"
    by clarsimp
  then have "sfilter P zs' = ys @- zs" by auto
  from \<open>alw (ev _) xs\<close> \<open>xs = _\<close> have "alw (ev (holds P)) zs'"
    by (metis ev.intros(2) ev_shift not_alw_iff stream.sel(2))
  from Cons.IH[OF \<open>sfilter P zs' = _\<close> this] obtain zs1 zs2 where
    "zs' = zs1 @- zs2" "filter P zs1 = ys" "sfilter P zs2 = zs"
    by clarsimp
  with decomp show ?case
    by (inst_existentials "ys' @ y # zs1" zs2; simp add: list.pred_set)
qed

lemma finite_sset_sfilter_decomp:
  assumes "finite (sset (sfilter P xs))" "alw (ev (holds P)) xs"
  obtains x ws ys zs where "xs = ws @- x ## ys @- x ## zs" "P x"
proof atomize_elim
  let ?xs = "sfilter P xs"
  have 1: "\<not> sdistinct (sfilter P xs)" using sdistinct_infinite_sset assms(1) by auto
  from not_sdistinct_decomp[OF 1] obtain ws ys x zs where guessed1:
    "sfilter P xs = ws @- x ## ys @- x ## zs" .
  from sfilter_shift_decomp[OF this assms(2)] obtain ys' zs' where guessed2:
    "xs = ys' @- zs'"
    "sfilter P zs' = x ## ys @- x ## zs"
    "ws = filter P ys'"
    by clarsimp
  then have "ev (holds P) zs'" using alw_shift assms(2) by blast
  from sfilter_SCons_decomp[OF guessed2(2) this] obtain zs1 zs2 where guessed3:
    "zs' = zs1 @- x ## zs2"
    "list_all (Not \<circ> P) zs1"
    "P x"
    "sfilter P zs2 = ys @- x ## zs"
    by clarsimp
  have "alw (ev (holds P)) zs2"
    by (metis alw_ev_stl alw_shift assms(2) guessed2(1) guessed3(1) stream.sel(2))
  from sfilter_shift_decomp[OF guessed3(4) this] obtain zs3 zs4 where guessed4:
    "zs2 = zs3 @- zs4"
    "sfilter P zs4 = x ## zs"
    "ys = filter P zs3"
    by clarsimp
  have "ev (holds P) zs4"
    using \<open>alw (ev (holds P)) zs2\<close> alw_shift guessed4(1) by blast
  from sfilter_SCons_decomp[OF guessed4(2) this] obtain zs5 zs6 where
    "zs4 = zs5 @- x ## zs6"
    "list_all (Not \<circ> P) zs5"
    "P x"
    "zs = sfilter P zs6"
    by clarsimp
  with guessed1 guessed2 guessed3 guessed4 show "\<exists>ws x ys zs. xs = ws @- x ## ys @- x ## zs \<and> P x"
    by (inst_existentials "ys' @ zs1" x "zs3 @ zs5" zs6; simp)
qed

text \<open>Useful?\<close>
lemma sfilter_shd_LEAST:
  "shd (sfilter P xs) = xs !! (LEAST n. P (xs !! n))" if "ev (holds P) xs"
proof -
  note [simp] = holds.simps
  from sdrop_wait[OF \<open>ev _ xs\<close>] have "\<exists> n. P (xs !! n)" by auto
  from sdrop_while_sdrop_LEAST[OF this] show ?thesis by simp
qed

lemma alw_nxt_holds_cong:
  "(nxt ^^ n) (holds (\<lambda>x. P x \<and> Q x)) xs = (nxt ^^ n) (holds Q) xs" if "alw (holds P) xs"
  using that unfolding nxt_holds_iff_snth alw_iff_sdrop by (simp add: holds.simps)

lemma alw_wait_holds_cong:
  "wait (holds (\<lambda>x. P x \<and> Q x)) xs = wait (holds Q) xs" if "alw (holds P) xs"
  unfolding wait_def alw_nxt_holds_cong[OF that] ..

lemma alw_sfilter:
  "sfilter (\<lambda> x. P x \<and> Q x) xs = sfilter Q xs" if "alw (holds P) xs" "alw (ev (holds Q)) xs"
  using that
proof (coinduction arbitrary: xs)
  case prems: stream_eq
  note [simp] = holds.simps
  from prems(3,4) have ev_one: "ev (holds (\<lambda>x. P x \<and> Q x)) xs"
    by (subst ev_cong[of _ _ _ "holds Q"]) (assumption | auto)+
  from prems have "a = shd (sfilter (\<lambda>x. P x \<and> Q x) xs)" "b = shd (sfilter Q xs)"
    by (metis stream.sel(1))+
  with prems(3,4) have
    "a = xs !! (LEAST n. P (xs !! n) \<and> Q (xs !! n))" "b = xs !! (LEAST n. Q (xs !! n))"
    using ev_one by (auto 4 3 dest: sfilter_shd_LEAST)
  with alw_wait_holds_cong[unfolded wait_LEAST, OF \<open>alw (holds P) xs\<close>] have "a = b" by simp
  from sfilter_SCons_decomp'[OF prems(1)[symmetric], OF ev_one] obtain u2 where guessed_a:
    "list_all (Not \<circ> (\<lambda>x. P x \<and> Q x)) (stake (wait (holds (\<lambda>x. P x \<and> Q x)) xs) xs)"
    "xs = stake (wait (holds (\<lambda>x. P x \<and> Q x)) xs) xs @- a ## u2"
    "u = sfilter (\<lambda>x. P x \<and> Q x) u2"
    by clarsimp
  have "ev (holds Q) xs" using prems(4) by blast
  from sfilter_SCons_decomp'[OF prems(2)[symmetric], OF this] obtain v2 where
    "list_all (Not \<circ> Q) (stake (wait (holds Q) xs) xs)"
    "xs = stake (wait (holds Q) xs) xs @- b ## v2"
    "v = sfilter Q v2"
    by clarsimp
  with guessed_a \<open>a = b\<close> show ?case
    apply (intro conjI exI)
        apply assumption+
      apply (simp add: alw_wait_holds_cong[OF prems(3)], metis shift_left_inj stream.inject)
    by (metis alw.cases alw_shift prems(3,4) stream.sel(2))+
qed

lemma alw_ev_holds_mp:
  "alw (holds P) xs \<Longrightarrow> ev (holds Q) xs \<Longrightarrow> ev (holds (\<lambda>x. P x \<and> Q x)) xs"
  by (subst ev_cong, assumption) (auto simp: holds.simps)

lemma alw_ev_conjI:
  "alw (ev (holds (\<lambda> x. P x \<and> Q x))) xs" if "alw (holds P) xs" "alw (ev (holds Q)) xs"
  using that(2,1) by - (erule alw_mp, coinduction arbitrary: xs, auto intro: alw_ev_holds_mp)

subsection \<open>Useful?\<close>

lemma alw_holds_pred_stream_iff:
  "alw (holds P) xs \<longleftrightarrow> pred_stream P xs"
  by (simp add: alw_iff_sdrop stream_pred_snth holds.simps)

lemma alw_holds_sset:
  "alw (holds P) xs = (\<forall> x \<in> sset xs. P x)"
  by (simp add: alw_holds_pred_stream_iff stream.pred_set)

lemma pred_stream_sfilter:
  assumes alw_ev: "alw (ev (holds P)) xs"
  shows "pred_stream P (sfilter P xs)"
  using alw_ev
proof (coinduction arbitrary: xs)
  case (stream_pred xs)
  then have "ev (holds P) xs" by auto
  have "sfilter P xs = shd (sfilter P xs) ## stl (sfilter P xs)"
    by (cases "sfilter P xs") auto
  from sfilter_SCons_decomp[OF this \<open>ev (holds P) xs\<close>] obtain ys' zs' where
    "xs = ys' @- shd (sdrop_while (Not \<circ> P) xs) ## zs'"
    "list_all (Not \<circ> P) ys'"
    "P (shd (sdrop_while (Not \<circ> P) xs))"
    "sfilter P zs' =
     sfilter P (stl (sdrop_while (Not \<circ> P) xs))"
    by clarsimp
  then show ?case
    apply (inst_existentials zs')
    apply (metis sfilter.simps(1) stream.sel(1) stream_pred(1))
    apply (metis scons_eq sfilter.simps(2) stream_pred(1))
    apply (metis alw_ev_stl alw_shift stream.sel(2) stream_pred(2))
    done
qed

lemma alw_ev_sfilter_mono:
  assumes alw_ev: "alw (ev (holds P)) xs"
    and mono: "\<And> x. P x \<Longrightarrow> Q x"
  shows "pred_stream Q (sfilter P xs)"
  using stream.pred_mono[of P Q] assms pred_stream_sfilter by blast

lemma sset_sfilter:
  "sset (sfilter P xs) \<subseteq> sset xs" if "alw (ev (holds P)) xs"
proof -
  have "alw (holds (\<lambda> x. x \<in> sset xs)) xs" by (simp add: alw_iff_sdrop holds.simps)
  with \<open>alw (ev _) _\<close> alw_sfilter[OF this \<open>alw (ev _) _\<close>, symmetric]
    have "pred_stream (\<lambda> x. x \<in> sset xs) (sfilter P xs)"
    by (simp) (rule alw_ev_sfilter_mono; auto intro: alw_ev_conjI)
  then have "\<forall> x \<in> sset (sfilter P xs). x \<in> sset xs" unfolding stream.pred_set by this
  then show ?thesis by blast
qed

lemma stream_all2_weaken:
  "stream_all2 Q xs ys" if "stream_all2 P xs ys" "\<And> x y. P x y \<Longrightarrow> Q x y"
  using that by (coinduction arbitrary: xs ys) auto

lemma stream_all2_SCons1:
  "stream_all2 P (x ## xs) ys = (\<exists>z zs. ys = z ## zs \<and> P x z \<and> stream_all2 P xs zs)"
  by (subst (3) stream.collapse[symmetric], simp del: stream.collapse, force)

lemma stream_all2_SCons2:
  "stream_all2 P xs (y ## ys) = (\<exists>z zs. xs = z ## zs \<and> P z y \<and> stream_all2 P zs ys)"
  by (subst stream.collapse[symmetric], simp del: stream.collapse, force)

lemma stream_all2_combine:
  "stream_all2 R xs zs" if
  "stream_all2 P xs ys" "stream_all2 Q ys zs" "\<And> x y z. P x y \<and> Q y z \<Longrightarrow> R x z"
  using that(1,2)
  by (coinduction arbitrary: xs ys zs)
     (auto intro: that(3) simp: stream_all2_SCons1 stream_all2_SCons2)

lemma stream_all2_shift1:
  "stream_all2 P (xs1 @- xs2) ys =
  (\<exists> ys1 ys2. ys = ys1 @- ys2 \<and> list_all2 P xs1 ys1 \<and> stream_all2 P xs2 ys2)"
  apply (induction xs1 arbitrary: ys)
   apply (simp; fail)
  apply (simp add: stream_all2_SCons1 list_all2_Cons1)
  apply safe
  subgoal for a xs1 ys z zs ys1 ys2
    by (inst_existentials "z # ys1" ys2; simp)
  subgoal for a xs1 ys ys1 ys2 z zs
    by (inst_existentials z "zs @- ys2" zs "ys2"; simp)
  done

lemma stream_all2_shift2:
  "stream_all2 P ys (xs1 @- xs2) =
  (\<exists> ys1 ys2. ys = ys1 @- ys2 \<and> list_all2 P ys1 xs1 \<and> stream_all2 P ys2 xs2)"
  by (meson list.rel_flip stream.rel_flip stream_all2_shift1)

lemma stream_all2_bisim:
  assumes "stream_all2 (\<in>) xs as" "stream_all2 (\<in>) ys as" "sset as \<subseteq> S"
  shows "stream_all2 (\<lambda> x y. \<exists> a. x \<in> a \<and> y \<in> a \<and> a \<in> S) xs ys"
  using assms
  apply (coinduction arbitrary: as xs ys)
  subgoal for a u b v as xs ys
    apply (rule conjI)
     apply (inst_existentials "shd as", auto simp: stream_all2_SCons1; fail)
    apply (inst_existentials "stl as", auto 4 3 simp: stream_all2_SCons1; fail)
    done
  done

end

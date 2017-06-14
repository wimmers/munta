(* Author: Julian Brunner *)
(* This is originally a part of the CAVA model checker *)
theory Sequence
imports
  "Basic"
  "~~/src/HOL/Library/Stream"
begin

  (* list basics *)

  declare upt_Suc[simp del]
  declare last.simps[simp del]
  declare butlast.simps[simp del]
  declare Cons_nth_drop_Suc[simp]

  lemma fold_const: "fold const xs a = last (a # xs)"
    by (induct xs arbitrary: a) (auto simp: last.simps)

  lemma take_Suc: "take (Suc n) xs = (if xs = [] then [] else hd xs # take n (tl xs))"
    by (simp add: take_Suc)

  lemma list_pred_cases:
    assumes "list_all P xs"
    obtains (nil) "xs = []" | (cons) y ys where "xs = y # ys" "P y" "list_all P ys"
    using assms by (cases xs) (auto)

  (* stream basics *)

  declare stream.map_id[simp]
  declare stream.set_map[simp]
  declare stream.set_sel(1)[intro!, simp]
  declare stream.pred_map[iff]
  declare stream.rel_map[iff]
  declare stake_sdrop[simp]
  declare stake_siterate[simp del]
  declare sdrop_snth[simp]
  declare flat_unfold[simp]

  lemma stream_rel_coinduct[case_names stream_rel, coinduct pred: stream_all2]:
    assumes "R u v"
    assumes "\<And> a u b v. R (a ## u) (b ## v) \<Longrightarrow> P a b \<and> R u v"
    shows "stream_all2 P u v"
    using assms by (coinduct) (metis stream.collapse)
  lemma stream_rel_coinduct_shift[case_names stream_rel, consumes 1]:
    assumes "R u v"
    assumes "\<And> u v. R u v \<Longrightarrow>
      \<exists> u\<^sub>1 u\<^sub>2 v\<^sub>1 v\<^sub>2. u = u\<^sub>1 @- u\<^sub>2 \<and> v = v\<^sub>1 @- v\<^sub>2 \<and> u\<^sub>1 \<noteq> [] \<and> v\<^sub>1 \<noteq> [] \<and> list_all2 P u\<^sub>1 v\<^sub>1 \<and> R u\<^sub>2 v\<^sub>2"
    shows "stream_all2 P u v"
  proof -
    have "\<exists> u\<^sub>1 u\<^sub>2 v\<^sub>1 v\<^sub>2. u = u\<^sub>1 @- u\<^sub>2 \<and> v = v\<^sub>1 @- v\<^sub>2 \<and> list_all2 P u\<^sub>1 v\<^sub>1 \<and> R u\<^sub>2 v\<^sub>2"
      using assms(1) by force
    then show ?thesis using assms(2) by (coinduct) (force elim: list.rel_cases)
  qed

  lemma stream_pred_coinduct[case_names stream_pred, coinduct pred: pred_stream]:
    assumes "R w"
    assumes "\<And> a w. R (a ## w) \<Longrightarrow> P a \<and> R w"
    shows "pred_stream P w"
    using assms unfolding stream.pred_rel eq_onp_def by (coinduction arbitrary: w) (auto)
  lemma stream_pred_coinduct_shift[case_names stream_pred, consumes 1]:
    assumes "R w"
    assumes "\<And> w. R w \<Longrightarrow> \<exists> u v. w = u @- v \<and> u \<noteq> [] \<and> list_all P u \<and> R v"
    shows "pred_stream P w"
  proof -
    have "\<exists> u v. w = u @- v \<and> list_all P u \<and> R v"
      using assms(1) by (metis list_all_simps(2) shift.simps(1))
    then show ?thesis using assms(2) by (coinduct) (force elim: list_pred_cases)
  qed

  lemmas stream_eq_coinduct[case_names stream_eq, coinduct pred: HOL.eq] =
    stream_rel_coinduct[where ?P = HOL.eq, unfolded stream.rel_eq]
  lemmas stream_eq_coinduct_shift[case_names stream_eq, consumes 1] =
    stream_rel_coinduct_shift[where ?P = HOL.eq, unfolded stream.rel_eq list.rel_eq]

  lemma sset_subset_stream_pred: "sset w \<subseteq> A \<longleftrightarrow> pred_stream (\<lambda> a. a \<in> A) w"
    unfolding stream.pred_set by auto
  lemma stream_pred_snth: "pred_stream P w \<longleftrightarrow> (\<forall> i. P (w !! i))"
    unfolding stream.pred_set sset_range by simp

  lemma eq_scons: "w = a ## v \<longleftrightarrow> a = shd w \<and> v = stl w" by auto
  lemma scons_eq: "a ## v = w \<longleftrightarrow> shd w = a \<and> stl w = v" by auto
  lemma eq_shift: "w = u @- v \<longleftrightarrow> stake (length u) w = u \<and> sdrop (length u) w = v"
    by (induct u arbitrary: w) (force+)
  lemma shift_eq: "u @- v = w \<longleftrightarrow> u = stake (length u) w \<and> v = sdrop (length u) w"
    by (induct u arbitrary: w) (force+)
  lemma scons_eq_shift: "a ## w = u @- v \<longleftrightarrow> ([] = u \<and> a ## w = v) \<or> (\<exists> u'. a # u' = u \<and> w = u' @- v)"
    by (cases u) (auto)
  lemma shift_eq_scons: "u @- v = a ## w \<longleftrightarrow> (u = [] \<and> v = a ## w) \<or> (\<exists> u'. u = a # u' \<and> u' @- v = w)"
    by (cases u) (auto)

  lemma smap_eq_scons[iff]: "smap f xs = y ## ys \<longleftrightarrow> f (shd xs) = y \<and> smap f (stl xs) = ys"
    using smap_ctr by metis
  lemma scons_eq_smap[iff]: "y ## ys = smap f xs \<longleftrightarrow> y = f (shd xs) \<and> ys = smap f (stl xs)"
    using smap_ctr by metis
  lemma smap_eq_shift[iff]:
    "smap f w = u @- v \<longleftrightarrow> (\<exists> w\<^sub>1 w\<^sub>2. w = w\<^sub>1 @- w\<^sub>2 \<and> map f w\<^sub>1 = u \<and> smap f w\<^sub>2 = v)"
    using sdrop_smap eq_shift stake_sdrop stake_smap by metis
  lemma shift_eq_smap[iff]:
    "u @- v = smap f w \<longleftrightarrow> (\<exists> w\<^sub>1 w\<^sub>2. w = w\<^sub>1 @- w\<^sub>2 \<and> u = map f w\<^sub>1 \<and> v = smap f w\<^sub>2)"
    using sdrop_smap eq_shift stake_sdrop stake_smap by metis

  lemma siterate_eq_scons[iff]: "siterate f s = a ## w \<longleftrightarrow> s = a \<and> siterate f (f s) = w"
    using siterate.ctr stream.inject by metis
  lemma scons_eq_siterate[iff]: "a ## w = siterate f s \<longleftrightarrow> a = s \<and> w = siterate f (f s)"
    using siterate.ctr stream.inject by metis

  lemma eqI_snth:
    assumes "\<And> i. u !! i = v !! i"
    shows "u = v"
    using assms by (coinduction arbitrary: u v) (metis stream.sel snth.simps)

  (* zip *)
(*
  notation zip (infixr "||" 51)

  declare zip_map_fst_snd[simp]

  (*
    we add a split rule for lists of pairs (in analogy to split_paired_all)
    this rule could simply be added to the simpset
    however, we want to add it as a safe simp rule, such that methods like safe and clarify use it
    to do so, we have to use safe_asm_full_simp_tac
    we also have to add the can_split matching logic to avoid looping
  *)
  lemma split_zip[no_atp]: "(\<And> x. PROP P x) \<equiv> (\<And> y z. length y = length z \<Longrightarrow> PROP P (y || z))"
  proof
    fix y z
    assume 1: "\<And> x. PROP P x"
    show "PROP P (y || z)" using 1 by this
  next
    fix x :: "('a \<times> 'b) list"
    assume 1: "\<And> y z. length y = length z \<Longrightarrow> PROP P (y || z)"
    have 2: "length (map fst x) = length (map snd x)" by simp
    have 3: "PROP P (map fst x || map snd x)" using 1 2 by this
    show "PROP P x" using 3 by simp
  qed

  ML
  {*
    local
      fun
        can_split (Const (@{const_name Pure.all}, _) $ Abs (_, Type (@{type_name list}, [T]), t)) =
          can HOLogic.dest_prodT T orelse can_split t |
        can_split (t $ u) = can_split t orelse can_split u |
        can_split (Abs (_, _, t)) = can_split t |
        can_split _ = false;
      val ss = simpset_of (put_simpset HOL_basic_ss @{context} addsimps
        [@{thm split_zip}, @{thm length_zip}, @{thm min.idem}]);
    in
      fun split_zip_tac ctxt = SUBGOAL (fn (t, i) =>
        if can_split t then safe_asm_full_simp_tac (put_simpset ss ctxt) i else no_tac);
    end;
  *}
  setup {* map_theory_claset (fn ctxt => ctxt addSbefore ("split_zip", split_zip_tac)) *}

  lemma split_zip_all[no_atp, iff]: "(\<forall> x. P x) \<longleftrightarrow> (\<forall> y z. length y = length z \<longrightarrow> P (y || z))" by auto
  lemma split_zip_ex[no_atp, iff]: "(\<exists> x. P x) \<longleftrightarrow> (\<exists> y z. length y = length z \<and> P (y || z))" by auto

  lemma last_zip[simp]:
    assumes "xs || ys \<noteq> []" "length xs = length ys"
    shows "last (xs || ys) = (last xs, last ys)"
  proof -
    have 1: "xs \<noteq> []" "ys \<noteq> []" using assms(1) by auto
    have "last (xs || ys) = (xs || ys) ! (length (xs || ys) - 1)" using last_conv_nth assms by blast
    also have "\<dots> = (xs ! (length (xs || ys) - 1), ys ! (length (xs || ys) - 1))" using assms 1 by simp
    also have "\<dots> = (xs ! (length xs - 1), ys ! (length ys - 1))" using assms(2) by simp
    also have "\<dots> = (last xs, last ys)" using last_conv_nth 1 by metis
    finally show ?thesis by this
  qed

  (* szip *)

  notation szip (infixr "|||" 51)

  declare szip_unfold[simp]

  lemma szip_smap_fst[simp]: "smap fst (xs ||| ys) = xs" by (coinduction arbitrary: xs ys) (auto)
  lemma szip_smap_snd[simp]: "smap snd (xs ||| ys) = ys" by (coinduction arbitrary: xs ys) (auto)
  lemma szip_smap[simp]: "smap fst zs ||| smap snd zs = zs" by (coinduction arbitrary: zs) (auto)

  (* see split_zip for explanation *)
  lemma split_szip[no_atp]: "(\<And> x. PROP P x) \<equiv> (\<And> y z. PROP P (y ||| z))"
  proof
    fix y z
    assume 1: "\<And> x. PROP P x"
    show "PROP P (y ||| z)" using 1 by this
  next
    fix x
    assume 1: "\<And> y z. PROP P (y ||| z)"
    have 2: "PROP P (smap fst x ||| smap snd x)" using 1 by this
    show "PROP P x" using 2 by simp
  qed

  ML
  {*
    local
      fun
        can_split (Const (@{const_name Pure.all}, _) $ Abs (_, Type (@{type_name stream}, [T]), t)) =
          can HOLogic.dest_prodT T orelse can_split t |
        can_split (t $ u) = can_split t orelse can_split u |
        can_split (Abs (_, _, t)) = can_split t |
        can_split _ = false;
      val ss = simpset_of (put_simpset HOL_basic_ss @{context} addsimps [@{thm split_szip}]);
    in
      fun split_szip_tac ctxt = SUBGOAL (fn (t, i) =>
        if can_split t then safe_asm_full_simp_tac (put_simpset ss ctxt) i else no_tac);
    end;
  *}
  setup {* map_theory_claset (fn ctxt => ctxt addSbefore ("split_szip", split_szip_tac)) *}

  lemma split_szip_all[no_atp, iff]: "(\<forall> x. P x) \<longleftrightarrow> (\<forall> y z. P (y ||| z))" by auto
  lemma split_szip_ex[no_atp, iff]: "(\<exists> x. P x) \<longleftrightarrow> (\<exists> y z. P (y ||| z))" by auto

  lemma szip_shift[simp]:
    assumes "length u = length s"
    shows "u @- v ||| s @- t = (u || s) @- (v ||| t)"
    using assms by (simp add: eq_shift)

  lemma szip_sset_fst[simp]: "fst ` sset (u ||| v) = sset u" by (metis stream.set_map szip_smap_fst)
  lemma szip_sset_snd[simp]: "snd ` sset (u ||| v) = sset v" by (metis stream.set_map szip_smap_snd)
  lemma szip_sset_elim[elim]:
    assumes "(a, b) \<in> sset (u ||| v)"
    obtains "a \<in> sset u" "b \<in> sset v"
    using assms by (metis image_eqI fst_conv snd_conv szip_sset_fst szip_sset_snd)
  lemma szip_sset[simp]: "sset (u ||| v) \<subseteq> sset u \<times> sset v" by auto

  lemma sset_szip_finite[iff]: "finite (sset (u ||| v)) \<longleftrightarrow> finite (sset u) \<and> finite (sset v)"
  proof safe
    assume 1: "finite (sset (u ||| v))"
    have 2: "finite (fst ` sset (u ||| v))" using 1 by blast
    have 3: "finite (snd ` sset (u ||| v))" using 1 by blast
    show "finite (sset u)" using 2 by simp
    show "finite (sset v)" using 3 by simp
  next
    assume 1: "finite (sset u)" "finite (sset v)"
    have "sset (u ||| v) \<subseteq> sset u \<times> sset v" by simp
    also have "finite \<dots>" using 1 by simp
    finally show "finite (sset (u ||| v))" by this
  qed
*)

  (* scans *)

  fun scan :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b list" where
    "scan f [] a = []" | "scan f (x # xs) a = f x a # scan f xs (f x a)"

  lemma scan_append[simp]: "scan f (xs @ ys) a = scan f xs a @ scan f ys (fold f xs a)"
    by (induct xs arbitrary: a) (auto)

  lemma scan_eq_nil[iff]: "scan f xs a = [] \<longleftrightarrow> xs = []" by (cases xs) (auto)
  lemma scan_eq_cons[iff]:
    "scan f xs a = b # w \<longleftrightarrow> (\<exists> y ys. xs = y # ys \<and> f y a = b \<and> scan f ys (f y a) = w)"
    by (cases xs) (auto)
  lemma scan_eq_append[iff]:
    "scan f xs a = u @ v \<longleftrightarrow> (\<exists> ys zs. xs = ys @ zs \<and> scan f ys a = u \<and> scan f zs (fold f ys a) = v)"
    by (induct u arbitrary: xs a) (auto, metis append_Cons fold_simps(2), blast)

  lemma scan_length[simp]: "length (scan f xs a) = length xs"
    by (induct xs arbitrary: a) (auto)
  lemma scan_last: "last (a # scan f xs a) = fold f xs a"
    by (induct xs arbitrary: a) (auto simp: last.simps)

  lemma scan_const[simp]: "scan const xs a = xs"
    by (induct xs arbitrary: a) (auto)
  lemma scan_nth[simp]:
    assumes "i < length (scan f xs a)"
    shows "scan f xs a ! i = fold f (take (Suc i) xs) a"
    using assms by (cases xs, simp, induct i arbitrary: xs a, auto simp: take_Suc neq_Nil_conv)
  lemma scan_map[simp]: "scan f (map g xs) a = scan (f \<circ> g) xs a"
    by (induct xs arbitrary: a) (auto)
  lemma scan_take[simp]: "take k (scan f xs a) = scan f (take k xs) a"
    by (induct k arbitrary: xs a) (auto simp: take_Suc neq_Nil_conv)
  lemma scan_drop[simp]: "drop k (scan f xs a) = scan f (drop k xs) (fold f (take k xs) a)"
    by (induct k arbitrary: xs a) (auto simp: take_Suc neq_Nil_conv)

  primcorec sscan :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a stream \<Rightarrow> 'b \<Rightarrow> 'b stream" where
    "sscan f xs a = f (shd xs) a ## sscan f (stl xs) (f (shd xs) a)"

  lemma sscan_scons[simp]: "sscan f (x ## xs) a = f x a ## sscan f xs (f x a)"
    by (simp add: stream.expand)
  lemma sscan_shift[simp]: "sscan f (xs @- ys) a = scan f xs a @- sscan f ys (fold f xs a)"
    by (induct xs arbitrary: a) (auto)

  lemma sscan_eq_scons[iff]:
    "sscan f xs a = b ## w \<longleftrightarrow> f (shd xs) a = b \<and> sscan f (stl xs) (f (shd xs) a) = w"
    using sscan.ctr stream.inject by metis
  lemma scons_eq_sscan[iff]:
    "b ## w = sscan f xs a \<longleftrightarrow> b = f (shd xs) a \<and> w = sscan f (stl xs) (f (shd xs) a)"
    using sscan.ctr stream.inject by metis

  lemma sscan_const[simp]: "sscan const xs a = xs"
    by (coinduction arbitrary: xs a) (auto)
  lemma sscan_snth[simp]: "sscan f xs a !! i = fold f (stake (Suc i) xs) a"
    by (induct i arbitrary: xs a) (auto)
  lemma sscan_scons_snth[simp]: "(a ## sscan f xs a) !! i = fold f (stake i xs) a"
    by (induct i arbitrary: xs a) (auto)
  lemma sscan_smap[simp]: "sscan f (smap g xs) a = sscan (f \<circ> g) xs a"
    by (coinduction arbitrary: xs a) (auto)
  lemma sscan_stake[simp]: "stake k (sscan f xs a) = scan f (stake k xs) a"
    by (induct k arbitrary: a xs) (auto)
  lemma sscan_sdrop[simp]: "sdrop k (sscan f xs a) = sscan f (sdrop k xs) (fold f (stake k xs) a)"
    by (induct k arbitrary: a xs) (auto)

  (* finite/infinite occurrence *)

  definition fins :: "'a set \<Rightarrow> 'a stream \<Rightarrow> bool" where
    "fins A w \<equiv> \<exists> u v. w = u @- v \<and> sset v \<inter> A = {}"

  abbreviation "infs A w \<equiv> \<not> fins A w"

  lemma fins_alt_def: "fins A w \<longleftrightarrow> (\<exists> n. \<forall> k \<ge> n. w !! k \<notin> A)"
  unfolding fins_def
  proof safe
    fix u v
    assume "sset v \<inter> A = {}"
    then have "v !! k \<notin> A" for k unfolding sset_range by auto
    then show "\<exists> n. \<forall> k \<ge> n. (u @- v) !! k \<notin> A" using shift_snth_ge by metis
  next
    fix n
    assume "\<forall> k \<ge> n. w !! k \<notin> A"
    then have "sset (sdrop n w) \<inter> A = {}" unfolding sset_range by auto
    then show "\<exists> u v. w = u @- v \<and> sset v \<inter> A = {}" using stake_sdrop by metis
  qed

  lemma fins_scons[iff]: "fins A (a ## w) \<longleftrightarrow> fins A w"
    unfolding fins_alt_def by (metis Suc_le_D Suc_le_mono le_Suc_eq snth_Stream)
  lemma fins_shift[iff]: "fins A (u @- v) \<longleftrightarrow> fins A v" by (induct u) (auto)
  lemma fins_stl[iff]: "fins A (stl w) \<longleftrightarrow> fins A w" using fins_scons by (metis stream.collapse)
  lemma fins_sdrop[iff]: "fins A (sdrop n w) \<longleftrightarrow> fins A w" using fins_shift by (metis stake_sdrop)
  lemma fins_sconst[iff]: "fins A (sconst a) \<longleftrightarrow> a \<notin> A" unfolding fins_alt_def by auto
  lemma fins_smap[iff]: "fins A (smap f w) \<longleftrightarrow> fins (f -` A) w" unfolding fins_alt_def by auto

  lemma fins_induct[case_names tail scons, induct pred: fins]:
    assumes "fins A w"
    assumes "\<And> w. sset w \<inter> A = {} \<Longrightarrow> P w"
    assumes "\<And> a w. P w \<Longrightarrow> P (a ## w)"
    shows "P w"
  proof -
    obtain u v where "w = u @- v" "sset v \<inter> A = {}" using assms(1) unfolding fins_def by auto
    then show ?thesis using assms(2, 3) by (induct u arbitrary: w) (auto)
  qed
  lemma infs_coinduct[case_names infs, coinduct pred: infs]:
    assumes "R w"
    assumes "\<And> w. R w \<Longrightarrow> \<exists> u v. w = u @- v \<and> set u \<inter> A \<noteq> {} \<and> R v"
    shows "infs A w"
  proof
    assume "fins A w"
    moreover have "\<exists> u v. w = u @- v \<and> R v" using shift.simps(1) assms(1) by metis
    ultimately show "False"
      using assms(2)
      by (induct) (force, metis empty_set inf_bot_right inf_commute shift_simps(2) stream.sel(2))
  qed

  lemma fins_subset[trans]: "sset w \<inter> A \<subseteq> B \<Longrightarrow> fins B w \<Longrightarrow> fins A w" unfolding fins_def by force
  lemma infs_supset[trans]: "infs A w \<Longrightarrow> sset w \<inter> A \<subseteq> B \<Longrightarrow> infs B w" using fins_subset by auto

  lemma fins_union[iff]: "fins (A \<union> B) w \<longleftrightarrow> fins A w \<and> fins B w"
  proof safe
    show "fins A w" "fins B w" if "fins (A \<union> B) w" using that by (auto intro: fins_subset)
    show "fins (A \<union> B) w" if "fins A w" "fins B w" using that by (induct) (auto intro: fins_subset)
  qed

  lemma fins_sset: "sset w \<inter> A = {} \<Longrightarrow> fins A w" unfolding fins_def using shift.simps(1) by metis
  lemma infs_sset: "sset w \<subseteq> A \<Longrightarrow> infs A w" unfolding fins_def using inf.absorb1 by force

  lemma fins_sset'[intro!, simp]: "fins (- sset w) w" by (auto intro!: fins_sset)
  lemma infs_sset'[intro!, simp]: "infs (sset w) w" by (auto intro!: infs_sset)

  lemma fins_empty[intro!, simp]: "fins {} w" by (auto intro!: fins_sset)
  lemma infs_UNIV[intro!, simp]: "infs UNIV w" by (auto intro!: infs_sset)

  lemma infs_flat_coinduct[case_names infs_flat, consumes 1]:
    assumes "R xss"
    assumes "\<And> xs xss. R (xs ## xss) \<Longrightarrow> set xs \<inter> A \<noteq> {} \<and> R xss"
    shows "infs A (flat xss)"
    using assms by (coinduction arbitrary: xss) (metis empty_set inf_bot_left flat_Stream stream.exhaust)

  (* sdistinct *)

  coinductive sdistinct :: "'a stream \<Rightarrow> bool" where
    scons[intro!]: "x \<notin> sset xs \<Longrightarrow> sdistinct xs \<Longrightarrow> sdistinct (x ## xs)"

  lemma sdistinct_scons_elim[elim!]:
    assumes "sdistinct (x ## xs)"
    obtains "x \<notin> sset xs" "sdistinct xs"
    using assms by (auto elim: sdistinct.cases)

  lemma sdistinct_coinduct[case_names sdistinct, coinduct pred: sdistinct]:
    assumes "P xs"
    assumes "\<And> x xs. P (x ## xs) \<Longrightarrow> x \<notin> sset xs \<and> P xs"
    shows "sdistinct xs"
    using stream.collapse sdistinct.coinduct assms by metis

  lemma sdistinct_shift[intro!]:
    assumes "distinct xs" "sdistinct ys" "set xs \<inter> sset ys = {}"
    shows "sdistinct (xs @- ys)"
    using assms by (induct xs) (auto)
  lemma sdistinct_shift_elim[elim!]:
    assumes "sdistinct (xs @- ys)"
    obtains "distinct xs" "sdistinct ys" "set xs \<inter> sset ys = {}"
    using assms by (induct xs) (auto)

  lemma sdistinct_infinite_sset:
    assumes "sdistinct w"
    shows "infinite (sset w)"
    using assms by (coinduction arbitrary: w) (force elim: sdistinct.cases)

  (* sorted streams *)

  coinductive (in order) sascending :: "'a stream \<Rightarrow> bool" where
    "a \<le> b \<Longrightarrow> sascending (b ## w) \<Longrightarrow> sascending (a ## b ## w)"

  coinductive (in order) sdescending :: "'a stream \<Rightarrow> bool" where
    "a \<ge> b \<Longrightarrow> sdescending (b ## w) \<Longrightarrow> sdescending (a ## b ## w)"

  lemma sdescending_coinduct[case_names sdescending, coinduct pred: sdescending]:
    assumes "P w"
    assumes "\<And> a b w. P (a ## b ## w) \<Longrightarrow> a \<ge> b \<and> P (b ## w)"
    shows "sdescending w"
    using stream.collapse sdescending.coinduct assms by (metis (no_types))

  lemma sdescending_sdrop:
    assumes "sdescending w"
    shows "sdescending (sdrop k w)"
    using assms by (induct k) (auto, metis sdescending.cases sdrop_stl stream.sel(2))

  lemma sdescending_snth_antimono:
    assumes "sdescending w"
    shows "antimono (snth w)"
  unfolding antimono_iff_le_Suc
  proof
    fix k
    have "sdescending (sdrop k w)" using sdescending_sdrop assms by this
    then obtain a b v where 2: "sdrop k w = a ## b ## v" "a \<ge> b" by rule
    then show "w !! k \<ge> w !! Suc k" by (metis sdrop_simps stream.sel)
  qed

  lemma sdescending_stuck:
    fixes w :: "'a :: wellorder stream"
    assumes "sdescending w"
    obtains k
    where "sdrop k w = sconst (w !! k)"
  using assms
  proof (induct "w !! 0" arbitrary: w thesis rule: less_induct)
    case less
    show ?case
    proof (cases "w = sconst (w !! 0)")
      case True
      show ?thesis using less(2)[of 0] True by simp
    next
      case False
      obtain k where 1: "w !! k \<noteq> w !! 0"
        using False by (metis empty_iff eqI_snth insert_iff snth_sset sset_sconst)
      have 2: "antimono (snth w)" using sdescending_snth_antimono less(3) by this
      have 3: "w !! k \<le> w !! 0" using 1 2 by (blast dest: antimonoD)
      have 4: "sdrop k w !! 0 < w !! 0" using 1 3 by auto
      have 5: "sdescending (sdrop k w)" using sdescending_sdrop less(3) by this
      obtain l where 5: "sdrop l (sdrop k w) = sconst (sdrop k w !! l)"
        using less(1)[OF 4 _ 5] by this
      show ?thesis using less(2) 5 by simp
    qed
  qed

end
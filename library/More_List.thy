(* Author: Simon Wimmer *)
theory More_List
  imports
    Main
    Instantiate_Existentials
begin

section \<open>@{term list_all2}\<close>

lemma list_all2_op_map_iff:
  "list_all2 (\<lambda> a b. b = f a) xs ys \<longleftrightarrow> map f xs = ys"
  unfolding list_all2_iff
  proof (induction xs arbitrary: ys)
    case Nil
    then show ?case by auto
  next
    case (Cons a xs ys)
    then show ?case by (cases ys) auto
  qed

lemma list_all2_last:
  "R (last xs) (last ys)" if "list_all2 R xs ys" "xs \<noteq> []"
  using that
  unfolding list_all2_iff
  proof (induction xs arbitrary: ys)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs ys)
    then show ?case by (cases ys) auto
  qed

lemma list_all2_set1:
  "\<forall>x\<in>set xs. \<exists>xa\<in>set as. P x xa" if "list_all2 P xs as"
  using that
proof (induction xs arbitrary: as)
  case Nil
  then show ?case by auto
next
  case (Cons a xs as)
  then show ?case by (cases as) auto
qed

lemma list_all2_swap:
  "list_all2 P xs ys \<longleftrightarrow> list_all2 (\<lambda> x y. P y x) ys xs"
  unfolding list_all2_iff by (fastforce simp: in_set_zip)+

lemma list_all2_set2:
  "\<forall>x\<in>set as. \<exists>xa\<in>set xs. P xa x" if "list_all2 P xs as"
  using that by - (rule list_all2_set1, subst (asm) list_all2_swap)

section \<open>Distinct lists\<close>

(* XXX Duplication with Floyd_Warshall.thy *)
lemma distinct_length_le:"finite s \<Longrightarrow> set xs \<subseteq> s \<Longrightarrow> distinct xs \<Longrightarrow> length xs \<le> card s"
  by (metis card_mono distinct_card)

section \<open>@{term filter}\<close>

lemma filter_eq_appendD:
  "\<exists> xs' ys'. filter P xs' = xs \<and> filter P ys' = ys \<and> as = xs' @ ys'" if "filter P as = xs @ ys"
  using that
proof (induction xs arbitrary: as)
  case Nil
  then show ?case
    by (inst_existentials "[] :: 'a list" as) auto
next
  case (Cons a xs)
  from filter_eq_ConsD[OF Cons.prems[simplified]] obtain us vs where
    "as = us @ a # vs" "\<forall>u\<in>set us. \<not> P u" "P a" "filter P vs = xs @ ys"
    by auto
  moreover from Cons.IH[OF \<open>_ = xs @ ys\<close>] obtain xs' ys where
    "filter P xs' = xs" "vs = xs' @ ys"
    by auto
  ultimately show ?case
    by (inst_existentials "us @ [a] @ xs'" ys) auto
qed

lemma list_all2_elem_filter:
  assumes "list_all2 P xs us" "x \<in> set xs"
  shows "length (filter (P x) us) \<ge> 1"
  using assms by (induction xs arbitrary: us) (auto simp: list_all2_Cons1)

lemma list_all2_replicate_elem_filter:
  assumes "list_all2 P (concat (replicate n xs)) ys" "x \<in> set xs"
  shows "length (filter (P x) ys) \<ge> n"
  using assms
  by (induction n arbitrary: ys; fastforce dest: list_all2_elem_filter simp: list_all2_append1)

section \<open>Sublists\<close>

lemma sublist_split:
  "sublist xs (A \<union> B) = sublist xs A @ sublist xs B" if "\<forall> i \<in> A. \<forall> j \<in> B. i < j"
  using that
  proof (induction xs arbitrary: A B)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    let ?A = "{j. Suc j \<in> A}" and ?B = "{j. Suc j \<in> B}"
    from Cons.prems have *: "\<forall>i\<in>?A. \<forall>a\<in>?B. i < a"
      by auto
    have [simp]: "{j. Suc j \<in> A \<or> Suc j \<in> B} = ?A \<union> ?B"
      by auto
    show ?case
      unfolding sublist_Cons
    proof (clarsimp, safe, goal_cases)
      case 2
      with Cons.prems have "A = {}"
        by auto
      with Cons.IH[OF *] show ?case by auto
    qed (use Cons.prems Cons.IH[OF *] in auto)
  qed

lemma sublist_nth:
  "sublist xs {i} = [xs ! i]" if "i < length xs"
  using that
  proof (induction xs arbitrary: i)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case
      by (cases i) (auto simp: sublist_Cons)
  qed

lemma sublist_shift:
  "sublist (xs @ ys) S = sublist ys {x - length xs | x. x \<in> S}" if
  "\<forall> i \<in> S. length xs \<le> i"
  using that
proof (induction xs arbitrary: S)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  have [simp]: "{x - length xs |x. Suc x \<in> S} = {x - Suc (length xs) |x. x \<in> S}" if "0 \<notin> S"
    using that apply safe
     apply force
    subgoal for x x'
      by (cases x') auto
    done
  from Cons.prems show ?case
    by (simp, subst sublist_Cons, subst Cons.IH; auto)
qed

lemma sublist_eq_ConsD:
  assumes "sublist xs I = x # as"
  shows
    "\<exists> ys zs.
      xs = ys @ x # zs \<and> length ys \<in> I \<and> (\<forall> i \<in> I. i \<ge> length ys)
      \<and> sublist zs ({i - length ys - 1 | i. i \<in> I \<and> i > length ys}) = as"
  using assms
proof (induction xs arbitrary: I x as)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  from Cons.prems show ?case
    unfolding sublist_Cons
    apply (auto split: if_split_asm)
    subgoal
      by (inst_existentials "[] :: 'a list" xs; force intro: arg_cong2[of xs xs _ _ sublist])
    subgoal
      apply (drule Cons.IH)
      apply safe
      subgoal for ys zs
        apply (inst_existentials "a # ys" zs)
           apply simp+
         apply standard
        subgoal for i
          by (cases i; auto)
        apply (rule arg_cong2[of zs zs _ _ sublist])
         apply simp
        apply safe
        subgoal for _ i
          by (cases i; auto)
        by force
      done
    done
qed

lemma sublist_out_of_bounds:
  "sublist xs I = []" if "\<forall>i \<in> I. i \<ge> length xs"
  using that
  (* Found by sledgehammer *)
proof -
  have
    "\<forall>N as.
      (\<exists>n. n \<in> N \<and> \<not> length (as::'a list) \<le> n)
      \<or> (\<forall>asa. sublist (as @ asa) N = sublist asa {n - length as |n. n \<in> N})"
    using sublist_shift by blast
  then obtain nn :: "nat set \<Rightarrow> 'a list \<Rightarrow> nat" where
    "\<forall>N as.
      nn N as \<in> N \<and> \<not> length as \<le> nn N as
    \<or> (\<forall>asa. sublist (as @ asa) N = sublist asa {n - length as |n. n \<in> N})"
    by moura
  then have
    "\<And>as. sublist as {n - length xs |n. n \<in> I} = sublist (xs @ as) I
      \<or> sublist (xs @ []) I = []"
    using that by fastforce
  then have "sublist (xs @ []) I = []"
    by (metis (no_types) sublist_nil)
  then show ?thesis
    by simp
qed

lemma sublist_eq_appendD:
  assumes "sublist xs I = as @ bs"
  shows
    "\<exists> ys zs.
        xs = ys @ zs \<and> sublist ys I = as
        \<and> sublist zs {i - length ys | i. i \<in> I \<and> i \<ge> length ys} = bs"
  using assms
proof (induction as arbitrary: xs I)
  case Nil
  then show ?case
    by (inst_existentials "[] :: 'a list" "sublist bs") auto
next
  case (Cons a ys xs)
  from sublist_eq_ConsD[of xs I a "ys @ bs"] Cons.prems obtain ys' zs' where
    "xs = ys' @ a # zs'" "length ys' \<in> I" "\<forall>i \<in> I. i \<ge> length ys'"
    "sublist zs' {i - length ys' - 1 |i. i \<in> I \<and> i > length ys'} = ys @ bs"
    by auto
  moreover from Cons.IH[OF \<open>sublist zs' _ = _\<close>] guess ys'' zs'' by clarify
  ultimately show ?case
    apply (inst_existentials "ys' @ a # ys''" zs'')
      apply (simp; fail)
    subgoal
      by (simp add: sublist_out_of_bounds sublist_append sublist_Cons)
        (rule arg_cong2[of ys'' ys'' _ _ sublist]; force)
    subgoal
      by safe (rule arg_cong2[of zs'' zs'' _ _ sublist]; force) (* Slow *)
    done
qed

lemma filter_sublist_length:
  "length (filter P (sublist xs I)) \<le> length (filter P xs)"
proof (induction xs arbitrary: I)
  case Nil
  then show ?case
    by simp
next
  case Cons
  then show ?case
  (* Found by sledgehammer *)
  proof -
    fix a :: 'a and xsa :: "'a list" and Ia :: "nat set"
    assume a1: "\<And>I. length (filter P (sublist xsa I)) \<le> length (filter P xsa)"
    have f2:
      "\<forall>b bs N. if 0 \<in> N then sublist ((b::'a) # bs) N =
        [b] @ sublist bs {n. Suc n \<in> N} else sublist (b # bs) N = [] @ sublist bs {n. Suc n \<in> N}"
      by (simp add: sublist_Cons)
    have f3:
      "sublist (a # xsa) Ia = [] @ sublist xsa {n. Suc n \<in> Ia}
        \<longrightarrow> length (filter P (sublist (a # xsa) Ia)) \<le> length (filter P xsa)"
      using a1 by (metis append_Nil)
    have f4: "length (filter P (sublist xsa {n. Suc n \<in> Ia})) + 0 \<le> length (filter P xsa) + 0"
      using a1 by simp
    have f5:
      "Suc (length (filter P (sublist xsa {n. Suc n \<in> Ia})) + 0)
      = length (a # filter P (sublist xsa {n. Suc n \<in> Ia}))"
      by force
    have f6: "Suc (length (filter P xsa) + 0) = length (a # filter P xsa)"
      by simp
    { assume "\<not> length (filter P (sublist (a # xsa) Ia)) \<le> length (filter P (a # xsa))"
      { assume "sublist (a # xsa) Ia \<noteq> [a] @ sublist xsa {n. Suc n \<in> Ia}"
        moreover
        { assume
            "sublist (a # xsa) Ia = [] @ sublist xsa {n. Suc n \<in> Ia}
            \<and> length (filter P (a # xsa)) \<le> length (filter P xsa)"
          then have "length (filter P (sublist (a # xsa) Ia)) \<le> length (filter P (a # xsa))"
            using a1 by (metis (no_types) append_Nil filter.simps(2) impossible_Cons) }
        ultimately have "length (filter P (sublist (a # xsa) Ia)) \<le> length (filter P (a # xsa))"
          using f3 f2 by (meson dual_order.trans le_cases) }
      then have "length (filter P (sublist (a # xsa) Ia)) \<le> length (filter P (a # xsa))"
        using f6 f5 f4 a1 by (metis Suc_le_mono append_Cons append_Nil filter.simps(2)) }
    then show "length (filter P (sublist (a # xsa) Ia)) \<le> length (filter P (a # xsa))"
      by meson
  qed
qed

end (* Theory *)
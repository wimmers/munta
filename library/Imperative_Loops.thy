theory Imperative_Loops
  imports Refine_Imperative_HOL.IICF Instantiate_Existentials
begin

subsection \<open>Additional proof rules for typical looping constructs\<close>

subsubsection \<open>@{term Heap_Monad.fold_map}\<close>

lemma fold_map_ht:
  assumes "list_all (\<lambda>x. <A * true> f x <\<lambda>r. \<up>(Q x r) * A>\<^sub>t) xs"
  shows "<A * true> Heap_Monad.fold_map f xs <\<lambda>rs. \<up>(list_all2 (\<lambda>x r. Q x r) xs rs) * A>\<^sub>t"
  using assms by (induction xs; sep_auto)

lemma fold_map_ht':
  assumes "list_all (\<lambda>x. <true> f x <\<lambda>r. \<up>(Q x r)>\<^sub>t) xs"
  shows "<true> Heap_Monad.fold_map f xs <\<lambda>rs. \<up>(list_all2 (\<lambda>x r. Q x r) xs rs)>\<^sub>t"
  using assms by (induction xs; sep_auto)

lemma fold_map_ht1:
  assumes "\<And>x xi. <A * R x xi * true> f xi <\<lambda>r. A * \<up>(Q x r)>\<^sub>t"
  shows "
  <A * list_assn R xs xsi * true>
    Heap_Monad.fold_map f xsi
  <\<lambda>rs. A * \<up>(list_all2 (\<lambda>x r. Q x r) xs rs)>\<^sub>t"
  apply (induction xs arbitrary: xsi)
   apply (sep_auto; fail)
  subgoal for x xs xsi
    by (cases xsi; sep_auto heap: assms)
  done

lemma fold_map_ht2:
  assumes "\<And>x xi. <A * R x xi * true> f xi <\<lambda>r. A * R x xi * \<up>(Q x r)>\<^sub>t"
  shows "
  <A * list_assn R xs xsi * true>
    Heap_Monad.fold_map f xsi
  <\<lambda>rs. A * list_assn R xs xsi * \<up>(list_all2 (\<lambda>x r. Q x r) xs rs)>\<^sub>t"
  apply (induction xs arbitrary: xsi)
   apply (sep_auto; fail)
  subgoal for x xs xsi
    apply (cases xsi; sep_auto heap: assms)
     apply (rule cons_rule[rotated 2], rule frame_rule, rprems)
      apply frame_inference
     apply frame_inference
    apply sep_auto
    done
  done

lemma fold_map_ht3:
  assumes "\<And>x xi. <A * R x xi * true> f xi <\<lambda>r. A * Q x r>\<^sub>t"
  shows "<A * list_assn R xs xsi * true> Heap_Monad.fold_map f xsi <\<lambda>rs. A * list_assn Q xs rs>\<^sub>t"
  apply (induction xs arbitrary: xsi)
   apply (sep_auto; fail)
  subgoal for x xs xsi
    apply (cases xsi; sep_auto heap: assms)
     apply (rule Hoare_Triple.cons_pre_rule[rotated], rule frame_rule, rprems, frame_inference)
    apply sep_auto
    done
  done

subsubsection \<open>@{term imp_for'} and @{term imp_for}\<close>

lemma imp_for_rule2:
  assumes
    "emp \<Longrightarrow>\<^sub>A I i a"
    "\<And>i a. <A * I i a * true> ci a <\<lambda>r. A * I i a * \<up>(r \<longleftrightarrow> c a)>\<^sub>t"
    "\<And>i a. i < j \<Longrightarrow> c a \<Longrightarrow> <A * I i a * true> f i a <\<lambda>r. A * I (i + 1) r>\<^sub>t"
    "\<And>a. I j a \<Longrightarrow>\<^sub>A Q a" "\<And>i a. i < j \<Longrightarrow> \<not> c a \<Longrightarrow> I i a \<Longrightarrow>\<^sub>A Q a"
    "i \<le> j"
  shows "<A * true> imp_for i j ci f a <\<lambda>r. A * Q r>\<^sub>t"
proof -
  have
    "<A * I i a * true>
      imp_for i j ci f a
    <\<lambda>r. A * (I j r \<or>\<^sub>A (\<exists>\<^sub>A i'. \<up>(i' < j \<and> \<not> c r) * I i' r))>\<^sub>t"
    using \<open>i \<le> j\<close> assms(2,3)
    apply (induction "j - i" arbitrary: i a; sep_auto)
      apply (rule ent_star_mono, rule ent_star_mono, rule ent_refl, rule ent_disjI1_direct, rule ent_refl)
     apply rprems
    apply sep_auto
      apply (rprems)
       apply sep_auto+
    apply (rule ent_star_mono, rule ent_star_mono, rule ent_refl, rule ent_disjI2')
     apply solve_entails
     apply simp+
    done
  then show ?thesis
    apply (rule cons_rule[rotated 2])
    subgoal
      apply (subst merge_true_star[symmetric])
      apply (rule ent_frame_fwd[OF assms(1)])
       apply frame_inference+
      done
    apply (rule ent_star_mono)
     apply (rule ent_star_mono, rule ent_refl)
     apply (solve_entails eintros: assms(5) assms(4) ent_disjE)+
    done
qed

lemma imp_for_rule:
  assumes
    "emp \<Longrightarrow>\<^sub>A I i a"
    "\<And>i a. <I i a * true> ci a <\<lambda>r. I i a * \<up>(r \<longleftrightarrow> c a)>\<^sub>t"
    "\<And>i a. i < j \<Longrightarrow> c a \<Longrightarrow> <I i a * true> f i a <\<lambda>r. I (i + 1) r>\<^sub>t"
    "\<And>a. I j a \<Longrightarrow>\<^sub>A Q a" "\<And>i a. i < j \<Longrightarrow> \<not> c a \<Longrightarrow> I i a \<Longrightarrow>\<^sub>A Q a"
    "i \<le> j"
  shows "<true> imp_for i j ci f a <\<lambda>r. Q r>\<^sub>t"
  by (rule cons_rule[rotated 2], rule imp_for_rule2[where A = true])
     (rule assms | sep_auto heap: assms; fail)+

lemma imp_for'_rule2:
  assumes
    "emp \<Longrightarrow>\<^sub>A I i a"
    "\<And>i a. i < j \<Longrightarrow> <A * I i a * true> f i a <\<lambda>r. A * I (i + 1) r>\<^sub>t"
    "\<And>a. I j a \<Longrightarrow>\<^sub>A Q a"
    "i \<le> j"
  shows "<A * true> imp_for' i j f a <\<lambda>r. A * Q r>\<^sub>t"
  unfolding imp_for_imp_for'[symmetric] using assms(3,4)
  by (sep_auto heap: assms imp_for_rule2[where c = "\<lambda>_. True"])

lemma imp_for'_rule:
  assumes
    "emp \<Longrightarrow>\<^sub>A I i a"
    "\<And>i a. i < j \<Longrightarrow> <I i a * true> f i a <\<lambda>r. I (i + 1) r>\<^sub>t"
    "\<And>a. I j a \<Longrightarrow>\<^sub>A Q a"
    "i \<le> j"
  shows "<true> imp_for' i j f a <\<lambda>r. Q r>\<^sub>t"
  unfolding imp_for_imp_for'[symmetric] using assms(3,4)
  by (sep_auto heap: assms imp_for_rule[where c = "\<lambda>_. True"])

lemmas nth_rule = sepref_fr_rules(160)[unfolded hn_refine_def hn_ctxt_def, simplified]

lemma imp_for_list_all:
  assumes
    "is_pure R" "n \<le> length xs"
    "\<And>x xi. <A * R x xi * true> Pi xi <\<lambda>r. A * \<up> (r \<longleftrightarrow> P x)>\<^sub>t"
  shows "
  <A * array_assn R xs a * true>
    imp_for 0 n Heap_Monad.return
    (\<lambda>i _. do {
      x \<leftarrow> Array.nth a i; Pi x
    })
    True
  <\<lambda>r. A *  array_assn R xs a * \<up>(r \<longleftrightarrow> list_all P (take n xs))>\<^sub>t"
  apply (rule imp_for_rule2[where I = "\<lambda>i r. \<up> (r \<longleftrightarrow> list_all P (take i xs))"])
       apply sep_auto
      apply sep_auto
  subgoal for i b
    using assms(2)
    apply (sep_auto heap: nth_rule)
     apply (rule cons_rule[rotated 2], rule frame_rule, rule nth_rule[of _ i xs], rule assms)
       apply simp
      apply (simp add: pure_def)
      apply frame_inference
     apply frame_inference
    apply (sep_auto heap: assms(3) simp: pure_def take_Suc_conv_app_nth)
    done
    apply (simp add: take_Suc_conv_app_nth)
   apply simp
  unfolding list_all_iff
   apply clarsimp
   apply (metis le_less set_take_subset_set_take subsetCE)
  ..

lemma imp_for_list_ex:
  assumes
    "is_pure R" "n \<le> length xs"
    "\<And>x xi. <A * R x xi * true> Pi xi <\<lambda>r. A * \<up> (r \<longleftrightarrow> P x)>\<^sub>t"
  shows "
  <A * array_assn R xs a * true>
    imp_for 0 n (\<lambda>x. Heap_Monad.return (\<not> x))
    (\<lambda>i _. do {
      x \<leftarrow> Array.nth a i; Pi x
    })
    False
  <\<lambda>r. A *  array_assn R xs a * \<up>(r \<longleftrightarrow> list_ex P (take n xs))>\<^sub>t"
  apply (rule imp_for_rule2[where I = "\<lambda>i r. \<up> (r \<longleftrightarrow> list_ex P (take i xs))"])
       apply sep_auto
      apply sep_auto
  subgoal for i b
    using assms(2)
    apply (sep_auto heap: nth_rule)
     apply (rule cons_rule[rotated 2], rule frame_rule, rule nth_rule[of _ i xs], rule assms)
       apply simp
      apply (simp add: pure_def)
      apply frame_inference
     apply frame_inference
    apply (sep_auto heap: assms(3) simp: pure_def take_Suc_conv_app_nth)
    done
    apply (simp add: take_Suc_conv_app_nth)
   apply simp
  unfolding list_ex_iff
   apply clarsimp
   apply (metis le_less set_take_subset_set_take subsetCE)
  ..

lemma imp_for_list_all2:
  assumes
    "is_pure R" "is_pure S" "n \<le> length xs" "n \<le> length ys"
    "\<And>x xi y yi. <A * R x xi * S y yi * true> Pi xi yi <\<lambda>r. A * \<up> (r \<longleftrightarrow> P x y)>\<^sub>t"
  shows "
  <A * array_assn R xs a  * array_assn S ys b * true>
    imp_for 0 n Heap_Monad.return
    (\<lambda>i _. do {
      x \<leftarrow> Array.nth a i; y \<leftarrow> Array.nth b i; Pi x y
    })
    True
  <\<lambda>r. A *  array_assn R xs a  * array_assn S ys b * \<up>(r \<longleftrightarrow> list_all2 P (take n xs) (take n ys))>\<^sub>t"
  apply (rule imp_for_rule2[where I = "\<lambda>i r. \<up> (r \<longleftrightarrow> list_all2 P (take i xs) (take i ys))"])
       apply (sep_auto; fail)
      apply (sep_auto; fail)
  subgoal for i _
    supply [simp] = pure_def
    using assms(3,4)
    apply sep_auto
     apply (rule cons_rule[rotated 2], rule frame_rule, rule nth_rule[of _ i xs], rule assms)
       apply (simp; fail)
      apply (simp, frame_inference; fail)
     apply frame_inference
    apply sep_auto

     apply (rule cons_rule[rotated 2], rule frame_rule, rule nth_rule[of _ i ys], rule assms)
    unfolding pure_def
       apply (simp; fail)
      apply (simp, frame_inference; fail)
     apply frame_inference
    apply sep_auto

    supply [sep_heap_rules] = assms(5)
    apply sep_auto
    subgoal
      unfolding list_all2_conv_all_nth apply clarsimp
      subgoal for i'
        by (cases "i' = i") auto
      done
    subgoal
      unfolding list_all2_conv_all_nth by clarsimp
    apply frame_inference
    done
  unfolding list_all2_conv_all_nth apply auto
  done

lemma imp_for_list_all2':
  assumes
    "is_pure R" "is_pure S" "n \<le> length xs" "n \<le> length ys"
    "\<And>x xi y yi. <R x xi * S y yi> Pi xi yi <\<lambda>r. \<up> (r \<longleftrightarrow> P x y)>\<^sub>t"
  shows "
  <array_assn R xs a  * array_assn S ys b>
    imp_for 0 n Heap_Monad.return
    (\<lambda>i _. do {
      x \<leftarrow> Array.nth a i; y \<leftarrow> Array.nth b i; Pi x y
    })
    True
  <\<lambda>r. array_assn R xs a  * array_assn S ys b * \<up>(r \<longleftrightarrow> list_all2 P (take n xs) (take n ys))>\<^sub>t"
  by (rule cons_rule[rotated 2], rule imp_for_list_all2[where A = true, rotated 4])
     (sep_auto heap: assms intro: assms)+

end
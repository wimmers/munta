(* Author: Simon Wimmer *)
theory Graphs
  imports
    "Stream_More"
    "~~/src/HOL/Library/Rewrite"
    "Instantiate_Existentials"
begin

chapter \<open>Graphs\<close>

locale Graph_Defs =
  fixes E :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

inductive steps where
  Single: "steps [x]" |
  Cons: "steps (x # y # xs)" if "E x y" "steps (y # xs)"

lemmas [intro] = steps.intros

lemma steps_append:
  "steps (xs @ tl ys)" if "steps xs" "steps ys" "last xs = hd ys"
  using that by induction (auto 4 4 elim: steps.cases)

coinductive run where
  "run (x ## y ## xs)" if "E x y" "run (y ## xs)"

lemmas [intro] = run.intros

lemma steps_appendD1:
  "steps xs" if "steps (xs @ ys)" "xs \<noteq> []"
  using that proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case
    by - (cases xs; auto elim: steps.cases)
qed

lemma steps_appendD2:
  "steps ys" if "steps (xs @ ys)" "ys \<noteq> []"
  using that by (induction xs) (auto elim: steps.cases)

lemma steps_appendD3:
  "steps (xs @ [x]) \<and> E x y" if "steps (xs @ [x, y])"
  using that proof (induction xs)
  case Nil
  then show ?case by (auto elim!: steps.cases)
next
  case prems: (Cons a xs)
  then show ?case by (cases xs) (auto elim: steps.cases)
qed

lemma steps_ConsD:
  "steps xs" if "steps (x # xs)" "xs \<noteq> []"
  using that by (auto elim: steps.cases)

lemmas stepsD = steps_ConsD steps_appendD1 steps_appendD2

lemma steps_alt_induct[consumes 1, case_names Single Snoc]:
  assumes
    "steps x" "(\<And>x. P [x])"
    "\<And>y x xs. E y x \<Longrightarrow> steps (xs @ [y]) \<Longrightarrow> P (xs @ [y]) \<Longrightarrow> P (xs @ [y,x])"
  shows "P x"
  using assms(1)
  proof (induction rule: rev_induct)
    case Nil
    then show ?case by (auto elim: steps.cases)
  next
    case prems: (snoc x xs)
    then show ?case by (cases xs rule: rev_cases) (auto intro: assms(2,3) dest!: steps_appendD3)
  qed

lemma steps_appendI:
  "steps (xs @ [x, y])" if "steps (xs @ [x])" "E x y"
  using that
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case by (cases xs; auto elim: steps.cases)
qed

lemma steps_append_single:
  assumes
    "steps xs" "E (last xs) x" "xs \<noteq> []"
  shows "steps (xs @ [x])"
  using assms(3,1,2) by (induction xs rule: list_nonempty_induct) (auto 4 4 elim: steps.cases)

lemma extend_run:
  assumes
    "steps xs" "E (last xs) x" "run (x ## ys)" "xs \<noteq> []"
  shows "run (xs @- x ## ys)"
  using assms(4,1-3) by (induction xs rule: list_nonempty_induct) (auto 4 3 elim: steps.cases)

lemma run_cycle:
  assumes "steps xs" "E (last xs) (hd xs)" "xs \<noteq> []"
  shows "run (cycle xs)"
  using assms proof (coinduction arbitrary: xs)
  case run
  then show ?case
    apply (rewrite at \<open>cycle xs\<close> stream.collapse[symmetric])
    apply (rewrite at \<open>stl (cycle xs)\<close> stream.collapse[symmetric])
    apply clarsimp
    apply (erule steps.cases)
    subgoal for x
      apply (rule conjI)
       apply (simp; fail)
      apply (rule disjI1)
      apply (inst_existentials xs)
         apply (simp, metis cycle_Cons[of x "[]", simplified])
      by auto
    subgoal for x y xs'
      apply (rule conjI)
       apply (simp; fail)
      apply (rule disjI1)
      apply (inst_existentials "y # xs' @ [x]")
      using steps_append_single[of "y # xs'" x]
         apply (auto elim: steps.cases split: if_split_asm)
       apply (subst (2) cycle_Cons, simp) (* XXX Automate forward reasoning *)
      apply (subst cycle_Cons, simp)
      done
    done
qed

lemma run_stl:
  "run (stl xs)" if "run xs"
  using that by (auto elim: run.cases)

lemma run_sdrop:
  "run (sdrop n xs)" if "run xs"
  using that by (induction n arbitrary: xs) (auto intro: run_stl)

lemma run_reachable':
  assumes "run (x ## xs)" "E\<^sup>*\<^sup>* x\<^sub>0 x"
  shows "pred_stream (\<lambda> x. E\<^sup>*\<^sup>* x\<^sub>0 x) xs"
  using assms by (coinduction arbitrary: x xs) (auto 4 3 elim: run.cases)

lemma run_reachable:
  assumes "run (x\<^sub>0 ## xs)"
  shows "pred_stream (\<lambda> x. E\<^sup>*\<^sup>* x\<^sub>0 x) xs"
  by (rule run_reachable'[OF assms]) blast

lemma run_decomp:
  assumes "run (xs @- ys)" "xs \<noteq> []"
  shows "steps xs \<and> run ys \<and> E (last xs) (shd ys)"
using assms(2,1) proof (induction xs rule: list_nonempty_induct)
  case (single x)
  then show ?case by (auto elim: run.cases)
next
  case (cons x xs)
  then show ?case by (cases xs; auto 4 4 elim: run.cases)
qed

lemma steps_decomp:
  assumes "steps (xs @ ys)" "xs \<noteq> []" "ys \<noteq> []"
  shows "steps xs \<and> steps ys \<and> E (last xs) (hd ys)"
using assms(2,1,3) proof (induction xs rule: list_nonempty_induct)
  case (single x)
  then show ?case by (auto elim: steps.cases)
next
  case (cons x xs)
  then show ?case by (cases xs; auto 4 4 elim: steps.cases)
qed

lemma steps_rotate:
  assumes "steps (x # xs @ y # ys @ [x])"
  shows "steps (y # ys @ x # xs @ [y])"
proof -
  from steps_decomp[of "x # xs" "y # ys @ [x]"] assms have
    "steps (x # xs)" "steps (y # ys @ [x])" "E (last (x # xs)) y"
    by auto
  then have "steps ((x # xs) @ [y])" by (blast intro: steps_append_single)
  from steps_append[OF \<open>steps (y # ys @ [x])\<close> this] show ?thesis by auto
qed

lemma run_shift_coinduct[case_names run_shift, consumes 1]:
  assumes "R w"
      and "\<And> w. R w \<Longrightarrow> \<exists> u v x y. w = u @- x ## y ## v \<and> steps (u @ [x]) \<and> E x y \<and> R (y ## v)"
  shows "run w"
  using assms(2)[OF \<open>R w\<close>] proof (coinduction arbitrary: w)
  case (run w)
  then obtain u v x y where "w = u @- x ## y ## v" "steps (u @ [x])" "E x y" "R (y ## v)"
    by auto
  then show ?case
    apply -
    apply (drule assms(2))
    apply (cases u)
     apply force
    subgoal for z zs
      apply (cases zs)
      subgoal
        apply simp
        apply safe
         apply (force elim: steps.cases)
        subgoal for u' v' x' y'
          by (inst_existentials "x # u'") (cases u'; auto)
        done
      subgoal for a as
        apply simp
        apply safe
         apply (force elim: steps.cases)
        subgoal for u' v' x' y'
          apply (inst_existentials "a # as @ x # u'")
          using steps_append[of "a # as @ [x, y]" "u' @ [x']"]
          apply simp
          apply (drule steps_appendI[of "a # as" x, rotated])
          by (cases u'; force elim: steps.cases)+
        done
      done
    done
qed

lemma run_flat_coinduct[case_names run_shift, consumes 1]:
  assumes "R xss"
    and
    "\<And> xs ys xss.
    R (xs ## ys ## xss) \<Longrightarrow> xs \<noteq> [] \<and> steps xs \<and> E (last xs) (hd ys) \<and> R (ys ## xss)"
  shows "run (flat xss)"
proof -
  obtain xs ys xss' where "xss = xs ## ys ## xss'" by (metis stream.collapse)
  with assms(2)[OF assms(1)[unfolded this]] show ?thesis
  proof (coinduction arbitrary: xs ys xss' xss rule: run_shift_coinduct)
    case (run_shift xs ys xss' xss)
    from run_shift show ?case
      apply (cases xss')
      apply clarify
      apply (drule assms(2))
      apply (inst_existentials "butlast xs" "tl ys @- flat xss'" "last xs" "hd ys")
         apply (cases ys)
          apply (simp; fail)
      subgoal premises prems for x1 x2 z zs
      proof (cases "xs = []")
        case True
        with prems show ?thesis
          by auto
      next
        case False
        then have "xs = butlast xs @ [last xs]" by auto
        then have "butlast xs @- last xs ## tail = xs @- tail" for tail
          by (metis shift.simps(1,2) shift_append)
        with prems show ?thesis by simp
      qed
        apply (simp; fail)
       apply assumption
      subgoal for ws wss
        by (inst_existentials ys ws wss) (cases ys, auto)
      done
  qed
qed


definition
  "Alw_ev \<phi> x \<equiv> \<forall> xs. run (x ## xs) \<longrightarrow> ev (holds \<phi>) (x ## xs)"

lemma Alw_ev:
  "Alw_ev \<phi> x \<longleftrightarrow> \<not> (\<exists> xs. run (x ## xs) \<and> alw (holds (Not o \<phi>)) (x ## xs))"
  unfolding Alw_ev_def
proof (safe, goal_cases)
  case prems: (1 xs)
  then have "ev (holds \<phi>) (x ## xs)" by auto
  then show ?case
    using prems(2,3) by induction (auto intro: run_stl)
next
  case prems: (2 xs)
  then have "\<not> alw (holds (Not \<circ> \<phi>)) (x ## xs)"
    by auto
  moreover have "(\<lambda> x. \<not> holds (Not \<circ> \<phi>) x) = holds \<phi>"
    by (rule ext) simp
  ultimately show ?case
    unfolding not_alw_iff by simp
qed


lemma steps_non_empty[simp]:
  "\<not> steps []"
  by (auto elim: steps.cases)

lemma steps_replicate:
  "steps (hd xs # concat (replicate n (tl xs)))" if "last xs = hd xs" "steps xs" "n > 0"
  using that
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases n)
    case 0
    with Suc.prems show ?thesis by (cases xs; auto)
  next
    case prems: (Suc nat)
    from Suc.prems have [simp]: "hd xs # tl xs @ ys = xs @ ys" for ys
      by (cases xs; auto)
    from Suc.prems have **: "tl xs @ ys = tl (xs @ ys)" for ys
      by (cases xs; auto)
    from prems Suc show ?thesis
      by - (simp; simp add: **; rule steps_append; cases xs; auto)
  qed
qed

end (* Graph Defs *)

locale Graph_Start_Defs = Graph_Defs +
  fixes s\<^sub>0 :: 'a
begin

definition reachable where
  "reachable = E\<^sup>*\<^sup>* s\<^sub>0"

lemma start_reachable[intro!, simp]:
  "reachable s\<^sub>0"
  unfolding reachable_def by auto

lemma reachable_step[intro]:
  "reachable b" if "reachable a" "E a b"
  using that unfolding reachable_def by auto

lemma reachable_steps_append:
  assumes "reachable a" "steps xs" "hd xs = a" "last xs = b"
  shows "reachable b"
  using assms unfolding reachable_def
  by (induction xs arbitrary: a; force intro: rtranclp.rtrancl_into_rtrancl elim: steps.cases)

lemmas steps_reachable = reachable_steps_append[of s\<^sub>0, simplified]

lemma reachable_steps_elem:
  "reachable y" if "reachable x" "steps xs" "y \<in> set xs" "hd xs = x"
proof -
  from \<open>y \<in> set xs\<close> obtain as bs where [simp]: "xs = as @ y # bs"
    by (auto simp: in_set_conv_decomp)
  show ?thesis
  proof (cases "as = []")
    case True
    with that show ?thesis
      by simp
  next
    case False
    with steps_appendD1[of \<open>as @ [y]\<close> bs] \<open>steps xs\<close> have "steps (as @ [y])"
      by simp
    with \<open>as \<noteq> []\<close> \<open>hd xs = x\<close> \<open>reachable x\<close> show ?thesis
      by (auto intro: reachable_steps_append)
  qed
qed

lemma reachable_steps:
  "\<exists> xs. steps xs \<and> hd xs = s\<^sub>0 \<and> last xs = x" if "reachable x"
  using that unfolding reachable_def
proof induction
  case base
  then show ?case by (inst_existentials "[s\<^sub>0]"; force)
next
  case (step y z)
  from step.IH guess xs by clarify
  with step.hyps show ?case
    apply (inst_existentials "xs @ [z]")
    apply (force intro: steps_append_single)
    by (cases xs; auto)+
qed

lemma reachable_cycle_iff:
  "(\<exists> ws. steps (s\<^sub>0 # ws @ [x] @ xs @ [x])) \<longleftrightarrow> reachable x \<and> steps ([x] @ xs @ [x])"
proof (safe, goal_cases)
  case (1 ws)
  then have "steps ((s\<^sub>0 # ws @ [x]) @ (xs @ [x]))"
    by simp
  then have "steps (s\<^sub>0 # ws @ [x])"
    by (blast dest: stepsD)
  then show ?case
    by (auto intro: steps_reachable stepsD)
next
  case (2 ws)
  then show ?case by (auto dest: stepsD)
next
  case prems: 3
  show ?case
  proof (cases "s\<^sub>0 = x")
    case True
    with prems show ?thesis
      by (inst_existentials xs) (frule steps_append, assumption, auto)
  next
    case False
    from reachable_steps[OF \<open>reachable x\<close>] obtain ws where
      "steps ws" "hd ws = s\<^sub>0" "last ws = x"
      by auto
    with \<open>_ \<noteq> x\<close> obtain us where "ws = s\<^sub>0 # us @ [x]"
      apply atomize_elim
      apply (cases ws)
       apply (simp; fail)
      subgoal for a ws'
        by (inst_existentials "butlast ws'") auto
      done
    with \<open>steps ws\<close> prems show ?thesis
      by (inst_existentials us) (drule steps_append, assumption, auto)
  qed
qed

end (* Graph Start Defs *)

end
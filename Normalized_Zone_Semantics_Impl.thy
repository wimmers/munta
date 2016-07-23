theory Normalized_Zone_Semantics_Impl
  imports
    Normalized_Zone_Semantics
    "../IRF/Refine_Imperative_HOL/Examples/Worklist_Subsumption"
    DBM_Operations_Impl
    FW_Code
begin

hide_const D              

section \<open>More on normalized zone semantics\<close>

context Regions
begin

(* XXX Maybe move *)
lemma step_z_beta_mono:
  assumes "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^sub>\<N> \<langle>l',D'\<rangle>" "global_clock_numbering A v n" "valid_abstraction A X k"
  and     "valid_dbm D" "valid_dbm M"
  and "[D]\<^bsub>v,n\<^esub> \<subseteq> [M]\<^bsub>v,n\<^esub>"
  shows "\<exists> M'. A \<turnstile> \<langle>l, M\<rangle> \<leadsto>\<^sub>\<N> \<langle>l', M'\<rangle> \<and> [D']\<^bsub>v,n\<^esub> \<subseteq> [M']\<^bsub>v,n\<^esub>"
proof -
  from norm_beta_sound[OF assms(1,2,3,4)] have "A \<turnstile> \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l', [D']\<^bsub>v,n\<^esub>\<rangle>" .
  from step_z_beta_mono[OF this assms(6)] assms(5) obtain Z where
    "A \<turnstile> \<langle>l, [M]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l', Z\<rangle>" "[D']\<^bsub>v,n\<^esub> \<subseteq> Z"
  by auto
  with norm_beta_complete[OF this(1) assms(2,3,5)] show ?thesis by metis
qed

end

section \<open>Implementation Semantics\<close>

term abstr_upd

term  "(up_canonical_upd (abstr_upd (inv_of A l) D) n)"

lemma fw_upd_out_of_bounds1:
  assumes "i' > i"
  shows "(fw_upd M k i j) i' j' = M i' j'"
using assms unfolding fw_upd_def Floyd_Warshall.upd_def by (auto split: split_min)

lemma fw_upd_out_of_bounds2:
  assumes "j' > j"
  shows "(fw_upd M k i j) i' j' = M i' j'"
using assms unfolding fw_upd_def Floyd_Warshall.upd_def by (auto split: split_min)

lemma fw_out_of_bounds1:
  assumes "i' > n" "i \<le> n"
  shows "(fw M n k i j) i' j' = M i' j'"
using assms
 apply (induction _ "(k, i, j)" arbitrary: k i j rule: wf_induct[of "less_than <*lex*> less_than <*lex*> less_than"])
 apply (auto; fail)
 subgoal for k i j
 by (cases k; cases i; cases j; auto simp add: fw_upd_out_of_bounds1)
done

lemma fw_out_of_bounds2:
  assumes "j' > n" "j \<le> n"
  shows "(fw M n k i j) i' j' = M i' j'"
using assms
 apply (induction _ "(k, i, j)" arbitrary: k i j rule: wf_induct[of "less_than <*lex*> less_than <*lex*> less_than"])
 apply (auto; fail)
 subgoal for k i j
 by (cases k; cases i; cases j; auto simp add: fw_upd_out_of_bounds2)
done

definition "FW' = uncurry oo FW o curry"
term norm_upd

lemma FW'_out_of_bounds1:
  assumes "i' > n"
  shows "(FW' M n) (i', j') = M (i', j')"
unfolding FW'_def by (simp add: fw_out_of_bounds1[OF assms])

lemma FW'_out_of_bounds2:
  assumes "j' > n"
  shows "(FW' M n) (i', j') = M (i', j')"
unfolding FW'_def by (simp add: fw_out_of_bounds2[OF assms])

inductive step_impl ::
  "('a, nat, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('t::time) DBM'
    \<Rightarrow> ('t list) \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> ('t::time) DBM' \<Rightarrow> bool"
("_ \<turnstile>\<^sub>I \<langle>_, _\<rangle> \<leadsto>\<^bsub>_,_\<^esub> \<langle>_, _\<rangle>" [61,61,61] 61)
where
  step_t_impl:
    "A \<turnstile>\<^sub>I \<langle>l,D\<rangle> \<leadsto>\<^bsub>k,n\<^esub> \<langle>l,norm_upd (FW' (abstr_upd (inv_of A l) (up_canonical_upd (abstr_upd (inv_of A l) D) n)) n) k n\<rangle>" |
  step_a_impl:
    "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'
    \<Longrightarrow> A \<turnstile>\<^sub>I \<langle>l,D\<rangle> \<leadsto>\<^bsub>k,n\<^esub> \<langle>l',norm_upd (FW' (abstr_upd (inv_of A l') (reset'_upd (abstr_upd g D) n r 0)) n) k n\<rangle>"

inductive_cases step_impl_cases: "A \<turnstile>\<^sub>I \<langle>l, D\<rangle> \<leadsto>\<^bsub>k,n\<^esub> \<langle>l', D'\<rangle>"

declare step_impl.intros[intro]

lemma norm_upd_default:
  assumes "dbm_default (curry M) n"
  shows "dbm_default (curry (norm_upd M k n)) n"
using assms by (auto simp: norm_upd_out_of_bounds1 norm_upd_out_of_bounds2)

lemma abstr_upd_default:
  assumes "dbm_default (curry M) n" "\<forall>c\<in>collect_clks cc. c \<le> n"
  shows "dbm_default (curry (abstr_upd cc M)) n"
using assms by (auto simp: abstr_upd_out_of_bounds1 abstr_upd_out_of_bounds2)

lemma up_canonical_upd_default:
  assumes "dbm_default (curry M) n"
  shows "dbm_default (curry (up_canonical_upd M n)) n"
using assms by (auto simp: up_canonical_out_of_bounds1 up_canonical_out_of_bounds2)

lemma reset'_upd_default:
  assumes "dbm_default (curry M) n" "\<forall>c\<in>set cs. c \<le> n"
  shows "dbm_default (curry (reset'_upd M n cs d)) n"
using assms by (auto simp: reset'_upd_out_of_bounds1 reset'_upd_out_of_bounds2)

lemma FW'_int_preservation:
  assumes "dbm_int (curry M) n"
  shows "dbm_int (curry (FW' M n)) n"
using FW_int_preservation[OF assms] unfolding FW'_def curry_def by auto

lemma constraint_clk_constraint_pair:
  "constraint_clk ac = fst (constraint_pair ac)"
apply (cases ac)
apply auto
done

lemma collect_clks_inv_clk_set:
  "collect_clks (inv_of A l) \<subseteq> clk_set A"
unfolding clkp_set_def collect_clki_def collect_clks_def collect_clock_pairs_def
by (auto simp: constraint_clk_constraint_pair) blast

lemma step_impl_dbm_default:
  assumes "A \<turnstile>\<^sub>I \<langle>l, D\<rangle> \<leadsto>\<^bsub>k,n\<^esub> \<langle>l', D'\<rangle>" "dbm_default (curry D) n" "\<forall> c \<in> clk_set A. c \<le> n"
  shows "dbm_default (curry D') n"
using assms
apply safe

 apply (cases rule: step_impl.cases)
 apply assumption

  apply (simp add: norm_upd_out_of_bounds1 FW'_out_of_bounds1)
  apply (subst abstr_upd_out_of_bounds1[where n = n])
  using collect_clks_inv_clk_set[of A] apply fastforce
  apply assumption
  apply (simp add: up_canonical_out_of_bounds1)
  apply (subst abstr_upd_out_of_bounds1[where n = n])
  using collect_clks_inv_clk_set[of A] apply fastforce
  apply assumption
  apply (simp; fail)

  apply (simp add: norm_upd_out_of_bounds1 FW'_out_of_bounds1)
  apply (subst abstr_upd_out_of_bounds1[where n = n])
  using collect_clks_inv_clk_set[of A] apply fastforce
  apply assumption
  apply (subst reset'_upd_out_of_bounds1[where n = n])
  apply (fastforce simp: collect_clkvt_def)
  apply assumption
  apply (subst abstr_upd_out_of_bounds1[where n = n]) 
  apply (auto simp: constraint_clk_constraint_pair clkp_set_def collect_clkt_def collect_clks_def
    collect_clock_pairs_def; blast; fail)
  apply assumption
  apply (simp; fail)

 apply (cases rule: step_impl.cases)
 apply assumption

  apply (simp add: norm_upd_out_of_bounds2 FW'_out_of_bounds2)
  apply (subst abstr_upd_out_of_bounds2[where n = n])
  using collect_clks_inv_clk_set[of A] apply fastforce
  apply assumption
  apply (simp add: up_canonical_out_of_bounds2)
  apply (subst abstr_upd_out_of_bounds2[where n = n])
  using collect_clks_inv_clk_set[of A] apply fastforce
  apply assumption
  apply (simp; fail)

  apply (simp add: norm_upd_out_of_bounds2 FW'_out_of_bounds2)
  apply (subst abstr_upd_out_of_bounds2[where n = n])
  using collect_clks_inv_clk_set[of A] apply fastforce
  apply assumption
  apply (subst reset'_upd_out_of_bounds2[where n = n])
  apply (fastforce simp: collect_clkvt_def)
  apply assumption
  apply (subst abstr_upd_out_of_bounds2[where n = n]) 
  apply (auto simp: constraint_clk_constraint_pair clkp_set_def collect_clkt_def collect_clks_def
    collect_clock_pairs_def; blast; fail)
  apply assumption
  apply (simp; fail)
done

lemma collect_clocks_clk_set:
  assumes
    "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"
  shows
    "collect_clks g \<subseteq> clk_set A"
using assms
by (auto simp: constraint_clk_constraint_pair clkp_set_def collect_clkt_def collect_clks_def
        collect_clock_pairs_def; blast)

lemma reset_clk_set:
  assumes
    "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"
  shows
    "set r \<subseteq> clk_set A"
using assms by (fastforce simp: clkp_set_def collect_clkvt_def)

lemma step_impl_norm_dbm_default_dbm_int:
  assumes "A \<turnstile>\<^sub>I \<langle>l, D\<rangle> \<leadsto>\<^bsub>k,n\<^esub> \<langle>l', D'\<rangle>" "dbm_default (curry D) n" "dbm_int (curry D) n"
          "\<forall> c \<in> clk_set A. c \<le> n \<and> c \<noteq> 0" "\<forall> (_, d)  \<in> clkp_set A. d \<in> \<int>"
  shows "\<exists> M. D' = norm_upd M k n \<and> dbm_default (curry M) n \<and> dbm_int (curry M) n"
using assms
 apply (cases rule: step_impl.cases)

  subgoal -- "Step is a time delay step"
  apply (rule exI[where x = "FW' (abstr_upd (inv_of A l) (up_canonical_upd (abstr_upd (inv_of A l) D) n)) n"])
  apply standard
  apply (simp; fail)
  apply standard
  apply standard
  apply safe[]
  
    apply (simp add: norm_upd_out_of_bounds1 FW'_out_of_bounds1)
    apply (subst abstr_upd_out_of_bounds1[where n = n])
    using collect_clks_inv_clk_set[of A] apply fastforce
    apply assumption
    apply (simp add: up_canonical_out_of_bounds1)
    apply (subst abstr_upd_out_of_bounds1[where n = n])
    using collect_clks_inv_clk_set[of A] apply fastforce
    apply assumption
    apply (simp; fail)

    apply standard
    apply safe[]
    apply (simp add: norm_upd_out_of_bounds2 FW'_out_of_bounds2)
    apply (subst abstr_upd_out_of_bounds2[where n = n])
    using collect_clks_inv_clk_set[of A] apply fastforce
    apply assumption
    apply (simp add: up_canonical_out_of_bounds2)
    apply (subst abstr_upd_out_of_bounds2[where n = n])
    using collect_clks_inv_clk_set[of A] apply fastforce
    apply assumption
    apply (simp; fail)

    apply (rule FW'_int_preservation)
    apply (rule abstr_upd_int_preservation)
    defer
    apply (rule up_canonical_upd_int_preservation)
    apply (rule abstr_upd_int_preservation)
    defer
    apply (simp add: clkp_set_def collect_clki_def; fast)+
  done

  subgoal for g a r -- "Step is an action step"
  apply (rule exI[where x = "FW' (abstr_upd (inv_of A l') (reset'_upd (abstr_upd g D) n r 0)) n"])
  apply standard
  apply (simp; fail)
  apply standard
  apply standard
  apply safe[]

    apply (simp add: norm_upd_out_of_bounds1 FW'_out_of_bounds1)
    apply (subst abstr_upd_out_of_bounds1[where n = n])
    using collect_clks_inv_clk_set[of A] apply fastforce
    apply assumption
    apply (subst reset'_upd_out_of_bounds1[where n = n])
    apply (fastforce simp: collect_clkvt_def)
    apply assumption
    apply (subst abstr_upd_out_of_bounds1[where n = n])
    using collect_clocks_clk_set apply fast
    apply assumption
    apply (simp; fail)

    apply safe[]
    apply (simp add: norm_upd_out_of_bounds2 FW'_out_of_bounds2)
    apply (subst abstr_upd_out_of_bounds2[where n = n])
    using collect_clks_inv_clk_set[of A] apply fastforce
    apply assumption
    apply (subst reset'_upd_out_of_bounds2[where n = n])
    apply (fastforce simp: collect_clkvt_def)
    apply assumption
    apply (subst abstr_upd_out_of_bounds2[where n = n])
    using collect_clocks_clk_set apply fast
    apply assumption
    apply (simp; fail)
    
    apply (rule FW'_int_preservation)
    apply (rule abstr_upd_int_preservation)
    defer
    apply (rule reset'_upd_int_preservation)
    apply (rule abstr_upd_int_preservation)
    apply (simp add: clkp_set_def collect_clkt_def; fast)
    apply assumption
    apply simp
    apply (auto dest!: reset_clk_set; fail)
    apply (simp add: clkp_set_def collect_clki_def; fast)
 done
done

lemma step_impl_norm_dbm_default:
  assumes "A \<turnstile>\<^sub>I \<langle>l, D\<rangle> \<leadsto>\<^bsub>k,n\<^esub> \<langle>l', D'\<rangle>" "dbm_default (curry D) n" "\<forall> c \<in> clk_set A. c \<le> n"
  shows "\<exists> M. D' = norm_upd M k n \<and> dbm_default (curry M) n"
using assms
 apply (cases rule: step_impl.cases)

  subgoal -- "Step is a time delay step"
  apply (rule exI[where x = "FW' (abstr_upd (inv_of A l) (up_canonical_upd (abstr_upd (inv_of A l) D) n)) n"])
  apply standard
  apply (simp; fail)
  apply safe
  
    apply (simp add: norm_upd_out_of_bounds1 FW'_out_of_bounds1)
    apply (subst abstr_upd_out_of_bounds1[where n = n])
    using collect_clks_inv_clk_set[of A] apply fastforce
    apply assumption
    apply (simp add: up_canonical_out_of_bounds1)
    apply (subst abstr_upd_out_of_bounds1[where n = n])
    using collect_clks_inv_clk_set[of A] apply fastforce
    apply assumption
    apply (simp; fail)

    apply (simp add: norm_upd_out_of_bounds2 FW'_out_of_bounds2)
    apply (subst abstr_upd_out_of_bounds2[where n = n])
    using collect_clks_inv_clk_set[of A] apply fastforce
    apply assumption
    apply (simp add: up_canonical_out_of_bounds2)
    apply (subst abstr_upd_out_of_bounds2[where n = n])
    using collect_clks_inv_clk_set[of A] apply fastforce
    apply assumption
    apply (simp; fail)
  done

  subgoal for g a r -- "Step is an action step"
  apply (rule exI[where x = "FW' (abstr_upd (inv_of A l') (reset'_upd (abstr_upd g D) n r 0)) n"])
  apply standard
  apply (simp; fail)
  apply safe

    apply (simp add: norm_upd_out_of_bounds1 FW'_out_of_bounds1)
    apply (subst abstr_upd_out_of_bounds1[where n = n])
    using collect_clks_inv_clk_set[of A] apply fastforce
    apply assumption
    apply (subst reset'_upd_out_of_bounds1[where n = n])
    apply (fastforce simp: collect_clkvt_def)
    apply assumption
    apply (subst abstr_upd_out_of_bounds1[where n = n])
    apply (auto simp: constraint_clk_constraint_pair clkp_set_def collect_clkt_def collect_clks_def
      collect_clock_pairs_def; blast; fail)
    apply assumption
    apply (simp; fail)

    apply (simp add: norm_upd_out_of_bounds2 FW'_out_of_bounds2)
    apply (subst abstr_upd_out_of_bounds2[where n = n])
    using collect_clks_inv_clk_set[of A] apply fastforce
    apply assumption
    apply (subst reset'_upd_out_of_bounds2[where n = n])
    apply (fastforce simp: collect_clkvt_def)
    apply assumption
    apply (subst abstr_upd_out_of_bounds2[where n = n])
    apply (auto simp: constraint_clk_constraint_pair clkp_set_def collect_clkt_def collect_clks_def
      collect_clock_pairs_def; blast; fail)
    apply assumption
    apply (simp; fail)
 done
done

inductive steps_impl ::
  "('a, nat, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('t::time) DBM' \<Rightarrow> ('t list) \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> 't DBM' \<Rightarrow> bool"
("_ \<turnstile>\<^sub>I \<langle>_, _\<rangle> \<leadsto>\<^bsub>_,_\<^esub>* \<langle>_, _\<rangle>" [61,61,61,61] 61)
where
  refl: "A \<turnstile>\<^sub>I \<langle>l, Z\<rangle> \<leadsto>\<^bsub>k,n\<^esub>* \<langle>l, Z\<rangle>" |
  step: "A \<turnstile>\<^sub>I \<langle>l, Z\<rangle> \<leadsto>\<^bsub>k,n\<^esub>* \<langle>l', Z'\<rangle> \<Longrightarrow> A \<turnstile>\<^sub>I \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>k,n\<^esub> \<langle>l'', Z''\<rangle>
        \<Longrightarrow> A \<turnstile>\<^sub>I \<langle>l, Z\<rangle> \<leadsto>\<^bsub>k,n\<^esub>* \<langle>l'', Z''\<rangle>"

lemma steps_impl_dbm_default:
  assumes "A \<turnstile>\<^sub>I \<langle>l, D\<rangle> \<leadsto>\<^bsub>k,n\<^esub>* \<langle>l', D'\<rangle>" "dbm_default (curry D) n" "\<forall> c \<in> clk_set A. c \<le> n"
  shows "dbm_default (curry D') n"
using assms
 apply induction
 apply (simp; fail)
 apply (rule step_impl_dbm_default)
by auto

lemma steps_impl_norm_dbm_default_dbm_int:
  assumes "A \<turnstile>\<^sub>I \<langle>l, D\<rangle> \<leadsto>\<^bsub>k,n\<^esub>* \<langle>l', D'\<rangle>"
    and "dbm_default (curry D) n"
    and "dbm_int (curry D) n"
    and "\<forall>c\<in>clk_set A. c \<le> n \<and> c \<noteq> 0"
    and "\<forall>(_, d)\<in>clkp_set A. d \<in> \<int>"
    and "\<forall>c\<in>set k. c \<in> \<int>"
    and "length k = Suc n"
  shows "l' = l \<and> D' = D \<or> (\<exists>M. D' = norm_upd M k n \<and>
             ((\<forall>i>n. \<forall>j. curry M i j = \<one>) \<and> (\<forall>j>n. \<forall>i. curry M i j = \<one>)) \<and> dbm_int (curry M) n)"
using assms proof (induction)
  case refl then show ?case by auto
next
  case (step A l Z k n l' Z' l'' Z'')
  then have "
    Z' = Z \<or>
    (\<exists>M. Z' = norm_upd M k n \<and>
         ((\<forall>i>n. \<forall>j. curry M i j = \<one>) \<and> (\<forall>j>n. \<forall>i. curry M i j = \<one>)) \<and> dbm_int (curry M) n)"
  by auto
  then show ?case
  proof (standard, goal_cases)
    case 1
    with step.prems step.hyps show ?thesis 
    by simp (drule step_impl_norm_dbm_default_dbm_int; simp)
  next
    case 2
    then obtain M where M:
      "Z' = norm_upd M k n" "dbm_default (curry M) n" "dbm_int (curry M) n"
    by auto
    with step.prems(3-) step.hyps show ?case
     apply -
     apply (drule step_impl_norm_dbm_default_dbm_int; simp)
      using norm_upd_default[where M = M] apply force
    using norm_upd_int_preservation[where M = M] by force
  qed
qed

definition default_ceiling_real where
  "default_ceiling_real A = (
    let M = (\<lambda> c. {m . (c, m) \<in> clkp_set A}) in
      (\<lambda> x. if M x = {} then 0 else nat (floor (Max (M x)) + 1)))"

(* This is for automata carrying real time annotations *)
lemma standard_abstraction:
  assumes "finite (clkp_set A)" "finite (collect_clkvt (trans_of A))" "\<forall>(_,m::real) \<in> clkp_set A. m \<in> \<nat>"
  shows "valid_abstraction A (clk_set A) (default_ceiling_real A)"
proof -
  from assms have 1: "finite (clk_set A)" by auto
  have 2: "collect_clkvt (trans_of A) \<subseteq> clk_set A" by auto
  from assms obtain L where L: "distinct L" "set L = clkp_set A" by (meson finite_distinct_list)
  let ?M = "\<lambda> c. {m . (c, m) \<in> clkp_set A}"
  let ?X = "clk_set A"
  let ?m = "map_of L"
  let ?k = "\<lambda> x. if ?M x = {} then 0 else nat (floor (Max (?M x)) + 1)"
  { fix c m assume A: "(c, m) \<in> clkp_set A"
    from assms(1) have "finite (snd ` clkp_set A)" by auto
    moreover have "?M c \<subseteq> (snd ` clkp_set A)" by force
    ultimately have fin: "finite (?M c)" by (blast intro: finite_subset)
    then have "Max (?M c) \<in> {m . (c, m) \<in> clkp_set A}" using Max_in A by auto
    with assms(3) have "Max (?M c) \<in> \<nat>" by auto
    then have "floor (Max (?M c)) = Max (?M c)" by (metis Nats_cases floor_of_nat of_int_of_nat_eq)
    with A have *: "?k c = Max (?M c) + 1"
    proof auto
      fix n :: int and x :: real
      assume "Max {m. (c, m) \<in> clkp_set A} = real_of_int n"
      then have "real_of_int (n + 1) \<in> \<nat>"
        using \<open>Max {m. (c, m) \<in> clkp_set A} \<in> \<nat>\<close> by auto
      then show "real (nat (n + 1)) = real_of_int n + 1"
        by (metis Nats_cases ceiling_of_int nat_int of_int_1 of_int_add of_int_of_nat_eq)
    qed
    from fin A have "Max (?M c) \<ge> m" by auto
    moreover from A assms(3) have "m \<in> \<nat>" by auto
    ultimately have "m \<le> ?k c" "m \<in> \<nat>" "c \<in> clk_set A" using A * by force+
  }
  then have "\<forall>(x, m)\<in>clkp_set A. m \<le> ?k x \<and> x \<in> clk_set A \<and> m \<in> \<nat>" by blast
  with 1 2 have "valid_abstraction A ?X ?k" by - (standard, assumption+)
  then show ?thesis unfolding default_ceiling_real_def by auto
qed

definition default_numbering where
  "default_numbering A = (SOME v. bij_betw v A {1..card A} \<and>
  (\<forall> c \<in> A. v c > 0) \<and>
  (\<forall> c. c \<notin> A \<longrightarrow> v c > card A))"

lemma default_numbering:
  assumes "finite S"
  defines "v \<equiv> default_numbering S"
  defines "n \<equiv> card S"
  shows "bij_betw v S {1..n}" (is "?A")
  and "\<forall> c \<in> S. v c > 0" (is "?B")
  and "\<forall> c. c \<notin> S \<longrightarrow> v c > n" (is "?C")
proof -
  from standard_numbering[OF \<open>finite S\<close>] obtain v' and n' :: nat where v':
    "bij_betw v' S {1..n'} \<and> (\<forall> c \<in> S. v' c > 0) \<and> (\<forall> c. c \<notin> S \<longrightarrow> v' c > n')"
  by metis
  moreover from this(1) \<open>finite S\<close> have "n' = n" unfolding n_def by (auto simp: bij_betw_same_card)
  ultimately have "?A \<and> ?B \<and> ?C" unfolding v_def default_numbering_def
  by - (drule someI[where x = v']; simp add: n_def)
  then show ?A ?B ?C by auto
qed
  
  
lemma finite_ta_Regions':
  fixes A :: "('a, 'c, real, 's) ta"
  defines "x \<equiv> SOME x. x \<notin> clk_set A"
  assumes "finite_ta A"
  shows "Regions' (clk_set A) (default_numbering (clk_set A)) (card (clk_set A)) x"
proof -
  from assms obtain x' where x': "x' \<notin> clk_set A" unfolding finite_ta_def by auto
  then have x: "x \<notin> clk_set A" unfolding x_def by (rule someI)
  from \<open>finite_ta A\<close> have "finite (clk_set A)" unfolding finite_ta_def by auto
  with default_numbering[of "clk_set A"] assms have
            "bij_betw (default_numbering (clk_set A)) (clk_set A) {1..(card (clk_set A))}"
            "\<forall>c\<in>clk_set A. 0 < (default_numbering (clk_set A)) c"
            "\<forall>c. c \<notin> clk_set A \<longrightarrow> (card (clk_set A)) < (default_numbering (clk_set A)) c"
  by auto
  then show ?thesis using x assms unfolding finite_ta_def by - (standard, auto)
qed

lemma finite_ta_RegionsD:
  assumes "finite_ta A"
  defines "S \<equiv> clk_set A"
  defines "v \<equiv> default_numbering S"
  defines "n \<equiv> card S"
  defines "x \<equiv> SOME x. x \<notin> S"
  defines "k \<equiv> default_ceiling_real A"
  shows
    "Regions' (clk_set A) v n x" "valid_abstraction A (clk_set A) k" "global_clock_numbering A v n"
proof -
  from standard_abstraction assms have k:
    "valid_abstraction A (clk_set A) k" 
  unfolding finite_ta_def by blast
  from finite_ta_Regions'[OF \<open>finite_ta A\<close>] have *: "Regions' (clk_set A) v n x" unfolding assms .
  then interpret interp: Regions' "clk_set A" k v n x .
  from interp.clock_numbering have "global_clock_numbering A v n" by blast
  with * k show
    "Regions' (clk_set A) v n x" "valid_abstraction A (clk_set A) k" "global_clock_numbering A v n"
  .
qed

definition valid_dbm where "valid_dbm M n \<equiv> dbm_int M n \<and> (\<forall> i \<le> n. M 0 i \<le> \<one>)"

lemma dbm_positive:
  assumes "M 0 (v c) \<le> \<one>" "v c \<le> n" "DBM_val_bounded v u M n"
  shows "u c \<ge> 0"
proof -
  from assms have "dbm_entry_val u None (Some c) (M 0 (v c))" unfolding DBM_val_bounded_def by auto
  with assms(1) show ?thesis
  proof (cases "M 0 (v c)", goal_cases)
    case 1
    then show ?case unfolding less_eq neutral using order_trans by (fastforce dest!: le_dbm_le)
  next
    case 2
    then show ?case unfolding less_eq neutral
    by (auto dest!: lt_dbm_le) (meson less_trans neg_0_less_iff_less not_less)
  next
    case 3
    then show ?case unfolding neutral less_eq dbm_le_def by auto
  qed
qed


lemma valid_dbm_pos:
  assumes "valid_dbm M n"
  shows "[M]\<^bsub>v,n\<^esub> \<subseteq> {u. \<forall> c. v c \<le> n \<longrightarrow> u c \<ge> 0}"
using dbm_positive assms unfolding valid_dbm_def unfolding DBM_zone_repr_def by fast

lemma (in Regions') V_alt_def:
  shows "{u. \<forall> c. v c > 0 \<and> v c \<le> n \<longrightarrow> u c \<ge> 0} = V"
unfolding V_def using clock_numbering by metis

(*
text \<open>
  An example of obtaining concrete models from our formalizations.
\<close>
lemma steps_z_norm_sound_spec:
  assumes "finite_ta A"
  obtains k v n where
  "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>k,v,n\<^esub>* \<langle>l',D'\<rangle> \<and> valid_dbm D n \<and> [D']\<^bsub>v,n\<^esub> \<noteq> {}
  \<longrightarrow> (\<exists>Z. A \<turnstile> \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>* \<langle>l',Z\<rangle> \<and> Z \<noteq> {})"
proof -
  from finite_ta_RegionsD[OF assms(1)] obtain k :: "'b \<Rightarrow> nat" and v n x where *:
    "Regions' (clk_set A) v n x" "valid_abstraction A (clk_set A) k" "global_clock_numbering A v n"
  .
  from this(1) interpret interp: Regions' "clk_set A" k v n x .
  def v' \<equiv> "\<lambda> i. if i \<le> n then (THE c. c \<in> clk_set A \<and> v c = i) else x"
  { fix l D l' D'
    assume step: "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>(k o v'),v,n\<^esub>* \<langle>l',D'\<rangle>"
    and valid: "valid_dbm D n" and non_empty: "[D']\<^bsub>v,n\<^esub> \<noteq> {}"
    from valid_dbm_pos[OF valid] interp.V_alt_def have "[D]\<^bsub>v,n\<^esub> \<subseteq> interp.V" by blas
    with valid have valid: "interp.valid_dbm D" unfolding valid_dbm_def by auto
    from step have "interp.steps_z_norm' A l D l' D'" unfolding v'_def interp.beta_interp.v'_def .
    note this = interp.steps_z_norm_sound'[OF this *(3,2) valid non_empty]
  }
  then show thesis by (blast intro: that)
qed
*)

definition "init_dbm = (\<lambda> (x, y). Le 0)"

lemma dbm_subset_refl:
  "dbm_subset n M M"
unfolding dbm_subset_def pointwise_cmp_def by simp

lemma dbm_subset_trans:
  assumes "dbm_subset n M1 M2" "dbm_subset n M2 M3"
  shows "dbm_subset n M1 M3"
using assms unfolding dbm_subset_def pointwise_cmp_def by fastforce

lemma
  "norm_lower \<infinity> k = \<infinity>"
by simp

lemma [simp]:
  "\<infinity> < x = False"
unfolding less by auto

(* XXX Copy from Normalized_Zone_Semantics *)
lemma normalized_integral_dbms_finite:
  "finite {norm M (k :: nat \<Rightarrow> nat) n | M. dbm_int M n \<and> dbm_default M n}"
proof -
  let ?u = "Max {k i | i. i \<le> n}" let ?l = "- ?u"
  let ?S = "(Le ` {d :: int. ?l \<le> d \<and> d \<le> ?u}) \<union> (Lt ` {d :: int. ?l \<le> d \<and> d \<le> ?u}) \<union> {\<infinity>}"
  from finite_set_of_finite_funs2[of "{0..n}" "{0..n}" ?S] have fin:
    "finite {f. \<forall>x y. (x \<in> {0..n} \<and> y \<in> {0..n} \<longrightarrow> f x y \<in> ?S)
                \<and> (x \<notin> {0..n} \<longrightarrow> f x y = \<one>) \<and> (y \<notin> {0..n} \<longrightarrow> f x y = \<one>)}" (is "finite ?R")
  by auto
  { fix M :: "t DBM" assume A: "dbm_int M n" "dbm_default M n"
    let ?M = "norm M k n"
    from norm_int_preservation[OF A(1)] norm_default_preservation[OF A(2)] have
      A: "dbm_int ?M n" "dbm_default ?M n"
    by auto
    { fix i j assume "i \<in> {0..n}" "j \<in> {0..n}"
      then have B: "i \<le> n" "j \<le> n" by auto
      have "?M i j \<in> ?S"
      proof (cases "?M i j = \<infinity>")
        case True then show ?thesis by auto
      next
        case False
        note not_inf = this
        with B A(1) have "get_const (?M i j) \<in> \<int>" by auto
        moreover have "?l \<le> get_const (?M i j) \<and> get_const (?M i j) \<le> ?u"
        proof (cases "i = 0")
          case True
          show ?thesis
          proof (cases "j = 0")
            case True
            with \<open>i = 0\<close> A(1) B have
              "?M i j = norm_lower (norm_upper (M 0 0) 0) 0"
            unfolding norm_def by auto
            also have "\<dots> \<noteq> \<infinity> \<longrightarrow> get_const \<dots> = 0" by (cases "M 0 0"; fastforce)
            finally show ?thesis using not_inf by auto
          next
            case False
            with \<open>i = 0\<close> B not_inf have "?M i j \<le> Le 0" "Lt (-real (k j)) \<le> ?M i j"
            unfolding norm_def
              apply (simp del: norm_upper.simps norm_lower.simps)
              apply (auto simp: less[symmetric])[]
              apply (rule ccontr)
              apply (drule not_le_imp_less)
              apply auto[]
             using \<open>i = 0\<close> B not_inf apply (auto simp: Let_def less[symmetric] intro: any_le_inf)[]
             apply (drule leI)
             apply (drule leI)
            by (rule order.trans; fastforce)
            with not_inf have "get_const (?M i j) \<le> 0" "-k j \<le> get_const (?M i j)"
            by (cases "?M i j"; auto)+
            moreover from \<open>j \<le> n\<close> have "- k j \<ge> ?l" by (auto intro: Max_ge)
            ultimately show ?thesis by auto
          qed
        next
          case False
          then have "i > 0" by simp
          show ?thesis
          proof (cases "j = 0")
            case True
            with \<open>i > 0\<close> A(1) B not_inf have "Lt 0 \<le> ?M i j" "?M i j \<le> Le (real (k i))"
            unfolding norm_def
              apply (simp del: norm_upper.simps norm_lower.simps)
              apply (auto simp: less[symmetric])[]
              
             using \<open>i > 0\<close> \<open>j = 0\<close> A(1) B not_inf unfolding norm_def
             apply (auto simp: Let_def less[symmetric] intro: any_le_inf)[]
             apply (rule ccontr)
            by (auto dest: not_le_imp_less)
            with not_inf have "0 \<le> get_const (?M i j)" "get_const (?M i j) \<le> k i"
            by (cases "?M i j"; auto)+
            moreover from \<open>i \<le> n\<close> have "k i \<le> ?u" by (auto intro: Max_ge)
            ultimately show ?thesis by auto
          next
            case False
            with \<open>i > 0\<close> A(1) B not_inf have
              "Lt (-real (k j)) \<le> ?M i j" "?M i j \<le> Le (real (k i))"
            unfolding norm_def
              apply (simp del: norm_upper.simps norm_lower.simps)
              apply (auto simp: less[symmetric])[]
              
             using \<open>i > 0\<close> \<open>j \<noteq> 0\<close> A(1) B not_inf unfolding norm_def
             apply (auto simp: Let_def less[symmetric] intro: any_le_inf)[]
             apply (rule ccontr)
            by (auto dest: not_le_imp_less)
            with not_inf have "- k j \<le> get_const (?M i j)" "get_const (?M i j) \<le> k i"
            by (cases "?M i j"; auto)+
            moreover from \<open>i \<le> n\<close> \<open>j \<le> n\<close> have "k i \<le> ?u" "k j \<le> ?u" by (auto intro: Max_ge)
            ultimately show ?thesis by auto
          qed
        qed
        ultimately show ?thesis by (cases "?M i j"; auto elim: Ints_cases)
      qed
    } moreover
    { fix i j assume "i \<notin> {0..n}"
      with A(2) have "?M i j = \<one>" by auto
    } moreover
    { fix i j assume "j \<notin> {0..n}"
      with A(2) have "?M i j = \<one>" by auto
    } moreover note the = calculation
  } then have "{norm M k n | M. dbm_int M n \<and> dbm_default M n} \<subseteq> ?R" by blast
  with fin show ?thesis by (blast intro: finite_subset)
qed

(* XXX Move *)
lemma norm_upd_norm:
  "norm_upd M k n (i, j) = norm (curry M) (\<lambda> i. k ! i) n i j"
 apply (cases "i > n")
 apply (simp add: norm_upd_out_of_bounds1 norm_def; fail)
 apply (cases "j > n"; simp add: norm_upd_out_of_bounds2 norm_def norm_upd_norm)
done

(* XXX Move *)
lemma norm_upd_norm':
  "curry (norm_upd M k n) = norm (curry M) (\<lambda> i. k ! i) n"
by (simp add: curry_def norm_upd_norm)

lemma norm_k_cong:
  assumes "\<forall> i \<le> n. k i = k' i"
  shows "norm M k n = norm M k' n"
using assms unfolding norm_def by fastforce

(* XXX Move *)
lemma norm_upd_norm'':
  fixes k :: "nat list"
  assumes "length k \<ge> Suc n"
  shows "curry (norm_upd M k n) = norm (curry M) (\<lambda> i. real (k ! i)) n"
 apply (simp add: curry_def norm_upd_norm)
 apply (rule norm_k_cong)
using assms by simp

lemma normalized_integral_dbms_finite':
  assumes "length k = Suc n"
  shows 
    "finite {norm_upd M (k :: nat list) n | M. dbm_int (curry M) n \<and> dbm_default (curry M) n}"
  (is "finite ?S")
proof -
  let ?k = "(\<lambda> i. k ! i)"
  have "norm_upd M k n = uncurry (norm (curry M) ?k n)" for M 
   apply (intro ext)
   apply clarify
   apply (subst norm_upd_norm[where k = k and M = M and n = n])
    apply simp
   apply (subst norm_k_cong)
  using assms by auto
  then have
    "?S \<subseteq> uncurry ` {norm (curry M) (\<lambda>i. k ! i) n | M. dbm_int (curry M) n \<and> dbm_default (curry M) n}"
  by auto
  moreover have "finite \<dots>"
    apply rule
    apply (rule finite_subset)
    prefer 2
    apply (rule normalized_integral_dbms_finite[where n = n and k = ?k])
  by blast
  ultimately show ?thesis by (auto intro: finite_subset)
qed

abbreviation n_eq ("_ =\<^sub>_ _" [51,51] 50) where
  "n_eq M n M' \<equiv> \<forall> i \<le> n. \<forall> j \<le> n. M i j = M' i j"

lemma FW'_FW:
  "curry (FW' M n) = FW (curry M) n"
unfolding FW'_def by auto

lemma And_eqI:
  assumes "[A]\<^bsub>v,n\<^esub> = [A1]\<^bsub>v,n\<^esub>" "[B]\<^bsub>v,n\<^esub> = [B1]\<^bsub>v,n\<^esub>" 
  shows "[And A B]\<^bsub>v,n\<^esub> = [And A1 B1]\<^bsub>v,n\<^esub>"
using assms by (simp only: And_correct[symmetric])

lemma DBM_zone_repr_up_eqI:
  assumes "clock_numbering' v n" "[A]\<^bsub>v,n\<^esub> = [B]\<^bsub>v,n\<^esub>"
  shows "[up A]\<^bsub>v,n\<^esub> = [up B]\<^bsub>v,n\<^esub>"
using assms DBM_up_complete'[where v = v] DBM_up_sound'[OF assms(1)] by fastforce

lemma canonical_eq_upto:
  assumes "clock_numbering' v n" "canonical A n" "canonical B n" "[A]\<^bsub>v,n\<^esub> \<noteq> {}" "[A]\<^bsub>v,n\<^esub> = [B]\<^bsub>v,n\<^esub>"
    "\<forall> i \<le> n. A i i = \<one>" "\<forall> i \<le> n. B i i = \<one>"
  shows "A =\<^sub>n B"
using DBM_canonical_subset_le[OF assms(1) \<open>canonical A n\<close>, of B] DBM_canonical_subset_le[OF assms(1) \<open>canonical B n\<close>, of A]
  assms(4-)
apply -
apply standard
apply standard
apply standard
apply standard
subgoal for i j
  apply (cases "i = j")
  apply fastforce
by (rule order.antisym; auto)
done

lemma DBM_zone_repr_norm_eqI:
  assumes "clock_numbering' v n" "[A]\<^bsub>v,n\<^esub> = [B]\<^bsub>v,n\<^esub>"
  shows "[norm A k n]\<^bsub>v,n\<^esub> = [norm B k n]\<^bsub>v,n\<^esub>"
oops


lemma reset'_correct:
  assumes "\<forall>c. 0 < v c \<and> (\<forall>x y. v x \<le> n \<and> v y \<le> n \<and> v x = v y \<longrightarrow> x = y)"
    and "\<forall>c\<in>set cs. v c \<le> n"
    and "\<forall>k\<le>n. 0 < k \<longrightarrow> (\<exists>c. v c = k)"
  shows "{[cs\<rightarrow>d]u | u. u \<in> [M]\<^bsub>v,n\<^esub>} = [reset' M n cs v d]\<^bsub>v,n\<^esub>"
proof safe
  fix u
  assume "u \<in> [M]\<^bsub>v,n\<^esub>"
  with DBM_reset'_complete[OF _ assms(1,2)] show
    "[cs\<rightarrow>d]u \<in> [reset' M n cs v d]\<^bsub>v,n\<^esub>"
  by (auto simp: DBM_zone_repr_def)
next
  fix u
  assume "u \<in> [reset' M n cs v d]\<^bsub>v,n\<^esub>"
  show "\<exists>u'. u = [cs\<rightarrow>d]u' \<and> u' \<in> [M]\<^bsub>v,n\<^esub>"
  proof (cases "[M]\<^bsub>v,n\<^esub> = {}")
    case True
    with \<open>u \<in> _\<close> DBM_reset'_empty[OF assms(3,1,2)] show ?thesis by auto
  next
    case False
    from DBM_reset'_sound[OF assms(3,1,2) \<open>u \<in> _\<close>] obtain ts where
      "set_clocks cs ts u \<in> [M]\<^bsub>v,n\<^esub>"
    by blast
    from DBM_reset'_resets'[OF assms(1,2)] \<open>u \<in> _\<close> \<open>_ \<noteq> {}\<close>
    have "u = [cs \<rightarrow> d](set_clocks cs ts u)" by (fastforce simp: reset_set DBM_zone_repr_def)
    with \<open>set_clocks _ _ _ \<in> _\<close> show ?thesis by auto
  qed
qed

lemma DBM_zone_repr_reset'_eqI:
  assumes "\<forall>c. 0 < v c \<and> (\<forall>x y. v x \<le> n \<and> v y \<le> n \<and> v x = v y \<longrightarrow> x = y)"
    and "\<forall>c\<in>set cs. v c \<le> n"
    and "\<forall>k\<le>n. 0 < k \<longrightarrow> (\<exists>c. v c = k)"
    and "[A]\<^bsub>v,n\<^esub> = [B]\<^bsub>v,n\<^esub>"
  shows "[reset' A n cs v d]\<^bsub>v,n\<^esub> = [reset' B n cs v d]\<^bsub>v,n\<^esub>"
using assms(4) reset'_correct[OF assms(1-3)] by blast

lemma DBM_zone_repr_eqI:
  assumes "[A]\<^bsub>v,n\<^esub> = [B]\<^bsub>v,n\<^esub>" "(f A) =\<^sub>n (g B)"
  shows "[f A]\<^bsub>v,n\<^esub> = [g B]\<^bsub>v,n\<^esub>"
oops

print_statement up_canonical_upd_up_canonical

lemma up_canonical_upd_up_canonical':
  shows "curry (up_canonical_upd M n) =\<^sub>n up_canonical (curry M)"
by (auto intro: up_canonical_upd_up_canonical)

(* XXX Move, here unnecessary *)
lemma And_commute:
  "And A B = And B A"
by (auto intro: min.commute)

thm FW_zone_equiv

lemma up_canonical_neg_diag:
  assumes "M i i < \<one>"
  shows "(up_canonical M) i i < \<one>"
using assms unfolding up_canonical_def by auto

lemma up_neg_diag:
  assumes "M i i < \<one>"
  shows "(up M) i i < \<one>"
using assms unfolding up_def by (auto split: split_min)

thm reset''_diag_preservation

lemma reset''_neg_diag:
  fixes v :: "'c \<Rightarrow> nat"
  assumes "\<forall> c. v c > 0" "M i i < \<one>" "i \<le> n"
  shows "(reset'' M n cs v d) i i < \<one>"
using reset''_diag_preservation[OF assms(1), where M = M and n = n] assms(2-) by auto

lemma FW_canonical':
  assumes "\<forall> i \<le> n. (FW M n) i i \<ge> \<one>"
  shows "canonical (FW M n) n"
using FW_neg_cycle_detect assms by - (rule fw_canonical; fastforce)

lemma FW_neg_diag_equiv:
  assumes diag: "\<exists> i \<le> n. (FW A n) i i < \<one>"
      and surj: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
      and cn: "\<forall> c. v c > 0"
      and equiv: "[A]\<^bsub>v,n\<^esub> = [B]\<^bsub>v,n\<^esub>"
  shows "\<exists> i \<le> n. (FW B n) i i < \<one>"
proof -
  from assms obtain i where "(FW A n) i i < \<one>" "i \<le> n" by force
  with neg_diag_empty[OF surj] FW_zone_equiv[OF surj] equiv have "[B]\<^bsub>v,n\<^esub> = {}" by fastforce
  with FW_zone_equiv[OF surj] have "[FW B n]\<^bsub>v,n\<^esub> = {}" by auto
  then obtain i where
    "(FW B n) i i < \<one>" "i \<le> n"
  using FW_detects_empty_zone[OF surj, where M = B, folded neutral] cn
  by auto
  then show ?thesis by auto
qed

lemma FW_dbm_zone_repr_eqI2:
  assumes f_diag: "\<And> M i. i \<le> n \<Longrightarrow> M i i < \<one> \<Longrightarrow> (f M) i i < \<one>"
      and g_diag: "\<And> M i. i \<le> n \<Longrightarrow> M i i < \<one> \<Longrightarrow> (g M) i i < \<one>"
      and canonical:
      "\<And> A B. canonical A n \<Longrightarrow> canonical B n \<Longrightarrow> \<forall> i \<le> n. A i i = \<one> \<Longrightarrow> \<forall> i \<le> n. B i i = \<one>
      \<Longrightarrow> [A]\<^bsub>v,n\<^esub> = [B]\<^bsub>v,n\<^esub>
      \<Longrightarrow> [f A]\<^bsub>v,n\<^esub> = [g B]\<^bsub>v,n\<^esub>"
      and surj: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
      and cn: "\<forall> c. v c > 0"
      and equiv: "[A]\<^bsub>v,n\<^esub> = [B]\<^bsub>v,n\<^esub>"
      and diag: "\<forall> i \<le> n. A i i \<le> \<one>" "\<forall> i \<le> n. B i i \<le> \<one>"
  shows "[f (FW A n)]\<^bsub>v,n\<^esub> = [g (FW B n)]\<^bsub>v,n\<^esub>"
proof (cases "\<forall> i \<le> n. (FW A n) i i \<ge> \<one>")
  case True
  with FW_neg_diag_equiv[OF _ surj cn equiv[symmetric]] have *: "\<forall>i\<le>n. \<one> \<le> (FW B n) i i" by fastforce
  with True FW_diag_preservation[where M = A, OF diag(1)] FW_diag_preservation[where M = B, OF diag(2)]
        FW_zone_equiv[OF surj, of A] FW_zone_equiv[OF surj, of B] equiv
  show ?thesis by - (rule canonical[OF FW_canonical'[OF True] FW_canonical'[OF *]]; fastforce)
next
  case False
  then obtain i where "(FW A n) i i < \<one>" "i \<le> n" by force
  moreover with FW_neg_diag_equiv[OF _ surj cn equiv] obtain j where
    "(FW B n) j j < \<one>" "j \<le> n"
  using FW_detects_empty_zone[OF surj, where M = B, folded neutral] cn by auto
  ultimately have "f (FW A n) i i < \<one>" "g (FW B n) j j < \<one>" using f_diag g_diag by auto
  with \<open>i \<le> n\<close> \<open>j \<le> n\<close> neg_diag_empty[OF surj] show ?thesis by auto
qed

lemma FW_dbm_zone_repr_eqI:
  assumes f_diag: "\<And> M i. i \<le> n \<Longrightarrow> M i i < \<one> \<Longrightarrow> (f M) i i < \<one>"
      and g_diag: "\<And> M i. i \<le> n \<Longrightarrow> M i i < \<one> \<Longrightarrow> (g M) i i < \<one>"
      and canonical: "\<And> M. canonical M n \<Longrightarrow> [f M]\<^bsub>v,n\<^esub> = [g M]\<^bsub>v,n\<^esub>"
      and surj: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
  shows "[f (FW M n)]\<^bsub>v,n\<^esub> = [g (FW M n)]\<^bsub>v,n\<^esub>"
proof (cases "\<forall> i \<le> n. (FW M n) i i \<ge> \<one>")
  case True
  from canonical[OF FW_canonical'[OF True]] show ?thesis .
next
  case False
  then obtain i where "(FW M n) i i < \<one>" "i \<le> n" by force
  with f_diag g_diag have "f (FW M n) i i < \<one>" "g (FW M n) i i < \<one>" by auto
  with \<open>i \<le> n\<close> neg_diag_empty[OF surj] show ?thesis by auto
qed

lemma FW_dbm_zone_repr_eqI':
  assumes f_diag: "\<And> M i. i \<le> n \<Longrightarrow> M i i < \<one> \<Longrightarrow> (f M) i i < \<one>"
      and g_diag: "\<And> M i. i \<le> n \<Longrightarrow> M i i < \<one> \<Longrightarrow> (g M) i i < \<one>"
      and canonical: "\<And> M. canonical M n \<Longrightarrow> \<forall> i \<le> n. M i i = \<one> \<Longrightarrow> [f M]\<^bsub>v,n\<^esub> = [g M]\<^bsub>v,n\<^esub>"
      and surj: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
      and diag: "\<forall> i \<le> n. M i i \<le> \<one>"
  shows "[f (FW M n)]\<^bsub>v,n\<^esub> = [g (FW M n)]\<^bsub>v,n\<^esub>"
proof (cases "\<forall> i \<le> n. (FW M n) i i \<ge> \<one>")
  case True
  with FW_diag_preservation[where M = M, OF diag] canonical[OF FW_canonical'[OF True]] show ?thesis
  by fastforce
next
  case False
  then obtain i where "(FW M n) i i < \<one>" "i \<le> n" by force
  with f_diag g_diag have "f (FW M n) i i < \<one>" "g (FW M n) i i < \<one>" by auto
  with \<open>i \<le> n\<close> neg_diag_empty[OF surj] show ?thesis by auto
qed

lemma
  assumes f_diag: "\<And> M i. i \<le> n \<Longrightarrow> M i i < \<one> \<Longrightarrow> (f M) i i < \<one>"
      and g_diag: "\<And> M i. i \<le> n \<Longrightarrow> M i i < \<one> \<Longrightarrow> (g M) i i < \<one>"
      and "[A]\<^bsub>v,n\<^esub> = [B]\<^bsub>v,n\<^esub>"
      and surj: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
  shows "[f (FW A n)]\<^bsub>v,n\<^esub> = [g (FW B n)]\<^bsub>v,n\<^esub>"
oops

thm FW_dbm_zone_repr_eqI

lemma delay_step_impl_correct:
  assumes "canonical (curry D) n" (* XXX atm unused, would need for optimized variant without full FW *)
          "clock_numbering' v n" "\<forall>c\<in>collect_clks (inv_of A l). v c = c \<and> v c > 0 \<and> v c < n"
      and surj: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
  assumes D_inv: "D_inv = abstr (inv_of A l) (\<lambda>i j. \<infinity>) v"
  shows
  "[curry (abstr_upd (inv_of A l) (up_canonical_upd (FW' (abstr_upd (inv_of A l) D) n) n))]\<^bsub>v,n\<^esub> =
  [And (up (And (curry D) D_inv)) D_inv]\<^bsub>v,n\<^esub>"
apply (subst abstr_upd_abstr')
defer
apply (subst abstr_abstr'[symmetric])
defer
unfolding D_inv
apply (subst And_abstr[symmetric])
defer
defer
apply (rule And_eqI)
apply (subst DBM_up_to_equiv[OF up_canonical_upd_up_canonical'])
apply (subst FW'_FW)
apply (subst FW_dbm_zone_repr_eqI[where g = up])
using up_canonical_neg_diag apply (auto; fail)
using up_neg_diag apply (auto; fail)
apply (rule up_canonical_equiv_up; assumption; fail)
defer
apply (rule DBM_zone_repr_up_eqI)
defer
apply (subst FW_zone_equiv[symmetric])
defer
apply (subst abstr_upd_abstr')
defer
apply (subst abstr_abstr'[symmetric])
defer
apply (subst And_abstr[symmetric])
using assms(2) apply fastforce
using assms(3) apply fastforce
apply (rule HOL.refl; fail)
apply (rule HOL.refl; fail)
using assms(3) apply fastforce
apply (rule surj; fail)
using assms(3) apply fastforce
done

lemma reset'''_reset'_upd'':
  assumes "\<forall>c\<in>set cs. c \<noteq> 0"
  shows "(curry (reset'_upd M n cs d)) =\<^sub>n (reset''' (curry M) n cs d)"
using reset'''_reset'_upd'[OF assms] by auto

lemma abstra_upd_diag_preservation:
  assumes "\<forall> i \<le> n. M (i, i) \<le> \<one>" "constraint_clk ac \<noteq> 0"
  shows "\<forall> i \<le> n. (abstra_upd ac M) (i, i) \<le> \<one>"
using assms by (cases ac) auto

lemma abstr_upd_diag_preservation:
  assumes "\<forall> i \<le> n. M (i, i) \<le> \<one>" "\<forall> c \<in> collect_clks cc. c \<noteq> 0"
  shows "\<forall> i \<le> n. (abstr_upd cc M) (i, i) \<le> \<one>"
using assms unfolding abstr_upd_def
by (induction cc arbitrary: M) (auto simp: abstra_upd_diag_preservation)


lemma action_step_impl_correct:
  assumes "canonical (curry D) n" (* XXX atm unused, would need for optimized variant without full FW *)
          "clock_numbering' v n" "\<forall>c\<in>collect_clks (inv_of A l'). v c = c \<and> c > 0 \<and> v c \<le> n"
          "\<forall>c\<in>collect_clks g. v c = c \<and> c > 0 \<and> v c \<le> n"
          "\<forall>c\<in> set r. v c = c \<and> c > 0 \<and> v c \<le> n"
          "\<forall> i \<le> n. D (i, i) \<le> \<one>"
      and surj: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
  shows
  "[curry (abstr_upd (inv_of A l') (reset'_upd (FW' (abstr_upd g D) n) n r 0))]\<^bsub>v,n\<^esub> =
   [And (reset' (And (curry D) (abstr g (\<lambda>i j. \<infinity>) v)) n r v 0)
                               (abstr (inv_of A l') (\<lambda>i j. \<infinity>) v)]\<^bsub>v,n\<^esub>"
apply (subst abstr_upd_abstr')
defer
apply (subst abstr_abstr'[symmetric])
defer
apply (subst And_abstr[symmetric])
defer
defer
apply (rule And_eqI)
apply (subst DBM_up_to_equiv[OF reset'''_reset'_upd''])
defer
apply (subst reset''_reset'''[symmetric, where v = v])
defer
apply (subst FW'_FW)
apply (subst FW_dbm_zone_repr_eqI'[where g = "\<lambda> M. reset' M n r v 0"])
apply (rule reset''_neg_diag; fastforce simp: assms(2))
apply (rule DBM_reset'_neg_diag_preservation')
apply assumption
apply assumption
using assms(2) apply fastforce
using assms(5) apply fastforce
apply (rule reset'_reset''_equiv[symmetric])
apply assumption
apply (simp; fail)
defer
defer
defer
defer
defer
defer
apply (rule DBM_zone_repr_reset'_eqI)
defer
defer
defer
apply (subst FW_zone_equiv[symmetric])
defer
apply (subst abstr_upd_abstr')
defer
apply (subst abstr_abstr'[symmetric])
defer
apply (subst And_abstr[symmetric])
using assms apply fastforce
using assms(4) apply fastforce
apply (rule HOL.refl; fail)
apply (rule HOL.refl; fail)
using assms(3) apply fastforce
using assms(3) apply fastforce
using assms(3) apply fastforce
using assms(5) apply fastforce
using assms(5) apply fastforce
using assms(6) apply fastforce
using assms(2) apply fastforce
using assms(5) apply fastforce
using assms(7) apply fastforce
using assms(4) abstr_upd_diag_preservation[OF assms(6)] apply fastforce
using assms(5) apply fastforce
using surj apply fastforce
using assms(4) apply fastforce
using assms(4) apply fastforce
done

lemma norm_eq_upto:
  assumes "A =\<^sub>n B"
  shows "norm A k n =\<^sub>n norm B k n"
using assms by (auto simp: norm_def)

thm cyc_free_not_empty

thm cyc_free_not_empty[OF canonical_cyc_free]

(* XXX Copy of Normalized_Zone_Semantics.Regions.norm_empty_diag_preservation *)
lemma norm_empty_diag_preservation:
  fixes k :: "nat \<Rightarrow> nat"
  assumes "i \<le> n"
  assumes "M i i < Le 0"
  shows "norm M k n i i < Le 0"
proof -
  have "\<not> Le (k i) \<prec> Le 0" by auto
  with assms show ?thesis unfolding norm_def by (auto simp: Let_def less)
qed

lemma And_diag1:
  assumes "A i i \<le> \<one>"
  shows "(And A B) i i \<le> \<one>"
using assms by (auto split: split_min)

lemma And_diag2:
  assumes "B i i \<le> \<one>"
  shows "(And A B) i i \<le> \<one>"
using assms by (auto split: split_min)

lemma norm_impl_correct:
  fixes k :: "nat list"
  assumes (* XXX atm unused, would need for optimized variant without full FW *)
          "clock_numbering' v n"
          "\<forall> i \<le> n. D (i, i) \<le> \<one>"
          "\<forall> i \<le> n. M i i \<le> \<one>"
      and surj: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
      and k: "Suc n \<le> length k"
      and equiv: "[curry D]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>"
  shows
    "[curry (FW' (norm_upd (FW' D n) k n) n)]\<^bsub>v,n\<^esub> = [norm (FW M n) (\<lambda> i. k ! i) n]\<^bsub>v,n\<^esub>"
apply (subst FW'_FW)
apply (subst FW_zone_equiv[symmetric, OF surj])
apply (subst norm_upd_norm'')
apply (simp add: k)

apply (subst FW'_FW)
apply (rule FW_dbm_zone_repr_eqI2)
defer
defer
apply (rule DBM_up_to_equiv)
apply (rule norm_eq_upto)
apply (rule canonical_eq_upto)
apply (rule assms)
apply assumption
apply assumption
using \<open>clock_numbering' v n\<close> apply - apply (rule cyc_free_not_empty[OF canonical_cyc_free]; simp)
apply assumption
apply simp
apply simp
apply (rule assms)
apply simp
apply (rule equiv)
using assms(2) apply fastforce
using assms(3) apply fastforce

apply (rule norm_empty_diag_preservation[folded neutral]; assumption)+
done

lemma norm_action_step_impl_correct:
  fixes k :: "nat list"
  assumes "canonical (curry D) n" (* XXX atm unused, would need for optimized variant without full FW *)
          "clock_numbering' v n" "\<forall>c\<in>collect_clks (inv_of A l'). v c = c \<and> c > 0 \<and> v c \<le> n"
          "\<forall>c\<in>collect_clks g. v c = c \<and> c > 0 \<and> v c \<le> n"
          "\<forall>c\<in> set r. v c = c \<and> c > 0 \<and> v c \<le> n"
          "\<forall> i \<le> n. D (i, i) \<le> \<one>"
      and surj: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
      and k: "Suc n \<le> length k"
  shows
  "[curry (FW' (norm_upd (FW' (abstr_upd (inv_of A l') (reset'_upd (FW' (abstr_upd g D) n) n r 0)) n) k n) n)]\<^bsub>v,n\<^esub> =
   [norm (FW(And (reset' (And (curry D) (abstr g (\<lambda>i j. \<infinity>) v)) n r v 0)
                               (abstr (inv_of A l') (\<lambda>i j. \<infinity>) v)) n) (\<lambda> i. k ! i) n]\<^bsub>v,n\<^esub>"
apply (rule norm_impl_correct)
apply (rule assms)
defer
defer
apply (rule surj)
apply (rule k)
apply (rule action_step_impl_correct; rule assms)

apply (rule abstr_upd_diag_preservation)
apply safe[]
apply (subst reset'_upd_diag_preservation)
using assms(5) apply fastforce
apply assumption
apply (simp add: FW'_def)
apply (rule FW_diag_preservation[rule_format])
apply (simp add: curry_def)
apply (rule abstr_upd_diag_preservation[rule_format, where n = n])
using assms(6) apply fastforce
using assms(4) apply fastforce
apply assumption
apply assumption
using assms(3) apply fastforce

apply safe
apply (rule And_diag1)
apply (rule DBM_reset'_diag_preservation[rule_format])
apply (rule And_diag1)
using assms(6) apply simp
using assms(2) apply simp
using assms(5) apply metis
apply assumption
done

(* XXX Move *)
lemma up_diag_preservation:
  assumes "M i i \<le> \<one>"
  shows "(up M) i i \<le> \<one>"
using assms unfolding up_def by (auto split: split_min)

lemma norm_delay_step_impl_correct:
  fixes k :: "nat list"
  assumes "canonical (curry D) n" (* XXX atm unused, would need for optimized variant without full FW *)
          "clock_numbering' v n" "\<forall>c\<in>collect_clks (inv_of A l). v c = c \<and> v c > 0 \<and> v c < n"
          "\<forall> i \<le> n. D (i, i) \<le> \<one>"
      and surj: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
      and k: "Suc n \<le> length k"
  assumes D_inv: "D_inv = abstr (inv_of A l) (\<lambda>i j. \<infinity>) v"
  shows
  "[curry (FW' (norm_upd (FW' (abstr_upd (inv_of A l) (up_canonical_upd (FW' (abstr_upd (inv_of A l) D) n) n)) n) k n) n)]\<^bsub>v,n\<^esub> =
  [norm (FW(And (up (And (curry D) D_inv)) D_inv) n) (\<lambda> i. k ! i) n]\<^bsub>v,n\<^esub>"
apply (rule norm_impl_correct)
apply (rule assms)
defer
defer
apply (rule surj)
apply (rule k)
apply (rule delay_step_impl_correct; rule assms)

apply (rule abstr_upd_diag_preservation)
apply safe[]
apply (subst up_canonical_upd_diag_preservation)
apply (simp add: FW'_def)
apply (rule FW_diag_preservation[rule_format])
apply (simp add: curry_def)
apply (rule abstr_upd_diag_preservation[rule_format, where n = n])
using assms(4) apply fastforce
using assms(3) apply fastforce
apply assumption
apply assumption
using assms(3) apply fastforce

apply safe
apply (rule And_diag1)
apply (rule up_diag_preservation)
apply (rule And_diag1)
using assms(4) by fastforce

lemma
  fixes k :: "nat list"
  assumes "canonical (curry D) n" "d \<ge> 0" "\<forall>i \<le> n. D (i, i) = \<one>"
          "clock_numbering' v n" "\<forall> c \<in> set cs. v c = c"
      and surj: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
      and step: "A \<turnstile>\<^sub>I \<langle>l,D\<rangle> \<leadsto>\<^bsub>k,n\<^esub> \<langle>l',D'\<rangle>"
      and "[curry D]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>"
  defines "k' \<equiv> \<lambda> i. if i \<le> n then op_list_get k i else 0"
  shows "\<exists> M'. A \<turnstile> \<langle>l,M\<rangle> \<leadsto>\<^bsub>k',v,n\<^esub> \<langle>l',M'\<rangle> \<and> [curry D']\<^bsub>v,n\<^esub> = [M']\<^bsub>v,n\<^esub>"
using step apply cases
apply simp
oops

lemma
  fixes k :: "nat list"
  assumes "canonical (curry D) n" "d \<ge> 0" "\<forall>i \<le> n. D (i, i) = \<one>"
          "clock_numbering' v n" "\<forall> c \<in> set cs. v c = c"
      and surj: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
      and step: "A \<turnstile>\<^sub>I \<langle>l,D\<rangle> \<leadsto>\<^bsub>k,n\<^esub> \<langle>l',D'\<rangle>"
      and "curry D =\<^sub>n M"
  defines "k' \<equiv> \<lambda> i. if i \<le> n then op_list_get k i else 0"
  shows "\<exists> M'. A \<turnstile> \<langle>l,M\<rangle> \<leadsto>\<^bsub>k',v,n\<^esub> \<langle>l',M'\<rangle> \<and> curry D' =\<^sub>n M'"
using step apply cases
apply simp
oops

lemma
  fixes k :: "nat list"
  assumes "canonical M n" "d \<ge> 0" "\<forall>i \<le> n. M i i = \<one>"
          "clock_numbering' v n" "\<forall> c \<in> set cs. v c = c"
      and surj: "\<forall> k \<le> n. k > 0 \<longrightarrow> (\<exists> c. v c = k)"
      and step: "A \<turnstile>\<^sub>I \<langle>l,D\<rangle> \<leadsto>\<^bsub>k,n\<^esub> \<langle>l',D'\<rangle>"
  defines "k' \<equiv> \<lambda> i. if i \<le> n then op_list_get k i else 0"
  shows "A \<turnstile> \<langle>l,curry D\<rangle> \<leadsto>\<^bsub>k',v,n\<^esub> \<langle>l',curry D'\<rangle>"
using step apply cases
apply simp
apply (subst norm_upd_norm')
apply (subst FW'_FW)
oops


section \<open>Mapping Transitions\<close>

type_synonym
  ('a, 'c, 'time, 's) transition_fun = "'s \<Rightarrow> (('c, 'time) cconstraint * 'a * 'c list * 's) list"

definition transition_\<alpha> :: "('a, 'c, 'time, 's) transition_fun \<Rightarrow> ('a, 'c, 'time, 's) transition set"
where
  "transition_\<alpha> f = {(s, t) | s t. t \<in> set (f s)}"

definition transition_rel where
  "transition_rel = (br transition_\<alpha> (\<lambda>_. True))"


section \<open>Reachability Checker\<close>

locale Reachability_Problem =
  fixes A :: "('a, nat, real, 's) ta" (* :: "('a, 'c, 't::time, 's) ta" *)
    and l\<^sub>0 :: 's
    and F :: "'s list"
    and trans_fun :: "('a, nat, real, 's) transition_fun"
  assumes finite:  "finite_ta A"
      and finite_trans: "finite (trans_of A)"
      and triv_clock_numbering: "clk_set A = {1..card (clk_set A)}"
      and valid: "\<forall>c\<in>clk_set A. c \<le> card (clk_set A) \<and> c \<noteq> 0" "\<forall>(_, d)\<in>clkp_set A. d \<in> \<int>"
      and not_empty: "clk_set A \<noteq> {}"
      and trans_fun: "(trans_fun, trans_of A) \<in> transition_rel"

begin

  definition "X \<equiv> clk_set A"
  definition "v \<equiv> default_numbering X"
  definition "n \<equiv> card X"
  definition "x \<equiv> SOME x. x \<notin> X"
  definition "k \<equiv> default_ceiling_real A"

  definition "k' \<equiv> map (real o k) [0..<Suc n]"

  lemma n_gt_0[intro, simp]:
    "n > 0"
  unfolding n_def X_def using not_empty card_0_eq finite_atLeastAtMost gr0I triv_clock_numbering
  by force 

  lemma n_bounded:
    "\<forall> c \<in> X. c \<le> n"
  unfolding n_def X_def using triv_clock_numbering by auto

  definition "locations \<equiv> {l\<^sub>0} \<union> fst ` trans_of A \<union> (snd o snd o snd o snd) ` trans_of A"

  lemma finite_locations:
    "finite locations"
  unfolding locations_def using finite_trans by auto

  definition "F_rel \<equiv> \<lambda> (l, _). l \<in> set F"
  
  definition "a\<^sub>0 = (l\<^sub>0, init_dbm)"

  definition "subsumes = (\<lambda> (l, M) (l', M'). l = l' \<and> dbm_subset n M M')"

  definition "E = (\<lambda> (l, M) (l', M'). step_impl A l M k' n l' M')"

  lemma E_closure:
    "E\<^sup>*\<^sup>* a\<^sub>0 (l', M') \<longleftrightarrow> A \<turnstile>\<^sub>I \<langle>l\<^sub>0, init_dbm\<rangle> \<leadsto>\<^bsub>k',n\<^esub>* \<langle>l', M'\<rangle>"
  unfolding a\<^sub>0_def E_def
  apply safe
  apply (drule rtranclp_induct[where P = "\<lambda> (l', M'). A \<turnstile>\<^sub>I \<langle>l\<^sub>0, init_dbm\<rangle> \<leadsto>\<^bsub>k',n\<^esub>* \<langle>l', M'\<rangle>"];
         auto dest: step intro: refl; fail
        )
  by (induction rule: steps_impl.induct; simp add: rtranclp.intros(2))

  lemma E_closure_finite:
    "finite {x. E\<^sup>*\<^sup>* a\<^sub>0 x}"
  proof -
    have k': "map real (map k [0..<Suc n]) = k'" unfolding k'_def by auto
    have *: "(l, M) = a\<^sub>0 \<or>
    (\<exists>M'. M = norm_upd M' k' n \<and>
          dbm_default (curry M') n \<and> dbm_int (curry M') n)"
      if "E\<^sup>*\<^sup>* a\<^sub>0 (l, M)" for l M
    using that unfolding E_closure
    apply -
    apply (drule steps_impl_norm_dbm_default_dbm_int)
    apply (auto simp: init_dbm_def neutral)[]
    apply (auto simp: init_dbm_def)[]
    defer
    defer
    apply (simp add: k'_def)
    apply (simp add: k'_def)
    apply (simp add: a\<^sub>0_def)
    using valid by (auto simp: n_def X_def)
    moreover have **: "l \<in> locations" if "E\<^sup>*\<^sup>* a\<^sub>0 (l, M)" for l M
    using that unfolding E_closure locations_def
     apply (induction rule: steps_impl.induct)
     apply (simp; fail)
    by (cases rule: step_impl.cases, assumption; force)
    have
      "{x. E\<^sup>*\<^sup>* a\<^sub>0 x} \<subseteq> {a\<^sub>0} \<union> (locations \<times> {norm_upd M k' n | M. dbm_int (curry M) n \<and> dbm_default (curry M) n})"
    (is "_ \<subseteq> _ \<union> ?S")
     apply safe
      apply (rule **)
      apply assumption
      apply (drule *)
    by auto
    moreover have "finite ?S"
    using normalized_integral_dbms_finite'[where k = "map k [0..<Suc n]"] finite_locations
    by (auto simp: k'_def)
    ultimately show ?thesis by (auto intro: finite_subset)
  qed

  lemma finite_X:
    "finite X"
  using triv_clock_numbering unfolding X_def by (metis finite_atLeastAtMost)

  lemma X_unfold:
    "X = {1..<Suc (card X)}"
  unfolding X_def using triv_clock_numbering atLeastLessThanSuc_atLeastAtMost by blast 

  lemma X_alt_def:
    "X = {1..<Suc n}"
  using X_unfold n_def by auto

  lemma v_bij:
    "bij_betw v {1..<Suc n} {1..n}"
  proof -
    from default_numbering(1)[of X] triv_clock_numbering finite_X have
      "bij_betw (default_numbering X) X {1..card X}"
    unfolding X_def by auto
    then show ?thesis unfolding v_def n_def by (subst (asm) (2) X_unfold)
  qed

  sublocale Regions' "{1..<Suc n}" k v n "Suc n"
    apply standard
    apply (simp; fail)
    using default_numbering(2)[OF finite_X] apply (subst (asm) X_unfold) apply (simp add: v_def n_def; fail)
    using default_numbering(3)[OF finite_X] apply (subst (asm) X_unfold) apply (simp add: v_def n_def; fail)
    apply (rule v_bij)
  by auto

  lemma step_impl_sound:
    assumes "A \<turnstile>\<^sub>I \<langle>l,D\<rangle> \<leadsto>\<^bsub>k',n\<^esub> \<langle>l',D'\<rangle>"
    shows "step_z_norm' A l (curry D) l' (curry D')"
  using assms
  apply (cases )
  apply auto
  sorry

  lemma step_impl_complete:
    assumes "step_z_norm' A l (curry D) l' (curry D')"
    shows "A \<turnstile>\<^sub>I \<langle>l,D\<rangle> \<leadsto>\<^bsub>k',n\<^esub> \<langle>l',D'\<rangle>"
  using assms
  apply (cases )
  apply auto
  sorry

  lemma step_impl_mono:
    assumes "A \<turnstile>\<^sub>I \<langle>l,D\<rangle> \<leadsto>\<^bsub>k',n\<^esub> \<langle>l',D'\<rangle>" "global_clock_numbering A v n" "valid_abstraction A X k"
    and     "valid_dbm (curry D)" "valid_dbm (curry M)"
    and "[curry D]\<^bsub>v,n\<^esub> \<subseteq> [curry M]\<^bsub>v,n\<^esub>"
    shows "\<exists> M'. A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>k',n\<^esub> \<langle>l', M'\<rangle> \<and> [curry D']\<^bsub>v,n\<^esub> \<subseteq> [curry M']\<^bsub>v,n\<^esub>"
  proof -
    from step_z_beta_mono[OF step_impl_sound[OF assms(1)] assms(2) assms(3)[unfolded X_alt_def] assms(4-)]
    obtain M' where M':
      "step_z_norm' A l (curry M) l' M'" "[curry D']\<^bsub>v,n\<^esub> \<subseteq> [M']\<^bsub>v,n\<^esub>"
    by auto
    let ?M' = "uncurry M'"
    from M' have
      "step_z_norm' A l (curry M) l' (curry ?M')" "[curry D']\<^bsub>v,n\<^esub> \<subseteq> [curry ?M']\<^bsub>v,n\<^esub>"
    by auto
    with step_impl_complete[OF this(1)] show ?thesis by blast
  qed

  lemma valid_dbm_reachable:
    assumes "E\<^sup>*\<^sup>* a\<^sub>0 (l, M)"
    shows "valid_dbm (curry M)"
  sorry

  (* XXX This does not hold at the moment *)
  lemma canonical_reachable:
    assumes "E\<^sup>*\<^sup>* a\<^sub>0 (l, M)"
    shows "canonical (curry M) n"
  sorry

  lemma diag_reachable:
    assumes "E\<^sup>*\<^sup>* a\<^sub>0 (l, M)"
    shows "\<forall> i \<le> n. (curry M) i i = \<one>"
  sorry

  lemma global_clock_numbering:
    "global_clock_numbering A v n"
  sorry

  lemma valid_abstraction:
    "valid_abstraction A X k"
  sorry

  lemma step_impl_mono_reachable:
    assumes "A \<turnstile>\<^sub>I \<langle>l,D\<rangle> \<leadsto>\<^bsub>k',n\<^esub> \<langle>l',D'\<rangle>"
    and     "E\<^sup>*\<^sup>* a\<^sub>0 (l, D)" "E\<^sup>*\<^sup>* a\<^sub>0 (l, M)"
    and "[curry D]\<^bsub>v,n\<^esub> \<subseteq> [curry M]\<^bsub>v,n\<^esub>"
    shows "\<exists> M'. A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>k',n\<^esub> \<langle>l', M'\<rangle> \<and> [curry D']\<^bsub>v,n\<^esub> \<subseteq> [curry M']\<^bsub>v,n\<^esub>"
  using step_impl_mono[OF _ global_clock_numbering valid_abstraction] valid_dbm_reachable assms
  by auto

  lemma step_impl_mono_reachable':
    assumes "A \<turnstile>\<^sub>I \<langle>l,D\<rangle> \<leadsto>\<^bsub>k',n\<^esub> \<langle>l',D'\<rangle>"
    and     "E\<^sup>*\<^sup>* a\<^sub>0 (l, D)" "E\<^sup>*\<^sup>* a\<^sub>0 (l, M)"
    and "dbm_subset n D M"
    shows "\<exists> M'. A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>k',n\<^esub> \<langle>l', M'\<rangle> \<and> [curry D']\<^bsub>v,n\<^esub> \<subseteq> [curry M']\<^bsub>v,n\<^esub>"
  using step_impl_mono[OF _ global_clock_numbering valid_abstraction] valid_dbm_reachable assms
    subset_eq_pointwise_le[OF canonical_reachable diag_reachable, where M' = "curry M"]
    global_clock_numbering diag_reachable
  unfolding dbm_subset_def
  by metis

  lemma step_impl_mono_reachable'':
    assumes "A \<turnstile>\<^sub>I \<langle>l,D\<rangle> \<leadsto>\<^bsub>k',n\<^esub> \<langle>l',D'\<rangle>"
    and     "E\<^sup>*\<^sup>* a\<^sub>0 (l, D)" "E\<^sup>*\<^sup>* a\<^sub>0 (l, M)"
    and "dbm_subset n D M"
    shows "\<exists> M'. A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>k',n\<^esub> \<langle>l', M'\<rangle> \<and> dbm_subset n D' M'"
  proof -
    from step_impl_mono_reachable'[OF assms] obtain M' where M':
      "A \<turnstile>\<^sub>I \<langle>l, M\<rangle> \<leadsto>\<^bsub>k',n\<^esub> \<langle>l', M'\<rangle>" "[curry D']\<^bsub>v,n\<^esub> \<subseteq> [curry M']\<^bsub>v,n\<^esub>"
    by auto
    with assms have "E\<^sup>*\<^sup>* a\<^sub>0 (l', M')" "E\<^sup>*\<^sup>* a\<^sub>0 (l', D')" by (auto simp: E_def intro: transitive_closurep_trans'(5))
    then have "dbm_subset n D' M'"
    unfolding dbm_subset_def
      apply -
      apply (subst subset_eq_pointwise_le[symmetric, where v = v])
      apply (rule canonical_reachable; assumption)
      apply (rule diag_reachable; assumption)
      apply (rule diag_reachable; assumption)
      using global_clock_numbering apply blast
    by (rule \<open>_ \<subseteq> _\<close>)
    with M'(1) show ?thesis by auto
  qed

  sublocale Search_Space E a\<^sub>0 F_rel subsumes
   apply standard
   using E_closure_finite unfolding Search_Space_Defs.reachable_def apply assumption
   using dbm_subset_refl apply (auto simp: subsumes_def; fail)
   using dbm_subset_trans apply (auto simp: subsumes_def; fail)
   apply (auto simp: subsumes_def step_impl_mono_reachable'' E_def; fail)
   apply (auto simp: F_rel_def subsumes_def; fail)
  done

  definition succs where
    "succs \<equiv> \<lambda> (l, D).
      (l, norm_upd (FW' (abstr_upd (inv_of A l) (up_canonical_upd (abstr_upd (inv_of A l) D) n)) n) k' n) #
      map (\<lambda> (g,a,r,l'). (l', norm_upd (FW' (abstr_upd (inv_of A l') (reset'_upd (abstr_upd g D) n r 0)) n) k' n)) (trans_fun l)"

  sepref_decl_op (no_mop, no_def) n :: "nat_rel" .

  lemma n_rel[sepref_param]:
    "(n, PR_CONST n) \<in> Id"
  by simp

  sepref_decl_impl (no_mop) n_rel .
  
  lemma [sepref_import_param]: "(A, A) \<in> Id" by simp
  lemma [sepref_import_param]: "(op =, op =) \<in> Id \<rightarrow> Id \<rightarrow> Id" by simp

  sepref_register n A

  (* XXX Remove other implemenations *)
  sepref_definition dbm_subset_impl'' is
    "uncurry (RETURN oo PR_CONST (dbm_subset n))" :: "(mtx_assn n)\<^sup>k *\<^sub>a (mtx_assn n)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding dbm_subset_alt_def[abs_def] list_all_foldli PR_CONST_def by sepref

  lemmas [sepref_fr_rules] = dbm_subset_impl''.refine

  sepref_register "PR_CONST (dbm_subset n)" :: "'e DBMEntry i_mtx \<Rightarrow> 'e DBMEntry i_mtx \<Rightarrow> bool"

  lemma [def_pat_rules]: "dbm_subset $ (Reachability_Problem.n $ A) \<equiv> PR_CONST (dbm_subset n)" by simp

  abbreviation "state_assn \<equiv> prod_assn id_assn (mtx_assn n)"

  sepref_definition subsumes_impl is
    "uncurry (RETURN oo subsumes)" :: "state_assn\<^sup>k *\<^sub>a state_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding subsumes_def by sepref

  (* XXX Somewhat peculiar use of the zero instance for DBM entries *)
  lemma init_dbm_alt_def:
    "init_dbm = op_asmtx_dfltNxN (Suc n) (Le 0)"
  unfolding init_dbm_def op_asmtx_dfltNxN_def zero_DBMEntry_def by auto

  lemma [sepref_import_param]: "(Le 0, PR_CONST (Le 0)) \<in> Id" by simp

  lemma [def_pat_rules]: "Le $ 0 \<equiv> PR_CONST (Le 0)" by simp

  sepref_register "PR_CONST (Le 0)"

  sepref_definition init_dbm_impl is
    "uncurry0 (RETURN (init_dbm :: nat \<times> nat \<Rightarrow> _))" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a (mtx_assn n)"
  unfolding init_dbm_alt_def by sepref
  
  lemmas [sepref_fr_rules] = init_dbm_impl.refine

  sepref_register l\<^sub>0 

  lemma [sepref_import_param]: "(l\<^sub>0, l\<^sub>0) \<in> Id" by simp

  sepref_definition a\<^sub>0_imp is
    "uncurry0 (RETURN a\<^sub>0)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a state_assn"
  unfolding a\<^sub>0_def by sepref

  term F term F_rel

  code_thms "op \<in>" term List.member

  (* XXX Better implementation? *)
  lemma F_rel_alt_def:
    "F_rel = (\<lambda> (l, _). List.member F l)"
  unfolding F_rel_def by (auto simp: List.member_def)

  sepref_register F

  lemma [sepref_import_param]: "(F, F) \<in> Id" by simp

  (* XXX Better implementation? *)
  lemma [sepref_import_param]: "(List.member, List.member) \<in> Id \<rightarrow> Id \<rightarrow> Id" by simp

  sepref_definition F_impl is
    "RETURN o F_rel" :: "state_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding F_rel_alt_def by sepref

  sepref_definition succs_impl is
    "RETURN o succs" :: "state_assn\<^sup>k \<rightarrow>\<^sub>a list_assn state_assn"



  definition dbm_subset' where
    "dbm_subset' = dbm_subset n"

  lemma subsumes_alt_def:
    "subsumes = (\<lambda> (l, M) (l', M'). l = l' \<and> dbm_subset' M M')"
  unfolding subsumes_def dbm_subset'_def by simp

  sepref_definition dbm_subset'_impl is
    "uncurry (RETURN oo PR_CONST dbm_subset')" :: "(mtx_assn n)\<^sup>k *\<^sub>a (mtx_assn n)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding dbm_subset'_def dbm_subset_alt_def[abs_def] list_all_foldli PR_CONST_def by sepref

  lemmas [sepref_fr_rules] = dbm_subset'_impl.refine

  sepref_register "PR_CONST dbm_subset'" :: "'e DBMEntry i_mtx \<Rightarrow> 'e DBMEntry i_mtx \<Rightarrow> bool"

  term n ML_val "@{term n}"

  lemma [def_pat_rules]: "Reachability_Problem.dbm_subset' $ A \<equiv> UNPROTECT dbm_subset'" by simp

  thm intf_of_assn

  sepref_definition subsumes_impl is
    "uncurry (RETURN oo subsumes)" :: "(prod_assn id_assn (mtx_assn n))\<^sup>k *\<^sub>a (prod_assn id_assn (mtx_assn n))\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding subsumes_alt_def by sepref
  apply sepref_keep
using [[goals_limit=1]]
  apply sepref_dbg_trans_keep
oops
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
oops
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply sepref_dbg_trans
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints

oops
  apply sepref_keep
using [[goals_limit=3]]
  apply sepref_dbg_trans_keep
  oops
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
using [[goals_limit=3]]
  apply sepref_dbg_trans_keep
  apply sepref_dbg_tran

  sublocale Worklist1 E a\<^sub>0 F_rel subsumes succs
  apply standard
  unfolding succs_def E_def
  apply auto
  using trans_fun unfolding transition_rel_def transition_\<alpha>_def[abs_def] apply auto[]
  sorry

  sepref_definition dbm_subset_impl is
  "uncurry (RETURN oo dbm_subset n)" ::
  "mtx_assn\<^sup>k *\<^sub>a mtx_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
unfolding dbm_subset_alt_def[abs_def] list_all_foldli by sepref












  

locale Reachability_Problem =
  fixes A :: "('a, nat, real, 's) ta" (* :: "('a, 'c, 't::time, 's) ta" *)
    and l :: 's
    and F :: "'s set"
  assumes "finite_ta A"

begin

  definition "S \<equiv> clk_set A"
  definition "v \<equiv> default_numbering S"
  definition "n \<equiv> card S"
  definition "x \<equiv> SOME x. x \<notin> S"
  definition "k \<equiv> default_ceiling_real A"

  definition "k' \<equiv> map (real o k) [1..<Suc n]"
    

  definition "F_rel \<equiv> \<lambda> (l, _). l \<in> F"
  
  definition "a\<^sub>0 = (l, init_dbm n)"

  definition "subsumes = (\<lambda> (l, M) (l', M'). dbm_subset n M M')"

  term step_impl

  definition "E = (\<lambda> (l, M) (l', M'). step_impl A l M k' n l' M')"

  lemma E_closure:
    "E\<^sup>*\<^sup>* a\<^sub>0 (l', M') \<longleftrightarrow> A \<turnstile>\<^sub>I \<langle>l, init_dbm n\<rangle> \<leadsto>\<^bsub>k',n\<^esub>* \<langle>l', M'\<rangle>"
  unfolding a\<^sub>0_def E_def
  apply safe
  apply (drule rtranclp_induct[where P = "\<lambda> (l', M'). A \<turnstile>\<^sub>I \<langle>l, init_dbm n\<rangle> \<leadsto>\<^bsub>k',n\<^esub>* \<langle>l', M'\<rangle>"];
         auto dest: step intro: refl; fail
        )
  by (induction rule: steps_impl.induct; simp add: rtranclp.intros(2))
  

sublocale bla: Search_Space E a\<^sub>0 F_rel subsumes
apply standard
subgoal
  unfolding Search_Space_Defs.reachable_def
  apply auto
  



end


end

lemma steps_z_norm_sound_spec:
  assumes "finite_ta A"
  obtains A' k n where
  "A' \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>k,id,n\<^esub>* \<langle>l',D'\<rangle> \<and> valid_dbm D n \<and> [D']\<^bsub>id,n\<^esub> \<noteq> {}"
  "(\<exists>Z. A \<turnstile> \<langle>l, [D]\<^bsub>id,n\<^esub>\<rangle> \<leadsto>* \<langle>l',Z\<rangle> \<and> Z \<noteq> {})"
sorry


end
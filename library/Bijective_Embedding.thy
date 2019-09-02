theory Bijective_Embedding
  imports "HOL-Library.Countable_Set"
begin

text \<open>Generalization of @{thm image_vimage_eq}\<close>
lemma inj_on_vimage_image_eq: "f -` (f ` A) \<inter> S = A" if "inj_on f S" "A \<subseteq> S"
  using that unfolding inj_on_def by blast

text \<open>Generalization of @{thm card_vimage_inj}\<close>
theorem card_vimage_inj_on:
  fixes f :: "'a \<Rightarrow> 'b"
    and A :: "'b set"
  assumes "inj_on f S"
    and "A \<subseteq> f ` S"
  shows "card (f -` A \<inter> S) = card A"
  using assms
  by (auto 4 3 simp: subset_image_iff inj_on_vimage_image_eq
      intro: card_image[symmetric, OF subset_inj_on])

context
begin

private lemma finiteI: "finite {x. x \<in> A \<and> ordX x \<le> ordX a \<and> Q x}" (is "finite ?S")
    if "inj_on ordX A" for A a Q and ordX :: "_ \<Rightarrow> nat"
proof -
  have "?S \<subseteq> {x. x \<in> A \<and> ordX x \<le> ordX a}"
    by blast
  moreover have "finite \<dots>"
  proof -
    have "\<dots> = ordX -` {n. n \<le> ordX a} \<inter> A"
      by auto
    moreover from \<open>inj_on ordX A\<close> have "finite \<dots>"
      by (intro finite_vimage_IntI) auto
    ultimately show ?thesis
      by simp
  qed
  ultimately show ?thesis
    by (rule finite_subset)
qed

qualified lemma enumeration_skip_finite_set_surj:
  "\<exists>a. a \<in> A \<and> a \<notin> S \<and> card {x \<in> A. ordX x \<le> ordX a \<and> x \<notin> S} = n"
  if "n > 0" "inj_on ordX A" "ordX ` A = \<nat>" "finite S" "S \<subseteq> A" for ordX :: "_ \<Rightarrow> nat"
  using \<open>finite S\<close> \<open>n > 0\<close> \<open>S \<subseteq> A\<close>
proof (induction arbitrary: n)
  case empty
  let ?a = "the_inv_into A ordX (n - 1)"
  have "card {x \<in> A. ordX x \<le> n - 1} = n"
  proof -
    have "{x \<in> A. ordX x \<le> n - 1} = ordX -` {x. x \<le> n - 1} \<inter> A"
      by auto
    moreover have "card \<dots> = card {x. x \<le> n - 1}"
      using \<open>inj_on ordX _\<close> \<open>ordX ` A = \<nat>\<close> by (intro card_vimage_inj_on) (auto simp: Nats_def)
    moreover have "\<dots> = n"
      using \<open>n > 0\<close> by auto
    ultimately show ?thesis
      by auto
  qed
  then have "\<exists> a \<in> A. card {x \<in> A. ordX x \<le> ordX a} = n"
    using \<open>inj_on ordX A\<close> \<open>ordX ` A = \<nat>\<close>
    unfolding Nats_def
    by (intro bexI[where x = "the_inv_into A ordX (n - 1)"])
       (auto intro: the_inv_into_into simp: f_the_inv_into_f[where f = ordX])
  then show ?case
    by auto
next
  case (insert x F)
  then obtain a where a: "a \<in> A" "a \<notin> F" "card {x \<in> A. ordX x \<le> ordX a \<and> x \<notin> F} = n"
    by blast
  show ?case
  proof (cases "ordX x \<le> ordX a")
    case True
    then have *:
      "{xa \<in> A. ordX xa \<le> ordX a \<and> xa \<notin> insert x F} = {x \<in> A. ordX x \<le> ordX a \<and> x \<notin> F} - {x}"
      by auto
    let ?m = "Max (ordX ` F)"
    show ?thesis
    proof (cases "\<exists>b \<in> A. b \<notin> F \<and> ordX a < ordX b \<and> ordX b \<le> ?m")
      case False
      let ?a = "the_inv_into A ordX (max ?m (ordX a) + 1)"
      let ?S = "{xa \<in> A. ordX xa \<le> ordX ?a \<and> xa \<notin> insert x F}"
      have "?a \<in> A"
        by (simp add: Nats_def \<open>inj_on ordX A\<close> \<open>ordX ` A = \<nat>\<close> the_inv_into_into)
      have "ordX ?a = max ?m (ordX a) + 1"
        using \<open>inj_on ordX A\<close> \<open>ordX ` A = \<nat>\<close> unfolding Nats_def
        by (subst f_the_inv_into_f[where f = ordX]) auto
      then have "?S = {xa \<in> A. ordX xa \<le> max ?m (ordX a) + 1 \<and> xa \<notin> insert x F}"
        by simp
      also have "\<dots> = {xa \<in> A. ordX xa \<le> ordX a \<and> xa \<notin> insert x F} \<union> {?a}"
      proof -
        have "{xa \<in> A. ordX xa = max ?m (ordX a) + 1 \<and> xa \<notin> insert x F} = {?a}"
          unfolding \<open>ordX ?a = _\<close>
          apply (auto simp: \<open>inj_on ordX A\<close> the_inv_into_f_eq)
          using True \<open>ordX ?a = _\<close> \<open>?a \<in> A\<close>
          apply -
          apply (auto; fail)+
          by (metis Max.in_idem Suc_eq_plus1 discrete finite_imageI imageI less_not_refl insert(1)
                    max.cobounded2 max.commute max.strict_coboundedI1)
        have *: "{xa \<in> A. ordX xa \<le> ordX a \<and> xa \<notin> insert x F}
              = {xa \<in> A. ordX xa \<le> max ?m (ordX a) \<and> xa \<notin> insert x F}"
          using False by auto
        show ?thesis
          unfolding \<open>_ = {?a}\<close>[symmetric] * by auto
      qed
      finally have "?S = ({x \<in> A. ordX x \<le> ordX a \<and> x \<notin> F} - {x}) \<union> {?a}"
        by auto
      moreover have "?a \<noteq> x"
        using True \<open>ordX ?a = max (MAX x \<in> F. ordX x) (ordX a) + 1\<close> by auto
      moreover have "?a \<notin> {x \<in> A. ordX x \<le> ordX a \<and> x \<notin> F}"
        using \<open>ordX ?a = max (MAX x \<in> F. ordX x) (ordX a) + 1\<close> by auto
      moreover have "x \<in> {x \<in> A. ordX x \<le> ordX a \<and> x \<notin> F}"
        using \<open>ordX x \<le> _\<close> \<open>insert x _ \<subseteq> A\<close> \<open>x \<notin> F\<close> by auto
      ultimately have "card ?S = card {x \<in> A. ordX x \<le> ordX a \<and> x \<notin> F}"
        apply simp
        apply (subst card_insert)
        subgoal
          by (force intro: finiteI[OF \<open>inj_on ordX A\<close>, of a])
        apply simp
        apply (subst card.remove[symmetric])
        subgoal
          by (force intro: finiteI[OF \<open>inj_on ordX A\<close>, of a])
        by auto
      also have "\<dots> = n"
        using \<open>_ = n\<close> by auto
      finally show ?thesis
        using \<open>inj_on ordX A\<close> \<open>ordX ` A = \<nat>\<close> unfolding Nats_def
        apply -
        apply (rule exI[where x = ?a], rule conjI)
         apply (auto intro: the_inv_into_into)
        using \<open>ordX x \<le> _\<close>
          apply (subgoal_tac "ordX x = Suc (ordX a)"; simp add: f_the_inv_into_f[where f = ordX])
         apply (subgoal_tac "ordX ?a \<le> ?m")
        subgoal
          using False
          apply (simp add: f_the_inv_into_f[where f = ordX])
          done
         apply (rule Max_ge)
        using \<open>finite F\<close> apply (rule finite_imageI)
         apply (rule imageI)
         apply (simp add: f_the_inv_into_f[where f = ordX])
        done
    next
      case True
      let ?M = "{b \<in> A. ordX a < ordX b \<and> ordX b \<le> ?m \<and> b \<notin> F}"
      from True have "?M \<noteq> {}"
        by auto
      have "finite ?M"
      proof -
        have "?M \<subseteq> {b \<in> A. ordX b \<le> ?m}"
          by auto
        moreover have "finite \<dots>"
        proof -
          have *: "\<dots> = ordX -` {x. x \<le> ?m} \<inter> A"
            by auto
          from \<open>inj_on ordX A\<close> show ?thesis
            unfolding * by (intro finite_vimage_IntI) auto
        qed
        ultimately show ?thesis
          by (rule finite_subset)
      qed
      let ?a = "arg_min_on ordX ?M"
      from arg_min_if_finite[OF \<open>finite ?M\<close> \<open>?M \<noteq> {}\<close>, of ordX] have a:
        "?a \<in> ?M" "\<not> (\<exists> x \<in> ?M. ordX x < ordX ?a)"
        by fast+
      with \<open>ordX x \<le> ordX a\<close> have "?a \<noteq> x"
        by auto
      then have **: "{xa \<in> A. ordX xa \<le> ordX ?a \<and> xa \<noteq> x \<and> xa \<notin> F} =
            {xa \<in> A. ordX xa \<le> ordX a \<and> xa \<noteq> x \<and> xa \<notin> F} \<union> {?a}"
        using a
        by auto
           (smt \<open>inj_on ordX A\<close> inj_on_eq_iff le_eq_less_or_eq le_trans mem_Collect_eq not_le)
      have "?a \<notin> {xa \<in> A. ordX xa \<le> ordX a \<and> xa \<noteq> x \<and> xa \<notin> F}"
        using a(1) by auto
      then have "card {xa \<in> A. ordX xa \<le> ordX ?a \<and> xa \<noteq> x \<and> xa \<notin> F} = n"
        unfolding *[simplified] **
        using \<open>card _ = n\<close>
        apply simp
        apply (subst card_insert)
        subgoal
          by (auto intro: finiteI[OF \<open>inj_on ordX A\<close>])
        apply simp
        apply (subst card.remove[symmetric])
        subgoal
          by (auto intro: finiteI[OF \<open>inj_on ordX A\<close>])
        subgoal
          using \<open>insert x F \<subseteq> A\<close> \<open>ordX x \<le> _\<close> \<open>x \<notin> F\<close> by simp
        apply assumption
        done
      then show ?thesis
        using a(1) \<open>ordX x \<le> _\<close> by (intro exI[where x = ?a]) auto
    qed
  next
    case False
    then have
      "{xa \<in> A. ordX xa \<le> ordX a \<and> xa \<notin> insert x F} = {x \<in> A. ordX x \<le> ordX a \<and> x \<notin> F}"
      by auto
    with a False show ?thesis
      by (intro exI[where x = a]) auto
  qed
qed

lemma bij_betw_relI:
  assumes "\<And>x y z. x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> z \<in> B \<Longrightarrow> R x y \<Longrightarrow> R x z \<Longrightarrow> y = z"
      and "\<And>x y z. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> B \<Longrightarrow> R x z \<Longrightarrow> R y z \<Longrightarrow> x = y"
      and "\<And>x. x \<in> A \<Longrightarrow> \<exists>y \<in> B. R x y" "\<And>y. y \<in> B \<Longrightarrow> \<exists>x \<in> A. R x y"
  shows "bij_betw (\<lambda>a. SOME b. R a b \<and> b \<in> B) A B"
  by (rule bij_betwI'; smt assms someI)

lemma bijective_embedding:
  fixes f :: "'a \<Rightarrow> 'b"
    and A :: "'a set" and B :: "'b set"
    and S :: "'a set"
  assumes "inj_on f S" and "S \<subseteq> A" and "f ` S \<subseteq> B"
    and "finite S"
    and "countable A" and "countable B"
    and "infinite A" and "infinite B"
  shows "\<exists>h. bij_betw h A B \<and> (\<forall>x \<in> S. h x = f x)"
proof -
  obtain ordX :: "_ \<Rightarrow> nat" and ordY :: "_ \<Rightarrow> nat" where
    "inj_on ordX A" "ordX ` A = \<nat>" and "inj_on ordY B" "ordY ` B = \<nat>"
    using assms(5-) unfolding Nats_def
    by (metis bij_betw_def bij_betw_from_nat_into bij_betw_imp_inj_on bij_betw_the_inv_into
        of_nat_id surj_def)
  define P where "P a b \<equiv> a \<in> A \<and> b \<in> B \<and> a \<notin> S \<and> b \<notin> f ` S \<and>
    card {x. x \<in> A \<and> ordX x \<le> ordX a \<and> x \<notin> S} = card {x. x \<in> B \<and> ordY x \<le> ordY b \<and> x \<notin> f ` S}"
    for a b
  let ?f = "\<lambda>a. card {x. x \<in> A \<and> ordX x \<le> ordX a \<and> x \<notin> S}"
  let ?g = "\<lambda>a. card {x. x \<in> B \<and> ordY x \<le> ordY a \<and> x \<notin> f ` S}"
  have P_right: "\<exists> b. P a b" if "a \<in> A" "a \<notin> S" for a
  proof -
    have *: "\<exists>b. b \<in> B \<and> b \<notin> f ` S \<and> ?g b = n" if "n > 0" for n
      using \<open>n > 0\<close> \<open>finite S\<close> \<open>f ` S \<subseteq> B\<close> \<open>inj_on ordY B\<close> \<open>ordY ` B = \<nat>\<close>
      by (intro enumeration_skip_finite_set_surj) auto
    from that have "?f a > 0"
      unfolding card_gt_0_iff by (auto intro: finiteI[OF \<open>inj_on ordX A\<close>])
    from *[OF this] show ?thesis
      unfolding P_def using that by auto
  qed
  have P_left: "\<exists>a. P a b" if "b \<in> B" "b \<notin> f ` S" for b
    using that \<open>finite S\<close> \<open>S \<subseteq> A\<close> \<open>inj_on ordX A\<close> \<open>inj_on ordY B\<close> \<open>ordX ` A = \<nat>\<close> unfolding P_def
    by (auto 4 3 intro: enumeration_skip_finite_set_surj finiteI simp: card_gt_0_iff)
  have P_surj: "a = b" if "P a c" "P b c" for a b c
  proof -
    from that have "?f a = ?f b" (is "card ?A = card ?B")
      unfolding P_def by auto
    have fin: "finite ?A" "finite ?B"
      by (intro finiteI \<open>inj_on ordX A\<close>)+
    have *: "a \<in> A" "b \<in> A" "a \<notin> S" "b \<notin> S"
      using that unfolding P_def by auto
    consider (lt) "ordX a < ordX b" | (eq) "ordX a = ordX b" | (gt) "ordX a > ordX b"
      by force
    then show ?thesis
    proof cases
      case lt
      with * have "?f a < ?f b"
        using leD by (intro psubset_card_mono fin) auto
      with \<open>?f a = ?f b\<close> show ?thesis
        by auto
    next
      case eq
      then show ?thesis
        using \<open>inj_on ordX A\<close> \<open>a \<in> A\<close> \<open>b \<in> A\<close> by (auto dest: inj_onD)
    next
      case gt
      with * have "?f a > ?f b"
        using leD by (intro psubset_card_mono fin) auto
      with \<open>?f a = ?f b\<close> show ?thesis
        by auto
    qed
  qed
  have P_inj: "b = c" if "P a b" "P a c" for a b c
  proof -
    from that have "?g b = ?g c" (is "card ?A = card ?B")
      unfolding P_def by auto
    have fin: "finite ?A" "finite ?B"
      by (intro finiteI \<open>inj_on ordY B\<close>)+
    have *: "b \<in> B" "c \<in> B" "b \<notin> f ` S" "c \<notin> f ` S"
      using that unfolding P_def by auto
    consider (lt) "ordY b < ordY c" | (eq) "ordY b = ordY c" | (gt) "ordY b > ordY c"
      by force
    then show ?thesis
    proof cases
      case lt
      with * have "?g b < ?g c"
        using leD by (intro psubset_card_mono fin) (auto, blast)
      with \<open>?g b = ?g c\<close> show ?thesis
        by auto
    next
      case eq
      then show ?thesis
        using \<open>inj_on ordY B\<close> \<open>b \<in> B\<close> \<open>c \<in> B\<close> by (auto dest: inj_onD)
    next
      case gt
      with * have "?g b > ?g c"
        using leD by (intro psubset_card_mono fin) (auto, blast)
      with \<open>?g b = ?g c\<close> show ?thesis
        by auto
    qed
  qed

  define R where "R a b \<equiv> if a \<in> S then b = f a else P a b" for a b
  have R_A: "a \<in> A" and R_B: "b \<in> B" if "R a b" for a b
    using that \<open>f ` S \<subseteq> B\<close> \<open>S \<subseteq> A\<close> unfolding R_def by (auto split: if_split_asm simp: P_def)
  have R_inj: "b = c" if "R a b" "R a c" for a b c
    using that unfolding R_def by (auto split: if_split_asm dest: P_inj)
  moreover have R_surj: "a = b" if "R a c" "R b c" for a b c
    using that unfolding R_def
    by (auto split: if_split_asm dest: P_surj inj_onD[OF \<open>inj_on f S\<close>]) (auto simp: P_def)
  moreover have R_right: "\<exists>b. R a b" if "a \<in> A" for a
    unfolding R_def by (auto dest: P_right[OF \<open>a \<in> A\<close>])
  moreover have R_left: "\<exists>a. R a b" if "b \<in> B" for b
    unfolding R_def
    by (cases "b \<in> f ` S", (auto; fail), (frule P_left[OF \<open>b \<in> B\<close>], auto simp: P_def))
  ultimately show ?thesis
    apply (intro exI[of _ "\<lambda>a. SOME b. R a b \<and> b \<in> B"] conjI)
     apply (rule bij_betw_relI)
        apply assumption+
      apply (smt R_A R_B)+
    using assms(3) by (subst R_def) (simp, blast)
qed

end

definition extend_bij :: "('a :: countable \<Rightarrow> 'b :: countable) \<Rightarrow> 'a set \<Rightarrow> _" where
  "extend_bij f S \<equiv> SOME h. bij h \<and> (\<forall>x \<in> S. h x = f x)"

lemma
  fixes f :: "'a  :: countable \<Rightarrow> 'b :: countable" and S :: "'a set"
  assumes "infinite (UNIV :: 'a set)" and "infinite (UNIV :: 'b set)"
      and "inj_on f S" and "finite S"
    shows extend_bij_bij: "bij (extend_bij f S)"
      and extend_bij_extends: "\<forall>x \<in> S. extend_bij f S x = f x"
proof -
  from bijective_embedding[OF assms(3) _ _ assms(4) _ _ assms(1,2)] obtain h where
    "bij h \<and> (\<forall>x\<in>S. h x = f x)"
    by auto
  then show "bij (extend_bij f S)" "\<forall>x \<in> S. extend_bij f S x = f x"
    unfolding atomize_conj extend_bij_def by (rule someI[where x = h])
qed

end
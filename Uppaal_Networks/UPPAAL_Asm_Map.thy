theory UPPAAL_Asm_Map
  imports UPPAAL_Asm "HOL-Library.Lattice_Syntax"
begin

subsection "State Map"

text\<open>
Central data structure of the abstract interpreter, mapping addresses to some value.
The common meaning is: "state before executing the instruction at the address".
\<close>
datatype 'a state_map = SM "addr \<Rightarrow> 'a"

lemma state_map_single_constructor: "\<exists>m. a = SM m"
  using state_map.exhaust by auto

fun lookup :: "'a state_map \<Rightarrow> addr \<Rightarrow> 'a" where
  "lookup (SM m) = m"

fun unwrap :: "'a state_map \<Rightarrow> addr \<Rightarrow> 'a" where
  "unwrap (SM m) = m"

fun single :: "addr \<Rightarrow> 'a::bot \<Rightarrow> 'a state_map" where
  "single k v = SM (\<lambda>pc. if pc = k then v else \<bottom>)"

lemma single_lookup: "lookup (single k v) k = v" by simp

fun domain :: "('b::bot) state_map \<Rightarrow> addr set" where
  "domain (SM m) = {a. m a \<noteq> \<bottom>}"

lemma single_domain: "domain (single k v) \<subseteq> {k}"
proof (standard, goal_cases)
  case (1 x)
  hence "(\<lambda>pc. if pc = k then v else \<bottom>) \<noteq> \<bottom>" by force
  then show ?case using 1 by fastforce
qed

lemma state_map_eq_fwd: "(\<And>p. lookup m p = lookup n p) \<Longrightarrow> m = n"
proof -
  assume lookeq: "lookup m p = lookup n p" for p
  obtain mm where mm: "m = SM mm" using lookup.cases by blast
  obtain nm where nm: "n = SM nm" using lookup.cases by blast
  have "mm = nm" using lookeq nm mm by auto
  thus "m = n" using mm nm by blast
qed

lemma state_map_eq: "(\<forall>p. lookup m p = lookup n p) \<longleftrightarrow> m = n" using state_map_eq_fwd by auto

instantiation state_map :: (order) order
begin
  definition less_eq_state_map :: "('a::order)state_map \<Rightarrow> 'a state_map \<Rightarrow> bool" where
  "C1 \<le> C2 \<longleftrightarrow> (\<forall>p. lookup C1 p \<le> lookup C2 p)"

  definition less_state_map :: "'a state_map \<Rightarrow> 'a state_map \<Rightarrow> bool" where
  "less_state_map x y = (x \<le> y \<and> \<not> y \<le> x)"

  instance proof (standard, goal_cases)
    case 1 show ?case by(simp add: less_state_map_def)
  next
    case 2 thus ?case by(auto simp: less_eq_state_map_def)
  next
    case 3 thus ?case using less_eq_state_map_def order_trans by fastforce
  next
    case 4 thus ?case by (simp add: less_eq_state_map_def dual_order.antisym state_map_eq_fwd)
  qed
end

lemma state_map_leI: "(\<And>p. lookup C1 p \<le> lookup C2 p) \<Longrightarrow> C1 \<le> C2"
  using less_eq_state_map_def by blast

instantiation state_map :: (bot) bot
begin
definition bot_state_map: "\<bottom> = SM (\<lambda>x. \<bottom>)"
instance ..
end

instantiation state_map :: (order_bot) order_bot
begin
lemma bot_lookup [simp]:
  "lookup \<bottom> x = \<bottom>"
  by (simp add: bot_state_map)
instance proof standard qed (simp add: less_eq_state_map_def)
end

instantiation state_map :: (top) top
begin
definition top_state_map[no_atp]: "\<top> = SM (\<lambda>x. \<top>)"
instance ..
end

instantiation state_map :: (order_top) order_top
begin
lemma top_lookup [simp]:
  "lookup \<top> x = \<top>"
  by (simp add: top_state_map)
instance proof standard qed (simp add: less_eq_state_map_def)
end

instantiation state_map :: (semilattice_sup) semilattice_sup
begin
definition "a \<squnion> b = SM (\<lambda>k. lookup a k \<squnion> lookup b k)"
lemma sup_lookup [simp]: "lookup (a \<squnion> b) x = lookup a x \<squnion> lookup b x"
  by (simp add: sup_state_map_def)
instance by standard (simp_all add: less_eq_state_map_def)
end

instantiation state_map :: (semilattice_inf) semilattice_inf
begin
definition "a \<sqinter> b = SM (\<lambda>x. lookup a x \<sqinter> lookup b x)"
lemma inf_apply [simp]: "lookup (a \<sqinter> b) x = lookup a x \<sqinter> lookup b x"
  by (simp add: inf_state_map_def)
instance by standard (simp_all add: less_eq_state_map_def)
end

instance state_map :: (lattice) lattice ..

instantiation state_map :: (Sup) Sup
begin
definition "\<Squnion>A = SM (\<lambda>x. \<Squnion>a\<in>A. lookup a x)"
lemma Sup_lookup [simp]: "lookup (\<Squnion>A) x = (\<Squnion>m\<in>A. lookup m x)"
  by (simp add: Sup_state_map_def)
instance ..
end

instantiation state_map :: (Inf) Inf
begin
definition "\<Sqinter>A = SM (\<lambda>x. \<Sqinter>a\<in>A. lookup a x)"
lemma Inf_lookup [simp]: "lookup (\<Sqinter>A) x = (\<Sqinter>m\<in>A. lookup m x)"
  by (simp add: Inf_state_map_def)
instance ..
end

instantiation state_map :: (bounded_semilattice_sup_bot) bounded_semilattice_sup_bot begin instance .. end

instantiation state_map :: (complete_lattice) complete_lattice
begin
instance proof
  show "(x::'a state_map) \<in> A \<Longrightarrow> \<Sqinter>A \<le> x" for A x
  proof -
    fix x A assume ass: "(x::'a state_map) \<in> A"
    have "lookup (SM (\<lambda>x. \<Sqinter>a\<in>A. lookup a x)) p \<le> lookup x p" for p using ass le_INF_iff by fastforce
    thus "\<Sqinter>A \<le> x" by (simp add: less_eq_state_map_def)
  qed
  show "(\<And>x. x \<in> A \<Longrightarrow> (z::'a state_map) \<le> x) \<Longrightarrow> z \<le> \<Sqinter> A" for A z by (simp add: INF_greatest less_eq_state_map_def)
  show "(x::'a state_map) \<in> A \<Longrightarrow> x \<le> \<Squnion> A" for A x
  proof -
    fix x A assume ass: "(x::'a state_map) \<in> A"
    have "lookup x p \<le> lookup (SM (\<lambda>x. \<Squnion>a\<in>A. lookup a x)) p" for p using ass SUP_le_iff by fastforce
    thus "x \<le> \<Squnion>A" by (simp add: less_eq_state_map_def)
  qed
  show "(\<And>x. x \<in> A \<Longrightarrow> x \<le> (z::'a state_map)) \<Longrightarrow> \<Squnion> A \<le> z" for A z by (simp add: SUP_le_iff less_eq_state_map_def)
  show "\<Sqinter> ({}::'a state_map set) = \<top>" by (simp add: state_map_eq_fwd Inf_state_map_def)
  show "\<Squnion> ({}::'a state_map set) = \<bottom>" by (simp add: state_map_eq_fwd Sup_state_map_def)
qed
end

lemma sup_top: "(\<top>::'a::{semilattice_sup, order_top}) \<squnion> a = \<top>"
  by (simp add: sup.absorb1)

lemma sup_top2: "a \<squnion> (\<top>::'a::{semilattice_sup, order_top}) = \<top>"
  by (simp add: sup.absorb2)

lemma sup_bot: "lookup (a::'a::{semilattice_sup, order_bot} state_map) pc \<squnion> lookup b pc \<noteq> \<bottom>
  \<longleftrightarrow> lookup a pc \<noteq> \<bottom> \<or> lookup b pc \<noteq> \<bottom>"
  by (standard; auto simp: eq_iff)

lemma sup_domain: "domain ((a::'a::{semilattice_sup, order_bot} state_map) \<squnion> b) = domain a \<union> domain b"
proof -
  have "domain (a \<squnion> b) = {pc. lookup a pc \<squnion> lookup b pc \<noteq> \<bottom>}" by (simp add: sup_state_map_def)
  also have "\<dots> = {pc. lookup a pc \<noteq> \<bottom> \<or> lookup b pc \<noteq> \<bottom>}" using sup_bot by blast
  also have "\<dots> = {pc. lookup a pc \<noteq> \<bottom>} \<union> {pc. lookup b pc \<noteq> \<bottom>}" by blast
  also have "\<dots> = domain a \<union> domain b" by (metis domain.simps lookup.elims)
  finally show ?thesis .
qed

lemma sup_domain_finite:
  assumes
    "finite (domain (a::'a::{semilattice_sup, order_bot} state_map))"
    "finite (domain b)"
  shows "finite (domain (a \<squnion> b))"
  using assms by (simp add: sup_domain)

lemma domain_top:
  assumes "(\<top>::'a::{order_top, order_bot}) \<noteq> \<bottom>"
  shows "domain (\<top>::'a state_map) = \<top>"
  by (metis (mono_tags) UNIV_eq_I assms domain.simps lookup.elims mem_Collect_eq top_lookup)

end
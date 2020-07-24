theory AbsInt_Refine
imports                   
  "HOL-Library.RBT_Mapping"
  State_Dumb
begin

instantiation mapping :: (type,bot) bot
begin
definition "bot_mapping \<equiv> Mapping.empty"
instance ..
end

type_synonym 'a r_state_map = "(addr, 'a) mapping"

fun r_lookup :: "('a, 'b::bot) mapping \<Rightarrow> 'a \<Rightarrow> 'b" where
  "r_lookup m = Mapping.lookup_default \<bottom> m"

instantiation mapping :: (type, "{preorder, bot}") preorder
begin
  definition less_eq_mapping :: "('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping \<Rightarrow> bool" where
  "C1 \<le> C2 \<longleftrightarrow> (\<forall>p. r_lookup C1 p \<le> r_lookup C2 p)"
  
  definition less_mapping :: "('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping \<Rightarrow> bool" where
  "less_mapping x y = (x \<le> y \<and> \<not> y \<le> x)"
  
  instance proof (standard, goal_cases)
    case 1 show ?case by(simp add: less_mapping_def)
  next
    case 2 thus ?case by(auto simp: less_eq_mapping_def)
  next
    case 3 thus ?case using less_eq_mapping_def order_trans by fastforce
  qed
end

lemma mapping_leI: "(\<And>p. r_lookup C1 p \<le> r_lookup C2 p) \<Longrightarrow> C1 \<le> C2"
  using less_eq_mapping_def by blast

definition RSM :: "('a::bot) r_state_map \<Rightarrow> 'a state_map" where
  "RSM m = SM (r_lookup m)"

declare RSM_def[simp]

lemma RSM_mono: "a \<le> b \<Longrightarrow> RSM a \<le> RSM b"
proof -
  assume "a \<le> b"
  hence "lookup (RSM a) pc \<le> lookup (RSM b) pc" for pc by (simp add: less_eq_mapping_def)
  thus ?thesis using less_eq_state_map_def by blast
qed

code_datatype RSM

definition "r_empty_map \<equiv> Mapping.empty::('a::bot) r_state_map"

lemma[code]: "\<bottom> = RSM r_empty_map"
  by (rule lookup_eq; simp add: lookup_default_empty r_empty_map_def)

lemma[code]: "lookup (RSM m) = r_lookup m" by simp

lemma[code]: "single k v = RSM (Mapping.update k v \<bottom>)"
  by (rule lookup_eq; simp add: bot_mapping_def lookup_default_empty lookup_default_update')

lemma single_lookup: "lookup (single k v) k = v" by simp

lemma single_lookup_le: "x \<le> single k v \<Longrightarrow> lookup x k \<le> v"
  by (metis less_eq_state_map_def single_lookup)

fun merge_single :: "('a::semilattice_sup) state_map \<Rightarrow> addr \<Rightarrow> 'a \<Rightarrow> 'a state_map" where
  "merge_single (SM m) pc x = SM (\<lambda>npc. if npc = pc then x \<squnion> m npc else m npc)"

lemma merge_single_grows: "m \<le> merge_single m pc x"
proof -
  obtain mm where sm: "m = SM mm" using state_map_single_constructor by blast
  have "lookup (SM mm) p \<le> lookup (merge_single (SM mm) pc x) p" for p by simp
  from this sm show ?thesis using less_eq_state_map_def by blast
qed

fun r_merge_single :: "('a::{semilattice_sup, bot}) r_state_map \<Rightarrow> addr \<Rightarrow> 'a \<Rightarrow> 'a r_state_map" where
  "r_merge_single tree pc x = Mapping.update pc (x \<squnion> (r_lookup tree pc)) tree"

lemma merge_single_neq:
  assumes "pc \<noteq> k"
  shows "lookup (RSM (r_merge_single m pc x)) k = lookup (RSM m) k"
proof -
  have r: "lookup (RSM m) k = Mapping.lookup_default \<bottom> m k" by simp
  from assms have l:"lookup (RSM (r_merge_single m pc x)) k = Mapping.lookup_default \<bottom> m k" by (simp add: lookup_default_update_neq) 
  from r l show ?thesis by simp
qed

lemma merge_single_eq:
  assumes "pc = k"
  shows "lookup (RSM (r_merge_single m pc x)) k = x \<squnion> lookup (RSM m) k"
proof -
  have r: "x \<squnion> lookup (RSM m) k = x \<squnion> Mapping.lookup_default \<bottom> m k" by simp
  from assms have l:"lookup (RSM (r_merge_single m pc x)) k = x \<squnion> Mapping.lookup_default \<bottom> m k" by (simp add: lookup_default_update) 
  from r l show ?thesis by simp
qed

lemma r_merge_single[code]: "merge_single (RSM m) pc x = RSM (r_merge_single m pc x)"
proof(rule lookup_eq)
  obtain mm where func: "RSM m = SM mm" using state_map_single_constructor by blast
  have "(if k = pc then x \<squnion> mm k else mm k) = lookup (RSM (r_merge_single m pc x)) k" for k
  proof(cases "k = pc")
    case True from this func show ?thesis using merge_single_eq by (metis lookup.simps) next
    case False from this func show ?thesis using merge_single_neq by (metis lookup.simps)
  qed
  thus "lookup (merge_single (RSM m) pc x) k = lookup (RSM (r_merge_single m pc x)) k" for k using func by auto
qed

lemma r_merge_single_grows: "m \<le> r_merge_single m pc x"
  by (simp add: less_eq_mapping_def lookup_default_update')

fun r_domain :: "('a, 'b::bot) mapping \<Rightarrow> 'a set" where
  "r_domain tree = Set.filter (\<lambda>pc. r_lookup tree pc \<noteq> \<bottom>) (Mapping.keys tree)"

lemma r_domain[code]: "domain (RSM m) = r_domain m"
proof (intro Set.equalityI Set.subsetI)
  fix x assume "x \<in> domain (RSM m)"
  hence lookup: "lookup (RSM m) x \<noteq> \<bottom>" by simp
  from lookup have r_lookup: "r_lookup m x \<noteq> \<bottom>" by simp
  from r_lookup have keys: "x \<in> Mapping.keys m"
    by (metis Option.is_none_def empty_iff keys_empty keys_is_none_rep lookup_default_def lookup_default_empty r_lookup.simps)
  from keys r_lookup show "x \<in> r_domain m" by auto
qed auto

lemma r_domain_finite: "finite (r_domain (Mapping m))" by (simp add: keys_Mapping)
lemma domain_finite: "finite (domain (RSM (Mapping m)))" using r_domain r_domain_finite by metis

fun sup_mapping_aux :: "('a, 'b::{semilattice_sup, bot}) mapping \<Rightarrow> 'a \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping" where
  "sup_mapping_aux b pc acc = Mapping.update pc (r_lookup acc pc \<squnion> r_lookup b pc) acc"

lemma sup_mapping_aux_pc: "r_lookup (sup_mapping_aux b pc acc) pc = r_lookup acc pc \<squnion> r_lookup b pc"
  by (simp add: lookup_default_update)

lemma sup_mapping_aux_grows: "acc \<le> sup_mapping_aux b pc acc"
proof(rule mapping_leI)
  show "r_lookup acc p \<le> r_lookup (sup_mapping_aux b pc acc) p" for p
  proof(cases "p = pc")
    case True
    have "r_lookup acc pc \<squnion> r_lookup b pc = r_lookup (sup_mapping_aux b pc acc) pc" using sup_mapping_aux_pc by metis
    then show ?thesis by (simp add: True)
  next
    case False
    have "r_lookup acc p = r_lookup (sup_mapping_aux b pc acc) p"
      by (metis False lookup_default_update_neq r_lookup.simps sup_mapping_aux.simps)
    then show ?thesis by simp
  qed
qed

instantiation mapping :: (linorder, "{semilattice_sup, bot}") sup
begin
fun sup_mapping :: "('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping" where
  "sup_mapping a b = fold
    (sup_mapping_aux b)
    (sorted_list_of_set (r_domain b)) a"
instance ..
end

lemma fold_grow:
  assumes "\<And>e acc. (acc::'a::preorder) \<le> f e acc"
  shows "a \<le> fold f l a"
proof(induction l arbitrary: a)
  case (Cons x xs)
  then show ?case using Cons.IH assms order_trans by fastforce
qed simp


text \<open>
It's not possible to instantiate mapping :: order
but we can still have some lemmas from semilattice_sup outside instantiations:
\<close>
lemma mapping_sup_ge1 [simp]: "(x::('a::linorder, 'b::{semilattice_sup, bot}) mapping) \<le> x \<squnion> y"
proof -
  have "acc \<le> (sup_mapping_aux y) a acc" for a acc using sup_mapping_aux_grows by simp
  thus ?thesis by (simp add: fold_grow)
qed

lemma mapping_sup_lookup: "r_lookup (a \<squnion> b) pc = r_lookup a pc \<squnion> r_lookup b pc"
proof(cases "pc \<in> r_domain b")
  case True
  then show ?thesis sorry
next
  case False
  then show ?thesis
  proof(induction "sorted_list_of_set (r_domain b)")
    case Nil
    from Nil have bot: "r_lookup b pc = \<bottom>" sorry (* this should be easy *)
    hence botsup: "r_lookup a pc \<squnion> \<bottom> = r_lookup a pc" sorry (* not sure why this fails *)
    from Nil have left: "r_lookup (a \<squnion> b) pc = r_lookup a pc" by simp
    from bot left botsup show ?case by simp
  next
    case (Cons a x)
    then show ?case sorry
  qed
qed

(*lemma mapping_sup_ge2 [simp]: "(y::('a::linorder, 'b::{semilattice_sup, bot}) mapping) \<le> x \<squnion> y" sorry
lemma mapping_sup_least: "(y::('a::linorder, 'b::{semilattice_sup, bot}) mapping) \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x" sorry*)

lemma[code]: "((RSM a)::'a::{semilattice_sup, bot} state_map) \<squnion> RSM b = RSM (a \<squnion> b)"
  by (rule state_map_eq_fwd, metis mapping_sup_lookup RSM_def lookup.simps sup_lookup)

(*subsection \<open>astep with r_step_map\<close>

type_synonym 'a r_astep = "instr \<Rightarrow> addr \<Rightarrow> 'a \<Rightarrow> 'a r_state_map"

definition RSTEP :: "'a::bot r_astep \<Rightarrow> 'a astep" where
  "RSTEP f = (\<lambda>op pc ist. RSM (f op pc ist))"

code_datatype RSTEP*)

subsection \<open>Stepping\<close>

lemma sorted_list_of_set_split:
  assumes "a \<in> s" "finite s"
  shows "\<exists>pre post. pre @ a # post = sorted_list_of_set s"
  using assms set_sorted_list_of_set split_list_first by fastforce

fun r_step_map_from :: "('a::absstate) astep \<Rightarrow> program \<Rightarrow> 'a state_map \<Rightarrow> addr \<Rightarrow> 'a state_map \<Rightarrow> 'a state_map" where
  "r_step_map_from f prog ctx ipc acc =
    (case prog ipc of
      Some op \<Rightarrow> acc \<squnion> f op ipc (lookup ctx ipc) |
      None \<Rightarrow> acc)"

lemma r_step_map_from_grows: "acc \<le> r_step_map_from f prog ctx ipc acc"
  using mapping_sup_ge1 by (cases "prog ipc"; auto)

fun r_step_map :: "('a::absstate) astep \<Rightarrow> program \<Rightarrow> 'a state_map \<Rightarrow> 'a state_map" where
  "r_step_map f prog ctx = fold (r_step_map_from f prog ctx) (sorted_list_of_set (domain ctx)) \<bottom>"

lemma fold_split:
  "fold f (pre @ x # post) = fold f post \<circ> f x \<circ> fold f pre"
  by simp

lemma fold_overgrowth:
  assumes
    "init \<le> y"
    "\<And>x acc. acc \<le> f x acc"
    "\<not> fold f l init \<le> y"
  shows
    "\<exists>pre x post. l = pre @ x # post \<and> fold f pre init \<le> y \<and> \<not> f x (fold f pre init) \<le> y"
using assms proof(induction l arbitrary: init)
  case (Cons a as)
  hence ih: "\<not> fold f as init \<le> y \<Longrightarrow> \<exists>pre x post. as = pre @ x # post \<and> fold f pre init \<le> y \<and> \<not> f x (fold f pre init) \<le> y" by blast
  then show ?case proof (cases "f a init \<le> y")
    case True then show ?thesis by (metis (full_types) Cons.IH Cons.prems(3) List.fold_simps(2) append_Cons assms(2))
  next
    case False then show ?thesis using Cons.prems(1) by fastforce
  qed
qed simp

lemma fold_overgrowth_lookup:
  assumes
    "lookup init k \<le> y"
    "\<And>x acc. acc \<le> f x acc" (* could be theoretically weaker (only growing on k) but not needed for our case *)
    "\<not> lookup (fold f l init) k \<le> y"
  shows
    "\<exists>pre x post. l = pre @ x # post \<and> lookup (fold f pre init) k \<le> y \<and> \<not> lookup (f x (fold f pre init)) k \<le> y"
using assms proof(induction l arbitrary: init)
  case (Cons a as)
  hence ih: "\<not> lookup (fold f as init) k \<le> y \<Longrightarrow> \<exists>pre x post. as = pre @ x # post \<and> lookup (fold f pre init) k \<le> y \<and> \<not> lookup (f x (fold f pre init)) k \<le> y" by blast
  then show ?case proof (cases "lookup (f a init) k \<le> y")
    case True then show ?thesis by (metis (full_types) Cons.IH Cons.prems(3) List.fold_simps(2) append_Cons assms(2))
  next
    case False then show ?thesis using Cons.prems(1) by fastforce
  qed
qed simp

lemma sorted_list_of_set_in: "\<exists>pre post. pre @ x # post = sorted_list_of_set s \<Longrightarrow> x \<in> s"
  by (metis Un_iff append_is_Nil_conv list.set_intros(1) list.simps(3) set_append set_sorted_list_of_set sorted_list_of_set.infinite)

lemma[code]: "step_map (f::('a::absstate) astep) prog (RSM (Mapping tree)) = r_step_map f prog (RSM (Mapping tree))"
proof(rule lookup_eq)     
  let ?ctx = "RSM (Mapping tree)"
  let ?smf = "r_step_map_from f prog ?ctx"
  have "\<Squnion>{ost. \<exists>ipc op. prog ipc = Some op \<and> lookup ?ctx ipc \<noteq> \<bottom> \<and> lookup (f op ipc (lookup ?ctx ipc)) pc = ost} = lookup (r_step_map f prog ?ctx) pc" for pc
  proof(rule Sup_eqI, goal_cases)
    case (1 ost)
    then obtain ipc op where step: "prog ipc = Some op" "lookup ?ctx ipc \<noteq> \<bottom>" "lookup (f op ipc (lookup ?ctx ipc)) pc = ost" by blast
    obtain m where "SM m = ?ctx" using state_map_single_constructor by metis
    from this step have "ipc \<in> domain ?ctx" by auto
    then obtain pre post where "pre @ ipc # post = sorted_list_of_set (domain ?ctx)" using sorted_list_of_set_split domain_finite by metis
    hence "r_step_map f prog ?ctx = (fold ?smf post \<circ> ?smf ipc \<circ> fold ?smf pre) \<bottom>" using fold_split by (metis r_step_map.simps)
    hence split: "r_step_map f prog ?ctx = fold ?smf post (?smf ipc (fold ?smf pre \<bottom>))" by simp
    hence post:"?smf ipc (fold ?smf pre \<bottom>) \<le> r_step_map f prog ?ctx" by (metis fold_grow r_step_map_from_grows)
    let ?prefold = "fold ?smf pre \<bottom>"
    have "ost \<le> lookup (?smf ipc ?prefold) pc"
    proof -
      have smf: "?smf ipc ?prefold = ?prefold \<squnion> f op ipc (lookup ?ctx ipc)" using step(1) by simp
      have "ost \<le> lookup (?prefold \<squnion> f op ipc (lookup ?ctx ipc)) pc" using step(3) by auto
      thus ?thesis using smf by simp
    qed
    from post this show ?case by (simp add: order_trans less_eq_state_map_def)
  next
    case (2 y)
    let ?supset = "{ost. \<exists>ipc op. prog ipc = Some op \<and> lookup ?ctx ipc \<noteq> \<bottom> \<and> lookup (f op ipc (lookup ?ctx ipc)) pc = ost}"
    show ?case
    proof(rule ccontr)
      assume ass: "\<not> lookup (r_step_map f prog ?ctx) pc \<le> y"
      let ?f = "r_step_map_from f prog ?ctx"
      let ?l = "sorted_list_of_set (domain ?ctx)"
      from ass have "\<not> lookup (fold ?f ?l \<bottom>) pc \<le> y" by simp
      from this obtain pre ipc post where split:
        "?l = pre @ ipc # post"
        "lookup (fold ?f pre \<bottom>) pc \<le> y"
        "\<not> lookup (?f ipc (fold ?f pre \<bottom>)) pc \<le> y"
        using fold_overgrowth_lookup by (metis bot_lookup r_step_map_from_grows sup.orderI sup_bot.right_neutral)
      let ?prefold = "fold ?f pre \<bottom>"

      have "\<exists>op. Some op = prog ipc" proof (cases "prog ipc")
        case None
        hence eq: "?f ipc ?prefold = ?prefold" by simp
        have neq: "?f ipc ?prefold \<noteq> ?prefold"
        proof (rule ccontr)
          assume "\<not> ?f ipc ?prefold \<noteq> ?prefold"
          from this split(2) have "lookup (?f ipc ?prefold) pc \<le> y" by simp
          from this split(3) show False by blast
        qed
        from eq neq show ?thesis by blast
      qed simp
      from this obtain op where op: "prog ipc = Some op" by fastforce

      let ?z = "lookup (f op ipc (lookup ?ctx ipc)) pc"
      from op split(3) split(2) have nope: "\<not> ?z \<le> y" by simp

      have zin: "?z \<in> ?supset" proof(standard, goal_cases)
        case 1
        from split(1) have "pre @ ipc # post = sorted_list_of_set (domain ?ctx)" ..
        hence "ipc \<in> domain ?ctx" using sorted_list_of_set_in by blast
        hence "lookup ?ctx ipc \<noteq> \<bottom>" by simp
        from this op show ?case by blast
      qed

      from zin nope 2 show False by blast
    qed
  qed
  thus "lookup (step_map f prog ?ctx) pc = lookup (r_step_map f prog ?ctx) pc" for pc by simp
qed

(***********)

value "
  let m = \<bottom>::bool state_map;
      m2 = merge_single m 42 True;
      m3 = merge_single m2 123 False in
  domain m3"

fun showit :: "bool state_map \<Rightarrow> string" where
  "showit m = (if m = \<top> then ''TOP!'' else ''something else'')"

end
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
datatype special_state_map = Top

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

fun RSMS :: "special_state_map \<Rightarrow> 'a::top state_map" where
  "RSMS m = \<top>"

code_datatype RSM RSMS

definition "r_empty_map \<equiv> Mapping.empty::('a::bot) r_state_map"

lemma r_bot[code]: "\<bottom> = RSM r_empty_map"
  by (rule lookup_eq; simp add: lookup_default_empty r_empty_map_def)

lemma r_top[code]: "\<top> = RSMS Top" by simp

lemma r_lookup[code]: "lookup (RSM m) = r_lookup m" by simp

lemma [code]: "lookup (RSMS m) pc = \<top>" by simp

fun r_single :: "addr \<Rightarrow> 'a::absstate \<Rightarrow> 'a r_state_map" where
  "r_single k v = Mapping.update k v \<bottom>"

lemma r_single[code]: "single k v = RSM (r_single k v)"
  by (rule lookup_eq; simp add: bot_mapping_def lookup_default_empty lookup_default_update')

lemma single_lookup: "lookup (single k v) k = v" by simp

lemma single_lookup_le: "x \<le> single k v \<Longrightarrow> lookup x k \<le> v"
  by (metis less_eq_state_map_def single_lookup)

lemma r_single_structure: "\<exists>m. r_single k v = Mapping m"
  by (metis bot_mapping_def empty_Mapping insert_Mapping r_single.simps)

fun merge_single :: "('a::bounded_semilattice_sup_bot) state_map \<Rightarrow> addr \<Rightarrow> 'a \<Rightarrow> 'a state_map" where
  "merge_single (SM m) pc x = SM (\<lambda>npc. if npc = pc then x \<squnion> m npc else m npc)"

lemma merge_single_grows: "m \<le> merge_single m pc x"
proof -
  obtain mm where sm: "m = SM mm" using state_map_single_constructor by blast
  have "lookup (SM mm) p \<le> lookup (merge_single (SM mm) pc x) p" for p by simp
  from this sm show ?thesis using less_eq_state_map_def by blast
qed

lemma merge_single_bot: "merge_single a k \<bottom> = a"
proof (rule state_map_eq_fwd)
  fix p
  obtain m where "a = SM m" using state_map_single_constructor by blast
  then show "lookup (merge_single a k \<bottom>) p = lookup a p" by simp
qed

fun r_merge_single :: "('a::{bounded_semilattice_sup_bot}) r_state_map \<Rightarrow> addr \<Rightarrow> 'a \<Rightarrow> 'a r_state_map" where
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

lemma r_domain: "r_domain m = {a. r_lookup m a \<noteq> \<bottom>}"
proof (intro Set.equalityI Set.subsetI)
  fix x assume "x \<in> {a. r_lookup m a \<noteq> \<bottom>}"
  hence lookup: "r_lookup m x \<noteq> \<bottom>" by simp
  from lookup have r_lookup: "r_lookup m x \<noteq> \<bottom>" by simp
  from r_lookup have keys: "x \<in> Mapping.keys m"
    by (metis Option.is_none_def empty_iff keys_empty keys_is_none_rep lookup_default_def lookup_default_empty r_lookup.simps)
  from keys r_lookup show "x \<in> r_domain m" by auto
qed auto

lemma r_domain_ref[code]: "domain (RSM m) = r_domain m" using r_domain by fastforce

lemma r_domain_finite: "finite (r_domain (Mapping m))" by (simp add: keys_Mapping)
lemma domain_finite: "finite (domain (RSM (Mapping m)))" using r_domain_ref r_domain_finite by metis

lemma r_domain_update_bot: "r_domain (Mapping.update k \<bottom> m) = r_domain m - {k}"
proof(intro Set.equalityI Set.subsetI, goal_cases)
  case (1 x)
  hence lookup: "r_lookup (Mapping.update k \<bottom> m) x \<noteq> \<bottom>" using r_domain by simp
  then show ?case
  proof (cases "x = k")
    case True
    hence False using lookup by (simp add: lookup_default_update)
    then show ?thesis ..
  next
    case False
    from lookup have "r_lookup m x \<noteq> \<bottom>" by (metis lookup_default_update' r_lookup.simps)
    hence inm: "x \<in> r_domain m" using r_domain by fastforce
    from False this show ?thesis by blast
  qed
next
  case (2 x)
  hence inm: "x \<in> r_domain m" by blast
  then show ?case
  proof (cases "x = k")
    case True
    then show ?thesis using 2 by blast
  next
    case False
    from inm have "r_lookup m x \<noteq> \<bottom>" using r_domain by simp
    from False this have "r_lookup (Mapping.update k \<bottom> m) x \<noteq> \<bottom>" by (metis lookup_default_update' r_lookup.simps)
    then show ?thesis using r_domain by fastforce
  qed
qed

lemma r_single_domain: 
  assumes "v \<noteq> \<bottom>"
  shows "r_domain (r_single k v) = {k}"
proof (intro Set.equalityI Set.subsetI, goal_cases)
  case (1 x)
  have "r_lookup (r_single k v) a \<noteq> \<bottom> \<Longrightarrow> a = k" for a
    by (metis bot_mapping_def lookup_default_empty lookup_default_update' r_lookup.simps r_single.simps)
  from 1 this have "x = k" by simp
  then show ?case by simp
next
  case (2 x)
  hence "x = k" by blast
  then show ?case using r_domain assms
    by (simp add: lookup_default_update')
qed

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

lemma sup_mapping_aux_structure: "\<exists>m. sup_mapping_aux b pc (Mapping acc) = Mapping m"
  using insert_Mapping by fastforce

instantiation mapping :: (linorder, "bounded_semilattice_sup_bot") sup
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
lemma mapping_sup_ge1 [simp]: "(x::('a::linorder, 'b::bounded_semilattice_sup_bot) mapping) \<le> x \<squnion> y"
proof -
  have "acc \<le> (sup_mapping_aux y) a acc" for a acc using sup_mapping_aux_grows by simp
  thus ?thesis by (simp add: fold_grow)
qed

lemma sorted_list_of_set_prep:
  assumes
    "x # xs = sorted_list_of_set s"
    "a \<in> set xs"
  shows
    "a \<noteq> x"
  by (metis Diff_insert_absorb assms(1) assms(2) distinct_sorted_list_of_set insert_absorb2 list.simps(15) mk_disjoint_insert remove1.simps(2) set_remove1_eq)

lemma mapping_sup_lookup:
  assumes "finite (r_domain b)"
  shows "r_lookup (a \<squnion> b) pc = r_lookup a pc \<squnion> r_lookup b pc"
using assms proof(induction "sorted_list_of_set (r_domain b)" arbitrary: a b)
  case Nil
  from Nil have left: "r_lookup (a \<squnion> b) pc = r_lookup a pc" by simp
  from Nil have nob: "r_domain b = {}" using sorted_list_of_set_eq_Nil_iff by fastforce
  have bot: "r_lookup b pc = \<bottom>"
  proof (rule ccontr)
    assume "\<not> r_lookup b pc = \<bottom>"
    thus False using r_domain nob by fastforce
  qed
  then show ?case using left by simp
next
  case (Cons x xs)
  
  let ?bprev = "Mapping.update x \<bottom> b"
  let ?anext = "sup_mapping_aux b x a"

  have prevdom: "r_domain ?bprev = r_domain b - {x}" by (rule r_domain_update_bot)

  have xs_bprev: "xs = sorted_list_of_set (r_domain ?bprev)" using prevdom
    by (metis Cons.hyps(2) Cons.prems remove1.simps(2) sorted_list_of_set_remove)

  have finite_bprev: "finite (r_domain ?bprev)" using prevdom Cons.prems by auto

  from Cons(2) have "aa \<in> set xs \<Longrightarrow> aa \<noteq> x" for aa by (rule sorted_list_of_set_prep)
  hence foldbprev_any: "fold (sup_mapping_aux ?bprev) xs init = fold (sup_mapping_aux b) xs init" for init
  proof(induction xs arbitrary: init)
    case (Cons aa xxs)
    hence "aa \<noteq> x" by simp
    hence "r_lookup ?bprev aa = r_lookup b aa" by (metis lookup_default_update_neq r_lookup.simps)
    hence "sup_mapping_aux ?bprev aa acc = sup_mapping_aux b aa acc" for acc by simp
    from this Cons show ?case by simp
  qed simp

  have sup: "a \<squnion> b = fold (sup_mapping_aux b) xs ?anext" by (metis Cons.hyps(2) List.fold_simps(2) sup_mapping.simps)
  from sup foldbprev_any have foldbprev_concrete: "a \<squnion> b = fold (sup_mapping_aux ?bprev) xs ?anext" by simp

  from xs_bprev finite_bprev have lookup_prev: "r_lookup (?anext \<squnion> ?bprev) pc = r_lookup ?anext pc \<squnion> r_lookup ?bprev pc" by (rule Cons(1))
  from foldbprev_concrete this show ?case
    by (metis (mono_tags, lifting) lookup_default_update lookup_default_update_neq r_lookup.simps sup_bot.right_neutral sup_mapping.simps sup_mapping_aux.elims xs_bprev)
qed

lemma mapping_sup_ge2:
  assumes "finite (r_domain y)"
  shows "(y::('a::linorder, 'b::bounded_semilattice_sup_bot) mapping) \<le> x \<squnion> y"
proof(rule mapping_leI)
  fix p
  from assms have "r_lookup (x \<squnion> y) p = r_lookup x p \<squnion> r_lookup y p" by (rule mapping_sup_lookup) 
  thus "r_lookup y p \<le> r_lookup (x \<squnion> y) p" by simp
qed

lemma mapping_sup_least:
  assumes
    "(y::('a::linorder, 'b::bounded_semilattice_sup_bot) mapping) \<le> x"
    "z \<le> x"
  shows "y \<squnion> z \<le> x"
proof(rule mapping_leI)
  fix p
  show "r_lookup (y \<squnion> z) p \<le> r_lookup x p" using assms
    by (metis List.fold_simps(1) le_sup_iff less_eq_mapping_def mapping_sup_lookup sorted_list_of_set.infinite sup_mapping.simps)
qed

lemma mapping_sup[code]: "((RSM a)::'a::bounded_semilattice_sup_bot state_map) \<squnion> RSM (Mapping bm) = RSM (a \<squnion> (Mapping bm))"
proof (rule state_map_eq_fwd)
  let ?b = "Mapping bm"
  have "finite (r_domain ?b)" using r_domain_finite by blast
  then show "lookup (RSM a \<squnion> RSM ?b) p = lookup (RSM (a \<squnion> ?b)) p" for p
    by (metis RSM_def lookup.simps mapping_sup_lookup sup_lookup)
qed

lemma fold_mapping_structure:
  assumes "\<And>e acc. \<exists>m. f e (Mapping acc) = Mapping m"
  shows "\<exists>m. fold f l (Mapping a) = Mapping m"
proof(induction l arbitrary: a)
  case (Cons x xs)
  then show ?case by (metis List.fold_simps(2) assms)
qed auto

lemma mapping_sup_structure: "\<exists>m. Mapping a \<squnion> Mapping b = Mapping m"
  using fold_mapping_structure sup_mapping_aux_structure by (metis sup_mapping.simps)

lemma r_merge_single_sup_single:
  assumes "v \<noteq> \<bottom>"
  shows "r_merge_single m k v = m \<squnion> r_single k v"
proof -
  from assms have "m \<squnion> r_single k v = fold (sup_mapping_aux (r_single k v)) [k] m" using r_single_domain by fastforce
  then show ?thesis by (simp add: lookup_default_update' sup.commute)
qed

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

text\<open>For advance on \<top>\<close>
lemma [code]: "(a::'a::absstate state_map) \<squnion> RSMS b = \<top>" by simp
lemma [code]: "((RSMS a)::'a::absstate state_map) \<squnion> b = \<top>" by simp

lemma advance_top[code]: "advance f prog (RSMS a) = (\<top>::'a::absstate state_map)" by simp

(* TODO: this is automatically deleted, is there a better way? *)
fun r_advance :: "('a::{semilattice_sup, Sup, bot}) astep \<Rightarrow> program \<Rightarrow> 'a state_map \<Rightarrow> 'a state_map" where
  "r_advance f prog ctx = ctx \<squnion> step_map f prog ctx"
lemma [code]: "advance f prog (RSM a) = r_advance f prog (RSM a)" by simp

text\<open>Early loop exit when encountering \<top>\<close>

fun loop_continue :: "('a::absstate) astep \<Rightarrow> program \<Rightarrow> fuel \<Rightarrow> 'a state_map \<Rightarrow> 'a state_map" where
  "loop_continue f prog n advanced = (if advanced = \<top> then \<top> else loop f prog n advanced)"

lemma [code]: "loop_continue f prog n (RSMS m) = \<top>" by simp

lemma "loop f prog (Suc n) st = loop_continue f prog n (advance f prog st)"
proof (cases "advance f prog st = \<top>")
  case True
  then show ?thesis by (induction n; simp)
qed simp

subsection \<open>Helper Refinement\<close>

fun r_deep_merge_l :: "(addr * ('a::absstate)) list \<Rightarrow> 'a r_state_map \<Rightarrow> 'a r_state_map" where
  "r_deep_merge_l sts init = fold (\<lambda>(pc, v) acc. r_merge_single acc pc v) sts init"

lemma r_deep_merge_l_cons:
  assumes "v \<noteq> \<bottom>"
  shows "r_deep_merge_l ((k, v) # xs) init = r_deep_merge_l xs (init \<squnion> r_single k v)"
  using assms r_merge_single_sup_single by fastforce

lemma r_deep_merge_l_lift: "RSM a = RSM b \<Longrightarrow> RSM (r_deep_merge_l l a) = RSM (r_deep_merge_l l b)"
proof(induction l arbitrary: a b)
  case (Cons x xs)
  then show ?case by (smt List.fold_simps(2) case_prod_conv r_deep_merge_l.simps r_merge_single r_single.cases)
qed simp

lemma r_merge_single_bot: "RSM (r_merge_single a k \<bottom>) = RSM a"
proof -
  have "RSM (r_merge_single a k \<bottom>) = merge_single (RSM a) k \<bottom>" using r_merge_single by metis
  then show ?thesis by (simp add: merge_single_bot)
qed

lemma r_deep_merge_l_bot: "RSM (r_deep_merge_l ((k, \<bottom>) # xs) init) = RSM (r_deep_merge_l xs init)"
proof -
  have same: "RSM (r_merge_single init k \<bottom>) = RSM init" using r_merge_single_bot by blast
  have "RSM (r_deep_merge_l xs (r_merge_single init k \<bottom>)) = RSM (r_deep_merge_l xs init)" using same by (rule r_deep_merge_l_lift)
  from this show ?thesis using r_deep_merge_l_lift by simp
qed

lemma deep_merge_init: "deep_merge (set s) \<squnion> (RSM (Mapping init)) = RSM (r_deep_merge_l s (Mapping init))"
proof(induction s arbitrary: init)
  case Nil
  let ?init = "Mapping init"
  have l: "deep_merge (set []) \<squnion> (RSM ?init) = RSM ?init" by (metis deep_merge_empty list.set(1) sup_bot.left_neutral)
  have r: "r_deep_merge_l [] ?init = ?init" by (simp add: bot_mapping_def lookup_default_empty)
  from l r show ?case by simp
next
  case (Cons x xs)
  let ?init = "Mapping init"
  obtain xp xv where x: "(xp, xv) = x" by (metis surj_pair)
  from this have "deep_merge (set (x # xs)) = deep_merge (set xs) \<squnion> single xp xv" using deep_merge_cons by blast
  hence "deep_merge (set (x # xs)) = deep_merge (set xs) \<squnion> RSM (r_single xp xv)" using r_single by metis
  hence split_l: "deep_merge (set (x # xs)) \<squnion> RSM ?init = deep_merge (set xs) \<squnion> RSM (r_single xp xv \<squnion> ?init)"
    by (metis (no_types, lifting) inf_sup_aci(6) mapping_sup)

  let ?nextinit = "?init \<squnion> r_single xp xv"

  have step: "deep_merge (set xs) \<squnion> RSM ?nextinit = RSM (r_deep_merge_l xs ?nextinit)"
  proof -
    have "\<exists>sm. r_single xp xv = Mapping sm" using r_single_structure by simp
    obtain m where "Mapping init \<squnion> r_single xp xv = Mapping m" using mapping_sup_structure r_single_structure by metis
    from this Cons show ?thesis by simp
  qed

  show ?case
  proof (cases "xv = \<bottom>")
    case True
    hence lreduce: "deep_merge (set (x # xs)) = deep_merge (set xs)" using deep_merge_bot using x by blast
    have "RSM (r_deep_merge_l (x # xs) (RBT_Mapping.Mapping init)) = RSM (r_deep_merge_l xs \<bottom>) \<squnion> RSM (RBT_Mapping.Mapping init)" using r_deep_merge_l_bot
      by (metis Cons.IH True boolean_algebra_cancel.sup0 bot_mapping_def empty_Mapping r_bot r_empty_map_def x)
    from this lreduce show ?thesis by (metis Cons.IH True r_deep_merge_l_bot x) 
  next
    case False
    hence "xv \<noteq> \<bottom> \<Longrightarrow> r_deep_merge_l (x # xs) ?init = r_deep_merge_l xs ?nextinit" using r_deep_merge_l_cons x by blast
    from this split_l step show ?thesis
      by (metis False mapping_sup r_single_structure sup.commute)
  qed
qed

lemma deep_merge[code]: "deep_merge ((set s)::(addr * 'b::absstate) set) = RSM (r_deep_merge_l s \<bottom>)"
proof -
  obtain init where init: "Mapping init = (\<bottom>::'b r_state_map)" by (simp add: bot_mapping_def empty_Mapping)
  have "deep_merge (set s) \<squnion> (RSM (Mapping init)) = RSM (r_deep_merge_l s (Mapping init))" by (rule deep_merge_init)
  from this init have "deep_merge (set s) \<squnion> (RSM \<bottom>) = RSM (r_deep_merge_l s \<bottom>)" by simp
  hence "deep_merge (set s) \<squnion> \<bottom> = RSM (r_deep_merge_l s \<bottom>)" by (simp add: r_bot bot_mapping_def r_empty_map_def)
  thus ?thesis by simp
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
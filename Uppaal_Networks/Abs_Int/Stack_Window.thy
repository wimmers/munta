theory Stack_Window
  imports Stack State_Smart Abs_Word
begin

type_synonym 'a stack_window = "'a list toption"

instantiation toption :: ("{semilattice_sup, order_bot}") absstack
begin
instance ..
end

fun \<gamma>_list_window :: "nat \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'a list \<Rightarrow> 'b list set" where
  "\<gamma>_list_window _ _ [] = {[]}" |
  "\<gamma>_list_window 0 \<gamma>_word (a # as) = {l. \<forall>x \<in> set l. x \<in> \<gamma>_word a}" |
  "\<gamma>_list_window (Suc n) \<gamma>_word (a # as) = {l. \<exists>x xs. l = x # xs \<and> x \<in> \<gamma>_word a \<and> xs \<in> \<gamma>_list_window n \<gamma>_word as} \<squnion> {[]}"

lemma \<gamma>_list_window_empty: "[] \<in> \<gamma>_list_window n \<gamma>_word l"
proof (cases l)
  case (Cons a as)
  then show ?thesis
  proof (cases n)
    case 0
    have "[] \<in> {l. \<forall>x \<in> set l. x \<in> \<gamma>_word a}" by simp
    then show ?thesis using 0 Cons by simp
  qed simp
qed simp

lemma \<gamma>_list_window_mono:
  assumes
    "\<And>ax bx. ax \<le> bx \<Longrightarrow> \<gamma>_word ax \<le> \<gamma>_word bx"
    "a \<le> b"
  shows "\<gamma>_list_window n \<gamma>_word a \<le> \<gamma>_list_window n \<gamma>_word b"
using assms(2) proof (induction a arbitrary: n b)
  case Nil
  then show ?case using \<gamma>_list_window_empty by simp
next
  case (Cons ax as)
  obtain bx bs where bsplit: "b = bx # bs" using Cons.prems less_eq_list.elims(2) by blast
  hence axbx: "\<gamma>_word ax \<le> \<gamma>_word bx" using assms(1) Cons by auto
  then show ?case
  proof (cases n)
    case 0
    then show ?thesis using axbx bsplit by fastforce
  next
    case (Suc nn)
    have "\<gamma>_list_window nn \<gamma>_word as \<subseteq> \<gamma>_list_window nn \<gamma>_word bs" using Cons.IH Cons.prems bsplit by auto
    hence "{l. \<exists>x xs. l = x # xs \<and> x \<in> \<gamma>_word ax \<and> xs \<in> \<gamma>_list_window nn \<gamma>_word as} \<le> {l. \<exists>x xs. l = x # xs \<and> x \<in> \<gamma>_word bx \<and> xs \<in> \<gamma>_list_window nn \<gamma>_word bs}" using axbx by auto
    then show ?thesis using Suc bsplit by fastforce
  qed
qed

fun \<gamma>_stack_window :: "nat \<Rightarrow> ('a \<Rightarrow> int set) \<Rightarrow> 'a stack_window \<Rightarrow> stack set" where
  "\<gamma>_stack_window _ _ Top = \<top>" |
  "\<gamma>_stack_window n \<gamma>_word (Minor l) = \<gamma>_list_window n \<gamma>_word l"

definition stack_window_top_equivalent :: "nat \<Rightarrow> 'a::order_top stack_window" where
  "stack_window_top_equivalent window_size \<equiv> Minor (replicate (Suc window_size) \<top>)"

lemma stack_window_top_equivalent:
  assumes "\<gamma>_word \<top> = \<top>"
  shows "\<gamma>_stack_window n \<gamma>_word (stack_window_top_equivalent n) = \<top>"
proof (induction n)
  case 0
  let ?l = "replicate (Suc 0) \<top>"
  have "\<gamma>_stack_window 0 \<gamma>_word (stack_window_top_equivalent 0) = \<gamma>_list_window 0 \<gamma>_word ?l"
    unfolding stack_window_top_equivalent_def by simp
  also have "\<dots> = {l. \<forall>x \<in> set l. x \<in> \<gamma>_word \<top>}" by simp
  finally show ?case using assms by simp
next
  case (Suc n)
  let ?l = "replicate (Suc (Suc n)) \<top>"
  have "\<gamma>_stack_window (Suc n) \<gamma>_word (stack_window_top_equivalent (Suc n)) = \<gamma>_list_window (Suc n) \<gamma>_word ?l"
    unfolding stack_window_top_equivalent_def by simp
  also have "\<dots> = {l. \<exists>x xs. l = x # xs \<and> x \<in> \<gamma>_word \<top> \<and> xs \<in> \<gamma>_list_window n \<gamma>_word (replicate (Suc n) \<top>)} \<squnion> {[]}" by simp
  also have "\<dots> = {l. \<exists>x xs. l = x # xs \<and> x \<in> \<gamma>_word \<top> \<and> xs \<in> \<top>} \<squnion> {[]}"
    using Suc.IH by (simp add: stack_window_top_equivalent_def)
  also have "\<dots> = {l. \<exists>x xs. l = x # xs} \<squnion> {[]}" using assms by auto
  also have "\<dots> = \<top>"
  proof (intro Set.equalityI Set.subsetI, goal_cases)
    case (2 x)
    then show ?case by (cases x; simp)
  qed blast
  finally show ?case .
qed

fun push_list_window :: "nat \<Rightarrow> ('a::absword) list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "push_list_window _ [] x = [x]" |
  "push_list_window 0 (a # as) x = (x \<squnion> a) # as" |
  "push_list_window (Suc n) (a # as) x = x # push_list_window n as a"

lemma push_list_window:
  assumes
    "c \<in> \<gamma>_list_window n \<gamma>_word b"
    "cx \<in> \<gamma>_word x" and
    gamma_mono: "\<And>ax bx. ax \<le> bx \<Longrightarrow> \<gamma>_word ax \<le> \<gamma>_word bx"
  shows "(cx # c) \<in> \<gamma>_list_window n \<gamma>_word (push_list_window n b x)"
using assms(1) assms(2) proof (induction n arbitrary: c cx b x)
  case 0
  then show ?case
  proof (cases b)
    case Nil
    hence "c = []" using 0 by simp
    then show ?thesis by (simp add: 0 local.Nil)
  next
    case (Cons bx bs)
    hence ccx: "\<forall>ccx\<in>set c. ccx \<in> \<gamma>_word bx" using "0.prems"(1) by auto
    obtain px ps where pxps: "px # ps = push_list_window 0 b x" by (simp add: local.Cons)
    have px: "px = bx \<squnion> x" using local.Cons pxps sup.commute by auto
    hence "cx \<in> \<gamma>_word px" using gamma_mono by (meson "0.prems"(2) in_mono sup.cobounded2)
    moreover from px ccx have "\<forall>ccx\<in>set c. ccx \<in> \<gamma>_word px" by (meson gamma_mono in_mono sup_ge1)
    ultimately have "cx # c \<in> {l. \<forall>x \<in> set l. x \<in> \<gamma>_word px}" by auto
    then show ?thesis using Cons pxps by simp
  qed
next
  case (Suc n)
  then show ?case
  proof (cases b)
    case Nil
    hence "c = []" using Suc by simp
    then show ?thesis by (simp add: Suc local.Nil)
  next
    case (Cons bx bs)
    obtain px ps where pxps: "px # ps = push_list_window (Suc n) b x" by (simp add: local.Cons)
    have "cx \<in> \<gamma>_word px" using Suc.prems(2) local.Cons pxps by auto
    moreover have "c \<in> \<gamma>_list_window n \<gamma>_word ps"
    proof(cases c)
      case Nil then show ?thesis using \<gamma>_list_window_empty by blast
    next
      fix ccx ccs assume ass: "c = ccx # ccs"
      have ps: "ps = push_list_window n bs bx" using Cons pxps by simp
      have "ccs \<in> \<gamma>_list_window n \<gamma>_word bs" using Suc.prems(1) ass local.Cons by auto
      moreover have "ccx \<in> \<gamma>_word bx" using Suc(2) ass local.Cons by auto
      ultimately have "ccx # ccs \<in> \<gamma>_list_window n \<gamma>_word (push_list_window n bs bx)" by (rule Suc.IH)
      thus ?thesis using ass ps by simp
    qed
    ultimately have "cx # c \<in> {l. \<exists>x xs. l = x # xs \<and> x \<in> \<gamma>_word px \<and> xs \<in> \<gamma>_list_window n \<gamma>_word ps} \<squnion> {[]}" by simp
    then show ?thesis by (metis \<gamma>_list_window.simps(3) pxps)
  qed
qed

fun push_stack_window :: "nat \<Rightarrow> ('a::absword) stack_window \<Rightarrow> 'a \<Rightarrow> 'a stack_window" where
  "push_stack_window _ Top _ = Top" |
  "push_stack_window n (Minor l) x = Minor (push_list_window n l x)"

fun pop_list_window :: "nat \<Rightarrow> ('a::absword) list \<Rightarrow> ('a * 'a list)" where
  "pop_list_window _ [] = (\<bottom>, [])" |
  "pop_list_window 0 (a # as) = (a, a # as)" |
  "pop_list_window (Suc n) (a # as) = (a, fst (pop_list_window n as) # snd (pop_list_window n as))"

lemma pop_list_window:
  assumes
    "(cx # c) \<in> \<gamma>_list_window n \<gamma>_word b" and
    gamma_mono: "\<And>ax bx. ax \<le> bx \<Longrightarrow> \<gamma>_word ax \<le> \<gamma>_word bx"
  shows
    "c \<in> \<gamma>_list_window n \<gamma>_word (snd (pop_list_window n b)) \<and> cx \<in> \<gamma>_word (fst (pop_list_window n b))"
using assms(1) proof(induction n arbitrary: c cx b)
  case 0
  from this obtain bx bs where bxbs: "b = bx # bs" by (metis \<gamma>_list_window.simps(1) empty_iff insert_iff list.distinct(1) list.exhaust)
  thus ?case using 0 by auto
next
  case (Suc n)
  from this obtain bx bs where bxbs: "b = bx # bs" by (metis \<gamma>_list_window.simps(1) empty_iff insert_iff list.distinct(1) list.exhaust)
  have "c \<in> {l. \<exists>x xs. l = x # xs \<and> x \<in> \<gamma>_word (fst (pop_list_window n bs)) \<and> xs \<in> \<gamma>_list_window n \<gamma>_word (snd (pop_list_window n bs))} \<squnion> {[]}"
  proof (cases c)
    case (Cons ccx ccs)
    have "ccx \<in> \<gamma>_word (fst (pop_list_window n bs)) \<and> ccs \<in> \<gamma>_list_window n \<gamma>_word (snd (pop_list_window n bs))" using Suc.IH Cons
      using Suc.prems bxbs by auto
    then show ?thesis using Cons by simp
  qed simp
  moreover have "cx \<in> \<gamma>_word (fst (pop_list_window (Suc n) (bx # bs)))" using Suc.prems bxbs by auto
  ultimately show ?case using bxbs by auto
qed

fun pop_stack_window :: "nat \<Rightarrow> ('a::absword) stack_window \<Rightarrow> ('a * 'a stack_window)" where
  "pop_stack_window _ Top = (\<top>, Top)" |
  "pop_stack_window n (Minor l) = (fst (pop_list_window n l), Minor (snd (pop_list_window n l)))"

lemma window_mono_gamma_stack:
  assumes
    "\<And>a b. a \<le> b \<Longrightarrow> \<gamma>_word a \<le> \<gamma>_word b"
    "a \<le> b"
  shows "\<gamma>_stack_window n \<gamma>_word a \<le> \<gamma>_stack_window n \<gamma>_word b"
proof (cases b)
  case (Minor sb)
  from this obtain sa where sa: "a = Minor sa" using assms(2) less_eq_toption.elims(2) by blast
  from this Minor show ?thesis using assms mono_gamma_list by (simp add: \<gamma>_list_window_mono)
qed simp

lemma window_gamma_Top: "\<gamma>_stack_window n \<gamma>_word \<top> = \<top>" by simp

lemma window_push_correct:
  assumes
    "\<And>a b. a \<le> b \<Longrightarrow> \<gamma>_word a \<le> \<gamma>_word b"
    "c \<in> \<gamma>_stack_window n \<gamma>_word b"
    "cx \<in> \<gamma>_word x"
  shows "(cx # c) \<in> \<gamma>_stack_window n \<gamma>_word (push_stack_window n b x)"
proof (cases b)
  case (Minor as)
  then show ?thesis using push_list_window
    by (metis assms \<gamma>_stack_window.simps(2) push_stack_window.simps(2))
qed simp

lemma window_pop_correct:
  assumes
    "\<And>a b. a \<le> b \<Longrightarrow> \<gamma>_word a \<le> \<gamma>_word b"
    "\<gamma>_word \<top> = \<top>"
    "(cx # c) \<in> \<gamma>_stack_window n \<gamma>_word b"
  shows
    "c \<in> \<gamma>_stack_window n \<gamma>_word (snd (pop_stack_window n b))"
    "cx \<in> \<gamma>_word (fst (pop_stack_window n b))"
proof (goal_cases)
  case 1 show ?case
  proof (cases b)
    case (Minor l)
    then show ?thesis using assms pop_list_window by force
  qed simp
next
  case 2 show ?case
  using assms(2) proof (cases b)
    case (Minor l)
    then show ?thesis using assms by (simp add: pop_list_window)
  qed simp
qed

locale Stack_Window = Abs_Stack \<gamma>_word "\<gamma>_stack_window n \<gamma>_word" "push_stack_window n" "pop_stack_window n" for n \<gamma>_word

sublocale Abs_Word \<subseteq> Window: Stack_Window
proof(standard, goal_cases)
  case (1 a b) from mono_gamma this show ?case by (rule window_mono_gamma_stack) next
  case 2 show ?case by (rule window_gamma_Top) next
  case (3 c rest cx a) from mono_gamma this show ?case by (rule window_push_correct) next
  case (4 cx c b) from mono_gamma gamma_Top this show ?case by (rule window_pop_correct(1)) next
  case (5 cx c b) from mono_gamma gamma_Top this show ?case by (rule window_pop_correct(2))
qed

(*context Abs_Word
begin
abbreviation "ai_loop \<equiv> Window.ai_loop"
end*)

end
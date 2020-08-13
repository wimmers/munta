theory Stack_Direct
  imports Stack State_Smart
begin

type_synonym 'a stack_direct = "'a list toption"

instantiation toption :: (bounded_semilattice_sup_bot) absstack
begin
instance ..
end

fun \<gamma>_stack_direct :: "('a \<Rightarrow> int set) \<Rightarrow> 'a stack_direct \<Rightarrow> stack set" where
  "\<gamma>_stack_direct _ Top = \<top>" |
  "\<gamma>_stack_direct \<gamma>_word (Minor l) = \<gamma>_list \<gamma>_word l"

fun push_stack_direct :: "'a stack_direct \<Rightarrow> 'a \<Rightarrow> 'a stack_direct" where
  "push_stack_direct Top _ = Top" |
  "push_stack_direct (Minor l) x = Minor (x # l)"

fun pop_stack_direct :: "('a::{bot, top}) stack_direct \<Rightarrow> ('a * 'a stack_direct)" where
  "pop_stack_direct Top = (\<top>, Top)" |
  "pop_stack_direct (Minor []) = (\<bottom>, Minor [])" |
  "pop_stack_direct (Minor (a # as)) = (a, Minor as)"

locale StackDirect = AbsStack \<gamma>_word "\<gamma>_stack_direct \<gamma>_word" push_stack_direct pop_stack_direct for \<gamma>_word

sublocale AbsWord \<subseteq> Direct: StackDirect
proof(standard, goal_cases)
  case (1 a b)
  then show ?case
  proof (cases b)
    case (Minor sb)
    from this obtain sa where sa: "a = Minor sa" using 1 less_eq_toption.elims(2) by blast
    from this Minor show ?thesis using 1 mono_gamma_list mono_gamma by auto
  qed simp
next
  case 2
  then show ?case by simp
next
  case (3 c rest cx a)
  then show ?case
  proof (cases rest)
    case (Minor as)
    hence "cx # c \<in> {l. \<exists>x xs. l = x # xs \<and> x \<in> \<gamma>_word a \<and> xs \<in> \<gamma>_list \<gamma>_word as}" using 3(1) 3(2) by auto
    then show ?thesis by (simp add: Minor)
  qed simp
next
  case (4 cx c b)
  then show ?case
  proof (cases b)
    case (Minor l)
    then show ?thesis
    proof (cases l)
      case Nil
      hence "\<gamma>_stack_direct \<gamma>_word b = {[]}" using Minor by simp
      hence False using 4 by simp
      thus ?thesis ..
    next
      case (Cons a as)
      then show ?thesis using 4 Minor by auto
    qed
  qed simp
next
  case (5 cx c b)
  then show ?case
  proof (cases b)
    case (Minor l)
    then show ?thesis
    proof (cases l)
      case Nil
      hence "\<gamma>_stack_direct \<gamma>_word b = {[]}" using Minor by simp
      hence False using 5 by simp
      thus ?thesis ..
    next
      case (Cons a as)
      then show ?thesis using 5 Minor by auto
    qed
  qed simp
qed

context AbsWord
begin
abbreviation "ai_loop \<equiv> Direct.ai_loop"
end

end
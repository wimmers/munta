theory Stack
  imports Word ListLattice
begin

class absstack = bounded_semilattice_sup_bot + order_top

locale AbsStack = AbsWord +
  fixes \<gamma>_stack :: "('b::absstack) \<Rightarrow> stack set" and
        push :: "'b \<Rightarrow> ('a::absword) \<Rightarrow> 'b" and
        pop :: "'b \<Rightarrow> ('b * 'a)"
  assumes mono_gamma_stack: "a \<le> b \<Longrightarrow> \<gamma>_stack a \<le> \<gamma>_stack b"
  and gamma_Top[simp]: "\<gamma>_stack \<top> = \<top>"
  and push_correct: "c \<in> \<gamma>_stack b \<Longrightarrow> cx \<in> \<gamma>_word x \<Longrightarrow> (cx # c) \<in> \<gamma>_stack (push b x)"
  and pop_stack_correct:  "(cx # c) \<in> \<gamma>_stack b \<Longrightarrow> c \<in> \<gamma>_stack (fst (pop b))"
  and pop_return_correct: "(cx # c) \<in> \<gamma>_stack b \<Longrightarrow> cx \<in> \<gamma>_word (snd (pop b))"

end
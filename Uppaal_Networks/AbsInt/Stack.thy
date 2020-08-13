theory Stack
  imports Word ListLattice
begin

class absstack = bounded_semilattice_sup_bot + order_top

locale AbsStack =
  fixes \<gamma>_word :: "('a::absword) \<Rightarrow> int set" and
        \<gamma>_stack :: "('b::absstack) \<Rightarrow> stack set" and
        push :: "'b \<Rightarrow> ('a::absword) \<Rightarrow> 'b" and
        pop :: "'b \<Rightarrow> ('a * 'b)"
  assumes mono_gamma_stack: "a \<le> b \<Longrightarrow> \<gamma>_stack a \<le> \<gamma>_stack b"
  and gamma_Top[simp]: "\<gamma>_stack \<top> = \<top>"
  and push_correct: "c \<in> \<gamma>_stack b \<Longrightarrow> cx \<in> \<gamma>_word x \<Longrightarrow> (cx # c) \<in> \<gamma>_stack (push b x)"
  and pop_stack_correct:  "(cx # c) \<in> \<gamma>_stack b \<Longrightarrow> c \<in> \<gamma>_stack (snd (pop b))"
  and pop_return_correct: "(cx # c) \<in> \<gamma>_stack b \<Longrightarrow> cx \<in> \<gamma>_word (fst (pop b))"
begin

fun pop2 :: "'b \<Rightarrow> ('a * 'a * 'b)" where
  "pop2 stack =
    (let (a, astack) = pop stack;
         (b, bstack) = pop astack
    in (a, b, bstack))"
lemma pop2_stack_correct: "(ca # cb # c) \<in> \<gamma>_stack b \<Longrightarrow> c \<in> \<gamma>_stack (snd (snd (pop2 b)))"
  by (metis (no_types, lifting) Pair_inject case_prod_beta' pop2.elims pop_stack_correct prod.exhaust_sel)

lemma pop2_return_b_correct: "(ca # cb # c) \<in> \<gamma>_stack b \<Longrightarrow> cb \<in> \<gamma>_word (fst (snd (pop2 b)))"
proof -
  assume ass: "(ca # cb # c) \<in> \<gamma>_stack b"
  hence i: "(cb # c) \<in> \<gamma>_stack (snd (pop b))" using pop_stack_correct by simp
  have "snd (pop2 b) = pop (snd (pop b))"
    by (metis (no_types, lifting) case_prod_beta' pop2.elims prod.exhaust_sel snd_conv)
  from this i show "cb \<in> \<gamma>_word (fst (snd (pop2 b)))" using pop_return_correct by auto
qed

lemma pop2_return_a_correct: "(ca # cb # c) \<in> \<gamma>_stack b \<Longrightarrow> ca \<in> \<gamma>_word (fst (pop2 b))"
  by (metis (no_types, lifting) case_prod_beta' fst_conv pop2.elims pop_return_correct)

fun pop2_push :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'b" where
  "pop2_push f stack =
    (let (a, b, rstack) = pop2 stack
    in push rstack (f a b))"

lemma[simp]: "pop2_push f stack =
  push (snd (snd (pop2 stack))) (f (fst (pop2 stack)) (fst (snd (pop2 stack))))"
  by (simp add: case_prod_beta)

lemma pop2_push:
  assumes
    "\<And>x y a b. x \<in> \<gamma>_word a \<Longrightarrow> y \<in> \<gamma>_word b \<Longrightarrow> (cop x y) \<in> \<gamma>_word (f a b)"
    "a # b # rcstack \<in> \<gamma>_stack iastack"
  shows "(cop a b) # rcstack \<in> \<gamma>_stack (pop2_push f iastack)"
  apply (simp add: case_prod_beta Let_def)
  using assms by (meson pop_return_correct pop_stack_correct push_correct)
end

end
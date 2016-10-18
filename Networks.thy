theory Networks
  imports Timed_Automata
begin

section \<open>Networks of Timed Automata\<close>

subsection \<open>Syntax and Operational Semantics\<close>

text \<open>Input, output and internal transitions\<close>

datatype 'a act = In 'a | Out 'a | Sil 'a

type_synonym
  ('a, 'c, 't, 's) nta = "('a act, 'c, 't, 's) ta list"

inductive step_n ::
  "('a, 'c, 't, 's) nta \<Rightarrow> 's list \<Rightarrow> ('c, ('t::time)) cval
  \<Rightarrow> 's list \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile>\<^sub>N \<langle>_, _\<rangle> \<rightarrow> \<langle>_,_\<rangle>" [61,61,61] 61)
where
  step_n_t:
    "\<lbrakk>\<forall> p \<in> {..<length N}. N!p \<turnstile> \<langle>L!p, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>L!p, u \<oplus> d\<rangle>; d \<ge> 0\<rbrakk>
    \<Longrightarrow> N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow> \<langle>L, u \<oplus> d\<rangle>" |
  step_n_i:
    "\<lbrakk>
      N!p \<turnstile> l \<longrightarrow>\<^bsup>g,Sil a,r\<^esup> l'; u \<turnstile> g; \<forall> p \<in> {..<length N}. u' \<turnstile> inv_of (N!p) (L'!p);
      L!p = l; p < length L; L' = L[p := l']; u' = [r\<rightarrow>0]u
     \<rbrakk>
    \<Longrightarrow> N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow> \<langle>L', u'\<rangle>" |
  step_n_s:
    "\<lbrakk>N!p \<turnstile> l1 \<longrightarrow>\<^bsup>g1,In a,r1\<^esup> l1'; N!q \<turnstile> l2 \<longrightarrow>\<^bsup>g2,Out a,r2\<^esup> l2'; u \<turnstile> g1; u \<turnstile> g2;
      \<forall> p \<in> {..<length N}. u' \<turnstile> inv_of (N!p) (L'!p);
      L!p = l1; L!q = l2; p < length L; q < length L;
      L' = L[p := l1', q := l2']; u' = [(r1 @ r2)\<rightarrow>0]u
     \<rbrakk> \<Longrightarrow> N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow> \<langle>L', u'\<rangle>"

inductive_cases[elim!]: "N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow> \<langle>L', u'\<rangle>"

lemma step_n_t_I:
  "\<lbrakk>\<forall> p \<in> {..<length N}. u \<turnstile> inv_of (N!p) (L!p); \<forall> p \<in> {..<length N}. u \<oplus> d \<turnstile> inv_of (N!p) (L!p);
    d \<ge> 0
   \<rbrakk> \<Longrightarrow> N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow> \<langle>L, u \<oplus> d\<rangle>"
by (auto intro: step_n_t)

subsection \<open>Product Automaton\<close>

abbreviation state_set :: "('a, 'c, 'time, 's) transition set \<Rightarrow> 's set" where
  "state_set T \<equiv> fst ` T \<union> (snd o snd o snd o snd) ` T"

lemma guard_concat:
  assumes "\<forall> g \<in> set xs. u \<turnstile> g"
  shows "u \<turnstile> concat xs"
using assms by (induction xs) auto

lemma concat_guard:
  assumes "u \<turnstile> concat xs" "g \<in> set xs"
  shows "u \<turnstile> g"
using assms by (auto simp: list_all_iff)

context
  fixes N :: "('a, 'c, 't :: time, 's) nta"
begin

  abbreviation "T \<equiv> map trans_of N"
  abbreviation "I \<equiv> map inv_of N"

  definition "states = {L. length L = length T \<and> (\<forall> p \<in> {..<length T}. L!p \<in> state_set (T!p))}"

  definition
    "product_trans_i =
      {(L,g,a,r,L[p:=l']) | L p g a r l'. L \<in> states \<and> (L!p, g, Sil a, r, l') \<in> T!p \<and> p < length L}"

  definition
    "product_trans_s =
      {(L,g1 @ g2,a,r1 @ r2,L[p:=l1',q:=l2']) | L p q g1 g2 a r1 r2 l1' l2'.
        L \<in> states \<and> (L!p, g1, In a, r1, l1') \<in> T!p \<and> (L!q, g2, Out a, r2, l2') \<in> T!q
        \<and> p < length L \<and> q < length L
      }"

  definition
    "product_trans \<equiv> product_trans_i \<union> product_trans_s"

  definition "product_invariant L \<equiv> concat (map (\<lambda> p. (I!p) (L!p)) [0..<length L])"

  definition product_ta :: "('a, 'c, 't, 's list) ta" where 
    "product_ta \<equiv> (product_trans, product_invariant)"

  lemma product_invariantD:
    assumes "u \<turnstile> product_invariant L" "p < length N" "length L = length N"
    shows "u \<turnstile> inv_of (N ! p) (L!p)"
  using assms unfolding product_invariant_def by (force intro: concat_guard)

  (* Network + valid start state *)
  context
    fixes L :: "'s list"
    assumes len[simp]: "length L = length N"
        and states[intro]: "L \<in> states"
  begin

  lemma product_complete:
    assumes step: "N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow> \<langle>L', u'\<rangle>"
    shows "product_ta \<turnstile> \<langle>L, u\<rangle> \<rightarrow> \<langle>L', u'\<rangle>"
  using step proof cases
    case prems: (step_n_t d)
    from prems(3) have *:
      "\<forall>p\<in>{..<length N}. u \<turnstile> inv_of (N ! p) (L ! p)"
      "\<forall>p\<in>{..<length N}. u \<oplus> d \<turnstile> inv_of (N ! p) (L ! p)"
    by auto
    from prems(1,2,4) * show ?thesis
    by (fastforce simp add: product_ta_def inv_of_def product_invariant_def[abs_def]
                  intro!: guard_concat
       )
  next
    case prems: (step_n_i p l g a r l')
    from prems show ?thesis
     apply -
     apply (rule step_a; rule step_a.intros[where g = g and r = r and a = a])
    by (fastforce
        simp: product_trans_def product_trans_i_def product_invariant_def product_ta_def
              trans_of_def inv_of_def
        intro: guard_concat
       )+
  next
    case prems: (step_n_s p l1 g1 a r1 l1' q l2 g2 r2 l2')
    from prems show ?thesis
     apply -
     apply (rule step_a; rule step_a.intros[where g = "g1 @ g2" and a = a and r = "r1 @ r2"])
     subgoal premises prems
       apply 
         (auto simp add:
             product_trans_def product_trans_s_def product_invariant_def product_ta_def
             trans_of_def inv_of_def
         )
       apply (erule allE[where x = p])
       using \<open>p < _\<close> apply simp
       apply (erule allE[where x = q])
     using prems by (fastforce simp: trans_of_def)
    by (fastforce simp: product_invariant_def product_ta_def inv_of_def intro: guard_concat)+
  qed

  lemma inv_of_product[simp]:
    "inv_of product_ta = product_invariant"
  unfolding product_ta_def inv_of_def by simp

  lemma product_ta_cases:
    assumes "product_ta \<turnstile> L \<longrightarrow>\<^bsup>g,a,r\<^esup> L'"
    shows "(L, g, a, r, L') \<in> product_trans_i \<or> (L, g, a, r, L') \<in> product_trans_s"
  using assms unfolding product_ta_def trans_of_def product_trans_def by auto

  lemma product_sound:
    assumes step: "product_ta \<turnstile> \<langle>L, u\<rangle> \<rightarrow> \<langle>L', u'\<rangle>"
    shows "N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow> \<langle>L', u'\<rangle>"
  using assms proof cases
    case (step_t d)
    then show ?thesis by (auto intro!: step_n_t product_invariantD len)
  next
    case (step_a a)
    then show ?thesis
     apply cases
     apply simp
     apply (drule product_ta_cases)
     apply (erule disjE)
     unfolding product_trans_i_def product_trans_s_def
     apply (auto intro: product_invariantD intro!: step_n_i; fail)
    by (auto intro: product_invariantD intro!: step_n_s)
  qed

  end (* End context: network + valid start state *)

end (* End context for product TA definition *)

end (* End of theory *)
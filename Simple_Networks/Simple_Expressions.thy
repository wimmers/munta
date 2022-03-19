theory Simple_Expressions
  imports Main
begin

datatype ('a, 'b) bexp =
  true |
  not "('a, 'b) bexp" |
  "and" "('a, 'b) bexp" "('a, 'b) bexp" |
  or "('a, 'b) bexp" "('a, 'b) bexp" |
  imply "('a, 'b) bexp" "('a, 'b) bexp" | \<comment> \<open>Boolean connectives\<close>
  eq "('a, 'b) exp" "('a, 'b) exp" |
  le "('a, 'b) exp" "('a, 'b) exp" |
  lt "('a, 'b) exp" "('a, 'b) exp" |
  ge "('a, 'b) exp" "('a, 'b) exp" |
  gt "('a, 'b) exp" "('a, 'b) exp"
and ('a, 'b) exp =
  const 'b | var 'a | if_then_else "('a, 'b) bexp" "('a, 'b) exp" "('a, 'b) exp" |
  binop "'b \<Rightarrow> 'b \<Rightarrow> 'b" "('a, 'b) exp" "('a, 'b) exp" | unop "'b \<Rightarrow> 'b" "('a, 'b) exp"

inductive check_bexp :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a, 'b :: linorder) bexp \<Rightarrow> bool \<Rightarrow> bool" and is_val
  where
  "check_bexp s true True" |
  "check_bexp s (not e) (\<not> b)" if "check_bexp s e b" |
  "check_bexp s (and e1 e2) (a \<and> b)" if "check_bexp s e1 a" "check_bexp s e2 b" |
  "check_bexp s (or e1 e2) (a \<or> b)" if "check_bexp s e1 a" "check_bexp s e2 b" |
  "check_bexp s (imply e1 e2) (a \<longrightarrow> b)" if "check_bexp s e1 a" "check_bexp s e2 b" |
  "check_bexp s (eq a b) (x = v)" if "is_val s a v" "is_val s b x" |
  "check_bexp s (le a b) (v \<le> x)" if "is_val s a v" "is_val s b x" |
  "check_bexp s (lt a b) (v < x)" if "is_val s a v" "is_val s b x" |
  "check_bexp s (ge a b) (v \<ge> x)" if "is_val s a v" "is_val s b x" |
  "check_bexp s (gt a b) (v > x)" if "is_val s a v" "is_val s b x" |
  "is_val s (const c) c" |
  "is_val s (var x)   v" if "s x = Some v" |
  "is_val s (if_then_else b e1 e2) (if bv then v1 else v2)"
  if "is_val s e1 v1" "is_val s e2 v2" "check_bexp s b bv" |
  "is_val s (binop f e1 e2) (f v1 v2)" if "is_val s e1 v1" "is_val s e2 v2" |
  "is_val s (unop f e) (f v)" if "is_val s e v"

inductive_simps check_bexp_simps:
  "check_bexp s bexp.true bv"
  "check_bexp s (bexp.not b) bv"
  "check_bexp s (bexp.and b1 b2) bv"
  "check_bexp s (bexp.or b1 b2) bv"
  "check_bexp s (bexp.imply b1 b2) bv"
  "check_bexp s (le i x) bv"
  "check_bexp s (lt i x) bv"
  "check_bexp s (ge i x) bv"
  "check_bexp s (eq i x) bv"
  "check_bexp s (gt i x) bv"

inductive_simps is_val_simps:
  "is_val s (const c) d"
  "is_val s (var x) v"
  "is_val s (if_then_else b e1 e2) v"
  "is_val s (binop f e1 e2) v"
  "is_val s (unop f e) v"

inductive_cases check_bexp_elims:
  "check_bexp s bexp.true bv"
  "check_bexp s (bexp.not b) bv"
  "check_bexp s (bexp.and b1 b2) bv"
  "check_bexp s (bexp.or b1 b2) bv"
  "check_bexp s (bexp.imply b1 b2) bv"
  "check_bexp s (le i x) bv"
  "check_bexp s (lt i x) bv"
  "check_bexp s (ge i x) bv"
  "check_bexp s (eq i x) bv"
  "check_bexp s (gt i x) bv"

inductive_cases is_val_elims:
  "is_val s (const c) d"
  "is_val s (var x) v"
  "is_val s (if_then_else b e1 e2) v"
  "is_val s (binop f e1 e2) v"
  "is_val s (unop f e) v"



type_synonym
  ('a, 'b) upd = "('a * ('a, 'b) exp) list"

definition is_upd where
  "is_upd s upd s' \<equiv> \<exists>x e v. upd = (x, e) \<and> is_val s e v \<and> s' = s(x := Some v)" for upd

inductive is_upds where
  "is_upds s [] s" |
  "is_upds s (x # xs) s''" if "is_upd s x s'" "is_upds s' xs s''"

inductive_cases is_upds_NilE:
  "is_upds s [] s'"
and is_upds_ConsE:
  "is_upds s (e # es) s'"

inductive_simps is_upds_Nil_iff: "is_upds s [] s'"
  and is_upds_Cons_iff: "is_upds s (f # upds) s'"

lemma is_upds_appendI:
  assumes "is_upds s upds1 s'" "is_upds s' upds2 s''"
  shows "is_upds s (upds1 @ upds2) s''"
  using assms by induction (auto intro: is_upds.intros)

lemma is_upds_appendE:
  assumes "is_upds s (upds1 @ upds2) s''"
  obtains s' where "is_upds s upds1 s'" "is_upds s' upds2 s''"
  using assms by (induction upds1 arbitrary: s) (auto intro: is_upds.intros elim!: is_upds_ConsE)

lemma is_upds_NilD:
  "s' = s" if "is_upds s [] s'"
  using that by (rule is_upds_NilE)

lemma is_upds_all_NilD:
  assumes "is_upds s (concat upds) s'" "(\<forall>xs\<in>set upds. xs = [])"
  shows "s' = s"
  using assms by (simp del: Nil_eq_concat_conv flip: concat_eq_Nil_conv) (rule is_upds_NilD)

lemma is_upd_const_simp:
  "is_upd s (x, const c) s' \<longleftrightarrow> s' = s(x := Some c)"
  unfolding is_upd_def by (simp add: is_val_simps)

end
theory Expression_Simplification
  imports Simple_Network_Language Simple_Network_Language_Impl_Refine
begin

no_notation bot_assn ("false")
no_notation top_assn ("true")

abbreviation false where
  "false \<equiv> not bexp.true"

text \<open>
In the following we define constant propagation (simplification)
for Boolean (\<^term>\<open>true\<close>/\<^term>\<open>false\<close>) and arithmetic (\<^term>\<open>const\<close>) expressions.
\<close>

definition simp_and where
  "simp_and b1 b2 = (case (b1, b2) of
    (false, b) \<Rightarrow> false
  | (b, false) \<Rightarrow> false
  | (bexp.true, b) \<Rightarrow> b
  | (b, bexp.true) \<Rightarrow> b
  | (a,b) \<Rightarrow> and a b)"

definition simp_or where
  "simp_or b1 b2 = (case (b1, b2) of
    (false, b) \<Rightarrow> b
  | (b, false) \<Rightarrow> b
  | (bexp.true, b) \<Rightarrow> bexp.true
  | (b, bexp.true) \<Rightarrow> bexp.true
  | (a,b) \<Rightarrow> bexp.or a b)"

definition simp_imply where
  "simp_imply b1 b2 = (case (b1, b2) of
    (false, b) \<Rightarrow> bexp.true
  | (b, false) \<Rightarrow> not b
  | (bexp.true, b) \<Rightarrow> b
  | (b, bexp.true) \<Rightarrow> bexp.true
  | (a,b) \<Rightarrow> imply a b)"

fun simp_not where
  "simp_not (not x) = x"
| "simp_not x = not x"

fun simp_ite where
  "simp_ite bexp.true e1 e2 = e1"
| "simp_ite false e1 e2 = e2"
| "simp_ite b e1 e2 = if_then_else b e1 e2"

fun op_simp where
  "op_simp op f (const a) (const b) = (if f a b then bexp.true else false)"
| "op_simp op f a b = op a b"

fun binop_simp where
  "binop_simp f (const a) (const b) = const (f a b)"
| "binop_simp f a b = binop f a b"

fun unop_simp where
  "unop_simp f (const a) = const (f a)"
| "unop_simp f a = unop f a"

definition simp_var where
  "simp_var v_opt x = (
    case v_opt of
      None \<Rightarrow> var x
    | Some v \<Rightarrow> const v
  )"

lemma simp_var_eq_var:
  "simp_var (s x) y = var y" if "x \<notin> dom s"
  using that unfolding simp_var_def dom_def by (simp split: option.splits)

lemma simp_var_eq_var_domD:
  "x \<notin> dom s" if "simp_var (s x) y = var y"
  using that unfolding simp_var_def dom_def by (simp split: option.splits)

lemma simp_var_eq_const_domD:
  "x \<in> dom s" if "simp_var (s x) y = const c"
  using that unfolding simp_var_def dom_def by (simp split: option.splits)

fun bsimp :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a, 'b :: linorder) bexp \<Rightarrow> (_, _) bexp" and esimp where
  "bsimp _ bexp.true = bexp.true" |
  "bsimp s (not e) = simp_not (bsimp s e)" |
  "bsimp s (and e1 e2) = simp_and (bsimp s e1) (bsimp s e2)" |
  "bsimp s (bexp.or e1 e2) = simp_or (bsimp s e1) (bsimp s e2)" |
  "bsimp s (imply e1 e2) = simp_imply (bsimp s e1) (bsimp s e2)" |
  "bsimp s (eq i x) = op_simp eq (=) (esimp s i) (esimp s x)" |
  "bsimp s (le i x) = op_simp le (\<le>) (esimp s i) (esimp s x)" |
  "bsimp s (lt i x) = op_simp lt (<) (esimp s i) (esimp s x)" |
  "bsimp s (ge i x) = op_simp ge (\<ge>) (esimp s i) (esimp s x)" |
  "bsimp s (gt i x) = op_simp gt (>) (esimp s i) (esimp s x)"
| "esimp s (const c) = const c"
| "esimp s (var x)   = simp_var (s x) x"
| "esimp s (if_then_else b e1 e2) = simp_ite (bsimp s b) (esimp s e1) (esimp s e2)"
| "esimp s (binop f e1 e2) = binop_simp f (esimp s e1) (esimp s e2)"
| "esimp s (unop f e) = unop_simp f (esimp s e)"

lemmas check_bexp_basic_simps = check_bexp_simps

lemma simp_ex_neg:
  "(\<exists>b. vb = (\<not>b) \<and> P b) \<longleftrightarrow> P (\<not> vb)"
  by force

named_theorems check_bexp_simps

lemma check_bexp_not_not_simp [check_bexp_simps]:
  "check_bexp s (not (not b)) vb \<longleftrightarrow> check_bexp s b vb"
  by (induction b arbitrary: vb) (simp_all add: check_bexp_basic_simps simp_ex_neg)

lemma check_bexp_simp_not:
  "check_bexp s' (simp_not b) vb \<longleftrightarrow> check_bexp s' (not b) vb"
  by (cases b rule: simp_not.cases; simp add: check_bexp_simps)

lemma check_bexp_simp_and:
  "check_bexp s' (simp_and b1 b2) vb \<longleftrightarrow> check_bexp s' (and b1 b2) vb"
  apply (cases b1 and b2; simp add: check_bexp_simps)
  oops

lemma
  assumes "s \<subseteq>\<^sub>m s'"
  shows "check_bexp s' (bsimp s b) vb \<longleftrightarrow> check_bexp s' b vb"
    and "is_val s' (esimp s e) v \<longleftrightarrow> is_val s' e v"
  using assms
  thm bexp_exp.induct
   apply (induction b and e arbitrary: vb v)
  apply simp_all
  oops

lemma bval_simp_not:
  "bval s (simp_not b) = (\<not> bval s b)"
  by (cases b rule: simp_not.cases; simp)

lemma simp_and_alt_def:
  "simp_and b1 b2 = (
    if b1 = false then false
    else if b2 = false then false
    else if b1 = bexp.true then b2
    else if b2 = bexp.true then b1
    else and b1 b2
  )"
  by (simp add: simp_and_def split: bexp.split)

lemma simp_or_alt_def:
  "simp_or b1 b2 = (
    if b1 = false then b2
    else if b2 = false then b1
    else if b1 = bexp.true then bexp.true
    else if b2 = bexp.true then bexp.true
    else bexp.or b1 b2
  )"
  by (simp add: simp_or_def split: bexp.split)

lemma simp_imply_alt_def:
  "simp_imply b1 b2 = (
    if b1 = false then true
    else if b2 = false then not b1
    else if b1 = true then b2
    else if b2 = bexp.true then bexp.true
    else bexp.imply b1 b2
  )"
  by (simp add: simp_imply_def split: bexp.split)

lemma op_simp_alt_def:
  "op_simp op f e1 e2 = (
    if \<exists>a b. e1 = const a \<and> e2 = const b then (if f a b then true else false) else op e1 e2)"
  apply (cases e1; cases e2; simp)
  oops

abbreviation
  "is_const b \<equiv> (b = true \<or> b = false)"

lemma simp_and_cases:
  assumes
    "b1 = false \<Longrightarrow> P false"
    "b2 = false \<Longrightarrow> P false"
    "b1 = true  \<Longrightarrow> P b2"
    "b2 = true  \<Longrightarrow> P b1"
    "\<not> is_const b1 \<Longrightarrow> \<not> is_const b2 \<Longrightarrow> P (and b1 b2)"
  shows "P (simp_and b1 b2)"
  using assms by (simp add: simp_and_alt_def)

no_notation OR (infix "or" 60)

lemma simp_or_cases:
  assumes
    "b1 = false \<Longrightarrow> P b2"
    "b2 = false \<Longrightarrow> P b1"
    "b1 = true  \<Longrightarrow> P true"
    "b2 = true  \<Longrightarrow> P true"
    "\<not> is_const b1 \<Longrightarrow> \<not> is_const b2 \<Longrightarrow> P (or b1 b2)"
  shows "P (simp_or b1 b2)"
  using assms by (simp add: simp_or_alt_def)

lemma simp_imply_cases:
  assumes
    "b1 = false \<Longrightarrow> P true"
    "b2 = false \<Longrightarrow> b1 \<noteq> false \<Longrightarrow> P (not b1)"
    "b1 = true  \<Longrightarrow> P b2"
    "b2 = true  \<Longrightarrow> P true"
    "\<not> is_const b1 \<Longrightarrow> \<not> is_const b2 \<Longrightarrow> P (imply b1 b2)"
  shows "P (simp_imply b1 b2)"
  using assms by (simp add: simp_imply_alt_def)

lemma op_simp_cases:
  assumes
    "\<And>a b. e1 = const a \<Longrightarrow> e2 = const b \<Longrightarrow> f a b \<Longrightarrow> P true"
    "\<And>a b. e1 = const a \<Longrightarrow> e2 = const b \<Longrightarrow> \<not> f a b \<Longrightarrow> P false"
    "P (op e1 e2)"
  shows "P (op_simp op f e1 e2)"
  using assms by (cases "(op, f, e1, e2)" rule: op_simp.cases; simp)

lemma op_simp_eqE:
  assumes
    "op_simp op f e1 e2 = b'"
  obtains
    a b where "e1 = const a" "e2 = const b" "f a b" "b' = true" |
    a b where "e1 = const a" "e2 = const b" "\<not> f a b" "b' = false" | 
    "\<And>a b. e1 \<noteq> const a \<or> e2 \<noteq> const b" "b' = op e1 e2"
  using assms by (cases "(op, f, e1, e2)" rule: op_simp.cases; simp split: if_split_asm)

lemma simp_ite_cases:
  assumes
    "b = true  \<Longrightarrow> P e1"
    "b = false \<Longrightarrow> P e2"
    "P (if_then_else b e1 e2)"
  shows "P (simp_ite b e1 e2)"
  using assms by (cases "(b, e1, e2)" rule: simp_ite.cases; simp)

lemma binop_simp_cases:
  assumes
    "\<And>a b. e1 = const a \<Longrightarrow> e2 = const b \<Longrightarrow> P (const (f a b))"
    "P (binop f e1 e2)"
  shows "P (binop_simp f e1 e2)"
  using assms by (cases "(f, e1, e2)" rule: binop_simp.cases; simp)

lemma unop_simp_cases:
  assumes
    "\<And>a. e = const a \<Longrightarrow> P (const (f a))"
    "P (unop f e)"
  shows "P (unop_simp f e)"
  using assms by (cases "(f, e)" rule: unop_simp.cases; simp)

lemma simp_not_cases:
  assumes
    "\<And>b'. b = not b' \<Longrightarrow> P b'"
    "P (not b)"
  shows "P (simp_not b)"
  using assms by (cases b rule: simp_not.cases; simp)

lemma simp_var_cases:
  assumes "v_opt = None \<Longrightarrow> P (var x)" "\<And>v. v_opt = Some v \<Longrightarrow> P (const v)"
  shows "P (simp_var v_opt x)"
  using assms by (auto split: option.split simp: simp_var_def)

lemmas bsimp_esimp_cases =
  simp_not_cases simp_and_cases simp_or_cases simp_imply_cases
  op_simp_cases binop_simp_cases unop_simp_cases simp_ite_cases
  simp_var_cases

lemma
  assumes "s \<subseteq>\<^sub>m Some o s'"
  shows bval_bsimp: "bval s' (bsimp s b) = bval s' b"
    and eval_esimp: "eval s' (esimp s e) = eval s' e"
  apply (induction b and e)
  apply simp_all
  apply (all \<open>(rule bsimp_esimp_cases; simp; fail)?\<close>)
  \<comment> \<open>not,var\<close>
  using assms by - (rule bsimp_esimp_cases; force simp add: comp_def map_le_def dom_def)+

lemma
  shows vars_of_bsimp_subs: "vars_of_bexp (bsimp s b) \<subseteq> vars_of_bexp b"
    and vars_of_esimp_subs: "vars_of_exp (esimp s e) \<subseteq> vars_of_exp e"
  by (induction b and e) (simp; rule bsimp_esimp_cases; simp; fast)+

lemma
  shows bsimp_removes_vars: "vars_of_bexp (bsimp s b) \<inter> dom s = {}"
    and esimp_removes_vars: "vars_of_exp  (esimp s e) \<inter> dom s = {}"
  by (induction b and e) (simp; rule bsimp_esimp_cases; simp; fast)+

lemma
  assumes "s \<subseteq>\<^sub>m s'"
  shows check_bexp_bsimp_iff:
    "\<forall>x \<in> vars_of_bexp b. x \<in> dom s' \<Longrightarrow> check_bexp s' (bsimp s b) vb \<longleftrightarrow> check_bexp s' b vb"
    and is_val_esimp_iff:
    "\<forall>x \<in> vars_of_exp e. x \<in> dom s'  \<Longrightarrow> is_val     s' (esimp s e) v  \<longleftrightarrow> is_val     s' e v"
proof -
  have map_le' [simp]: "s \<subseteq>\<^sub>m Some o (the o s')"
    using assms by (auto simp: map_le_def dom_def)
  let ?b = "bsimp s b"
  assume A: \<open>\<forall>x\<in>vars_of_bexp b. x \<in> dom s'\<close>
  then have B:\<open>\<forall>x\<in>vars_of_bexp ?b. x \<in> dom s'\<close>
    using vars_of_bsimp_subs by fast
  from check_bexp_bval[OF A] check_bexp_bval[OF B]
  show \<open>check_bexp s' (bsimp s b) vb = check_bexp s' b vb\<close>
    by - (safe; drule (1) check_bexp_determ, simp add: bval_bsimp)
next
  have map_le' [simp]: "s \<subseteq>\<^sub>m Some o (the o s')"
    using assms by (auto simp: map_le_def dom_def)
  let ?e = "esimp s e"
  assume A: \<open>\<forall>x\<in>vars_of_exp e. x \<in> dom s'\<close>
  then have B:\<open>\<forall>x\<in>vars_of_exp ?e. x \<in> dom s'\<close>
    using vars_of_esimp_subs by fast
  from is_val_eval[OF A] is_val_eval[OF B] show \<open>is_val s' (esimp s e) v = is_val s' e v\<close>
    by - (safe; drule (1) is_val_determ, simp add: eval_esimp)
qed

lemma
  assumes "s \<subseteq>\<^sub>m s'"
  shows check_bexp_bsimpI': "check_bexp s' b vb \<Longrightarrow> check_bexp s' (bsimp s b) vb"
    and is_val_esimpI':     "is_val s' e v      \<Longrightarrow> is_val     s' (esimp s e) v"
proof (induction b and e arbitrary: vb and v)
  case (var x v)
  with assms show ?case
    \<comment> \<open>Odd case: handles the real ``semantic'' reasoning\<close>
    by - (simp; rule simp_var_cases; simp add: is_val_simps map_le_def dom_def)
next
  case (if_then_else b v1 v2 vb)
  then show ?case
    \<comment> \<open>Odd case: needs metis\<close>
    by - (simp; rule simp_ite_cases; simp add: check_bexp_basic_simps is_val_simps; metis)
next
  \<comment> 
   \<open>The remaining cases could all be handled the same way using @{thm bsimp_esimp_cases} but
    specifying the right rule is faster.
    This could be improved by a different unification algorithm or tagging.\<close>
  case not
  then show ?case
    by - (simp; rule simp_not_cases; simp add: check_bexp_basic_simps is_val_simps; fastforce)
next
  case ("and" b1 b2 vb)
  then show ?case
    by - (simp; rule simp_and_cases; simp add: check_bexp_basic_simps; fastforce)
next
  case (or b1 b2 vb)
  then show ?case
    by - (simp; rule simp_or_cases; simp add: check_bexp_basic_simps; fastforce)
next
  case (imply b1 b2 vb)
  then show ?case
    by - (simp; rule simp_imply_cases; simp add: check_bexp_basic_simps; fastforce)
qed (simp; rule bsimp_esimp_cases; simp add: check_bexp_basic_simps is_val_simps; fast)+

lemma simp_not_cases_strong:
  assumes
    "\<And>b'. b = not b' \<Longrightarrow> P b'"
    "\<forall>b'. b \<noteq> not b' \<Longrightarrow> P (not b)"
  shows "P (simp_not b)"
  using assms by (cases b rule: simp_not.cases; simp)

lemma
  assumes "s \<subseteq>\<^sub>m s'"
  notes [simp] = check_bexp_basic_simps is_val_simps
  shows check_bexp_bsimp_eq: "check_bexp s b vb \<Longrightarrow> bsimp s' b = (if vb then true else false)"
    and is_val_esimp_eq:     "is_val s e v      \<Longrightarrow> esimp s' e = const v"
proof (induction b and e arbitrary: vb and v)
  case ("and" x1 x2)
  then show ?case
    by (auto; simp add: simp_and_alt_def split: if_split_asm)
next
  case (or x1 x2)
  then show ?case
    by (auto; simp add: simp_or_alt_def split: if_split_asm)
next
  case (imply x1 x2)
  then show ?case
    by (auto; simp add: simp_imply_alt_def split: if_split_asm)
next
  case (var x)
  with assms show ?case
    by (auto simp: simp_var_def map_le_def dom_def)
qed auto

lemma
  assumes "s \<subseteq>\<^sub>m s'"
  shows check_bexp_bsimpI: "check_bexp s' b vb \<Longrightarrow> check_bexp (s' |` (dom s' - dom s)) (bsimp s b) vb"
    and is_val_esimpI:     "is_val s' e v      \<Longrightarrow> is_val     (s' |` (dom s' - dom s)) (esimp s e) v"
proof (induction b and e arbitrary: vb and v)
  case (var x v)
  with assms show ?case
    \<comment> \<open>Odd case: handles the real ``semantic'' reasoning\<close>
    by - (simp; rule simp_var_cases; simp add: is_val_simps map_le_def dom_def)
next
  case (if_then_else b v1 v2 vb)
  then show ?case
    \<comment> \<open>Odd case: needs metis\<close>
    by - (simp; rule simp_ite_cases; simp add: check_bexp_basic_simps is_val_simps; metis)
next
  \<comment> 
   \<open>The remaining cases could all be handled the same way using @{thm bsimp_esimp_cases} but
    specifying the right rule is faster.
    This could be improved by a different unification algorithm or tagging.\<close>
  case not
  then show ?case
    by - (simp; rule simp_not_cases; simp add: check_bexp_basic_simps is_val_simps; fastforce)
next
  case ("and" b1 b2 vb)
  then show ?case
    by - (simp; rule simp_and_cases; simp add: check_bexp_basic_simps; fastforce)
next
  case (or b1 b2 vb)
  then show ?case
    by - (simp; rule simp_or_cases; simp add: check_bexp_basic_simps; fastforce)
next
  case (imply b1 b2 vb)
  then show ?case
    by - (simp; rule simp_imply_cases; simp add: check_bexp_basic_simps; fastforce)
qed (simp; rule bsimp_esimp_cases; simp add: check_bexp_basic_simps is_val_simps; fast)+

lemma
  shows check_bexp_env_cong:
    "\<forall>x \<in> vars_of_bexp b. s x = s' x \<Longrightarrow> check_bexp s b vb \<longleftrightarrow> check_bexp s' b vb"
    and is_val_env_cong:
    "\<forall>x \<in> vars_of_exp e. s x = s' x  \<Longrightarrow> is_val s e v   \<longleftrightarrow> is_val s' e v"
  by (induction b and e arbitrary: vb and v) (simp_all add: check_bexp_basic_simps is_val_simps)

lemma check_bexp_restrict: "check_bexp s b vb \<longleftrightarrow> check_bexp (s |` vars_of_bexp b) b vb"
  and is_val_restrict:     "is_val s e v      \<longleftrightarrow> is_val     (s |` vars_of_exp e)  e v"
  by (intro check_bexp_env_cong is_val_env_cong; auto)+

fun bsimp' :: "(('a, 'b) bexp \<rightharpoonup> ('a, 'b) bexp) \<Rightarrow> ('a, 'b :: linorder) bexp \<Rightarrow> (_, _) bexp" where
  "bsimp' _ bexp.true = bexp.true" |
  "bsimp' I (not e) = simp_not (bsimp' I e)" |
  "bsimp' I (and e1 e2) = simp_and (bsimp' I e1) (bsimp' I e2)" |
  "bsimp' I (or e1 e2) = simp_or (bsimp' I e1) (bsimp' I e2)" |
  "bsimp' I (imply e1 e2) = simp_imply (bsimp' I e1) (bsimp' I e2)" |
  "bsimp' I b = (case I b of None \<Rightarrow> b | Some b' \<Rightarrow> b')"

fun atoms :: "('x, 'v :: linorder) bexp \<Rightarrow> (_, _) bexp set" where
  "atoms bexp.true = {}" |
  \<^cancel>\<open>"atoms false = {}" |\<close>
  "atoms (not b) = atoms b" |
  "atoms (and b1 b2) = (atoms b1 \<union> atoms b2)" |
  "atoms (or b1 b2) = (atoms b1 \<union> atoms b2)" |
  "atoms (imply b1 b2) = (atoms b1 \<union> atoms b2)" |
  "atoms e = {e}"

fun is_atom :: "('x, 'v :: linorder) bexp \<Rightarrow> bool" where
  "is_atom bexp.true = True" |
  "is_atom false = True" |
  "is_atom (not _) = False" |
  "is_atom (and e1 e2) = False" |
  "is_atom (bexp.or e1 e2) = False" |
  "is_atom (imply e1 e2) = False" |
  "is_atom _ \<longleftrightarrow> True"

lemma bsimp'_bsimp_eq:
  assumes "\<forall>b'.\<forall>b. I b = Some b' \<longrightarrow> bsimp s b = b'" "\<forall>b'\<in>atoms b. I b' = None \<longrightarrow> bsimp s b' = b'"
  shows "bsimp' I b = bsimp s b"
  using assms
proof (induction b rule: bsimp'.induct)
  case (1 I)
  then show ?case
    by simp
next
  case (2 I e)
  then show ?case
    by simp
next
  case ("6_1" I v va)
  let ?e = "eq v va"
  from "6_1" show ?case
    by (force split: option.split)
qed (simp; force split: option.split)+

inductive bexp_rel :: "
  (('x, 'v :: linorder) bexp \<Rightarrow> ('x1, 'v1 :: linorder) bexp \<Rightarrow> bool) \<Rightarrow>
  ('x, 'v :: linorder) bexp \<Rightarrow> ('x1, 'v1 :: linorder) bexp \<Rightarrow> bool" for R where
  "bexp_rel R true true"
| "bexp_rel R false false"
| "bexp_rel R (and b1 b2) (and b1' b2')" if "bexp_rel R b1 b1'" "bexp_rel R b2 b2'"
| "bexp_rel R (imply b1 b2) (imply b1' b2')" if "bexp_rel R b1 b1'" "bexp_rel R b2 b2'"
| "bexp_rel R (or b1 b2) (or b1' b2')" if "bexp_rel R b1 b1'" "bexp_rel R b2 b2'"
| "bexp_rel R (not b) (not b')" if "bexp_rel R b b'"
| "bexp_rel R b b'" if "is_atom b" "is_atom b'" "\<not> is_const b" "\<not> is_const b'" "R b b'"

inductive_cases bexp_rel_cases:
  "bexp_rel R true true"
  "bexp_rel R false false"
  "bexp_rel R (and b1 b2) (and b1' b2')"
  "bexp_rel R (imply b1 b2) (imply b1' b2')"
  "bexp_rel R (or b1 b2) (or b1' b2')"
  "bexp_rel R (not b) (not b')"

\<^cancel>\<open>inductive_cases bexp_rel_false_right_E0:
  "bexp_rel R b false"

inductive_cases bexp_rel_false_left_E0:
  "bexp_rel R false b"\<close>

inductive_cases bexp_rel_more_cases:
  "bexp_rel R b (not b')"
  "bexp_rel R (not b) b'"
  "bexp_rel R b true"
  "bexp_rel R true b"
  "bexp_rel R b false"
  "bexp_rel R false b"

lemma bexp_rel_false_rightE:
  assumes "bexp_rel R b false"
  obtains "b = false"
  using assms by (auto elim: bexp_rel_more_cases)

lemma bexp_rel_false_leftE:
  assumes "bexp_rel R false b"
  obtains "b = false"
  using assms by (auto elim: bexp_rel_more_cases)

lemma bexp_rel_true_rightE:
  assumes "bexp_rel R b true"
  obtains "b = true"
  using assms by (auto elim: bexp_rel_more_cases)

lemma bexp_rel_true_leftE:
  assumes "bexp_rel R true b"
  obtains "b = true"
  using assms by (auto elim: bexp_rel_more_cases)

lemmas bexp_rel_false_cases = bexp_rel_false_rightE bexp_rel_false_leftE

lemma bexp_rel_mono:
  "bexp_rel R' b1 b2" if "bexp_rel R b1 b2" "\<And>b1 b2. R b1 b2 \<Longrightarrow> R' b1 b2"
  using that by induction (auto intro: bexp_rel.intros)
  

thm bexp_rel_more_cases

theorem bsimp'_induct[case_names true not "and" or imply atom]:
  assumes "P bexp.true"
    and "\<And>e. P e \<Longrightarrow> P (bexp.not e)"
    and "\<And>e1 e2. P e1 \<Longrightarrow> P e2 \<Longrightarrow> P (bexp.and e1 e2)"
    and "\<And>e1 e2. P e1 \<Longrightarrow> P e2 \<Longrightarrow> P (bexp.or e1 e2)"
    and "\<And>e1 e2. P e1 \<Longrightarrow> P e2 \<Longrightarrow> P (bexp.imply e1 e2)"
    and "\<And>b. \<not> is_const b \<Longrightarrow> is_atom b \<Longrightarrow> P b"
  shows "P b"
  by (induction rule: bsimp'.induct; rule assms; (assumption | simp))

print_statement bsimp'.induct bsimp'_induct

lemma is_atom_bsimp:
  assumes "is_atom b"
  shows "is_atom (bsimp s b)"
  using assms by (cases b rule: is_atom.cases) (auto intro: op_simp_cases)

lemma is_atom_not:
  "is_atom (not b) \<longleftrightarrow> b = true"
  by (cases b; simp)

lemma bsimp'_bsimp_rel:
  assumes "\<forall>b'.\<forall>b. I b = Some b' \<longrightarrow> bsimp s b = b'"
    "\<forall>b'\<in>atoms b. I b' = None \<longrightarrow> R b' (bsimp s b')"
    "\<forall>b b'. R b b' \<longrightarrow> is_const b = is_const b'"
    "\<forall>b \<in> ran I. R b b"
  shows "bexp_rel R (bsimp' I b) (bsimp s b)"
  using assms(2)
proof (induction b rule: bsimp'_induct)
  case true
  then show ?case
    by simp rule
next
  case (not e)
  then show ?case
    supply [simp] = bexp_rel.intros is_atom_not
    by simp (rule simp_not_cases_strong; rule simp_not_cases_strong;
        simp; erule bexp_rel_more_cases; simp)
next
  case ("and" e1 e2)
  then show ?case
    apply simp
    apply (rule simp_and_cases)
    apply (auto simp add: simp_and_alt_def bexp_rel.intros elim: bexp_rel_more_cases bexp_rel_false_cases)
    done
next
  case (or e1 e2)
  then show ?case
    apply simp
    apply (rule simp_or_cases)
    apply (auto simp add: simp_or_alt_def bexp_rel.intros elim: bexp_rel_more_cases bexp_rel_false_cases)
    done
next
  case (imply e1 e2)
  then show ?case
    apply simp
    apply (rule simp_imply_cases)
    apply (auto simp add: simp_imply_alt_def bexp_rel.intros elim: bexp_rel_more_cases bexp_rel_false_cases)
    done
next
  case prems: (atom b)
  from \<open>is_atom b\<close> have "is_atom (bsimp s b)"
    by (rule is_atom_bsimp)
  from \<open>\<not> is_const _\<close> \<open>is_atom b\<close> have "b \<in> atoms b"
    by (cases b rule: is_atom.cases) auto
  show ?case
  proof (cases "I b")
    case None
    with prems \<open>b \<in> _\<close> have "R b (bsimp s b)"
      by auto
    from None \<open>is_atom b\<close> have "bsimp' I b = b"
      by (cases b rule: is_atom.cases) auto
    from \<open>\<not> is_const _\<close>  \<open>R b _\<close> assms(3) have "\<not> is_const (bsimp s b)"
        by blast
    with None \<open>is_atom b\<close> \<open>is_atom (bsimp _ _)\<close> \<open>R _ _\<close> \<open>bsimp' I b = b\<close> show ?thesis
      by (intro bexp_rel.intros) auto
  next
    case (Some b')
    with prems(1) assms(1) have "bsimp s b = b'"
      by blast
    moreover from Some \<open>is_atom b\<close> \<open>\<not> is_const b\<close> have "bsimp' I b = b'"
      by (cases b rule: is_atom.cases) auto
    moreover from Some prems(1) assms(4) have "R b' b'"
      unfolding ran_def by auto
    ultimately show ?thesis
      using \<open>is_atom (bsimp s b)\<close> by (cases "is_const b'") (auto intro: bexp_rel.intros)
  qed
qed

lemma bsimp_full_eval:
  assumes "vars_of_bexp b \<subseteq> dom s"
  shows "bsimp s b \<in> {true, false}"
  by (metis (no_types, lifting)
        assms check_bexp_bsimp_eq check_bexp_bval insert_iff map_le_def subset_iff)

context
  fixes clks :: "'x set" and vars :: "'x set"
begin

definition
  "all_vars = (clks \<union> vars)"

definition
  "is_uninterpreted bexp \<equiv> vars_of_bexp bexp \<subseteq> clks"

fun is_atom' :: "('x, 'v :: linorder) bexp \<Rightarrow> bool" where
  "is_atom' bexp.true = True" |
  "is_atom' false = True" |
  "is_atom' (not _) = False" |
  "is_atom' (and e1 e2) = False" |
  "is_atom' (bexp.or e1 e2) = False" |
  "is_atom' (imply e1 e2) = False" |
  \<^cancel>\<open>"is_atom' (eq i e) \<longleftrightarrow> \<^cancel>\<open>vars_of_exp e \<subseteq> clks\<close> vars_of_exp i \<subseteq> clks" |
  "is_atom' (le i e) \<longleftrightarrow> vars_of_exp i \<subseteq> clks" |
  "is_atom' (lt i e) \<longleftrightarrow> vars_of_exp i \<subseteq> clks" |
  "is_atom' (ge i e) \<longleftrightarrow> vars_of_exp i \<subseteq> clks" |
  "is_atom' (gt i e) \<longleftrightarrow> vars_of_exp i \<subseteq> clks"\<close>
  "is_atom' (eq (var x) e) \<longleftrightarrow> x \<in> clks \<and> vars_of_exp e \<subseteq> vars" |
  "is_atom' (le (var x) e) \<longleftrightarrow> x \<in> clks \<and> vars_of_exp e \<subseteq> vars" |
  "is_atom' (lt (var x) e) \<longleftrightarrow> x \<in> clks \<and> vars_of_exp e \<subseteq> vars" |
  "is_atom' (ge (var x) e) \<longleftrightarrow> x \<in> clks \<and> vars_of_exp e \<subseteq> vars" |
  "is_atom' (gt (var x) e) \<longleftrightarrow> x \<in> clks \<and> vars_of_exp e \<subseteq> vars" |
  "is_atom' _ = False"

definition
  "clk_atoms b = {b' \<in> atoms b. is_atom' b'}"

definition
  "assignments b \<equiv> {m. dom m = (atoms b - clk_atoms b) \<and> ran m \<subseteq> {true, false}}"

fun dest_conj :: "('x, 'v :: linorder) bexp \<Rightarrow> ('x, 'v) bexp list option" where
  "dest_conj (and b1 b2) = (case (dest_conj b1, dest_conj b2) of
    (Some bs1, Some bs2) \<Rightarrow> Some (bs1 @ bs2)
  | _ \<Rightarrow> None
  )"
| "dest_conj b = (if is_atom b then Some [b] else None)"

lemma dest_conj_all_atoms:
  assumes "dest_conj e = Some xs"
   shows "\<forall>x \<in> set xs. is_atom x"
  using assms
  by (induction e arbitrary: xs rule: dest_conj.induct) (auto split: option.splits if_splits)

lemma dest_conj_induct[consumes 1, case_names atom "and", induct pred: dest_conj]:
  assumes "dest_conj e = Some xs"
      and atom:  "\<And>b. is_atom b \<Longrightarrow> P b [b]"
      and "and":
        "\<And>b1 b2 bs1 bs2.
          P b1 bs1 \<Longrightarrow> P b2 bs2 \<Longrightarrow> dest_conj b1 = Some bs1 \<Longrightarrow> dest_conj b2 = Some bs2
        \<Longrightarrow> P (and b1 b2) (bs1 @ bs2)"
    shows "P e xs"
  using assms(1)
proof (induction e arbitrary: xs rule: dest_conj.induct)
  case (1 b1 b2)
  then show ?case
    using "and" by (auto split: option.split_asm)
qed (auto split: if_split_asm intro: atom)

lemma check_bexp_dest_conj_iff:
  assumes "dest_conj b = Some bs"
  shows "check_bexp s b vb \<longleftrightarrow> (\<exists>vbs. list_all2 (check_bexp s) bs vbs \<and> vb = list_all id vbs)"
  using assms
proof (induction arbitrary: vb)
  case (atom b)
  then show ?case
    by (auto simp: list_all2_Cons1)
next
  case ("and" b1 b2 bs1 bs2)
  show ?case
    by (clarsimp simp: list_all2_append1 check_bexp_basic_simps "and", safe)
       (metis list_all2_conv_all_nth list_all_append)+
qed

lemma check_bexp_bsimp_dest_conj_split:
  assumes "dest_conj (bsimp sv b) = Some bs" "\<forall>x \<in> vars_of_bexp b. x \<in> dom (sc ++ sv)"
  shows "check_bexp (sc ++ sv) b vb
    \<longleftrightarrow> (\<exists>vbs. list_all2 (check_bexp sc) bs vbs \<and> vb = list_all id vbs)" (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  from assms(2) have "check_bexp (sc ++ sv) b vb \<longleftrightarrow> check_bexp (sc ++ sv) (bsimp sv b) vb"
    by (intro check_bexp_bsimp_iff[symmetric]) auto
  also have "\<dots> \<longleftrightarrow> check_bexp sc (bsimp sv b) vb"
  proof (rule check_bexp_env_cong, safe)
    fix x :: 'x
    assume \<open>x \<in> vars_of_bexp (bsimp sv b)\<close>
    then show \<open>(sc ++ sv) x = sc x\<close>
      using bsimp_removes_vars[of sv b] by (cases "x \<in> dom sv") auto
  qed
  also from assms(1) have "\<dots> \<longleftrightarrow> ?rhs"
    by (rule check_bexp_dest_conj_iff)
  finally show ?thesis .
qed


fun is_conj :: "('x, 'v :: linorder) bexp \<Rightarrow> bool" where
  "is_conj (and b1 b2) = (is_conj b1 \<and> is_conj b2)"
| "is_conj b = is_atom b"

definition
  "is_guard b = (\<forall>m \<in> assignments b. dest_conj (bsimp' m b) \<noteq> None)"

lemma is_atom_is_conj:
  assumes "is_atom b"
  shows "is_conj b"
  using assms by (cases b; simp)

lemma is_conj_alt_def:
  "is_conj b \<longleftrightarrow> dest_conj b \<noteq> None"
  by (induction b; auto split: option.splits)

lemma bexp_rel_is_conj:
  assumes "bexp_rel (\<lambda>b b'. is_atom b \<longleftrightarrow> is_atom b') b b'"
  shows "is_conj b \<longleftrightarrow> is_conj b'"
  using assms
  by (induction) (auto intro: is_atom_is_conj elim: bexp_rel.cases simp: is_atom_not)

lemma is_atom'_is_atom:
  "is_atom b" if "is_atom' b"
  using that by (cases b rule: is_atom'.cases) auto

lemma not_is_const_bsimp_clk_atoms:
  "\<not> is_const (bsimp s b)" if "is_atom' b" "\<not> is_const b" "dom s \<inter> clks = {}"
  using that
  by (induction b rule: is_atom'.induct)
     (auto 4 4 dest: simp_var_eq_const_domD elim: op_simp_eqE)

definition
  "is_valid_atom b \<equiv> vars_of_bexp b \<subseteq> vars \<or> is_atom' b"

context
  fixes b :: "('x, 'a::linorder) bexp"
  assumes vars_of_b: "vars_of_bexp b \<subseteq> vars \<union> clks"
      and valid_atoms: "\<forall>b' \<in> atoms b. is_valid_atom b'"
begin

lemma vars_of_bexp_var_atoms':
  "vars_of_bexp b' \<subseteq> vars" if "b' \<in> atoms b" "\<not> is_atom' b'"
  using valid_atoms that unfolding is_valid_atom_def by auto

lemma vars_of_bexp_var_atoms:
  "vars_of_bexp b' \<subseteq> vars" if "b' \<in> atoms b" "b' \<notin> clk_atoms b"
  using valid_atoms that unfolding is_valid_atom_def clk_atoms_def by auto

lemma is_guard_ensures_conjunction:
  assumes "is_guard b" "vars \<subseteq> dom s" "dom s \<inter> clks = {}"
  shows "dest_conj (bsimp s b) \<noteq> None"
proof -
  define I where "I \<equiv> \<lambda>b'. if b' \<in> clk_atoms b \<or> b' \<notin> atoms b then None else Some (bsimp s b')"
  define R :: "('x, 'a) bexp \<Rightarrow> ('x, 'a) bexp \<Rightarrow> bool" where
    "R \<equiv> (\<lambda>b b'. is_atom b = is_atom b' \<and> is_const b = is_const b')"
  have "\<forall>b' b. I b = Some b' \<longrightarrow> bsimp s b = b'"
    unfolding I_def by simp
  have "I \<in> assignments b" \<comment> \<open>Discrete state atoms can be evaluated to consts\<close>
    unfolding assignments_def
    apply (auto simp: I_def split: if_split_asm simp: ran_def)
    apply (drule (1) vars_of_bexp_var_atoms, drule subset_trans[OF _ \<open>vars \<subseteq> _\<close>])
    apply (drule bsimp_full_eval)
    apply simp
    done
  with assms have "is_conj (bsimp' I b)"
    unfolding is_guard_def is_conj_alt_def[symmetric] by auto
  moreover have "bexp_rel R (bsimp' I b) (bsimp s b)"
    apply  (rule bsimp'_bsimp_rel)
  proof -
    show \<open>\<forall>b' b. I b = Some b' \<longrightarrow> bsimp s b = b'\<close>
      unfolding I_def by simp
  next
    from \<open>dom s \<inter> _ = {}\<close> show \<open>\<forall>b'\<in>atoms b. I b' = None \<longrightarrow> R b' (bsimp s b')\<close>
      \<comment> \<open>Clock atoms cannot be evaluated to consts\<close>
      by (simp add: R_def I_def clk_atoms_def is_atom_bsimp)
         (auto intro: is_atom_bsimp is_atom'_is_atom dest: not_is_const_bsimp_clk_atoms)
  next
    show \<open>\<forall>b b'. R b b' \<longrightarrow> is_const b = is_const b'\<close>
      unfolding R_def by safe
  next
    show \<open>\<forall>b\<in>ran I. R b b\<close>
      unfolding R_def by simp
  qed
  ultimately show ?thesis
    unfolding is_conj_alt_def[symmetric]
    by - (drule bexp_rel_is_conj[OF bexp_rel_mono], auto simp: R_def)
qed

lemma is_guard_ensures_conjunction':
  assumes "clks \<inter> vars = {}" "is_guard b" "dom s = vars"
  shows "dest_conj (bsimp s b) \<noteq> None"
  using assms by (intro is_guard_ensures_conjunction) auto

end

end

end
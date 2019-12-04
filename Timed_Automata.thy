theory Timed_Automata
  imports "TA_Library.Graphs"
begin

chapter \<open>Basic Definitions and Semantics\<close>

section \<open>Time\<close>

class time = linordered_ab_group_add +
  assumes dense: "x < y \<Longrightarrow> \<exists>z. x < z \<and> z < y"
  assumes non_trivial: "\<exists> x. x \<noteq> 0"

begin

lemma non_trivial_neg: "\<exists> x. x < 0"
proof -
  from non_trivial obtain x where "x \<noteq> 0" by auto
  then show ?thesis
  proof (cases "x < 0", auto, goal_cases)
    case 1
    then have "x > 0" by auto
    then have "(-x) < 0" by auto
    then show ?case by blast
  qed
qed

end

datatype ('c, 't) acconstraint =
  LT 'c 't |
  LE 'c 't |
  EQ 'c 't |
  GT 'c 't |
  GE 'c 't

type_synonym ('c, 't) cconstraint = "('c, 't) acconstraint list"

section \<open>Syntactic Definition\<close>

text \<open>
  For an informal description of timed automata we refer to Bengtsson and Yi \cite{BengtssonY03}.
  We define a timed automaton \<open>A\<close>
\<close>

type_synonym
  ('c, 'time, 's) invassn = "'s \<Rightarrow> ('c, 'time) cconstraint"

type_synonym
  ('a, 'c, 'time, 's) transition = "'s * ('c, 'time) cconstraint * 'a * 'c list * 's"

type_synonym
  ('a, 'c, 'time, 's) ta = "('a, 'c, 'time, 's) transition set * ('c, 'time, 's) invassn"

definition trans_of :: "('a, 'c, 'time, 's) ta \<Rightarrow> ('a, 'c, 'time, 's) transition set" where
  "trans_of \<equiv> fst"
definition inv_of  :: "('a, 'c, 'time, 's) ta \<Rightarrow> ('c, 'time, 's) invassn" where
  "inv_of \<equiv> snd"

abbreviation transition ::
  "('a, 'c, 'time, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, 'time) cconstraint \<Rightarrow> 'a \<Rightarrow> 'c list \<Rightarrow> 's \<Rightarrow> bool"
("_ \<turnstile> _ \<longrightarrow>\<^bsup>_,_,_\<^esup> _" [61,61,61,61,61,61] 61) where
  "(A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l') \<equiv> (l,g,a,r,l') \<in> trans_of A"

subsection \<open>Collecting Information About Clocks\<close>

fun constraint_clk :: "('c, 't) acconstraint \<Rightarrow> 'c"
where
  "constraint_clk (LT c _) = c" |
  "constraint_clk (LE c _) = c" |
  "constraint_clk (EQ c _) = c" |
  "constraint_clk (GE c _) = c" |
  "constraint_clk (GT c _) = c"

definition collect_clks :: "('c, 't) cconstraint \<Rightarrow> 'c set"
where
  "collect_clks cc \<equiv> constraint_clk ` set cc"

fun constraint_pair :: "('c, 't) acconstraint \<Rightarrow> ('c * 't)"
where
  "constraint_pair (LT x m) = (x, m)" |
  "constraint_pair (LE x m) = (x, m)" |
  "constraint_pair (EQ x m) = (x, m)" |
  "constraint_pair (GE x m) = (x, m)" |
  "constraint_pair (GT x m) = (x, m)"

definition collect_clock_pairs :: "('c, 't) cconstraint \<Rightarrow> ('c * 't) set"
where
  "collect_clock_pairs cc = constraint_pair ` set cc"

definition collect_clkt :: "('a, 'c, 't, 's) transition set \<Rightarrow> ('c *'t) set"
where
  "collect_clkt S = \<Union> {collect_clock_pairs (fst (snd t)) | t . t \<in> S}"

definition collect_clki :: "('c, 't, 's) invassn \<Rightarrow> ('c *'t) set"
where
  "collect_clki I = \<Union> {collect_clock_pairs (I x) | x. True}"

definition clkp_set :: "('a, 'c, 't, 's) ta \<Rightarrow> ('c *'t) set"
where
  "clkp_set A = collect_clki (inv_of A) \<union> collect_clkt (trans_of A)"

definition collect_clkvt :: "('a, 'c, 't, 's) transition set \<Rightarrow> 'c set"
where
  "collect_clkvt S = \<Union> {set ((fst o snd o snd o snd) t) | t . t \<in> S}"

abbreviation clk_set where "clk_set A \<equiv> fst ` clkp_set A \<union> collect_clkvt (trans_of A)"

(* We do not need this here but most other theories will make use of this predicate *)
inductive valid_abstraction
where
  "\<lbrakk>\<forall>(x,m) \<in> clkp_set A. m \<le> k x \<and> x \<in> X \<and> m \<in> \<nat>; collect_clkvt (trans_of A) \<subseteq> X; finite X\<rbrakk>
  \<Longrightarrow> valid_abstraction A X k"


section \<open>Operational Semantics\<close>

type_synonym ('c, 't) cval = "'c \<Rightarrow> 't"

definition cval_add :: "('c,'t) cval \<Rightarrow> 't::plus \<Rightarrow> ('c,'t) cval" (infixr "\<oplus>" 64)
where
  "u \<oplus> d = (\<lambda> x. u x + d)"

term list_all

inductive clock_val_a ("_ \<turnstile>\<^sub>a _" [62, 62] 62) where
  "\<lbrakk>u c < d\<rbrakk> \<Longrightarrow> u \<turnstile>\<^sub>a LT c d" |
  "\<lbrakk>u c \<le> d\<rbrakk> \<Longrightarrow> u \<turnstile>\<^sub>a LE c d" |
  "\<lbrakk>u c = d\<rbrakk> \<Longrightarrow> u \<turnstile>\<^sub>a EQ c d" |
  "\<lbrakk>u c \<ge> d\<rbrakk> \<Longrightarrow> u \<turnstile>\<^sub>a GE c d" |
  "\<lbrakk>u c > d\<rbrakk> \<Longrightarrow> u \<turnstile>\<^sub>a GT c d"

inductive_cases[elim!]: "u \<turnstile>\<^sub>a LT c d"
inductive_cases[elim!]: "u \<turnstile>\<^sub>a LE c d"
inductive_cases[elim!]: "u \<turnstile>\<^sub>a EQ c d"
inductive_cases[elim!]: "u \<turnstile>\<^sub>a GE c d"
inductive_cases[elim!]: "u \<turnstile>\<^sub>a GT c d"

declare clock_val_a.intros[intro]

definition clock_val :: "('c, 't) cval \<Rightarrow> ('c, 't::time) cconstraint \<Rightarrow> bool" ("_ \<turnstile> _" [62, 62] 62)
where
  "u \<turnstile> cc = list_all (clock_val_a u) cc"

fun clock_set :: "'c list \<Rightarrow> 't::time \<Rightarrow> ('c,'t) cval \<Rightarrow> ('c,'t) cval"
where
  "clock_set [] _ u = u" |
  "clock_set (c#cs) t u = (clock_set cs t u)(c:=t)"

abbreviation clock_set_abbrv :: "'c list \<Rightarrow> 't::time \<Rightarrow> ('c,'t) cval \<Rightarrow> ('c,'t) cval"
("[_\<rightarrow>_]_" [65,65,65] 65)
where
  "[r \<rightarrow> t]u \<equiv> clock_set r t u"

inductive step_t ::
  "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, 't) cval \<Rightarrow> ('t::time) \<Rightarrow> 's \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<rightarrow>\<^bsup>_\<^esup> \<langle>_, _\<rangle>" [61,61,61] 61)
where
  "\<lbrakk>u \<oplus> d \<turnstile> inv_of A l; d \<ge> 0\<rbrakk> \<Longrightarrow> A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l, u \<oplus> d\<rangle>"

declare step_t.intros[intro]

context
  notes step_t.cases[elim!] step_t.intros[intro!]
begin

lemma step_t_determinacy1:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l',u'\<rangle> \<Longrightarrow>  A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l'',u''\<rangle> \<Longrightarrow> l' = l''"
by auto

lemma step_t_determinacy2:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l',u'\<rangle> \<Longrightarrow>  A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l'',u''\<rangle> \<Longrightarrow> u' = u''"
by auto

lemma step_t_cont1:
  "d \<ge> 0 \<Longrightarrow> e \<ge> 0 \<Longrightarrow> A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l',u'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l', u'\<rangle> \<rightarrow>\<^bsup>e\<^esup> \<langle>l'',u''\<rangle>
  \<Longrightarrow> A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d+e\<^esup> \<langle>l'',u''\<rangle>"
proof -
  assume A: "d \<ge> 0" "e \<ge> 0" "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l',u'\<rangle>" "A \<turnstile> \<langle>l', u'\<rangle> \<rightarrow>\<^bsup>e\<^esup> \<langle>l'',u''\<rangle>"
  hence "u' = (u \<oplus> d)" "u'' = (u' \<oplus> e)" by auto
  hence "u'' = (u \<oplus> (d + e))" unfolding cval_add_def by auto
  with A show ?thesis by auto
qed

end (* End of context for aggressive elimination and intro rules *)

inductive step_a ::
  "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, ('t::time)) cval \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<rightarrow>\<^bsub>_\<^esub> \<langle>_, _\<rangle>" [61,61,61] 61)
where
  "\<lbrakk>A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'; u \<turnstile> g; u' \<turnstile> inv_of A l'; u' = [r \<rightarrow> 0]u\<rbrakk> \<Longrightarrow> (A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l', u'\<rangle>)"

inductive step ::
  "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, ('t::time)) cval \<Rightarrow> 's \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<rightarrow> \<langle>_,_\<rangle>" [61,61,61] 61)
where
  step_a: "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l',u'\<rangle> \<Longrightarrow> (A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>)" |
  step_t: "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l',u'\<rangle> \<Longrightarrow> (A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>)"

declare step.intros[intro]
declare step.cases[elim]

inductive
  steps :: "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, ('t::time)) cval \<Rightarrow> 's \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<rightarrow>* \<langle>_, _\<rangle>" [61,61,61] 61)
where
  refl: "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l, u\<rangle>" |
  step: "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l', u'\<rangle> \<rightarrow>* \<langle>l'', u''\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l'', u''\<rangle>"

declare steps.intros[intro]


section \<open>Contracting Runs\<close>

inductive step' ::
  "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, ('t::time)) cval \<Rightarrow> 's \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile>' \<langle>_, _\<rangle> \<rightarrow> \<langle>_, _\<rangle>" [61,61,61] 61)
where
  step': "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l', u'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l', u'\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l'', u''\<rangle> \<Longrightarrow> A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l'', u''\<rangle>"

lemmas step'[intro]

lemma step'_altI:
  assumes
    "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" "u \<oplus> d \<turnstile> g" "u \<oplus> d \<turnstile> inv_of A l" "0 \<le> d"
    "u' = [r \<rightarrow> 0](u \<oplus> d)" "u' \<turnstile> inv_of A l'"
  shows "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>"
  using assms by (auto intro: step_a.intros)

inductive
  steps' :: "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, ('t::time)) cval \<Rightarrow> 's \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile>' \<langle>_, _\<rangle> \<rightarrow>* \<langle>_, _\<rangle>" [61,61,61] 61)
where
  refl': "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>* \<langle>l, u\<rangle>" |
  step': "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle> \<Longrightarrow> A \<turnstile>' \<langle>l', u'\<rangle> \<rightarrow>* \<langle>l'', u''\<rangle> \<Longrightarrow> A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>* \<langle>l'', u''\<rangle>"

lemmas steps'.intros[intro]

lemma steps'_altI:
  "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>* \<langle>l'', u''\<rangle>" if "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>" "A \<turnstile>' \<langle>l', u'\<rangle> \<rightarrow> \<langle>l'', u''\<rangle>"
  using that by induction auto

lemma step_d_refl[intro]:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>0\<^esup> \<langle>l, u\<rangle>" if "u \<turnstile> inv_of A l"
proof -
  from that have "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>0\<^esup> \<langle>l, u \<oplus> 0\<rangle>" by - (rule step_t.intros; force simp: cval_add_def)
  then show ?thesis by (simp add: cval_add_def)
qed

lemma cval_add_simp:
  "(u \<oplus> d) \<oplus> d' = u \<oplus> (d + d')" for d d' :: "'t :: time"
  unfolding cval_add_def by auto

context
  notes [elim!]  = step'.cases step_t.cases
  and   [intro!] = step_t.intros
begin

lemma step_t_trans:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d + d'\<^esup> \<langle>l, u''\<rangle>" if "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l, u'\<rangle>" "A \<turnstile> \<langle>l, u'\<rangle> \<rightarrow>\<^bsup>d'\<^esup> \<langle>l, u''\<rangle>"
  using that by (auto simp add: cval_add_simp)

lemma steps'_complete:
  "\<exists> u'. A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>" if "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>" "u \<turnstile> inv_of A l"
  using that
proof (induction)
  case (refl A l u)
  then show ?case by blast
next
  case (step A l u l' u' l'' u'')
  then have "u' \<turnstile> inv_of A l'" by (auto elim: step_a.cases)
  from step(1) show ?case
  proof cases
    case (step_a a)
    with \<open>u \<turnstile> _\<close> \<open>u' \<turnstile> _\<close> step(3) show ?thesis by (auto 4 5)
  next
    case (step_t d)
    then have [simp]: "l' = l" by auto
    from step(3) \<open>u' \<turnstile> _\<close> obtain u0 where "A \<turnstile>' \<langle>l, u'\<rangle> \<rightarrow>* \<langle>l'', u0\<rangle>" by auto
    then show ?thesis
    proof cases
      case refl'
      then show ?thesis by blast
    next
      case (step' l1 u1)
      with step_t show ?thesis by (auto 4 7 intro: step_t_trans)
    qed
  qed
qed

lemma steps'_sound:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>" if "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>"
  using that by (induction; blast)

lemma steps_steps'_equiv:
  "(\<exists> u'. A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>) \<longleftrightarrow> (\<exists> u'. A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>)" if "u \<turnstile> inv_of A l"
  using that steps'_sound steps'_complete by metis

end (* End of context for aggressive elimination and intro rules *)


section \<open>Zone Semantics\<close>

type_synonym ('c, 't) zone = "('c, 't) cval set"

definition zone_delay :: "('c, ('t::time)) zone \<Rightarrow> ('c, 't) zone"
("_\<^sup>\<up>" [71] 71)
where
  "Z\<^sup>\<up> = {u \<oplus> d|u d. u \<in> Z \<and> d \<ge> (0::'t)}"

definition zone_set :: "('c, 't::time) zone \<Rightarrow> 'c list \<Rightarrow> ('c, 't) zone"
("_\<^bsub>_ \<rightarrow> 0\<^esub>" [71] 71)
where
  "zone_set Z r = {[r \<rightarrow> (0::'t)]u | u . u \<in> Z}"

lemma clock_set_set[simp]:
  "([r\<rightarrow>d]u) c = d" if "c \<in> set r"
  using that by (induction r) auto

lemma clock_set_id[simp]:
  "([r\<rightarrow>d]u) c = u c" if "c \<notin> set r"
  using that by (induction r) auto

datatype 'a action = Tau ("\<tau>") | Action 'a ("\<upharpoonleft>_")

inductive step_z ::
  "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, ('t::time)) zone \<Rightarrow> 'a action \<Rightarrow> 's \<Rightarrow> ('c, 't) zone \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto>\<^bsub>_\<^esub> \<langle>_, _\<rangle>" [61,61,61,61] 61)
where
  step_t_z:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l, Z\<^sup>\<up> \<inter> {u. u \<turnstile> inv_of A l}\<rangle>" |
  step_a_z:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l', zone_set (Z \<inter> {u. u \<turnstile> g}) r \<inter> {u. u \<turnstile> inv_of A l'}\<rangle>"
  if "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"

lemmas step_z.intros[intro]
inductive_cases step_t_z_E[elim]: "A \<turnstile> \<langle>l, u\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l', u'\<rangle>"
inductive_cases step_a_z_E[elim]: "A \<turnstile> \<langle>l, u\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l', u'\<rangle>"

subsection \<open>Zone Semantics for Compressed Runs\<close>

definition
  step_z' :: "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, ('t::time)) zone \<Rightarrow> 's \<Rightarrow> ('c, 't) zone \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto> \<langle>_, _\<rangle>" [61,61,61] 61)
where
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z''\<rangle> \<equiv> (\<exists> Z' a. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l, Z'\<rangle> \<and> A \<turnstile> \<langle>l, Z'\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l', Z''\<rangle>)"

abbreviation
  steps_z :: "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, ('t::time)) zone \<Rightarrow> 's \<Rightarrow> ('c, 't) zone \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto>* \<langle>_, _\<rangle>" [61,61,61] 61)
where
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l', Z''\<rangle> \<equiv> (\<lambda> (l, Z) (l', Z''). A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z''\<rangle>)\<^sup>*\<^sup>* (l, Z) (l', Z'')"

context
  notes [elim!]  = step.cases step'.cases step_t.cases step_z.cases
begin

lemma step_t_z_sound:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l',Z'\<rangle> \<Longrightarrow> \<forall> u' \<in> Z'. \<exists> u \<in> Z. \<exists> d.  A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l',u'\<rangle>"
  by (auto 4 5 simp: zone_delay_def zone_set_def)

lemma step_a_z_sound:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l',Z'\<rangle> \<Longrightarrow> \<forall> u' \<in> Z'. \<exists> u \<in> Z. \<exists> d.  A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l',u'\<rangle>"
  by (auto 4 4 simp: zone_delay_def zone_set_def intro: step_a.intros)

lemma step_z_sound:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l',Z'\<rangle> \<Longrightarrow> \<forall> u' \<in> Z'. \<exists> u \<in> Z.  A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>"
  by (auto 4 6 simp: zone_delay_def zone_set_def intro: step_a.intros)

lemma step_a_z_complete:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l', u'\<rangle> \<Longrightarrow> u \<in> Z \<Longrightarrow> \<exists> Z'. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l', Z'\<rangle> \<and> u' \<in> Z'"
  by (auto 4 4 simp: zone_delay_def zone_set_def elim!: step_a.cases)

lemma step_t_z_complete:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l', u'\<rangle> \<Longrightarrow> u \<in> Z \<Longrightarrow> \<exists> Z'. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l', Z'\<rangle> \<and> u' \<in> Z'"
  by (auto 4 4 simp: zone_delay_def zone_set_def elim!: step_a.cases)

lemma step_z_complete:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle> \<Longrightarrow> u \<in> Z \<Longrightarrow> \<exists> Z' a. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l', Z'\<rangle> \<and> u' \<in> Z'"
  by (auto 4 4 simp: zone_delay_def zone_set_def elim!: step_a.cases)

end (* End of context for aggressive elimination rules *)

lemma step_z_sound':
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l',Z'\<rangle> \<Longrightarrow> \<forall> u' \<in> Z'. \<exists> u \<in> Z.  A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>"
  unfolding step_z'_def by (fastforce dest!: step_t_z_sound step_a_z_sound)

lemma step_z_complete':
  "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle> \<Longrightarrow> u \<in> Z \<Longrightarrow> \<exists> Z'. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle> \<and> u' \<in> Z'"
  unfolding step_z'_def by (auto dest!: step_a_z_complete step_t_z_complete elim!: step'.cases)

lemma steps_z_sound:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l', Z'\<rangle> \<Longrightarrow> u' \<in> Z' \<Longrightarrow> \<exists> u \<in> Z. A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>"
  by (induction arbitrary: u' rule: rtranclp_induct2;
      fastforce intro: steps'_altI dest!: step_z_sound')

lemma steps_z_complete:
  "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<Longrightarrow> u \<in> Z \<Longrightarrow> \<exists> Z'. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l', Z'\<rangle> \<and> u' \<in> Z'"
  oops

lemma ta_zone_sim:
  "Simulation
    (\<lambda>(l, u) (l', u'). A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)
    (\<lambda>(l, Z) (l', Z''). A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z''\<rangle>)
    (\<lambda>(l, u) (l', Z). u \<in> Z \<and> l = l')"
  by standard (auto dest!: step_z_complete')

lemma steps'_iff:
  "(\<lambda>(l, u) (l', u'). A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)\<^sup>*\<^sup>* (l, u) (l', u') \<longleftrightarrow> A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>"
  apply standard
  subgoal
    by (induction rule: rtranclp_induct2; blast intro: steps'_altI)
  subgoal
    by (induction rule: steps'.induct; blast intro: converse_rtranclp_into_rtranclp)
  done

lemma steps_z_complete:
  "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<Longrightarrow> u \<in> Z \<Longrightarrow> \<exists> Z'. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l', Z'\<rangle> \<and> u' \<in> Z'"
  using Simulation.simulation_reaches[OF ta_zone_sim, of A "(l, u)" "(l', u')"]
  unfolding steps'_iff by auto

end (* Theory *)
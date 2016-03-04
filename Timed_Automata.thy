(* chapter {* Diagonal-free Timed Automata in Isabelle/HOL *} *)

section \<open>Diagonal-Free Timed Automata in Isabelle/HOL\<close>

(*<*)
theory Timed_Automata
  imports Main
begin
(*>*)
(*<*)
subsection \<open>Time\<close>

text \<open>
  Our basic formalizations of Timed Automata and DBMs are not strictly defined on reals
  as a time space. Instead we use a derived type class to model time
  (where \<open>linordered_ab_group_add\<close> is a type class for totally ordered abelian groups):
\<close>

class time = linordered_ab_group_add +
  assumes dense: "x < y \<Longrightarrow> \<exists>z. x < z \<and> z < y"
  assumes non_trivial: "\<exists> x. x \<noteq> 0"
(*>*)
(*<*)
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
(*>*)
(*<*)
datatype ('c, 't :: time) cconstraint =
  AND "('c, 't) cconstraint" "('c, 't) cconstraint" |
  LT 'c 't |
  LE 'c 't |
  EQ 'c 't |
  GT 'c 't |
  GE 'c 't
(*>*)
subsection \<open>Syntactic Definition\<close>

(*
text \<open>
  For instance, the constraint @{term "AND (LT c\<^sub>1 1) (EQ d\<^sub>2 2)"} postulates that @{term "c\<^sub>1"} is
  smaller than one and that @{term "c\<^sub>2"} is 2.
\<close>
*)

(*<*)
text \<open>\noindent
  \label{section:TimedAutomata}
  %For an informal description of timed automata we refer to Bengtsson and Yi \cite{kanade_timed_2004}.
  We define a timed automaton \<open>A\<close>
\<close>
(*>*)

(*<*)

type_synonym
  ('c, 'time, 's) invassn = "'s \<Rightarrow> ('c, 'time) cconstraint"

type_synonym
  ('a, 'c, 'time, 's) transition = "'s * ('c, 'time) cconstraint * 'a * 'c list * 's"

type_synonym
  ('a, 'c, 'time, 's) ta = "('a, 'c, 'time, 's) transition set * ('c, 'time, 's) invassn"

(*>*)

(*<*)

definition trans_of :: "('a, 'c, 'time, 's) ta \<Rightarrow> ('a, 'c, 'time, 's) transition set" where
  "trans_of \<equiv> fst"
definition inv_of  :: "('a, 'c, 'time, 's) ta \<Rightarrow> ('c, 'time, 's) invassn" where
  "inv_of \<equiv> snd"

abbreviation transition ::
  "('a, 'c, 'time, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, 'time) cconstraint \<Rightarrow> 'a \<Rightarrow> 'c list \<Rightarrow> 's \<Rightarrow> bool"
("_ \<turnstile> _ \<longrightarrow>\<^bsup>_,_,_\<^esup> _" [61,61,61,61,61,61] 61) where
  "(A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l') \<equiv> (l,g,a,r,l') \<in> trans_of A"

(*>*)

text \<open>
  Compared to, say DFAs, %say finite state-machines,
  timed automata introduce, in addition to the ideas of locations
  and transitions among them, a notion of clocks.
  We will fix a type @{typ "'c"} for the space of clocks, type @{typ "'t"} for time, and a type
  @{typ "'s"} for locations. While most of our formalizations only require @{typ "'t"} to belong
  to a custom type class for totally ordered dense abelian groups, we worked on the concrete
  type \<open>real\<close> for the region construction for simplicity.

  Locations and transitions are guarded with \<open>clock constraints\<close>, which have to be fulfilled to stay
  in a location or to transition among them.
  The following datatype models the variants of these constraints: @{datatype[display] cconstraint}
  We define a timed automaton \<open>A\<close> as a pair \<open>(T, I)\<close> where
  @{term[show_types] "I :: ('c, 't, 's) invassn"} is an assignment of clock invariants to locations;
  and \<open>T\<close> is a set of transitions written as @{term "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"} where
    \<^item> @{term[show_types] "l :: 's"} and @{term[show_types] "l' :: 's"} are start and successor location,
    \<^item> @{term[show_types] "a :: 'a"} is an action label,
    \<^item> and @{term[show_types] "r :: 'c list"} is a list of clocks that will be reset to zero
      when the transition is taken.

  \noindent
  Standard definitions of timed automata would include a fixed set of locations with designated a
  start location and a set of end locations. The language emptiness problem usually asks if any
  number of legal transitions can be taken to reach an end location from the start location.
  Thus we can confine ourselves to study reachability and implicitly assume the set of locations
  to be given by the transitions of the automaton.
  Note that although the definition of clocks constraints
  allows constants from the whole time space, we will later crucially restrict them to the natural
  numbers in order to obtain decidability.
\<close>

(*<*)
text \<open>
 as a quadruple \<open>(N, l\<^bsub>0\<^esub>, T, I)\<close> where:
  \begin{itemize}
    \item $N$ is a set of locations (or nodes) of type @{typ 's},
    \item \<open>l\<^bsub>0\<^esub> \<in> N\<close> is a single initial location,
    \item \<open>T\<close> is a set of transitions as defined below,
    %\item and \<open>I\<close> is function of type @{typ "'s \<Rightarrow> ('c, 'time) cconstraint"} assigning clock
    %      invariants to locations.
    \item and \<open>I\<close> is an assignment of clock invariants to locations.
  \end{itemize}
  Transitions are tuples of the form \<open>(l,g,a,r,l')\<close>
  of type @{typ "'s * ('c, 'time) cconstraint * 'a * 'c list * 's"},
  where $l$ and $l'$ are a start and a successor location, $a$ of type @{typ 'a} is an action label,
  $g$ is a clock constraint guarding the transition, and $r$ is a \textit{list} of clocks that will be reset
  when the transition is taken.
  We introduce the sugared notation @{term "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"} to denote that @{term "(l,g,a,r,l') \<in> T"}.
  %Locations are also often referred to as nodes and we will use the two terms interchangeably from now on.
  %We have not yet formalized the concept of clock constraints.
  %To do this, we define an inductive datatpe
  %@{typ "('c, 't) cconstraint"}
\<close>
(*>*)

(*<*)
subsubsection \<open>Collecting Information About Clocks\<close>

fun collect_clks :: "('c, 't :: time) cconstraint \<Rightarrow> 'c set"
where
  "collect_clks (AND cc1 cc2) = collect_clks cc1 \<union> collect_clks cc2" |
  "collect_clks (LT c _) = {c}" |
  "collect_clks (LE c _) = {c}" |
  "collect_clks (EQ c _) = {c}" |
  "collect_clks (GE c _) = {c}" |
  "collect_clks (GT c _) = {c}"

fun collect_clock_pairs :: "('c, 't :: time) cconstraint \<Rightarrow> ('c * 't) set"
where
  "collect_clock_pairs (LT x m) = {(x, m)}" |
  "collect_clock_pairs (LE x m) = {(x, m)}" |
  "collect_clock_pairs (EQ x m) = {(x, m)}" |
  "collect_clock_pairs (GE x m) = {(x, m)}" |
  "collect_clock_pairs (GT x m) = {(x, m)}" |
  "collect_clock_pairs (AND cc1 cc2) = (collect_clock_pairs cc1 \<union> collect_clock_pairs cc2)"

definition collect_clkt :: "('a, 'c, 't::time, 's) transition set \<Rightarrow> ('c *'t) set"
where
  "collect_clkt S = \<Union> {collect_clock_pairs (fst (snd t)) | t . t \<in> S}"

definition collect_clki :: "('c, 't :: time, 's) invassn \<Rightarrow> ('c *'t) set"
where
  "collect_clki I = \<Union> {collect_clock_pairs (I x) | x. True}"

definition clkp_set :: "('a, 'c, 't :: time, 's) ta \<Rightarrow> ('c *'t) set"
where
  "clkp_set A = collect_clki (inv_of A) \<union> collect_clkt (trans_of A)"

definition collect_clkvt :: "('a, 'c, 't::time, 's) transition set \<Rightarrow> 'c set"
where
  "collect_clkvt S = \<Union> {set ((fst o snd o snd o snd) t) | t . t \<in> S}"

abbreviation clk_set where "clk_set A \<equiv> fst ` clkp_set A \<union> collect_clkvt (trans_of A)"

(* We don not need this here but most other theories will make use of this predicate *)
inductive valid_abstraction
where
  "\<lbrakk>\<forall>(x,m) \<in> clkp_set A. m \<le> k x \<and> x \<in> X \<and> m \<in> \<nat>; collect_clkvt (trans_of A) \<subseteq> X; finite X\<rbrakk>
  \<Longrightarrow> valid_abstraction A X k"

(*>*)

subsection \<open>Operational Semantics\<close>

(*<*)
(* subsubsection \<open>Clock Valuations\<close> *)
(*>*)
(*<*)
type_synonym ('c, 't) cval = "'c \<Rightarrow> 't"
(*>*)
(*<*)
definition cval_add :: "('c,'t) cval \<Rightarrow> 't::time \<Rightarrow> ('c,'t) cval" (infixr "\<oplus>" 64)
where
  "u \<oplus> d = (\<lambda> x. u x + d)"
(*>*)
(*<*)
inductive clock_val :: "('c, 't) cval \<Rightarrow> ('c, 't::time) cconstraint \<Rightarrow> bool" ("_ \<turnstile> _" [62, 62] 62)
where
  "\<lbrakk>u \<turnstile> cc1; u \<turnstile> cc2\<rbrakk> \<Longrightarrow> u \<turnstile> AND cc1 cc2" |
  "\<lbrakk>u c < d\<rbrakk> \<Longrightarrow> u \<turnstile> LT c d" |
  "\<lbrakk>u c \<le> d\<rbrakk> \<Longrightarrow> u \<turnstile> LE c d" |
  "\<lbrakk>u c = d\<rbrakk> \<Longrightarrow> u \<turnstile> EQ c d" |
  "\<lbrakk>u c \<ge> d\<rbrakk> \<Longrightarrow> u \<turnstile> GE c d" |
  "\<lbrakk>u c > d\<rbrakk> \<Longrightarrow> u \<turnstile> GT c d"
(*>*)

(*<*)

declare clock_val.intros[intro]

inductive_cases[elim!]: "u \<turnstile> AND cc1 cc2"
inductive_cases[elim!]: "u \<turnstile> LT c d"
inductive_cases[elim!]: "u \<turnstile> LE c d"
inductive_cases[elim!]: "u \<turnstile> EQ c d"
inductive_cases[elim!]: "u \<turnstile> GE c d"
inductive_cases[elim!]: "u \<turnstile> GT c d"

fun clock_set :: "'c list \<Rightarrow> 't::time \<Rightarrow> ('c,'t) cval \<Rightarrow> ('c,'t) cval"
where
  "clock_set [] _ u = u" |
  "clock_set (c#cs) t u = (clock_set cs t u)(c:=t)"

abbreviation clock_set_abbrv :: "'c list \<Rightarrow> 't::time \<Rightarrow> ('c,'t) cval \<Rightarrow> ('c,'t) cval"
("[_\<rightarrow>_]_" [65,65,65] 65)
where
  "[r \<rightarrow> t]u \<equiv> clock_set r t u"

(*>*)

(*<*)

inductive step_t ::
  "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, 't) cval \<Rightarrow> ('t::time) \<Rightarrow> 's \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<rightarrow>\<^bsup>_\<^esup> \<langle>_, _\<rangle>" [61,61,61] 61)                      
where
  "\<lbrakk>u \<turnstile> inv_of A l; u \<oplus> d \<turnstile> inv_of A l; d \<ge> 0\<rbrakk> \<Longrightarrow> A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l, u \<oplus> d\<rangle>"

declare step_t.intros[intro!]

inductive_cases[elim!]: "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l',u'\<rangle>"

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

inductive_cases[elim!]: "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>"

(*>*)

text \<open>
  We want to define an operational semantics for timed automata via an inductive relation, as they
  are particularly enjoyable to work with in Isabelle/HOL.
  Compared to standard automata, states of timed automata are pairs of a location and
  a \<^emph>\<open>clock valuation\<close> of type @{typ  "'c \<Rightarrow> 't"} assigning time values to clocks.
  Time lapse is modeled by shifting a clock valuation \<open>u\<close> by a constant value \<open>d\<close>:
  @{thm cval_add_def}.
  Finally, we connect clock valuations and constraints by writing, for instance,
  \<open>u \<turnstile> AND (LT c\<^sub>1 1) (EQ c\<^sub>2 2)\<close> if \<open>u c\<^sub>1 < 1\<close> and \<open>u c\<^sub>2 = 2\<close>.

  Using these definitions, the operational semantics can be defined as relations between pairs of locations and clock
  valuations.
  %More specifically, we define \<^emph>\<open>action steps\<close>:
  %  @{thm [mode = Rule, show_types = false, show_sorts = false] step_a.intros};
  %and \<^emph>\<open>delay steps\<close>: %, written as @{term "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>t\<^esup> \<langle>l',u'\<rangle>"}, via
  %  @{thm [mode = Rule, show_types = false, show_sorts = false] step_t.intros}.
  More specifically, we define \<^emph>\<open>action steps\<close> via %, written as @{term "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l',u'\<rangle>"}, via
  \begin{center}
    @{thm [mode = Rule, show_types = false, show_sorts = false] step_a.intros}
  \end{center}
  and \<^emph>\<open>delay steps\<close> via %, written as @{term "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>t\<^esup> \<langle>l',u'\<rangle>"}, via
  \begin{center}
    @{thm [mode = Rule, show_types = false, show_sorts = false] step_t.intros}
  \end{center}\dotdot
  %Here @{term "inv_of A l"} denotes the invariant assigned to node $l$ in automaton $A$
  Here @{term[show_types = false] "inv_of (T, I) = I"}
  and the notation %@{term [show_types = true, show_sorts = false] "[r \<rightarrow> 0]u"}
  \<open>[r \<rightarrow> 0]u\<close> means that we update the clocks in \<open>r\<close> to \<open>0\<close> in \<open>u\<close>.
  %We use @{term "u \<turnstile> g"} to express that $u$ fulfills constraint $g$.
  % , while we leave the valuation $u$ untouched for the clocks outside of $r$.
  %Clocks assignments and constraints are related by another inductive relation:
    %{thm [display, names_short] clock_val.intros}
  We write @{term "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>"} if either @{term "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l',u'\<rangle>"} or
  @{term "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>t\<^esup> \<langle>l',u'\<rangle>"}.
\<close>

(*<*)
declare step.intros[intro]

inductive
  steps :: "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, ('t::time)) cval \<Rightarrow> 's \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<rightarrow>* \<langle>_, _\<rangle>" [61,61,61] 61)
where
  refl: "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l, u\<rangle>" |
  step: "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l', u'\<rangle> \<rightarrow>* \<langle>l'', u''\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l'', u''\<rangle>"

declare steps.intros[intro]

(*>*)

subsection \<open>Zone Semantics\<close>
(*<*)
type_synonym ('c, 't) zone = "('c, 't) cval set"
(*>*)
(*<*)

definition zone_delay :: "('c, ('t::time)) zone \<Rightarrow> ('c, 't) zone"
("_\<^sup>\<up>" [71] 71)
where
  "Z\<^sup>\<up> = {u \<oplus> d|u d. u \<in> Z \<and> d \<ge> (0::'t)}"

definition zone_set :: "('c, 't::time) zone \<Rightarrow> 'c list \<Rightarrow> ('c, 't) zone"
("_\<^bsub>_ \<rightarrow> 0\<^esub>" [71] 71)
where
  "zone_set Z r = {[r \<rightarrow> (0::'t)]u | u . u \<in> Z}"

(*>*)
text \<open>
  The first conceptual step to get from this abstract operational semantics towards concrete
  algorithms on DBMs is to consider \<^emph>\<open>zones\<close>. %, which are sets of valuations.
  Informally, the concept is simple; a zone is the set of clock valuations fulfilling a clock
  constraint: %(i.e. the solutions of a clock constraint):
  \<open>('c, 't) zone \<equiv> ('c \<Rightarrow> 't) set\<close>.
  This allows us to abstract from a concrete state \<open>\<langle>l, u\<rangle>\<close> to a pair of node and zone
  \<open>\<langle>l, Z\<rangle>\<close>. We need the following operations on zones:
  %\setlist[description]{font=\normalfont\ttfamily}
  %\begin{description}
  %  \isastyle
  %  \item[up:] @{thm zone_delay_def}
  %  \item[reset:] @{thm zone_set_def}
  %\end{description}
  \begin{description}
    \item[up:] @{thm[show_types = false, show_sorts = false] zone_delay_def}
    \item[reset:] @{thm[show_types = false, show_sorts = false] zone_set_def}
  \end{description}
\<close>
(*<*)
text \<open>
  \<^descr>\<^bold>\<open>up:\<close> @{thm[show_types = false, show_sorts = false] zone_delay_def}
  \<^descr>\<^bold>\<open>reset:\<close> @{thm[show_types = false, show_sorts = false] zone_set_def}
\<close>
(*>*)
(*<*)

inductive step_z ::
  "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, ('t::time)) zone \<Rightarrow> 's \<Rightarrow> ('c, 't) zone \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto> \<langle>_, _\<rangle>" [61,61,61] 61)
where
  step_t_z: "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l, (Z \<inter> {u. u \<turnstile> inv_of A l})\<^sup>\<up> \<inter> {u. u \<turnstile> inv_of A l}\<rangle>" |
  step_a_z: "\<lbrakk>A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'\<rbrakk>
              \<Longrightarrow> (A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', zone_set (Z \<inter> {u. u \<turnstile> g}) r \<inter> {u. u \<turnstile> inv_of A l'}\<rangle> )"

inductive_cases[elim!]: "A \<turnstile> \<langle>l, u\<rangle> \<leadsto> \<langle>l', u'\<rangle>"

declare step_z.intros[intro]

(*>*)

text \<open>\noindent
  Naturally, we define the operational semantics with zones by means of
  another inductive relation: %{thm [display] step_z.intros}
  \begin{center}
  @{thm [mode = Axiom] step_z.intros(1)} \\[1em]
  @{thm [mode = Rule] step_z.intros(2)} \\[1em]
  \end{center}
\<close>

(*<*)
lemma step_z_sound:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l',Z'\<rangle> \<Longrightarrow> (\<forall> u' \<in> Z'. \<exists> u \<in> Z.  A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>)"
proof (induction rule: step_z.induct, goal_cases)
  case 1 thus ?case unfolding zone_delay_def by blast
next
  case (2 A l g a r l' Z)
  show ?case
  proof
    fix u' assume "u' \<in> zone_set (Z \<inter> {u. u \<turnstile> g}) r \<inter> {u. u \<turnstile> inv_of A l'}"
    then obtain u where
      "u \<turnstile> g" "u' \<turnstile> inv_of A l'" "u' = [r\<rightarrow>0]u" "u \<in> Z"
    unfolding zone_set_def by auto
    with step_a.intros[OF 2 this(1-3)] show "\<exists>u\<in>Z. A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>" by fast
  qed
qed

lemma step_z_complete:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle> \<Longrightarrow> u \<in> Z \<Longrightarrow> \<exists> Z'. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle> \<and> u' \<in> Z'"
proof (induction rule: step.induct, goal_cases)
  case (1 A l u a l' u')
  then obtain g r
  where u': "u' = [r\<rightarrow>0]u" "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" "u \<turnstile> g" "[r\<rightarrow>0]u \<turnstile> inv_of A l'"
  by (cases rule: step_a.cases) auto
  hence "u' \<in> zone_set (Z \<inter> {u. u \<turnstile> g}) r \<inter> {u. u \<turnstile> inv_of A l'}"
  unfolding zone_set_def using \<open>u \<in> Z\<close> by blast
  with u'(1,2) show ?case by blast
next
  case (2 A l u d l' u')
  hence u': "u' = (u \<oplus> d)" "u \<turnstile> inv_of A l" "u \<oplus> d \<turnstile> inv_of A l" "0 \<le> d" and "l = l'" by auto
  with u' \<open>u \<in> Z\<close> have
    "u' \<in> {u'' \<oplus> d |u'' d. u'' \<in> Z \<inter> {u. u \<turnstile> inv_of A l} \<and> 0 \<le> d} \<inter> {u. u \<turnstile> inv_of A l}"
  by fastforce
  thus ?case using \<open>l = l'\<close>  step_t_z[unfolded zone_delay_def, of A l] by blast
qed

text \<open>
Corresponds to version in papers --
not strong enough for inductive proof over transitive closure relation.
\<close>
lemma step_z_complete1:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle> \<Longrightarrow> \<exists> Z. A \<turnstile> \<langle>l, {u}\<rangle> \<leadsto> \<langle>l', Z\<rangle> \<and> u' \<in> Z"
proof (induction rule: step.induct, goal_cases)
  case (1 A l u a l' u')
  then obtain g r
  where u': "u' = [r\<rightarrow>0]u" "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" "u \<turnstile> g" "[r\<rightarrow>0]u \<turnstile> inv_of A l'"
  by (cases rule: step_a.cases) auto
  hence "{[r\<rightarrow>0]u} = zone_set ({u} \<inter> {u. u \<turnstile> g}) r \<inter> {u. u \<turnstile> inv_of A l'}"
  unfolding zone_set_def by blast
  with u'(1,2) show ?case by auto 
next
  case (2 A l u d l' u')
  hence u': "u' = (u \<oplus> d)" "u \<turnstile> inv_of A l" "u \<oplus> d \<turnstile> inv_of A l" "0 \<le> d" and "l = l'" by auto
  hence "{u} = {u} \<inter> {u''. u'' \<turnstile> inv_of A l}" by fastforce 
  with u'(1) have "{u'} = {u'' \<oplus> d |u''. u'' \<in> {u} \<inter> {u''. u'' \<turnstile> inv_of A l}}" by fastforce
  with u' have
    "u' \<in> {u'' \<oplus> d |u'' d. u'' \<in> {u} \<inter> {u. u \<turnstile> inv_of A l} \<and> 0 \<le> d} \<inter> {u. u \<turnstile> inv_of A l}"
  by fastforce
  thus ?case using \<open>l = l'\<close> step_t_z[unfolded zone_delay_def, of A l "{u}"] by blast
qed

text \<open>
  Easier proof.
\<close>
lemma step_z_complete2:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle> \<Longrightarrow> \<exists> Z. A \<turnstile> \<langle>l, {u}\<rangle> \<leadsto> \<langle>l', Z\<rangle> \<and> u' \<in> Z"
using step_z_complete by fast

(*>*)

(*<*)

inductive
  steps_z :: "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, ('t::time)) zone \<Rightarrow> 's \<Rightarrow> ('c, 't) zone \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto>* \<langle>_, _\<rangle>" [61,61,61] 61)
where
  refl: "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l, Z\<rangle>" |
  step: "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>* \<langle>l'', Z''\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l'', Z''\<rangle>"

declare steps_z.intros[intro]

(* Soundness *)

text \<open>Abstain from quantifying u explicitly for ease of proof
Compare: {@text "A \<turnstile> \<langle>l, {u0}\<rangle> \<leadsto>* \<langle>l',Z\<rangle> \<Longrightarrow> (\<forall> u \<in> Z. A \<turnstile> \<langle>l, u0\<rangle> \<rightarrow>* \<langle>l',u\<rangle>)"}
Generalize from one starting sate for induction to work out.
Compare ease of proof to wpd-forte94-full.pdf
Alternation as explicit assumption?
\<close>

lemma steps_z_sound:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l', Z'\<rangle> \<Longrightarrow> u' \<in> Z' \<Longrightarrow> \<exists> u \<in> Z. A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>"
proof (induction A l _ l' _ arbitrary: rule: steps_z.induct, goal_cases)
  case refl thus ?case by fast
next
  case (step A l Z l' Z' l'' Z'')
  then obtain u'' where u'': "A \<turnstile> \<langle>l', u''\<rangle> \<rightarrow>* \<langle>l'',u'\<rangle>" "u'' \<in> Z'" by auto
  then obtain u where "u \<in> Z" "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u''\<rangle>" using step_z_sound[OF step(1)] by blast
  with u'' show ?case by blast
qed

lemma steps_z_complete:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<Longrightarrow> u \<in> Z \<Longrightarrow> \<exists> Z'. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l', Z'\<rangle> \<and> u' \<in> Z'"
proof (induction arbitrary: Z rule: steps.induct)
  case refl thus ?case by auto
next
  case (step A l u l' u' l'' u'' Z)
  from step_z_complete[OF this(1,4)] obtain Z' where Z': "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l',Z'\<rangle>" "u' \<in> Z'" by auto
  then obtain Z'' where "A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>* \<langle>l'',Z''\<rangle>" "u'' \<in> Z''" using step by metis
  with Z' show ?case by blast
qed

(*>*)

text \<open>\noindent
  %When we turn to the discussion of DBMs in \refSection{DBM}, we will implicitly show that the mentioned
  %zone operations really yield zones from zones, in the sense of solution sets of clock constraints.
  With the help of two easy inductive arguments one can show %that our zone abstracted semantics really
  %capture the right notion, i.e. the soundness and completeness of our semantics
  %the soundness and completeness of our semantics:
  soundness and completeness of this semantics \wrt the original semantics
  (where \<open>*\<close> is the \<^emph>\<open>Kleene star\<close> operator):
  % (using the Kleene star operation analogous to the above).
  \begin{description}%[font=\itshape]
    \item[(Soundness)] @{thm steps_z_sound}
    \item[(Completeness)] @{thm steps_z_complete}
  \end{description}
  %that this semantics is sound: \begin{center}@{thm steps_z_sound};\end{center}
  %and complete \wrt to the
  %original semantics: \begin{center}@{thm steps_z_complete}\end{center}\dotdot
  This is an example of where proof assistants really shine. Not only are our Isabelle proofs
  shorter to write down % XXX ADD in Isar + citation?
  than for example the proof given in \cite{{YiPD94}} --
  we have also found that the less general version given there (i.e. where @{term "Z = {u}"})
  yields an induction hypothesis
  that is not strong enough in the case of the completeness proof. This slight lapse is hard to detect
  in a human-written proof.
\<close>

(*<*)
end
(*>*)
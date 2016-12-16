theory UPPAAL_State_Networks
  imports State_Networks Normalized_Zone_Semantics UPPAAL_Asm_Clocks
begin

no_notation Ref.update ("_ := _" 62)
no_notation fun_rel_syn (infixr "\<rightarrow>" 60)

section \<open>Networks of Timed Automata with Shared State and UPPAAL-style Assembler guards and updates\<close>

subsection \<open>Syntax and Operational Semantics\<close>

text \<open>
  We formalize Networks of Timed Automata with integer variable state using UPPAAL-style
  guards and updates. The specification language for guards and updates is our formalization of
  the UPPAAL like Assembler language.
  We extend Networks of Timed Automata with arbitrary shared (global) state.
  Syntactically, this extension is very simple.
  We can just use the free action label slot to annotate edges with a guard
  and an update function on discrete states.
  The slightly more clumsy part is adding invariants for discrete states
  by directly specifying an invariant annotating function.
\<close>

type_synonym
  ('c, 'time, 's) invassn = "'s \<Rightarrow> ('c, 'time) cconstraint"

type_synonym
  ('a, 's) transition = "'s * addr * 'a * addr * 's"

type_synonym
  ('a, 'c, 'time, 's) uta = "('a, 's) transition set * ('c, 'time, 's) invassn"

type_synonym
  ('a, 'time, 's) unta =
  "'time programc \<times> ('a act, nat, 'time, 's) uta list \<times> ('s \<Rightarrow> addr) list \<times> (int * int) list"

term stepsc

definition
  "bounded bounds s \<equiv>
   length s = length bounds \<and> (\<forall> i < length s. fst (bounds ! i) < s ! i \<and> s ! i < snd (bounds ! i))"

inductive step_u ::
  "('a, 't :: time, 's) unta \<Rightarrow> nat \<Rightarrow> 's list \<Rightarrow> int list \<Rightarrow> (nat, 't) cval
  \<Rightarrow> 's list \<Rightarrow> int list \<Rightarrow> (nat, 't) cval \<Rightarrow> bool"
("_ \<turnstile>\<^sub>_ \<langle>_, _, _\<rangle> \<rightarrow> \<langle>_, _, _\<rangle>" [61,61,61,61,61,61] 61)
where
  step_u_t:
    "\<lbrakk>
      \<forall> p < length N. \<exists> pc st s' rs.
        stepst P n (u \<oplus> d) ((I ! p) (L ! p), [], s, True, []) (pc, st, s', True, rs);
      \<forall> p < length N. u \<turnstile> snd (N ! p) (L ! p);
      \<forall> p < length N. u \<oplus> d \<turnstile> snd (N ! p) (L ! p);
      d \<ge> 0;
      bounded B s
     \<rbrakk>
    \<Longrightarrow> (P, N, I, B) \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L, s, u \<oplus> d\<rangle>" |
  step_u_i:
    "\<lbrakk>
      stepst P n u (pc_g, [], s, True, []) (_, _, _, True, _);
      stepst P n u (pc_u, [], s, True, []) (_, _, s', _, r);
      \<forall> p < length N. \<exists> pc st s rs.
        stepst P n u' ((I ! p) (L' ! p), [], s', True, []) (pc, st, s, True, rs);
      (l, pc_g, Sil a, pc_u, l') \<in> fst (N ! p);
      \<forall> p < length N. u' \<turnstile> snd (N ! p) (L' ! p);
      L!p = l; p < length L; L' = L[p := l']; u' = [r\<rightarrow>0]u;
      bounded B s'
     \<rbrakk>
    \<Longrightarrow> (P, N, I, B) \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>" |
  step_u_s:
    "\<lbrakk>
      stepst P n u (pc_g1, [], s, True, []) (_, _, _, True, _);
      stepst P n u (pc_g2, [], s, True, []) (_, _, _, True, _);
      stepst P n u (pc_u2, [], s, True, []) (_, _, s1, _, r2);
      (* XXX UPPAAL semantics quirk *)
      ((\<exists> pc st s' f. stepst P n u (pc_u1, [], s, True, []) (pc, st, s', f, r1))
        \<or> (\<not> (\<exists> pc st s' f r'. stepst P n u (pc_u1, [], s, True, []) (pc, st, s', f, r')) \<and> r1 = []));
      stepst P n u (pc_u1, [], s1, True, []) ( _, _, s', _, _);
      (* stepst P n u (pc_u2, [], s1, True, []) ( _, _, s2, _, r2); *)
      \<forall> p < length N. \<exists> pc st s rs.
        stepst P n u' ((I ! p) (L' ! p), [], s', True, []) (pc, st, s, True, rs);
      (l1, pc_g1, In a, pc_u1, l1') \<in> fst (N ! p);
      (l2, pc_g2, Out a, pc_u2, l2') \<in> fst (N ! q);
      \<forall> p < length N. u' \<turnstile> snd (N ! p) (L' ! p);
      L!p = l1; L!q = l2; p < length L; q < length L; p \<noteq> q;
      L' = L[p := l1', q := l2']; u' = [(r1 @ r2)\<rightarrow>0]u;
      bounded B s'
     \<rbrakk> \<Longrightarrow> (P, N, I, B) \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"

inductive_cases[elim!]: "A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"

inductive steps_un ::
  "('a, 't :: time, 's) unta \<Rightarrow> nat \<Rightarrow> 's list \<Rightarrow> int list \<Rightarrow> (nat, 't) cval
  \<Rightarrow> 's list \<Rightarrow> int list \<Rightarrow> (nat, 't) cval \<Rightarrow> bool"
("_ \<turnstile>\<^sub>_ \<langle>_, _, _\<rangle> \<rightarrow>* \<langle>_, _, _\<rangle>" [61,61,61,61,61,61] 61)
where
  refl: "A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L, s, u\<rangle>" |
  step: "A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle> \<Longrightarrow> A \<turnstile>\<^sub>n  \<langle>L', s', u'\<rangle> \<rightarrow> \<langle>L'', s'', u''\<rangle>
        \<Longrightarrow> A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L'', s'', u''\<rangle>"

declare steps_un.intros[intro]

lemma stepI2:
  "A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L'', s'', u''\<rangle>" if
  "A \<turnstile>\<^sub>n \<langle>L', s', u'\<rangle> \<rightarrow>* \<langle>L'', s'', u''\<rangle>" "A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"
  using that
  apply induction
   apply rule
    apply (rule refl)
   apply assumption
  apply simp
  by (rule; assumption)

subsection \<open>Equivalent State Network Automaton\<close>

(*
abbreviation state_set :: "('a, 'c, 'time, 's) transition set \<Rightarrow> 's set" where
  "state_set T \<equiv> fst ` T \<union> (snd o snd o snd o snd) ` T"
*)

definition "stripp p \<equiv> map_option strip o p"
definition "stripfp p \<equiv> map_option stripf o p"
definition "striptp p \<equiv> map_option stript o p"

locale Equiv_TA_Defs =
  fixes A :: "('a, 't, 's) unta"
    and n :: nat -- "Fuel"
begin

abbreviation "N \<equiv> fst (snd A)"
abbreviation "P \<equiv> fst A"
abbreviation "I \<equiv> fst (snd (snd A))"
abbreviation "B \<equiv> snd (snd (snd A))"
abbreviation "P' \<equiv> stripfp P"
abbreviation "PF \<equiv> stripfp P"
abbreviation "PT \<equiv> striptp P"
definition "p \<equiv> length N"

term "((a, b), c)"

definition "make_f pc_u \<equiv> \<lambda> s.
  case (exec P' n (pc_u, [], s, True, []) []) of
    None \<Rightarrow> []
  | Some ((_, _, _, _, r), _) \<Rightarrow> r"

definition "make_mt pc_u \<equiv> \<lambda> s.
  case (exec PT n (pc_u, [], s, True, []) []) of
    None \<Rightarrow> None
  | Some ((_, _, s', _, r), _) \<Rightarrow> Some s'"

definition "make_mf pc_u \<equiv> \<lambda> s.
  case (exec PF n (pc_u, [], s, True, []) []) of
    None \<Rightarrow> None
  | Some ((_, _, s', _, r), _) \<Rightarrow> Some s'"

definition "make_c pc_g \<equiv> \<lambda> s.
  case (exec PT n (pc_g, [], s, True, []) []) of
    None \<Rightarrow> False
  | Some ((_, _, _, f, _), _) \<Rightarrow> f"

term map_filter

term P

definition "make_g pc_g \<equiv> \<lambda> s.
  case (exec PT n (pc_g, [], s, True, []) []) of
    None \<Rightarrow> []
  | Some ((_, _, _, _, _), pcs) \<Rightarrow>
      List.map_filter (\<lambda> pc.
        case P pc of
          Some (CEXP ac) \<Rightarrow> Some ac
        | _ \<Rightarrow> None
          )
        pcs"

definition "
  state_trans_t i \<equiv>
    {(l, make_g pc_g, (a, make_c pc_g, make_mf pc_u), make_f pc_u, l') | l a l' pc_g pc_u.
      (l, pc_g, a, pc_u, l') \<in> fst (N ! i)
    }
  "

  (*
definition "
  state_trans_f i \<equiv>
    {(l, \<lambda> i. [], (a, make_c pc_g, make_mf pc_u), make_f pc_u, l') | l a l' pc_g pc_u.
      (l, pc_g, a, pc_u, l') \<in> fst (N ! i)
    }
  "
*)

(* definition "state_trans i \<equiv> state_trans_f i \<union> state_trans_t i" *)

abbreviation "state_trans \<equiv> state_trans_t"

definition "
  state_pred i \<equiv> \<lambda> l s.
    case (exec P' n ((I ! i) l, [], s, True, []) []) of
      None \<Rightarrow> False
    | Some ((_, _, _, f, _), _) \<Rightarrow> f \<and> bounded B s
  "

definition "
  state_inv i \<equiv> snd (N ! i)
"

definition "
  state_ta \<equiv> (map (\<lambda> p. (state_trans p, state_inv p)) [0..<p], map state_pred [0..<p])
"

term state_ta

term Prod_TA_Defs

sublocale defs: Prod_TA_Defs state_ta .

end (* End of definitions locale *)

fun is_instr :: "'t instrc \<Rightarrow> bool" where
  "is_instr (INSTR _) = True" |
  "is_instr _ = False"

lemma step_stripf:
  assumes
    "is_instr cmd"
  shows
    "stepc cmd u (pc, st, s, f, rs) = step (stripf cmd) (pc, st, s, f, rs)"
proof (cases cmd)
  case (INSTR instr)
  with assms(1) show ?thesis
    by (cases instr) (auto split: option.split)
next
  case (CEXP x2)
  with assms show ?thesis by auto
qed

lemma step_stript:
  assumes
    "is_instr cmd"
  shows
    "stepc cmd u (pc, st, s, f, rs) = step (stript cmd) (pc, st, s, f, rs)"
proof (cases cmd)
  case (INSTR instr)
  with assms(1) show ?thesis
    by (cases instr) (auto split: option.split)
next
  case (CEXP x2)
  with assms show ?thesis by auto
qed

(* XXX Move? *)
lemmas [intro] = stepsc.intros

lemma stepsc_f_complete:
  assumes
    "stepsc P n' u start end"
    "\<And> pc' st s' f' rs cmd.
    stepsc P n' u start (pc', st, s', f', rs) \<Longrightarrow> P pc' = Some cmd
\<Longrightarrow> is_instr cmd"
  shows
    "steps (stripfp P) n' start end"
  using assms proof (induction P \<equiv> P n' u \<equiv> u x4 \<equiv> start "end" arbitrary: start rule: stepsc.induct)
    case 1
    then show ?case unfolding stripfp_def by auto
  next
    case (2 cmd pc st m f rs s n' s')
    have "is_instr cmd" if
      "stepsc P n' u s (pc', st, s', f', rs)" "P pc' = Some cmd" for pc' st s' f' rs cmd
      using 2(1,2) that by (auto intro: 2(5))
    with 2(4) have *: "steps (stripfp P) n' s s'" by auto
    show ?case
    proof (cases cmd)
      case (INSTR instr)
      with 2(1) step_stripf have
        "step (stripf cmd) (pc, st, m, f, rs) = Some s"
        by (auto split: option.split_asm)
      with 2(1-3) 2(5-) * show ?thesis unfolding stripfp_def by auto
    next
      case (CEXP ac)
      with 2 show ?thesis by fastforce
    qed
  qed

lemma stepsc_f_sound:
  assumes
    "steps (stripfp P) n' start end"
    "\<And> pc' st s' f' rs cmd.
    stepsc P n' u start (pc', st, s', f', rs) \<Longrightarrow> P pc' = Some cmd
    \<Longrightarrow> is_instr cmd"
  shows
    "stepsc P n' u start end"
using assms proof (induction "stripfp P" n' start "end")
  case (1 n start)
  then show ?case by auto
next
  case (2 instr pc st m f rs s n s')
  from 2(2) obtain cmd where "P pc = Some cmd" unfolding stripfp_def by auto
  show ?case
  proof (cases cmd)
    case prems: (INSTR instr)
    with \<open>P pc = _\<close> 2(2) step_stripf[of cmd, symmetric] 2(1) have step:
      "stepc cmd u (pc, st, m, f, rs) = Some s"
      unfolding stripfp_def by auto
    with \<open>P pc = _\<close> have "is_instr cmd" if
      "stepsc P n u s (pc', st, s', f', rs)" "P pc' = Some cmd" for pc' st s' f' rs cmd
      using that unfolding stripfp_def by (force intro: 2(5))
    with 2(4) have "stepsc P n u s s'" by auto
    with step \<open>P pc = _\<close> show ?thesis unfolding stripfp_def by auto
  next
    case prems: (CEXP ac)
    from \<open>P pc = _\<close> 2(5) have "is_instr cmd" by blast
    with prems show ?thesis by auto
  qed
qed

definition
  "time_indep P n start \<equiv>
    \<forall> pc' st s' f' rs cmd u.
      stepsc P n u start (pc', st, s', f', rs) \<and> P pc' = Some cmd
  \<longrightarrow> is_instr cmd"

lemma stepsc_t_complete:
  assumes
    "stepsc P n' u start end"
    "\<And> pc' st s' f' rs ac.
    stepsc P n' u start (pc', st, s', f', rs) \<Longrightarrow> P pc' = Some (CEXP ac) \<Longrightarrow> u \<turnstile>\<^sub>a ac"
  shows
    "steps (striptp P) n' start end"
  using assms proof (induction P \<equiv> P n' u \<equiv> u x4 \<equiv> start "end" arbitrary: start rule: stepsc.induct)
    case 1
    then show ?case unfolding stripfp_def by auto
  next
    case (2 cmd pc st m f rs s n' s')
    have "u \<turnstile>\<^sub>a ac" if
      "stepsc P n' u s (pc', st, s', f', rs)" "P pc' = Some (CEXP ac)" for pc' st s' f' rs ac
      using 2(1,2) that by (auto intro: 2(5))
    with 2(4) have *: "steps (striptp P) n' s s'" by auto
    show ?case
    proof (cases cmd)
      case (INSTR instr)
      with 2(1) step_stript have
        "step (stript cmd) (pc, st, m, f, rs) = Some s"
        by (auto split: option.split_asm)
      with 2(1-3) 2(5-) * show ?thesis unfolding striptp_def by auto
    next
      case (CEXP ac)
      with 2(1-3) have "u \<turnstile>\<^sub>a ac" by (auto intro: 2(5))
      with 2(1) have
        "step (stript cmd) (pc, st, m, f, rs) = Some s"
        using \<open>cmd = _\<close> by auto
      with 2(1-3) 2(5-) * show ?thesis unfolding striptp_def by auto
    qed
  qed

lemma stepsc_t_complete2:
  assumes
    "stepsc P n' u start (pc', st', s', f', rs')"
    "\<And> pc' st s' f' rs ac.
    stepsc P n' u start (pc', st, s', f', rs) \<Longrightarrow> P pc' = Some (CEXP ac) \<Longrightarrow> u \<turnstile>\<^sub>a ac"
  shows
    "steps (striptp P) n' start (pc', st', s', f', rs') \<and> (\<forall> ac. P pc' = Some (CEXP ac) \<longrightarrow> u \<turnstile>\<^sub>a ac)"
  using assms
  proof (induction P \<equiv> P n' u \<equiv> u x4 \<equiv> start "(pc', st', s', f', rs')" arbitrary: start rule: stepsc.induct)
    case 1
    then show ?case unfolding stripfp_def by blast
  next
    case (2 cmd pc st m f rs s n')
    have "u \<turnstile>\<^sub>a ac" if
      "stepsc P n' u s (pc', st, s', f', rs)" "P pc' = Some (CEXP ac)" for pc' st s' f' rs ac
      using 2(1,2) that by (auto intro: 2(5))
    with 2(4) have *:
      "steps (striptp P) n' s (pc', st', s', f', rs')" "\<forall>ac. P pc' = Some (CEXP ac) \<longrightarrow> u \<turnstile>\<^sub>a ac"
      by auto
    show ?case
    proof (cases cmd)
      case (INSTR instr)
      with 2(1) step_stript have
        "step (stript cmd) (pc, st, m, f, rs) = Some s"
        by (auto split: option.split_asm)
      with 2(1-3) 2(5-) * show ?thesis unfolding striptp_def by auto
    next
      case (CEXP ac)
      with 2(1-3) have "u \<turnstile>\<^sub>a ac" by (auto intro: 2(5))
      with 2(1) have
        "step (stript cmd) (pc, st, m, f, rs) = Some s"
        using \<open>cmd = _\<close> by auto
      with 2(1-3) 2(5-) * show ?thesis unfolding striptp_def by auto
    qed
  qed

lemma stepsc_t_visitedc:
  assumes
    "stepsc P n' u start end"
    "\<And> pc' st s' f' rs.
    stepsc P n' u start (pc', st, s', f', rs) \<Longrightarrow> Q pc'"
  shows "\<exists> pcs. visitedc P n' u start end pcs
  \<and> (\<forall> pc \<in> set pcs. Q pc)"
  using assms by (induction) (fastforce intro!: visitedc.intros)+

lemma visitedc_t_visited:
  assumes
    "visitedc P n' u start end pcs"
    "\<And> pc' ac. pc' \<in> set pcs \<Longrightarrow> P pc' = Some (CEXP ac) \<Longrightarrow> u \<turnstile>\<^sub>a ac"
  shows
    "visited (striptp P) n' start end pcs
  \<and> (\<forall> pc ac. pc' \<in> set pcs \<and> P pc' = Some (CEXP ac) \<longrightarrow> u \<turnstile>\<^sub>a ac)"
  using assms
  proof (induction P \<equiv> P n' u \<equiv> u x4 \<equiv> start "end" pcs arbitrary: start rule: visitedc.induct)
    case 1
    then show ?case by (auto intro: visited.intros)
  next
    case (2 cmd pc st m f rs s n' s' pcs)
    have "u \<turnstile>\<^sub>a ac" if
      "pc' \<in> set pcs" "P pc' = Some (CEXP ac)" for pc' ac
      using 2(1,2) that by (auto intro: 2(5))
    with 2(4) have *:
      "visited (striptp P) n' s s' pcs" "\<forall>pc ac. pc' \<in> set pcs \<and> P pc' = Some (CEXP ac) \<longrightarrow> u \<turnstile>\<^sub>a ac"
      by auto
    show ?case
    proof (cases cmd)
      case (INSTR instr)
      with 2(1) step_stript have
        "step (stript cmd) (pc, st, m, f, rs) = Some s"
        by (auto split: option.split_asm)
      with 2(1-3) 2(5-) * show ?thesis unfolding striptp_def by (auto intro: visited.intros)
    next
      case (CEXP ac)
      with 2(1-3) have "u \<turnstile>\<^sub>a ac" by (auto intro: 2(5))
      with 2(1) have
        "step (stript cmd) (pc, st, m, f, rs) = Some s"
        using \<open>cmd = _\<close> by auto
      with 2(1-3) 2(5-) * show ?thesis unfolding striptp_def by (auto intro: visited.intros)
    qed
  qed

lemma stepsc_t_sound:
  assumes
    "steps (striptp P) n' start end"
    "\<And> pc' st s' f' rs ac.
    stepsc P n' u start (pc', st, s', f', rs) \<Longrightarrow> P pc' = Some (CEXP ac) \<Longrightarrow> u \<turnstile>\<^sub>a ac"
  shows
    "stepsc P n' u start end"
using assms proof (induction "striptp P" n' start "end")
  case (1 n start)
  then show ?case by auto
next
  case (2 instr pc st m f rs s n s')
  from 2(2) obtain cmd where "P pc = Some cmd" unfolding striptp_def by auto
  show ?case
  proof (cases cmd)
    case prems: (INSTR instr)
    with \<open>P pc = _\<close> 2(2) step_stript[of cmd, symmetric] 2(1) have step:
      "stepc cmd u (pc, st, m, f, rs) = Some s"
      unfolding striptp_def by auto
    with \<open>P pc = _\<close> have "u \<turnstile>\<^sub>a ac" if
      "stepsc P n u s (pc', st, s', f', rs)" "P pc' = Some (CEXP ac)" for pc' st s' f' rs ac
      using that unfolding striptp_def by (force intro: 2(5))
    with 2(4) have "stepsc P n u s s'" by auto
    with step \<open>P pc = _\<close> show ?thesis unfolding striptp_def by auto
  next
    case prems: (CEXP ac)
    with \<open>P pc = _\<close> 2(2) have [simp]: "P pc = Some (CEXP ac)" by auto
    then have "u \<turnstile>\<^sub>a ac" by (auto intro: 2(5))
    with 2(2,1) \<open>cmd = _\<close> have step:
      "stepc cmd u (pc, st, m, f, rs) = Some s"
      unfolding striptp_def by auto
    with \<open>P pc = Some cmd\<close> have "u \<turnstile>\<^sub>a ac" if
      "stepsc P n u s (pc', st, s', f', rs)" "P pc' = Some (CEXP ac)" for pc' st s' f' rs ac
      using that unfolding striptp_def by (force intro: 2(5))
    with 2(4) have "stepsc P n u s s'" by auto
    with step \<open>P pc = Some cmd\<close> show ?thesis unfolding striptp_def by auto
  qed
qed

lemma stepsc_visitedc:
  "\<exists> cc. visitedc P n u start end cc" if "stepsc P n u start end"
  using that by induction (auto intro: visitedc.intros)

lemma visitedc_stepsc:
  "stepsc P n u start end" if "visitedc P n u start end cc"
  using that by (induction; blast)

lemma steps_visited:
  "\<exists> cc. visited P n start end cc" if "steps P n start end"
  using that by induction (auto intro: visited.intros)

lemma visited_steps:
  "steps P n start end" if "visited P n start end cc"
  using that by (induction; blast)

context
  fixes P n u start
  assumes constraints_conj: "\<forall> pc' st s' f' rs ac.
    stepsc P n u start (pc', st, s', f', rs) \<and> P pc' = Some (CEXP ac) \<longrightarrow> u \<turnstile>\<^sub>a ac"
begin

  lemma stepsc_t_sound':
    assumes
      "steps (striptp P) n start end"
    shows
      "stepsc P n u start end"
    using assms constraints_conj by (auto intro: stepsc_t_sound)

  lemma stepsc_t_complete':
    assumes
      "stepsc P n u start end"
    shows
      "steps (striptp P) n start end"
    using assms constraints_conj by (auto intro: stepsc_t_complete)

  lemma stepsc_t_complete'':
    assumes
      "stepsc P n u start end"
    shows
      "\<exists> pcs. visitedc P n u start end pcs \<and> (\<forall> pc \<in> set pcs. \<forall> ac. P pc = Some (CEXP ac) \<longrightarrow> u \<turnstile>\<^sub>a ac)"
    using assms constraints_conj by (auto intro: stepsc_t_complete stepsc_t_visitedc)

  lemma stepsc_t_visited:
    assumes
      "stepsc P n u start end"
    shows
      "\<exists> pcs. visited (striptp P) n start end pcs \<and> (\<forall> pc \<in> set pcs. \<forall> ac. P pc = Some (CEXP ac) \<longrightarrow> u \<turnstile>\<^sub>a ac)"
    using stepsc_t_complete''[OF assms] visitedc_t_visited by blast

  lemma stepst_t_complete:
    assumes
      "stepst P n u start end"
    shows
      "\<exists> pcs. exec (striptp P) n start [] = Some (end, pcs) \<and> (\<forall> pc \<in> set pcs. \<forall> ac. P pc = Some (CEXP ac) \<longrightarrow> u \<turnstile>\<^sub>a ac)"
      using assms by (auto dest!: stepsc_t_visited visited_exec' simp: striptp_def stepst_def)

  lemma stepst_t_equiv:
    "(\<exists> pcs'. exec (striptp P) n start pcs = Some ((pc, st, m, f, rs), pcs'))
    \<longleftrightarrow> stepst P n u start (pc, st, m, f, rs)"
    apply rule+
     apply safe
     apply (drule exec_steps)
    unfolding stepst_def
     apply safe
      apply (rule stepsc_t_sound'; assumption)
     apply (simp add: striptp_def)
     apply safe
    subgoal for z
      by (case_tac z) auto
    by (auto dest!: stepsc_t_complete' steps_exec simp: striptp_def)

end

context
  fixes P n start
  assumes time_indep: "time_indep P n start"
begin

  lemma time_indep':
    "\<And> pc' st s' f' rs cmd.
      stepsc P n u start (pc', st, s', f', rs) \<Longrightarrow> P pc' = Some cmd
  \<Longrightarrow> is_instr cmd"
    using time_indep unfolding time_indep_def by blast

  lemma stepsc_f_complete':
    assumes
      "stepsc P n u start end"
    shows
      "steps (stripfp P) n start end"
    using assms time_indep' by (auto intro: stepsc_f_complete[where P = P])

  lemma stepsc_f_sound':
    assumes
      "steps (stripfp P) n start end"
    shows
      "stepsc P n u start end"
    using assms time_indep' by (auto intro: stepsc_f_sound[where P = P])

  lemma stepsc_f_equiv:
    "steps (stripfp P) n start end \<longleftrightarrow> stepsc P n u start end"
    using stepsc_f_sound' stepsc_f_complete' by fast

  lemma stepst_f_equiv:
    "(\<exists> pcs'. exec (stripfp P) n start pcs = Some ((pc, st, m, f, rs), pcs'))
    \<longleftrightarrow> stepst P n u start (pc, st, m, f, rs)"
    apply rule+
     apply safe
     apply (drule exec_steps)
    unfolding stepst_def
     apply safe
      apply (rule stepsc_f_sound'; assumption)
     apply (simp add: stripfp_def)
     apply safe
    subgoal for z
      by (case_tac z) auto
    by (auto dest!: stepsc_f_complete' steps_exec simp: stripfp_def)

end (* End of context for equivalence *)

  term time_indep

    term "exec PT n (pc_g, [], s', True, []) [] = Some (s'', pcs)"

    thm steps_exec

lemma exec_acc:
  assumes "exec P n s pcs = Some (s', pcs')"
  shows "\<exists> pcs''. pcs' = pcs'' @ pcs"
  using assms
  sorry


lemma exec_min_steps:
  assumes "exec P n s pcs = Some (s', pcs' @ pcs)"
  shows "exec P (length pcs') s pcs = Some (s', pcs' @ pcs)"
using assms proof (induction n arbitrary: s pcs s' pcs')
  case 0
  then show ?case by auto
next
  case (Suc n)
  obtain pc st m f rs pc' st' m' f' rs' where [simp]:
    "s = (pc, st, m, f, rs)" "s' = (pc', st', m', f', rs')"
    using prod.exhaust by metis
  from Suc obtain instr where "P pc = Some instr" by (auto split: option.splits if_splits)
  show ?case
  proof (cases "instr = HALT")
    case True
    with \<open>P pc = _\<close> Suc show ?thesis by auto
  next
    case False
    with Suc.prems \<open>P pc = _\<close> obtain s'' where s'':
      "step instr s = Some s''" "exec P n s'' (pc # pcs) = Some (s', pcs' @ pcs)"
      by (auto split: option.splits)
    with exec_acc[OF this(2)] obtain pcs'' where "pcs' = pcs'' @ [pc]" by auto
    with Suc.IH[of s'' "pc # pcs" s' "pcs''"] \<open>P pc = _\<close> False s'' show ?thesis by auto
  qed
qed

lemma exec_steps_visited:
  assumes
    "exec P (length pcs') s pcs = Some (s', pcs' @ pcs)"
    "steps P (length pcs') s (pc, st, m, f, rs)"
  shows "pc \<in> set pcs'"
  using assms proof (induction P \<equiv> P "length pcs'" s pcs arbitrary: pc st m f rs pcs' rule: exec.induct)
  case 1
  then show ?case by simp
next
  case (2 n pc' st' m' f' rs' pcs pcs')
  from this(2)[symmetric] this(3) obtain instr where "P pc' = Some instr" by (cases "P pc'") auto
  show ?case
  proof (cases "instr = HALT")
    case True
    with "2.prems" \<open>P pc' = _\<close> \<open>Suc n = _\<close>[symmetric] show ?thesis by (force elim: steps.cases)
  next
    case False
    with 2 obtain pcs'' where "pcs' = pcs'' @ [pc']"
      apply atomize_elim
      apply (rule exec_acc)
        sorry
    with False 2 \<open>P pc' = _\<close> \<open>Suc n = _\<close>[symmetric] show ?thesis by (auto split: option.split_asm elim: steps.cases)
  qed
qed

lemma stepsc_mono:
  assumes "stepsc P n u start end" "n' \<ge> n"
  shows "stepsc P n' u start end"
  using assms proof (induction arbitrary: n')
  case (1 prog n u start)
  then show ?case by (cases n') auto
next
  case (2 cmd u pc st m f rs s prog n s')
  then show ?case by (cases n') auto
qed

lemma stepst_mono:
  assumes "stepst P n u start end" "n' \<ge> n"
  shows "stepst P n' u start end"
    using assms stepsc_mono unfolding stepst_def by blast

definition
  "state_indep P n \<equiv>
    \<forall> pc f pc' st f' rs u s1 s1' s2 s2' rs1 rs2.
      stepsc P n u (pc, st, s1, f, rs) (pc', st, s1', f', rs1) \<and>
      stepsc P n u (pc, st, s2, f, rs) (pc', st, s2', f', rs2)
  \<longrightarrow> rs1 = rs2"

locale Equiv_TA =
  Equiv_TA_Defs A n for A :: "('a, 't :: time, 's) unta" and n :: nat +
  fixes L :: "'s list" and s :: "int list" and u :: "(nat, 't) cval"
  assumes states[intro]: "L \<in> defs.states' s"
      (*
      and pred_time_indep:
      "\<forall> L' s' u' s''. \<forall> p' < p. \<forall> L'' \<in> defs.states' s''. A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>
    \<longrightarrow> time_indep P n ((I ! p') (L'' ! p'), [], s'', True, [])" *)
    and pred_time_indep:
      "\<forall> s. \<forall> L \<in> defs.states' s. \<forall> q < p. time_indep P n ((I ! q) (L ! q), [], s, True, [])"
    and upd_time_indep:
      "\<forall> l pc_g a l' pc_u s. \<forall> q < p. (l, pc_g, a, pc_u, l') \<in> fst (N ! q)
    \<longrightarrow> time_indep P n (pc_u, [], s, True, [])"
    and clock_conj:
      "\<forall> l pc_g a l' pc_u s u pc' st s' f' rs ac. \<forall> q < p. (l, pc_g, a, pc_u, l') \<in> fst (N ! q)
      \<and> stepsc P n u (pc_g, [], s, True, []) (pc', st, s', f', rs) \<and> P pc' = Some (CEXP ac) \<longrightarrow>
        u \<turnstile>\<^sub>a ac"
    (* Reset clocks may not depend on state. XXX *)
    (*
    and "\<forall> l pc_g a pc_u l'. (l, pc_g, In a, pc_u, l') \<in> fst (N ! q) \<longrightarrow> state_indep P pc_u"
    and "\<forall> l pc_g a pc_u l'. (l, pc_g, Out a, pc_u, l') \<in> fst (N ! q) \<longrightarrow> state_indep P pc_u"
    *)
  assumes Len: "length N = length I"
      and inv: "\<forall> q < p. \<exists> pc st s' rs pcs.
        exec P' n ((I ! q) (L ! q), [], s, True, []) [] = Some ((pc, st, s', True, rs), pcs)"
      and bounded: "bounded B s"
begin

lemma [simp]:
  "length defs.N = p"
  unfolding p_def state_ta_def by simp

lemma [simp]:
  "length defs.P = p"
  unfolding p_def state_ta_def by simp

lemma inv':
  "\<forall>p<length defs.P. (defs.P ! p) (L ! p) s"
  using inv bounded unfolding state_ta_def state_pred_def by (force simp: p_def)

lemma inv'':
  "\<exists> pc st s' rs. stepst P n u' ((I ! q) (L ! q), [], s, True, []) (pc, st, s', True, rs)"
  if "q < p" for u'
proof -
  from pred_time_indep that have "time_indep P n ((I ! q) (L ! q), [], s, True, [])" by blast
  with inv that stepst_f_equiv[symmetric] show ?thesis by blast
qed

lemma A_simp[simp]:
  "PP = P" "N' = N" "I' = I" "B' = B" if "A = (PP, N', I', B')"
using that by auto

lemma A_unfold:
  "A = (P, N, I, B)"
  by simp

sublocale prod: Prod_TA state_ta by standard (auto simp: inv')

lemma inv_simp:
  "snd (defs.N ! q) (L' ! q) = snd (N ! q) (L' ! q)" if "q < p" for L'
  using that unfolding state_ta_def state_inv_def by simp

lemma [simp]:
  "defs.p = p"
  by (simp add: defs.p_def p_def)

lemma [simp]:
  "(\<forall> x \<in> {..<m}. Q x) \<longleftrightarrow> (\<forall> x < m. Q x)"
  by auto

term "state_trans_f"

(*
lemma trans_state_taD:
  assumes "(l, g, (Sil a, c, m), f, l') \<in> fst (defs.N ! q)" "q < p"
  shows
    "(l, g, (Sil a, c, m), f, l') \<in> state_trans_f q \<or> (l, g, (Sil a, c, m), f, l') \<in> state_trans_t q"
  using assms unfolding state_ta_def state_trans_def by simp
*)

lemma trans_state_taD:
  assumes "(l, g, (a, c, m), f, l') \<in> fst (defs.N ! q)" "q < p"
  shows
    "(l, g, (a, c, m), f, l') \<in> state_trans_t q"
  using assms unfolding state_ta_def by simp

lemma N_transD:
  assumes "(l, pc_g, a, pc_u, l') \<in> fst (N ! q)" "q < p"
  shows "(l, make_g pc_g, (a, make_c pc_g, make_mf pc_u), make_f pc_u, l') \<in> fst (defs.N ! q)"
    using assms unfolding state_ta_def state_trans_t_def by auto

lemma pred_time_indep':
  "\<forall> L' s' u'. \<forall> p' < p. A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>
\<longrightarrow> time_indep P n ((I ! p') (L' ! p'), [], s', True, [])"
  using pred_time_indep oops

lemma P_steps_upd:
  assumes
    "Some s'' = make_mf pc_u s'"
    "q < p" "(l, pc_g, a, pc_u, l') \<in> fst (N ! q)"
  shows
    "\<exists> pc st f. stepst P n u' (pc_u, [], s', True, []) (pc, st, s'', f, make_f pc_u s')"
proof -
  from assms upd_time_indep have *: "time_indep P n (pc_u, [], s', True, [])" by auto
  from assms(1) \<open>q < p\<close> obtain pc st f rs pcs where
    "exec PF n (pc_u, [], s', True, []) [] = Some ((pc, st, s'', f, rs), pcs)"
    unfolding make_mf_def state_ta_def by (fastforce split: option.splits)
  with stepst_f_equiv[OF *] show ?thesis unfolding make_f_def by fastforce
qed

lemma P_steps_reset:
  assumes
    "q < p" "(l, pc_g, a, pc_u, l') \<in> fst (N ! q)"
  shows
    "(\<exists>pc st s'' f. stepst P n u (pc_u, [], s', True, []) (pc, st, s'', f, make_f pc_u s')) \<or>
       (\<nexists>pc st s'' f r'. stepst P n u (pc_u, [], s', True, []) (pc, st, s'', f, r')) \<and>
       make_f pc_u s' = []"
  using assms sorry

lemma steps_P_reset:
  assumes
    "(\<exists>pc st s'' f. stepst P n u (pc_u, [], s', True, []) (pc, st, s'', f, r)) \<or>
     (\<nexists>pc st s'' f r'. stepst P n u (pc_u, [], s', True, []) (pc, st, s'', f, r')) \<and> r = []"
  shows "make_f pc_u s' = r"
    using assms sorry

lemma steps_P_upd:
  assumes
    "stepst P n u' (pc_u, [], s', True, []) (pc, st, s'', f, r)"
    "q < p" "(l, pc_g, a, pc_u, l') \<in> fst (N ! q)"
  shows
    "Some s'' = make_mf pc_u s'" (is "?A") "r = make_f pc_u s'" (is "?B")
proof -
  from assms upd_time_indep have "time_indep P n (pc_u, [], s', True, [])" by auto
  from stepst_f_equiv[OF this, symmetric] assms(1) \<open>q < p\<close> obtain pc st f pcs where
    "exec PF n (pc_u, [], s', True, []) [] = Some ((pc, st, s'', f, r), pcs)"
    unfolding make_mf_def state_ta_def by (fastforce split: option.splits)
  then show ?A ?B unfolding make_f_def make_mf_def by (auto split: option.split)
qed

lemma steps_P_guard:
  assumes
    "stepst P n u' (pc_g, [], s', True, []) (pc, st, s'', True, rs)"
    "q < p" "(l, pc_g, a, pc_u, l') \<in> fst (N ! q)"
  shows
    "make_c pc_g s'" (is "?A") "u' \<turnstile> make_g pc_g s'" (is "?B")
proof -
  from stepst_t_complete[OF _ assms(1)] clock_conj assms(2-) obtain pcs where
    "exec PT n (pc_g, [], s', True, []) [] = Some ((pc, st, s'', True, rs), pcs)"
    "\<forall> pc\<in>set pcs. \<forall>ac. P pc = Some (CEXP ac) \<longrightarrow> u' \<turnstile>\<^sub>a ac"
    by auto
  then show ?A ?B unfolding make_c_def make_g_def
    by (auto split: option.split instrc.split_asm simp: list_all_iff set_map_filter intro!: clock_val.intros)
qed

lemma P_steps_guard:
  assumes
    "make_c pc_g s'" "u' \<turnstile> make_g pc_g s'"
    "q < p" "(l, pc_g, a, pc_u, l') \<in> fst (N ! q)"
  shows
    "\<exists> pc s'' st rs. stepst P n u' (pc_g, [], s', True, []) (pc, st, s'', True, rs)"
proof -
  from assms(1) \<open>q < p\<close> obtain pc st s'' rs pcs where *:
    "exec PT n (pc_g, [], s', True, []) [] = Some ((pc, st, s'', True, rs), pcs)"
    unfolding make_c_def state_ta_def by (fastforce split: option.splits)
  with assms(2) have
    "u' \<turnstile> List.map_filter (\<lambda>pc. case P pc of
        None \<Rightarrow> None
      | Some (INSTR xa) \<Rightarrow> Map.empty xa
      | Some (CEXP xa) \<Rightarrow> Some xa) pcs" unfolding make_g_def
    by auto
  moreover from * exec_min_steps[of PT n _ "[]" _ pcs] exec_steps_visited[of PT pcs _ "[]"] have "pc \<in> set pcs"
    if "steps PT (length pcs) (pc_g, [], s', True, []) (pc, st, m, f, rs)" for pc st m f rs
    using that by fastforce
  ultimately have "u' \<turnstile>\<^sub>a ac"
    if "steps PT (length pcs) (pc_g, [], s', True, []) (pc, st, m, f, rs)" "P pc = Some (CEXP ac)"
    for pc st m f rs ac
    using that by (force split: option.splits simp: list_all_iff set_map_filter)
  then have "\<forall>pc' st s'' f' rs ac. stepsc P (length pcs) u' (pc_g, [], s', True, []) (pc', st, s'', f', rs) \<and> P pc' = Some (CEXP ac) \<longrightarrow> u' \<turnstile>\<^sub>a ac"
    sorry
  from stepst_t_equiv[OF this] * exec_min_steps[of PT n _ "[]" _ pcs] have
    "stepst P (length pcs) u' (pc_g, [], s', True, []) (pc, st, s'', True, rs)"
    by fastforce
  moreover have "n \<ge> length pcs" sorry
  ultimately show ?thesis by (blast intro: stepst_mono)
qed

lemma P_bounded:
  assumes
    "(defs.P ! q) (L' ! q) s'" "q < p"
  shows "bounded B s'"
  using assms unfolding state_pred_def state_ta_def by (auto split: option.splits)

lemma P_steps:
  assumes
    "(defs.P ! q) (L' ! q) s'"
    "q < p" "L' \<in> defs.states' s'"
  shows
    "\<exists> pc st s'' rs. stepst P n u' ((I ! q) (L' ! q), [], s', True, []) (pc, st, s'', True, rs)"
proof -
  from assms pred_time_indep have *: "time_indep P n ((I ! q) (L' ! q), [], s', True, [])" by auto
  from assms(1) \<open>q < p\<close> obtain pc st s'' rs pcs where
    "exec PF n ((I ! q) (L' ! q), [], s', True, []) [] = Some ((pc, st, s'', True, rs), pcs)"
    unfolding state_pred_def state_ta_def by (auto split: option.splits)
  with stepst_f_equiv[OF *] show ?thesis by blast
qed

lemma steps_P:
  assumes
    "stepst P n u' ((I ! q) (L' ! q), [], s', True, []) (pc, st, s'', True, rs)"
    "q < p" "L' \<in> defs.states' s'"
    "bounded B s'"
  shows
    "(defs.P ! q) (L' ! q) s'"
proof -
  from assms pred_time_indep have "time_indep P n ((I ! q) (L' ! q), [], s', True, [])" by auto
  from stepst_f_equiv[OF this] assms(1) obtain pcs' where
    "exec PF n ((I ! q) (L' ! q), [], s', True, []) [] = Some ((pc, st, s'', True, rs), pcs')"
    by blast
  with \<open>q < p\<close> \<open>bounded B s'\<close> show ?thesis unfolding state_pred_def state_ta_def by simp
qed

lemma P_iff:
  "(\<exists> pc st rs s''. stepst P n u' ((I ! q) (L' ! q), [], s', True, []) (pc, st, s'', True, rs)
  \<and> bounded B s')
  \<longleftrightarrow> (defs.P ! q) (L' ! q) s'" if "q < p" "L' \<in> defs.states' s'"
  using that by (metis steps_P P_steps P_bounded)

lemma states'_updI':
  assumes "(L' ! q, g, (a, c, m), f, l') \<in> fst (defs.N ! q)" "L' \<in> defs.states' s''"
  shows "L'[q := l'] \<in> defs.states' s'"
  using assms
  unfolding prod.states'_simp[of s' s'']
  unfolding Product_TA_Defs.states_def
  apply clarsimp
  subgoal for p
    by (cases "p = q"; force simp: prod.trans_of_N_s_2 prod.N_s_length)
  done

lemma states'_updI:
  assumes "(L ! q, g, (a, c, m), f, l') \<in> fst (defs.N ! q)"
  shows "L[q := l'] \<in> defs.states' s'"
using assms by (auto intro: states'_updI')

lemma states'_updI'':
  assumes
    "(L' ! q, g, (a, c, m), f, l') \<in> fst (defs.N ! q)"
    "(L' ! q', g', (a', c', m'), f', l'') \<in> fst (defs.N ! q')"
    "L' \<in> defs.states' s''" "q \<noteq> q'"
  shows "L'[q := l', q' := l''] \<in> defs.states' s'"
  using assms by (auto intro: states'_updI')

lemma equiv_sound:
  assumes step: "state_ta \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"
    shows "A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"
  using step proof cases
  case (step_sn_t N d I)
  then show ?thesis
    apply simp
    apply (subst A_unfold)
    apply (frule prod.A_simp(1))
    apply (frule prod.A_simp(2))
    apply (rule step_u_t)
    using inv'' bounded by (auto simp: inv_simp p_def)
next
  case (step_sn_i l g a c m f l' N p r I)
  then show ?thesis
    apply (simp)
    apply (frule prod.A_simp(1))
    apply (frule prod.A_simp(2))
    apply (simp add: prod.N_s_length)
    apply (subst A_unfold)
    apply (drule trans_state_taD)
     apply assumption
    subgoal
      unfolding state_trans_t_def
      apply safe
      apply (drule P_steps_upd)
        prefer 2
        apply assumption
       apply assumption
      apply (drule P_steps_guard)
         apply blast
        prefer 2
        apply assumption
       apply assumption
      apply safe
      apply (rule step_u_i)
              prefer 3
      subgoal
        apply safe
        apply (rule P_steps)
          apply (fastforce simp: p_def)
         apply (fastforce simp: p_def)
        by (metis Prod_TA_Defs'.states'_simp Prod_TA_Defs'.states_step local.step states)
      by (auto simp: inv_simp p_def prod.N_s_length intro!: P_bounded)
    done
next
  case (step_sn_s l1 g1 a ci mi f1 l1' N p l2 g2 co mo f2 l2' q r1 r2 I)
  then show ?thesis
    apply (simp)
    apply (frule prod.A_simp(1))
    apply (frule prod.A_simp(2))
    apply (simp add: prod.N_s_length)
    apply (subst A_unfold)
    apply (drule trans_state_taD)
     apply assumption
    apply (drule trans_state_taD)
     apply assumption
    subgoal
      unfolding state_trans_t_def
      apply safe
      apply (drule P_steps_upd)
        prefer 2
        apply assumption
       apply assumption
      apply (drule P_steps_upd)
        prefer 2
        apply assumption
       apply assumption
      apply (drule P_steps_guard)
         apply blast
        prefer 2
        apply assumption
       apply assumption
      apply (drule P_steps_guard)
         apply blast
        prefer 2
        apply assumption
       apply assumption
      apply safe
      apply (rule step_u_s)
      using [[goals_limit = 1]]
                     prefer 4
        apply (rule P_steps_reset; force)
                       prefer 5
          subgoal
        apply safe
        apply (rule P_steps)
          apply (fastforce simp: p_def)
         apply (fastforce simp: p_def)
            by (metis Prod_TA_Defs'.states'_simp Prod_TA_Defs'.states_step local.step states)
              by (auto simp: inv_simp p_def prod.N_s_length intro!: P_bounded)
    done
qed

lemma state_ta_unfold:
  "state_ta = (defs.N, defs.P)"
  by simp

lemma equiv_complete:
  assumes step: "A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"
    shows "state_ta \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"
    using step proof cases
    case (step_u_t N P d I)
    note [simp] = A_simp[OF this(1)]
    from step_u_t(2-) show ?thesis
      by (auto simp: state_ta_def p_def state_inv_def intro: step_sn_t)
  next
    case (step_u_i P pc_g uu uv uw ux pc_u uy uz va r N I l a l' p)
    note [simp] = A_simp[OF this(1)]
    from step_u_i(2-) show ?thesis
      apply -
      apply (simp add: prod.N_s_length)
      apply (subst state_ta_unfold)
      apply (frule steps_P_guard(1))
        apply assumption
        apply (simp; fail)
      apply (drule steps_P_guard(2))
        apply assumption
        apply (simp; fail)
      apply (frule steps_P_upd(1))
        apply assumption
        apply (simp; fail)
      apply (drule steps_P_upd(2))
        apply assumption
        apply (simp; fail)
      apply (drule N_transD)
       apply assumption
      apply (rule step_sn_i)
        apply assumption
                apply auto
        apply (simp add: state_ta_def p_def state_inv_def state_pred_def; fail)
       apply (simp add: prod.N_s_length; fail)
      by (fastforce simp: p_def intro: steps_P intro!: states'_updI)
  next
    case (step_u_s P pc_g1 vb vc vd ve pc_g2 vf vg vh vi pc_u2 vj vk s1 vl r2 pc_u1 r1 vm vn vo vp N I l1 a l1' p' l2 l2' q)
    note [simp] = A_simp[OF this(1)]
    from \<open>q < length L\<close> have "q < p" by (simp add: prod.N_s_length)
    from step_u_s(2-) show ?thesis
      apply -
      apply (simp add: prod.N_s_length)
      apply (subst state_ta_unfold)
      apply (frule steps_P_guard(1))
        apply assumption
        apply (simp; fail)
      apply (drule steps_P_guard(2))
        apply assumption
       apply (simp; fail)
      apply (frule steps_P_guard(1))
        apply (rule \<open>q < p\<close>)
        apply (simp; fail)
      apply (drule steps_P_guard(2))
        apply (rule \<open>q < p\<close>)
        apply (simp; fail)
      apply (frule steps_P_upd(1))
        apply (rule \<open>q < p\<close>)
        apply (simp; fail)
      apply (drule steps_P_upd(2))
        apply (rule \<open>q < p\<close>)
       apply (simp; fail)
      apply (drule steps_P_reset[simplified])
        apply (frule steps_P_upd(1))
        apply assumption
        apply (simp; fail)
      apply (drule steps_P_upd(2))
        apply assumption
        apply (simp; fail)
      apply (drule N_transD)
       apply assumption
      apply (drule N_transD)
       apply assumption
      apply (rule step_sn_s)
                         apply assumption
                        apply assumption
                apply auto
        apply (simp add: state_ta_def p_def state_inv_def state_pred_def; fail)
         apply (simp add: prod.N_s_length; fail)
        apply (simp add: prod.N_s_length; fail)
       apply (simp add: p_def)
       apply (erule allE)
       apply (erule impE)
        apply (rotate_tac 5)
        apply assumption
        apply safe
       by (fastforce simp: p_def intro: steps_P intro!: states'_updI'')
   qed

lemma equiv_sound':
  assumes step: "state_ta \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"
    shows "A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle> \<and> L' \<in> defs.states' s' \<and> (\<forall>q<p. \<exists>pc st s'' rs pcs.
             exec PF n ((I ! q) (L' ! q), [], s', True, []) [] =
             Some ((pc, st, s'', True, rs), pcs))"
  using step proof cases
  case (step_sn_t N d I)
  then show ?thesis
    apply simp
    apply (subst A_unfold)
    apply (frule prod.A_simp(1))
    apply (frule prod.A_simp(2))
    apply (rule conjI)
    apply (rule step_u_t)
    using inv inv'' bounded by (auto simp: inv_simp p_def)
next
  case (step_sn_i l g a c m f l' N p r I)
  then show ?thesis
    apply (simp)
    apply (frule prod.A_simp(1))
    apply (frule prod.A_simp(2))
    apply (simp add: prod.N_s_length)
    apply (subst A_unfold)
    apply (drule trans_state_taD)
     apply assumption
    subgoal
      unfolding state_trans_t_def
      apply safe
      apply (drule P_steps_upd)
        prefer 2
        apply assumption
       apply assumption
      apply (drule P_steps_guard)
         apply blast
        prefer 2
        apply assumption
       apply assumption
      apply safe
      apply (rule step_u_i)
              prefer 3
      subgoal
        apply safe
        apply (rule P_steps)
          apply (fastforce simp: p_def)
         apply (fastforce simp: p_def)
        by (metis Prod_TA_Defs'.states'_simp Prod_TA_Defs'.states_step local.step states)
                apply (auto simp: inv_simp p_def prod.N_s_length intro!: P_bounded)
       apply (metis Prod_TA_Defs'.states'_simp Prod_TA_Defs'.states_step local.step states)
      subgoal premises prems for pc_g pc_u q
        using prems(7) \<open>q < _\<close> unfolding state_ta_def state_pred_def
        by (fastforce simp: p_def split: option.splits)
      done
    done
next
  case (step_sn_s l1 g1 a ci mi f1 l1' N p l2 g2 co mo f2 l2' q r1 r2 I)
  then show ?thesis
    apply (simp)
    apply (frule prod.A_simp(1))
    apply (frule prod.A_simp(2))
    apply (simp add: prod.N_s_length)
    apply (subst A_unfold)
    apply (drule trans_state_taD)
     apply assumption
    apply (drule trans_state_taD)
     apply assumption
    subgoal
      unfolding state_trans_t_def
      apply safe
      apply (drule P_steps_upd)
        prefer 2
        apply assumption
       apply assumption
      apply (drule P_steps_upd)
        prefer 2
        apply assumption
       apply assumption
      apply (drule P_steps_guard)
         apply blast
        prefer 2
        apply assumption
       apply assumption
      apply (drule P_steps_guard)
         apply blast
        prefer 2
        apply assumption
       apply assumption
      apply safe
      apply (rule step_u_s)
      using [[goals_limit = 1]]
                     prefer 4
        apply (rule P_steps_reset; force)
                       prefer 5
          subgoal
        apply safe
        apply (rule P_steps)
          apply (fastforce simp: p_def)
         apply (fastforce simp: p_def)
            by (metis Prod_TA_Defs'.states'_simp Prod_TA_Defs'.states_step local.step states)
              (* XXX Metis-free proof? *)
                        apply (auto simp: inv_simp p_def prod.N_s_length intro!: P_bounded)
          apply (metis Prod_TA_Defs'.states'_simp Prod_TA_Defs'.states_step local.step states)
            subgoal premises prems for pc_g pc_ga pc_u pc_ua q'
            using prems(11) \<open>q' < _\<close> unfolding state_ta_def state_pred_def
            by (fastforce simp: p_def split: option.splits)
          done
    done
qed

lemma equiv_complete':
  assumes step: "A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"
  shows "state_ta \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle> \<and> L' \<in> defs.states' s'
      \<and> (\<forall> q < p. (defs.P ! q) (L' ! q) s')"
    using step proof cases
    case (step_u_t N P d I)
    note [simp] = A_simp[OF this(1)]
    from step_u_t(2-) show ?thesis
      apply (auto simp: state_ta_def p_def state_inv_def intro: step_sn_t) sorry
  next
    case (step_u_i P pc_g uu uv uw ux pc_u uy uz va r N I l a l' p)
    note [simp] = A_simp[OF this(1)]
    from step_u_i(2-) show ?thesis
      apply -
      apply (simp add: prod.N_s_length)
      apply (subst state_ta_unfold)
      apply (frule steps_P_guard(1))
        apply assumption
        apply (simp; fail)
      apply (drule steps_P_guard(2))
        apply assumption
        apply (simp; fail)
      apply (frule steps_P_upd(1))
        apply assumption
        apply (simp; fail)
      apply (drule steps_P_upd(2))
        apply assumption
        apply (simp; fail)
      apply (drule N_transD)
       apply assumption
        apply safe
      apply (rule step_sn_i)
        apply assumption
                apply auto
        apply (simp add: state_ta_def p_def state_inv_def state_pred_def; fail)
       apply (simp add: prod.N_s_length; fail)
        by (fastforce simp: p_def intro: steps_P intro!: states'_updI)+
  next
    case (step_u_s P pc_g1 vb vc vd ve pc_g2 vf vg vh vi pc_u2 vj vk s1 vl r2 pc_u1 r1 vm vn vo vp N I l1 a l1' p' l2 l2' q)
    note [simp] = A_simp[OF this(1)]
    from \<open>q < length L\<close> have "q < p" by (simp add: prod.N_s_length)
    from step_u_s(2-) show ?thesis
      apply -
      apply (simp add: prod.N_s_length)
      apply (subst state_ta_unfold)
      apply (frule steps_P_guard(1))
        apply assumption
        apply (simp; fail)
      apply (drule steps_P_guard(2))
        apply assumption
       apply (simp; fail)
      apply (frule steps_P_guard(1))
        apply (rule \<open>q < p\<close>)
        apply (simp; fail)
      apply (drule steps_P_guard(2))
        apply (rule \<open>q < p\<close>)
        apply (simp; fail)
      apply (frule steps_P_upd(1))
        apply (rule \<open>q < p\<close>)
        apply (simp; fail)
      apply (drule steps_P_upd(2))
        apply (rule \<open>q < p\<close>)
       apply (simp; fail)
      apply (drule steps_P_reset[simplified])
        apply (frule steps_P_upd(1))
        apply assumption
        apply (simp; fail)
      apply (drule steps_P_upd(2))
        apply assumption
        apply (simp; fail)
      apply (drule N_transD)
       apply assumption
      apply (drule N_transD)
       apply assumption
        apply safe
      apply (rule step_sn_s)
                         apply assumption
                        apply assumption
                apply auto
        apply (simp add: state_ta_def p_def state_inv_def state_pred_def; fail)
         apply (simp add: prod.N_s_length; fail)
        apply (simp add: prod.N_s_length; fail)
       apply (simp add: p_def)
       apply (erule allE)
       apply (erule impE)
        apply (rotate_tac 5)
        apply assumption
        apply (fastforce simp: p_def intro: steps_P intro!: states'_updI'')
       apply (fastforce simp: p_def intro: steps_P intro!: states'_updI'')
        apply (simp add: p_def)
       apply (erule allE)
       apply (erule impE)
        apply (rotate_tac 5)
        apply assumption
        by (fastforce simp: p_def intro: steps_P intro!: states'_updI'') (* XXX Cleanup *)
   qed

  lemma equiv_complete'':
    assumes step: "A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>" "p > 0"
      shows "(\<forall>q<p. \<exists>pc st s'' rs pcs.
               exec PF n ((I ! q) (L' ! q), [], s', True, []) [] =
               Some ((pc, st, s'', True, rs), pcs))" (is ?A)
            "bounded B s'" (is ?B)
  proof -
    from assms equiv_complete' have *: "\<forall>q<p. (defs.P ! q) (L' ! q) s'" by simp
    then show ?A unfolding state_ta_def state_pred_def by (fastforce split: option.splits)
    from \<open>p > 0\<close> * have "(defs.P ! 0) (L' ! 0) s'" by auto
    with \<open>p > 0\<close> show ?B unfolding state_ta_def state_pred_def by (auto split: option.splits)
  qed

  lemma equiv_steps_sound':
    assumes step: "state_ta \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>"
    shows "A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle> \<and> L' \<in> defs.states' s' \<and>
        (\<forall>q<p. \<exists>pc st s'' rs pcs.
             exec PF n ((I ! q) (L' ! q), [], s', True, []) [] =
             Some ((pc, st, s'', True, rs), pcs)) \<and> bounded B s'"
    using step states inv
  proof (induction A \<equiv> state_ta L \<equiv> L s \<equiv> s u \<equiv> u L' s' u' arbitrary: rule: steps_sn.induct)
    case (refl)
    with bounded show ?case by blast
  next
    case prems: (step L' s' u' L'' s'' u'')
    from prems have *:
      "A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>" "L' \<in> defs.states' s'"
      "(\<forall>q<p. \<exists>pc st s'' rs pcs.
             exec PF n ((I ! q) (L' ! q), [], s', True, []) [] =
             Some ((pc, st, s'', True, rs), pcs))"
      "bounded B s'"
      by auto
    interpret interp: Equiv_TA A n L' s' u'
      using pred_time_indep upd_time_indep clock_conj * by unfold_locales (auto simp: Len intro!: *)
    from prems(3) have
      "A \<turnstile>\<^sub>n \<langle>L', s', u'\<rangle> \<rightarrow> \<langle>L'', s'', u''\<rangle>" "L'' \<in> defs.states' s''"
      "\<forall>q<p. \<exists>pc st s''' rs pcs.
              exec PF n ((I ! q) (L'' ! q), [], s'', True, []) [] =
              Some ((pc, st, s''', True, rs), pcs)"
      "bounded B s''"
      by (force dest!: interp.equiv_sound')+
    with * interp.states show ?case by - (assumption | rule)+
  qed

lemma equiv_steps_complete':
    "state_ta \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle> \<and> L' \<in> defs.states' s' \<and>
        (\<forall>q<p. \<exists>pc st s'' rs pcs.
             exec PF n ((I ! q) (L' ! q), [], s', True, []) [] =
             Some ((pc, st, s'', True, rs), pcs)) \<and> bounded B s'"
    if "A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>" "p > 0"
    using that states inv proof (induction A \<equiv> A n \<equiv> n L \<equiv> L s \<equiv> s u \<equiv> u _ _ _ rule: steps_un.induct)
    case refl
    with bounded show ?case by blast
  next
    case prems: (step L' s' u' L'' s'' u'')
    from prems have *:
      "state_ta \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>" "L' \<in> defs.states' s'"
      "(\<forall>q<p. \<exists>pc st s'' rs pcs.
             exec PF n ((I ! q) (L' ! q), [], s', True, []) [] =
             Some ((pc, st, s'', True, rs), pcs))"
      "bounded B s'"
      by auto
    interpret interp: Equiv_TA A n L' s' u'
      using pred_time_indep upd_time_indep clock_conj by unfold_locales (auto simp: Len intro!: *)
    from interp.equiv_complete'[OF prems(3)] interp.equiv_complete''[OF prems(3) \<open>p > 0\<close>] have
      "state_ta \<turnstile> \<langle>L', s', u'\<rangle> \<rightarrow> \<langle>L'', s'', u''\<rangle>" "L'' \<in> defs.states' s''"
      "\<forall>q<p. \<exists>pc st s''' rs pcs.
              exec PF n ((I ! q) (L'' ! q), [], s'', True, []) [] =
              Some ((pc, st, s''', True, rs), pcs)"
      "bounded B s''"
      by auto
    with * interp.states show ?case by - (assumption | rule)+
  qed

  lemmas equiv_steps_sound = equiv_steps_sound'[THEN conjunct1]
  lemmas equiv_steps_complete = equiv_steps_complete'[THEN conjunct1]

  lemma equiv_correct:
    "state_ta \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle> \<longleftrightarrow> A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>" if "p > 0"
    using that equiv_steps_sound equiv_steps_complete by metis

  lemma prod_correct:
    "defs.prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow>* \<langle>(L', s'), u'\<rangle> \<longleftrightarrow> A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>" if "p > 0"
    by (metis prod.prod_correct equiv_correct that)

  end (* End context: UPPAAL network + valid start state *)

end (* End of theory *)
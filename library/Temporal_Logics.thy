theory Temporal_Logics
  imports CTL LTL.LTL LTL_Master_Theorem.Omega_Words_Fun_Stream
begin

lemmas [simp] = holds.simps

lemma suffix_stl:
  "suffix (Suc 0) (snth xs) = snth (stl xs)"
  unfolding suffix_def by auto

lemma suntil_iff_sdrop:
  "(\<phi> suntil \<psi>) xs \<longleftrightarrow> (\<exists>i. \<psi> (sdrop i xs) \<and> (\<forall>j<i. \<phi> (sdrop j xs)))"
proof safe
  show "\<exists>i. \<psi> (sdrop i xs) \<and> (\<forall>j<i. \<phi> (sdrop j xs))" if "(\<phi> suntil \<psi>) xs"
    using that
  proof (induction rule: suntil.induct)
    case (base \<omega>)
    then show ?case
      by force
  next
    case (step \<omega>)
    then obtain i where "\<psi> (sdrop i (stl \<omega>))" "\<forall>j<i. \<phi> (sdrop j (stl \<omega>))"
      by safe
    with \<open>\<phi> \<omega>\<close> have "\<phi> (sdrop j \<omega>)" if "j<i + 1" for j
      using that by (cases j) auto
    with \<open>\<psi> (sdrop i (stl \<omega>))\<close> show ?case
      by (inst_existentials "i + 1") auto
  qed
  show "(\<phi> suntil \<psi>) xs" if "\<psi> (sdrop i xs)" "\<forall>j<i. \<phi> (sdrop j xs)" for i
    using that by (induction i arbitrary: xs; fastforce intro: suntil.intros)
qed

lemma to_stream_suffix_Suc:
  "to_stream (suffix (Suc k) xs) = stl (to_stream (suffix k xs))"
  by (metis add.right_neutral add_Suc_right suffix_stl suffix_suffix
        to_omega_def to_omega_to_stream to_stream_to_omega)

lemma to_stream_stake:
  "sdrop k (to_stream w) = to_stream (suffix k w)"
  by (induction k arbitrary: w) (auto simp: sdrop_stl to_stream_suffix_Suc)

lemma to_omega_suffix[simp]:
  "suffix k (to_omega s) = to_omega (sdrop k s)"
  by auto

primrec semantics_ltlc' :: "['a word, ('a \<Rightarrow> bool) ltlc] \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>c' _" [80,80] 80)
where
  "\<xi> \<Turnstile>\<^sub>c' true\<^sub>c = True"
| "\<xi> \<Turnstile>\<^sub>c' false\<^sub>c = False"
| "\<xi> \<Turnstile>\<^sub>c' prop\<^sub>c(q) = (q (\<xi> 0))"
| "\<xi> \<Turnstile>\<^sub>c' not\<^sub>c \<phi> = (\<not> \<xi> \<Turnstile>\<^sub>c' \<phi>)"
| "\<xi> \<Turnstile>\<^sub>c' \<phi> and\<^sub>c \<psi> = (\<xi> \<Turnstile>\<^sub>c' \<phi> \<and> \<xi> \<Turnstile>\<^sub>c' \<psi>)"
| "\<xi> \<Turnstile>\<^sub>c' \<phi> or\<^sub>c \<psi> = (\<xi> \<Turnstile>\<^sub>c' \<phi> \<or> \<xi> \<Turnstile>\<^sub>c' \<psi>)"
| "\<xi> \<Turnstile>\<^sub>c' \<phi> implies\<^sub>c \<psi> = (\<xi> \<Turnstile>\<^sub>c' \<phi> \<longrightarrow> \<xi> \<Turnstile>\<^sub>c' \<psi>)"
| "\<xi> \<Turnstile>\<^sub>c' X\<^sub>c \<phi> = (suffix 1 \<xi> \<Turnstile>\<^sub>c' \<phi>)"
| "\<xi> \<Turnstile>\<^sub>c' F\<^sub>c \<phi> = (\<exists>i. suffix i \<xi> \<Turnstile>\<^sub>c' \<phi>)"
| "\<xi> \<Turnstile>\<^sub>c' G\<^sub>c \<phi> = (\<forall>i. suffix i \<xi> \<Turnstile>\<^sub>c' \<phi>)"
| "\<xi> \<Turnstile>\<^sub>c' \<phi> U\<^sub>c \<psi> = (\<exists>i. suffix i \<xi> \<Turnstile>\<^sub>c' \<psi> \<and> (\<forall>j<i. suffix j \<xi> \<Turnstile>\<^sub>c' \<phi>))"
| "\<xi> \<Turnstile>\<^sub>c' \<phi> R\<^sub>c \<psi> = (\<forall>i. suffix i \<xi> \<Turnstile>\<^sub>c' \<psi> \<or> (\<exists>j<i. suffix j \<xi> \<Turnstile>\<^sub>c' \<phi>))"
| "\<xi> \<Turnstile>\<^sub>c' \<phi> W\<^sub>c \<psi> = (\<forall>i. suffix i \<xi> \<Turnstile>\<^sub>c' \<phi> \<or> (\<exists>j\<le>i. suffix j \<xi> \<Turnstile>\<^sub>c' \<psi>))"
| "\<xi> \<Turnstile>\<^sub>c' \<phi> M\<^sub>c \<psi> = (\<exists>i. suffix i \<xi> \<Turnstile>\<^sub>c' \<phi> \<and> (\<forall>j\<le>i. suffix j \<xi> \<Turnstile>\<^sub>c' \<psi>))"

lemma semantics_ltlc'_sugar [simp]:
  "\<xi> \<Turnstile>\<^sub>c' \<phi> iff\<^sub>c \<psi> = (\<xi> \<Turnstile>\<^sub>c' \<phi> \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>c' \<psi>)"
  "\<xi> \<Turnstile>\<^sub>c' F\<^sub>c \<phi> = \<xi> \<Turnstile>\<^sub>c' (true\<^sub>c U\<^sub>c \<phi>)"
  "\<xi> \<Turnstile>\<^sub>c' G\<^sub>c \<phi> = \<xi> \<Turnstile>\<^sub>c' (false\<^sub>c R\<^sub>c \<phi>)"
  by (auto simp add: Iff_ltlc_def)

definition "language_ltlc' \<phi> \<equiv> {\<xi>. \<xi> \<Turnstile>\<^sub>c' \<phi>}"

fun ltlc_to_pltl :: "('a \<Rightarrow> bool) ltlc \<Rightarrow> 'a pltl"
where
  "ltlc_to_pltl true\<^sub>c = true\<^sub>p"
| "ltlc_to_pltl false\<^sub>c = false\<^sub>p"
| "ltlc_to_pltl (prop\<^sub>c(q)) = atom\<^sub>p(q)"
| "ltlc_to_pltl (not\<^sub>c \<phi>) = not\<^sub>p (ltlc_to_pltl \<phi>)"
| "ltlc_to_pltl (\<phi> and\<^sub>c \<psi>) = (ltlc_to_pltl \<phi>) and\<^sub>p (ltlc_to_pltl \<psi>)"
| "ltlc_to_pltl (\<phi> or\<^sub>c \<psi>) = (ltlc_to_pltl \<phi>) or\<^sub>p (ltlc_to_pltl \<psi>)"
| "ltlc_to_pltl (\<phi> implies\<^sub>c \<psi>) = (ltlc_to_pltl \<phi>) implies\<^sub>p (ltlc_to_pltl \<psi>)"
| "ltlc_to_pltl (X\<^sub>c \<phi>) = X\<^sub>p (ltlc_to_pltl \<phi>)"
| "ltlc_to_pltl (F\<^sub>c \<phi>) = F\<^sub>p (ltlc_to_pltl \<phi>)"
| "ltlc_to_pltl (G\<^sub>c \<phi>) = G\<^sub>p (ltlc_to_pltl \<phi>)"
| "ltlc_to_pltl (\<phi> U\<^sub>c \<psi>) = (ltlc_to_pltl \<phi>) U\<^sub>p (ltlc_to_pltl \<psi>)"
| "ltlc_to_pltl (\<phi> R\<^sub>c \<psi>) = (ltlc_to_pltl \<phi>) R\<^sub>p (ltlc_to_pltl \<psi>)"
| "ltlc_to_pltl (\<phi> W\<^sub>c \<psi>) = (ltlc_to_pltl \<phi>) W\<^sub>p (ltlc_to_pltl \<psi>)"
| "ltlc_to_pltl (\<phi> M\<^sub>c \<psi>) = (ltlc_to_pltl \<phi>) M\<^sub>p (ltlc_to_pltl \<psi>)"

lemma ltlc_to_pltl_semantics [simp]:
  "w \<Turnstile>\<^sub>p ltlc_to_pltl \<phi> \<longleftrightarrow> w \<Turnstile>\<^sub>c' \<phi>"
  by (induction \<phi> arbitrary: w) simp_all

lemma semantics_ltlc'_semantics_ltlc_atoms_iff:
  "w \<Turnstile>\<^sub>c' \<phi> \<longleftrightarrow> (\<lambda>i. {a \<in> atoms_ltlc \<phi>. a (w i)}) \<Turnstile>\<^sub>c \<phi>"
proof -
  have *:
    "(\<lambda>i. {a. (a \<in> atoms_ltlc \<phi>1 \<or> a \<in> atoms_ltlc \<phi>2) \<and> a (w i)}) \<Turnstile>\<^sub>c \<phi>1
    \<longleftrightarrow> ((\<lambda>i. {a \<in> atoms_ltlc \<phi>1. a (w i)}) \<Turnstile>\<^sub>c \<phi>1)" for w :: "nat \<Rightarrow> 'a" and \<phi>1 \<phi>2
    by (rule ltlc_eq_on) (auto simp: pw_eq_on_def)
  have **:
    "(\<lambda>i. {a. (a \<in> atoms_ltlc \<phi>1 \<or> a \<in> atoms_ltlc \<phi>2) \<and> a (w i)}) \<Turnstile>\<^sub>c \<phi>2
    \<longleftrightarrow> ((\<lambda>i. {a \<in> atoms_ltlc \<phi>2. a (w i)}) \<Turnstile>\<^sub>c \<phi>2)"  for w :: "nat \<Rightarrow> 'a" and \<phi>1 \<phi>2
      by (rule ltlc_eq_on) (auto simp: pw_eq_on_def)
  show ?thesis
    by (induction \<phi> arbitrary: w) (simp_all add: suffix_def * **)
qed

lemma semantics_ltlc'_semantics_ltlc_atoms_iff':
  "w \<Turnstile>\<^sub>c' \<phi> \<longleftrightarrow> ((\<lambda>x. {a \<in> atoms_ltlc \<phi>. a x}) o w) \<Turnstile>\<^sub>c \<phi>"
  unfolding comp_def by (rule semantics_ltlc'_semantics_ltlc_atoms_iff)

lemma map_semantics_ltlc_inj:
  assumes "inj f"
  shows "w \<Turnstile>\<^sub>c \<phi> \<longleftrightarrow> (image f o w) \<Turnstile>\<^sub>c map_ltlc f \<phi>"
  using assms unfolding comp_def by (intro map_semantics_ltlc_aux) auto

lemma semantics_ltlc'_abstract:
  assumes "inj abstr" "\<And>x. label x = abstr ` {a \<in> atoms_ltlc \<phi>. a x}"
  shows "w \<Turnstile>\<^sub>c' \<phi> \<longleftrightarrow> (label o w) \<Turnstile>\<^sub>c map_ltlc abstr \<phi>"
  by (subst semantics_ltlc'_semantics_ltlc_atoms_iff')
     (simp add: comp_def assms(2) map_semantics_ltlc_inj[OF \<open>inj abstr\<close>])

context
  includes lifting_syntax
begin

lemma holds_transfer:
  "((R ===> (=)) ===> stream_all2 R ===> (=)) holds holds"
  apply (intro rel_funI)
  subgoal for \<phi> \<psi> xs ys
    by (cases xs; cases ys) (auto dest: rel_funD)
  done

lemma alw_mono1:
  "alw \<phi> xs" if "(stream_all2 R ===> (=)) \<phi> \<psi>" "stream_all2 R xs ys" "alw \<psi> ys"
  using that(2,3)
  by (coinduction arbitrary: xs ys) (use that(1) stream.rel_sel in \<open>auto dest!: rel_funD\<close>)

lemma alw_mono2:
  "alw \<psi> ys" if "(stream_all2 R ===> (=)) \<phi> \<psi>" "stream_all2 R xs ys" "alw \<phi> xs"
  using that(2,3)
  by (coinduction arbitrary: xs ys) (use that(1) stream.rel_sel in \<open>auto dest!: rel_funD\<close>)

lemma alw_transfer':
  "alw x xs = alw y ys" if "(stream_all2 R ===> (=)) x y" "stream_all2 R xs ys"
  using alw_mono1 alw_mono2 that by blast

lemma alw_transfer:
  "((stream_all2 R ===> (=)) ===> stream_all2 R ===> (=)) alw alw"
  by (intro rel_funI) (rule alw_transfer')

lemma nxt_transfer:
  "((stream_all2 R ===> (=)) ===> stream_all2 R ===> (=)) nxt nxt"
  by (intro rel_funI) (simp, meson rel_funD stream.rel_sel)

lemma suntil_mono1:
  "(\<phi> suntil \<psi>) xs"
  if "(stream_all2 R ===> (=)) \<phi> \<phi>'" "(stream_all2 R ===> (=)) \<psi> \<psi>'" "stream_all2 R xs ys"
     "(\<phi>' suntil \<psi>') ys"
  using that(4,3)
proof (induction arbitrary: xs)
  case (base \<omega>)
  then show ?case
    using that(1,2) by (auto dest!: rel_funD intro: suntil.base)
next
  case (step \<omega>)
  from \<open>stream_all2 R xs \<omega>\<close> have "stream_all2 R (stl xs) (stl \<omega>)"
    using stream.rel_sel by auto
  from \<open>\<phi>' \<omega>\<close> \<open>stream_all2 R xs \<omega>\<close> have "\<phi> xs"
    using that(1,2) by (auto dest!: rel_funD)
  moreover from step.IH \<open>stream_all2 R xs \<omega>\<close> have "(\<phi> suntil \<psi>) (stl xs)"
    using stream.rel_sel by auto
  ultimately show ?case ..
qed

lemma suntil_mono2:
  "(\<phi>' suntil \<psi>') ys"
  if "(stream_all2 R ===> (=)) \<phi> \<phi>'" "(stream_all2 R ===> (=)) \<psi> \<psi>'" "stream_all2 R xs ys"
     "(\<phi> suntil \<psi>) xs"
  using that(4,3)
proof (induction arbitrary: ys)
  case (base \<omega>)
  then show ?case
    using that(1,2) by (auto dest!: rel_funD intro: suntil.base)
next
  case (step xs \<omega>)
  from \<open>stream_all2 R xs \<omega>\<close> have "stream_all2 R (stl xs) (stl \<omega>)"
    using stream.rel_sel by auto
  from \<open>\<phi> xs\<close> \<open>stream_all2 R xs \<omega>\<close> have "\<phi>' \<omega>"
    using that(1,2) by (auto dest!: rel_funD)
  moreover from step.IH \<open>stream_all2 R xs \<omega>\<close> have "(\<phi>' suntil \<psi>') (stl \<omega>)"
    using stream.rel_sel by auto
  ultimately show ?case ..
qed

lemma suntil_transfer':
  "(\<phi> suntil \<psi>) xs = (\<phi>' suntil \<psi>') ys"
  if "(stream_all2 R ===> (=)) \<phi> \<phi>'" "(stream_all2 R ===> (=)) \<psi> \<psi>'" "stream_all2 R xs ys"
  using suntil_mono1 suntil_mono2 that by metis

lemma suntil_transfer:
  "((stream_all2 R ===> (=)) ===> (stream_all2 R ===> (=)) ===> stream_all2 R ===> (=))
    Linear_Temporal_Logic_on_Streams.suntil Linear_Temporal_Logic_on_Streams.suntil"
  by (intro rel_funI) (rule suntil_transfer')

lemma ev_mono1:
  "ev \<phi> xs" if "(stream_all2 R ===> (=)) \<phi> \<psi>" "stream_all2 R xs ys" "ev \<psi> ys"
  using that(3,2) by (induction arbitrary: xs; use that(1) stream.rel_sel in \<open>blast dest: rel_funD\<close>)

lemma ev_mono2:
  "ev \<psi> ys" if "(stream_all2 R ===> (=)) \<phi> \<psi>" "stream_all2 R xs ys" "ev \<phi> xs"
  using that(3,2) by (induction arbitrary: ys; use that(1) stream.rel_sel in \<open>blast dest: rel_funD\<close>)

lemma ev_transfer':
  "ev x xs = ev y ys" if "(stream_all2 R ===> (=)) x y" "stream_all2 R xs ys"
  using ev_mono1 ev_mono2 that by blast

lemma ev_transfer:
  "((stream_all2 R ===> (=)) ===> (stream_all2 R ===> (=))) ev ev"
  by (intro rel_funI) (rule ev_transfer')

end

datatype 'a ctl_formula =
  AG "'a ctl_formula" | AX "'a ctl_formula" | EG "'a ctl_formula" | EX "'a ctl_formula" | PropC 'a |
  ImpliesC "'a ctl_formula" "'a ctl_formula" | NotC "'a ctl_formula"

datatype 'a state_formula =
  All "'a path_formula" | Ex "'a path_formula"
| ImpliesS "'a state_formula" "'a state_formula" | NotS "'a state_formula" | PropS 'a
and 'a path_formula =
  G "'a path_formula" | F "'a path_formula"
| X "'a path_formula" | Until "'a path_formula" "'a path_formula"
| ImpliesP "'a path_formula" "'a path_formula" | NotP "'a path_formula" | State "'a state_formula"
| FalseP

fun ctl_to_state where
  "ctl_to_state (AG \<phi>) = All (G (State (ctl_to_state \<phi>)))"
| "ctl_to_state (AX \<phi>) = All (F (State (ctl_to_state \<phi>)))"
| "ctl_to_state (EG \<phi>) = Ex  (G (State (ctl_to_state \<phi>)))"
| "ctl_to_state (ctl_formula.EX \<phi>) = Ex (F (State (ctl_to_state \<phi>)))"
| "ctl_to_state (PropC \<phi>) = PropS \<phi>"
| "ctl_to_state (ImpliesC \<phi> \<psi>) = ImpliesS (ctl_to_state \<phi>) (ctl_to_state \<psi>)"
| "ctl_to_state (NotC \<phi>) = NotS (ctl_to_state \<phi>)"

fun ltlp_to_path where
  "ltlp_to_path false\<^sub>p = FalseP"
| "ltlp_to_path (atom\<^sub>p(\<phi>)) = State (PropS \<phi>)"
| "ltlp_to_path (\<phi> implies\<^sub>p \<psi>) = ImpliesP (ltlp_to_path \<phi>) (ltlp_to_path \<psi>)"
| "ltlp_to_path (X\<^sub>p \<phi>) = X (ltlp_to_path \<phi>)"
| "ltlp_to_path (\<phi> U\<^sub>p \<psi>) = Until (ltlp_to_path \<phi>) (ltlp_to_path \<psi>)"

fun rel_pltl where
  "rel_pltl R false\<^sub>p false\<^sub>p = True"
| "rel_pltl R atom\<^sub>p(x) atom\<^sub>p(y) = R x y"
| "rel_pltl R (x implies\<^sub>p y) (x' implies\<^sub>p y') \<longleftrightarrow> rel_pltl R x x' \<and> rel_pltl R y y'"
| "rel_pltl R (x U\<^sub>p y) (x' U\<^sub>p y') \<longleftrightarrow> rel_pltl R x x' \<and> rel_pltl R y y'"
| "rel_pltl R (X\<^sub>p x) (X\<^sub>p y) \<longleftrightarrow> rel_pltl R x y"
| "rel_pltl _ _ _ = False"

lemma rel_ltlp_to_path:
  "rel_pltl R \<phi> \<psi> \<longleftrightarrow> rel_path_formula R (ltlp_to_path \<phi>) (ltlp_to_path \<psi>)"
  by (induction R \<phi> \<psi> rule: rel_pltl.induct) auto

lemma [simp]:
  "false\<^sub>p = true\<^sub>p \<longleftrightarrow> False"
  unfolding True_ltlp_def Not_ltlp_def by auto

lemmas ltlp_defs =
  True_ltlp_def Not_ltlp_def And_ltlp_def Or_ltlp_def
  Eventually_ltlp_def Always_ltlp_def Release_ltlp_def WeakUntil_ltlp_def StrongRelease_ltlp_def

text \<open>The converse does not hold!\<close>
lemma rel_ltlc_to_pltl:
  "rel_pltl R (ltlc_to_pltl \<phi>) (ltlc_to_pltl \<psi>)" if "rel_ltlc R \<phi> \<psi>"
  using that by (induction rule: ltlc.rel_induct) (auto simp: ltlp_defs)

context Graph_Defs
begin

fun models_state and models_path where
  "models_state (PropS P) x = P x"
| "models_state (All \<phi>) x = (\<forall>xs. run (x ## xs) \<longrightarrow> models_path \<phi> (x ## xs))"
| "models_state (Ex \<phi>) x = (\<exists>xs. run (x ## xs) \<and> models_path \<phi> (x ## xs))"
| "models_state (ImpliesS \<psi> \<psi>') xs = (models_state \<psi> xs \<longrightarrow> models_state \<psi>' xs)"
| "models_state (NotS \<psi>) xs = (\<not> models_state \<psi> xs)"
| "models_path  (State \<psi>) = holds (models_state \<psi>)"
| "models_path  (G \<psi>) = alw (models_path \<psi>)"
| "models_path  (F \<psi>) = ev (models_path \<psi>)"
| "models_path  (X \<psi>) = nxt (models_path \<psi>)"
| "models_path  (Until \<psi> \<psi>') = models_path \<psi> suntil models_path \<psi>'"
| "models_path  FalseP = (\<lambda>_. False)"
| "models_path  (ImpliesP \<psi> \<psi>') = (\<lambda>xs. models_path \<psi> xs \<longrightarrow> models_path \<psi>' xs)"
| "models_path  (NotP \<psi>) = (\<lambda>xs. \<not> models_path \<psi> xs)"

fun models_ctl where
  "models_ctl (PropC P) = P"
| "models_ctl (AG \<phi>) = Alw_alw (models_ctl \<phi>)"
| "models_ctl (AX \<phi>) = Alw_ev (models_ctl \<phi>)"
| "models_ctl (EG \<phi>) = Ex_alw (models_ctl \<phi>)"
| "models_ctl (ctl_formula.EX \<phi>) = Ex_ev (models_ctl \<phi>)"
| "models_ctl (ImpliesC \<phi> \<psi>) = (\<lambda>x. models_ctl \<phi> x \<longrightarrow> models_ctl \<psi> x)"
| "models_ctl (NotC \<phi>) = (\<lambda>x. \<not> models_ctl \<phi> x)"

fun models_ltlp where
  "models_ltlp false\<^sub>p = (\<lambda>_. False)"
| "models_ltlp (atom\<^sub>p(P)) = holds P"
| "models_ltlp (\<phi> implies\<^sub>p \<psi>) = (\<lambda>x. models_ltlp \<phi> x \<longrightarrow> models_ltlp \<psi> x)"
| "models_ltlp (\<phi> U\<^sub>p \<psi>) = models_ltlp \<phi> suntil models_ltlp \<psi>"
| "models_ltlp (X\<^sub>p \<phi>) = nxt (models_ltlp \<phi>)"

lemma models_ltlp_correct:
  "models_ltlp \<phi> xs \<longleftrightarrow> to_omega xs \<Turnstile>\<^sub>p \<phi>"
  by (induction \<phi> arbitrary: xs; simp add: suntil_iff_sdrop)

definition
  "models_ltlc \<phi> xs = to_omega xs \<Turnstile>\<^sub>c' \<phi>"

lemma models_ltlc_alt_def:
  "models_ltlc \<phi> = models_ltlp (ltlc_to_pltl \<phi>)"
  unfolding models_ltlc_def models_ltlp_correct by simp

theorem ctl_to_state_correct:
  "models_ctl \<phi> = models_state (ctl_to_state \<phi>)"
  by (induction \<phi>) (simp add: Alw_alw_def Alw_ev_def Ex_ev_def Ex_alw_def)+

theorem ltlp_to_path_correct:
  "models_ltlp \<phi> = models_path (ltlp_to_path \<phi>)"
  by (induction \<phi>; simp)

end

context Bisimulation_Invariant
begin

context
  includes lifting_syntax
begin

abbreviation compatible where
  "compatible \<equiv> A_B.equiv' ===> (=)"

abbreviation (input)
  "compatible_op \<equiv> compatible ===> compatible"

abbreviation
  "compatible_path \<equiv> stream_all2 A_B.equiv' ===> (=)"

named_theorems compatible

lemma compatible_opI:
  assumes "\<And>\<phi> \<psi>. compatible \<phi> \<psi> \<Longrightarrow> compatible (\<Phi> \<phi>) (\<Psi> \<psi>)"
  shows "compatible_op \<Phi> \<Psi>"
  using assms unfolding rel_fun_def by auto

lemma compatible_opE:
  assumes "compatible_op \<Phi> \<Psi>" "compatible \<phi> \<psi>"
  shows "compatible (\<Phi> \<phi>) (\<Psi> \<psi>)"
  using assms unfolding rel_fun_def by auto

lemma Ex_ev_compatible[compatible, transfer_rule]:
  "compatible_op A.Ex_ev B.Ex_ev"
  using Ex_ev_iff unfolding rel_fun_def by blast

lemma Alw_ev_compatible[compatible, transfer_rule]:
  "compatible_op A.Alw_ev B.Alw_ev"
  using Alw_ev_iff unfolding rel_fun_def by blast

lemma Not_compatible[compatible]:
  "compatible_op ((\<circ>) Not) ((\<circ>) Not)"
  unfolding rel_fun_def by simp

lemma compatible_op_compI:
  assumes [transfer_rule]: "compatible_op \<Phi> \<Psi>" "compatible_op \<Phi>' \<Psi>'"
  shows "compatible_op (\<Phi> o \<Phi>') (\<Psi> o \<Psi>')"
  by transfer_prover

lemma compatible_op_NotI:
  assumes "compatible_op \<Phi> \<Psi>"
  shows "compatible_op (\<lambda>\<phi> x. \<not> \<Phi> \<phi> x) (\<lambda>\<psi> x. \<not> \<Psi> \<psi> x)"
  by (rule compatible_op_compI[unfolded comp_def],
      rule Not_compatible[unfolded comp_def], rule assms)

lemma
  shows Alw_alw_compatible[compatible, transfer_rule]: "compatible_op A.Alw_alw B.Alw_alw"
    and Ex_alw_compatible[compatible, transfer_rule]:  "compatible_op A.Ex_alw B.Ex_alw"
  unfolding Graph_Defs.Alw_alw_iff Graph_Defs.Ex_alw_iff
  by (rule compatible_op_NotI, rule compatible_op_compI[unfolded comp_def]; (rule compatible))+

lemma conj_compatible:
  "(compatible ===> compatible ===> compatible) (\<lambda>\<phi> \<phi>' x. \<phi> x \<and> \<phi>' x) (\<lambda>\<psi> \<psi>' x. \<psi> x \<and> \<psi>' x)"
  by transfer_prover

lemma implies_compatible:
  "(compatible ===> compatible ===> compatible) (\<lambda>\<phi> \<phi>' x. \<phi> x \<longrightarrow> \<phi>' x) (\<lambda>\<psi> \<psi>' x. \<psi> x \<longrightarrow> \<psi>' x)"
  by transfer_prover

lemma disj_compatible:
  "(compatible ===> compatible ===> compatible) (\<lambda>\<phi> \<phi>' x. \<phi> x \<or> \<phi>' x) (\<lambda>\<psi> \<psi>' x. \<psi> x \<or> \<psi>' x)"
  by transfer_prover

lemma Leadsto_compatible:
  "(compatible ===> compatible ===> compatible) A.leadsto B.leadsto"
  unfolding A.leadsto_def B.leadsto_def by transfer_prover

lemmas [compatible] = implies_compatible[THEN rel_funD]

definition
  "protect x = x"

lemma protect_cong[cong]:
  "protect x = protect x"
  unfolding protect_def ..

lemmas [compatible] = Not_compatible[unfolded comp_def]

lemma CTL_compatible:
  assumes "rel_ctl_formula compatible \<phi> \<psi>"
  shows "compatible (A.models_ctl \<phi>) (B.models_ctl \<psi>)"
  using assms by induction (simp; rule compatible_opE, rule compatible, assumption)+

lemma ctl_star_compatible_aux:
  "(rel_state_formula compatible \<phi> \<phi>' \<longrightarrow> compatible (A.models_state \<phi>) (B.models_state \<phi>'))
\<and> (rel_path_formula compatible \<psi> \<psi>' \<longrightarrow> compatible_path (A.models_path \<psi>) (B.models_path \<psi>'))"
proof (induction rule: state_formula_path_formula.rel_induct)
  case (All a b) \<comment> \<open>State\<close>
  then show ?case
    by - (drule holds_transfer[THEN rel_funD], unfold A.models_path.simps B.models_path.simps)
next
  case (ImpliesS a b) \<comment> \<open>All\<close>
  then show ?case
    apply simp
    apply (intro rel_funI allI iffI impI)
     apply (auto 4 4
        dest!: B_A.simulation_run stream_all2_rotate_1 dest: rel_funD elim: equiv'_rotate_1; fail)
    by (auto 4 4 dest!: A_B.simulation_run dest: rel_funD)
next
  case (NotS a12 b12) \<comment> \<open>Ex\<close>
  then show ?case
    apply simp
    apply (intro rel_funI allI iffI impI)
     apply (smt A_B.simulation_run rel_fun_def stream.rel_sel stream.sel(1) stream.sel(2))
    by (smt B_A.simulation_run equiv'_rotate_1 rel_fun_def stream.rel_inject stream_all2_rotate_1)
next
  case (Until a22 b22) \<comment> \<open>F\<close>
  then show ?case
    by - (drule ev_transfer[THEN rel_funD], unfold A.models_path.simps B.models_path.simps)
next
  case (X a b) \<comment> \<open>G\<close>
  then show ?case
    by - (drule alw_transfer[THEN rel_funD], unfold A.models_path.simps B.models_path.simps)
next
  case (ImpliesP a b) \<comment> \<open>X\<close>
  then show ?case
    by - (drule nxt_transfer[THEN rel_funD], unfold A.models_path.simps B.models_path.simps)
next
  case (NotP a22 b22) \<comment> \<open>Until\<close>
  then show ?case
    by - (drule suntil_transfer[THEN rel_funD, THEN rel_funD],
          unfold A.models_path.simps B.models_path.simps)
qed (simp add: rel_fun_def; fail | auto; fail)+

lemmas models_state_compatible = ctl_star_compatible_aux[THEN conjunct1, rule_format]
   and models_path_compatible  = ctl_star_compatible_aux[THEN conjunct2, rule_format]

lemma
  "(compatible_path ===> compatible_path) alw alw"
  by (rule alw_transfer)

lemma
  "(compatible_path ===> compatible_path) ev ev"
  by (rule ev_transfer)

lemma holds_compatible:
  "(compatible ===> compatible_path) holds holds"
  by (rule holds_transfer)

lemma models_ltlp_compatible:
  assumes "rel_pltl compatible \<psi> \<psi>'"
  shows "compatible_path (A.models_ltlp \<psi>) (B.models_ltlp \<psi>')"
  by (metis assms
      A.ltlp_to_path_correct B.ltlp_to_path_correct models_path_compatible rel_ltlp_to_path)

lemma models_ltlc_compatible:
  assumes "rel_ltlc compatible \<psi> \<psi>'"
  shows "compatible_path (A.models_ltlc \<psi>) (B.models_ltlc \<psi>')"
  using assms unfolding A.models_ltlc_alt_def
  by (intro models_ltlp_compatible) (simp only: rel_ltlc_to_pltl)

end (* Transfer Syntax *)

end (* Bisimulation Invariant *)

lemmas [simp del] = holds.simps

end (* Theory *)
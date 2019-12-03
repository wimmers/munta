theory Temporal_Logics
  imports CTL
begin

lemmas [simp] = holds.simps

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
  "((stream_all2 R ===> (=)) ===> (stream_all2 R ===> (=))) alw alw"
  by (intro rel_funI) (rule alw_transfer')

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

datatype 'a ltl_formula =
  G "'a ltl_formula" | F "'a ltl_formula" | PropL 'a |
  ImpliesL "'a ltl_formula" "'a ltl_formula" | NotL "'a ltl_formula"

datatype 'a state_formula =
  All "'a path_formula" | Ex "'a path_formula"
| ImpliesS "'a state_formula" "'a state_formula" | NotS "'a state_formula" | PropS 'a
and 'a path_formula =
  G "'a path_formula" | F "'a path_formula"
| ImpliesP "'a path_formula" "'a path_formula" | NotP "'a path_formula" | State "'a state_formula"

fun ctl_to_state where
  "ctl_to_state (AG \<phi>) = All (G (State (ctl_to_state \<phi>)))"
| "ctl_to_state (AX \<phi>) = All (F (State (ctl_to_state \<phi>)))"
| "ctl_to_state (EG \<phi>) = Ex  (G (State (ctl_to_state \<phi>)))"
| "ctl_to_state (ctl_formula.EX \<phi>) = Ex (F (State (ctl_to_state \<phi>)))"
| "ctl_to_state (PropC \<phi>) = PropS \<phi>"
| "ctl_to_state (ImpliesC \<phi> \<psi>) = ImpliesS (ctl_to_state \<phi>) (ctl_to_state \<psi>)"
| "ctl_to_state (NotC \<phi>) = NotS (ctl_to_state \<phi>)"

fun ltl_to_path where
  "ltl_to_path (ltl_formula.F \<phi>) = F (ltl_to_path \<phi>)"
| "ltl_to_path (ltl_formula.G \<phi>) = G (ltl_to_path \<phi>)"
| "ltl_to_path (ltl_formula.NotL \<phi>) = NotP (ltl_to_path \<phi>)"
| "ltl_to_path (ltl_formula.ImpliesL \<phi> \<psi>) = ImpliesP (ltl_to_path \<phi>) (ltl_to_path \<psi>)"
| "ltl_to_path (ltl_formula.PropL \<phi>) = State (PropS \<phi>)"

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

fun models_ltl where
  "models_ltl  (PropL P) = holds P"
| "models_ltl  (ltl_formula.G \<psi>) = alw (models_ltl \<psi>)"
| "models_ltl  (ltl_formula.F \<psi>) = ev (models_ltl \<psi>)"
| "models_ltl  (ImpliesL \<psi> \<psi>') = (\<lambda>xs. models_ltl \<psi> xs \<longrightarrow> models_ltl \<psi>' xs)"
| "models_ltl  (NotL \<psi>) = (\<lambda>xs. \<not> models_ltl \<psi> xs)"

theorem ctl_to_state_correct:
  "models_ctl \<phi> = models_state (ctl_to_state \<phi>)"
  by (induction \<phi>) (simp add: Alw_alw_def Alw_ev_def Ex_ev_def Ex_alw_def)+

theorem ltl_to_path_correct:
  "models_ltl \<phi> = models_path (ltl_to_path \<phi>)"
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
  case (Ex a25 b25)
  then show ?case
    by - (drule holds_transfer[THEN rel_funD], unfold A.models_path.simps B.models_path.simps)
next
  case (ImpliesS a11 b11)
  then show ?case
    apply simp
    apply (intro rel_funI allI iffI impI)
     apply (auto 4 4
        dest!: B_A.simulation_run stream_all2_rotate_1 dest: rel_funD elim: equiv'_rotate_1; fail)
    by (auto 4 4 dest!: A_B.simulation_run dest: rel_funD)
next
  case (NotS a12 b12)
  then show ?case
    apply simp
    apply (intro rel_funI allI iffI impI)
     apply (smt A_B.simulation_run rel_fun_def stream.rel_sel stream.sel(1) stream.sel(2))
    by (smt B_A.simulation_run equiv'_rotate_1 rel_fun_def stream.rel_inject stream_all2_rotate_1)
next
  case (ImpliesP a21 b21)
  then show ?case
    by - (drule alw_transfer[THEN rel_funD], unfold A.models_path.simps B.models_path.simps)
next
  case (NotP a22 b22)
  then show ?case
    by - (drule ev_transfer[THEN rel_funD], unfold A.models_path.simps B.models_path.simps)
qed (simp add: rel_fun_def)+

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

end (* Transfer Syntax *)

end (* Bisimulation Invariant *)

lemmas [simp del] = holds.simps

end (* Theory *)
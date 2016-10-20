theory Sepref_Acconstraint
  imports "IICF/IICF" Timed_Automata
begin

term hn_ctxt

  subsection \<open>Refinement Assertion\<close>
  fun acconstraint_assn where
(*
    "acconstraint_assn A (E1 x) (E1 x') = A x x'"
  | "acconstraint_assn A (E2 x) (E2 x') = A x x'"
  | "acconstraint_assn A (E3) (E3) = emp"
*)
  "acconstraint_assn A B (LT x y) (LT x' y') = A x x' * B y y'"
  | "acconstraint_assn A B (LE x y) (LE x' y') = A x x' * B y y'"
  | "acconstraint_assn A B (EQ x y) (EQ x' y') = A x x' * B y y'"
  | "acconstraint_assn A B (GE x y) (GE x' y') = A x x' * B y y'"
  | "acconstraint_assn A B (GT x y) (GT x' y') = A x x' * B y y'"
(*
  | "acconstraint_assn A (E5 x y) (E5 x' y') = bool_assn x x' * A y y'"
*)
  | "acconstraint_assn _ _ _ _ = false"


  fun acconstraint_relp where
  "acconstraint_relp A B (LT x y) (LT x' y') \<longleftrightarrow> A x x' \<and> B y y'"
  | "acconstraint_relp A B (LE x y) (LE x' y') \<longleftrightarrow> A x x' \<and> B y y'"
  | "acconstraint_relp A B (EQ x y) (EQ x' y') \<longleftrightarrow> A x x' \<and> B y y'"
  | "acconstraint_relp A B (GE x y) (GE x' y') \<longleftrightarrow> A x x' \<and> B y y'"
  | "acconstraint_relp A B (GT x y) (GT x' y') \<longleftrightarrow> A x x' \<and> B y y'"
  | "acconstraint_relp _ _ _ _ \<longleftrightarrow> False"

  definition [to_relAPP]: "acconstraint_rel A B \<equiv> p2rel (acconstraint_relp (rel2p A) (rel2p B))"
  
  lemma aconstraint_assn_pure_conv[constraint_simps]:
    "acconstraint_assn (pure A) (pure B) \<equiv> pure (\<langle>A,B\<rangle> acconstraint_rel)"
  apply (rule eq_reflection)
  apply (intro ext)
  subgoal for a b
  apply (cases a; cases b; simp add: acconstraint_rel_def pure_def p2rel_def rel2p_def)
  done
  done

  lemmas [sepref_import_rewrite, sepref_frame_normrel_eqs, fcomp_norm_unfold] =
    aconstraint_assn_pure_conv[symmetric]

  text \<open>You might want to prove some properties\<close>

  text \<open>A pure-rule is required to enable recovering of invalidated data that was not stored on the heap\<close>
  lemma acconstraint_assn_pure[constraint_rules]: "is_pure A \<Longrightarrow> is_pure B \<Longrightarrow> is_pure (acconstraint_assn A B)"
    apply (auto simp: is_pure_iff_pure_assn)
    apply (rename_tac x x')
    apply (case_tac x; case_tac x'; simp add: pure_def)
    done

  text \<open>An identitiy rule is required to easily prove trivial refinement theorems\<close>    
  lemma acconstraint_assn_id[simp]: "acconstraint_assn id_assn id_assn = id_assn"
    apply (intro ext)
    subgoal for x y by (cases x; cases y; simp add: pure_def)
    done

  text \<open>With congruence condition\<close>  
  lemma acconstraint_match_cong[sepref_frame_match_rules]: 
    "\<lbrakk>\<And>x y. \<lbrakk>x\<in>set1_acconstraint e; y\<in>set1_acconstraint e'\<rbrakk> \<Longrightarrow> hn_ctxt A x y \<Longrightarrow>\<^sub>t hn_ctxt A' x y\<rbrakk>
    \<Longrightarrow> \<lbrakk>\<And>x y. \<lbrakk>x\<in>set2_acconstraint e; y\<in>set2_acconstraint e'\<rbrakk> \<Longrightarrow> hn_ctxt B x y \<Longrightarrow>\<^sub>t hn_ctxt B' x y\<rbrakk>
    \<Longrightarrow> hn_ctxt (acconstraint_assn A B) e e' \<Longrightarrow>\<^sub>t hn_ctxt (acconstraint_assn A' B') e e'"
    by (cases e; cases e'; simp add: hn_ctxt_def entt_star_mono)
      

  lemma acconstraint_merge_cong[sepref_frame_merge_rules]:
    assumes "\<And>x y. \<lbrakk>x\<in>set1_acconstraint e; y\<in>set1_acconstraint e'\<rbrakk> \<Longrightarrow> hn_ctxt A x y \<or>\<^sub>A hn_ctxt A' x y \<Longrightarrow>\<^sub>t hn_ctxt Am x y"
    assumes "\<And>x y. \<lbrakk>x\<in>set2_acconstraint e; y\<in>set2_acconstraint e'\<rbrakk> \<Longrightarrow> hn_ctxt B x y \<or>\<^sub>A hn_ctxt B' x y \<Longrightarrow>\<^sub>t hn_ctxt Bm x y"
    shows "hn_ctxt (acconstraint_assn A B) e e' \<or>\<^sub>A hn_ctxt (acconstraint_assn A' B') e e' \<Longrightarrow>\<^sub>t hn_ctxt (acconstraint_assn Am Bm) e e'"
    apply (blast intro: entt_disjE acconstraint_match_cong entt_disjD1[OF assms(1)] entt_disjD2[OF assms(1)] entt_disjD1[OF assms(2)] entt_disjD2[OF assms(2)])
    done

  text \<open>Propagating invalid\<close>  
  lemma entt_invalid_acconstraint: "hn_invalid (acconstraint_assn A B) e e' \<Longrightarrow>\<^sub>t hn_ctxt (acconstraint_assn (invalid_assn A) (invalid_assn B)) e e'"
    apply (simp add: hn_ctxt_def invalid_assn_def[abs_def])
    apply (rule enttI)
    apply clarsimp
    apply (cases e; cases e'; auto simp: mod_star_conv pure_def) 
    done

  lemmas invalid_acconstraint_merge[sepref_frame_merge_rules] = gen_merge_cons[OF entt_invalid_acconstraint]

  subsection \<open>Constructors\<close>  
  text \<open>Constructors need to be registered\<close>
  sepref_register LT LE EQ GE GT
  
  text \<open>Refinement rules can be proven straightforwardly on the separation logic level (method @{method sepref_to_hoare})\<close>
  (*
  lemma [sepref_fr_rules]: "(return o E1,RETURN o E1) \<in> A\<^sup>d \<rightarrow>\<^sub>a acconstraint_assn A"
    by sepref_to_hoare sep_auto
  lemma [sepref_fr_rules]: "(return o E2,RETURN o E2) \<in> A\<^sup>d \<rightarrow>\<^sub>a acconstraint_assn A"
    by sepref_to_hoare sep_auto
  lemma [sepref_fr_rules]: "(uncurry0 (return E3),uncurry0 (RETURN E3)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a acconstraint_assn A"
    by sepref_to_hoare sep_auto
  *)
  lemma [sepref_fr_rules]: "(uncurry (return oo LT),uncurry (RETURN oo LT)) \<in> A\<^sup>d*\<^sub>aB\<^sup>d \<rightarrow>\<^sub>a acconstraint_assn A B"
    by sepref_to_hoare sep_auto
  lemma [sepref_fr_rules]: "(uncurry (return oo LE),uncurry (RETURN oo LE)) \<in> A\<^sup>d*\<^sub>aB\<^sup>d \<rightarrow>\<^sub>a acconstraint_assn A B"
    by sepref_to_hoare sep_auto
  lemma [sepref_fr_rules]: "(uncurry (return oo EQ),uncurry (RETURN oo EQ)) \<in> A\<^sup>d*\<^sub>aB\<^sup>d \<rightarrow>\<^sub>a acconstraint_assn A B"
    by sepref_to_hoare sep_auto
  lemma [sepref_fr_rules]: "(uncurry (return oo GE),uncurry (RETURN oo GE)) \<in> A\<^sup>d*\<^sub>aB\<^sup>d \<rightarrow>\<^sub>a acconstraint_assn A B"
    by sepref_to_hoare sep_auto
  lemma [sepref_fr_rules]: "(uncurry (return oo GT),uncurry (RETURN oo GT)) \<in> A\<^sup>d*\<^sub>aB\<^sup>d \<rightarrow>\<^sub>a acconstraint_assn A B"
    by sepref_to_hoare sep_auto
  (*
  lemma [sepref_fr_rules]: "(uncurry (return oo E4),uncurry (RETURN oo E4)) \<in> A\<^sup>d*\<^sub>aA\<^sup>d \<rightarrow>\<^sub>a acconstraint_assn A"
    by sepref_to_hoare sep_auto
  *)
  (*
  lemma [sepref_fr_rules]: "(uncurry (return oo E5),uncurry (RETURN oo E5)) \<in> bool_assn\<^sup>k*\<^sub>aA\<^sup>d \<rightarrow>\<^sub>a acconstraint_assn A"
    by sepref_to_hoare (sep_auto simp: pure_def)
  *)

  subsection \<open>Destructor\<close>  
  text \<open>There is currently no automation for destructors, so all the registration boilerplate 
    needs to be done manually\<close>

  text \<open>Set ups operation identification heuristics\<close>
  sepref_register case_acconstraint

  text \<open>In the monadify phase, this eta-expands to make visible all required arguments\<close>
  lemma [sepref_monadify_arity]: "case_acconstraint \<equiv> \<lambda>\<^sub>2f1 f2 f3 f4 f5 x. SP case_acconstraint$(\<lambda>\<^sub>2x. f1$x)$(\<lambda>\<^sub>2x. f2$x)$f3$(\<lambda>\<^sub>2x y. f4$x$y)$(\<lambda>\<^sub>2x y. f5$x$y)$x"
    by simp

  text \<open>This determines an evaluation order for the first-order operands\<close>  
  lemma [sepref_monadify_comb]: "case_acconstraint$f1$f2$f3$f4$f5$x \<equiv> op \<bind>$(EVAL$x)$(\<lambda>\<^sub>2x. SP case_acconstraint$f1$f2$f3$f4$f5$x)" by simp

  text \<open>This enables translation of the case-distinction in a non-monadic context.\<close>  
  lemma [sepref_monadify_comb]: "EVAL$(case_acconstraint$(\<lambda>\<^sub>2x y. f1 x y)$(\<lambda>\<^sub>2x y. f2 x y)$(\<lambda>\<^sub>2x y. f3 x y)$(\<lambda>\<^sub>2x y. f4 x y)$(\<lambda>\<^sub>2x y. f5 x y)$x) 
    \<equiv> op \<bind>$(EVAL$x)$(\<lambda>\<^sub>2x. SP case_acconstraint$(\<lambda>\<^sub>2x y. EVAL $ f1 x y)$(\<lambda>\<^sub>2x y. EVAL $ f2 x y)$(\<lambda>\<^sub>2x y. EVAL $ f3 x y)$(\<lambda>\<^sub>2x y. EVAL $ f4 x y)$(\<lambda>\<^sub>2x y. EVAL $ f5 x y)$x)"
    apply (rule eq_reflection)
    by (simp split: acconstraint.splits)

  text \<open>Auxiliary lemma, to lift simp-rule over \<open>hn_ctxt\<close>\<close>  
  lemma acconstraint_assn_ctxt: "acconstraint_assn A B x y = z \<Longrightarrow> hn_ctxt (acconstraint_assn A B) x y = z"
    by (simp add: hn_ctxt_def)

  text \<open>The cases lemma first extracts the refinement for the datatype from the precondition.
    Next, it generate proof obligations to refine the functions for every case. 
    Finally the postconditions of the refinement are merged. 

    Note that we handle the
    destructed values separately, to allow reconstruction of the original datatype after the case-expression.

    Moreover, we provide (invalidated) versions of the original compound value to the cases,
    which allows access to pure compound values from inside the case.
    \<close>  
  lemma acconstraint_cases_hnr:
    fixes A B and e :: "('a,'b) acconstraint" and e' :: "('ai,'bi) acconstraint"
    defines [simp]: "INVe \<equiv> hn_invalid (acconstraint_assn A B) e e'"
    assumes FR: "\<Gamma> \<Longrightarrow>\<^sub>t hn_ctxt (acconstraint_assn A B) e e' * F"
    (*
    assumes E1: "\<And>x1 x1a. \<lbrakk>e = E1 x1; e' = E1 x1a\<rbrakk> \<Longrightarrow> hn_refine (hn_ctxt A x1 x1a * INVe * F) (f1' x1a) (hn_ctxt A1' x1 x1a * hn_ctxt XX1 e e' * \<Gamma>1') R (f1 x1)"
    assumes E2: "\<And>x2 x2a. \<lbrakk>e = E2 x2; e' = E2 x2a\<rbrakk> \<Longrightarrow> hn_refine (hn_ctxt A x2 x2a * INVe * F) (f2' x2a) (hn_ctxt A2' x2 x2a * hn_ctxt XX2 e e' * \<Gamma>2') R (f2 x2)"
    assumes E3: "\<lbrakk>e = E3; e' = E3\<rbrakk> \<Longrightarrow> hn_refine F f3' \<Gamma>3' R f3"
    *)
    assumes LT: "\<And>x41 x42 x41a x42a.
       \<lbrakk>e = LT x41 x42; e' = LT x41a x42a\<rbrakk>
       \<Longrightarrow> hn_refine
            (hn_ctxt A x41 x41a * hn_ctxt B x42 x42a * INVe * F)
            (f1' x41a x42a)
            (hn_ctxt A1a' x41 x41a * hn_ctxt B1b' x42 x42a * hn_ctxt XX1 e e' * \<Gamma>1') R
            (f1 x41 x42)"
    assumes LE: "\<And>x41 x42 x41a x42a.
       \<lbrakk>e = LE x41 x42; e' = LE x41a x42a\<rbrakk>
       \<Longrightarrow> hn_refine
            (hn_ctxt A x41 x41a * hn_ctxt B x42 x42a * INVe * F)
            (f2' x41a x42a)
            (hn_ctxt A2a' x41 x41a * hn_ctxt B2b' x42 x42a * hn_ctxt XX2 e e' * \<Gamma>2') R
            (f2 x41 x42)"
    assumes EQ: "\<And>x41 x42 x41a x42a.
       \<lbrakk>e = EQ x41 x42; e' = EQ x41a x42a\<rbrakk>
       \<Longrightarrow> hn_refine
            (hn_ctxt A x41 x41a * hn_ctxt B x42 x42a * INVe * F)
            (f3' x41a x42a)
            (hn_ctxt A3a' x41 x41a * hn_ctxt B3b' x42 x42a * hn_ctxt XX3 e e' * \<Gamma>3') R
            (f3 x41 x42)"
    assumes GE: "\<And>x41 x42 x41a x42a.
       \<lbrakk>e = GE x41 x42; e' = GE x41a x42a\<rbrakk>
       \<Longrightarrow> hn_refine
            (hn_ctxt A x41 x41a * hn_ctxt B x42 x42a * INVe * F)
            (f4' x41a x42a)
            (hn_ctxt A4a' x41 x41a * hn_ctxt B4b' x42 x42a * hn_ctxt XX4 e e' * \<Gamma>4') R
            (f4 x41 x42)"
    assumes GT: "\<And>x41 x42 x41a x42a.
       \<lbrakk>e = GT x41 x42; e' = GT x41a x42a\<rbrakk>
       \<Longrightarrow> hn_refine
            (hn_ctxt A x41 x41a * hn_ctxt B x42 x42a * INVe * F)
            (f5' x41a x42a)
            (hn_ctxt A5a' x41 x41a * hn_ctxt B5b' x42 x42a * hn_ctxt XX5 e e' * \<Gamma>5') R
            (f5 x41 x42)"
    (*
    assumes E5: "\<And>x51 x52 x51a x52a.
       \<lbrakk>e = E5 x51 x52; e' = E5 x51a x52a\<rbrakk>
       \<Longrightarrow> hn_refine (hn_ctxt bool_assn x51 x51a * hn_ctxt A x52 x52a * INVe * F) (f5' x51a x52a)
            (hn_ctxt bool_assn x51 x51a * hn_ctxt A5' x52 x52a * hn_ctxt XX5 e e' * \<Gamma>5') R (f5 x51 x52)"
    *)
    assumes MERGE1a[unfolded hn_ctxt_def]:
      "\<And>x x'. hn_ctxt A1a' x x' \<or>\<^sub>A hn_ctxt A2a' x x' \<or>\<^sub>A hn_ctxt A3a' x x' \<or>\<^sub>A hn_ctxt A4a' x x' \<or>\<^sub>A hn_ctxt A5a' x x' \<Longrightarrow>\<^sub>t hn_ctxt A' x x'"
    assumes MERGE1b[unfolded hn_ctxt_def]:
      "\<And>x x'. hn_ctxt B1b' x x' \<or>\<^sub>A hn_ctxt B2b' x x' \<or>\<^sub>A hn_ctxt B3b' x x' \<or>\<^sub>A hn_ctxt B4b' x x' \<or>\<^sub>A hn_ctxt B5b' x x' \<Longrightarrow>\<^sub>t hn_ctxt B' x x'"
    assumes MERGE2[unfolded hn_ctxt_def]: "\<Gamma>1' \<or>\<^sub>A \<Gamma>2' \<or>\<^sub>A \<Gamma>3' \<or>\<^sub>A \<Gamma>4' \<or>\<^sub>A \<Gamma>5' \<Longrightarrow>\<^sub>t \<Gamma>'"
    shows "hn_refine \<Gamma> (case_acconstraint f1' f2' f3' f5' f4' e') (hn_ctxt (acconstraint_assn A' B') e e' * \<Gamma>') R (case_acconstraint$(\<lambda>\<^sub>2x y. f1 x y)$(\<lambda>\<^sub>2x y. f2 x y)$(\<lambda>\<^sub>2x y. f3 x y)$(\<lambda>\<^sub>2x y. f5 x y)$(\<lambda>\<^sub>2x y. f4 x y)$e)"
    
    apply (rule hn_refine_cons_pre[OF FR])
    apply1 extract_hnr_invalids
    apply (cases e; cases e'; simp add: acconstraint_assn.simps[THEN acconstraint_assn_ctxt])
    subgoal 
      apply (rule hn_refine_cons[OF _ LT _ entt_refl]; assumption?)
      applyS (simp add: hn_ctxt_def)
      apply (rule entt_star_mono)
      apply1 (rule entt_fr_drop)
      apply (rule entt_star_mono)

      apply1 (rule entt_trans[OF _ MERGE1a])
      applyS (simp add: hn_ctxt_def entt_disjI1' entt_disjI2')

      apply1 (rule entt_trans[OF _ MERGE1b])
      applyS (simp add: hn_ctxt_def entt_disjI1' entt_disjI2')

      apply1 (rule entt_trans[OF _ MERGE2])
      applyS (simp add: entt_disjI1' entt_disjI2')
    done
    subgoal 
      apply (rule hn_refine_cons[OF _ LE _ entt_refl]; assumption?)
      applyS (simp add: hn_ctxt_def)
      apply (rule entt_star_mono)
      apply1 (rule entt_fr_drop)
      apply (rule entt_star_mono)

      apply1 (rule entt_trans[OF _ MERGE1a])
      applyS (simp add: hn_ctxt_def entt_disjI1' entt_disjI2')

      apply1 (rule entt_trans[OF _ MERGE1b])
      applyS (simp add: hn_ctxt_def entt_disjI1' entt_disjI2')

      apply1 (rule entt_trans[OF _ MERGE2])
      applyS (simp add: entt_disjI1' entt_disjI2')
    done
    subgoal 
      apply (rule hn_refine_cons[OF _ EQ _ entt_refl]; assumption?)
      applyS (simp add: hn_ctxt_def)
      apply (rule entt_star_mono)
      apply1 (rule entt_fr_drop)
      apply (rule entt_star_mono)

      apply1 (rule entt_trans[OF _ MERGE1a])
      applyS (simp add: hn_ctxt_def entt_disjI1' entt_disjI2')

      apply1 (rule entt_trans[OF _ MERGE1b])
      applyS (simp add: hn_ctxt_def entt_disjI1' entt_disjI2')

      apply1 (rule entt_trans[OF _ MERGE2])
      applyS (simp add: entt_disjI1' entt_disjI2')
    done
    subgoal
      apply (rule hn_refine_cons[OF _ GT _ entt_refl]; assumption?)
      applyS (simp add: hn_ctxt_def)
      apply (rule entt_star_mono)
      apply1 (rule entt_fr_drop)
      apply (rule entt_star_mono)

      apply1 (rule entt_trans[OF _ MERGE1a])
      applyS (simp add: hn_ctxt_def entt_disjI1' entt_disjI2')

      apply1 (rule entt_trans[OF _ MERGE1b])
      applyS (simp add: hn_ctxt_def entt_disjI1' entt_disjI2')

      apply1 (rule entt_trans[OF _ MERGE2])
      applyS (simp add: entt_disjI1' entt_disjI2')
    done
    subgoal 
      apply (rule hn_refine_cons[OF _ GE _ entt_refl]; assumption?)
      applyS (simp add: hn_ctxt_def)
      apply (rule entt_star_mono)
      apply1 (rule entt_fr_drop)
      apply (rule entt_star_mono)

      apply1 (rule entt_trans[OF _ MERGE1a])
      applyS (simp add: hn_ctxt_def entt_disjI1' entt_disjI2')

      apply1 (rule entt_trans[OF _ MERGE1b])
      applyS (simp add: hn_ctxt_def entt_disjI1' entt_disjI2')

      apply1 (rule entt_trans[OF _ MERGE2])
      applyS (simp add: entt_disjI1' entt_disjI2')
    done
  done

  text \<open>After some more preprocessing (adding extra frame-rules for non-atomic postconditions, 
    and splitting the merge-terms into binary merges), this rule can be registered\<close>
  lemmas [sepref_comb_rules] = acconstraint_cases_hnr[sepref_prep_comb_rule]

  subsection \<open>Regression Test\<close>
(*

  definition "test \<equiv> do {
    let x = E1 True;

    _ \<leftarrow> case x of
      E1 _ \<Rightarrow> RETURN x  (* Access compound inside case *)
    | _ \<Rightarrow> RETURN E3;  

    (* Now test with non-pure *)
    let a = op_array_replicate 4 (3::nat);
    let x = E5 False a;
    
    _ \<leftarrow> case x of
      E1 _ \<Rightarrow> RETURN (0::nat)
    | E2 _ \<Rightarrow> RETURN 1
    | E3 \<Rightarrow> RETURN 0
    | E4 _ _ \<Rightarrow> RETURN 0
    | E5 _ a \<Rightarrow> mop_list_get a 0;

    (* Rely on that compound still exists (it's components are only read in the case above) *)
    case x of
      E1 a \<Rightarrow> do {mop_list_set a 0 0; RETURN (0::nat)}
    | E2 _ \<Rightarrow> RETURN 1
    | E3 \<Rightarrow> RETURN 0
    | E4 _ _ \<Rightarrow> RETURN 0
    | E5 _ _ \<Rightarrow> RETURN 0
  }"

  sepref_definition foo is "SYNTH (uncurry0 test) (unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn)"      
    unfolding test_def
    supply [[goals_limit=1]]
    by sepref
*)

end

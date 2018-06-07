theory ML_Util
  imports Main
begin

(* Printing util *)
ML \<open>
  fun pretty_cterm ctxt ctm = Syntax.pretty_term ctxt (Thm.term_of ctm)
  val string_of_cterm = Pretty.string_of oo pretty_cterm
  val string_of_term = Pretty.string_of oo Syntax.pretty_term
\<close>

(* Printing util *)
ML \<open>
  fun string_of_thm ctxt = string_of_cterm ctxt o Thm.cprop_of
\<close>

ML \<open>
val term_pat_setup =
  let
    val parser = Args.context -- Scan.lift Args.name
      fun term_pat (ctxt, str) =
        str
        |> Proof_Context.read_term_pattern ctxt
        |> ML_Syntax.print_term
        |> ML_Syntax.atomic
in
  ML_Antiquotation.inline @{binding "term_pat"} (parser >> term_pat) end
\<close>

setup \<open>term_pat_setup\<close>

ML \<open>
fun match_resolve ctxt concl goal thm =
  let
      val concl_pat = Drule.strip_imp_concl (Thm.cprop_of thm)
      val insts = Thm.first_order_match (concl, concl_pat)
    in
      (Drule.instantiate_normalize insts goal |> resolve_tac ctxt [thm] 1)
    end handle Pattern.MATCH => Seq.empty
val fo_assm_tac = Subgoal.FOCUS_PREMS (
    fn {context = ctxt, concl, prems, ...} => fn goal =>
      Seq.maps (match_resolve ctxt concl goal) (Seq.of_list prems)
  )
\<close>

schematic_goal "c s \<Longrightarrow> c ?x"
  apply (tactic \<open>fo_assm_tac @{context} 1\<close>)
  done

schematic_goal "c s \<Longrightarrow> ?P s"
  apply (tactic \<open>fo_assm_tac @{context} 1\<close>)
  done

ML \<open>
fun dest_binop ct = (Thm.dest_arg1 ct, Thm.dest_arg ct)
val refl_match_tac = Subgoal.FOCUS_PREMS (
  fn {context = ctxt, concl, ...} =>
    let
      val stripped = Thm.dest_arg concl
      val (l, r) = dest_binop stripped
      val insts =
        Thm.first_order_match (r, l)
        handle Pattern.MATCH => Thm.first_order_match (l, r)
    in
      Seq.single o Drule.instantiate_normalize insts THEN
      resolve_tac ctxt [@{thm HOL.refl}] 1
    end handle Pattern.MATCH => no_tac
  )
\<close>

schematic_goal
  "x = ?x"
  by (tactic \<open>refl_match_tac @{context} 1\<close>)

schematic_goal
  "?x = x"
  by (tactic \<open>refl_match_tac @{context} 1\<close>)

ML \<open>fun assumption ctxt = SIMPLE_METHOD (fo_assm_tac ctxt 1)\<close>
ML \<open>fun refl_match ctxt = SIMPLE_METHOD (refl_match_tac ctxt 1)\<close>

method_setup fo_assumption =
  \<open>Scan.succeed assumption\<close> \<open>Prove by assumption with first-order matching\<close>

method_setup refl_match =
  \<open>Scan.succeed refl_match\<close> \<open>Prove equality by reflexivity with first-order matching\<close>

end

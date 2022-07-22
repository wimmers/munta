theory Tag_Explorer
  imports Simple_Networks.Tagging "~/Code/explorer/Explorer"
  keywords "print_tag" "explore_tagged_subgoals" "explore_tags" :: diag
begin

ML \<open>
\<comment> \<open>Stolen from \<open>Explorer\<close>, modifications are highlighted\<close>

datatype explore_kind = PREFER | SUBGOAL \<comment> \<open>modified\<close>

fun split_clause t =
  let
    val (fixes, horn) = funpow_yield (length (Term.strip_all_vars t)) Logic.dest_all_global t;
    val assms = Logic.strip_imp_prems horn;
    val shows = Logic.strip_imp_concl horn;
  in (fixes, assms, shows) end;

(*
  We cannot reuse ATP_Util.maybe_quote because it does not support selecting the
  quoting function. But, this is a copy-paste of that function.
*)
val unquote_tvar = perhaps (try (unprefix "'"))
val unquery_var = perhaps (try (unprefix "?"))

val is_long_identifier = forall Symbol_Pos.is_identifier o Long_Name.explode
fun maybe_quote_with keywords quote y =
  let val s = YXML.content_of y in
    y |> ((not (is_long_identifier (unquote_tvar s)) andalso
           not (is_long_identifier (unquery_var s))) orelse
           Keyword.is_literal keywords s) ? quote
  end

fun enclose ctxt thy =
  let
    val quote_type = Explorer_Lib.default_raw_params thy |> snd
  in
    (case quote_type of
       Explorer_Lib.GUILLEMOTS => maybe_quote_with (Thy_Header.get_keywords' ctxt) cartouche
     | Explorer_Lib.QUOTES => maybe_quote_with (Thy_Header.get_keywords' ctxt) quote)
  end

fun subgoal_text ctxt aim enclosure (fixes, _, goal) =
  let \<comment> \<open>modified\<close>
    val tag_opt = extract_tag_trm goal
    val kw_prefer = "preferT"
    val kw_prefer_opt = (case tag_opt of
      NONE => []
    | SOME tag => [kw_prefer, Syntax.string_of_term ctxt tag |> enclosure])
    val kw_subgoal = "subgoal"
    val kw_premises = "premises prems[tagged]"
    val kw_fix = "for"
    val kw_goal = "using prems apply tag"
    val kw_sorry = "sorry"
    val fixes_s = if null fixes then ""
      else kw_fix ^ " " ^ space_implode " "
        (map (fn (v, _) => v) fixes)
    val lines = map (space_implode " ")
      [
        kw_prefer_opt @ [kw_subgoal, kw_premises] @ (if fixes_s = "" then [] else [fixes_s]), \<comment> \<open>modified\<close>
        [kw_goal],
        [kw_sorry]
      ]
    in space_implode "\n  " lines end;

fun prefer_text ctxt aim enclosure (_, _, goal) = \<comment> \<open>modified/new\<close>
  let
    val tag_opt = extract_tag_trm goal
    val kw_prefer = "preferT"
    val kw_prefer_opt = (case tag_opt of
      NONE => []
    | SOME tag => [kw_prefer, Syntax.string_of_term ctxt tag |> enclosure])
    val kw_tac = "apply (tag)"
    val lines = map (space_implode " ")
      [
        kw_prefer_opt,
        [kw_tac]
      ]
    in space_implode "\n  " lines end;

fun generate_text SUBGOAL context enclosure clauses =
   let
     val lines = map (subgoal_text context SUBGOAL enclosure) clauses
   in (separate "" lines @ ["done"]) end
| generate_text PREFER context enclosure clauses =
   let
     val lines = map (prefer_text context PREFER enclosure) clauses
   in (separate "" lines @ ["done"]) end;

fun explore aim st =
  let
    val thy = Toplevel.theory_of st
    val ctxt = Toplevel.presentation_context st
    val enclosure = enclose ctxt thy
    val st = Toplevel.proof_of st
    val { context, facts = _, goal } = Proof.goal st;
    val goal_props = Logic.strip_imp_prems (Thm.prop_of goal);
    val clauses = map split_clause goal_props;
    val text = \<comment> \<open>modified\<close>
      cat_lines (generate_text aim context enclosure clauses);
    val message = Active.sendback_markup_properties [] text;
  in
    st
    |> tap (fn _ => Output.information ("Proof outline with cases:\n" ^ message))
  end

val explore_tagged_cmd = \<comment> \<open>modified\<close>
  Toplevel.keep_proof (K () o explore SUBGOAL)

val explore_tags_cmd = \<comment> \<open>modified\<close>
  Toplevel.keep_proof (K () o explore PREFER)

val _ = \<comment> \<open>modified\<close>
  Outer_Syntax.command @{command_keyword "explore_tagged_subgoals"}
    "explore current goal state as apply-style subgoals, tagging subgoals where appropriate"
    (Scan.succeed explore_tagged_cmd)

val _ = \<comment> \<open>modified\<close>
  Outer_Syntax.command @{command_keyword "explore_tags"}
    "explore current goal state as a number of \<open>preferT\<close> statements"
    (Scan.succeed explore_tags_cmd)
\<close>

ML \<open>
fun subgoal_text ctxt aim enclosure (fixes, _, goal) =
  let \<comment> \<open>modified\<close>
    val tag_opt = extract_tag_trm goal
    val kw_prefer = "preferT"
    val kw_prefer_opt = (case tag_opt of
      NONE => []
    | SOME tag => [kw_prefer, Syntax.string_of_term ctxt tag |> enclosure])
    val lines = map (space_implode " ")
      [
        kw_prefer_opt
      ]
    in space_implode "\n  " lines end;

fun generate_text SUBGOAL context enclosure clauses =
   let
     val lines = map (subgoal_text context SUBGOAL enclosure) clauses
   in (separate "" lines) end \<comment> \<open>modified\<close>

fun explore aim st =
  let
    val thy = Toplevel.theory_of st
    val ctxt = Toplevel.presentation_context st
    val enclosure = enclose ctxt thy
    val st = Toplevel.proof_of st
    val { context, facts = _, goal } = Proof.goal st;
    val goal_props = Logic.strip_imp_prems (Thm.prop_of goal);
    val clauses = map split_clause goal_props |> Library.chop 1 |> fst; \<comment> \<open>modified\<close>
    val text = \<comment> \<open>modified\<close>
      cat_lines (generate_text aim context enclosure clauses);
    val message = Active.sendback_markup_properties [] text;
  in
    st
    |> tap (fn _ => Output.information ("Proof outline with cases:\n" ^ message))
  end

val print_tag_cmd = \<comment> \<open>modified\<close>
  Toplevel.keep_proof (K () o explore SUBGOAL)

val _ = \<comment> \<open>modified\<close>
  Outer_Syntax.command @{command_keyword "print_tag"}
    "explore current goal state as apply-style subgoals, tagging subgoals where appropriate"
    (Scan.succeed print_tag_cmd)
\<close>

notepad begin
  fix t1 t2 :: 'a and P Q :: bool

  have [tagged]: "t1 \<bar> P" "Some t2 \<bar> Q"
    explore_tagged_subgoals
    explore_tags
    print_tag
    sorry

  have False
    using [[get_tagged \<open>t1\<close>]] \<^cancel>\<open>[[get_tagged \<open>t2\<close>]]\<close> [[get_tagged (2) (keep) \<open>Some _\<close>]]
    sorry

  have False
    usingT- (keep) \<open>''hi''\<close> \<open>Some _\<close> \<open>t1\<close>
    sorry

  have False
    apply (insertT \<open>''hi''\<close> \<open>Some _\<close> \<open>t1\<close>)
    sorry

  have [tagged]: "t1 \<bar> True" unfolding TAG_def ..

  have "False \<Longrightarrow> t1 \<bar> True"
    apply (tactic \<open>auto_insert_tac @{context} 1\<close>)
    by untag

  have "t1 \<bar> True"
    apply (insertT \<open>Some _\<close> \<open>''hi''\<close>)
    by untag

  have "t1 \<bar> True" "t2 \<bar> True"
     apply (untag, rule HOL.TrueI)+
    done

end

end
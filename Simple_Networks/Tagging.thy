section \<open>Tagged facts\<close>
theory Tagging
  imports Simple_Network_Language
  keywords "usingT"  :: prf_decl % "proof"
       and "preferT" :: prf_script % "proof"
begin

named_theorems tagged

subsection \<open>Prototyping Our Methods With Eisbach\<close>

ML \<open>
fun unfold_tac' ctxt rewrs =
  let
    val rewrs = map (Local_Defs.abs_def_rule ctxt) rewrs
  in
    rewrite_goal_tac ctxt rewrs
  end

fun insert'_meth ths ctxt = SIMPLE_METHOD' (Method.insert_tac ctxt ths)

fun unfold'_meth ths ctxt = SIMPLE_METHOD (CHANGED_PROP (unfold_tac' ctxt ths 1))
\<close>

method_setup insert' = \<open>Attrib.thms >> insert'_meth\<close> "insert theorems into first subgoal"

method_setup unfold' = \<open>Attrib.thms >> unfold'_meth\<close> "unfold definitions in first subgoal"

method tags' uses keep declares tagged =
  use nothing in \<open>insert' method_facts tagged\<close>,
  use nothing in \<open>tags del: TAG keep: keep, unfold' TAG_def, ((thin_tac True)+)?\<close>

lemma
  assumes "TAG ''tagged'' (x > 0)"
  shows "x > 0"
  using assms
  apply (tags' keep: TAG[of "''tagged''"] tagged: assms)
  apply assumption
  done

method tags uses keep declares tagged =
   match conclusion in "tag \<bar> P" for tag P \<Rightarrow>
     \<open>tags' keep: keep TAG[of tag] tagged: tagged\<close>
 | tags' keep: keep tagged: tagged

lemma
  assumes "''tagged'' \<bar> (x > 0)" and [tagged]: "''test'' \<bar> P" and "''test'' \<bar> Q" 
  shows "''tagged'' \<bar> x > 0"
  using assms(1)
  apply (tags keep: TAG[of "''test''"] tagged: assms(3))
  apply assumption
  done

method etag for tag uses keep declares tagged =
  tags keep: keep TAG[of tag] tagged: tagged

lemma
  assumes "''tagged'' \<bar> (x > 0)" and [tagged]: "''test'' \<bar> P" and "''test'' \<bar> Q" 
  shows "''tagged'' \<bar> x > 0"
  using assms(1)
  apply (etag "''test''" tagged: assms(3))
  apply assumption
  done


subsection \<open>Recalling Facts by Tag\<close>

ML \<open>
val empty = (Vartab.empty, Vartab.empty)

fun matches thy pat trm = (Pattern.match thy (pat, trm) empty; true)
  handle Pattern.MATCH => false

fun filter_thms thy pat = List.filter (fn thm => matches thy pat (Thm.prop_of thm))

fun filter_tagged thy tag =
  filter_thms thy (\<^instantiate>\<open>tag in term (schematic) \<open>Trueprop (tag \<bar> P)\<close>\<close>)

val tagged = Named_Theorems.check @{context} ("tagged", Position.none)

fun get_tagged ctxt tag =
  filter_tagged (Proof_Context.theory_of ctxt) tag (Named_Theorems.get ctxt tagged)

fun filter_thms_attr s = Thm.rule_attribute [] (fn context => fn _ =>
  let
    val ctxt = Context.proof_of context
    val pat = Proof_Context.read_term_pattern ctxt s
  in
    case get_tagged ctxt pat of
      [] => Drule.dummy_thm | (x :: _) => x
  end)

val get_tagged_state: string -> Proof.state -> Proof.state = fn s => fn st =>
  let
    val ctxt = Proof.context_of st
    val tag = Proof_Context.read_term_pattern ctxt s
    val thms = get_tagged ctxt tag
  in Proof.using [[(thms, [])]] st end

val get_tagged_trans = fold get_tagged_state

val auto_insert_tac = Subgoal.FOCUS (fn {context = ctxt, concl, ...} =>
  case Thm.term_of concl of
    \<^Const>\<open>Trueprop for \<^Const>\<open>TAG _ _ for tag _\<close>\<close> =>
      Method.insert_tac ctxt (get_tagged ctxt tag) 1
  | _ => no_tac
)

fun TRY' tac = tac ORELSE' K all_tac;

fun insert_tagged_meth xs ctxt =
  let
    val facts = flat (map (get_tagged ctxt) xs)
    val tac = Method.insert_tac ctxt facts THEN' TRY' (auto_insert_tac ctxt)
  in
    SIMPLE_METHOD' tac
  end

fun untag_tac ctxt = unfold_tac' ctxt @{thms TAG_def}
\<close>

ML \<open>
Outer_Syntax.command \<^command_keyword>\<open>usingT\<close> "use tagged facts"
  (Scan.repeat1 Parse.embedded_inner_syntax >> (Toplevel.proof o get_tagged_trans))
\<close>

method_setup insertT = \<open>Scan.repeat Args.term_pattern >> insert_tagged_meth\<close> "insert tagged facts"

method_setup untag =
  \<open>Args.context >> (fn _ => fn ctxt => SIMPLE_METHOD' (untag_tac ctxt))\<close> "remove tags"

attribute_setup get_tagged = \<open>Scan.lift Parse.embedded_inner_syntax  >> filter_thms_attr\<close>

notepad begin
  fix t1 t2 :: 'a and P Q :: bool

  have [tagged]: "t1 \<bar> P" "SEL t2 \<bar> Q"
    sorry

  have False
    using [[get_tagged \<open>t1\<close>]] [[get_tagged \<open>t2\<close>]] [[get_tagged \<open>SEL _\<close>]]
    sorry

  have False
    usingT \<open>''hi''\<close> \<open>SEL _\<close> \<open>t1\<close>
    sorry

  have False
    apply (insertT \<open>''hi''\<close> \<open>SEL _\<close> \<open>t1\<close>)
    sorry

  have [tagged]: "t1 \<bar> True" unfolding TAG_def ..

  have "False \<Longrightarrow> t1 \<bar> True"
    apply (tactic \<open>auto_insert_tac @{context} 1\<close>)
    by untag

  have "t1 \<bar> True"
    apply (insertT \<open>SEL _\<close> \<open>''hi''\<close>)
    by untag

  have "t1 \<bar> True" "t2 \<bar> True"
     apply (untag, rule HOL.TrueI)+
    done

end




subsection \<open>Deleting Assumptions\<close>

\<comment> \<open>How @{method thin_tac} does it.\<close>
lemma
  "x > 0 \<Longrightarrow> y > 0 \<Longrightarrow> z > 0"
  apply (tactic "eresolve_tac @{context} [Drule.thin_rl] 1")
  oops

lemma
  "x > 0 \<Longrightarrow> y > 0 \<Longrightarrow> z > 0"
  apply (erule Pure.thin_rl[where V = "y > 0"])
  oops


lemma thin_tag_rl:
  "TAG t V \<Longrightarrow> PROP W \<Longrightarrow> PROP W"
  by (rule thin_rl)

ML \<open>
fun thin_tag_tac ctxt s fixes =
  Rule_Insts.eres_inst_tac ctxt [((("t", 0), Position.none), s)] fixes @{thm thin_tag_rl};
\<close>

method_setup thin_tag =
  \<open>(Args.goal_spec -- Scan.lift (Parse.embedded_inner_syntax -- Parse.for_fixes) >>
      (fn (quant, (prop, fixes)) => fn ctxt =>
        SIMPLE_METHOD'' quant (thin_tag_tac ctxt prop fixes)))\<close>
  "filter me"

lemma
  "TAG t V \<Longrightarrow> TAG (SEL p) P \<Longrightarrow> TAG r U \<Longrightarrow> P"
  apply (thin_tag \<open>SEL _\<close>)
  oops

ML \<open>
fun del_tags_tac ctxt = REPEAT1 (eresolve_tac ctxt @{thms thin_tag_rl} 1)
\<close>

method_setup del_tags =
  \<open>Args.context >> (fn _ => fn ctxt => SIMPLE_METHOD (del_tags_tac ctxt))\<close> "test"

lemma
  "TAG t V \<Longrightarrow> TAG (SEL p) P \<Longrightarrow> TAG r U \<Longrightarrow> P"
  apply del_tags
  oops


subsection \<open>Main Tactics\<close>

ML \<open>
  fun instantiate_TAG ctxt (t: term) =
  let
    val ct = Thm.cterm_of ctxt t
  in (* XXX How infefficient is this? *)
    \<^instantiate>\<open>'t = \<open>Thm.ctyp_of_cterm ct\<close> and t = ct in
      lemma (schematic) \<open>(t \<bar> P) = TAG' t P\<close> for t :: 't by (rule TAG)\<close>
  end

fun protect_tag_tac ctxt s fixes i =
  let
    val thm = Rule_Insts.where_rule ctxt [((("t", 0), Position.none), s)] fixes @{thm TAG};
  in REPEAT1 (CHANGED_PROP (unfold_tac' ctxt [thm] i)) end

fun protect_tags_tac ctxt props fixes i =
  let
    fun mk_thm s =
      Rule_Insts.where_rule ctxt [((("t", 0), Position.none), s)] fixes @{thm TAG}
    val thms = map mk_thm props
  in REPEAT1 (CHANGED_PROP (unfold_tac' ctxt thms i)) end

fun filter_tags_tac ctxt props fixes =
  TRY (protect_tags_tac ctxt props fixes 1)
  THEN TRY (del_tags_tac ctxt)
  THEN TRY (unfold_tac' ctxt @{thms TAG'_def} 1)

fun mk_auto_insert_tac tac = SUBGOAL (fn (concl, i) =>
  case Logic.strip_imp_concl concl of
    \<^Const>\<open>Trueprop for \<^Const>\<open>TAG _ _ for tag _\<close>\<close> => tac [tag] i
  | _ => tac [] i
)

fun auto_filter_tags_and_insert_tac0 ctxt props fixes tags0 =
  let
    val tags = map (Proof_Context.read_term_pattern ctxt) props @ tags0
    val facts = flat (map (get_tagged ctxt) tags)
    val protect_eqs = map (instantiate_TAG ctxt) tags0
  in
    REPEAT (CHANGED_PROP (unfold_tac' ctxt protect_eqs 1))
    THEN filter_tags_tac ctxt props fixes
    THEN TRY (Method.insert_tac ctxt facts 1)
  end

fun auto_filter_tags_and_insert_tac ctxt props fixes =
  mk_auto_insert_tac
    (fn tags => fn _ => auto_filter_tags_and_insert_tac0 ctxt props fixes tags) 1

val props_fixes_parser: (string list * (binding * string option * mixfix) list) context_parser =
  Scan.lift (Scan.repeat Parse.embedded_inner_syntax -- Parse.for_fixes)
\<close>

method_setup protect_tag =
  \<open>(Scan.lift (Parse.embedded_inner_syntax -- Parse.for_fixes) >>
      (fn (prop, fixes) => fn ctxt => SIMPLE_METHOD' (protect_tag_tac ctxt prop fixes)))\<close>
  "TAG \<rightarrow> TAG' (single)"

method_setup protect_tags =
  \<open>props_fixes_parser >>
     (fn (props, fixes) => fn ctxt => SIMPLE_METHOD' (protect_tags_tac ctxt props fixes))\<close>
  "TAG \<rightarrow> TAG' (multiple)"

method_setup filter_tags =
  \<open>props_fixes_parser >>
     (fn (props, fixes) => fn ctxt => SIMPLE_METHOD (filter_tags_tac ctxt props fixes))\<close>
  "Filter tagged facts"

method_setup tag0 =
  \<open>props_fixes_parser >>
     (fn (props, fixes) => fn ctxt =>
        SIMPLE_METHOD (auto_filter_tags_and_insert_tac ctxt props fixes))\<close>
  "Filter tagged facts and insert matching tagged facts, taking goal tag into account"

method_setup tag =
  \<open>props_fixes_parser >>
     (fn (props, fixes) => fn ctxt =>
        SIMPLE_METHOD (
               auto_filter_tags_and_insert_tac ctxt props fixes
          THEN unfold_tac' ctxt @{thms TAG_def} 1))\<close>
  "Like tags0 but removing tags in the end"

lemma
  "TAG t V \<Longrightarrow> TAG (SEL p) P \<Longrightarrow> TAG r U \<Longrightarrow> P"
  apply (protect_tags \<open>SEL x\<close> t for x, del_tags, unfold' TAG'_def)
  oops

lemma
  "TAG t V \<Longrightarrow> TAG (SEL p) P \<Longrightarrow> TAG r U \<Longrightarrow> P"
  apply (filter_tags \<open>SEL x\<close> t for x)
  oops

lemma [tagged]: "SEL ''s'' \<bar> True" unfolding TAG_def ..
lemma [tagged]: "SEL u \<bar> True" unfolding TAG_def ..

lemma
  "TAG t V \<Longrightarrow> TAG (SEL p) P \<Longrightarrow> TAG r U \<Longrightarrow> P"
  \<comment> \<open>XXX: The first three fail to recall facts from \<open>tagged\<close>.
      We would need to read the variables (and generalize them again) like in \<open>rule_insts.ML\<close>.\<close>
  apply (tag0 \<open>SEL x\<close> t for x)
  apply (tag \<open>SEL u\<close> t for u)
  apply (tag \<open>SEL s\<close> t for s :: string)
  apply (insertT \<open>SEL _\<close>)
  apply (tag \<open>SEL _\<close>)
  oops

lemma [tagged]: "''hi'' \<bar> True" unfolding TAG_def ..

lemma
  "TAG t V \<Longrightarrow> TAG (SEL p) P \<Longrightarrow> TAG ''hi'' U \<Longrightarrow> TAG ''hi'' P"
  apply (tag t)
  apply (tactic \<open>prefer_tac 1\<close>)
  prefer 1
  oops


subsection \<open>Reordering Subgoals\<close>

ML \<open>
(* Find index of first subgoal in thm whose conclusion matches pred *)
fun find_subgoal pred thm =
  let
    val subgoals = Thm.prems_of thm
  in
    Library.find_index (fn goal => pred (Logic.strip_imp_concl goal)) subgoals
  end

fun prefer_by_pred_tac pred: tactic = fn thm =>
  let
    val i = find_subgoal pred thm + 1
  in
    if i > 0 then Tactic.prefer_tac i thm else no_tac thm
  end

fun prefer_by_pat_tac thy pat: tactic =
  prefer_by_pred_tac (matches thy pat)

fun prefer_by_tag_tac thy tag: tactic =
  prefer_by_pat_tac thy (\<^instantiate>\<open>tag in term (schematic) \<open>Trueprop (tag \<bar> P)\<close>\<close>)
\<close>

lemma
  "TAG p P" "TAG q Q" "TAG r R" "TAG p P2"
  apply -
     apply (tactic \<open>prefer_by_pat_tac @{theory} @{term_pat "Trueprop (TAG r _)"}\<close>)
     apply (tactic \<open>prefer_by_pat_tac @{theory} @{term_pat "Trueprop (TAG p _)"}\<close>)
  apply (tactic \<open>prefer_by_tag_tac @{theory} \<^term>\<open>q\<close>\<close>)
  oops

ML \<open>
fun prefer_tag pat st =
  let
    val st = Proof.assert_no_chain st
    val thy = Proof.theory_of st
  in
    Proof.refine_singleton (Method.Basic (fn _ => METHOD (fn _ => prefer_by_tag_tac thy pat))) st
  end

val prefer_tag_trans: string -> Proof.state -> Proof.state = fn s => fn st =>
  let
    val ctxt = Proof.context_of st
    val tag = Proof_Context.read_term_pattern ctxt s
  in prefer_tag tag st end
\<close>

ML \<open>Outer_Syntax.command \<^command_keyword>\<open>preferT\<close> "select subgoal by tag"
  (Parse.embedded_inner_syntax >> (Toplevel.proof o prefer_tag_trans))
\<close>

lemma
  "TAG p P" "TAG q Q" "TAG r R" "TAG p P2"
     apply -
     preferT \<open>p\<close>
  oops

end
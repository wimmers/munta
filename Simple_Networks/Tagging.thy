section \<open>Tagged facts\<close>
theory Tagging
  imports Main "HOL-Eisbach.Eisbach"
  keywords "usingT"  :: prf_decl % "proof"
       and "preferT" :: prf_script % "proof"
       and "print_tags" :: diag
begin

subsection \<open>Tags\<close>

definition TAG ("_ \<bar> _" [8, 8] 9) where
  \<open>TAG t x = x\<close>

definition
  "TAG' t x = TAG t x"

lemmas TAG = TAG'_def[symmetric]

lemmas add_tag = TAG_def[symmetric]

named_theorems tagged


subsection \<open>Prototyping Our Methods With Eisbach\<close>

lemma rm_TAG:
  assumes "TAG t x" "TAG t x = TAG' t x"
  shows True
  by auto

method tags0 uses del keep =
  (unfold keep)?,
  ((drule rm_TAG, rule del)+)?,
  (unfold keep[symmetric])?

lemma
  assumes "TAG 1 False" "TAG (Some STR ''remove'') (x > 0)"
  shows False
  using assms
  apply -
  apply (tags0 del: TAG[of "Some t" for t] TAG[of 1] keep: TAG[of 1])
  unfolding TAG_def .

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
  use nothing in \<open>tags0 del: TAG keep: keep, unfold' TAG_def, ((thin_tac True)+)?\<close>

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

lemmas add_TAG = TAG_def[THEN eq_reflection, symmetric]

lemma re_TAG:
  "(t \<bar> P) \<equiv> (t_new \<bar> P)"
  unfolding TAG_def .

ML \<open>
fun mk_add_tag_thm t =
  \<^instantiate>\<open>'t = \<open>Thm.ctyp_of_cterm t\<close> and t = t in
    lemma (schematic) \<open>y \<equiv> t \<bar> y\<close> for t :: 't by (rule add_TAG)\<close>
fun mk_re_tag_thm t =
  \<^instantiate>\<open>'t = \<open>Thm.ctyp_of_cterm t\<close> and t_new = t in
    lemma (schematic) \<open>(t_old \<bar> P) \<equiv> (t_new \<bar> P)\<close> for t_new :: 't by (rule re_TAG)\<close>
fun lift_conv conv =
  conv |> Conv.rewr_conv |> Conv.arg_conv |> Conv.concl_conv 100 |> K |> Conv.params_conv 100
fun add_tag_conv ct = mk_add_tag_thm ct |> lift_conv
fun re_tag_conv ct  = mk_re_tag_thm ct |> lift_conv
fun tag_thm ct ctxt = Conv.fconv_rule (add_tag_conv ct ctxt)
fun re_tag_thm ct ctxt = Conv.fconv_rule (Conv.try_conv (re_tag_conv ct ctxt))

fun extract_tag_trm trm =
  case trm of
    \<^Const>\<open>Trueprop for \<^Const>\<open>TAG _ _ for tag _\<close>\<close> => SOME tag
  | _ => NONE

val empty = (Vartab.empty, Vartab.empty)

fun matches thy pat trm = (Pattern.match thy (pat, trm) empty; true)
  handle Pattern.MATCH => false

fun matches_tag0 thy tag =
  matches thy (\<^instantiate>\<open>tag in term (schematic) \<open>Trueprop (tag \<bar> P)\<close>\<close>)

fun matches_tag thy tag goal =
  case extract_tag_trm goal of
      NONE => false
    | SOME t => matches thy tag t

fun filter_thms thy pat = List.filter (fn thm => matches thy pat (Thm.prop_of thm))

fun filter_tagged thy tag =
  List.filter (fn thm => matches_tag thy tag (Thm.prop_of thm))

val tagged = Named_Theorems.check @{context} ("tagged", Position.none)

fun get_tagged ctxt tag =
  filter_tagged (Proof_Context.theory_of ctxt) tag (Named_Theorems.get ctxt tagged)

fun err ctxt trm pos msg =
  error (msg ^ Position.here pos ^ ":\n" ^ Syntax.string_of_term ctxt trm);

fun check_single ctxt tag pos thms = case thms of
  [x] => [x]
| [] => err ctxt tag pos "No fact with tag"
| _  => err ctxt tag pos "Ambiguous tag"

fun get_tagged_single ctxt pos tag = get_tagged ctxt tag |> check_single ctxt tag pos

fun check_at_least_one ctxt tag pos thms = case thms of
  [] => err ctxt tag pos "No fact with tag"
| xs => xs

fun get_tagged_at_least_one ctxt pos tag = get_tagged ctxt tag |> check_at_least_one ctxt tag pos

fun unfold_tags ctxt = Local_Defs.unfold ctxt @{thms TAG_def}

fun filter_thms_attr ((opt_num, keep_tags), s) = Thm.rule_attribute [] (fn context => fn _ =>
  let
    val pos = Syntax.read_input_pos s
    val ctxt = Context.proof_of context
    val pat = Proof_Context.read_term_pattern ctxt s
    val facts = (
      if opt_num = NONE then
        get_tagged_single ctxt pos pat
      else
        get_tagged_at_least_one ctxt pos pat)
    val post_fact = if keep_tags then I else unfold_tags ctxt
  in
    case opt_num of
      NONE => List.hd facts |> post_fact
    | SOME i =>
      if length facts >= i andalso i > 0 then
        Library.nth facts (i - 1)
      else err ctxt pat pos ("Index " ^ string_of_int i ^ " out of range")
  end)

fun tag_thms_attr ((keep_tags,retag), s) = Thm.mixed_attribute (fn (context, thm) =>
  let
    val ctxt = Context.proof_of context
    val ct = Syntax.read_term ctxt s |> Thm.cterm_of ctxt
    val thm = if retag then re_tag_thm ct ctxt thm else tag_thm ct ctxt thm
    val context = Named_Theorems.add_thm tagged thm context
    val thm = if keep_tags then thm else unfold_tags ctxt thm
  in
    (context, thm)
  end)

val untagged_attr = Thm.rule_attribute [] (fn context => unfold_tags (Context.proof_of context))

fun get_tagged_state strict keep_tags s: Proof.state -> Proof.state = fn st =>
  let
    val pos = Syntax.read_input_pos s
    val ctxt = Proof.context_of st
    val tag = Proof_Context.read_term_pattern ctxt s
    val thms = (if strict then get_tagged_single else get_tagged_at_least_one) ctxt pos tag
    val thms = if keep_tags then thms else map (unfold_tags ctxt) thms
  in Proof.using [[(thms, [])]] st end

fun get_tagged_trans ((non_strict, keep_tags), xs) =
  fold (get_tagged_state (not non_strict) keep_tags) xs

val auto_insert_tac = Subgoal.FOCUS (fn {context = ctxt, concl, ...} =>
  case Thm.term_of concl of
    \<^Const>\<open>Trueprop for \<^Const>\<open>TAG _ _ for tag _\<close>\<close> =>
      Method.insert_tac ctxt (get_tagged ctxt tag) 1
  | _ => no_tac
)

fun TRY' tac = tac ORELSE' K all_tac;

fun insert_tagged_meth xs ctxt =
  let
    val facts = flat (map (fn (pos, tag) => get_tagged_at_least_one ctxt pos tag) xs)
    val tac = Method.insert_tac ctxt facts THEN' TRY' (auto_insert_tac ctxt)
  in
    SIMPLE_METHOD' tac
  end

fun untag_tac ctxt = unfold_tac' ctxt @{thms TAG_def}
\<close>

ML \<open>
val position_parser: Position.T parser = Scan.ahead Parse.not_eof >> Token.pos_of
val position_ctxt_parser: Position.T context_parser = Scan.lift position_parser
val parse_non_strict: bool parser = Scan.optional (Args.$$$ "-" >> K true) false
\<close>

ML \<open>
Outer_Syntax.command \<^command_keyword>\<open>usingT\<close> "use tagged facts"
  (parse_non_strict -- Args.mode "keep" -- Scan.repeat1 Parse.embedded_inner_syntax
    >> (Toplevel.proof o get_tagged_trans))
\<close>

method_setup insertT =
  \<open>Scan.repeat (position_ctxt_parser -- Args.term_pattern) >> insert_tagged_meth\<close>
  "insert tagged facts"

method_setup untag =
  \<open>Args.context >> (fn _ => fn ctxt => SIMPLE_METHOD' (untag_tac ctxt))\<close> "remove tags"

attribute_setup get_tagged =
  \<open>Scan.lift (Scan.option (Args.parens Parse.nat) -- Args.mode "keep" -- Parse.embedded_inner_syntax)
    >> filter_thms_attr\<close>

attribute_setup tag =
  \<open>Scan.lift (Args.mode "keep" -- Args.mode "re" -- Parse.embedded_inner_syntax) >> tag_thms_attr\<close>

attribute_setup untagged =
  \<open>Scan.succeed () >> (fn _ => untagged_attr)\<close>

notepad begin
  fix t1 t2 :: 'a and P Q :: bool

  have [tagged]: "t1 \<bar> P" "Some t2 \<bar> Q"
    sorry

  have False
    using [[get_tagged \<open>t1\<close>]] \<^cancel>\<open>[[get_tagged \<open>t2\<close>]]\<close> [[get_tagged \<open>Some _\<close>]]
    sorry

  have False thm tagged
    usingT \<^cancel>\<open>\<open>''hi''\<close>\<close> \<open>Some _\<close> \<open>t1\<close>
    sorry

  have False
    apply (insertT \<^cancel>\<open>\<open>''hi''\<close>\<close> \<open>Some _\<close> \<open>t1\<close>)
    sorry

  have [tagged]: "t1 \<bar> True" unfolding TAG_def ..

  thm [[get_tagged (1) \<open>t1\<close>]]

  \<comment> \<open>Note that these next three are not actually retrievable later.\<close>
  have test[tag (re) \<open>''tag''\<close>]: "True" "x = x" "tt \<bar> y = y" if "x > 0" for x y tt :: nat
    unfolding TAG_def by auto
  thm tagged thm test

  have test[tag \<open>''tag''\<close>]: "True" "x = x" "tt \<bar> y = y" if "x > 0" for x y tt :: nat
    unfolding TAG_def by auto
  thm tagged thm test

  have test[tag (keep) \<open>''tag''\<close>]: "True" "x = x" "tt \<bar> y = y" if "x > 0" for x y tt :: nat
    unfolding TAG_def by auto thm test

  thm tagged[untagged] thm tagged

  have "False \<Longrightarrow> t1 \<bar> True"
    apply (tactic \<open>auto_insert_tac @{context} 1\<close>)
    by untag

  have "t1 \<bar> True"
    apply (insertT \<open>Some _\<close> \<^cancel>\<open>\<open>''hi''\<close>\<close> \<^cancel>\<open>\<open>t1\<close>\<close>)
    by untag

  have "t1 \<bar> True" "t2 \<bar> True"
    apply (untag, rule HOL.TrueI)+
    usingT - \<^cancel>\<open>\<open>''hi''\<close>\<close> \<open>Some _\<close> \<open>t1\<close>
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
  "TAG t V \<Longrightarrow> TAG (Some p) P \<Longrightarrow> TAG r U \<Longrightarrow> P"
  apply (thin_tag \<open>Some _\<close>)
  oops

ML \<open>
fun del_tags_tac ctxt = REPEAT1 (eresolve_tac ctxt @{thms thin_tag_rl} 1)
\<close>

method_setup del_tags =
  \<open>Args.context >> (fn _ => fn ctxt => SIMPLE_METHOD (del_tags_tac ctxt))\<close> "test"

lemma
  "TAG t V \<Longrightarrow> TAG (Some p) P \<Longrightarrow> TAG r U \<Longrightarrow> P"
  apply del_tags
  oops


subsection \<open>Main Tactics\<close>

ML \<open>
fun instantiate_TAG ctxt (t: term) =
let
  val ct = Thm.cterm_of ctxt t
in (* XXX How inefficient is this? *)
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
  case concl |> Logic.strip_assums_concl |> extract_tag_trm of
    SOME tag => tac [tag] i
  | _ => tac [] i
)

fun auto_filter_tags_and_insert_tac0 strict ctxt props fixes tags0 =
  let
    val pos_tags = map
      (fn s => (Syntax.read_input_pos s, Proof_Context.read_term_pattern ctxt s))
      props
    val get_fact =
      if strict then
        fn (pos, t) => get_tagged_at_least_one ctxt pos t
      else
        fn (_, t) => get_tagged ctxt t
    val facts = flat (map get_fact pos_tags) @ flat (map (get_tagged ctxt) tags0)
    val protect_eqs = map (instantiate_TAG ctxt) tags0
  in
    REPEAT (CHANGED_PROP (unfold_tac' ctxt protect_eqs 1))
    THEN filter_tags_tac ctxt props fixes
    THEN TRY (Method.insert_tac ctxt facts 1)
  end

fun auto_filter_tags_and_insert_tac strict ctxt props fixes =
  mk_auto_insert_tac
    (fn tags => fn _ => auto_filter_tags_and_insert_tac0 strict ctxt props fixes tags) 1

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
  \<open>Scan.lift parse_non_strict -- props_fixes_parser >>
     (fn (non_strict, (props, fixes)) => fn ctxt =>
        SIMPLE_METHOD (auto_filter_tags_and_insert_tac (not non_strict) ctxt props fixes))\<close>
  "Filter tagged facts and insert matching tagged facts, taking goal tag into account"

method_setup tag =
  \<open>Scan.lift parse_non_strict -- props_fixes_parser >>
     (fn (non_strict, (props, fixes)) => fn ctxt =>
        SIMPLE_METHOD (DETERM (
               auto_filter_tags_and_insert_tac (not non_strict) ctxt props fixes
          THEN unfold_tac' ctxt @{thms TAG_def} 1)))\<close>
  "Like tags0 but removing tags in the end"

lemma
  "TAG t V \<Longrightarrow> TAG (Some p) P \<Longrightarrow> TAG r U \<Longrightarrow> P"
  apply (protect_tags \<open>Some x\<close> t for x, del_tags, unfold' TAG'_def)
  oops

lemma
  "TAG t V \<Longrightarrow> TAG (Some p) P \<Longrightarrow> TAG r U \<Longrightarrow> P"
  apply (filter_tags \<open>Some x\<close> t for x)
  oops

lemma [tagged]: "Some ''s'' \<bar> True" unfolding TAG_def ..
lemma [tagged]: "Some u \<bar> True" unfolding TAG_def ..

lemma
  "TAG t V \<Longrightarrow> TAG (Some p) P \<Longrightarrow> TAG r U \<Longrightarrow> P"
  \<comment> \<open>XXX: The first three fail to recall facts from \<open>tagged\<close>.
      We would need to read the variables (and generalize them again) like in \<open>rule_insts.ML\<close>.\<close>
\<^cancel>\<open>  apply (tag0 \<open>Some x\<close> t for x)
  apply (tag \<open>Some u\<close> t for u)
  apply (tag \<open>Some s\<close> t for s :: string)\<close>
  apply (insertT \<open>Some _\<close>)
  apply (tag \<open>Some _\<close>)
  oops

lemma [tagged]: "''hi'' \<bar> True" unfolding TAG_def ..

lemma
  "\<And>tt. TAG t V \<Longrightarrow> TAG (Some p) P \<Longrightarrow> TAG ''hi'' U \<Longrightarrow> TAG ''hi'' P"
  apply (tag- t)
  oops


subsection \<open>Reordering Subgoals\<close>

ML \<open>
(* Find index of first subgoal in thm whose conclusion matches pred *)
fun find_subgoal pred thm =
  let
    val subgoals = Thm.prems_of thm
  in
    Library.find_index (fn goal => pred (Logic.strip_assums_concl goal)) subgoals
  end

fun prefer_by_pred_tac pred: tactic = fn thm =>
  let
    val i = find_subgoal pred thm + 1
  in
    if i > 0 then Tactic.prefer_tac i thm else no_tac thm
  end

fun prefer_by_tag_tac0 thy tag: tactic =
  prefer_by_pred_tac (matches_tag0 thy tag)

fun prefer_by_tag_tac thy tag: tactic =
  prefer_by_pred_tac (matches_tag thy tag)
\<close>

lemma
  "TAG p P" "TAG q Q" "TAG r R" "TAG p P2"
  apply -
     apply (tactic \<open>prefer_by_tag_tac0 @{theory} \<^term>\<open>r\<close>\<close>)
     apply (tactic \<open>prefer_by_tag_tac0 @{theory} \<^term>\<open>p\<close>\<close>)
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
     preferT \<open>r\<close>
  oops

lemma
  "\<And>t. TAG p P \<and> TAG q Q"
  apply (rule conjI)
   preferT \<open>q\<close>
  oops


subsection \<open>Diagnostic Commands\<close>

ML \<open>
val extract_tag_thm = extract_tag_trm o Thm.prop_of

fun tags_of_tagged ctxt =
  let
    val thms = Named_Theorems.get ctxt tagged
  in
    Library.map_filter extract_tag_thm thms
  end

fun pretty_term_item ctxt trm = Pretty.item [Syntax.pretty_term ctxt trm]

fun string_of_tags ctxt () =
  let
    val tags = tags_of_tagged ctxt
    val pretty_tags = map (pretty_term_item ctxt) tags
    val pretty = Pretty.blk (0, Pretty.fbreaks pretty_tags)
  in
    Pretty.string_of pretty
  end

\<comment> \<open>From \<open>Pure.thy\<close>\<close>
val opt_modes =
  Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.!!! (Scan.repeat1 Parse.name --| \<^keyword>\<open>)\<close>)) [];

\<comment> \<open>From \<open>isar_cmd.ml\<close>\<close>
fun print_item string_of (modes, arg) = Toplevel.keep (fn state =>
  Print_Mode.with_modes modes (fn () => writeln (string_of state arg)) ());

val print_tags = print_item (string_of_tags o Toplevel.context_of);
\<close>

ML \<open>
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_tags\<close>
    "print tags of theorems in collection 'tagged'"
    (opt_modes -- Scan.succeed () >> print_tags);
\<close>

print_tags

end
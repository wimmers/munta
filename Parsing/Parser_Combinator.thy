(* Author: Peter Lammich *)
chapter \<open>Parsing\<close>
section \<open>Parser Combinators\<close>

theory Parser_Combinator
imports
  "HOL-Library.Monad_Syntax"
  "HOL-Library.Char_ord"
  "HOL-Library.Code_Target_Nat"
  "Certification_Monads.Error_Monad"
  Error_Monad_Add
  "Show.Show"
  "HOL-Library.Rewrite"
begin

  (**
    Parser Combinators, based on Sternagel et Thiemann's Parser_Monad, with the following additional features/differences:

    * Setup for the function package, to handle recursion
      parser uses fuel to ensure termination.
    * Uses (unit \<Rightarrow> shows) for error messages instead of String (lazy computation of messages, more comfortable due to shows)
    * Everything defined over generic token type
    * Some fancy combinators
        a \<parallel> b    choice, type a = type b
        --[f]    sequential composition, combine results with f
        --       = --[Pair]
        --*      seq, ignore right result
        *--      seq, ignore left result

    TODO/FIXME

    * Currently, the bind and repeat operation dynamically check whether input is consumed and then fail.
      At least for bind (no input is generated), we could try to encode this information into the parser's type.
      However, interplay with function package is not clear at this point :(
      Possible solution: Fixed-point based recursion combinator and partial_function. We could then do totality proof afterwards.


  *)


subsection \<open>Type Definitions\<close>

datatype 'a len_list = LL (ll_fuel: nat) (ll_list: "'a list")
definition "ll_from_list l \<equiv> LL (length l) l"

lemma [measure_function]: "is_measure ll_fuel" by rule

text \<open>
  A parser takes a list of tokes and returns either an error message or
  a result together with the remaining tokens.
\<close>

type_synonym
  ('t, 'a) parser = "'t len_list \<Rightarrow> (unit \<Rightarrow> shows) + ('a \<times> 't len_list)"

text \<open>A \emph{consuming parser} (cparser for short) consumes at least one token of input.\<close>
definition is_cparser :: "('t,'a) parser \<Rightarrow> bool"
where
  "is_cparser p \<longleftrightarrow> (\<forall>l l' x. p l = Inr (x,l') \<longrightarrow> ll_fuel l' < ll_fuel l)"

lemma is_cparserI:
  assumes "\<And>l l' x. p l = Inr (x, l') \<Longrightarrow> ll_fuel l' < ll_fuel l"
  shows "is_cparser p"
  using assms unfolding is_cparser_def by blast

lemma is_cparserE:
  assumes "is_cparser p"
    and "(\<And>l l' x. p l = Inr (x, l') \<Longrightarrow> ll_fuel l' < ll_fuel l) \<Longrightarrow> P"
  shows "P"
  using assms by (auto simp: is_cparser_def; blast)

lemma is_cparser_length[simp, dest]:
  assumes "p l = Inr (x, l')" and "is_cparser p"
  shows "ll_fuel l' < ll_fuel l"
  using assms by (blast elim: is_cparserE)

text \<open>Used by fundef congruence rules\<close>
definition "PCONG_INR x ts' \<equiv> Inr (x,ts')"

lemma PCONG_EQ_D[dest!]:
  assumes "p l = PCONG_INR x l'"
  assumes "is_cparser p"
  shows "ll_fuel l' < ll_fuel l"
  using assms unfolding PCONG_INR_def by auto

named_theorems parser_rules

lemmas parser0_rules = disjI1 disjI2 allI impI conjI

thm disjI2 asm_rl


ML \<open>
  structure Parser_Combinator = struct

    val cfg_simproc = Attrib.setup_config_bool @{binding parser_simproc} (K true)

    val cfg_debug = Attrib.setup_config_bool @{binding parser_debug} (K false)

    fun trace_tac ctxt msg = if Config.get ctxt cfg_debug then print_tac ctxt msg else all_tac
    fun trace_tac' ctxt msg i =
      if Config.get ctxt cfg_debug then
        print_tac ctxt (msg ^ " on subgoal " ^ Int.toString i)
      else all_tac

    fun prove_cparser_step_tac ctxt =
      let
        val p_rls = Named_Theorems.get ctxt @{named_theorems parser_rules}
      in
        trace_tac' ctxt "prove_cparser_step" THEN'
        (
          resolve_tac ctxt (@{thms parser0_rules} @ p_rls)
          ORELSE' SOLVED' (asm_simp_tac ctxt)
        )
      end


    fun prove_cparser_tac ctxt =
      trace_tac ctxt "prove_cparser" THEN
      DEPTH_SOLVE (FIRSTGOAL (prove_cparser_step_tac ctxt))

    fun add_cparser_def def_thm context = let
      val ctxt = Context.proof_of context
      val orig_ctxt = ctxt

      val ctxt = Config.put cfg_simproc false ctxt

      val (def_thm, ctxt) = yield_singleton (apfst snd oo Variable.import true) def_thm ctxt

      val lhs = def_thm
        |> Local_Defs.meta_rewrite_rule ctxt
        |> (fst o Logic.dest_equals o Thm.prop_of)

      val T = fastype_of lhs
      val cp_stmt =
           Const (@{const_name is_cparser}, T --> HOLogic.boolT)$lhs
        |> HOLogic.mk_Trueprop

      fun is_cparser_free (@{const Trueprop} $ (Const (@{const_name is_cparser},_) $ Free _)) = true
        | is_cparser_free _ = false

      fun is_goal_ok st =
        Thm.prop_of st |> Logic.strip_imp_prems
        |> map (Logic.strip_assums_concl)
        |> forall is_cparser_free

      val cp_thm =
        cp_stmt |> Thm.cterm_of ctxt
        |> Goal.init
        |> SINGLE (
            unfold_tac ctxt [def_thm] THEN
            trace_tac ctxt "cparser def proof" THEN
            DEPTH_FIRST is_goal_ok (
              FIRSTGOAL (prove_cparser_step_tac ctxt)
            )
          )

      val cp_thm = case cp_thm of
        NONE => error "Could not prove any is_cparser theorem: Empty result sequence"
      | SOME thm =>
          Goal.conclude thm


      val cp_thm =
           singleton (Variable.export ctxt orig_ctxt) cp_thm
        |> Drule.zero_var_indexes

      (*
      val cp_thm =
        Goal.prove ctxt [] [] cp_stmt (fn {context, ...} => tac context)
      |> singleton (Variable.export ctxt orig_ctxt)
      *)

      val context = Named_Theorems.add_thm @{named_theorems parser_rules} cp_thm context
    in
      context
    end
  end
\<close>


attribute_setup consuming = \<open>
  Scan.succeed (Thm.declaration_attribute (Parser_Combinator.add_cparser_def))
\<close>

simproc_setup is_cparser_prover ("is_cparser p") = \<open>fn _ => fn ctxt => fn ct =>
  if Config.get ctxt Parser_Combinator.cfg_simproc then
    let
      open Parser_Combinator
      val t = Thm.term_of ct
      val stmt = Logic.mk_equals (t,@{term True})

      val _ = if Config.get ctxt cfg_debug then
          (Pretty.block [Pretty.str "is_cparser simproc invoked on: ", Syntax.pretty_term ctxt t, Pretty.fbrk, Syntax.pretty_term ctxt stmt]) |> Pretty.string_of |> tracing
        else ()

      val ctxt = Config.put Parser_Combinator.cfg_simproc false ctxt

      val othm = try (Goal.prove ctxt [] [] stmt) (fn {context=ctxt, ...} =>
        FIRSTGOAL (resolve_tac ctxt @{thms HOL.Eq_TrueI})
        THEN TRY (Parser_Combinator.prove_cparser_tac ctxt)
      )

      val _ =
        if Config.get ctxt cfg_debug andalso is_none othm then
          (Pretty.block [Pretty.str "is_cparser simproc failed on: ", Syntax.pretty_term ctxt t, Pretty.fbrk, Syntax.pretty_term ctxt stmt]) |> Pretty.string_of |> tracing
        else ()

      (*
      val _ = case othm of
        NONE => (Pretty.block [Pretty.str "is_cparser simproc failed on: ", Syntax.pretty_term ctxt t, Pretty.fbrk, Syntax.pretty_term ctxt stmt]) |> Pretty.string_of |> warning
     | SOME _ => ();
      *)
    in
      othm
    end
  else
    NONE
\<close>

text \<open>Wrapping a parser to dynamically assert that it consumes tokens.\<close>
definition ensure_cparser :: "('t,'a) parser \<Rightarrow> ('t,'a) parser" where
  "ensure_cparser p \<equiv> \<lambda>ts. do {
    (x, ts') \<leftarrow> p ts;
    if (ll_fuel ts' < ll_fuel ts) then Error_Monad.return (x,ts')
    else Error_Monad.error (\<lambda>_. shows ''Dynamic parser check failed'')
  }"

lemma ensure_cparser_cparser[parser_rules]: "is_cparser (ensure_cparser p)"
  apply (rule is_cparserI)
  unfolding ensure_cparser_def
  by (auto simp: Error_Monad.bind_def split: sum.splits if_splits)

lemma ensure_cparser_cong[fundef_cong]:
  assumes "l=l'"
  assumes "p l = p' l'"
  shows "ensure_cparser p l = ensure_cparser p' l'"
  using assms by (auto simp: ensure_cparser_def)


abbreviation bnf_eq :: "('t,'a) parser \<Rightarrow> ('t,'a) parser \<Rightarrow> prop" (infix "::=" 2) where
  "bnf_eq p1 p2 \<equiv> (\<And>l. p1 l = p2 l)"



subsection \<open>Monad-Setup for Parsers\<close>

definition return :: "'a \<Rightarrow> ('t, 'a) parser"
where
  "return x = (\<lambda>ts. Error_Monad.return (x, ts))"

definition error_aux :: "(unit \<Rightarrow> shows) \<Rightarrow> ('t, 'a) parser"
where
  "error_aux e = (\<lambda>_. Error_Monad.error e)"

abbreviation error where "error s \<equiv> error_aux (ERR s)"
abbreviation "error_str s \<equiv> error_aux (ERRS s)"

definition update_error :: "('t,'a) parser \<Rightarrow> (shows \<Rightarrow> shows) \<Rightarrow> ('t,'a) parser"
  where "update_error m f l \<equiv> m l <+? (\<lambda>e _. f (e ()))"

definition ensure_parser :: "('t,'a) parser \<Rightarrow> ('t,'a) parser" where
  "ensure_parser p \<equiv> \<lambda>ts. do {
    (x, ts') \<leftarrow> p ts;
    if (ll_fuel ts' \<le> ll_fuel ts) then Error_Monad.return (x,ts')
    else Error_Monad.error (ERRS ''Dynamic parser check failed'')
  }"

definition bind :: "('t, 'a) parser \<Rightarrow> ('a \<Rightarrow> ('t, 'b) parser) \<Rightarrow> ('t, 'b) parser"
where
  "bind m f \<equiv> \<lambda>ts. do {
    (x, ts) \<leftarrow> ensure_parser m ts;
    ensure_parser (f x) ts
  }"

definition get :: "('t,'t) parser" where
  "get ll \<equiv> case ll of LL (Suc n) (x#xs) \<Rightarrow> Error_Monad.return (x,LL n xs) | _ \<Rightarrow> (Error_Monad.error (\<lambda>_. shows_string ''Expecting more input''))"

definition get_tokens :: "('t,'t list) parser" where
  "get_tokens \<equiv> \<lambda>ll. Error_Monad.return (ll_list ll,ll)"

adhoc_overloading
      Monad_Syntax.bind bind
  and Error_Syntax.update_error update_error

(* TODO: Specialize to parser type? *)
lemma let_cong' [fundef_cong]:
  "M = N \<Longrightarrow> l=l' \<Longrightarrow> (\<And>x. x = N \<Longrightarrow> f x l' = g x l') \<Longrightarrow> Let M f l = Let N g l'"
  unfolding Let_def by blast

lemma if_cong' [fundef_cong]:
  assumes "b = c"
    and "l=l'"
    and "c \<Longrightarrow> x l' = u l'"
    and "\<not> c \<Longrightarrow> y l' = v l'"
  shows "(if b then x else y) l = (if c then u else v) l'"
  using assms by simp

lemma split_cong' [fundef_cong]:
  "l=l' \<Longrightarrow> (\<And>x y. (x, y) = q \<Longrightarrow> f x y l' = g x y l' ) \<Longrightarrow> p = q \<Longrightarrow> case_prod f p l = case_prod g q l'"
  by (auto simp: split_def)

lemma bind_cong [fundef_cong]:
  fixes m1 :: "('t, 'a) parser"
  assumes "m1 ts2 = m2 ts2"
    and "\<And> y ts. \<lbrakk> m2 ts2 = PCONG_INR y ts; ll_fuel ts \<le> ll_fuel ts2\<rbrakk> \<Longrightarrow> f1 y ts = f2 y ts"
    and "ts1 = ts2"
  shows "((m1 \<bind> f1) ts1) = ((m2 \<bind> f2) ts2)"
  using assms
  unfolding bind_def PCONG_INR_def
  by (auto simp: Error_Monad.bind_def ensure_parser_def split: sum.split prod.split)

lemma is_cparser_bind[parser_rules]:
  assumes "is_cparser p \<or> (\<forall>x. is_cparser (q x))"
  shows "is_cparser (p \<bind> q)"
  apply (rule is_cparserI)
  using assms unfolding is_cparser_def bind_def Error_Monad.bind_def ensure_parser_def
  by (fastforce split: sum.splits if_splits)

lemma return_eq[simp]: "return x l = Inr y \<longleftrightarrow> y=(x,l)"
  unfolding return_def by auto


lemma is_cparser_error[parser_rules]: "is_cparser (error_aux e)"
  by (auto simp: error_aux_def intro: is_cparserI)

lemma is_cparser_get[parser_rules]:
  "is_cparser get"
  apply (rule is_cparserI)
  apply (auto simp: get_def split: len_list.splits nat.splits list.splits)
  done

lemma monad_laws[simp]:
  "bind m return = ensure_parser m"
  "bind (return x) f = ensure_parser (f x)"
  "bind (bind m f) g = bind m (\<lambda>x. bind (f x) g)"
  "ensure_parser (ensure_parser m) = ensure_parser m"
  "bind (ensure_parser m) f = bind m f"
  "bind m (\<lambda>x. ensure_parser (f x)) = bind m f"
  unfolding bind_def return_def ensure_parser_def Error_Monad.bind_def
  by (auto split: if_splits sum.splits prod.splits intro!: ext)

subsection \<open>More Combinators\<close>

term "shows"


definition err_expecting_aux :: "(unit \<Rightarrow> shows) \<Rightarrow> ('t::show, 'a) parser"
where
  "err_expecting_aux msg = do { ts \<leftarrow> get_tokens; error
    (shows_string ''expecting '' o msg () o shows_string '', but found: '' o shows_quote (shows (take 100 ts)))}"

abbreviation err_expecting :: "shows \<Rightarrow> ('t::show, 'a) parser"
where
  "err_expecting msg \<equiv> err_expecting_aux (\<lambda>_. msg)"

abbreviation "err_expecting_str msg \<equiv> err_expecting (shows_string msg)"

definition "eoi \<equiv> do {
  tks \<leftarrow> get_tokens; if tks=[] then return () else err_expecting_str ''end of input'' }"


definition alt :: "(_,'a) parser \<Rightarrow> (_,'b) parser \<Rightarrow> (_,'a+'b) parser" where
  "alt p1 p2 l \<equiv> try   do { (r,l) \<leftarrow> p1 l; Error_Monad.return (Inl r, l) }
                 catch (\<lambda>e1. (try do { (r,l) \<leftarrow> p2 l; Error_Monad.return (Inr r, l) }
                 catch (\<lambda>e2. Error_Monad.error (\<lambda>_. e1 () o shows ''\<newline>  | '' o e2 ()))))"

fun sum_join where
  "sum_join (Inl x) = x" | "sum_join (Inr x) = x"

abbreviation alt' :: "(_,'a) parser \<Rightarrow> (_,'a) parser \<Rightarrow> (_,'a) parser" (infixr "\<parallel>" 53)
  where "alt' p q \<equiv> alt p q \<bind> return o sum_join"

abbreviation gseq :: "('t,'a) parser \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('t,'b) parser \<Rightarrow> ('t,'c) parser" ("_--[_]_" [61,0,60] 60)
  where "gseq p f q \<equiv> p \<bind> (\<lambda>a. q \<bind> (\<lambda>b. return (f a b)))" (* TODO/FIXME: Do-notation and abbreviation generate additional type vars here *)

abbreviation seq :: "('t,'a) parser \<Rightarrow> ('t,'b) parser \<Rightarrow> ('t,'a\<times>'b) parser" (infixr "--" 60)
  where "seq p q \<equiv> p --[Pair] q"

abbreviation seq_ignore_left :: "('t,'a) parser \<Rightarrow> ('t,'b) parser \<Rightarrow> ('t,'b) parser" (infixr "*--" 60)
  where "p *-- q \<equiv> p --[\<lambda>_ x. x] q"

abbreviation seq_ignore_right :: "('t,'a) parser \<Rightarrow> ('t,'b) parser \<Rightarrow> ('t,'a) parser" (infixr "--*" 60)
  where "p --* q \<equiv> p --[\<lambda>x _. x] q"

abbreviation map_result :: "('t,'a) parser \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> ('t,'b) parser" (infixr "with" 54)
  where "p with f \<equiv> p \<bind> return o f"

definition "exactly ts \<equiv> foldr (\<lambda>t p. do { x\<leftarrow>get; if x=t then p \<bind> return o (#) x else error id}) ts (return [])
    \<parallel> err_expecting (shows_string ''Exactly '' o shows ts)"

declare err_expecting_aux_def[consuming]

lemma alt_is_cparser[parser_rules]:
  "is_cparser p \<Longrightarrow> is_cparser q \<Longrightarrow> is_cparser (alt p q)"
  apply (rule is_cparserI)
  unfolding alt_def
  by (auto simp: Error_Monad.bind_def split: sum.splits)

lemma alt_cong[fundef_cong]:
  "\<lbrakk> l=l'; p1 l = p1' l'; \<And>e. p1' l' = Inl e \<Longrightarrow> p2 l = p2' l' \<rbrakk> \<Longrightarrow> alt p1 p2 l = alt p1' p2' l'"
  unfolding alt_def by (auto split: sum.splits simp: Error_Monad.bind_def)

lemma [parser_rules]: "ts\<noteq>[] \<Longrightarrow> is_cparser (exactly ts)"
  by (cases ts) (auto simp: exactly_def intro: parser_rules)


abbreviation optional :: "'a \<Rightarrow> ('t,'a) parser \<Rightarrow> ('t,'a) parser" where
  "optional dflt p \<equiv> p \<parallel> return dflt"

term "a\<^sup>*"

abbreviation maybe :: "('t,'a) parser \<Rightarrow> ('t,'a option) parser" ("(_?)" [1000] 999)
  where "p? \<equiv> p with Some \<parallel> return None"


subsubsection \<open>Repeat\<close>

fun repeat :: "('t,'a) parser \<Rightarrow> ('t,'a list) parser" where
  "repeat p ::= optional [] (ensure_cparser p --[(#)] repeat p)"

abbreviation "repeat1 p \<equiv> p --[(#)] repeat p"


declare repeat.simps[simp del]

lemma repeat_cong[fundef_cong]:
  assumes "\<And>nts. \<lbrakk> ll_fuel nts \<le> ll_fuel l' \<rbrakk> \<Longrightarrow> p (nts) = p' (nts)"
  assumes "l=l'"
  shows "repeat p l = repeat p' l'"
  using assms(1)
  unfolding \<open>l=l'\<close>
  apply (induction p l' rule: repeat.induct)
  apply (rewrite in "_=\<hole>" repeat.simps)
  apply (rewrite in "\<hole>=_" repeat.simps)
  apply (intro alt_cong bind_cong)
  apply (auto simp: ensure_cparser_def PCONG_INR_def)
  done

subsubsection \<open>Left and Right Associative Chaining\<close>
text \<open>Parse a sequence of \<open>A\<close> separated by \<open>F\<close>,
  and then fold the sequence with the results of \<open>F\<close>,
  either left or right associative.

  Example: Assume we have the input \<open>x\<^sub>1 o\<^sub>1 \<dots> o\<^sub>n\<^sub>-\<^sub>1 x\<^sub>n\<close>,
    and the result of parsing the \<open>x\<close> with \<open>A\<close> and the \<open>o\<close> with \<open>F\<close>
    are \<open>a\<^sub>i\<close> and \<open>+\<^sub>i\<close>.
    Then, \<open>chainL1\<close> returns \<open>(\<dots>((a\<^sub>1 +\<^sub>1 a\<^sub>2) +\<^sub>2 a\<^sub>3) +\<^sub>3 \<dots>) \<close>
    and \<open>chainR1\<close> returns \<open>a\<^sub>1 +\<^sub>1 (a\<^sub>2 +\<^sub>2 (a\<^sub>3 +\<^sub>3 \<dots>)\<dots>) \<close>
\<close>
context
  fixes A :: "('t,'a) parser"
  fixes F :: "('t,'a\<Rightarrow>'a\<Rightarrow>'a) parser"
begin
  definition chainL1 :: "('t,'a) parser" where
    "chainL1 \<equiv> do {
      x \<leftarrow> A;
      xs \<leftarrow> repeat (F --[\<lambda>f b a. f a b] A);
      return (foldl (\<lambda>a f. f a) x xs)
    }"

  qualified fun fold_shiftr :: "('a \<Rightarrow> (('a\<Rightarrow>'a\<Rightarrow>'a)\<times>'a) list \<Rightarrow> 'a)" where
    "fold_shiftr a [] = a"
  | "fold_shiftr a ((f,b)#xs) = f a (fold_shiftr b xs)"

  definition chainR1 :: "('t,'a) parser" where
    "chainR1 \<equiv> do {
      x \<leftarrow> A;
      xs \<leftarrow> repeat (F -- A);
      return (fold_shiftr x xs)
    } "

end


lemma chainL1_cong[fundef_cong]:
  assumes "\<And>l2. ll_fuel l2 \<le> ll_fuel l' \<Longrightarrow> A l2 = A' l2"
  assumes "\<And>l2. ll_fuel l2 \<le> ll_fuel l' \<Longrightarrow> F l2 = F' l2"
  assumes "l=l'"
  shows "chainL1 A F l = chainL1 A' F' l'"
  unfolding chainL1_def
  apply (intro bind_cong repeat_cong assms order_refl)
  by auto

lemma chainR1_cong[fundef_cong]:
  assumes "\<And>l2. ll_fuel l2 \<le> ll_fuel l' \<Longrightarrow> A l2 = A' l2"
  assumes "\<And>l2. ll_fuel l2 \<le> ll_fuel l' \<Longrightarrow> F l2 = F' l2"
  assumes "l=l'"
  shows "chainR1 A F l = chainR1 A' F' l'"
  unfolding chainR1_def
  apply (intro bind_cong repeat_cong assms order_refl)
  by auto




subsection \<open>Lexing Utilities\<close>

definition tk_with_prop' :: "shows \<Rightarrow> ('t::show \<Rightarrow> bool) \<Rightarrow> ('t,'t) parser" where
  [consuming]: "tk_with_prop' errmsg \<Phi> \<equiv> do {
    x\<leftarrow>get;
    if \<Phi> x then return x
    else err_expecting errmsg
  }"

abbreviation tk_with_prop :: "('t::show \<Rightarrow> bool) \<Rightarrow> ('t,'t) parser" where
  "tk_with_prop \<equiv> tk_with_prop' id"

definition range :: "'t::{linorder,show} \<Rightarrow> 't \<Rightarrow> ('t,'t) parser" where
  [consuming]: "range a b \<equiv> do {
    x\<leftarrow>get;
    if a\<le>x \<and> x\<le>b then return x
    else err_expecting (shows_string ''Token in range '' o shows a o shows_string '' - '' o shows b) }"

definition any :: "'t::show list \<Rightarrow> ('t,'t) parser" where
  [consuming]: "any ts \<equiv> do { t\<leftarrow>get; if t\<in>set ts then return t else err_expecting (shows_string ''One of '' o shows ts) }"

definition "gen_token ws p \<equiv> ws *-- p"

lemma [parser_rules]: "is_cparser p \<Longrightarrow> is_cparser (gen_token ws p)"
  unfolding gen_token_def by simp

subsubsection \<open>Characters\<close>
abbreviation (input) "char_tab \<equiv> CHR 0x09"
abbreviation (input) "char_carriage_return \<equiv> CHR 0x0D"
abbreviation (input) "char_wspace \<equiv> [CHR '' '', CHR ''\<newline>'', char_tab, char_carriage_return]"

text \<open>Some standard idioms\<close>
definition [consuming]: "lx_lowercase \<equiv> (range CHR ''a'' CHR ''z'' )"
definition [consuming]: "lx_uppercase \<equiv> (range CHR ''A'' CHR ''Z'' )"
definition [consuming]: "lx_alpha \<equiv> (lx_lowercase \<parallel> lx_uppercase)"
definition [consuming]: "lx_digit \<equiv> (range CHR ''0'' CHR ''9'' )"
abbreviation "lx_alphanum \<equiv> lx_alpha \<parallel> lx_digit"

subsection \<open>Code Generator Setup\<close>
declare monad_laws[code_unfold]
lemma bind_return_o_unfold[code_unfold]: "(m \<bind> return o f) = do { x\<leftarrow>m; return (f x)}" by (auto simp: o_def)
declare split[code_unfold] (* TODO: Should this be code_unfold by default? *)


subsection \<open>Utilities for Parsing\<close>

text \<open>Project out remainder token sequence\<close>
fun show_pres where
  "show_pres (Inr (ll,_)) = Inr ll"
| "show_pres (Inl e) = Inl e"

text \<open>Parse complete input, parameterized by parser for trailing whitespace\<close>
definition "parse_all ws p \<equiv> show_pres o (p --* ws --* eoi) o ll_from_list o String.explode"

definition "parse_all_implode ws p s \<equiv> parse_all ws p s <+? (\<lambda>msg. String.implode (msg () ''''))"

definition "parse_all_implode_nows p s \<equiv> parse_all_implode (return ()) p s"


ML \<open>
  (* Read file to string *)
  fun file_to_string name = let
    val f = TextIO.openIn name
    val s = TextIO.inputAll f
    val _ = TextIO.closeIn f
  in s end
\<close>



end
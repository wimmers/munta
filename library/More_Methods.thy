theory More_Methods
  imports Main Reordering_Quantifiers "HOL-Eisbach.Eisbach" ML_Util
begin

ML \<open>fun mini_ex ctxt = SIMPLE_METHOD (mini_ex_tac ctxt 1)\<close>
ML \<open>fun defer_ex ctxt = SIMPLE_METHOD (defer_ex_tac ctxt 1)\<close>

method_setup mini_existential =
  \<open>Scan.succeed mini_ex\<close> \<open>Miniscope existential quantifiers\<close>
method_setup defer_existential =
  \<open>Scan.succeed defer_ex\<close> \<open>Rotate first conjunct under existential quantifiers to last position\<close>

method mini_ex = ((simp only: ex_simps[symmetric])?, mini_existential, (simp)?)
method defer_ex = ((simp only: ex_simps[symmetric])?, defer_existential, (simp)?)
method defer_ex' = (defer_existential, (simp)?)

method solve_triv =
  fo_assumption | refl_match | simp; fail | assumption | (erule image_eqI[rotated], solve_triv)

method solve_ex_triv2 = (((rule exI)+)?, (rule conjI)+, solve_triv)

method solve_conj_triv = solve_triv | (rule conjI, solve_conj_triv)

method solve_conj_triv2 =
  (match conclusion in
    "_ \<and> _" \<Rightarrow> \<open>rule conjI, solve_conj_triv2\<close>
  \<bar> _ \<Rightarrow> solve_triv)

method solve_ex_triv = (((rule exI)+)?, solve_conj_triv)

named_theorems intros
named_theorems elims

lemmas [intros] =
  allI ballI exI bexI[rotated] conjI impI
and [elims] =
  bexE exE bexE conjE impE

method intros uses add  = (intro add intros)
method elims  uses add  = (elim  add elims)

text \<open>Test case\<close>
lemma all_mp:
  "\<forall> x. P x \<longrightarrow> R x" if "\<forall> x. P x \<longrightarrow> Q x" "\<And> x. P x \<Longrightarrow> Q x \<Longrightarrow> R x"
  using that by (intros; elims add: allE)

method rprem =
  (match premises in R: _ \<Rightarrow> \<open>rule R\<close>)

text \<open>Test case for @{method rprem}.\<close>
lemma
  "A \<Longrightarrow> (A \<Longrightarrow> C) \<Longrightarrow> (A \<Longrightarrow> B) \<Longrightarrow> B"
  by rprem

ML \<open>
fun all_forward_tac ctxt n thms nsubgoal =
  let
    val assumes = replicate n (assume_tac ctxt nsubgoal)
    fun forward thm = forward_tac ctxt [thm] nsubgoal :: assumes |> EVERY |> TRY
  in EVERY (map forward thms) end;
\<close>

ML \<open>
fun xrule_meth tac =
  Scan.lift (Scan.optional (Args.parens Parse.nat) 0) -- Attrib.thms >>
  (fn (n, ths) => fn ctxt => SIMPLE_METHOD (tac ctxt n ths 1));
val all_forward_meth = xrule_meth all_forward_tac
\<close>

method_setup all_forward = \<open>all_forward_meth\<close> "Apply each rule exactly once in forward manner"

named_theorems forward1
named_theorems forward2
named_theorems forward3
named_theorems forward4

method frule1 = changed \<open>all_forward forward1\<close>
method frule2 = changed \<open>all_forward (1) forward2\<close>
method frule3 = changed \<open>all_forward (2) forward3\<close>
method frule4 = changed \<open>all_forward (3) forward4\<close>

method frules = changed \<open>
  all_forward (0) forward1,
  all_forward (1) forward2,
  all_forward (2) forward3,
  all_forward (3) forward4
\<close>

ML \<open>
fun dedup_prems_tac ctxt =
  let
    fun Then NONE tac = SOME tac
      | Then (SOME tac) tac' = SOME (tac THEN' tac');
    fun thins H (tac, n) =
      if H then (tac, n + 1)
      else (Then tac (rotate_tac n THEN' eresolve_tac ctxt [thin_rl]), 0);
    fun member x = List.exists (fn y => x = y)
    fun mark_dups _ [] = []
    |   mark_dups passed (x :: xs) =
        if member x passed
        then false :: mark_dups passed xs
        else true :: mark_dups (x :: passed) xs
  in
    SUBGOAL (fn (goal, i) =>
      let
        val Hs = Logic.strip_assums_hyp goal
        val marked = mark_dups [] Hs
      in
        (case fst (fold thins marked (NONE, 0)) of
          NONE => no_tac
        | SOME tac => tac i)
      end)
  end;
\<close>

method_setup dedup_prems =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (fn i => CHANGED (dedup_prems_tac ctxt i)))\<close>
  "Remove duplicate premises"

method repeat methods m =
  determ \<open>(changed m, repeat m)?\<close>

ML \<open>
fun REPEAT_ROTATE tac =
  let
    fun repeat (trm, i) = let
      val num_prems = Logic.strip_assums_hyp trm |> length
      val tac2 = TRY (tac i) THEN rotate_tac 1 i
      val tacs = replicate num_prems tac2
    in DETERM (EVERY tacs) end
in SUBGOAL repeat end
\<close>

method_setup repeat_rotate =
 \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>
   let
     fun tac st' = method_evaluate m ctxt facts st'
   in SIMPLE_METHOD (REPEAT_ROTATE (K tac) 1) facts end)
\<close>

end (* Theory *)

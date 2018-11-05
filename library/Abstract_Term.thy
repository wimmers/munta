theory Abstract_Term
  imports Main
begin

ML \<open>
  fun pull_let ctxt u name t =
    let
      val t1 = abstract_over (u, t);
      val r1 = Const (@{const_name "HOL.Let"}, dummyT) $ u $ Abs (name, dummyT, t1);
      val ct1 = Syntax.check_term ctxt r1;
      val g1 =
        Goal.prove ctxt [] [] (Logic.mk_equals (t, ct1))
        (fn {context, ...} => EqSubst.eqsubst_tac context [0] [@{thm Let_def}] 1
        THEN resolve_tac context [@{thm Pure.reflexive}] 1)
    in g1 end;

  fun get_rhs thm =
    let
      val Const ("Pure.eq", _) $ _ $ r = Thm.full_prop_of thm
    in r end;

  fun get_lhs thm =
    let
      val Const ("Pure.imp", _) $ (Const ("Pure.eq", _) $ l $ _) $ _ = Thm.full_prop_of thm
    in l end;

  fun pull_tac' ctxt u name thm =
    let
      val l = get_lhs thm;
      val rewr = pull_let ctxt u name l;
    in Local_Defs.unfold_tac ctxt [rewr] thm end;

  fun pull_tac ctxt u name = SELECT_GOAL (pull_tac' ctxt u name) 1;
\<close>

ML \<open>
fun lift_parser p = fn (ctxt, x) => Args.text x |> (fn (r, s) => (r, (ctxt, s)))
\<close>

method_setup abstract_let =
  \<open>Args.term -- Scan.option (lift_parser Args.text) >> (
    fn (t, n_opt) => fn ctxt => SIMPLE_METHOD (pull_tac ctxt t (Option.getOpt (n_opt, "_"))))
  \<close>
  "Abstract over a subterm and extract it into a Let-binding"

text \<open>Example Usage\<close>

schematic_goal "(1 :: nat) * 2 * 3 \<equiv> ?x"
  apply (abstract_let "1 :: nat" one)
  apply (abstract_let "2 :: nat")
  apply (abstract_let "3 :: nat" two)
  by (rule Pure.reflexive)

end
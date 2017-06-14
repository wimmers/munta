(* Author: Manuel Eberl *)
theory Instantiate_Existentials
  imports Main
begin

ML \<open>
fun inst_existentials_tac ctxt [] = TRY o REPEAT_ALL_NEW (resolve_tac ctxt @{thms conjI})
  | inst_existentials_tac ctxt (t :: ts) =
      (TRY o REPEAT_ALL_NEW (resolve_tac ctxt @{thms conjI}))
      THEN_ALL_NEW (TRY o (
        let
          val thm = Drule.infer_instantiate' ctxt [NONE, SOME (Thm.cterm_of ctxt t)] @{thm exI}
        in
          resolve_tac ctxt [thm] THEN' inst_existentials_tac ctxt ts
        end))
\<close>

method_setup inst_existentials =
  \<open>
  Scan.lift (Scan.repeat Parse.term) >>
      (fn ts => fn ctxt => SIMPLE_METHOD' (inst_existentials_tac ctxt
         (map (Syntax.read_term ctxt)  ts)))
  \<close>

end
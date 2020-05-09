theory UPPAAL_Asm_AbsInt
  imports UPPAAL_Asm
begin

type_synonym 'a ainstr = "'a * instr" \<comment> \<open>Instruction with state before it is executed\<close>
type_synonym 'a aprogram = "addr \<Rightarrow> (('a ainstr) option)"

fun annot_all :: "program \<Rightarrow> 'a \<Rightarrow> 'a aprogram" where
  "annot_all prog v addr =
    (case prog addr of
        Some instr \<Rightarrow> Some (v, instr)
      | None \<Rightarrow> None)"

(* this probably makes no sense: *)
fun collect_step :: "state set aprogram \<Rightarrow> state \<Rightarrow> state set aprogram" where
  "collect_step prog entry pc =
    (let ainstr = (prog pc) in
    case ainstr of
        Some (astates, instr) \<Rightarrow>
          let instates = if state_pc entry = pc then astates \<union> {entry} else astates in
          undefined
      | None \<Rightarrow> None)"

end
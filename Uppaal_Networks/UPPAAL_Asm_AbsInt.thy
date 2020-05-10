theory UPPAAL_Asm_AbsInt
  imports UPPAAL_Asm
begin

type_synonym 'a ainstr = "instr * 'a" \<comment> \<open>Instruction with state after it was executed\<close>
type_synonym 'a aprogram = "addr \<Rightarrow> (('a ainstr) option)"

fun annot_all :: "program \<Rightarrow> 'a \<Rightarrow> 'a aprogram" where
  "annot_all prog v addr =
    (case prog addr of
        Some instr \<Rightarrow> Some (instr, v)
      | None \<Rightarrow> None)"

fun collect_predecs :: "addrspace \<Rightarrow> state set aprogram \<Rightarrow> addr \<Rightarrow> state set" where
  "collect_predecs space prog pc =
    \<Union> ((\<lambda>epc.
          case prog pc of
              Some (_, sts) \<Rightarrow> Set.filter (\<lambda>stt. state_pc stt = pc) sts
            | None \<Rightarrow> {}
      ) ` space)"

fun collect_step :: "addrspace \<Rightarrow> state set aprogram \<Rightarrow> state \<Rightarrow> state set aprogram" where
  "collect_step space prog entry pc =
    (case prog pc of
        Some (instr, _) \<Rightarrow>
          let instates = (collect_predecs space prog pc) \<union> (if state_pc entry = pc then {entry} else {}) in
          Some (instr, instates) \<comment> \<open>TODO: instead of just the instates, apply instr and return the results\<close>
      | None \<Rightarrow> None)"

end
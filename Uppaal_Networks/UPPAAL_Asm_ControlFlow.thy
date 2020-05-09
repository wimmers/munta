theory UPPAAL_Asm_ControlFlow
  imports UPPAAL_Asm
begin

text \<open>
  Analysis of a program with respect to successor and predecessor addresses for each contained
  instruction. Predecessors are necessary for abstract interpretation to know from where to
  "pull forward" the states.
\<close>

type_synonym succs = "addr \<Rightarrow> addr set"
type_synonym predecs = "addr \<Rightarrow> addr set"

fun successors :: "program \<Rightarrow> succs" where
  "successors prog pc =
    (case prog pc of
        Some (JMPZ jmp) \<Rightarrow> {jmp, pc + 1}
      | Some HALT       \<Rightarrow> {}
      | None            \<Rightarrow> {}
      | _               \<Rightarrow> {pc + 1})"


lemma stack2: obtains "s = []" | "\<exists>a ss. s = a # ss" by (meson list.exhaust) 
lemma stack3: obtains "s = []" | "\<exists>a. s = a # []" | "\<exists>a b ss. s = a # b # ss"
  by (meson remdups_adj.cases) (* TODO: this rule here makes no sense *)

lemma successors_complete:
  assumes
    "Some instr = ((prog::program) pc)"
    "step instr (pc, st, m, f, rs) = Some (rpc, rst, rm, rf, rrs)"
  shows "rpc \<in> successors prog pc"
proof (cases "instr")
case (JMPZ x1)
  from this assms show ?thesis sorry
next
  case ADD
  from assms(2) this have nextpc: "rpc = pc + 1" by (cases "st" rule: stack3) auto
  from ADD assms(1) have "prog pc = Some ADD" by simp
  from this nextpc ADD show ?thesis by auto
next
  case NOT
  from assms(2) this have nextpc: "rpc = pc + 1" by (cases "st" rule: stack2) auto
  from NOT assms(1) have "prog pc = Some NOT" by simp
  from this nextpc show ?thesis by auto
next
  case AND
  from assms(2) this have nextpc: "rpc = pc + 1"
  proof (cases "st" rule: stack2)
    case 2
    then obtain b ss where "st = b # ss" by blast
    from assms(2) AND this show ?thesis by (cases "b = 0 \<or> b = 1") auto
  qed auto
  from AND assms(1) have "prog pc = Some AND" by simp
  from this nextpc show ?thesis by auto
next
  case LT
  from assms(2) this have nextpc: "rpc = pc + 1" by (cases "st" rule: stack3) auto
  from LT assms(1) have "prog pc = Some LT" by simp
  from this nextpc show ?thesis by auto
next
  case LE
  from assms(2) this have nextpc: "rpc = pc + 1" by (cases "st" rule: stack3) auto
  from LE assms(1) have "prog pc = Some LE" by simp
  from this nextpc show ?thesis by auto
next
  case EQ
  from assms(2) EQ have nextpc: "rpc = pc + 1" by (cases "st" rule: stack3) auto
  from EQ assms(1) have "prog pc = Some EQ" by simp
  from this nextpc show ?thesis by auto
next
  case (PUSH x8)
  from assms(2) this have nextpc: "rpc = pc + 1" by auto
  from PUSH assms(1) have "prog pc = Some (PUSH x8)" by simp
  from this nextpc show ?thesis by auto
next
  case POP
  from assms(2) POP have nextpc: "rpc = pc + 1" by (cases "st" rule: stack2) auto
  from POP assms(1) have "prog pc = Some POP" by simp
  from this nextpc show ?thesis by auto
next
  case (LID x10)
  from assms(2) LID have nextpc: "rpc = pc + 1" by auto
  from LID assms(1) have "prog pc = Some (LID x10)" by simp
  from this nextpc show ?thesis by auto
next
  case STORE
  from assms(2) STORE have nextpc: "rpc = pc + 1"
  proof (cases "st" rule: stack3)
    case 3
    from this obtain v r sst where "st = v # r # sst" by blast
    from assms(2) STORE this show ?thesis by (cases "r \<ge> 0") auto
  qed auto
  from STORE assms(1) have "prog pc = Some STORE" by simp
  from this nextpc show ?thesis by auto
next
  case (STOREI x121 x122)
  from assms(2) STOREI have nextpc: "rpc = pc + 1" by auto
  from STOREI assms(1) have "prog pc = Some (STOREI x121 x122)" by simp
  from this nextpc show ?thesis by auto
next
  case COPY
  from assms(2) COPY have nextpc: "rpc = pc + 1" by auto
  from COPY assms(1) have "prog pc = Some COPY" by simp
  from this nextpc show ?thesis by auto
next
  case CALL
  (* This cannot work, CALL is indirect *)
  then show ?thesis sorry
next
  case RETURN
  then show ?thesis sorry
next
  case HALT
  then show ?thesis sorry
next
  case (STOREC x171 x172)
  then show ?thesis sorry
next
  case (SETF x18)
  then show ?thesis sorry
qed

end

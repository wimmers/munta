theory UPPAAL_Asm
  imports Main
begin

type_synonym addr = nat
type_synonym val = int
type_synonym reg = nat

datatype instr =
  JMPZ addr |
  ADD |
  NOT |
  AND |
  LT |
  LE |
  EQ |
  PUSH int -- "Push value on stack" |
  POP |
  LID reg -- "Push register value on stack" |
  STORE -- "Store stack value in register" |
  STOREI reg val -- "Store value in register" |
  COPY |
  CALL |
  RETURN |
  HALT |
  STOREC nat int -- "Special instruction, signals a clock reset" |
  SETF bool -- "Meta instruction"

type_synonym stack = "int list"
type_synonym flag = bool
type_synonym rstate = "int list" -- "Partial map from registers to values"
type_synonym state = "addr * stack * rstate * flag * nat list"
-- "Instruction pointer, stack, register state, comparison flag, reset clocks"

definition int_of :: "bool \<Rightarrow> int" where
  "int_of x \<equiv> if x then 1 else 0"

fun step :: "instr \<Rightarrow> state \<Rightarrow> state option" where
  "step (JMPZ q) (pc, st, m, f, rs) = Some (if f then (pc + 1) else q, st, m, f, rs)" |
  "step ADD (pc, a # b # st, m, f, rs) = Some (pc + 1, (a + b) # st, m, f, rs)" |
  "step NOT (pc, b # st, m , f, rs) = Some (pc + 1, st, m, \<not> f, rs)" |
  "step AND (pc, b # st, m, f, rs) =
    (if b = 0 \<or> b = 1
     then Some (pc + 1, st, m, b = 1 \<and> f, rs)
     else None)" |
  "step LT (pc, a # b # st, m, f, rs) = Some (pc + 1, st, m, a < b, rs)" |
  "step LE (pc, a # b # st, m, f, rs) = Some (pc + 1, st, m, a \<le> b, rs)" |
  "step EQ (pc, a # b # st, m, f, rs) = Some (pc + 1, st, m, a = b, rs)" |
  "step (PUSH v) (pc, st, m, f, rs) = Some (pc + 1, v # st, m, f, rs)" |
  "step POP (pc, v # st, m, f, rs) = Some (pc + 1, st, m, f, rs)" |
  "step (LID r) (pc, st, m, f, rs) = Some (pc + 1, m ! r # st, m, f, rs)" |
  "step STORE (pc, v # r # st, m, f, rs) =
    (if r \<ge> 0 then Some (pc + 1, st, m[nat r := v], f, rs) else None)" |
  "step (STOREI r v) (pc, st, m, f, rs) = Some (pc + 1, st, m[r := v], f, rs)" |
  "step COPY (pc, st, m, f, rs) = Some (pc + 1, int_of f # st, m, f, rs)" |
  "step CALL (pc, q # st, m, f, rs) =
    (if q \<ge> 0 then Some (nat q, int pc # st, m, f, rs) else None)" |
  "step RETURN (pc, q # st, m, f, rs) =
    (if q \<ge> 0 then Some (nat q + 1, st, m, f, rs) else None)" |
  (*
  "step HALT s = Some s" |
  *)
  "step (STOREC c d) (pc, st, m, f, rs) =
    (if d = 0 then Some (pc + 1, st, m, f, c # rs) else None)" |
  "step (SETF b) (pc, st, m, f, rs) = Some (pc + 1, st, m, b, rs)" |
  "step _ _ = None"

type_synonym program = "addr \<Rightarrow> instr option"
type_synonym fuel = nat

fun exec :: "program \<Rightarrow> fuel \<Rightarrow> state \<Rightarrow> addr list \<Rightarrow> (state * addr list) option" where
  "exec _ 0 _ _ = None" |
  "exec prog (Suc n) (pc, st, m, f, rs) pcs =
    (case prog pc of
       Some instr \<Rightarrow>
         if instr = HALT
         then Some ((pc, st, m, f, rs), pc # pcs)
         else
           case step instr (pc, st, m, f, rs) of
             Some s \<Rightarrow> exec prog n s (pc # pcs)
           | None \<Rightarrow> None
     | None \<Rightarrow> None)"

inductive steps :: "program \<Rightarrow> fuel \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
  "steps prog (Suc n) start start" | (*
  "steps prog (Suc n) s s'" if
    "step cmd (pc, st, m, f, rs) = Some s'"
    "steps prog n s (pc, st, m, f, rs)"
    "prog pc = Some cmd" | *)
  "steps prog (Suc n) (pc, st, m, f, rs) s'" if
    "step cmd (pc, st, m, f, rs) = Some s"
    "prog pc = Some cmd"
    "steps prog n s s'"

inductive visited :: "program \<Rightarrow> fuel \<Rightarrow> state \<Rightarrow> state \<Rightarrow> addr list \<Rightarrow> bool" where
  "visited prog (Suc n) s s []" |
  "visited prog (Suc n) (pc, st, m, f, rs) s' (pcs @ [pc])" if
    "step cmd (pc, st, m, f, rs) = Some s"
    "prog pc = Some cmd"
    "visited prog n s s' pcs"

lemmas [intro] = steps.intros

lemma exec_steps:
  assumes "exec prog n s pcs = Some ((pc, st, m, f, rs), pcs')"
  shows "steps prog n s (pc, st, m, f, rs) \<and> prog pc = Some HALT"
using assms proof (induction P \<equiv> prog n s pcs arbitrary: pc st m f rs rule: exec.induct)
  case 1
  then show ?case by simp
next
  case (2 n pc' st' m' f' rs' pcs')
  then obtain instr where "prog pc' = Some instr" by (cases "prog pc'") auto
  show ?case
  proof (cases "instr = HALT")
    case True
    with "2.prems" \<open>prog pc' = _\<close> show ?thesis by auto
  next
    case False
    with 2 \<open>prog pc' = _\<close> show ?thesis by (auto split: option.split_asm)
  qed
qed

lemma steps_halt:
  assumes "steps prog n (pc, st, m, f, rs) s" "prog pc = Some HALT"
  shows "s = (pc, st, m, f, rs)"
  using assms by (induction prog n "(pc, st, m, f, rs)" s) auto

lemma steps_exec:
  assumes "steps prog n s (pc, st, m, f, rs)" "prog pc = Some HALT"
  shows "\<exists> pcs'. exec prog n s pcs = Some ((pc, st, m, f, rs), pcs')"
using assms proof (induction P \<equiv> prog n s "(pc, st, m, f, rs)" arbitrary: pcs rule: steps.induct)
  case (1 n)
  then show ?case by simp
next
  case (2 cmd pc' st' m' f' rs' s n)
  then obtain pcs' where "exec prog n s (pc' # pcs) = Some ((pc, st, m, f, rs), pcs')" by auto
  with 2(1-3) show ?case by (auto dest!: steps_halt)
qed

lemma visited_halt:
  assumes "visited prog n (pc, st, m, f, rs) s pcs" "prog pc = Some HALT"
  shows "s = (pc, st, m, f, rs)"
  using assms by (induction prog n "(pc, st, m, f, rs)" s pcs) auto

lemma exec_length_mono:
  assumes "exec prog n s pcs = Some (s', pcs')"
  shows "length pcs' > length pcs"
  using assms
    by (induction P \<equiv> prog n s pcs arbitrary: s' pcs' rule: exec.induct)
       (force split: option.splits if_splits)+

inductive_cases visitedE1: "visited prog n s (pc, st, m, f, rs) []"

lemma visited_exec:
  assumes "visited prog n s (pc, st, m, f, rs) pcs" "prog pc = Some HALT"
  shows "exec prog n s pcs' = Some ((pc, st, m, f, rs), pc # pcs @ pcs')"
using assms proof (induction P \<equiv> prog n s "(pc, st, m, f, rs)" pcs arbitrary: pcs' rule: visited.induct)
  case (1 n)
  then show ?case by simp
next
  case (2 cmd pc' st' m' f' rs' s n pcs pcs')
  with 2 have "exec prog n s (pc' # pcs') = Some ((pc, st, m, f, rs), pc # pcs @ pc' # pcs')"
    by auto
  with 2(1-3) show ?case by (auto dest!: steps_halt)
qed

lemma visited_exec':
  assumes "visited prog n s (pc, st, m, f, rs) pcs" "prog pc = Some HALT"
  shows "exec prog n s [] = Some ((pc, st, m, f, rs), pc # pcs)"
using visited_exec assms by auto

end
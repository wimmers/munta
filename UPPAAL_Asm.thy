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
  LE |
  LT |
  PUSH int -- "Push value on stack" |
  POP |
  LID reg -- "Push register value on stack" |
  STORE reg val -- "Store value in register" |
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
  "step (JMPZ q) (pc, st, m, f, rs) = Some (if f then pc else q, st, m, f, rs)" |
  "step ADD (pc, a # b # st, m, f, rs) = Some (pc + 1, (a + b) # st, m, f, rs)" |
  "step NOT (pc, b # st, m , f, rs) =
    (if b = 0 \<or> b = 1
     then Some (pc + 1, int_of (b = 0) # st, m, f, rs)
     else None)" |
  "step AND (pc, a # b # st, m, f, rs) =
    (if (a = 0 \<or> a = 1) \<and> (b = 0 \<or> b = 1)
     then Some (pc + 1, int_of (a = 1 \<and> b = 1) # st, m, f, rs)
     else None)" |
  "step LE (pc, a # b # st, m, f, rs) = Some (pc + 1, int_of (a \<le> b) # st, m, f, rs)" |
  "step LT (pc, a # b # st, m, f, rs) = Some (pc + 1, int_of (a < b) # st, m, f, rs)" |
  "step (PUSH v) (pc, st, m, f, rs) = Some (pc + 1, v # st, m, f, rs)" |
  "step POP (pc, v # st, m, f, rs) = Some (pc + 1, st, m, f, rs)" |
  "step (LID r) (pc, st, m, f, rs) = Some (pc + 1, m ! r # st, m, f, rs)" |
  "step (STORE r v) (pc, st, m, f, rs) = Some (pc, st, m[r := v], f, rs)" |
  "step COPY (pc, st, m, f, rs) = Some (pc + 1, int_of f # st, m, f, rs)" |
  "step CALL (pc, q # st, m, f, rs) =
    (if q \<ge> 0 then Some (nat q, int pc # st, m, f, rs) else None)" |
  "step RETURN (pc, q # st, m, f, rs) =
    (if q \<ge> 0 then Some (nat q + 1, st, m, f, rs) else None)" |
  "step HALT s = Some s" |
  "step (STOREC c d) (pc, st, m, f, rs) =
    (if d = 0 then Some (pc, st, m, f, c # rs) else None)" |
  "step (SETF b) (pc, st, m, f, rs) = Some (pc, st, m, b, rs)" |
  "step _ _ = None"

type_synonym program = "addr \<Rightarrow> instr option"
type_synonym fuel = nat

fun steps :: "program \<Rightarrow> fuel \<Rightarrow> state \<Rightarrow> state option" where
  "steps _ 0 _ = None" |
  "steps prog (Suc n) (pc, st, m, f, rs) =
    (case prog pc of
       Some instr \<Rightarrow>
         if instr = HALT
         then Some (pc, st, m, f, rs)
         else
           case step instr (pc, st, m, f, rs) of
             Some s \<Rightarrow> steps prog n s
           | None \<Rightarrow> None
     | None \<Rightarrow> None)"

end
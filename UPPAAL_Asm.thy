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
  HALT

type_synonym stack = "int list"
type_synonym flag = bool
type_synonym rstate = "reg \<Rightarrow> int option" -- "Partial map from registers to values"
type_synonym state = "addr * stack * rstate * flag"
-- "Instruction pointer, stack, register state, comparison flag"

definition int_of :: "bool \<Rightarrow> int" where
  "int_of x \<equiv> if x then 1 else 0"

fun step :: "instr \<Rightarrow> state \<Rightarrow> state option" where
  "step (JMPZ q) (pc, st, m, f) = Some (if f then pc else q, st, m, f)" |
  "step ADD (pc, a # b # st, m, f) = Some (pc + 1, (a + b) # st, m, f)" |
  "step NOT (pc, b # st, m , f) =
    (if b = 0 \<or> b = 1
     then Some (pc + 1, int_of (b = 0) # st, m, f)
     else None)" |
  "step AND (pc, a # b # st, m, f) =
    (if (a = 0 \<or> a = 1) \<and> (b = 0 \<or> b = 1)
     then Some (pc + 1, int_of (a = 1 \<and> b = 1) # st, m, f)
     else None)" |
  "step LE (pc, a # b # st, m, f) = Some (pc + 1, int_of (a \<le> b) # st, m, f)" |
  "step LT (pc, a # b # st, m, f) = Some (pc + 1, int_of (a < b) # st, m, f)" |
  "step (PUSH v) (pc, st, m, f) = Some (pc + 1, v # st, m, f)" |
  "step POP (pc, v # st, m, f) = Some (pc + 1, st, m, f)" |
  "step (LID r) (pc, st, m, f) =
    (case m r of Some v \<Rightarrow> Some (pc + 1, v # st, m, f) | None \<Rightarrow> None)" |
  "step (STORE r v) (pc, st, m, f) = Some (pc, st, m(r := Some v), f)" |
  "step COPY (pc, st, m, f) = Some (pc + 1, int_of f # st, m, f)" |
  "step CALL (pc, q # st, m, f) =
    (if q \<ge> 0 then Some (nat q, int pc # st, m, f) else None)" |
  "step RETURN (pc, q # st, m, f) =
    (if q \<ge> 0 then Some (nat q + 1, st, m, f) else None)" |
  "step HALT s = Some s" |
  "step _ _ = None"

type_synonym program = "addr \<Rightarrow> instr option"
type_synonym fuel = nat

fun steps :: "program \<Rightarrow> fuel \<Rightarrow> state \<Rightarrow> state option" where
  "steps _ 0 _ = None" |
  "steps prog (Suc n) (pc, st, m, f) =
    (case prog pc of
       Some instr \<Rightarrow>
         if instr = HALT
         then Some (pc, st, m, f)
         else
           case step instr (pc, st, m, f) of
             Some s \<Rightarrow> steps prog n s
           | None \<Rightarrow> None
     | None \<Rightarrow> None)"

end
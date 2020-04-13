theory Syntax_Bundles
  imports
    "HOL-Library.Stream" "HOL-Imperative_HOL.Imperative_HOL" "HOL-Word.Bits"
    Automatic_Refinement.Relators "HOL-Library.Extended_Nat"
begin

bundle bit_syntax begin
notation
      bitNOT ("NOT")
  and bitAND (infixr "AND" 64)
  and bitOR  (infixr "OR"  59)
  and bitXOR (infixr "XOR" 59)
  and shiftl (infixl "<<" 55)
  and shiftr (infixl ">>" 55)
  and test_bit (infixl "!!" 100)
end

bundle no_bit_syntax begin
no_notation
      bitNOT ("NOT")
  and bitAND (infixr "AND" 64)
  and bitOR  (infixr "OR"  59)
  and bitXOR (infixr "XOR" 59)
  and shiftl (infixl "<<" 55)
  and shiftr (infixl ">>" 55)
  and test_bit (infixl "!!" 100)
end

bundle imperative_hol_syntax begin
notation
  Ref.noteq (infix "=!=" 70) and
  Ref.lookup ("!_" 61) and
  Ref.update ("_ := _" 62) and
  Array.noteq (infix "=!!=" 70)
end

bundle no_imperative_hol_syntax begin
no_notation
  Ref.noteq (infix "=!=" 70) and
  Ref.lookup ("!_" 61) and
  Ref.update ("_ := _" 62) and
  Array.noteq (infix "=!!=" 70)
end

bundle no_library_syntax begin
no_notation Stream.snth (infixl "!!" 100)
no_notation fun_rel_syn (infixr "\<rightarrow>" 60)
no_notation Extended_Nat.infinity ("\<infinity>")
unbundle no_imperative_hol_syntax
unbundle no_bit_syntax
end

end
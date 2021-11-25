theory TA_Syntax_Bundles
  imports
    "HOL-Library.Stream"
    "HOL-Imperative_HOL.Imperative_HOL"
    "Word_Lib.Bit_Shifts_Infix_Syntax"
    "Word_Lib.Syntax_Bundles"
    Automatic_Refinement.Relators
    "HOL-Library.Extended_Nat"
begin

bundle bit_syntax begin

unbundle bit_projection_infix_syntax

notation
      ring_bit_operations_class.not ("NOT")
  and semiring_bit_operations_class.and (infixr "AND" 64)
  and semiring_bit_operations_class.or  (infixr "OR"  59)
  and semiring_bit_operations_class.xor (infixr "XOR" 59)
  and shiftl (infixl "<<" 55)
  and shiftr (infixl ">>" 55)

end

bundle no_bit_syntax begin
no_notation
      ring_bit_operations_class.not ("NOT")
  and semiring_bit_operations_class.and (infixr "AND" 64)
  and semiring_bit_operations_class.or  (infixr "OR"  59)
  and semiring_bit_operations_class.xor (infixr "XOR" 59)
  and shiftl (infixl "<<" 55)
  and shiftr (infixl ">>" 55)
  and bit (infixl "!!" 100)
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
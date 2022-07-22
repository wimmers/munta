theory OCaml_Code_Printings
  imports Separation_Logic_Imperative_HOL.Sep_Examples
begin

code_printing constant blit' \<rightharpoonup> (OCaml)
  "(fun/ ()/ -> /Array.blit _ (Z.to'_int _) _ (Z.to'_int _) (Z.to'_int _))"

export_code blit checking SML
export_code blit in OCaml

end

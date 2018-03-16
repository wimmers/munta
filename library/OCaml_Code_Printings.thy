theory OCaml_Code_Printings
  imports Separation_Logic_Imperative_HOL.Sep_Examples
begin

code_printing constant blit' \<rightharpoonup> (OCaml)
  "(fun/ ()/ -> /Array.blit _ (Big'_int.to'_int _) _ (Big'_int.to'_int _) (Big'_int.to'_int _))"

export_code blit checking SML
export_code blit in OCaml

end
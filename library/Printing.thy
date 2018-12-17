theory Printing
  imports Main
begin

definition print :: "String.literal \<Rightarrow> unit" where
"print x = ()"

definition println :: "String.literal \<Rightarrow> unit" where
  "println x = print (x + STR ''\<newline>'')"

definition "print_err = print"
definition "println_err x = print_err (x + STR ''\<newline>'')"

end
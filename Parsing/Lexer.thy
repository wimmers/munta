(* Author: Peter Lammich *)
section \<open>Basic Lexing\<close>

theory Lexer
  imports Parser_Combinator
begin

\<comment> \<open>We start by defining a lexer\<close>
definition "lx_ws \<equiv> repeat (any char_wspace)"
abbreviation "token \<equiv> gen_token lx_ws"

definition [consuming]: "tk_plus = token (exactly ''+'')"
definition [consuming]: "tk_times \<equiv> token (exactly ''*'')"
definition [consuming]: "tk_minus \<equiv> token (exactly ''-'')"
definition [consuming]: "tk_div \<equiv> token (exactly ''/'')"
definition [consuming]: "tk_power \<equiv> token (exactly ''^'')"
definition [consuming]: "tk_lparen \<equiv> token (exactly ''('')"
definition [consuming]: "tk_rparen \<equiv> token (exactly '')'')"

abbreviation "lx_digit' \<equiv> lx_digit with (\<lambda>d. nat_of_char d - nat_of_char CHR ''0'')"

\<comment> \<open>We convert the string to a number while parsing, using a parameterized parser.
   NB: Allows leading zeroes\<close>
fun lx_nat_aux :: "nat \<Rightarrow> (char,nat) parser" where
  " lx_nat_aux acc ::= do { d \<leftarrow> lx_digit'; lx_nat_aux (10*acc + d) }
  \<parallel> return acc"

definition [consuming]: "lx_nat \<equiv> lx_digit' \<bind> lx_nat_aux"
definition [consuming]: "lx_int \<equiv> exactly ''-'' *-- lx_nat with uminus o int \<parallel> lx_nat with int"

definition [consuming]: "tk_int \<equiv> token lx_int"

end
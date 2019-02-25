theory Error_List_Monad
  imports Main "HOL-Library.Monad_Syntax"
begin


(* Error monad *)
type_synonym error = String.literal

datatype 'a result =
  is_result: Result 'a
| is_error:  Error "error list"

fun bind where "bind m f = (case m of
  Result x \<Rightarrow> f x
| Error es \<Rightarrow> Error es)"

adhoc_overloading "Monad_Syntax.bind" bind

fun err_msg where
  "err_msg m (Error es) = Error (m # es)"
| "err_msg m x = x"

fun make_err where
  "make_err m (Error es) = Error (es @ [m])"
| "make_err m _ = Error [m]"

definition assert_msg where "assert_msg b m = (if b then (\<lambda>x. x) else make_err m)"

definition assert where "assert b m = (if b then Result () else Error [m])"

fun the_result where
  "the_result (Result x) = x"

fun the_errors where
  "the_errors (Error es) = es"

fun combine2_gen where
  "combine2_gen comb (Error e1) (Error e2) = Error (List.append e1 e2)"
| "combine2_gen comb (Error e)  (Result _) = Error e"
| "combine2_gen comb (Result _) (Error e)  = Error e"
| "combine2_gen comb (Result a) (Result b) = comb a b"

(* let combine2: ('a result * 'b result -> ('a * 'b) result) = combine2_gen (fun a b -> Result (a, b)) *)

definition "combine2 = combine2_gen (\<lambda>a b. Result (a, b))"

notation combine2 (infixr "<|>" 60)

fun combine where
  "combine [] = Result []"
| "combine (x # xs) = combine2_gen (\<lambda>x xs. Result (x # xs)) x (combine xs)"

abbreviation (input) app (infixl "|>" 59) where "a |> b \<equiv> b a"

definition "combine_map f xs = List.map f xs |> combine"

fun map_errors where
  "map_errors f (Error errors) = Error (List.map f errors)"
| "map_errors f r = r"

fun fold_error where
  "fold_error f [] a = Result a"
| "fold_error f (x # xs) a = do {a \<leftarrow> f x a; fold_error f xs a}"

end
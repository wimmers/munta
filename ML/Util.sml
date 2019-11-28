structure Util =
struct

(** Printing utilites **)
fun println s = print (s ^ "\n")

fun list_to_string f = (fn x => "[" ^ x ^ "]") o String.concatWith ", " o map f

fun print_result NONE = println("Invalid input\n")
    | print_result (SOME true) = println("Property is satisfied\n")
    | print_result (SOME false) = println("Property is not satisfied\n")

(** File reading **)
fun read_lines stream =
  let
    val input = TextIO.inputLine stream
      handle Size => (println "Input line too long!"; raise Size)
  in
    case input of
      NONE => ""
    | SOME input => input ^ read_lines stream
  end

fun read_file f =
  let
    val file = TextIO.openIn f
    val s = read_lines file
    val _ = TextIO.closeIn file
  in s end

(** Processing command line arguments **)
datatype 'a argument = Is_Present | Is_Not_Present | Has_Val of 'a

type arguments = string argument list

exception Unknown_Argument of string

datatype argument_type = Arg | Flag

val common_arguments = [
  (["deadlock", "dc"], "Ignore formula and run deadlock check.", Flag),
  (["model", "m"],
    "Input file for the model & formula. "
    ^ "If this is not specified, the input is read from stdin.",     
    Arg),
  (["help", "h", "?"], "Show this help string.", Flag),
  (["cpu-time", "cpu"], "Report CPU time.", Flag),
  (["num-threads", "n"], "Number of threads.", Arg)
]

val the_args = ref []

fun is_present arg = case List.find (fn (k, v) => k = arg) (!the_args) of
    NONE => raise Unknown_Argument arg
  | SOME (_, Is_Not_Present) => false
  | _ => true

fun find_arg arg = case List.find (fn (k, v) => k = arg) (!the_args) of
    NONE => raise Unknown_Argument arg
  | SOME (_, Has_Val v) => SOME v
  | _ => NONE

val get_arg = the o find_arg

fun find_with_arg P [] = NONE
  | find_with_arg P [_] = NONE
  | find_with_arg P (x :: y :: xs) = if P x then SOME y else find_with_arg P (y :: xs)

fun read_arguments arguments =
  let
    val args = CommandLine.arguments()
    fun find_name names name = List.find (fn x => "-" ^ x = name) names <> NONE
    fun find_it (names, Flag) =
      (case List.find (find_name names) args of
        NONE => Is_Not_Present
      | SOME _ => Is_Present)
    | find_it (names, Arg) =
      (case find_with_arg (find_name names) args of
        NONE => Is_Not_Present
      | SOME x => Has_Val x)
    val args = map (fn (names, _, typ) => (hd names, find_it (names, typ))) arguments
  in
    the_args := args
  end

fun print_usage arguments =
  arguments
  |> map (fn (names, descr, _) =>
      (map (fn s => "-" ^ s ^ " ") names|> String.concat) ^ ": " ^ descr ^ "\n")
  |> String.concat
  |> (fn s => "Usage:\n" ^ s)
  |> println

end
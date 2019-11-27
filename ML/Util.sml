structure Util =
struct

(*** Printing utilites ***)
fun println s = print (s ^ "\n")

fun list_to_string f = (fn x => "[" ^ x ^ "]") o String.concatWith ", " o map f

fun print_result NONE = println("Invalid input\n")
    | print_result (SOME true) = println("Property is satisfied\n")
    | print_result (SOME false) = println("Property is not satisfied\n")

fun read_lines stream =
  let
    val input = TextIO.inputLine stream
      handle Size => (println "Input line too long!"; raise Size)
  in
    case input of
      NONE => ""
    | SOME input => input ^ read_lines stream
  end

fun find_with_arg P [] = NONE
  | find_with_arg P [_] = NONE
  | find_with_arg P (x :: y :: xs) = if P x then SOME y else find_with_arg P (y :: xs)

fun read_file f =
  let
    val file = TextIO.openIn f
    val s = read_lines file
    val _ = TextIO.closeIn file
  in s end

fun print_json () =
  let
    val messages = Logging.get_trace ()
    val jsons = filter (fn (i, s) => i = 2) messages |> map snd
    val _ = println ""
    val _ = println "The following JSON was read by the parser:"
    val _ = if length jsons > 0 then println (hd jsons) else ()
  in () end

end
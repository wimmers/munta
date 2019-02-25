open Model_Checker;

(*** Printing utilites ***)
fun println s = print (s ^ "\n")

fun list_to_string f = (fn x => "[" ^ x ^ "]") o String.concatWith ", " o map f;

fun print_result NONE = println("Invalid input\n")
    | print_result (SOME true) = println("Property is satisfied\n")
    | print_result (SOME false) = println("Property is not satisfied\n")

(*** Wrapping up the checker ***)
fun run_and_print check_deadlock s =
  let
    val debug_level: Int32.int Unsynchronized.ref = ref 0
    val _ = debug_level := 2
    val t = Time.now ()
    val r = parse_convert_run check_deadlock s ()
    val t = Time.- (Time.now (), t)
    val _ = println("")
    val _ = println("Internal time for precondition check + actual checking: " ^ Time.toString t)
    val _ = println("")
  in
    case r of
      Error es => let
        val _ = println "Failure:"
        val _ = map println es
      in () end
    | Result r => let
      val _ = if !debug_level >= 1 then let
          val _ = println("# explored states: " ^ Int.toString(Tracing.get_count ()))
          val _ = println("")
        in () end else ()
      in println r end
  end;

fun read_lines stream =
  let
    val input = TextIO.inputLine stream
      handle Size => (println "Input line too long!"; raise Size)
  in
    case input of
      NONE => ""
    | SOME input => input ^ read_lines stream
  end;

fun check_and_verify_from_stream stream _ =
  let
    val args = CommandLine.arguments()
    val check_deadlock = List.find (fn x => x = "-deadlock" orelse x = "-dc") args <> NONE
    val input = read_lines stream
  in
    if input = ""
    then println "Failed to read line from input!"
      (* We append a space to terminate the input for the parser *)
    else input ^ " " |> run_and_print check_deadlock
  end;

val main = check_and_verify_from_stream TextIO.stdIn
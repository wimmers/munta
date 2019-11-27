open Model_Checker;
open Util;

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
  end

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
  end

val to_large_int = fn x => x;

fun print_json () =
  let
    val messages = Logging.get_trace ()
    val jsons = filter (fn (i, s) => i = 2) messages |> map snd
    val _ = println ""
    val _ = println "The following JSON was read by the parser:"
    val _ = if length jsons > 0 then println (hd jsons) else ()
  in () end

fun print_explored () =
  let
    val messages = Logging.get_trace ()
    val explored = filter (fn (i, s) => i = 5 andalso String.isPrefix "Explored: " s) messages
    val explored = map (fn (_, s) => String.extract (s, String.size "Explored: ", NONE)) explored
    val final = filter (fn (i, s) => i = 5 andalso String.isPrefix "Final: " s) messages
    val final = map (fn (_, s) => String.extract (s, String.size "Final: ", NONE)) final
    val _ = println ""
    val _ = println "The search explored the following states:"
    val _ = map println explored
    val _ = if length final > 0 then println "The search hit the following final state:" else ()
    val _ = if length final > 0 then map println final else [()]
  in () end

val arguments = common_arguments @ [
  (["explored", "e"], "Report set of explored states (only works for reachability formulas).", Flag),
  (["show", "s"], "Print back the JSON that was parsed from the input.", Flag)
]

fun main () =
  let
    val _ = read_arguments arguments
    val check_deadlock = is_present "deadlock"
    val cpu_time = is_present "cpu-time"
    val trace_explored = is_present "explored"
    val model = find_arg "model"
    val num_threads = find_arg "num-threads"
    val show_json = is_present "show"
    val show_help = is_present "help"
    fun convert f NONE = NONE
      | convert f (SOME x) = SOME (f x)
        handle Fail msg => (println ("Argument error: " ^ msg); OS.Process.exit OS.Process.failure)
    fun int_of_string err_msg s = case Int.fromString s of
        NONE => raise Fail (err_msg ^ " should be an integer")
      | SOME x => x
    fun the_default x NONE = x
      | the_default _ (SOME x) = x
    val num_threads = num_threads
      |> convert (int_of_string "Number of threads")
      |> the_default 1
    val _ = println "** Configuration options **"
    val _ = "* Deadlock: " ^ (if check_deadlock then "True" else "False") |> println
    val _ = "* Model: " ^ (case model of NONE => "from stdin" | SOME m => m) |> println
    val _ = "* Report explored states: " ^ (if trace_explored then "True" else "False") |> println
    (* val _ = "* Num Threads: " ^ Int.toString num_threads |> println *)
    (* val _ = "* Measuring CPU time: " ^ (if cpu_time then "True" else "False") |> println *)
    val num_threads = 10000
    (* val num_threads = num_threads |> to_large_int |> nat_of_integer *)
    (* val _ = if cpu_time then Timing.set_cpu true else () *)
    val _ = if show_json then Logging.set_level 2 else ()
    val _ = if trace_explored then Logging.set_level 5 else ()
    val input = ref ""
  in
    if show_help then
      print_usage arguments
    else (case model of
      NONE => input := read_lines TextIO.stdIn |
      SOME f =>
        let
          val file = TextIO.openIn f
          val s = read_lines file
          val _ = TextIO.closeIn file
          val _ = input := s
        in () end;
      run_and_print check_deadlock (!input);
      (if show_json then print_json () else ());
      (if trace_explored then print_explored () else ())
    )
  end

(* val main = check_and_verify_from_stream TextIO.stdIn *)
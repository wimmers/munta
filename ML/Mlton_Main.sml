(* val main = check_and_verify_from_stream (TextIO.stdIn) *)
val main = check_and_verify
val _ = if MLton.isMLton then main() else ()
val main = check_and_verify_from_stream (TextIO.stdIn)
val _ = if MLton.isMLton then main() else ()
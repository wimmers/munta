use "Unsynchronized.sml";
use "Writeln.sml";
use "basics.ML";
use "library.ML";
(*use "parallel.sml";*)
(* use "sequential.sml"; *)
use "parallel_task_queue.sml";
use "Certificate.sml";
val mlunta_dir =
  case OS.Process.getEnv "MLUNTA_CERT" of
    SOME x => x
  | NONE => raise Fail "The location of mlunta certificate needs to be specified in $MLUNTA_CERT";
map (fn f => use (mlunta_dir ^ "/" ^ f)) [
  "prelude.sml",
  "serializable.sml",
  "certificate.sml"
];
use "Muntac.sml";
(* use "profile_poly.sml" *)

(*
Dummy implementation for ML compilers that do not support parallelism.

See parallel.sml
*)
structure Par_List:
sig
  val map: ('a -> 'b) -> 'a list -> 'b list
end =
struct

val map = map;

end;
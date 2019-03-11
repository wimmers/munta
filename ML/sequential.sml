(*
Dummy implementation for ML compilers that do not support parallelism.

See parallel.sml
*)
structure Par_List:
sig
  val map: ('a -> 'b) -> 'a list -> 'b list
end =
struct

val mapi = fn f =>
  let
    fun mapi _ [] = []
      | mapi cnt (x :: xs) = f cnt x :: mapi (cnt + 1) xs
  in mapi 0 end;

val map = fn f => fn xs =>
  let
    fun timeit id x =
      let
        val t = Time.now ()
        val y = f x
        val t = Time.- (Time.now (), t)
        val _ = print ("Time to run process #" ^ Int.toString id ^ ":" ^ Time.toString t ^ "\n")
      in y end
  in mapi timeit xs end

end;
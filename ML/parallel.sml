(*
Parallel map combinator for Poly/ML.
Assigns an individual process to each element in the list.
*)
structure Par_List:
sig
  val map: ('a -> 'b) -> 'a list -> 'b list
end =
struct

open Thread;

datatype 'a result = Pending | Result of 'a | Exception of exn
type 'a future = Mutex.mutex * ConditionVar.conditionVar * 'a result ref

fun future (f: unit -> 'a): 'a future =
  let
    val m = Mutex.mutex ();
    val v = ConditionVar.conditionVar ();
    val r = ref Pending;
    val comp = fn () =>
      (
      let
        val x = f ();
        val _ = Mutex.lock m;
        val _ = r := Result x;
        val _ = Mutex.unlock m;
      in () end
      handle e => (Mutex.lock m; r := Exception e; Mutex.unlock m);
      ConditionVar.signal v);
    val _ = Thread.fork (comp, [])
  in (m, v, r) end

fun join ((m, v, r): 'a future): 'a =
  let
    fun loop () =
      case !r of
        Result x => (Mutex.unlock m; x)
      | Exception e => (Mutex.unlock m; raise e)
      | Pending => (ConditionVar.wait (v, m); loop ())
    val _ = Mutex.lock m;
  in loop () end

val map = fn f => fn xs =>
  let
    val forked = map (fn x => future (fn () => f x)) xs
  in map join forked end

end;
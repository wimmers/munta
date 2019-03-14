(*
Parallel map combinator for Poly/ML.
Assigns an individual process to each element in the list.
*)
structure Par_List:
sig
  val map: ('a -> 'b) -> 'a list -> 'b list
  val set_num_threads: int -> unit
end =
struct

val num_threads = ref 1;

fun set_num_threads n = num_threads := n;

open Thread;

datatype 'a result = Pending | Result of 'a | Exception of exn
type 'a future = Mutex.mutex * ConditionVar.conditionVar * 'a result ref

val task_queue: (unit -> unit) list ref = ref [];

val task_queue_mutex = Mutex.mutex ();

fun worker_thread () =
  let
    val _ = Mutex.lock task_queue_mutex;
  in
    case !task_queue of
      [] => (Mutex.unlock task_queue_mutex; ())
    | task :: tasks =>
      let
        val _ = task_queue := tasks
        val _ = Mutex.unlock task_queue_mutex
        val _ = task ()
      in
        worker_thread ()
      end
  end

fun future (id: int) (f: unit -> 'a): 'a future =
  let
    val m = Mutex.mutex ();
    val v = ConditionVar.conditionVar ();
    val r = ref Pending;
    val comp = (fn () =>
      let
        val x = Result (f ()) handle e => Exception e;
        val _ = Mutex.lock m;
        val _ = r := x;
        val _ = Mutex.unlock m;
        val _ = ConditionVar.signal v;
      in () end
    );
    val _ = task_queue := comp :: !task_queue
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

val mapi = fn f =>
  let
    fun mapi _ [] = []
      | mapi cnt (x :: xs) = f cnt x :: mapi (cnt + 1) xs
  in mapi 0 end;

fun for_n f n =
  if n <= 0 then () else (f (); for_n f (n - 1))

val map = fn f => fn xs =>
  let
    val forked = mapi (fn i => fn x => future i (fn () => f x)) xs
    val _ = for_n (fn () => Thread.fork (worker_thread, [])) (!num_threads)
  in map join forked end

end;
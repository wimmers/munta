theory Trace_Timing
  imports Main
begin

datatype time = Time int

definition now :: "unit \<Rightarrow> time" where
  "now _ = undefined"

instantiation time :: minus
begin

definition "minus_time (_ :: time) (_ :: time) = (undefined :: time)"

instance ..

end

definition time_to_string :: "time \<Rightarrow> String.literal" where
  "time_to_string _ = undefined"

code_printing
  constant "now" \<rightharpoonup> (SML) "Time.now _"

code_printing
  constant "time_to_string" \<rightharpoonup> (SML) "(fn x => Time.toString x) _"

code_printing
  constant "(-) :: time \<Rightarrow> time \<Rightarrow> time" \<rightharpoonup> (SML) "(fn x => fn y => Time.- (x, y)) _ _"

code_printing code_module "Timing" \<rightharpoonup> (SML)
\<open>
structure Timing : sig
  val start_timer: unit -> unit
  val save_time: string -> unit
  val get_timings: unit -> (string * Time.time) list
end = struct
  val t = Unsynchronized.ref Time.zeroTime;
  val timings = Unsynchronized.ref [];
  fun start_timer () = (t := Time.now ());
  fun get_elapsed () = Time.- (Time.now (), !t);
  fun save_time s = (timings := ((s, get_elapsed ()) :: !timings));
  fun get_timings () = !timings;
end
\<close>

definition start_timer :: "unit \<Rightarrow> unit" where
  "start_timer _ = ()"

definition save_time :: "String.literal \<Rightarrow> unit" where
  "save_time s = ()"

code_reserved SML Timing

code_printing
  constant start_timer \<rightharpoonup> (SML) "Timing.start'_timer _"

code_printing
  constant save_time \<rightharpoonup> (SML) "Timing.save'_time _"

definition "test \<equiv> let _ = start_timer (); _ = save_time STR ''test'' in ()"

export_code test checking SML

hide_const test

end
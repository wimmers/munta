theory Trace_Timing
  imports Refine_Imperative_HOL.Sepref
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

paragraph \<open>Setup for Sepref\<close>

lemma [sepref_import_param]:
  "(start_timer, start_timer) \<in> Id \<rightarrow> Id"
  "(save_time, save_time) \<in> Id \<rightarrow> Id"
  by simp+

definition
  "START_TIMER = RETURN o start_timer"

definition
  "start_timer_impl = return o start_timer"

definition
  "SAVE_TIME = RETURN o save_time"

definition
  "save_time_impl = return o save_time"

lemma start_timer_hnr:
  "hn_refine (hn_val Id x' x) (start_timer_impl x) (hn_val Id x' x) unit_assn (START_TIMER $ x')"
  unfolding START_TIMER_def start_timer_impl_def by sepref_to_hoare sep_auto

lemma save_time_hnr:
  "(save_time_impl, SAVE_TIME) \<in> id_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn"
  unfolding SAVE_TIME_def save_time_impl_def by sepref_to_hoare sep_auto

sepref_register START_TIMER SAVE_TIME

lemmas [sepref_fr_rules] = start_timer_hnr save_time_hnr

definition
  "time_it s f = (let _ = start_timer (); r = f (); _ = save_time s in r)"

lemma time_it:
  "e = time_it s (\<lambda>_. e)"
  unfolding Let_def time_it_def ..

method time_it for s :: String.literal and t = (subst time_it[where s = s and e = t])

end
theory Tracing
  imports Main Refine_Imperative_HOL.Sepref
begin

datatype message = ExploredState

definition write_msg :: "message \<Rightarrow> unit" where
  "write_msg m = ()"

code_printing code_module "Tracing" \<rightharpoonup> (SML)
\<open>
structure Tracing : sig
  val count_up : unit -> unit
  val get_count : unit -> int
end = struct
  val counter = Unsynchronized.ref 0;
  fun count_up () = (counter := !counter + 1);
  fun get_count () = !counter;
end
\<close> and (OCaml)
\<open>
module Tracing : sig
  val count_up : unit -> unit
  val get_count : unit -> int
end = struct
  let counter = ref 0
  let count_up () = (counter := !counter + 1)
  let get_count () = !counter
end
\<close>

code_reserved SML Tracing

code_reserved OCaml Tracing

code_printing
  constant write_msg \<rightharpoonup> (SML) "(fn x => Tracing.count'_up ()) _"
       and            (OCaml) "(fun x -> Tracing.count'_up ()) _"

definition trace where
  "trace m x = (let a = write_msg m in x)"

lemma trace_alt_def[simp]:
  "trace m x = (\<lambda> _. x) (write_msg x)"
  unfolding trace_def by simp

definition
  "test m = trace ExploredState ((3 :: int) + 1)"

definition "TRACE m = RETURN (trace m ())"

lemma TRACE_bind[simp]:
  "do {TRACE m; c} = c"
  unfolding TRACE_def by simp

lemma [sepref_import_param]:
  "(trace, trace) \<in> \<langle>Id,\<langle>Id,Id\<rangle>fun_rel\<rangle>fun_rel"
  by simp

sepref_definition TRACE_impl is
  "TRACE" :: "id_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn"
  unfolding TRACE_def by sepref

lemmas [sepref_fr_rules] = TRACE_impl.refine


text \<open>Somehow Sepref does not want to pick up TRACE as it is, so we use the following workaround:\<close>

definition "TRACE' = TRACE ExploredState"

definition "trace' = trace ExploredState"

lemma TRACE'_alt_def:
  "TRACE' = RETURN (trace' ())"
  unfolding TRACE_def TRACE'_def trace'_def ..

lemma [sepref_import_param]:
  "(trace', trace') \<in> \<langle>Id,Id\<rangle>fun_rel"
  by simp

sepref_definition TRACE'_impl is
  "uncurry0 TRACE'" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a unit_assn"
  unfolding TRACE'_alt_def
  by sepref

lemmas [sepref_fr_rules] = TRACE'_impl.refine

end

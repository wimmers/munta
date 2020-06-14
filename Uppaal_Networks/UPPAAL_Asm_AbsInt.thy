theory UPPAAL_Asm_AbsInt
imports
  UPPAAL_Asm
  "HOL.List"
begin

type_synonym 'a astate = "addr \<rightharpoonup> 'a"
type_synonym cpstate = "stack * rstate * flag * nat list"
type_synonym collect_ctx = "(cpstate set astate) * (addr set)"

fun collect_ctx_dom :: "collect_ctx \<Rightarrow> addr set" where "collect_ctx_dom (_, d) = d"
fun collect_ctx_lookup :: "collect_ctx \<Rightarrow> addr \<Rightarrow> cpstate set option" where "collect_ctx_lookup (m, _) k = m k"

fun def :: "'a \<Rightarrow> 'a option \<Rightarrow> 'a" where
  "def _ (Some v) = v" |
  "def d _ = d"

fun states_domain :: "state set \<Rightarrow> addr set" where
  "states_domain states = fst ` states"

fun states_at :: "state set \<Rightarrow> addr \<Rightarrow> cpstate set" where
  "states_at states pc = snd ` {s\<in>states. fst s = pc}"

fun propagate :: "collect_ctx \<Rightarrow> state set \<Rightarrow> collect_ctx" where
  "propagate (oldst, olddom) ss =
    (let newdom = olddom \<union> states_domain ss;
         newmap = (\<lambda>pc.
            let news = states_at ss pc in
            case (oldst pc, news) of
              (Some oldss, newss) \<Rightarrow> Some (oldss \<union> news) |
              (None, newss) \<Rightarrow> if newss = {} then None else Some newss)
    in (newmap, newdom))"

fun step_all :: "instr \<Rightarrow> addr \<Rightarrow> cpstate set \<Rightarrow> state set" where
  "step_all op pc instates =
    {outs. \<exists>ins\<in>instates. Some outs = step op (pc, ins)}" (* TODO: How to handle failure? (None) *)

lemma[code]: "step_all op pc (set instates) =
  Option.these (set (map (\<lambda>ins. step op (pc, ins)) instates))" using in_these_eq by fastforce

fun collect_step :: "program \<Rightarrow> collect_ctx \<Rightarrow> collect_ctx option" where
  "collect_step prog ctx =
    fold (\<lambda>pc ost.
      case (ost, prog pc) of
        (Some ctx, Some op) \<Rightarrow>
          let ins = def {} (collect_ctx_lookup ctx pc);
              res = step_all op pc ins in
          Some (propagate ctx res)
        | _ \<Rightarrow> None
    ) (sorted_list_of_set (collect_ctx_dom ctx)) (Some ctx)"

fun collect_loop :: "program \<Rightarrow> fuel \<Rightarrow> collect_ctx \<Rightarrow> collect_ctx option" where
  "collect_loop prog 0 st = Some st" |
  "collect_loop prog (Suc n) st =
    (case collect_step prog st of
      Some nst \<Rightarrow> collect_loop prog n nst |
      None \<Rightarrow> None)"

end
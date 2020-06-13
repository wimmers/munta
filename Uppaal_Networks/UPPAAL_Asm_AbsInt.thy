theory UPPAAL_Asm_AbsInt
imports
  UPPAAL_Asm
  "HOL.List"
begin

type_synonym 'a astate = "addr \<rightharpoonup> 'a"
type_synonym cpstate = "stack * rstate * flag * nat list"
type_synonym cstate = "(cpstate set astate) * (addr set)"

fun cdom :: "cstate \<Rightarrow> addr set" where
  "cdom (_, d) = d"

fun lookup :: "cstate \<Rightarrow> addr \<Rightarrow> cpstate set option" where
  "lookup (m, _) k = m k"

find_consts "'a \<Rightarrow> 'a option \<Rightarrow> 'a"
find_consts "('a \<Rightarrow> 'b option) \<Rightarrow> 'a set \<Rightarrow> 'b set"
find_consts "'a set \<Rightarrow> 'a list"
find_consts "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list"

fun def :: "'a \<Rightarrow> 'a option \<Rightarrow> 'a" where
  "def _ (Some v) = v" |
  "def d _ = d"

fun states_domain :: "state set \<Rightarrow> addr set" where
  "states_domain states = fst ` states"

fun states_at :: "state set \<Rightarrow> addr \<Rightarrow> cpstate set" where
  "states_at states pc = snd ` {s\<in>states. fst s = pc}"

fun propagate :: "cstate \<Rightarrow> state set \<Rightarrow> cstate" where
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

fun collect_step :: "program \<Rightarrow> cstate \<Rightarrow> cstate option" where
  "collect_step prog st =
    fold (\<lambda>pc ost.
      case (ost, prog pc) of
        (Some st, Some op) \<Rightarrow>
          let ins = def {} (lookup st pc);
              res = step_all op pc ins in
          Some (propagate st res)
        | _ \<Rightarrow> None
    ) (sorted_list_of_set (cdom st)) (Some st)"

fun collect_loop :: "program \<Rightarrow> fuel \<Rightarrow> cstate \<Rightarrow> cstate option" where
  "collect_loop prog 0 st = Some st" |
  "collect_loop prog (Suc n) st =
    (case collect_step prog st of
      Some nst \<Rightarrow> collect_loop prog n nst |
      None \<Rightarrow> None)"

end
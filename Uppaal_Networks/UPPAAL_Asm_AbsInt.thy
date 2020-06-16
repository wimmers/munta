theory UPPAAL_Asm_AbsInt
imports
  UPPAAL_Asm
  "HOL.List"
  "HOL.Complete_Lattices"
begin

subsection "State Map"

datatype 'a state_map = SM "addr \<rightharpoonup> 'a"
fun entry :: "(addr * 'a) set \<Rightarrow> 'a set state_map" where
  "entry states = SM (\<lambda>pc. if (\<exists>st. (pc, st) \<in> states) then Some {st. (pc, st) \<in> states} else None)"
fun lookup :: "'a state_map \<Rightarrow> addr \<Rightarrow> 'a option" where "lookup (SM m) = m"
fun domain :: "'a state_map \<Rightarrow> addr set" where "domain (SM m) = dom m"

lemma state_map_eq_fwd: "(\<forall>p. lookup m p = lookup n p) \<Longrightarrow> m = n"
proof -
  assume lookeq: "\<forall>p. lookup m p = lookup n p"
  obtain mm where mm: "m = SM mm" using lookup.cases by blast
  obtain nm where nm: "n = SM nm" using lookup.cases by blast
  have "mm = nm" using lookeq nm mm by auto
  thus "m = n" using mm nm by blast
qed

lemma "(\<forall>p. lookup m p = lookup n p) \<longleftrightarrow> m = n" using state_map_eq_fwd by auto

(* -- *)
(* From HOL_IMP.Abs_Int0 *)
instantiation option :: (order)order
begin
  fun less_eq_option where
    "Some x \<le> Some y = (x \<le> y)" |
    "None \<le> y = True" |
    "Some _ \<le> None = False"
  
  definition less_option where "x < (y::'a option) = (x \<le> y \<and> \<not> y \<le> x)"
  
  lemma le_None[simp]: "(x \<le> None) = (x = None)"
  by (cases x) simp_all
  
  lemma Some_le[simp]: "(Some x \<le> u) = (\<exists>y. u = Some y \<and> x \<le> y)"
  by (cases u) auto
  
  instance proof (standard, goal_cases)
    case 1 show ?case by(rule less_option_def)
  next
    case (2 x) show ?case by(cases x, simp_all)
  next
    case (3 x y z) thus ?case by(cases z, simp, cases y, simp, cases x, auto)
  next
    case (4 x y) thus ?case by(cases y, simp, cases x, auto)
  qed
end
(* -- *)

instantiation state_map :: (order) order
begin
  definition less_eq_state_map :: "('a::order)state_map \<Rightarrow> 'a state_map \<Rightarrow> bool" where
  "C1 \<le> C2 \<longleftrightarrow> (\<forall>p. lookup C1 p \<le> lookup C2 p)"
  
  definition less_state_map :: "'a state_map \<Rightarrow> 'a state_map \<Rightarrow> bool" where
  "less_state_map x y = (x \<le> y \<and> \<not> y \<le> x)"
  
  instance proof (standard, goal_cases)
    case 1 show ?case by(simp add: less_state_map_def)
  next
    case 2 thus ?case by(auto simp: less_eq_state_map_def)
  next
    case 3 thus ?case using less_eq_state_map_def order_trans by fastforce
  next
    case 4 thus ?case by (simp add: less_eq_state_map_def dual_order.antisym state_map_eq_fwd)
  qed
end

(*
notation
  Sup ("\<Squnion>") and
  Inf ("\<Sqinter>") and
  bot ("\<bottom>") and
  top ("\<top>")

instantiation state_map :: (complete_lattice) complete_lattice
begin
definition "\<Sqinter>A = {x. \<Sqinter>((\<lambda>B. x \<in> B) ` A)}"
definition "\<Squnion>A = {x. \<Squnion>((\<lambda>B. x \<in> B) ` A)}"
instance
  by standard (auto simp add: less_eq_set_def Inf_set_def Sup_set_def le_fun_def)
qed*)


subsection "Collecting Semantics"

type_synonym collect_state = "stack * rstate * flag * nat list"
type_synonym collect_ctx = "collect_state set state_map"

fun def :: "'a \<Rightarrow> 'a option \<Rightarrow> 'a" where
  "def _ (Some v) = v" |
  "def d _ = d"

fun states_domain :: "(addr * 'a) set \<Rightarrow> addr set" where
  "states_domain states = fst ` states"

fun states_at :: "(addr * 'a) set \<Rightarrow> addr \<Rightarrow> 'a set" where
  "states_at states pc = snd ` {s\<in>states. fst s = pc}"

fun propagate :: "'a set state_map \<Rightarrow> (addr * 'a) set \<Rightarrow> 'a set state_map" where
  "propagate (SM oldmap) ss =
    (let newmap = (\<lambda>pc.
            let news = states_at ss pc in
            case (oldmap pc, news) of
              (Some oldss, newss) \<Rightarrow> Some (oldss \<union> news) |
              (None, newss) \<Rightarrow> if newss = {} then None else Some newss)
    in (SM newmap))"

fun step_all :: "instr \<Rightarrow> addr \<Rightarrow> collect_state set \<Rightarrow> state set" where
  "step_all op pc instates =
    {outs. \<exists>ins\<in>instates. Some outs = step op (pc, ins)}" (* TODO: How to handle failure? (None) *)

fun collect_step :: "program \<Rightarrow> collect_ctx \<Rightarrow> collect_ctx option" where
  "collect_step prog ctx =
    fold (\<lambda>pc ost.
      case (ost, prog pc) of
        (Some ctx, Some op) \<Rightarrow>
          let ins = def {} (lookup ctx pc);
              res = step_all op pc ins in
          Some (propagate ctx res)
        | _ \<Rightarrow> None
    ) (sorted_list_of_set (domain ctx)) (Some ctx)"

fun collect_loop :: "program \<Rightarrow> fuel \<Rightarrow> collect_ctx \<Rightarrow> collect_ctx option" where
  "collect_loop prog 0 st = Some st" |
  "collect_loop prog (Suc n) st =
    (case collect_step prog st of
      Some nst \<Rightarrow> collect_loop prog n nst |
      None \<Rightarrow> None)"

end
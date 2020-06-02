theory UPPAAL_Asm_AbsInt
imports
  UPPAAL_Asm
  "HOL-Data_Structures.RBT_Map"
  "HOL.List"
begin

type_synonym 'a astate = "(addr * 'a) rbt"
type_synonym cpstate = "stack * rstate * flag * nat list"
type_synonym cstate = "cpstate list astate"

find_consts "'a \<Rightarrow> 'a option \<Rightarrow> 'a"
find_consts "('a \<Rightarrow> 'b option) \<Rightarrow> 'a set \<Rightarrow> 'b set"
find_consts "'a list \<Rightarrow> 'a list"
find_consts "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list"

fun def :: "'a \<Rightarrow> 'a option \<Rightarrow> 'a" where
  "def _ (Some v) = v" |
  "def d _ = d"

fun keys :: "('a * 'b) rbt \<Rightarrow> 'a list" where
  "keys t = map (\<lambda>(k, _) \<Rightarrow> k) (inorder t)"

(*fun insert :: "'a \<Rightarrow> 'b set \<Rightarrow> ('a::linorder * 'b set) rbt \<Rightarrow> ('a * 'b set) rbt" where
  "insert k v t = update k
    (case lookup t k of
      Some vv \<Rightarrow> v \<union> vv |
      None \<Rightarrow> v) t"*)

(*fun merge :: "('a::linorder * 'b set) rbt \<Rightarrow> ('a * 'b set) rbt \<Rightarrow> ('a * 'b set) rbt" where
  "merge a b = fold (\<lambda>(k, v). insert k v) (inorder b) a"*)

fun insert :: "'a \<Rightarrow> 'b list \<Rightarrow> ('a::linorder * 'b list) rbt \<Rightarrow> ('a * 'b list) rbt" where
  "insert k v t = update k
    (case lookup t k of
      Some vv \<Rightarrow> remdups (v @ vv) |
      None \<Rightarrow> v) t"

fun merge :: "('a::linorder * 'b list) rbt \<Rightarrow> ('a * 'b list) rbt \<Rightarrow> ('a * 'b list) rbt" where
  "merge a b = fold (\<lambda>(k, v). insert k v) (inorder b) a"

fun step_all :: "instr \<Rightarrow> addr \<Rightarrow> cpstate list \<Rightarrow> state list" where
  "step_all op pc instates =
    List.map_filter (\<lambda>ins. step op (pc, ins)) instates"

fun collect_step :: "program \<Rightarrow> cstate \<Rightarrow> cstate option" where
  "collect_step prog st =
    fold (\<lambda>pc ost.
      case (ost, prog pc) of
        (Some st, Some op) \<Rightarrow>
          let ins = def [] (lookup st pc) in
          let res = step_all op pc ins in
          Some (fold (\<lambda>(pc, pst) st. insert pc [pst] st) res st)
        | _ \<Rightarrow> None
    ) (keys st) (Some st)"

fun collect_loop :: "program \<Rightarrow> fuel \<Rightarrow> cstate \<Rightarrow> cstate option" where
  "collect_loop prog 0 st = Some st" |
  "collect_loop prog (Suc n) st =
    (case collect_step prog st of
      Some nst \<Rightarrow> collect_loop prog n (merge st nst) |
      None \<Rightarrow> None)"

end
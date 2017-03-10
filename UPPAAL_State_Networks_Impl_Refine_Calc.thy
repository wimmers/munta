theory UPPAAL_State_Networks_Impl_Refine_Calc
  imports UPPAAL_State_Networks_Impl_Refine "$AFP/Gabow_SCC/Gabow_SCC_Code"
begin

term "compute_SCC_code \<lparr> gi_V = (\<lambda> x. True), gi_E = (\<lambda> x. [3]), gi_V0 = [1], \<dots> = 3 \<rparr>"
term "gi_V \<lparr> gi_V = (\<lambda> x. True), gi_E = (\<lambda> x. [3]), gi_V0 = [1] \<rparr>"

text \<open>
  Efficiently calculate shortest paths in a graph with non-negative edge weights,
  and where the only cycles are 0-cycles.
\<close>
definition
"calc_shortest_scc_paths G n \<equiv>
let
  sccs = compute_SCC_tr G;
  d = repeat None n @ [Some 0];
  d = (
    fold
      (\<lambda> vs d.
        fold
          (\<lambda> u d.
            fold
              (\<lambda> v d.
                case d ! u of
                  None \<Rightarrow> d
                | Some du \<Rightarrow>
                  case d ! v of
                    None \<Rightarrow> d[v := Some (du + more G u v)]
                  | Some dv \<Rightarrow>
                      if du + more G u v < dv
                      then d[v := Some(du + more G u v)]
                      else d
              )
              (gi_E G u)
              d
          )
          vs
          d
      )
      sccs
      d
  );
  d = (
    fold
      (\<lambda> vs d.
        let
          dscc =
            fold
            (\<lambda> v dscc.
              case dscc of
                None \<Rightarrow> d ! v
              | Some d' \<Rightarrow>
                  case d ! v of
                    None \<Rightarrow> dscc
                  | Some dv \<Rightarrow> Some (min dv d')
            )
            vs
            None
        in
          fold (\<lambda> v d. d[v:=dscc]) vs d
      )
      sccs
      d
  )
in d
"

context UPPAAL_Reachability_Problem_precompiled_defs
begin

context
  fixes q c :: nat
begin

  definition "n \<equiv> length (trans ! q)"

  definition "V \<equiv> \<lambda> v. v \<le> n"

  definition "
    bound_g l \<equiv>
      Max ({0} \<union> \<Union> ((\<lambda> (x, d). if x = c then {d} else {}) ` clkp_set'' q l))
    "

  definition "
    bound_inv l \<equiv>
      Max ({0} \<union> \<Union> ((\<lambda> (x, d). if x = c then {d} else {}) ` collect_clock_pairs (inv ! q ! l)))
  "

  definition "
    bound l \<equiv> max (bound_g l) (bound_inv l)
  "

definition "
  resets l \<equiv>
    fold
    (\<lambda> (g, a, r, l') xs. if l' \<in> set xs \<or> c \<in> fst ` collect_store'' r then xs else (l' # xs))
    (trans ! q ! l)
    []
"

definition "
  E l \<equiv> if l = n then [0..<n] else resets l
"

definition "
  W l l' \<equiv> if l = n then - bound l' else 0
"

definition "
  G \<equiv> \<lparr> gi_V = V, gi_E = E, gi_V0 = [n], \<dots> = W \<rparr>
"

definition "
  local_ceiling \<equiv>
  let
    w = calc_shortest_scc_paths G n
  in
    map (\<lambda> x. case x of None \<Rightarrow> 0 | Some x \<Rightarrow> -x) w
"

end

definition "
  k \<equiv>
    rev $
    fold
      (\<lambda> q xs.
        (\<lambda> x. rev x # xs) $
        fold
          (\<lambda> l xs.
            (\<lambda> x. (0 # rev x) # xs) $
            fold
              (\<lambda> c xs. local_ceiling q c ! l # xs)
              [1..<Suc m]
              []
          )
          [0..<n q]
          []
      )
      [0..<p]
      []
"

end



no_notation bitAND (infixr "AND" 64)


definition p where "p == 3"

definition m where "m == 3"

definition global_ceiling where "global_ceiling == [0, 808, 808, 26]"

definition max_steps where "max_steps == 10000"

definition invariants where
  "invariants == [[[], [], [acconstraint.LE 3 26], [acconstraint.LE 3 0]], [[], [acconstraint.LE 1 808], [], [acconstraint.LE 1 52]], [[], [acconstraint.LE 2 808], [acconstraint.LE 2 52]]]"

definition transitions where
  "transitions == [[[(50, In 20, 54, 1)], [(60, In 18, 64, 0), (70, Out 17, 78, 1), (84, In 20, 92, 2)], [(98, Out 13, 106, 3)], [(112, Out 21, 120, 0)]], [[(174, Out 20, 178, 1), (184, In 13, 188, 0), (194, In 13, 198, 3), (204, In 17, 208, 3)], [(214, Out 18, 232, 0), (238, In 13, 246, 3), (252, Sil 0, 260, 2)], [(266, Sil 0, 270, 1)], [(276, Out 20, 284, 1), (290, In 13, 298, 3)]], [[(346, Out 20, 350, 1), (356, In 21, 360, 0), (366, In 21, 370, 2), (376, In 17, 380, 2)], [(386, Out 18, 404, 0), (410, In 21, 418, 2)], [(424, Out 20, 432, 1), (438, In 21, 446, 2)]]]"

definition prog where
  "prog == [Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 26)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 26)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (STOREC 3 0)), Some (INSTR (HALT)), Some (INSTR (PUSH (-1))), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (STOREC 3 0)), Some (INSTR (HALT)), Some (INSTR (PUSH (-2))), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (CEXP (acconstraint.GE 3 26)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH (-26))), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 3)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (CEXP (acconstraint.LT 3 26)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 26)), Some (INSTR (HALT)), Some (INSTR (STOREC 3 0)), Some (INSTR (HALT)), Some (INSTR (PUSH (-1))), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (CEXP (acconstraint.LT 3 26)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 26)), Some (INSTR (HALT)), Some (INSTR (STOREC 3 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 4)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (CEXP (acconstraint.LE 3 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (STOREC 3 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 5)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 2)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 808)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 2)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 808)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 2)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 52)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 2)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 52)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (STOREC 1 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (STOREC 1 0)), Some (INSTR (HALT)), Some (INSTR (PUSH (-4))), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (STOREC 1 0)), Some (INSTR (HALT)), Some (INSTR (PUSH (-4))), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (STOREC 1 0)), Some (INSTR (HALT)), Some (INSTR (PUSH (-3))), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (CEXP (acconstraint.LE 1 808)), Some (INSTR (COPY)), Some (INSTR (JMPZ 219)), Some (CEXP (acconstraint.GE 1 808)), Some (INSTR (AND)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 2)), Some (INSTR (HALT)), Some (INSTR (PUSH (-808))), Some (INSTR (HALT)), Some (INSTR (PUSH 2)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 808)), Some (INSTR (HALT)), Some (INSTR (STOREC 1 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 2)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (CEXP (acconstraint.LT 1 52)), Some (INSTR (HALT)), Some (INSTR (PUSH 2)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 52)), Some (INSTR (HALT)), Some (INSTR (STOREC 1 0)), Some (INSTR (HALT)), Some (INSTR (PUSH (-4))), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (CEXP (acconstraint.GE 1 52)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 2)), Some (INSTR (HALT)), Some (INSTR (PUSH (-52))), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (CEXP (acconstraint.LT 1 52)), Some (INSTR (HALT)), Some (INSTR (PUSH 2)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 52)), Some (INSTR (HALT)), Some (INSTR (STOREC 1 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (CEXP (acconstraint.LT 1 52)), Some (INSTR (HALT)), Some (INSTR (PUSH 2)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 52)), Some (INSTR (HALT)), Some (INSTR (STOREC 1 0)), Some (INSTR (HALT)), Some (INSTR (PUSH (-4))), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 3)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 808)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 3)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 808)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 3)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 52)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 3)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 52)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (STOREC 2 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (STOREC 2 0)), Some (INSTR (HALT)), Some (INSTR (PUSH (-5))), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (STOREC 2 0)), Some (INSTR (HALT)), Some (INSTR (PUSH (-5))), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (STOREC 2 0)), Some (INSTR (HALT)), Some (INSTR (PUSH (-3))), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (CEXP (acconstraint.LE 2 808)), Some (INSTR (COPY)), Some (INSTR (JMPZ 391)), Some (CEXP (acconstraint.GE 2 808)), Some (INSTR (AND)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 3)), Some (INSTR (HALT)), Some (INSTR (PUSH (-808))), Some (INSTR (HALT)), Some (INSTR (PUSH 3)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 808)), Some (INSTR (HALT)), Some (INSTR (STOREC 2 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 2)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (CEXP (acconstraint.LT 2 52)), Some (INSTR (HALT)), Some (INSTR (PUSH 3)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 52)), Some (INSTR (HALT)), Some (INSTR (STOREC 2 0)), Some (INSTR (HALT)), Some (INSTR (PUSH (-5))), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (CEXP (acconstraint.LT 2 52)), Some (INSTR (HALT)), Some (INSTR (PUSH 3)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 52)), Some (INSTR (HALT)), Some (INSTR (STOREC 2 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (INSTR (PUSH 1)), Some (INSTR (HALT)), Some (CEXP (acconstraint.LT 2 52)), Some (INSTR (HALT)), Some (INSTR (PUSH 3)), Some (INSTR (HALT)), Some (INSTR (PUSH 0)), Some (INSTR (HALT)), Some (INSTR (PUSH 52)), Some (INSTR (HALT)), Some (INSTR (STOREC 2 0)), Some (INSTR (HALT)), Some (INSTR (PUSH (-5))), Some (INSTR (HALT))]"

lemmas [code] =
  UPPAAL_Reachability_Problem_precompiled_defs.k_def
  UPPAAL_Reachability_Problem_precompiled_defs.local_ceiling_def
  UPPAAL_Reachability_Problem_precompiled_defs.n_def
  UPPAAL_Reachability_Problem_precompiled_defs.G_def
  UPPAAL_Reachability_Problem_precompiled_defs.W_def
  UPPAAL_Reachability_Problem_precompiled_defs.V_def
  UPPAAL_Reachability_Problem_precompiled_defs.E_def
  UPPAAL_Reachability_Problem_precompiled_defs.resets_def
  UPPAAL_Reachability_Problem_precompiled_defs.bound_def
  UPPAAL_Reachability_Problem_precompiled_defs.bound_inv_def
  UPPAAL_Reachability_Problem_precompiled_defs.bound_g_def

export_code UPPAAL_Reachability_Problem_precompiled_defs.k checking SML_imp

value \<open>
  UPPAAL_Reachability_Problem_precompiled_defs.k p m max_steps invariants transitions prog
\<close>

value \<open>
  UPPAAL_Reachability_Problem_precompiled_defs.G max_steps invariants transitions prog 0 0
\<close>

value \<open>
  map
  (gi_V (UPPAAL_Reachability_Problem_precompiled_defs.G max_steps invariants transitions prog 0 0))
  [0..<10]
\<close>

value \<open>
  map
  (gi_E (UPPAAL_Reachability_Problem_precompiled_defs.G max_steps invariants transitions prog 0 3))
  [0..<5]
\<close>

value \<open>
  UPPAAL_Reachability_Problem_precompiled_defs.local_ceiling max_steps invariants transitions prog 0 3
\<close>

value \<open>
  UPPAAL_Reachability_Problem_precompiled_defs.local_ceiling max_steps invariants transitions prog 1 1
\<close>

value \<open>
   UPPAAL_Reachability_Problem_precompiled_defs.local_ceiling max_steps invariants transitions prog 2 2
\<close>

value \<open>
  map (\<lambda> i.
    map (more (UPPAAL_Reachability_Problem_precompiled_defs.G max_steps invariants transitions prog 0 3) i)
      [0..<5])
  [0..<5]
\<close>

value \<open>
  map (\<lambda> i.
    map (more (UPPAAL_Reachability_Problem_precompiled_defs.G max_steps invariants transitions prog 0 0) i)
      (gi_E (UPPAAL_Reachability_Problem_precompiled_defs.G max_steps invariants transitions prog 0 3) i))
  [0..<5]
\<close>

value \<open>
  compute_SCC_tr (UPPAAL_Reachability_Problem_precompiled_defs.G max_steps invariants transitions prog 0 3)
\<close>

value \<open>
  UPPAAL_Reachability_Problem_precompiled_defs.check_ceiling p m max_steps invariants transitions prog
  (map (map (map nat))
  (UPPAAL_Reachability_Problem_precompiled_defs.k p m max_steps invariants transitions prog))
\<close>

text \<open>Individual parts of clock ceiling check\<close>
context UPPAAL_Reachability_Problem_precompiled_defs
begin

context
  fixes k :: "nat list list list"
    begin

  definition
    "check1 \<equiv> \<forall> i < p. \<forall> l < length (trans ! i). \<forall> (x, m) \<in> clkp_set'' i l. m \<le> k ! i ! l ! x"
  definition
    "check2 \<equiv> \<forall> i < p. \<forall> l < length (trans ! i). \<forall> (x, m) \<in> collect_clock_pairs (inv ! i ! l).
      m \<le> k ! i ! l ! x"
  definition
    "check3 \<equiv> \<forall> i < p. \<forall> l < length (trans ! i). \<forall> (g, a, r, l') \<in> set (trans ! i ! l).
     \<forall> c \<in> {0..<m+1} - fst ` collect_store'' r. k ! i ! l' ! c \<le> k ! i ! l ! c"
  definition
    "check4 \<equiv> length k = p \<and> (\<forall> i < p. length (k ! i) = length (trans ! i))"
  definition
    "check5 \<equiv> \<forall> xs \<in> set k. \<forall> xxs \<in> set xs. length xxs = m + 1"
  definition
    "check6 \<equiv> \<forall> i < p. \<forall> l < length (trans ! i). k ! i ! l ! 0 = 0"

 end
end

lemmas [code] =
  UPPAAL_Reachability_Problem_precompiled_defs.check1_def
  UPPAAL_Reachability_Problem_precompiled_defs.check2_def
  UPPAAL_Reachability_Problem_precompiled_defs.check3_def
  UPPAAL_Reachability_Problem_precompiled_defs.check4_def
  UPPAAL_Reachability_Problem_precompiled_defs.check5_def
  UPPAAL_Reachability_Problem_precompiled_defs.check6_def

value \<open>
  UPPAAL_Reachability_Problem_precompiled_defs.check1 p max_steps invariants transitions prog
  (map (map (map nat))
  (UPPAAL_Reachability_Problem_precompiled_defs.k p m max_steps invariants transitions prog))
\<close>

value \<open>
  UPPAAL_Reachability_Problem_precompiled_defs.check2 p invariants transitions
  (map (map (map nat))
  (UPPAAL_Reachability_Problem_precompiled_defs.k p m max_steps invariants transitions prog))
\<close>

value \<open>
  UPPAAL_Reachability_Problem_precompiled_defs.check3 p m transitions prog
  (map (map (map nat))
  (UPPAAL_Reachability_Problem_precompiled_defs.k p m max_steps invariants transitions prog))
\<close>

value \<open>
  UPPAAL_Reachability_Problem_precompiled_defs.check4 p transitions
  (map (map (map nat))
  (UPPAAL_Reachability_Problem_precompiled_defs.k p m max_steps invariants transitions prog))
\<close>

value \<open>
  UPPAAL_Reachability_Problem_precompiled_defs.check5 m
  (map (map (map nat))
  (UPPAAL_Reachability_Problem_precompiled_defs.k p m max_steps invariants transitions prog))
\<close>

value \<open>
  UPPAAL_Reachability_Problem_precompiled_defs.check6 p transitions
  (map (map (map nat))
  (UPPAAL_Reachability_Problem_precompiled_defs.k p m max_steps invariants transitions prog))
\<close>

text \<open>Attempt on definition in \<open>nres\<close> monad\<close>

hide_const "instr.RETURN"

(*
text \<open>
  Efficiently calculate shortest paths in a graph with non-negative edge weights,
  and where the only cycles are 0-cycles.
\<close>
definition
"calc_shortest_scc_paths G n \<equiv>
do {
  sccs \<leftarrow> compute_SCC_code G;
  d \<leftarrow> RETURN (repeat None n);
  d \<leftarrow> RETURN (
    fold
      (\<lambda> vs d.
        fold
          (\<lambda> u d.
            fold
              (\<lambda> v d.
                case d ! u of
                  None \<Rightarrow> d
                | Some du \<Rightarrow>
                  case d ! v of
                    None \<Rightarrow> d[v:=Some (du + more G u v)]
                  | Some dv \<Rightarrow>
                      if du + more G u v < dv
                      then d[v := Some(du + more G u v)]
                      else d
              )
              (gi_E G u)
              d
          )
          vs
          d
      )
      sccs
      d
  );
  d \<leftarrow> RETURN (
    fold
      (\<lambda> vs d.
        let
          dscc =
            fold
            (\<lambda> v dscc.
              case dscc of
                None \<Rightarrow> d ! v
              | Some d' \<Rightarrow>
                  case d ! v of
                    None \<Rightarrow> dscc
                  | Some dv \<Rightarrow> Some (min dv d')
            )
            vs
            None
        in
          fold (\<lambda> v d. d[v:=dscc]) vs d
      )
      sccs
      d
  );
  RETURN d
}
"

context UPPAAL_Reachability_Problem_precompiled_defs
begin

sepref_register p trans m max_steps inv prog

context
  fixes q c :: nat
begin

  definition "n \<equiv> length (trans ! q)"

  definition "V \<equiv> \<lambda> v. v < n"

definition "
  bound_g l \<equiv>
    Max (\<Union> ((\<lambda> (x, d). if x = c then {d} else {}) ` clkp_set'' q l))
  "

definition "
  bound_inv l \<equiv>
    Max (\<Union> ((\<lambda> (x, d). if x = c then {d} else {}) ` collect_clock_pairs (inv ! q ! l)))
"

definition "
  bound l \<equiv> max (bound_g l) (bound_inv l)
"

(*
definition "
  max_bound = fold max (map bound [0..<n]) 0
"
*)

definition "
  resets l \<equiv>
    fold
    (\<lambda> (g, a, r, l') xs. if l' \<in> set xs \<or> c \<in> fst ` collect_store'' r then xs else (l' # xs))
    (trans ! q ! l)
    []
"

definition "
  E l \<equiv> n # resets l
"

definition "
  W l l' \<equiv> if l = n then - bound l' else 0
"

definition "
  G \<equiv> \<lparr> gi_V = V, gi_E = E, gi_V0 = [n], \<dots> = W \<rparr>
"

definition "
  local_ceiling \<equiv>
  do {
    w \<leftarrow> calc_shortest_scc_paths G n;
    RETURN (map (\<lambda> x. case x of None \<Rightarrow> 0 | Some x \<Rightarrow> -x) w)
  }
"

sepref_register q c

lemma [sepref_import_param]: "(max_steps, max_steps) \<in> Id" by simp
lemma [sepref_import_param]: "(inv, inv) \<in> Id" by simp
lemma [sepref_import_param]: "(trans, trans) \<in> Id" by simp
lemma [sepref_import_param]: "(prog, prog) \<in> Id" by simp

sepref_definition local_ceiling_impl is
  "uncurry0 (RETURN local_ceiling)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  apply sepref_dbg_keep
    apply sepref_dbg_trans_keep

end

definition "
  k \<equiv>
    nfoldli
      [0..<p]
      (\<lambda> x. True)
      (\<lambda> q xs.
        nfoldli
          [0..<n q]
          (\<lambda> x. True)
          (\<lambda> l xs.
            nfoldli
            [0..<m]
            (\<lambda> x. True)
            (\<lambda> c xs. do {k \<leftarrow> local_ceiling q c; RETURN (k ! l # xs)})
            [] \<bind> (\<lambda> x. RETURN (rev x # xs))
          )
          [] \<bind> (\<lambda> x. RETURN (rev x # xs))
      )
      [] \<bind> (RETURN o rev)
"

lemma [sepref_import_param]: "(p, p) \<in> Id" by simp

term local_ceiling

sepref_definition local_ceiling is
  ""

sepref_definition k_impl is
  "uncurry0 (RETURN k)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding k_def
  apply sepref_dbg_keep
    apply sepref_dbg_monadify_keep

end

term "UPPAAL_Reachability_Problem_precompiled_defs.k"

thm UPPAAL_Reachability_Problem_precompiled_defs.k_def

concrete_definition k_impl
  uses UPPAAL_Reachability_Problem_precompiled_defs.k_def

lemmas [code] =
  UPPAAL_Reachability_Problem_precompiled_defs.k_def

thm k_impl_def term k_impl

export_code UPPAAL_Reachability_Problem_precompiled_defs.k checking SML_imp

*)

end
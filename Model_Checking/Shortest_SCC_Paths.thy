theory Shortest_SCC_Paths
  imports Gabow_SCC.Gabow_SCC_Code
begin

definition compute_SCC_tr ::
  "('a :: hashable \<Rightarrow> bool, 'a \<Rightarrow> 'a list, 'a list, 'b) gen_g_impl_scheme \<Rightarrow> _" where
  "compute_SCC_tr =
    Gabow_SCC_Code.compute_SCC_tr (=) bounded_hashcode_nat (def_hashmap_size TYPE('a))"

term "compute_SCC_tr \<lparr> gi_V = (\<lambda> x. True), gi_E = (\<lambda> x. [3]), gi_V0 = [1], \<dots> = 3 \<rparr>"

text \<open>
  Efficiently calculate shortest paths in a graph with non-negative edge weights,
  and where the only cycles are 0-cycles.
\<close>
definition
"calc_shortest_scc_paths G n \<equiv>
let
  sccs = compute_SCC_tr G;
  d = replicate n None @ [Some 0];
  d = (
    fold
      (\<lambda> vs d.
        fold
          (\<lambda> u d.
            fold
              (\<lambda> v d.
                case d ! u of
                  None \<Rightarrow> d
                | Some du \<Rightarrow> (
                  case d ! v of
                    None \<Rightarrow> d[v := Some (du + more G u v)]
                  | Some dv \<Rightarrow>
                      if du + more G u v < dv
                      then d[v := Some (du + more G u v)]
                      else d
                  )
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
              | Some d' \<Rightarrow> (
                  case d ! v of
                    None \<Rightarrow> dscc
                  | Some dv \<Rightarrow> Some (min dv d')
                )
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

end
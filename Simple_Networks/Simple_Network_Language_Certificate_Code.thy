theory Simple_Network_Language_Certificate_Code
  imports
    Simple_Network_Language_Certificate
    Simple_Network_Language_Export_Code
    Simple_Network_Language_Certificate_Checking
begin

paragraph \<open>Optimized code equations\<close>

lemmas [code_unfold] = imp_for_imp_for'

definition dbm_subset'_impl'_int
  :: "nat \<Rightarrow> int DBMEntry Heap.array \<Rightarrow> int DBMEntry Heap.array \<Rightarrow> bool Heap"
  where [symmetric, int_folds]:
    "dbm_subset'_impl'_int = dbm_subset'_impl'"

lemma less_eq_dbm_le_int[int_folds]:
  "(\<le>) = dbm_le_int"
  unfolding dbm_le_dbm_le_int less_eq ..

schematic_goal dbm_subset'_impl'_int_code[code]:
  "dbm_subset'_impl'_int \<equiv> \<lambda>m a b.
    do {
    imp_for 0 ((m + 1) * (m + 1)) Heap_Monad.return
      (\<lambda>i _. do {
        x \<leftarrow> Array.nth a i; y \<leftarrow> Array.nth b i; Heap_Monad.return (dbm_le_int x y)
      })
      True
    }
"
  unfolding dbm_subset'_impl'_int_def[symmetric] dbm_subset'_impl'_def int_folds .


definition dbm_subset_impl_int
  :: "nat \<Rightarrow> int DBMEntry Heap.array \<Rightarrow> int DBMEntry Heap.array \<Rightarrow> bool Heap"
  where [symmetric, int_folds]:
    "dbm_subset_impl_int = dbm_subset_impl"

schematic_goal dbm_subset_impl_int_code[code]:
  "dbm_subset_impl_int \<equiv> ?i"
  unfolding dbm_subset_impl_int_def[symmetric] dbm_subset_impl_def
  unfolding int_folds
  .

lemmas [code_unfold] = int_folds

export_code state_space in SML module_name Test

hide_const Parser_Combinator.return
hide_const Error_Monad.return

definition
  "show_lit = String.implode o show"

definition "rename_state_space \<equiv> \<lambda>dc ids_to_names (broadcast, automata, bounds) L\<^sub>0 s\<^sub>0 formula.
  let _ = println (STR ''Make renaming'') in
  do {
    (m, num_states, num_actions, renum_acts, renum_vars, renum_clocks, renum_states,
      inv_renum_states, inv_renum_vars, inv_renum_clocks)
      \<leftarrow> make_renaming broadcast automata bounds;
    let _ = println (STR ''Renaming'');
    let (broadcast', automata', bounds') = rename_network
      broadcast bounds automata renum_acts renum_vars renum_clocks renum_states;
    let _ = println (STR ''Calculating ceiling'');
    let k = Simple_Network_Impl_nat_defs.local_ceiling broadcast' bounds' automata' m num_states;
    let _ = println (STR ''Running model checker'');
    let inv_renum_states' = (\<lambda>i. ids_to_names i o inv_renum_states i);
    let f = (\<lambda>show_clock
      show_state broadcast bounds' automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula.
      state_space broadcast bounds' automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula
        show_clock show_state ()
    );
    let r = do_rename_mc f dc broadcast bounds automata k STR ''_urge'' L\<^sub>0 s\<^sub>0 formula
      m num_states num_actions renum_acts renum_vars renum_clocks renum_states
      inv_renum_states' inv_renum_vars inv_renum_clocks;
    let show_clock = show o inv_renum_clocks;
    let show_state = (show_state :: _ \<Rightarrow> _ \<Rightarrow> _ \<times> int list \<Rightarrow> _) inv_renum_states inv_renum_vars;
    let renamings =
      (m, num_states, num_actions, renum_acts, renum_vars, renum_clocks, renum_states,
       inv_renum_states, inv_renum_vars, inv_renum_clocks
      );
    Result (r, show_clock, show_state, renamings, k)
  }"

definition
  "check_subsumed n xs (i :: int) M \<equiv>
  do {
    (_, b) \<leftarrow> imp_nfoldli xs (\<lambda>(_, b). return (\<not> b)) (\<lambda>M' (j, b).
      if i = j then return (j + 1, b) else do {
        b \<leftarrow> dbm_subset'_impl n M M';
        if b then return (j, True) else return (j + 1, False)
      }
    ) (0, False);
    return b
  }
"

definition
  "imp_filter_index P xs = do {
  (_, xs) \<leftarrow> imp_nfoldli xs (\<lambda>_. return True) (\<lambda>x (i :: nat, xs).
    do {
      b \<leftarrow> P i x;
      return (i + 1, if b then (x # xs) else xs)
    }
  ) (0, []);
  return (rev xs)
  }"

definition
  "filter_dbm_list n xs =
    imp_filter_index (\<lambda>i M. do {b \<leftarrow> check_subsumed n xs i M; return (\<not> b)}) xs"

partial_function (heap) imp_map :: "('a \<Rightarrow> 'b Heap) \<Rightarrow> 'a list \<Rightarrow> 'b list Heap" where
  "imp_map f xs =
  (if xs = [] then return [] else do {y \<leftarrow> f (hd xs); ys \<leftarrow> imp_map f (tl xs); return (y # ys)})"

lemma imp_map_simps[code, simp]:
  "imp_map f [] = return []"
  "imp_map f (x # xs) = do {y \<leftarrow> f x; ys \<leftarrow> imp_map f xs; return (y # ys)}"
  by (simp add: imp_map.simps)+

definition trace_state where
  "trace_state n show_clock show_state \<equiv>
  \<lambda> (l, M). do {
      let st = show_state l;
      m \<leftarrow> show_dbm_impl n show_clock show M;
      let s = ''(''  @ st @ '', ['' @ m @ ''])''; 
      let s = String.implode s;
      let _ = println s;
      return ()
  }
" for show_clock show_state

definition
  "show_str = String.implode o show"

definition parse_convert_run_print where
  "parse_convert_run_print dc s \<equiv>
   case parse json s \<bind> convert of
     Error es \<Rightarrow> do {let _ = map println es; return ()}
   | Result (ids_to_names, _, broadcast, automata, bounds, formula, L\<^sub>0, s\<^sub>0) \<Rightarrow> do {
      let r = rename_state_space dc ids_to_names (broadcast, automata, bounds) L\<^sub>0 s\<^sub>0 formula;
      case r of
        Error es \<Rightarrow> do {let _ = map println es; return ()}
      | Result (r, show_clk, show_st, renamings, k) \<Rightarrow>
        case r of None \<Rightarrow> return () | Some r \<Rightarrow>
        do {
          r \<leftarrow> r;
          let _ = STR ''Number of discrete states: '' + (length r |> show_str) |> println;
          let _ =
            STR ''Size of passed list: '' + show_str (sum_list (map (length o snd) r)) |> println;
          let n = Simple_Network_Impl.clk_set' automata |> list_of_set |> length;
          r \<leftarrow> imp_map (\<lambda> (a, b). do {
              b \<leftarrow> imp_map (return o snd) b; b \<leftarrow> filter_dbm_list n b; return (a, b)
            }) r;
          let _ = STR ''Number of discrete states: '' + show_str (length r) |> println;
          let _ = STR ''Size of passed list after removing subsumed states: ''
            + show_str (sum_list (map (length o snd) r)) |> println;
          let show_dbm = (\<lambda>M. do {
            s \<leftarrow> show_dbm_impl_all n show_clk show M;
            return (''<'' @ s @ ''>'')
          });
          _ \<leftarrow> imp_map (\<lambda> (s, xs).
          do {
            let s = show_st s;
            xs \<leftarrow> imp_map show_dbm xs;
            let _ = s @ '': '' @ show xs |> String.implode |> println;
            return ()
          }
          ) r;
          return ()
        }
  }"

ML \<open>
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

ML \<open>
fun print_timings () =
  let
    val tab = Timing.get_timings ();
    fun print_time (s, t) = writeln(s ^ ": " ^ Time.toString t);
  in map print_time tab end;
\<close>

code_printing
  constant "Show_State_Defs.tracei" \<rightharpoonup>
      (SML)   "(fn n => fn show_state => fn show_clock => fn typ => fn x => ()) _ _ _"
  and (OCaml) "(fun n show_state show_clock ty x -> ()) _ _ _"

datatype mode = Impl1 | Impl2 | Impl3 | Buechi

definition
  "distr xs \<equiv>
  let (m, d) =
  fold
    (\<lambda>x (m, d). case m x of None \<Rightarrow> (m(x \<mapsto> 1:: nat), x # d) | Some y \<Rightarrow> (m(x \<mapsto> (y + 1)), d))
    xs (Map.empty, [])
  in map (\<lambda>x. (x, the (m x))) (sort d)"

definition split_k'' :: "nat \<Rightarrow> ('a \<times> 'b list) list \<Rightarrow> ('a \<times> 'b list) list list" where
  "split_k'' k xs \<equiv> let
    width = sum_list (map (length o snd) xs) div k;
    width = (if length xs mod k = 0 then width else width + 1)
  in split_size (length o snd) width 0 [] xs"

definition
  "print_errors es = do {Heap_Monad.fold_map print_line_impl es; return ()}"

definition parse_convert_run_check where
  "parse_convert_run_check mode num_split dc s \<equiv>
   case parse json s \<bind> convert of
     Error es \<Rightarrow> print_errors es
   | Result (ids_to_names, _, broadcast, automata, bounds, formula, L\<^sub>0, s\<^sub>0) \<Rightarrow> do {
      let r = rename_state_space dc ids_to_names (broadcast, automata, bounds) L\<^sub>0 s\<^sub>0 formula;
      case r of
        Error es \<Rightarrow> print_errors es
      | Result (r, show_clk, show_st, renamings, k) \<Rightarrow>
        case r of None \<Rightarrow> return () | Some r \<Rightarrow> do {
        let t = now ();
        r \<leftarrow> r;
        let t = now () - t;
        print_line_impl
          (STR ''Time for model checking + certificate extraction: '' + time_to_string t);
        let (m,num_states,num_actions,renum_acts,renum_vars,renum_clocks,renum_states,
          inv_renum_states, inv_renum_vars, inv_renum_clocks
        ) = renamings;
        let _ = start_timer ();
        state_space \<leftarrow> Heap_Monad.fold_map (\<lambda>(s, xs).
          do {
            let xs = map snd xs;
            xs \<leftarrow> Heap_Monad.fold_map (dbm_to_list_impl m) xs;
            return (s, xs)
          }
        ) r;
        let _ = save_time STR ''Time for converting DBMs in certificate'';
        print_line_impl
          (STR ''Number of discrete states of state space: '' + show_lit (length state_space));
        let _ = STR ''Size of passed list: ''  + show_str (sum_list (map (length o snd) r))
          |> println;
        STR ''DBM list length distribution: '' + show_str (distr (map (length o snd) state_space))
          |> print_line_impl;
        let split =
          (if mode = Impl3 then split_k'' num_split state_space else split_k num_split state_space);
        let split_distr = map (sum_list o map (length o snd)) split;
        STR ''Size of passed list distribution after split: '' + show_str split_distr
          |> print_line_impl;
        let t = now ();
        check \<leftarrow> case mode of
          Impl1 \<Rightarrow> rename_check num_split dc broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
            m num_states num_actions renum_acts renum_vars renum_clocks renum_states
            state_space
        | Impl2 \<Rightarrow> rename_check2 num_split dc broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
            m num_states num_actions renum_acts renum_vars renum_clocks renum_states
            state_space |> return
        | Impl3 \<Rightarrow> rename_check3 num_split dc broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
            m num_states num_actions renum_acts renum_vars renum_clocks renum_states
            state_space |> return;
        let t = now () - t;
        print_line_impl (STR ''Time for certificate checking: '' + time_to_string t);
        case check of
          Renaming_Failed \<Rightarrow> print_line_impl (STR ''Renaming failed'')
        | Preconds_Unsat \<Rightarrow> print_line_impl (STR ''Preconditions were not met'')
        | Sat \<Rightarrow> print_line_impl (STR ''Certificate was accepted'')
        | Unsat \<Rightarrow> print_line_impl (STR ''Certificate was rejected'')
        }
    }"

ML \<open>
  fun do_test dc file =
  let
    val s = file_to_string file;
  in
    @{code parse_convert_run_print} dc s end
\<close>

ML_val \<open>
  do_test true "/Users/wimmers/Formalizations/Timed_Automata/benchmarks/HDDI_02.muntax" ()
\<close>

ML_val \<open>
  do_test true "/Users/wimmers/Formalizations/Timed_Automata/benchmarks/HDDI_02_test.muntax" ()
\<close>

ML_val \<open>
  do_test true "/Users/wimmers/Formalizations/Timed_Automata/benchmarks/simple.muntax" ()
\<close>

ML_val \<open>
  do_test true "/Users/wimmers/Formalizations/Timed_Automata/benchmarks/light_switch.muntax" ()
\<close>

ML_val \<open>
  do_test true "/Users/wimmers/Formalizations/Timed_Automata/benchmarks/PM_test.muntax" ()
\<close>

ML_val \<open>
  do_test true "/Users/wimmers/Formalizations/Timed_Automata/benchmarks/bridge.muntax" ()
\<close>

ML_val \<open>
  do_test true "/Users/wimmers/Formalizations/Timed_Automata/benchmarks/PM_mod1.muntax" ()
\<close>

code_printing
  constant "parallel_fold_map" \<rightharpoonup>
      (SML)   "(fn f => fn xs => fn () => Par'_List.map (fn x => f x ()) xs) _ _"

definition
  "num_split \<equiv> 4 :: nat"

ML \<open>
  fun do_check dc file =
  let
    val s = file_to_string file;
  in
    @{code parse_convert_run_check} @{code Impl3} @{code num_split} dc s end
\<close>

(*
ML_val \<open>
  do_check false "/Users/wimmers/Formalizations/Timed_Automata/benchmarks/HDDI_02.muntax" ()
\<close>

ML_val \<open>
  do_check true "/Users/wimmers/Formalizations/Timed_Automata/benchmarks/HDDI_02.muntax" ()
\<close>

ML_val \<open>
  do_check true "/Users/wimmers/Formalizations/Timed_Automata/benchmarks/simple.muntax" ()
\<close>

ML_val \<open>
  do_check true "/Users/wimmers/Formalizations/Timed_Automata/benchmarks/light_switch.muntax" ()
\<close>

ML_val \<open>
  do_check false "/Users/wimmers/Formalizations/Timed_Automata/benchmarks/PM_test.muntax" ()
\<close>

ML_val \<open>
  do_check true "/Users/wimmers/Formalizations/Timed_Automata/benchmarks/PM_test.muntax" ()
\<close>

ML_val \<open>
  do_check true "/Users/wimmers/Formalizations/Timed_Automata/benchmarks/bridge.muntax" ()
\<close>
*)

ML_val \<open>
  do_check false "/Users/wimmers/Formalizations/Timed_Automata/benchmarks/PM_all_3.muntax" ()
\<close>

(*
ML_val \<open>
  do_check true "/Users/wimmers/Formalizations/Timed_Automata/benchmarks/PM_all_3.muntax" ()
\<close>
*)

text \<open>Executing \<open>Heap_Monad.fold_map\<close> in parallel in Isabelle/ML\<close>

definition
  \<open>Test \<equiv> Heap_Monad.fold_map (\<lambda>x. do {let _ = println STR ''x''; return x}) ([1,2,3] :: nat list)\<close>

ML_val \<open>@{code Test} ()\<close>


paragraph \<open>Checking external certificates\<close>

definition
  "list_of_json_object obj \<equiv>
  case obj of
    Object m \<Rightarrow> Result m
  | _ \<Rightarrow> Error [STR ''Not an object'']
"

definition
  "map_of_debug prefix m \<equiv>
    let m = map_of m in
    (\<lambda>x.
      case m x of
        None \<Rightarrow> let _ = println (STR ''Key error('' + prefix + STR ''): '' + show_lit x) in None
      | Some v \<Rightarrow> Some v)" for prefix

definition
  "renaming_of_json' opt prefix json \<equiv> do {
    vars \<leftarrow> list_of_json_object json;
    vars \<leftarrow> combine_map (\<lambda> (a, b). do {b \<leftarrow> of_nat b; Result (String.implode a, b)}) vars;
    let vars = vars @ (case opt of Some x \<Rightarrow> [(x, fold max (map snd vars) 0 + 1)] | _ \<Rightarrow> []);
    Result (the o map_of_debug prefix vars, the o map_of_debug prefix (map prod.swap vars))
  }
  " for json prefix

definition "renaming_of_json \<equiv> renaming_of_json' None"

definition
  "nat_renaming_of_json prefix max_id json \<equiv> do {
    vars \<leftarrow> list_of_json_object json;
    vars \<leftarrow> combine_map (\<lambda>(a, b). do {
      a \<leftarrow> parse lx_nat (String.implode a);
      b \<leftarrow> of_nat b;
      Result (a, b)
    }) vars;
    let ids = fst ` set vars;
    let missing = filter (\<lambda>i. i \<notin> ids) [0..<max_id];
    let m = the o map_of_debug prefix vars;
    let m = extend_domain m missing (length vars);
    Result (m, the o map_of_debug prefix (map prod.swap vars))
  }
  " for json prefix

definition convert_renaming ::
  "(nat \<Rightarrow> nat \<Rightarrow> String.literal) \<Rightarrow> (String.literal \<Rightarrow> nat) \<Rightarrow> JSON \<Rightarrow> _" where
  "convert_renaming ids_to_names process_names_to_index json \<equiv> do {
    json \<leftarrow> of_object json;
    vars \<leftarrow> get json ''vars'';
    (var_renaming, var_inv) \<leftarrow> renaming_of_json STR ''var renaming'' vars;
    clocks \<leftarrow> get json ''clocks'';
    (clock_renaming, clock_inv)
      \<leftarrow> renaming_of_json' (Some STR ''_urge'') STR ''clock renaming'' clocks;
    processes \<leftarrow> get json ''processes'';
    (process_renaming, process_inv) \<leftarrow> renaming_of_json STR ''process renaming'' processes;
    locations \<leftarrow> get json ''locations'';
    locations \<leftarrow> list_of_json_object locations; \<comment>\<open>process name \<rightarrow> json\<close>
    locations \<leftarrow> combine_map (\<lambda>(name, renaming). do {
        let p_num = process_names_to_index (String.implode name);
        assert
          (process_renaming (String.implode name) = p_num)
          (STR ''Process renamings do not agree on '' + String.implode name);
        let max_id = 1000;
        renaming \<leftarrow> nat_renaming_of_json (STR ''process'' + show_str p_num) max_id renaming;
          \<comment>\<open>location id \<rightarrow> nat\<close>
        Result (p_num, renaming)
      }
      ) locations;
    \<comment>\<open>process id \<rightarrow> location id \<rightarrow> nat\<close>
    let location_renaming = the o map_of_debug STR ''location'' (map (\<lambda>(i, f, _). (i, f)) locations);
    let location_inv = the o map_of_debug STR ''location inv''  (map (\<lambda>(i, _, f). (i, f)) locations);
    Result (var_renaming, clock_renaming, location_renaming, var_inv, clock_inv, location_inv)
  }
  "
  for json

definition
  "load_renaming dc model renaming \<equiv>
  case
  do {
    model \<leftarrow> parse json model;
    renaming \<leftarrow> parse json renaming;
    (ids_to_names, process_names_to_index, broadcast, automata, bounds, formula, L\<^sub>0, s\<^sub>0)
      \<leftarrow> convert model;
    convert_renaming ids_to_names process_names_to_index renaming
  }
  of
    Error e \<Rightarrow> return (Error e)
  | Result r \<Rightarrow> do {
    let (var_renaming, clock_renaming, location_renaming, _, _, _) = r;
    let _ = map (\<lambda>p. map (\<lambda>n. location_renaming p n |> show_lit |> println) [0..<8]) [0..<6];
    return (Result ())
  }
"

ML \<open>
  fun do_check dc model_file renaming_file =
  let
    val model = file_to_string model_file;
    val renaming = file_to_string renaming_file;
  in
    @{code load_renaming} dc model renaming end
\<close>

ML_val \<open>
  do_check
    true
    "/Users/wimmers/Code/mlunta/benchmarks/resources/csma_R_6.muntax"
    "/Users/wimmers/Scratch/certificates/csma.renaming"
    ()
\<close>

definition parse_convert_check1 where
  "parse_convert_check1 model renaming \<equiv>
   do {
    model \<leftarrow> parse json model;
    (ids_to_names, process_names_to_index, broadcast, automata, bounds, formula, L\<^sub>0, s\<^sub>0)
      \<leftarrow> convert model;
    renaming \<leftarrow> parse json renaming;
    (var_renaming, clock_renaming, location_renaming,
     inv_renum_vars, inv_renum_clocks, inv_renum_states)
      \<leftarrow> convert_renaming ids_to_names process_names_to_index renaming;
    (m, num_states, num_actions, renum_acts, renum_vars, renum_clocks, renum_states, _, _, _)
      \<leftarrow> make_renaming broadcast automata bounds;
    assert (renum_clocks STR ''_urge'' = m) STR ''Computed renaming: _urge is not last clock!'';
    let renum_vars = var_renaming;
    let renum_clocks = clock_renaming;
    let renum_states = location_renaming;
    assert (renum_clocks STR ''_urge'' = m) STR ''Given renaming: _urge is not last clock!'';
    let _ = println (STR ''Renaming'');
    let (broadcast', automata', bounds') = rename_network
      broadcast bounds automata renum_acts renum_vars renum_clocks renum_states;
    let _ = println (STR ''Calculating ceiling'');
    let k = Simple_Network_Impl_nat_defs.local_ceiling broadcast' bounds' automata' m num_states;
    Result (broadcast, bounds, automata, k, L\<^sub>0, s\<^sub>0, formula,
          m, num_states, num_actions, renum_acts, renum_vars, renum_clocks, renum_states,
          inv_renum_states, inv_renum_vars, inv_renum_clocks)
   }" for num_split

datatype 'l state_space =
    Reachable_Set (reach_of: "(('l list \<times> int list) \<times> int DBMEntry list list) list")
  | Buechi_Set    (buechi_of: "(('l list \<times> int list) \<times> (int DBMEntry list \<times> nat) list) list")

definition normalize_dbm :: "nat \<Rightarrow> int DBMEntry list \<Rightarrow> int DBMEntry list" where
  "normalize_dbm m xs = do {
    dbm \<leftarrow> Array.of_list xs;
    dbm \<leftarrow> fw_impl_int m dbm;
    Array.freeze dbm
  } |> run_heap
  "

definition insert_every_nth :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insert_every_nth n a xs \<equiv>
    fold (\<lambda>x (i, xs). if i = n then (1, a # x # xs) else (i + 1, x # xs)) xs (1, []) |> snd |> rev"

definition convert_dbm where
  "convert_dbm urge m dbm =
    take m dbm @ Le 0 #
    insert_every_nth m DBMEntry.INF (drop m dbm)
    @ (if urge then Le 0 else DBMEntry.INF) # replicate (m - 1) DBMEntry.INF @ [Le 0]
  |> normalize_dbm m"

fun convert_state_space :: "_ \<Rightarrow> _ \<Rightarrow> int state_space \<Rightarrow> nat state_space" where
  "convert_state_space m is_urgent (Reachable_Set xs) = Reachable_Set (
    map (\<lambda>((locs, vars), dbms).
      ((map nat locs, vars), map (convert_dbm (is_urgent (locs, vars)) m) dbms))
    xs)"
| "convert_state_space m is_urgent (Buechi_Set xs) = Buechi_Set (
    map (\<lambda>((locs, vars), dbms).
      ((map nat locs, vars), map (\<lambda>(dbm, i). (convert_dbm (is_urgent (locs, vars)) m dbm, i)) dbms))
    xs)"

fun len_of_state_space where
  "len_of_state_space (Reachable_Set xs) = length xs"
| "len_of_state_space (Buechi_Set xs) = length xs"

context
  fixes num_clocks :: nat
  fixes inv_renum_states :: "nat \<Rightarrow> nat \<Rightarrow> nat"
    and inv_renum_vars   :: "nat \<Rightarrow> String.literal"
    and inv_renum_clocks :: "nat \<Rightarrow> String.literal"
begin

private definition show_st where
  "show_st = show_state inv_renum_states inv_renum_vars"

private definition show_dbm :: "int DBMEntry list \<Rightarrow> char list" where
  "show_dbm = dbm_list_to_string num_clocks (show_clock inv_renum_clocks) show"

fun show_state_space where
  "show_state_space (Reachable_Set xs) =
    map (\<lambda>(l, xs).
      map (\<lambda>x. ''('' @ show_st l @ '', <'' @ show_dbm x @ ''>)'' |> String.implode |> println) xs)
    xs"
| "show_state_space (Buechi_Set xs) =
    map (\<lambda>(l, xs).
      map (\<lambda>(x, i). show i @ '': ('' @ show_st l @ '', <'' @ show_dbm x @ ''>)''
            |> String.implode |> println)
      xs)
    xs"

end

definition
  "print_sep \<equiv> \<lambda>(). println (String.implode (replicate 100 CHR ''-''))"

definition parse_convert_check where
  "parse_convert_check mode num_split dc model renaming state_space show_cert \<equiv>
   let
     r = parse_convert_check1 model renaming
   in case r of Error es \<Rightarrow> do {let _ = map println es; return ()}
   | Result r \<Rightarrow> do {
      let (broadcast, bounds, automata, k, L\<^sub>0, s\<^sub>0, formula,
        m, num_states, num_actions, renum_acts, renum_vars, renum_clocks, renum_states,
        inv_renum_states, inv_renum_vars, inv_renum_clocks) = r;
      let inv_renum_clocks = (\<lambda>i. if i = m then STR ''_urge'' else inv_renum_clocks i);
      let t = now ();
      let state_space = convert_state_space m (\<lambda>_. False) state_space;
      let t = now () - t;
      let _ = println (STR ''Time for converting state space: '' + time_to_string t);
      let _ = start_timer ();
      \<comment> \<open>XXX: What is going on here?\<close>
      let _ = save_time STR ''Time for converting DBMs in certificate'';
      let _ =
        println (STR ''Number of discrete states: ''+ show_lit (len_of_state_space state_space));
      let _ = do {
        if show_cert then do {
          let _ = print_sep ();
          let _ = println (STR ''Certificate'');
          let _ = print_sep ();
          let _ = show_state_space m inv_renum_states inv_renum_vars inv_renum_clocks state_space;
          let _ = print_sep ();
          return ()}
        else return ()
      };
      let t = now ();
      check \<leftarrow> case mode of
        Impl1 \<Rightarrow> rename_check num_split dc broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
          m num_states num_actions renum_acts renum_vars renum_clocks renum_states
          (reach_of state_space)
      | Impl2 \<Rightarrow> rename_check2 num_split dc broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
          m num_states num_actions renum_acts renum_vars renum_clocks renum_states
          (reach_of state_space) |> return
      | Impl3 \<Rightarrow> rename_check3 num_split dc broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
          m num_states num_actions renum_acts renum_vars renum_clocks renum_states
          (reach_of state_space) |> return
      | Buechi \<Rightarrow> rename_check_buechi num_split broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
          m num_states num_actions renum_acts renum_vars renum_clocks renum_states
          (buechi_of state_space) |> return;
      let t = now () - t;
      let _ = println (STR ''Time for certificate checking: '' + time_to_string t);
      case check of
        Renaming_Failed \<Rightarrow> do {let _ = println STR ''Renaming failed''; return ()}
      | Preconds_Unsat \<Rightarrow> do {let _ = println STR ''Preconditions were not met''; return ()}
      | Sat \<Rightarrow> do {let _ = println STR ''Certificate was accepted''; return ()}
      | Unsat \<Rightarrow> do {let _ = println STR ''Certificate was rejected''; return ()}
    }
" for num_split and state_space :: "int state_space"

(* XXX This is a bug fix. Fix in Isabelle distribution *)
code_printing
  constant IArray.length' \<rightharpoonup> (SML) "(IntInf.fromInt o Vector.length)"

code_printing
  constant Parallel.map \<rightharpoonup> (SML) "Par'_List.map"

lemma [code]: "run_map_heap f xs = Parallel.map (run_heap o f) xs"
  unfolding run_map_heap_def Parallel.map_def ..

code_printing code_module "Timing" \<rightharpoonup> (SML)
\<open>
structure Timing : sig
  val start_timer: unit -> unit
  val save_time: string -> unit
  val get_timings: unit -> (string * Time.time) list
  val set_cpu: bool -> unit
end = struct

  open Timer;

  val is_cpu = Unsynchronized.ref false;
  fun set_cpu b = is_cpu := b;

  val cpu_timer: cpu_timer option Unsynchronized.ref = Unsynchronized.ref NONE;
  val real_timer: real_timer option Unsynchronized.ref = Unsynchronized.ref NONE;

  val timings = Unsynchronized.ref [];
  fun start_timer () = (
    if !is_cpu then
      cpu_timer := SOME (startCPUTimer ())
    else
      real_timer := SOME (startRealTimer ()));
  fun get_elapsed () = (
    if !is_cpu then
      #usr (!cpu_timer |> the |> checkCPUTimer)
    else
      (!real_timer |> the |> checkRealTimer));
  fun save_time s = (timings := ((s, get_elapsed ()) :: !timings));
  fun get_timings () = !timings;
end
\<close>

paragraph \<open>Optimized code printings\<close>

definition
  "array_freeze' = array_freeze"

lemma [code]: "array_freeze a = array_freeze' a"
  unfolding array_freeze'_def ..

definition
  "array_unfreeze' = array_unfreeze"

lemma [code]: "array_unfreeze a = array_unfreeze' a"
  unfolding array_unfreeze'_def ..

definition
  "array_copy' = array_copy"

lemma [code]: "array_copy a = array_copy' a"
  unfolding array_copy'_def ..

code_printing constant array_freeze' \<rightharpoonup> (SML) "(fn () => Array.vector _)"

code_printing constant array_unfreeze' \<rightharpoonup> (SML)
  "(fn a => fn () => Array.tabulate (Vector.length a, fn i => Vector.sub (a, i))) _"

code_printing constant array_copy' \<rightharpoonup> (SML)
  "(fn a => fn () => Array.tabulate (Array.length a, fn i => Array.sub (a, i))) _"

text \<open>According to microbenchmarks, these versions are nearly two times faster.\<close>

code_printing constant array_unfreeze' \<rightharpoonup> (SML)
"(fn a => fn () =>
  if Vector.length a = 0
  then Array.fromList []
  else
    let
      val x = Vector.sub(a, 0)
      val n = Array.array (Vector.length a, x)
      val '_ = Array.copyVec {src=a,dst=n,di=0}
    in n end
) _"

code_printing constant array_copy' \<rightharpoonup> (SML)
"(fn a => fn () =>
  if Array.length a = 0
  then Array.fromList []
  else
    let
      val x = Array.sub(a, 0)
      val n = Array.array (Array.length a, x)
      val '_ = Array.copy {src=a,dst=n,di=0}
    in n end
) _"


partial_function (heap) imp_for_int_inner ::
  "integer \<Rightarrow> integer \<Rightarrow> ('a \<Rightarrow> bool Heap) \<Rightarrow> (integer \<Rightarrow> 'a \<Rightarrow> 'a Heap) \<Rightarrow> 'a \<Rightarrow> 'a Heap" where
  "imp_for_int_inner i u c f s = (if i \<ge> u then return s else
    do {ctn <- c s; if ctn then f i s \<bind> imp_for_int_inner (i + 1) u c f else return s})"

lemma integer_of_nat_le_simp:
  "integer_of_nat i \<le> integer_of_nat u \<longleftrightarrow> i \<le> u"
  unfolding integer_of_nat_eq_of_nat by simp

lemma imp_for_imp_for_int_inner[code_unfold]:
  "imp_for i u c f s
  = imp_for_int_inner (integer_of_nat i) (integer_of_nat u) c (f o nat_of_integer) s"
  apply (induction "u - i" arbitrary: i u s)
   apply (simp add: integer_of_nat_le_simp imp_for_int_inner.simps; fail)
  apply (subst imp_for_int_inner.simps, simp add: integer_of_nat_le_simp)
  apply auto
  apply (fo_rule arg_cong, rule ext)
  apply clarsimp
  apply (fo_rule arg_cong)
  apply (auto simp: algebra_simps integer_of_nat_eq_of_nat)
  done

definition
  "imp_for_int i u c f s \<equiv>
  imp_for_int_inner (integer_of_nat i) (integer_of_nat u) c (f o nat_of_integer) s"

lemma imp_for_imp_for_int[code_unfold]:
  "imp_for = imp_for_int"
  by (intro ext, unfold imp_for_int_def imp_for_imp_for_int_inner, rule HOL.refl)

partial_function (heap) imp_for'_int_inner ::
  "integer \<Rightarrow> integer \<Rightarrow> (integer \<Rightarrow> 'a \<Rightarrow> 'a Heap) \<Rightarrow> 'a \<Rightarrow> 'a Heap" where
  "imp_for'_int_inner i u f s =
    (if i \<ge> u then return s else f i s \<bind> imp_for'_int_inner (i + 1) u f)"

lemma imp_for'_imp_for_int_inner:
  "imp_for' i u f s \<equiv>
  imp_for'_int_inner (integer_of_nat i) (integer_of_nat u) (f o nat_of_integer) s"
  apply (induction "u - i" arbitrary: i u s)
   apply (simp add: integer_of_nat_le_simp imp_for'_int_inner.simps; fail)
  apply (subst imp_for'_int_inner.simps, simp add: integer_of_nat_le_simp)
  apply auto
  apply (fo_rule arg_cong, rule ext)
  apply (auto simp: algebra_simps integer_of_nat_eq_of_nat)
  done

lemma imp_for'_int_cong:
  "imp_for' l u f a = imp_for' l u g a"
  if "\<And> i x. l \<le> i \<Longrightarrow> i < u \<Longrightarrow> f i x = g i x"
  using that
  apply (induction "u - l" arbitrary: l u a)
   apply (simp add: imp_for'.simps; fail)
  apply (subst imp_for'.simps, simp add: integer_of_nat_le_simp)
  apply safe
  apply clarsimp
  apply (fo_rule arg_cong)
  apply auto
  done


definition
  "imp_for'_int i u f s \<equiv>
  imp_for'_int_inner (integer_of_nat i) (integer_of_nat u) (f o nat_of_integer) s"

lemma imp_for'_imp_for_int[code_unfold, int_folds]:
  "imp_for' = imp_for'_int"
  by (intro ext, unfold imp_for'_int_def imp_for'_imp_for_int_inner, rule HOL.refl)

code_printing code_module "Iterators" \<rightharpoonup> (SML)
\<open>
fun imp_for_inner i u c f s =
  let
    fun imp_for1 i u f s =
      if IntInf.<= (u, i) then (fn () => s)
      else if c s () then imp_for1 (i + 1) u f (f i s ())
      else (fn () => s)
  in imp_for1 i u f s end;

fun imp_fora_inner i u f s =
  let
    fun imp_for1 i u f s =
      if IntInf.<= (u, i) then (fn () => s)
      else imp_for1 (i + 1) u f (f i s ())
  in imp_for1 i u f s end;
\<close>

code_reserved SML imp_for_inner imp_fora_inner
(* XXX How much do we gain from this? *)
(*
code_printing
  constant imp_for_int_inner \<rightharpoonup> (SML) "imp'_for'_inner"
| constant imp_for'_int_inner \<rightharpoonup> (SML) "imp'_fora'_inner"
*)


definition
  "nth_integer a n = Array.nth a (nat_of_integer n)"

definition
  "upd_integer n x a = Array.upd (nat_of_integer n) x a"

code_printing
  constant upd_integer \<rightharpoonup> (SML) "(fn a => fn () => (Array.update (a, IntInf.toInt _, _); a)) _"
| constant nth_integer \<rightharpoonup> (SML) "(fn () => Array.sub (_, IntInf.toInt _))"

definition
  "fw_upd_impl_integer n a k i j = do {
  let n = n + 1;
  let i' = i * n + j;
  y \<leftarrow> nth_integer a (i * n + k);
  z \<leftarrow> nth_integer a (k * n + j);
  x \<leftarrow> nth_integer a i';
  let m = dbm_add_int y z;
  if dbm_lt_int m x then upd_integer i' m a else return a
}
"

lemma nat_of_integer_add:
  "nat_of_integer i + nat_of_integer j = nat_of_integer (i + j)" if "i \<ge> 0" "j \<ge> 0"
proof -
  have *: "nat a + nat b = nat (a + b)" if "a \<ge> 0" "b \<ge> 0" for a b
    using that by simp
  show ?thesis
    unfolding nat_of_integer.rep_eq
    apply (simp add: *)
    apply (subst *)
    subgoal
      using zero_integer.rep_eq less_eq_integer.rep_eq that by metis
    subgoal
      using zero_integer.rep_eq less_eq_integer.rep_eq that by metis
    ..
qed

lemma nat_of_integer_mult:
  "nat_of_integer i * nat_of_integer j = nat_of_integer (i * j)" if "i \<ge> 0" "j \<ge> 0"
  using that
proof -
  have *: "nat a * nat b = nat (a * b)" if "a \<ge> 0" "b \<ge> 0" for a b
    using that by (simp add: nat_mult_distrib)
  show ?thesis
    unfolding nat_of_integer.rep_eq
    apply simp
    apply (subst *)
    subgoal
      using zero_integer.rep_eq less_eq_integer.rep_eq that by metis
    subgoal
      using zero_integer.rep_eq less_eq_integer.rep_eq that by metis
    ..
qed

lemma fw_upd_impl_int_fw_upd_impl_integer:
  "fw_upd_impl_int (nat_of_integer n) a (nat_of_integer k) (nat_of_integer i) (nat_of_integer j)
= fw_upd_impl_integer n a k i j"
  if "i \<ge> 0" "j \<ge> 0" "k \<ge> 0" "n \<ge> 0"
  unfolding
    fw_upd_impl_integer_def fw_upd_impl_int_def[symmetric] fw_upd_impl_def mtx_get_def mtx_set_def
  unfolding int_folds less
  unfolding nth_integer_def upd_integer_def fst_conv snd_conv
  using that
  apply (simp add: nat_of_integer_add nat_of_integer_mult algebra_simps)
  apply (fo_rule arg_cong | rule ext)+
  apply (simp add: nat_of_integer_add nat_of_integer_mult algebra_simps)
  done

lemma integer_of_nat_nat_of_integer:
  "integer_of_nat (nat_of_integer n) = n" if "n \<ge> 0"
  using that by (simp add: integer_of_nat_eq_of_nat max_def)

lemma integer_of_nat_aux:
  "integer_of_nat (nat_of_integer n + 1) = n + 1" if "n \<ge> 0"
proof -
  have "nat_of_integer n + 1 = nat_of_integer n + nat_of_integer 1"
    by simp
  also have "\<dots> = nat_of_integer (n + 1)"
    using that by (subst nat_of_integer_add; simp)
  finally show ?thesis
    using that by (simp add: integer_of_nat_nat_of_integer)
qed

definition
  "fwi_impl_integer n a k = fwi_impl_int (nat_of_integer n) a (nat_of_integer k)"

lemma fwi_impl_int_eq1:
  "fwi_impl_int n a k \<equiv> fwi_impl_integer (integer_of_nat n) a (integer_of_nat k)"
  unfolding fwi_impl_integer_def fwi_impl_int_def by simp

partial_function (heap) imp_for'_int_int ::
  "int \<Rightarrow> int \<Rightarrow> (int \<Rightarrow> 'a \<Rightarrow> 'a Heap) \<Rightarrow> 'a \<Rightarrow> 'a Heap" where
  "imp_for'_int_int i u f s =
    (if i \<ge> u then return s else f i s \<bind> imp_for'_int_int (i + 1) u f)"

lemma int_bounds_up_induct:
  assumes "\<And>l. u \<le> (l :: int) \<Longrightarrow> P l u"
      and "\<And>l. P (l + 1) u \<Longrightarrow> l < u \<Longrightarrow> P l u"
  shows "P l u"
  by (induction "nat (u - l)" arbitrary: l) (auto intro: assms)

lemma imp_for'_int_int_cong:
  "imp_for'_int_int l u f a = imp_for'_int_int l u g a"
  if "\<And> i x. l \<le> i \<Longrightarrow> i < u \<Longrightarrow> f i x = g i x"
  using that
  apply (induction arbitrary: a rule: int_bounds_up_induct)
   apply (simp add: imp_for'_int_int.simps; fail)
  apply (subst (2) imp_for'_int_int.simps)
  apply (subst imp_for'_int_int.simps)
  apply simp
  apply (fo_rule arg_cong, rule ext)
  .

lemma plus_int_int_of_integer_aux:
  "(plus_int (int_of_integer l) 1) = int_of_integer (l + 1)"
  by simp

lemma imp_for'_int_inner_imp_for'_int_int:
  "imp_for'_int_inner l u f a
= imp_for'_int_int (int_of_integer l) (int_of_integer u) (f o integer_of_int) a"
  apply (induction "int_of_integer l" "int_of_integer u" arbitrary: a l u rule: int_bounds_up_induct)
   apply (simp add: imp_for'_int_int.simps imp_for'_int_inner.simps less_eq_integer.rep_eq; fail)
  apply (subst imp_for'_int_int.simps)
  apply (subst imp_for'_int_inner.simps)
  apply (simp add: less_eq_integer.rep_eq)
  apply (fo_rule arg_cong, rule ext)
  apply (subst plus_int_int_of_integer_aux)
  apply rprems
  using plus_int_int_of_integer_aux by metis+

lemma imp_for'_int_inner_cong:
  "imp_for'_int_inner l u f a = imp_for'_int_inner l u g a"
  if "\<And> i x. l \<le> i \<Longrightarrow> i < u \<Longrightarrow> f i x = g i x"
  unfolding imp_for'_int_inner_imp_for'_int_int
  by (rule imp_for'_int_int_cong)(auto simp: less_eq_integer.rep_eq less_integer.rep_eq intro: that)

schematic_goal fwi_impl_int_unfold1:
  "fwi_impl_int (nat_of_integer n) a (nat_of_integer k) = ?i" if "0 \<le> k" "0 \<le> n"
  unfolding fwi_impl_int_def[symmetric] fwi_impl_def
  unfolding int_folds
  unfolding imp_for'_int_def
  unfolding comp_def integer_of_nat_0
  apply (rule imp_for'_int_inner_cong)
  apply (rule imp_for'_int_inner_cong)
  apply (rule fw_upd_impl_int_fw_upd_impl_integer)
  by (assumption | rule that)+

lemma integer_of_nat_add:
  "integer_of_nat (x + y) = integer_of_nat x + integer_of_nat y"
  by (simp add: integer_of_nat_eq_of_nat)

schematic_goal fwi_impl_int_code [code]:
  "fwi_impl_int n a k \<equiv> ?x"
  unfolding fwi_impl_int_eq1
  unfolding fwi_impl_integer_def
  apply (subst fwi_impl_int_unfold1)
    apply (simp add: integer_of_nat_eq_of_nat; fail)
   apply (simp add: integer_of_nat_eq_of_nat; fail)
  unfolding nat_of_integer_integer_of_nat
  unfolding integer_of_nat_add integer_of_nat_1
  apply (abstract_let "integer_of_nat n + 1" n_plus_1)
  apply (abstract_let "integer_of_nat n" n)
  .


code_printing code_module "Integer" \<rightharpoonup> (Eval)
\<open>
structure Integer: sig
  val div_mod: int -> int -> int * int
end = struct
  fun div_mod i j = (i div j, i mod j)
end
\<close>

text \<open>Delete ``junk''\<close>
code_printing code_module Bits_Integer \<rightharpoonup> (SML) \<open>\<close>

text \<open>For agreement with SML\<close>
code_printing
  type_constructor Typerep.typerep \<rightharpoonup> (Eval)
| constant Typerep.Typerep \<rightharpoonup> (Eval)
(*
code_printing
  type_constructor Typerep.typerep \<rightharpoonup> (Eval) "typerepa"
| constant Typerep.Typerep \<rightharpoonup> (Eval) "Typerep/ (_, _)"
*)

(* datatype typerepa = Typerep of string * typerepa list; *)

(* Speedup for Poly *)
(*
definition
  "fw_upd_impl_integer' = fw_upd_impl_integer"

lemma [code]:
  "fw_upd_impl_integer = fw_upd_impl_integer'"
  unfolding fw_upd_impl_integer'_def ..

code_printing
  constant fw_upd_impl_integer' \<rightharpoonup> (SML) "(fn n => fn a => fn k => fn i => fn j =>
  let
    val na = IntInf.+ (n, (1 : IntInf.int));
    val ia = IntInf.+ (IntInf.* (i, na), j);
    val x = Array.sub (a, IntInf.toInt ia);
    val y = Array.sub (a, IntInf.toInt (IntInf.+ (IntInf.* (i, na), k)));
    val z = Array.sub (a, IntInf.toInt (IntInf.+ (IntInf.* (k, na), j)));
    val m = dbm'_add'_int y z;
  in
    if dbm'_lt'_int m x
    then (fn () => (Array.update (a, IntInf.toInt ia, m); a))
    else (fn () => a)
  end) _ _ _ _ _"
*)

lemmas [code] = imp_for'_int_inner.simps imp_for_int_inner.simps

export_code parse_convert_check parse_convert_run_print parse_convert_run_check Result Error
  nat_of_integer int_of_integer DBMEntry.Le DBMEntry.Lt DBMEntry.INF
  Impl1 Impl2 Impl3 Buechi Reachable_Set Buechi_Set
  E_op_impl
  in Eval module_name Model_Checker file "../ML/Certificate.ML"

export_code parse_convert_check parse_convert_run_print parse_convert_run_check Result Error
  nat_of_integer int_of_integer DBMEntry.Le DBMEntry.Lt DBMEntry.INF
  Impl1 Impl2 Impl3 Buechi Reachable_Set Buechi_Set
  E_op_impl
  in SML module_name Model_Checker file "../ML/Certificate.sml"



code_printing code_module "Printing" \<rightharpoonup> (Haskell)
\<open>
import qualified Debug.Trace;

print s = Debug.Trace.trace s ();

printM s = Debug.Trace.traceM s;
\<close>

code_printing
  constant Printing.print \<rightharpoonup> (Haskell) "Printing.print _"
(* 
code_printing code_module "Timing" \<rightharpoonup> (Haskell)
\<open>
import Data.Time.Clock.System;

now = systemToTAITime . Prelude.unsafePerformIO getSystemTime;
\<close>
 *)

code_printing
  constant print_line_impl \<rightharpoonup> (Haskell) "Printing.printM _"

(* code_printing
  constant "now" \<rightharpoonup> (Haskell) "Prelude.const (Time (Int'_of'_integer 0)) _"

code_printing
  constant "time_to_string" \<rightharpoonup> (Haskell) "Prelude.show _"

code_printing
  constant "(-) :: time \<Rightarrow> time \<Rightarrow> time" \<rightharpoonup> (Haskell)
    "(case _ of Time a -> case _ of Time b -> Time (b - a))" *)

code_printing
  type_constructor time \<rightharpoonup> (Haskell) "Integer"
  | constant "now" \<rightharpoonup> (Haskell) "Prelude.const 0"
  | constant "time_to_string" \<rightharpoonup> (Haskell) "Prelude.show _"
  | constant "(-) :: time \<Rightarrow> time \<Rightarrow> time" \<rightharpoonup> (Haskell) "(-)"

code_printing
  constant list_of_set' \<rightharpoonup> (Haskell) "(case _ of Set xs -> xs)"

export_code parse_convert_check parse_convert_run_print parse_convert_run_check Result Error
  nat_of_integer int_of_integer DBMEntry.Le DBMEntry.Lt DBMEntry.INF
  Impl1 Impl2 Impl3 Buechi Reachable_Set Buechi_Set
  in Haskell module_name Model_Checker file "../Haskell/"

end

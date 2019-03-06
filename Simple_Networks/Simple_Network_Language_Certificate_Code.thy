theory Simple_Network_Language_Certificate_Code
  imports
    Simple_Network_Language_Certificate
    Simple_Network_Language_Export_Code
    Simple_Network_Language_Certificate_Checking
begin

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
    let r = do_rename_mc f dc broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
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
          let _ = ''Number of discrete states: '' @ show (length r) |> String.implode |> println;
          let _ = ''Size of passed list: ''
            @ show (sum_list (map (length o snd) r)) |> String.implode |> println;
          let n = Simple_Network_Impl.clk_set' automata |> list_of_set |> length;
          r \<leftarrow> imp_map (\<lambda> (a, b). do {
              b \<leftarrow> imp_map (return o snd) b; b \<leftarrow> filter_dbm_list n b; return (a, b)
            }) r;
          let _ = ''Number of discrete states: '' @ show (length r) |> String.implode |> println;
          let _ = ''Size of passed list after removing subsumed states: ''
            @ show (sum_list (map (length o snd) r)) |> String.implode |> println;
          let show_dbm = (\<lambda>M. do {s \<leftarrow> show_dbm_impl_all n show_clk show M; return (''<'' @ s @ ''>'')});
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

datatype mode = Impl1 | Impl2 | Impl3

definition parse_convert_run_check where
  "parse_convert_run_check mode num_split dc s \<equiv>
   case parse json s \<bind> convert of
     Error es \<Rightarrow> do {let _ = map println es; return ()}
   | Result (ids_to_names, _, broadcast, automata, bounds, formula, L\<^sub>0, s\<^sub>0) \<Rightarrow> do {
      let t = now ();
      let r = rename_state_space dc ids_to_names (broadcast, automata, bounds) L\<^sub>0 s\<^sub>0 formula;
      let t = now () - t;
      let _ = println (STR ''Time for model checking + certificate extraction: '' + time_to_string t);
      case r of
        Error es \<Rightarrow> do {let _ = map println es; return ()}
      | Result (r, show_clk, show_st, renamings, k) \<Rightarrow>
        case r of None \<Rightarrow> return () | Some r \<Rightarrow> do {
        r \<leftarrow> r;
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
        let _ = println (
          STR ''Number of discrete states of state space: '' + show_lit (length state_space));
        let _ = ''Size of passed list: ''
            @ show (sum_list (map (length o snd) r)) |> String.implode |> println;
        let t = now ();
        check \<leftarrow> case mode of
          Impl1 \<Rightarrow> rename_check num_split dc broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
            m num_states num_actions renum_acts renum_vars renum_clocks renum_states
            (* inv_renum_states inv_renum_vars inv_renum_clocks *)
            state_space
        | Impl2 \<Rightarrow> rename_check2 num_split dc broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
            m num_states num_actions renum_acts renum_vars renum_clocks renum_states
            state_space |> return
        | Impl3 \<Rightarrow> rename_check3 num_split dc broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
            m num_states num_actions renum_acts renum_vars renum_clocks renum_states
            state_space |> return;
        let t = now () - t;
        let _ = println (STR ''Time for certificate checking: '' + time_to_string t);
        case check of
          Renaming_Failed \<Rightarrow> do {let _ = println STR ''Renaming failed''; return ()}
        | Preconds_Unsat \<Rightarrow> do {let _ = println STR ''Preconditions were not met''; return ()}
        | Sat \<Rightarrow> do {let _ = println STR ''Certificate was accepted''; return ()}
        | Unsat \<Rightarrow> do {let _ = println STR ''Certificate was rejected''; return ()}
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

(*
code_printing
  constant "parallel_fold_map" \<rightharpoonup>
      (SML)   "(fn f => fn xs => fn () => Par'_List.map (fn x => f x ()) xs) _ _"
*)

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
  "map_of_debug m \<equiv>
    let m = map_of m in
    (\<lambda>x.
      case m x of
        None \<Rightarrow> let _ = println (STR ''Key error: '' + show_lit x) in None
      | Some v \<Rightarrow> Some v)"

definition
  "renaming_of_json json \<equiv> do {
    vars \<leftarrow> list_of_json_object json;
    vars \<leftarrow> combine_map (\<lambda> (a, b). do {b \<leftarrow> of_nat b; Result (String.implode a, b)}) vars;
    Result (the o map_of_debug vars)
  }
  " for json

definition
  "nat_renaming_of_json max_id json \<equiv> do {
    vars \<leftarrow> list_of_json_object json;
    vars \<leftarrow> combine_map (\<lambda> (a, b). do {
      a \<leftarrow> parse lx_nat (String.implode a);
      b \<leftarrow> of_nat b;
      Result (a, b)
    }) vars;
    let ids = fst ` set vars;
    let missing = filter (\<lambda>i. i \<notin> ids) [0..<max_id];
    let m = the o map_of_debug vars;
    let m = extend_domain m missing (length vars);
    Result m
  }
  " for json

definition convert_renaming ::
  "(nat \<Rightarrow> nat \<Rightarrow> String.literal) \<Rightarrow> (String.literal \<Rightarrow> nat) \<Rightarrow> JSON \<Rightarrow> _" where
  "convert_renaming ids_to_names process_names_to_index json \<equiv> do {
    json \<leftarrow> of_object json;
    vars \<leftarrow> get json ''vars'';
    var_renaming \<leftarrow> renaming_of_json vars;
    clocks \<leftarrow> get json ''clocks'';
    clock_renaming \<leftarrow> renaming_of_json clocks;
    processes \<leftarrow> get json ''processes'';
    process_renaming \<leftarrow> renaming_of_json processes;
    locations \<leftarrow> get json ''locations'';
    locations \<leftarrow> list_of_json_object locations; \<comment>\<open>process name \<rightarrow> json\<close>
    locations \<leftarrow> combine_map (\<lambda> (name, renaming). do {
        let p_num = process_names_to_index (String.implode name);
        assert
          (process_renaming (String.implode name) = p_num)
          (STR ''Process renamings do not agree on '' + String.implode name);
        let max_id = 1000;
        renaming \<leftarrow> nat_renaming_of_json max_id renaming; \<comment>\<open>location id \<rightarrow> nat\<close>
        Result (p_num, renaming)
      }
      ) locations;
    let location_renaming = the o map_of locations; \<comment>\<open>process id \<rightarrow> location id \<rightarrow> nat\<close>
    Result (var_renaming, clock_renaming, location_renaming)
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
    let (var_renaming, clock_renaming, location_renaming) = r;
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
    "/Users/wimmers/Scratch/csma.renaming"
    ()
\<close>


definition convert_state_space :: "_ \<Rightarrow> ((nat list \<times> _) \<times> _) list" where
  "convert_state_space state_space \<equiv>
    map (\<lambda>((locs, vars), dbms). ((map nat locs, vars), dbms)) state_space"
  for state_space :: "((int list \<times> int list) \<times> int DBMEntry list list) list"

definition parse_convert_check1 where
  "parse_convert_check1 model renaming state_space \<equiv>
   do {
    model \<leftarrow> parse json model;
    (ids_to_names, process_names_to_index, broadcast, automata, bounds, formula, L\<^sub>0, s\<^sub>0)
      \<leftarrow> convert model;
    renaming \<leftarrow> parse json renaming;
    (var_renaming, clock_renaming, location_renaming) \<leftarrow>
        convert_renaming ids_to_names process_names_to_index renaming;
    let t = now ();
    let state_space = convert_state_space state_space;
    let t = now () - t;
    let _ = println (STR ''Time for converting state space: '' + time_to_string t);
    (m, num_states, num_actions, renum_acts, renum_vars, renum_clocks, renum_states,
      inv_renum_states, inv_renum_vars, inv_renum_clocks) \<leftarrow>
      make_renaming broadcast automata bounds;
    let renum_vars = var_renaming;
    let renum_clocks = clock_renaming;
    let renum_states = location_renaming;
    let _ = println (STR ''Renaming'');
    let (broadcast', automata', bounds') = rename_network
      broadcast bounds automata renum_acts renum_vars renum_clocks renum_states;
    let _ = println (STR ''Calculating ceiling'');
    let k = Simple_Network_Impl_nat_defs.local_ceiling broadcast' bounds' automata' m num_states;
    Result (broadcast, bounds, automata, k, L\<^sub>0, s\<^sub>0, formula,
          m, num_states, num_actions, renum_acts, renum_vars, renum_clocks, renum_states,
          state_space)
   }" for num_split and state_space :: "((int list \<times> int list) \<times> int DBMEntry list list) list"

definition parse_convert_check where
  "parse_convert_check mode num_split dc model renaming state_space \<equiv>
   let
     r = parse_convert_check1 model renaming state_space
   in case r of Error es \<Rightarrow> do {let _ = map println es; return ()}
   | Result r \<Rightarrow> do {
     let (broadcast, bounds, automata, k, L\<^sub>0, s\<^sub>0, formula,
          m, num_states, num_actions, renum_acts, renum_vars, renum_clocks, renum_states,
          state_space) = r;
        let _ = start_timer ();
        let _ = save_time STR ''Time for converting DBMs in certificate'';
        let _ = println (STR ''Number of discrete states: '' + show_lit (length state_space));
        let t = now ();
        check \<leftarrow> case mode of
          Impl1 \<Rightarrow> rename_check num_split dc broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
            m num_states num_actions renum_acts renum_vars renum_clocks renum_states
            (* inv_renum_states inv_renum_vars inv_renum_clocks *)
            state_space
        | Impl2 \<Rightarrow> rename_check2 num_split dc broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
            m num_states num_actions renum_acts renum_vars renum_clocks renum_states
            (* inv_renum_states inv_renum_vars inv_renum_clocks *)
            state_space |> return;
        let t = now () - t;
        let _ = println (STR ''Time for certificate checking: '' + time_to_string t);
        case check of
          Renaming_Failed \<Rightarrow> do {let _ = println STR ''Renaming failed''; return ()}
        | Preconds_Unsat \<Rightarrow> do {let _ = println STR ''Preconditions were not met''; return ()}
        | Sat \<Rightarrow> do {let _ = println STR ''Certificate was accepted''; return ()}
        | Unsat \<Rightarrow> do {let _ = println STR ''Certificate was rejected''; return ()}
    }
" for num_split and state_space :: "((int list \<times> int list) \<times> int DBMEntry list list) list"

export_code parse_convert_check parse_convert_run_print parse_convert_run_check Result Error
  nat_of_integer int_of_integer DBMEntry.Le DBMEntry.Lt DBMEntry.INF
  Impl1 Impl2 Impl3
  in SML module_name Model_Checker file "../ML/Certificate.sml"

end
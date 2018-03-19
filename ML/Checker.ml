open UPPAAL_Model_Checker
open Angstrom

(*** Utilities for parsing
 * Should be removed at some point
***)
type ('a, 'b) instr' = JMPZ' of 'a | ADD' | NOT' | AND' | LT' | LE' | EQ' | PUSH' of 'b | POP' |
    LID' of 'a | STOREI' of 'a * 'b | COPY' | CALL' | RETURN' | HALT' |
    STOREC' of 'a * 'b | SETF' of bool

type ('a, 'b, 'c) instrc' = INSTR' of ('a, 'b) instr' | CEXP' of ('a, 'c) Model_Checker.acconstraint

type ('a, 'b) bexp' =
  Not' of ('a, 'b) bexp' |
  And' of ('a, 'b) bexp' * ('a, 'b) bexp' |
  Or' of ('a, 'b) bexp' * ('a, 'b) bexp' |
  Imply' of ('a, 'b) bexp' * ('a, 'b) bexp' |
  Loc' of 'a * 'a | Eq' of 'a * 'b | Lea' of 'a * 'b |
  Lta' of 'a * 'b | Ge' of 'a * 'b | Gt' of 'a * 'b

type ('a, 'b) formula' =
  EX' of ('a, 'b) bexp' |
  EG' of ('a, 'b) bexp' |
  AX' of ('a, 'b) bexp' |
  AG' of ('a, 'b) bexp' |
  Leadsto' of ('a, 'b) bexp' * ('a, 'b) bexp'

let map_acconstraint f g = function
  Model_Checker.LTa (a, b) -> Model_Checker.LTa (f a, g b) |
  LEa (a, b) -> LEa (f a, g b) |
  EQa (a, b) -> EQa (f a, g b) |
  GE (a, b) -> GE (f a, g b) |
  GT (a, b) -> GT (f a, g b)

let map_act f = function
  Model_Checker.In a -> Model_Checker.In (f a) |
  Out a -> Out (f a) |
  Sil a -> Sil (f a)

let map_instr f_nat f_int = function
  JMPZ' n -> Model_Checker.JMPZ (f_nat n) |
  PUSH' i -> PUSH (f_int i) |
  LID' n -> LID (f_nat n) |
  STOREI' (n, i) -> STOREI (f_nat n, f_int i) |
  STOREC' (n, i) -> STOREC (f_nat n, f_int i) |
  ADD' -> ADD | NOT' -> NOT | AND' -> AND | LT' -> LT | LE' -> LE | EQ' -> EQ |
  POP' -> POP | COPY' -> COPY | CALL' -> CALL | RETURN' -> RETURN | HALT' -> HALT |
  SETF' b -> SETF b

let map_instrc f_nat f_int f_time = function
  INSTR' instr -> Model_Checker.INSTR (map_instr f_nat f_int instr) |
  CEXP' ac -> CEXP (map_acconstraint f_nat f_time ac)

let rec map_bexp f_nat f_int = function
  Not' a -> Model_Checker.Not (map_bexp f_nat f_int a) |
  And' (a, b) -> And (map_bexp f_nat f_int a, map_bexp f_nat f_int b) |
  Or' (a, b) -> Or (map_bexp f_nat f_int a, map_bexp f_nat f_int b) |
  Imply' (a, b) -> Imply (map_bexp f_nat f_int a, map_bexp f_nat f_int b) |
  Loc' (p, l) -> Loc (f_nat p, f_nat l) |
  Lta' (v, x) -> Lta (f_nat v, f_int x) |
  Lea' (v, x) -> Lea (f_nat v, f_int x) |
  Eq' (v, x) -> Eq (f_nat v, f_int x) |
  Ge' (v, x) -> Ge (f_nat v, f_int x) |
  Gt' (v, x) -> Gt (f_nat v, f_int x)

let map_formula f_nat f_int =
  let
    f = map_bexp f_nat f_int
  in
    function
      EX' a -> Model_Checker.EX (f a) |
      EG' a -> EG (f a) |
      AX' a -> AX (f a) |
      AG' a -> AG (f a) |
      Leadsto' (a, b) -> Leadsto (f a, f b)


(*** Conversion helpers ***)

let int_of x = Big_int_Z.big_int_of_int x |> fun x -> Model_Checker.Int_of_integer x
let nat_of x = Big_int_Z.big_int_of_int x |> Model_Checker.nat_of_integer 
let int_to_nat x = Model_Checker.integer_of_int x |> Model_Checker.nat_of_integer
let nat_of_int = int_to_nat

let to_int = int_of
let to_nat = nat_of
let nat_to_int x = Model_Checker.integer_of_nat x |> fun x -> Model_Checker.Int_of_integer x


(*** Parsing ***)

(** Helpers **)

let is_space =
    function | ' ' | '\t' | '\n' -> true | _ -> false

let scan_whitespace = skip_while is_space

let pair_and_skip p1 p2 = lift2 (fun r1 r2 -> (r1, r2)) p1 (scan_whitespace *> p2)

let (---) = pair_and_skip

let is_digit = function '0' .. '9' -> true | _ -> false

let scan_int =
  (option 1 (string "~" >>| fun _ -> -1) >>= fun sign -> take_while1 (function '0' .. '9' -> true | _ -> false) >>| fun x -> int_of_string x * sign) <?> "int"

let scan_nat = take_while1 is_digit >>| int_of_string

let scan_collection lparen rparen sep item_parser =
    string lparen *> sep_by (string sep *> scan_whitespace) item_parser <* string rparen

let scan_list item_parser = scan_collection "[" "]" "," item_parser

let scan_collection' lparen rparen sep item_parsers =
    let rec scan_inner = function
        | [] -> return []
        | [p] -> p >>| (fun x -> [x])
        | (p :: ps) ->
            (p <* string sep <* scan_whitespace) >>= fun x ->
            scan_inner ps >>= fun xs ->
            return (x :: xs)
    in string lparen *> scan_inner item_parsers <* string rparen

let scan_tuple' ps = scan_collection' "(" ")" "," ps
let scan_pair ps = scan_tuple' ps >>| (fun [a;b] -> (a,b))

let scan_pairc ps head constr = string head *> scan_whitespace *> scan_pair ps >>| constr

let scan_singlec p head constr = string head *> scan_whitespace *> p >>| constr

let scan_infix_pair p1 p2 sep =
    lift2 (fun x y -> (x, y)) p1 (scan_whitespace *> string sep *> scan_whitespace *> p2)

let scan_infix_pairc p1 p2 sep constr = scan_infix_pair p1 p2 sep >>| constr


(** Main parser **)

let scan_pairc_int = scan_pairc [scan_int; scan_int]
let scan_acconstraint_lt = scan_pairc_int "LTa" (fun (x, y) -> Model_Checker.LTa (x, y))
let scan_acconstraint_le = scan_pairc_int "LEa" (fun (x, y) -> Model_Checker.LEa (x, y))
let scan_acconstraint_eq = scan_pairc_int "EQa" (fun (x, y) -> Model_Checker.EQa (x, y))
let scan_acconstraint_ge = scan_pairc_int "GE" (fun (x, y) -> Model_Checker.GE (x, y))
let scan_acconstraint_gt = scan_pairc_int "GT" (fun (x, y) -> Model_Checker.GT (x, y))
let scan_acconstraint = choice [
  scan_acconstraint_lt;
  scan_acconstraint_le;
  scan_acconstraint_eq;
  scan_acconstraint_ge;
  scan_acconstraint_gt;
  ];;

let scan_infix_pairc_int s f = scan_infix_pairc scan_int scan_int s f

let scan_parens lparen rparen inner =
  string lparen *> scan_whitespace *> inner <* scan_whitespace <* string rparen

let scan_bexp_elem = choice [
  scan_pairc [scan_int; scan_int] "Loc'"  (fun (x, y) -> Loc' (x, y));
  scan_pairc [scan_int; scan_int] "Lea''" (fun (x, y) -> Lea' (x, y));
  scan_pairc [scan_int; scan_int] "Eq'"   (fun (x, y) -> Eq' (x, y));
  scan_pairc [scan_int; scan_int] "Lta'"  (fun (x, y) -> Lta' (x, y));
  scan_pairc [scan_int; scan_int] "Ge'"   (fun (x, y) -> Ge' (x, y));
  scan_pairc [scan_int; scan_int] "Gt'"   (fun (x, y) -> Gt' (x, y));
]

let scan_bexp =
  let scan_parens = scan_parens "(" ")" in
  fix (fun scan_7 ->
    let
      scan_6 = fix (fun scan_6 ->
        let scan_inner_bexp = scan_parens scan_7
        in let scan_prefix sep constr =
          string sep *> scan_whitespace *> scan_inner_bexp >>| constr
        in let scan_0 =
            scan_prefix "Not'" (fun x -> Not' x) <|>
            scan_bexp_elem <|>
            scan_inner_bexp
        in scan_infix_pairc scan_0 scan_6 "And'" (fun (x, y) -> And' (x, y)) <|> scan_0
      )
    in
      scan_infix_pairc scan_6 scan_7 "Imply'" (fun (x, y) -> Imply' (x, y)) <|>
      scan_infix_pairc scan_6 scan_7 "Or'" (fun (x, y) -> Or' (x, y)) <|>
      scan_6
  )

let scan_formula = scan_parens "(" ")" (choice [
  scan_singlec scan_bexp "EX" (fun x -> EX' x);
  scan_singlec scan_bexp "EG" (fun x -> EG' x);
  scan_singlec scan_bexp "AX" (fun x -> AX' x);
  scan_singlec scan_bexp "AG" (fun x -> AG' x);
  scan_infix_pairc scan_bexp scan_bexp "Leadsto" (fun (x, y) -> Leadsto' (x, y));
  scan_infix_pairc scan_bexp scan_bexp "-->"     (fun (x, y) -> Leadsto' (x, y));
  ])

let scan_singlec_int = scan_singlec scan_int

let scan_bool =
  (string "true" >>| fun _ -> true) <|> (string "false" >>| fun _ -> false)

let instr_nullaries = [
  ("ADD'", ADD');
  ("NOT'", NOT');
  ("AND'", AND');
  ("LT'", LT');
  ("LE'", LE');
  ("EQ'", EQ');
  ("COPY'", COPY');
  ("CALL'", CALL');
  ("RETURN'", RETURN');
  ("HALT'", HALT');
  ("POP'", POP');
  ]

let scan_nullary head constr = string head >>| fun _ -> constr

let scan_nullary_instr = choice (List.map (fun (x, y) -> scan_nullary x y) instr_nullaries)

let scan_instr =
  choice [
  scan_nullary_instr;
  scan_pairc [scan_int; scan_int] "STOREI'" (fun (x, y) -> STOREI' (x, y));
  scan_pairc [scan_int; scan_int] "STOREC'" (fun (x, y) -> STOREC' (x, y));
  scan_singlec_int "JMPZ'" (fun x -> JMPZ' x);
  scan_singlec_int "LID'" (fun x -> LID' x);
  scan_singlec_int "PUSH'" (fun x -> PUSH' x);
  scan_singlec scan_bool "SETF'" (fun x -> SETF' x);
  ]

let scan_act = choice [
  scan_singlec scan_int "In" (fun x -> Model_Checker.In (x));
  scan_singlec scan_int "Out" (fun x -> Model_Checker.Out (x));
  scan_singlec scan_int "Sil" (fun x -> Model_Checker.Sil (x));
  ]

let scan_instrc =
  scan_singlec scan_nullary_instr "INSTR'" (fun x -> INSTR' x) <|>
  scan_singlec (scan_parens "(" ")" scan_instr) "INSTR'" (fun x -> INSTR' x) <|>
  scan_singlec (scan_parens "(" ")" scan_acconstraint) "CEXP'" (fun x -> CEXP' x)

let scan_option p = scan_nullary "NONE" None <|> scan_singlec p "SOME" (fun x -> Some x)

let scan_quadruple' (p1, p2, p3, p4) =
  lift4
    (fun a b c d -> (a, b, c, d))
    (p1 <* string "," <* scan_whitespace)
    (p2 <* string "," <* scan_whitespace)
    (p3 <* string "," <* scan_whitespace)
    p4
  |> scan_parens "(" ")"

let scan_invariant = scan_acconstraint |> scan_list |> scan_list |> scan_list

let scan_trans =
  scan_quadruple' (scan_int, scan_act, scan_int, scan_int) |>
  scan_list |>
  scan_list |>
  scan_list

let scan_prog = scan_parens "(" ")" scan_instrc |> scan_option |> scan_list

let scan_all =
  (scan_int <?> "Number of processes") --- (* p *)
  (scan_int <?> "Number of clocks") --- (* m *)
  (scan_list scan_int <?> "Clock ceiling") --- (* k *)
  (scan_int <?> "Number of max. steps") --- (* max_steps *)
  (scan_invariant <?> "Invariants") --- (* inv *)
  (scan_trans <?> "Transitions") --- (* trans *)
  (scan_prog <?> "Program") --- (* prog *)
  (scan_formula <?> "Query") --- (* query *)
  (scan_list (scan_pair [scan_int; scan_int]) <?> "Variable bounds") --- (* bounds *)
  ((scan_int |> scan_list |> scan_list) <?> "Predicates") --- (* pred *)
  (scan_list scan_int <?> "Initial state of variables") --- (* s *)
  ((scan_int <* scan_whitespace) <?> "Number of actions") (* na *)
  (* XXX Can we end with EOF or EOS here? *)


(*** Utilites ***)
let println s = print_string (s ^ "\n")

let list_to_string f xs = List.map f xs |> String.concat ", " |> fun x -> "[" ^ x ^ "]"

let print_result = function None -> println("Invalid input\n")
    | Some true -> println("Property is satisfied\n")
    | Some false -> println("Property is not satisfied\n")

let map_option f = function
    | None -> None
    | Some x -> Some (f x)

let implode xs =
    String.init (List.length xs) (List.nth xs)

(*** Wrapping up the checker ***)
let check_and_verify2 p m ignore_k max_steps inv trans prog query bounds pred s na () =
  let
    debug_level: int ref = ref 0
    and map = List.map
    in let _ = debug_level := 2 in
    let map_constraint = map (map_acconstraint to_nat to_int);
    in
    let inv = map (map map_constraint) inv;
    and trans =
      map (map (map (fun (g, a, r, l) -> (to_nat g, (map_act to_nat a, (to_nat r, to_nat l)))))) trans;
    and prog = map (map_option (map_instrc to_nat to_int to_int)) prog
    and query = map_formula to_nat to_int query
    and bounds = map (fun (a, b) -> (to_int a, to_int b)) bounds
    and pred = map (map to_nat) pred
    and s = map to_int s
    and p = to_nat p
    and m = to_nat m
    and max_steps = to_nat max_steps
    and na = to_nat na;
    in
    let _ = if !debug_level >= 3 then println("Now calculating ceiling") else ();
    and k = Model_Checker.k p m max_steps inv trans prog;
    in
    let k = map (map (map nat_of_int)) k;
    and _ = if !debug_level >= 3 then println("Finished calculating ceiling") else ();
    in
    let _ =
      if !debug_level >= 3 then
        println (
          "\n"
          ^ list_to_string (list_to_string (list_to_string (fun x -> Model_Checker.integer_of_nat x |> Big_int_Z.string_of_big_int))) k
          ^ "\n"
        )
      else ()

    and print_checks name tests =
        if List.for_all snd tests then () else
        "\n\nThe following checks failed (" ^ name ^ "):\n- " ^
        String.concat "\n- " (tests |> List.filter (fun (_, b) -> not b) |> List.map (fun (x, _) -> implode x))
        |> println


    in let _ = if !debug_level >= 2 then
      let
        pre_checks = Model_Checker.pre_checks p m inv pred trans prog
        and start_checks = Model_Checker.start_checks p max_steps trans prog bounds pred s
        and ceiling_checks = Model_Checker.ceiling_checks p m max_steps inv trans prog k
        and more_checks = Model_Checker.more_checks trans na
        in
        let _ = print_checks "Preconditions" pre_checks
        and _ = print_checks "Start" start_checks
        and _ = print_checks "Ceiling" ceiling_checks
        and _ = print_checks "Actions" more_checks
      in println "" else ();
    and t = Sys.time()
    and result = Model_Checker.precond_mc p m k max_steps inv trans prog query bounds pred s na ()
    in let t = Sys.time() -. t
    in let _ = println("Internal time for precondition check + actual checking: " ^ string_of_float t)
    and _ = println("")
    (* and _ = if !debug_level >= 1 then
      let
        _ = println("# explored states: " ^ string_of_int(Tracing.get_count ()))
        and _ = println("")
      in () else (); *)
  in
    print_result result

let check_and_verify_parse input = match parse_string scan_all input with
  | Error s -> println "Parse error:\nFailed to read: "; println s
  | Ok result ->
    let (result, na) = result
    in let (result, s) = result
    in let (result, pred) = result
    in let (result, bounds) = result
    in let (result, query) = result
    in let (result, prog) = result
    in let (result, trans) = result
    in let (result, inv) = result
    in let (result, max_steps) = result
    in let (result, ignore_k) = result
    in let (result, m) = result
    in let p = result
  in
    check_and_verify2 p m ignore_k max_steps inv trans prog query bounds pred s na ()

let check_and_verify_from_stream () =
  let
    input = read_line ()
  in
    if input = ""
    then println "Failed to read line from input!"
    (* We append a space to terminate the input for the parser *)
    else input ^ " " |> check_and_verify_parse;;

check_and_verify_from_stream ()
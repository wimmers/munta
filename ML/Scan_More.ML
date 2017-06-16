infix 5 ---;

structure Scan_More =
struct

  (** Copied from Mlton/sml90 to achieve compatiblity with Isabelle/ML **)
  exception Ord
  fun ord s =
         if String.size s = 0
            then raise Ord
         else Char.ord(String.sub(s, 0))

  (** Additional parsers to read ints, lists, and datatype constructor terms **)
  val explode_string = map Char.toString o String.explode;
  val scan_neg = op $$ "~" >> K (~1);
  val scan_nat = Scan.many1 (fn x => ord "0" <= ord x andalso ord x <= ord "9") >> (the o Int.fromString o String.concat);
  val scan_int = Scan.optional scan_neg 1 -- scan_nat >> op *;
  val scan_whitespace = Scan.many (fn x => ord x = ord " ");
  fun (p1 --- p2) = (p1 --| scan_whitespace -- p2)
  fun scan_collection lparen rparen sep (item_parser : (string list -> 'a * string list)) =
    op $$ lparen |--
    (
    (item_parser -- Scan.repeat (op $$ sep --- item_parser >> snd) >> op ::) ||
    Scan.succeed []
    )
    --| op $$ rparen;
  fun scan_list item_parser = scan_collection "[" "]" "," item_parser;
  fun scan_tuple item_parser = scan_collection "(" ")" "," item_parser;
  fun scan_collection' lparen rparen sep item_parsers =
    let
      fun scan_inner [] = Scan.succeed []
        | scan_inner [p] = p >> (fn x => [x])
        | scan_inner (p :: ps) =
            (p -- op $$ sep -- scan_whitespace >> (fst o fst)) -- scan_inner ps >> op ::
    in op $$ lparen -- scan_inner item_parsers -- op $$ rparen >> (snd o fst) end
  fun scan_tuple' ps = scan_collection' "(" ")" "," ps;
  fun scan_pair ps = scan_tuple' ps >> (fn [a,b] => (a,b))
  fun scan_triple ps = scan_tuple' ps >> (fn [a,b,c] => (a,b,c))
  fun scan_quadruple ps = scan_tuple' ps >> (fn [a,b,c,d] => (a,b,c,d))
  fun scan_pairc ps head constr =
    Scan.this_string head -- scan_whitespace |-- scan_pair ps >> constr
  fun scan_singlec p head constr =
    Scan.this_string head -- scan_whitespace |-- p >> constr
  fun scan_nullary head constr =
    Scan.this_string head >> K constr
  fun scan_infix_pair p1 p2 sep =
    p1 --| (scan_whitespace -- Scan.this_string sep -- scan_whitespace) -- p2
  fun scan_infix_pairc p1 p2 sep constr =
    scan_infix_pair p1 p2 sep >> constr

end;

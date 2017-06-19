(* Taken from Isabelle: https://isabelle.in.tum.de *)
(*  Title:      Pure/library.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Markus Wenzel, TU Muenchen

Basic library: functions, pairs, booleans, lists, integers,
strings, lists as sets, orders, current directory, misc.

See also General/basics.ML for the most fundamental concepts.
*)

infix 2 ?
infix 3 o oo ooo oooo
infix 4 ~~ upto downto
infix orf andf

signature BASIC_LIBRARY =
sig
  (*functions*)
  val undefined: 'a -> 'b
  val I: 'a -> 'a
  val K: 'a -> 'b -> 'a
  val curry: ('a * 'b -> 'c) -> 'a -> 'b -> 'c
  val uncurry: ('a -> 'b -> 'c) -> 'a * 'b -> 'c
  val ? : bool * ('a -> 'a) -> 'a -> 'a
  val oo: ('a -> 'b) * ('c -> 'd -> 'a) -> 'c -> 'd -> 'b
  val ooo: ('a -> 'b) * ('c -> 'd -> 'e -> 'a) -> 'c -> 'd -> 'e -> 'b
  val oooo: ('a -> 'b) * ('c -> 'd -> 'e -> 'f -> 'a) -> 'c -> 'd -> 'e -> 'f -> 'b
  val funpow: int -> ('a -> 'a) -> 'a -> 'a
  val funpow_yield: int -> ('a -> 'b * 'a) -> 'a -> 'b list * 'a

  (*pairs*)
  val pair: 'a -> 'b -> 'a * 'b
  val rpair: 'a -> 'b -> 'b * 'a
  val fst: 'a * 'b -> 'a
  val snd: 'a * 'b -> 'b
  val eq_fst: ('a * 'c -> bool) -> ('a * 'b) * ('c * 'd) -> bool
  val eq_snd: ('b * 'd -> bool) -> ('a * 'b) * ('c * 'd) -> bool
  val eq_pair: ('a * 'c -> bool) -> ('b * 'd -> bool) -> ('a * 'b) * ('c * 'd) -> bool
  val swap: 'a * 'b -> 'b * 'a
  val apfst: ('a -> 'b) -> 'a * 'c -> 'b * 'c
  val apsnd: ('a -> 'b) -> 'c * 'a -> 'c * 'b
  val apply2: ('a -> 'b) -> 'a * 'a -> 'b * 'b

  (*booleans*)
  val equal: ''a -> ''a -> bool
  val not_equal: ''a -> ''a -> bool
  val orf: ('a -> bool) * ('a -> bool) -> 'a -> bool
  val andf: ('a -> bool) * ('a -> bool) -> 'a -> bool
  val exists: ('a -> bool) -> 'a list -> bool
  val forall: ('a -> bool) -> 'a list -> bool

  (*lists*)
  val single: 'a -> 'a list
  val the_single: 'a list -> 'a
  val singleton: ('a list -> 'b list) -> 'a -> 'b
  val yield_singleton: ('a list -> 'c -> 'b list * 'c) -> 'a -> 'c -> 'b * 'c
  val perhaps_apply: ('a -> 'a option) list -> 'a -> 'a option
  val perhaps_loop: ('a -> 'a option) -> 'a -> 'a option
  val foldl1: ('a * 'a -> 'a) -> 'a list -> 'a
  val foldr1: ('a * 'a -> 'a) -> 'a list -> 'a
  val eq_list: ('a * 'a -> bool) -> 'a list * 'a list -> bool
  val maps: ('a -> 'b list) -> 'a list -> 'b list
  val filter: ('a -> bool) -> 'a list -> 'a list
  val filter_out: ('a -> bool) -> 'a list -> 'a list
  val map_filter: ('a -> 'b option) -> 'a list -> 'b list
  val take: int -> 'a list -> 'a list
  val drop: int -> 'a list -> 'a list
  val chop: int -> 'a list -> 'a list * 'a list
  val chop_groups: int -> 'a list -> 'a list list
  val nth: 'a list -> int -> 'a
  val nth_list: 'a list list -> int -> 'a list
  val nth_map: int -> ('a -> 'a) -> 'a list -> 'a list
  val nth_drop: int -> 'a list -> 'a list
  val map_index: (int * 'a -> 'b) -> 'a list -> 'b list
  val fold_index: (int * 'a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val map_range: (int -> 'a) -> int -> 'a list
  val fold_range: (int -> 'a -> 'a) -> int -> 'a -> 'a
  val split_last: 'a list -> 'a list * 'a
  val find_first: ('a -> bool) -> 'a list -> 'a option
  val find_index: ('a -> bool) -> 'a list -> int
  val get_first: ('a -> 'b option) -> 'a list -> 'b option
  val get_index: ('a -> 'b option) -> 'a list -> (int * 'b) option
  val flat: 'a list list -> 'a list
  val unflat: 'a list list -> 'b list -> 'b list list
  val grouped: int -> (('a list -> 'b list) -> 'c list list -> 'd list list) ->
    ('a -> 'b) -> 'c list -> 'd list
  val burrow: ('a list -> 'b list) -> 'a list list -> 'b list list
  val burrow_options: ('a list -> 'b list) -> 'a option list -> 'b option list
  val fold_burrow: ('a list -> 'c -> 'b list * 'd) -> 'a list list -> 'c -> 'b list list * 'd
  val separate: 'a -> 'a list -> 'a list
  val surround: 'a -> 'a list -> 'a list
  val replicate: int -> 'a -> 'a list
  val map_product: ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val fold_product: ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
  val map2: ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val fold2: ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
  val map_split: ('a -> 'b * 'c) -> 'a list -> 'b list * 'c list
  val zip_options: 'a list -> 'b option list -> ('a * 'b) list
  val ~~ : 'a list * 'b list -> ('a * 'b) list
  val split_list: ('a * 'b) list -> 'a list * 'b list
  val burrow_fst: ('a list -> 'b list) -> ('a * 'c) list -> ('b * 'c) list
  val is_prefix: ('a * 'a -> bool) -> 'a list -> 'a list -> bool
  val take_prefix: ('a -> bool) -> 'a list -> 'a list * 'a list
  val chop_prefix: ('a * 'b -> bool) -> 'a list * 'b list -> 'a list * ('a list * 'b list)
  val take_suffix: ('a -> bool) -> 'a list -> 'a list * 'a list
  val prefixes1: 'a list -> 'a list list
  val prefixes: 'a list -> 'a list list
  val suffixes1: 'a list -> 'a list list
  val suffixes: 'a list -> 'a list list
  val trim: ('a -> bool) -> 'a list -> 'a list

end;

signature LIBRARY =
sig
  include BASIC_LIBRARY
  val foldl: ('a * 'b -> 'a) -> 'a * 'b list -> 'a
  val foldr: ('a * 'b -> 'b) -> 'a list * 'b -> 'b
end;

structure Library: LIBRARY =
struct

(* functions *)

fun undefined _ = raise Match;

fun I x = x;
fun K x = fn _ => x;
fun curry f x y = f (x, y);
fun uncurry f (x, y) = f x y;

(*conditional application*)
fun b ? f = fn x => if b then f x else x;

(*composition with multiple args*)
fun (f oo g) x y = f (g x y);
fun (f ooo g) x y z = f (g x y z);
fun (f oooo g) x y z w = f (g x y z w);

(*function exponentiation: f (... (f x) ...) with n applications of f*)
fun funpow (0 : int) _ = I
  | funpow n f = f #> funpow (n - 1) f;

fun funpow_yield (0 : int) _ x = ([], x)
  | funpow_yield n f x = x |> f ||>> funpow_yield (n - 1) f |>> op ::;


(* pairs *)

fun pair x y = (x, y);
fun rpair x y = (y, x);

fun fst (x, y) = x;
fun snd (x, y) = y;

fun eq_fst eq ((x1, _), (x2, _)) = eq (x1, x2);
fun eq_snd eq ((_, y1), (_, y2)) = eq (y1, y2);
fun eq_pair eqx eqy ((x1, y1), (x2, y2)) = eqx (x1, x2) andalso eqy (y1, y2);

fun swap (x, y) = (y, x);

fun apfst f (x, y) = (f x, y);
fun apsnd f (x, y) = (x, f y);
fun apply2 f (x, y) = (f x, f y);


(* booleans *)

(*polymorphic equality*)
fun equal x y = x = y;
fun not_equal x y = x <> y;

(*combining predicates*)
fun p orf q = fn x => p x orelse q x;
fun p andf q = fn x => p x andalso q x;

val exists = List.exists;
val forall = List.all;



(** lists **)

fun single x = [x];

fun the_single [x] = x
  | the_single _ = raise List.Empty;

fun singleton f x = the_single (f [x]);

fun yield_singleton f x = f [x] #>> the_single;

fun perhaps_apply funs arg =
  let
    fun app [] res = res
      | app (f :: fs) (changed, x) =
          (case f x of
            NONE => app fs (changed, x)
          | SOME x' => app fs (true, x'));
  in (case app funs (false, arg) of (false, _) => NONE | (true, arg') => SOME arg') end;

fun perhaps_loop f arg =
  let
    fun loop (changed, x) =
      (case f x of
        NONE => (changed, x)
      | SOME x' => loop (true, x'));
  in (case loop (false, arg) of (false, _) => NONE | (true, arg') => SOME arg') end;


(* fold -- old versions *)

(*the following versions of fold are designed to fit nicely with infixes*)

(*  (op @) (e, [x1, ..., xn])  ===>  ((e @ x1) @ x2) ... @ xn
    for operators that associate to the left (TAIL RECURSIVE)*)
fun foldl (f: 'a * 'b -> 'a) : 'a * 'b list -> 'a =
  let fun itl (e, [])  = e
        | itl (e, a::l) = itl (f(e, a), l)
  in  itl end;

(*  (op @) ([x1, ..., xn], e)  ===>   x1 @ (x2 ... @ (xn @ e))
    for operators that associate to the right (not tail recursive)*)
fun foldr f (l, e) =
  let fun itr [] = e
        | itr (a::l) = f(a, itr l)
  in  itr l  end;

(*  (op @) [x1, ..., xn]  ===>  ((x1 @ x2) @ x3) ... @ xn
    for operators that associate to the left (TAIL RECURSIVE)*)
fun foldl1 f [] = raise List.Empty
  | foldl1 f (x :: xs) = foldl f (x, xs);

(*  (op @) [x1, ..., xn]  ===>   x1 @ (x2 ... @ (x[n-1] @ xn))
    for n > 0, operators that associate to the right (not tail recursive)*)
fun foldr1 f [] = raise List.Empty
  | foldr1 f l =
      let fun itr [x] = x
            | itr (x::l) = f(x, itr l)
      in  itr l  end;


(* basic list functions *)

fun eq_list eq (list1, list2) =
    let
      fun eq_lst (x :: xs, y :: ys) = eq (x, y) andalso eq_lst (xs, ys)
        | eq_lst _ = true;
    in length list1 = length list2 andalso eq_lst (list1, list2) end;

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

val filter = List.filter;
fun filter_out f = filter (not o f);
val map_filter = List.mapPartial;

fun take (0: int) xs = []
  | take _ [] = []
  | take n (x :: xs) = x :: take (n - 1) xs;

fun drop (0: int) xs = xs
  | drop _ [] = []
  | drop n (x :: xs) = drop (n - 1) xs;

fun chop (0: int) xs = ([], xs)
  | chop _ [] = ([], [])
  | chop n (x :: xs) = chop (n - 1) xs |>> cons x;

fun chop_groups n list =
  (case chop (Int.max (n, 1)) list of
    ([], _) => []
  | (g, rest) => g :: chop_groups n rest);


(*return nth element of a list, where 0 designates the first element;
  raise Subscript if list too short*)
fun nth xs i = List.nth (xs, i);

fun nth_list xss i = nth xss i handle General.Subscript => [];

fun nth_map 0 f (x :: xs) = f x :: xs
  | nth_map n f (x :: xs) = x :: nth_map (n - 1) f xs
  | nth_map (_: int) _ [] = raise Subscript;

fun nth_drop n xs =
  List.take (xs, n) @ List.drop (xs, n + 1);

fun map_index f =
  let
    fun map_aux (_: int) [] = []
      | map_aux i (x :: xs) = f (i, x) :: map_aux (i + 1) xs
  in map_aux 0 end;

fun fold_index f =
  let
    fun fold_aux (_: int) [] y = y
      | fold_aux i (x :: xs) y = fold_aux (i + 1) xs (f (i, x) y)
  in fold_aux 0 end;

fun map_range f i =
  let
    fun map_aux (k: int) =
      if k < i then f k :: map_aux (k + 1) else []
  in map_aux 0 end;

fun fold_range f i =
  let
    fun fold_aux (k: int) y =
      if k < i then fold_aux (k + 1) (f k y) else y
  in fold_aux 0 end;


(*rear decomposition*)
fun split_last [] = raise List.Empty
  | split_last [x] = ([], x)
  | split_last (x :: xs) = apfst (cons x) (split_last xs);

(*find first element satisfying predicate*)
val find_first = List.find;

(*find position of first element satisfying a predicate*)
fun find_index pred =
  let fun find (_: int) [] = ~1
        | find n (x :: xs) = if pred x then n else find (n + 1) xs;
  in find 0 end;

(*get first element by lookup function*)
fun get_first _ [] = NONE
  | get_first f (x :: xs) =
      (case f x of
        NONE => get_first f xs
      | some => some);

fun get_index f =
  let
    fun get (_: int) [] = NONE
      | get i (x :: xs) =
          (case f x of
            NONE => get (i + 1) xs
          | SOME y => SOME (i, y))
  in get 0 end;

val flat = List.concat;

fun unflat (xs :: xss) ys =
      let val (ps, qs) = chop (length xs) ys
      in ps :: unflat xss qs end
  | unflat [] [] = []
  | unflat _ _ = raise ListPair.UnequalLengths;

fun grouped n comb f = chop_groups n #> comb (map f) #> flat;

fun burrow f xss = unflat xss (f (flat xss));

fun burrow_options f os = map (try hd) (burrow f (map the_list os));

fun fold_burrow f xss s =
  apfst (unflat xss) (f (flat xss) s);

(*separate s [x1, x2, ..., xn]  ===>  [x1, s, x2, s, ..., s, xn]*)
fun separate s (x :: (xs as _ :: _)) = x :: s :: separate s xs
  | separate _ xs = xs;

fun surround s (x :: xs) = s :: x :: surround s xs
  | surround s [] = [s];

(*make the list [x, x, ..., x] of length n*)
fun replicate (n: int) x =
  let fun rep (0, xs) = xs
        | rep (n, xs) = rep (n - 1, x :: xs)
  in
    if n < 0 then raise Subscript
    else rep (n, [])
  end;


(* direct product *)

fun map_product f _ [] = []
  | map_product f [] _ = []
  | map_product f (x :: xs) ys = map (f x) ys @ map_product f xs ys;

fun fold_product f _ [] z = z
  | fold_product f [] _ z = z
  | fold_product f (x :: xs) ys z = z |> fold (f x) ys |> fold_product f xs ys;


(* lists of pairs *)

fun map2 _ [] [] = []
  | map2 f (x :: xs) (y :: ys) = f x y :: map2 f xs ys
  | map2 _ _ _ = raise ListPair.UnequalLengths;

fun fold2 _ [] [] z = z
  | fold2 f (x :: xs) (y :: ys) z = fold2 f xs ys (f x y z)
  | fold2 _ _ _ _ = raise ListPair.UnequalLengths;

fun map_split _ [] = ([], [])
  | map_split f (x :: xs) =
      let
        val (y, w) = f x;
        val (ys, ws) = map_split f xs;
      in (y :: ys, w :: ws) end;

fun zip_options (x :: xs) (SOME y :: ys) = (x, y) :: zip_options xs ys
  | zip_options (_ :: xs) (NONE :: ys) = zip_options xs ys
  | zip_options _ [] = []
  | zip_options [] _ = raise ListPair.UnequalLengths;

(*combine two lists forming a list of pairs:
  [x1, ..., xn] ~~ [y1, ..., yn]  ===>  [(x1, y1), ..., (xn, yn)]*)
fun [] ~~ [] = []
  | (x :: xs) ~~ (y :: ys) = (x, y) :: (xs ~~ ys)
  | _ ~~ _ = raise ListPair.UnequalLengths;

(*inverse of ~~; the old 'split':
  [(x1, y1), ..., (xn, yn)]  ===>  ([x1, ..., xn], [y1, ..., yn])*)
val split_list = ListPair.unzip;

fun burrow_fst f xs = split_list xs |>> f |> op ~~;


(* prefixes, suffixes *)

fun is_prefix _ [] _ = true
  | is_prefix eq (x :: xs) (y :: ys) = eq (x, y) andalso is_prefix eq xs ys
  | is_prefix eq _ _ = false;

(* [x1, ..., xi, ..., xn]  --->  ([x1, ..., x(i-1)], [xi, ..., xn])
   where xi is the first element that does not satisfy the predicate*)
fun take_prefix (pred : 'a -> bool)  (xs: 'a list) : 'a list * 'a list =
  let fun take (rxs, []) = (rev rxs, [])
        | take (rxs, x :: xs) =
            if  pred x  then  take(x :: rxs, xs)  else  (rev rxs, x :: xs)
  in  take([], xs)  end;

fun chop_prefix eq ([], ys) = ([], ([], ys))
  | chop_prefix eq (xs, []) = ([], (xs, []))
  | chop_prefix eq (xs as x :: xs', ys as y :: ys') =
      if eq (x, y) then
        let val (ps', xys'') = chop_prefix eq (xs', ys')
        in (x :: ps', xys'') end
      else ([], (xs, ys));

(* [x1, ..., xi, ..., xn]  --->  ([x1, ..., xi], [x(i+1), ..., xn])
   where xi is the last element that does not satisfy the predicate*)
fun take_suffix _ [] = ([], [])
  | take_suffix pred (x :: xs) =
      (case take_suffix pred xs of
        ([], sffx) => if pred x then ([], x :: sffx) else ([x], sffx)
      | (prfx, sffx) => (x :: prfx, sffx));

fun prefixes1 [] = []
  | prefixes1 (x :: xs) = map (cons x) ([] :: prefixes1 xs);

fun prefixes xs = [] :: prefixes1 xs;

fun suffixes1 xs = map rev (prefixes1 (rev xs));
fun suffixes xs = [] :: suffixes1 xs;

fun trim pred = take_prefix pred #> #2 #> take_suffix pred #> #1;

end;

structure Basic_Library: BASIC_LIBRARY = Library;
open Basic_Library;


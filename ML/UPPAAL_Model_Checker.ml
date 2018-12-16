module Uint : sig
  type t = int
  val dflt_size : Big_int.big_int
  val less : t -> t -> bool
  val less_eq : t -> t -> bool
  val set_bit : t -> Big_int.big_int -> bool -> t
  val shiftl : t -> Big_int.big_int -> t
  val shiftr : t -> Big_int.big_int -> t
  val shiftr_signed : t -> Big_int.big_int -> t
  val test_bit : t -> Big_int.big_int -> bool
  val int_mask : int
  val int32_mask : int32
  val int64_mask : int64
end = struct

type t = int

(* Can be replaced with Sys.int_size in OCaml 4.03.0 *)
let dflt_size_int = 
  let rec f n = if n=0 then 0 else f (n / 2) + 1 
  in f min_int;;

let dflt_size = Big_int.big_int_of_int dflt_size_int;;

(* negative numbers have their highest bit set, 
   so they are greater than positive ones *)
let less x y =
  if x<0 then
    y<0 && x<y
  else y < 0 || x < y;;

let less_eq x y =
  if x < 0 then
    y < 0 &&  x <= y
  else y < 0 || x <= y;;

let set_bit x n b =
  let mask = 1 lsl (Big_int.int_of_big_int n)
  in if b then x lor mask
     else x land (lnot mask);;

let shiftl x n = x lsl (Big_int.int_of_big_int n);;

let shiftr x n = x lsr (Big_int.int_of_big_int n);;

let shiftr_signed x n = x asr (Big_int.int_of_big_int n);;

let test_bit x n = x land (1 lsl (Big_int.int_of_big_int n)) <> 0;;

let int_mask =
  if dflt_size_int < 32 then lnot 0 else 0xFFFFFFFF;;

let int32_mask = 
  if dflt_size_int < 32 then Int32.pred (Int32.shift_left Int32.one dflt_size_int) 
  else Int32.of_string "0xFFFFFFFF";;

let int64_mask = 
  if dflt_size_int < 64 then Int64.pred (Int64.shift_left Int64.one dflt_size_int) 
  else Int64.of_string "0xFFFFFFFFFFFFFFFF";;

end;; (*struct Uint*)

module Uint32 : sig
  val less : int32 -> int32 -> bool
  val less_eq : int32 -> int32 -> bool
  val set_bit : int32 -> Big_int.big_int -> bool -> int32
  val shiftl : int32 -> Big_int.big_int -> int32
  val shiftr : int32 -> Big_int.big_int -> int32
  val shiftr_signed : int32 -> Big_int.big_int -> int32
  val test_bit : int32 -> Big_int.big_int -> bool
end = struct

(* negative numbers have their highest bit set, 
   so they are greater than positive ones *)
let less x y =
  if Int32.compare x Int32.zero < 0 then
    Int32.compare y Int32.zero < 0 && Int32.compare x y < 0
  else Int32.compare y Int32.zero < 0 || Int32.compare x y < 0;;

let less_eq x y =
  if Int32.compare x Int32.zero < 0 then
    Int32.compare y Int32.zero < 0 && Int32.compare x y <= 0
  else Int32.compare y Int32.zero < 0 || Int32.compare x y <= 0;;

let set_bit x n b =
  let mask = Int32.shift_left Int32.one (Big_int.int_of_big_int n)
  in if b then Int32.logor x mask
     else Int32.logand x (Int32.lognot mask);;

let shiftl x n = Int32.shift_left x (Big_int.int_of_big_int n);;

let shiftr x n = Int32.shift_right_logical x (Big_int.int_of_big_int n);;

let shiftr_signed x n = Int32.shift_right x (Big_int.int_of_big_int n);;

let test_bit x n =
  Int32.compare 
    (Int32.logand x (Int32.shift_left Int32.one (Big_int.int_of_big_int n)))
    Int32.zero
  <> 0;;

end;; (*struct Uint32*)


module FArray = struct

  type 'a cell = Value of 'a array | Upd of int * 'a * 'a cell ref ;;

  type 'a array = 'a cell ref;;

  let array (size,v) = ref (Value (Array.make size v));;
  let tabulate (size, f) = ref (Value (Array.init size f));;
  let fromList l = ref (Value (Array.of_list l));;

  let rec sub = function
    | ({contents = (Value a)}, idx) -> Array.get a idx
    | ({contents = Upd (i,v,cr)}, idx) ->
        if i=idx then v
        else sub (cr,idx);;

  let rec length = function
    | {contents = Value a} -> Array.length a
    | {contents = Upd (i,v,cr)} -> length cr;;

  let rec realize_aux (aref, v) =
    match aref with
      | {contents = Value a} -> (
        let len = Array.length a in
        let a' = Array.make len v
        in
          Array.blit a 0 a' 0 (Array.length a);
          ref (Value a')
      )
      | {contents = Upd (i,v,cr)} -> (
        let res=realize_aux (cr,v) in
          match res with
            {contents = Value a} -> (Array.set a i v; res)
      );;

  let realize aref =
    match aref with
      | {contents  = Value _} -> aref
      | {contents = Upd (i,v,cr)} -> realize_aux(aref,v);;

  let update (aref,idx,v) =
    match aref with
      | {contents = Value a} -> (
        let nref=ref (Value a) in
          aref := Upd (idx,Array.get a idx,nref);
          Array.set  a idx v;
          nref
      )
      | {contents = Upd _} ->
        let ra = realize_aux(aref,v) in
          match ra with
            {contents = Value a} -> Array.set a idx v;
          ra
      ;;

  let rec grow (aref, inc, x) = match aref with
    | {contents = Value a} -> (
      let len=Array.length a in
      let na = Array.make (len+inc) x
      in
        Array.blit a 0 na 0 (Array.length a);
        ref (Value na)
      )
  | {contents = Upd _} -> (
    grow (realize aref, inc, x)
  );;

exception Size;;

  let rec shrink (aref, sz) = match aref with
    | {contents = Value a} -> (
      if sz > Array.length a then
        raise Size
      else (
        ref (Value (Array.init sz (fun i -> Array.get a i)))
      )
    )
    | { contents = Upd _} -> (
      shrink (realize aref,sz)
    );;

module IsabelleMapping = struct

type 'a array_type = 'a array;;

let new_array (a:'a) (n:Big_int.big_int) = array (Big_int.int_of_big_int n, a);;

let array_length (a:'a array_type) = Big_int.big_int_of_int (length a);;

let array_get (a:'a array_type) (i:Big_int.big_int) = sub (a, Big_int.int_of_big_int i);;

let array_set (a:'a array_type) (i:Big_int.big_int) (e:'a) = update (a, Big_int.int_of_big_int i, e);;

let array_of_list (xs:'a list) = fromList xs;;

let array_grow (a:'a array_type) (i:Big_int.big_int) (x:'a) = grow (a, Big_int.int_of_big_int i, x);;

let array_shrink (a:'a array_type) (sz:Big_int.big_int) = shrink (a,Big_int.int_of_big_int sz);;

let array_get_oo (d:'a) (a:'a array_type) (i:Big_int.big_int) =
  try sub (a,Big_int.int_of_big_int i) with Invalid_argument _ -> d

let array_set_oo (d:(unit->'a array_type)) (a:'a array_type) (i:Big_int.big_int) (e:'a) =
  try update (a, Big_int.int_of_big_int i, e) with Invalid_argument _ -> d ()

end;;

end;;



module Tracing : sig
  val count_up : unit -> unit
  val get_count : unit -> int
end = struct
  let counter = ref 0
  let count_up () = (counter := !counter + 1)
  let get_count () = !counter
end


module Bits_Integer : sig
  val and_pninteger : Big_int.big_int -> Big_int.big_int -> Big_int.big_int
  val or_pninteger : Big_int.big_int -> Big_int.big_int -> Big_int.big_int
  val shiftl : Big_int.big_int -> Big_int.big_int -> Big_int.big_int
  val shiftr : Big_int.big_int -> Big_int.big_int -> Big_int.big_int
  val test_bit : Big_int.big_int -> Big_int.big_int -> bool
end = struct

let and_pninteger bi1 bi2 =
  Big_int.and_big_int bi1
    (Big_int.xor_big_int
      (Big_int.pred_big_int
        (Big_int.shift_left_big_int Big_int.unit_big_int
           (max (Big_int.num_digits_big_int bi1 * Nat.length_of_digit)
                (Big_int.num_digits_big_int bi2 * Nat.length_of_digit))))
      (Big_int.pred_big_int (Big_int.minus_big_int bi2)));;

let or_pninteger bi1 bi2 =
  Big_int.pred_big_int (Big_int.minus_big_int
    (Big_int.and_big_int
      (Big_int.xor_big_int
         (Big_int.pred_big_int
           (Big_int.shift_left_big_int Big_int.unit_big_int
              (max (Big_int.num_digits_big_int bi1 * Nat.length_of_digit)
                   (Big_int.num_digits_big_int bi2 * Nat.length_of_digit))))
         bi1)
      (Big_int.pred_big_int (Big_int.minus_big_int bi2))));;

(* We do not need an explicit range checks here,
   because Big_int.int_of_big_int raises Failure 
   if the argument does not fit into an int. *)
let shiftl x n = Big_int.shift_left_big_int x (Big_int.int_of_big_int n);;

let shiftr x n = Big_int.shift_right_big_int x (Big_int.int_of_big_int n);;

let test_bit x n = 
  Big_int.eq_big_int 
    (Big_int.extract_big_int x (Big_int.int_of_big_int n) 1) 
    Big_int.unit_big_int

end;; (*struct Bits_Integer*)

module Model_Checker : sig
  type int = Int_of_integer of Big_int.big_int
  val integer_of_int : int -> Big_int.big_int
  type nat
  val integer_of_nat : nat -> Big_int.big_int
  val nat_of_integer : Big_int.big_int -> nat
  type instr = JMPZ of nat | ADD | NOT | AND | LT | LE | EQ | PUSH of int | POP
    | LID of nat | STORE | STOREI of nat * int | COPY | CALL | RETURN | HALT |
    STOREC of nat * int | SETF of bool
  type ('a, 'b) acconstraint = LTa of 'a * 'b | LEa of 'a * 'b | EQa of 'a * 'b
    | GT of 'a * 'b | GE of 'a * 'b
  type 'a instrc = INSTR of instr | CEXP of (nat, 'a) acconstraint
  type 'a set
  type 'a act = In of 'a | Out of 'a | Sil of 'a
  type bexp = Not of bexp | And of bexp * bexp | Or of bexp * bexp |
    Imply of bexp * bexp | Loc of nat * nat | Eq of nat * int | Lea of nat * int
    | Lta of nat * int | Ge of nat * int | Gt of nat * int
  type formula = EX of bexp | EG of bexp | AX of bexp | AG of bexp |
    Leadsto of bexp * bexp
  val map_option : ('a -> 'b) -> 'a option -> 'b option
  val pre_checks :
    nat ->
      nat ->
        (((nat, int) acconstraint list) list) list ->
          ('a list) list ->
            ((('b * ('c * ('d * nat))) list) list) list ->
              (int instrc option) list -> (string * bool) list
  val more_checks :
    (((nat * (nat act * (nat * nat))) list) list) list ->
      nat -> (string * bool) list
  val start_checks :
    nat ->
      nat ->
        (((nat * ('a * (nat * 'b))) list) list) list ->
          (int instrc option) list ->
            (int * int) list ->
              (nat list) list -> int list -> (string * bool) list
  val precond_dc :
    nat ->
      nat ->
        ((nat list) list) list ->
          nat ->
            (((nat, int) acconstraint list) list) list ->
              (((nat * (nat act * (nat * nat))) list) list) list ->
                (int instrc option) list ->
                  (int * int) list ->
                    (nat list) list ->
                      int list -> nat -> (unit -> (bool option))
  val ceiling_checks :
    nat ->
      nat ->
        nat ->
          (((nat, int) acconstraint list) list) list ->
            (((nat * (nat act * (nat * nat))) list) list) list ->
              (int instrc option) list ->
                ((nat list) list) list -> (string * bool) list
  val precond_mc :
    nat ->
      nat ->
        ((nat list) list) list ->
          nat ->
            (((nat, int) acconstraint list) list) list ->
              (((nat * (nat act * (nat * nat))) list) list) list ->
                (int instrc option) list ->
                  formula ->
                    (int * int) list ->
                      (nat list) list ->
                        int list -> nat -> (unit -> (bool option))
  val k :
    nat ->
      nat ->
        nat ->
          (((nat, int) acconstraint list) list) list ->
            (((nat * (nat act * (nat * nat))) list) list) list ->
              (int instrc option) list -> ((int list) list) list
end = struct

type int = Int_of_integer of Big_int.big_int;;

let rec integer_of_int (Int_of_integer k) = k;;

let rec equal_inta
  k l = Big_int.eq_big_int (integer_of_int k) (integer_of_int l);;

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let equal_int = ({equal = equal_inta} : int equal);;

type typerepa = Typerep of string * typerepa list;;

type 'a itself = Type;;

let rec typerep_inta t = Typerep ("Int.int", []);;

type 'a typerep = {typerep : 'a itself -> typerepa};;
let typerep _A = _A.typerep;;

type 'a countable = unit;;

type 'a heap = {countable_heap : 'a countable; typerep_heap : 'a typerep};;

let countable_int = (() : int countable);;

let typerep_int = ({typerep = typerep_inta} : int typerep);;

let heap_int =
  ({countable_heap = countable_int; typerep_heap = typerep_int} : int heap);;

let rec uminus_inta
  k = Int_of_integer (Big_int.minus_big_int (integer_of_int k));;

let zero_inta : int = Int_of_integer Big_int.zero_big_int;;

type num = One | Bit0 of num | Bit1 of num;;

let rec sgn_integer
  k = (if Big_int.eq_big_int k Big_int.zero_big_int then Big_int.zero_big_int
        else (if Big_int.lt_big_int k Big_int.zero_big_int
               then (Big_int.minus_big_int (Big_int.big_int_of_int 1))
               else (Big_int.big_int_of_int 1)));;

let rec apsnd f (x, y) = (x, f y);;

let rec comp f g = (fun x -> f (g x));;

let rec divmod_integer
  k l = (if Big_int.eq_big_int k Big_int.zero_big_int
          then (Big_int.zero_big_int, Big_int.zero_big_int)
          else (if Big_int.eq_big_int l Big_int.zero_big_int
                 then (Big_int.zero_big_int, k)
                 else comp (comp apsnd Big_int.mult_big_int) sgn_integer l
                        (if Big_int.eq_big_int (sgn_integer k) (sgn_integer l)
                          then Big_int.quomod_big_int (Big_int.abs_big_int k)
                                 (Big_int.abs_big_int l)
                          else (let (r, s) =
                                  Big_int.quomod_big_int (Big_int.abs_big_int k)
                                    (Big_int.abs_big_int l)
                                  in
                                 (if Big_int.eq_big_int s Big_int.zero_big_int
                                   then (Big_int.minus_big_int r,
  Big_int.zero_big_int)
                                   else (Big_int.sub_big_int
   (Big_int.minus_big_int r) (Big_int.big_int_of_int 1),
  Big_int.sub_big_int (Big_int.abs_big_int l) s))))));;

let rec snd (x1, x2) = x2;;

let rec modulo_integer k l = snd (divmod_integer k l);;

type nat = Nat of Big_int.big_int;;

let rec integer_of_nat (Nat x) = x;;

let rec modulo_nat
  m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));;

let rec fst (x1, x2) = x1;;

let rec divide_integer k l = fst (divmod_integer k l);;

let rec divide_nat
  m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));;

let rec equal_nata
  m n = Big_int.eq_big_int (integer_of_nat m) (integer_of_nat n);;

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

let rec max _A a b = (if less_eq _A a b then b else a);;

let ord_integer =
  ({less_eq = Big_int.le_big_int; less = Big_int.lt_big_int} :
    Big_int.big_int ord);;

let rec nat_of_integer k = Nat (max ord_integer Big_int.zero_big_int k);;

let zero_nata : nat = Nat Big_int.zero_big_int;;

let one_nata : nat = Nat (Big_int.big_int_of_int 1);;

type char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;;

let rec string_of_digit
  n = (if equal_nata n zero_nata
        then [Chara (false, false, false, false, true, true, false, false)]
        else (if equal_nata n one_nata
               then [Chara (true, false, false, false, true, true, false,
                             false)]
               else (if equal_nata n (nat_of_integer (Big_int.big_int_of_int 2))
                      then [Chara (false, true, false, false, true, true, false,
                                    false)]
                      else (if equal_nata n
                                 (nat_of_integer (Big_int.big_int_of_int 3))
                             then [Chara (true, true, false, false, true, true,
   false, false)]
                             else (if equal_nata n
(nat_of_integer (Big_int.big_int_of_int 4))
                                    then [Chara
    (false, false, true, false, true, true, false, false)]
                                    else (if equal_nata n
       (nat_of_integer (Big_int.big_int_of_int 5))
   then [Chara (true, false, true, false, true, true, false, false)]
   else (if equal_nata n (nat_of_integer (Big_int.big_int_of_int 6))
          then [Chara (false, true, true, false, true, true, false, false)]
          else (if equal_nata n (nat_of_integer (Big_int.big_int_of_int 7))
                 then [Chara (true, true, true, false, true, true, false,
                               false)]
                 else (if equal_nata n
                            (nat_of_integer (Big_int.big_int_of_int 8))
                        then [Chara (false, false, false, true, true, true,
                                      false, false)]
                        else [Chara (true, false, false, true, true, true,
                                      false, false)])))))))));;

let rec less_nat
  m n = Big_int.lt_big_int (integer_of_nat m) (integer_of_nat n);;

let rec shows_string x = (fun a -> x @ a);;

let rec showsp_nat
  p n = (if less_nat n (nat_of_integer (Big_int.big_int_of_int 10))
          then shows_string (string_of_digit n)
          else comp (showsp_nat p
                      (divide_nat n
                        (nat_of_integer (Big_int.big_int_of_int 10))))
                 (shows_string
                   (string_of_digit
                     (modulo_nat n
                       (nat_of_integer (Big_int.big_int_of_int 10))))));;

let rec less_int
  k l = Big_int.lt_big_int (integer_of_int k) (integer_of_int l);;

let rec nat k = Nat (max ord_integer Big_int.zero_big_int (integer_of_int k));;

let rec showsp_int
  p i = (if less_int i zero_inta
          then comp (shows_string
                      [Chara (true, false, true, true, false, true, false,
                               false)])
                 (showsp_nat p (nat (uminus_inta i)))
          else showsp_nat p (nat i));;

let rec shows_prec_int x = showsp_int x;;

let rec shows_sep
  s sep x2 = match s, sep, x2 with s, sep, [] -> shows_string []
    | s, sep, [x] -> s x
    | s, sep, x :: v :: va ->
        comp (comp (s x) sep) (shows_sep s sep (v :: va));;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec shows_list_gen
  showsx e l s r xs =
    (if null xs then shows_string e
      else comp (comp (shows_string l) (shows_sep showsx (shows_string s) xs))
             (shows_string r));;

let rec showsp_list
  s p xs =
    shows_list_gen (s zero_nata)
      [Chara (true, true, false, true, true, false, true, false);
        Chara (true, false, true, true, true, false, true, false)]
      [Chara (true, true, false, true, true, false, true, false)]
      [Chara (false, false, true, true, false, true, false, false);
        Chara (false, false, false, false, false, true, false, false)]
      [Chara (true, false, true, true, true, false, true, false)] xs;;

let rec shows_list_int x = showsp_list shows_prec_int zero_nata x;;

type 'a show =
  {shows_prec : nat -> 'a -> char list -> char list;
    shows_list : 'a list -> char list -> char list};;
let shows_prec _A = _A.shows_prec;;
let shows_list _A = _A.shows_list;;

let show_int =
  ({shows_prec = shows_prec_int; shows_list = shows_list_int} : int show);;

let rec plus_inta
  k l = Int_of_integer
          (Big_int.add_big_int (integer_of_int k) (integer_of_int l));;

type 'a plus = {plus : 'a -> 'a -> 'a};;
let plus _A = _A.plus;;

let plus_int = ({plus = plus_inta} : int plus);;

type 'a zero = {zero : 'a};;
let zero _A = _A.zero;;

let zero_int = ({zero = zero_inta} : int zero);;

let rec minus_inta
  k l = Int_of_integer
          (Big_int.sub_big_int (integer_of_int k) (integer_of_int l));;

type 'a minus = {minus : 'a -> 'a -> 'a};;
let minus _A = _A.minus;;

let minus_int = ({minus = minus_inta} : int minus);;

type 'a uminus = {uminus : 'a -> 'a};;
let uminus _A = _A.uminus;;

let uminus_int = ({uminus = uminus_inta} : int uminus);;

let rec less_eq_int
  k l = Big_int.le_big_int (integer_of_int k) (integer_of_int l);;

let ord_int = ({less_eq = less_eq_int; less = less_int} : int ord);;

type 'a preorder = {ord_preorder : 'a ord};;

type 'a order = {preorder_order : 'a preorder};;

let preorder_int = ({ord_preorder = ord_int} : int preorder);;

let order_int = ({preorder_order = preorder_int} : int order);;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};;

type 'a cancel_semigroup_add =
  {semigroup_add_cancel_semigroup_add : 'a semigroup_add};;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add; zero_monoid_add : 'a zero};;

type 'a group_add =
  {cancel_semigroup_add_group_add : 'a cancel_semigroup_add;
    minus_group_add : 'a minus; monoid_add_group_add : 'a monoid_add;
    uminus_group_add : 'a uminus};;

let semigroup_add_int = ({plus_semigroup_add = plus_int} : int semigroup_add);;

let cancel_semigroup_add_int =
  ({semigroup_add_cancel_semigroup_add = semigroup_add_int} :
    int cancel_semigroup_add);;

let monoid_add_int =
  ({semigroup_add_monoid_add = semigroup_add_int; zero_monoid_add = zero_int} :
    int monoid_add);;

let group_add_int =
  ({cancel_semigroup_add_group_add = cancel_semigroup_add_int;
     minus_group_add = minus_int; monoid_add_group_add = monoid_add_int;
     uminus_group_add = uminus_int}
    : int group_add);;

let rec def_hashmap_size_int
  x = (fun _ -> nat_of_integer (Big_int.big_int_of_int 16)) x;;

type 'a hashable =
  {hashcode : 'a -> int32; def_hashmap_size : 'a itself -> nat};;
let hashcode _A = _A.hashcode;;
let def_hashmap_size _A = _A.def_hashmap_size;;

let rec test_bit_integer x n = Bits_Integer.test_bit x (integer_of_nat n);;

let rec bitNOT_integer
  i = Big_int.sub_big_int (Big_int.minus_big_int i) (Big_int.big_int_of_int 1);;

let rec bitAND_integer
  i j = (if Big_int.le_big_int Big_int.zero_big_int i
          then (if Big_int.le_big_int Big_int.zero_big_int j
                 then Big_int.and_big_int i j
                 else Bits_Integer.and_pninteger i j)
          else (if Big_int.lt_big_int j Big_int.zero_big_int
                 then bitNOT_integer
                        (Big_int.or_big_int (bitNOT_integer i)
                          (bitNOT_integer j))
                 else Bits_Integer.and_pninteger j i));;

let rec uint32
  i = (let ia = bitAND_integer i (Big_int.big_int_of_string "4294967295") in
        (if test_bit_integer ia (nat_of_integer (Big_int.big_int_of_int 31))
          then Big_int.int32_of_big_int
                 (Big_int.sub_big_int ia
                   (Big_int.big_int_of_string "4294967296"))
          else Big_int.int32_of_big_int ia));;

let rec uint32_of_int i = uint32 (integer_of_int i);;

let rec hashcode_int i = uint32_of_int i;;

let hashable_int =
  ({hashcode = hashcode_int; def_hashmap_size = def_hashmap_size_int} :
    int hashable);;

type 'a linorder = {order_linorder : 'a order};;

let linorder_int = ({order_linorder = order_int} : int linorder);;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};;

type 'a cancel_ab_semigroup_add =
  {ab_semigroup_add_cancel_ab_semigroup_add : 'a ab_semigroup_add;
    cancel_semigroup_add_cancel_ab_semigroup_add : 'a cancel_semigroup_add;
    minus_cancel_ab_semigroup_add : 'a minus};;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add;
    monoid_add_comm_monoid_add : 'a monoid_add};;

type 'a cancel_comm_monoid_add =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add : 'a cancel_ab_semigroup_add;
    comm_monoid_add_cancel_comm_monoid_add : 'a comm_monoid_add};;

type 'a ab_group_add =
  {cancel_comm_monoid_add_ab_group_add : 'a cancel_comm_monoid_add;
    group_add_ab_group_add : 'a group_add};;

let ab_semigroup_add_int =
  ({semigroup_add_ab_semigroup_add = semigroup_add_int} :
    int ab_semigroup_add);;

let cancel_ab_semigroup_add_int =
  ({ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_int;
     cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_int;
     minus_cancel_ab_semigroup_add = minus_int}
    : int cancel_ab_semigroup_add);;

let comm_monoid_add_int =
  ({ab_semigroup_add_comm_monoid_add = ab_semigroup_add_int;
     monoid_add_comm_monoid_add = monoid_add_int}
    : int comm_monoid_add);;

let cancel_comm_monoid_add_int =
  ({cancel_ab_semigroup_add_cancel_comm_monoid_add =
      cancel_ab_semigroup_add_int;
     comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_int}
    : int cancel_comm_monoid_add);;

let ab_group_add_int =
  ({cancel_comm_monoid_add_ab_group_add = cancel_comm_monoid_add_int;
     group_add_ab_group_add = group_add_int}
    : int ab_group_add);;

type 'a ordered_ab_semigroup_add =
  {ab_semigroup_add_ordered_ab_semigroup_add : 'a ab_semigroup_add;
    order_ordered_ab_semigroup_add : 'a order};;

type 'a strict_ordered_ab_semigroup_add =
  {ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add :
     'a ordered_ab_semigroup_add};;

type 'a ordered_cancel_ab_semigroup_add =
  {cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
     'a cancel_ab_semigroup_add;
    strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
      'a strict_ordered_ab_semigroup_add};;

type 'a ordered_ab_semigroup_add_imp_le =
  {ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le :
     'a ordered_cancel_ab_semigroup_add};;

type 'a strict_ordered_comm_monoid_add =
  {comm_monoid_add_strict_ordered_comm_monoid_add : 'a comm_monoid_add;
    strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add :
      'a strict_ordered_ab_semigroup_add};;

type 'a ordered_comm_monoid_add =
  {comm_monoid_add_ordered_comm_monoid_add : 'a comm_monoid_add;
    ordered_ab_semigroup_add_ordered_comm_monoid_add :
      'a ordered_ab_semigroup_add};;

type 'a ordered_cancel_comm_monoid_add =
  {ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add :
     'a ordered_cancel_ab_semigroup_add;
    ordered_comm_monoid_add_ordered_cancel_comm_monoid_add :
      'a ordered_comm_monoid_add;
    strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add :
      'a strict_ordered_comm_monoid_add};;

type 'a ordered_ab_semigroup_monoid_add_imp_le =
  {cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le :
     'a cancel_comm_monoid_add;
    ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le :
      'a ordered_ab_semigroup_add_imp_le;
    ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le :
      'a ordered_cancel_comm_monoid_add};;

type 'a ordered_ab_group_add =
  {ab_group_add_ordered_ab_group_add : 'a ab_group_add;
    ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add :
      'a ordered_ab_semigroup_monoid_add_imp_le};;

let ordered_ab_semigroup_add_int =
  ({ab_semigroup_add_ordered_ab_semigroup_add = ab_semigroup_add_int;
     order_ordered_ab_semigroup_add = order_int}
    : int ordered_ab_semigroup_add);;

let strict_ordered_ab_semigroup_add_int =
  ({ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add =
      ordered_ab_semigroup_add_int}
    : int strict_ordered_ab_semigroup_add);;

let ordered_cancel_ab_semigroup_add_int =
  ({cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
      cancel_ab_semigroup_add_int;
     strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
       strict_ordered_ab_semigroup_add_int}
    : int ordered_cancel_ab_semigroup_add);;

let ordered_ab_semigroup_add_imp_le_int =
  ({ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le =
      ordered_cancel_ab_semigroup_add_int}
    : int ordered_ab_semigroup_add_imp_le);;

let strict_ordered_comm_monoid_add_int =
  ({comm_monoid_add_strict_ordered_comm_monoid_add = comm_monoid_add_int;
     strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add =
       strict_ordered_ab_semigroup_add_int}
    : int strict_ordered_comm_monoid_add);;

let ordered_comm_monoid_add_int =
  ({comm_monoid_add_ordered_comm_monoid_add = comm_monoid_add_int;
     ordered_ab_semigroup_add_ordered_comm_monoid_add =
       ordered_ab_semigroup_add_int}
    : int ordered_comm_monoid_add);;

let ordered_cancel_comm_monoid_add_int =
  ({ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add =
      ordered_cancel_ab_semigroup_add_int;
     ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
       ordered_comm_monoid_add_int;
     strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
       strict_ordered_comm_monoid_add_int}
    : int ordered_cancel_comm_monoid_add);;

let ordered_ab_semigroup_monoid_add_imp_le_int =
  ({cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
      cancel_comm_monoid_add_int;
     ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le =
       ordered_ab_semigroup_add_imp_le_int;
     ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
       ordered_cancel_comm_monoid_add_int}
    : int ordered_ab_semigroup_monoid_add_imp_le);;

let ordered_ab_group_add_int =
  ({ab_group_add_ordered_ab_group_add = ab_group_add_int;
     ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add =
       ordered_ab_semigroup_monoid_add_imp_le_int}
    : int ordered_ab_group_add);;

type 'a linordered_ab_semigroup_add =
  {ordered_ab_semigroup_add_linordered_ab_semigroup_add :
     'a ordered_ab_semigroup_add;
    linorder_linordered_ab_semigroup_add : 'a linorder};;

type 'a linordered_cancel_ab_semigroup_add =
  {linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add :
     'a linordered_ab_semigroup_add;
    ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add :
      'a ordered_ab_semigroup_add_imp_le};;

type 'a linordered_ab_monoid_add =
  {linordered_ab_semigroup_add_linordered_ab_monoid_add :
     'a linordered_ab_semigroup_add;
    ordered_comm_monoid_add_linordered_ab_monoid_add :
      'a ordered_comm_monoid_add};;

type 'a linordered_cancel_ab_monoid_add =
  {linordered_ab_monoid_add_linordered_cancel_ab_monoid_add :
     'a linordered_ab_monoid_add;
    linordered_cancel_ab_semigroup_add_linordered_cancel_ab_monoid_add :
      'a linordered_cancel_ab_semigroup_add};;

type 'a linordered_ab_group_add =
  {linordered_cancel_ab_monoid_add_linordered_ab_group_add :
     'a linordered_cancel_ab_monoid_add;
    ordered_ab_group_add_linordered_ab_group_add : 'a ordered_ab_group_add};;

let linordered_ab_semigroup_add_int =
  ({ordered_ab_semigroup_add_linordered_ab_semigroup_add =
      ordered_ab_semigroup_add_int;
     linorder_linordered_ab_semigroup_add = linorder_int}
    : int linordered_ab_semigroup_add);;

let linordered_cancel_ab_semigroup_add_int =
  ({linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add =
      linordered_ab_semigroup_add_int;
     ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add =
       ordered_ab_semigroup_add_imp_le_int}
    : int linordered_cancel_ab_semigroup_add);;

let linordered_ab_monoid_add_int =
  ({linordered_ab_semigroup_add_linordered_ab_monoid_add =
      linordered_ab_semigroup_add_int;
     ordered_comm_monoid_add_linordered_ab_monoid_add =
       ordered_comm_monoid_add_int}
    : int linordered_ab_monoid_add);;

let linordered_cancel_ab_monoid_add_int =
  ({linordered_ab_monoid_add_linordered_cancel_ab_monoid_add =
      linordered_ab_monoid_add_int;
     linordered_cancel_ab_semigroup_add_linordered_cancel_ab_monoid_add =
       linordered_cancel_ab_semigroup_add_int}
    : int linordered_cancel_ab_monoid_add);;

let linordered_ab_group_add_int =
  ({linordered_cancel_ab_monoid_add_linordered_ab_group_add =
      linordered_cancel_ab_monoid_add_int;
     ordered_ab_group_add_linordered_ab_group_add = ordered_ab_group_add_int}
    : int linordered_ab_group_add);;

let equal_nat = ({equal = equal_nata} : nat equal);;

let rec typerep_nata t = Typerep ("Nat.nat", []);;

let countable_nat = (() : nat countable);;

let typerep_nat = ({typerep = typerep_nata} : nat typerep);;

let heap_nat =
  ({countable_heap = countable_nat; typerep_heap = typerep_nat} : nat heap);;

let rec shows_prec_nat x = showsp_nat x;;

let rec shows_list_nat x = showsp_list shows_prec_nat zero_nata x;;

let show_nat =
  ({shows_prec = shows_prec_nat; shows_list = shows_list_nat} : nat show);;

type 'a one = {one : 'a};;
let one _A = _A.one;;

let one_nat = ({one = one_nata} : nat one);;

let rec plus_nata
  m n = Nat (Big_int.add_big_int (integer_of_nat m) (integer_of_nat n));;

let plus_nat = ({plus = plus_nata} : nat plus);;

let zero_nat = ({zero = zero_nata} : nat zero);;

let rec less_eq_nat
  m n = Big_int.le_big_int (integer_of_nat m) (integer_of_nat n);;

let ord_nat = ({less_eq = less_eq_nat; less = less_nat} : nat ord);;

let rec sup_nata x = max ord_nat x;;

type 'a sup = {sup : 'a -> 'a -> 'a};;
let sup _A = _A.sup;;

let sup_nat = ({sup = sup_nata} : nat sup);;

let preorder_nat = ({ord_preorder = ord_nat} : nat preorder);;

let order_nat = ({preorder_order = preorder_nat} : nat order);;

let rec def_hashmap_size_nat
  x = (fun _ -> nat_of_integer (Big_int.big_int_of_int 16)) x;;

let rec int_of_nat n = Int_of_integer (integer_of_nat n);;

let rec hashcode_nat n = uint32_of_int (int_of_nat n);;

let hashable_nat =
  ({hashcode = hashcode_nat; def_hashmap_size = def_hashmap_size_nat} :
    nat hashable);;

let linorder_nat = ({order_linorder = order_nat} : nat linorder);;

type ('a, 'b) phantom = Phantom of 'b;;

let finite_UNIV_nata : (nat, bool) phantom = Phantom false;;

let card_UNIV_nata : (nat, nat) phantom = Phantom zero_nata;;

type 'a finite_UNIV = {finite_UNIV : ('a, bool) phantom};;
let finite_UNIV _A = _A.finite_UNIV;;

type 'a card_UNIV =
  {finite_UNIV_card_UNIV : 'a finite_UNIV; card_UNIV : ('a, nat) phantom};;
let card_UNIV _A = _A.card_UNIV;;

let finite_UNIV_nat = ({finite_UNIV = finite_UNIV_nata} : nat finite_UNIV);;

let card_UNIV_nat =
  ({finite_UNIV_card_UNIV = finite_UNIV_nat; card_UNIV = card_UNIV_nata} :
    nat card_UNIV);;

let rec eq _A a b = equal _A a b;;

let rec equal_lista _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> eq _A x21 y21 && equal_lista _A x22 y22
    | [], [] -> true;;

let rec equal_list _A = ({equal = equal_lista _A} : ('a list) equal);;

let rec typerep_lista _A t = Typerep ("List.list", [typerep _A Type]);;

let rec countable_list _A = (() : ('a list) countable);;

let rec typerep_list _A = ({typerep = typerep_lista _A} : ('a list) typerep);;

let rec heap_list _A =
  ({countable_heap = (countable_list _A.countable_heap);
     typerep_heap = (typerep_list _A.typerep_heap)}
    : ('a list) heap);;

let rec shows_prec_list _A p xs = shows_list _A xs;;

let rec shows_list_list _A
  xss = showsp_list (shows_prec_list _A) zero_nata xss;;

let rec show_list _A =
  ({shows_prec = shows_prec_list _A; shows_list = shows_list_list _A} :
    ('a list) show);;

let rec times_nat
  m n = Nat (Big_int.mult_big_int (integer_of_nat m) (integer_of_nat n));;

let rec def_hashmap_size_list _A
  = (fun _ ->
      times_nat (nat_of_integer (Big_int.big_int_of_int 2))
        (def_hashmap_size _A Type));;

let rec foldl f a x2 = match f, a, x2 with f, a, [] -> a
                | f, a, x :: xs -> foldl f (f a x) xs;;

let rec hashcode_list _A
  = foldl (fun h x ->
            Int32.add (Int32.mul h (uint32 (Big_int.big_int_of_int 33)))
              (hashcode _A x))
      (uint32 (Big_int.big_int_of_int 5381));;

let rec hashable_list _A =
  ({hashcode = hashcode_list _A; def_hashmap_size = def_hashmap_size_list _A} :
    ('a list) hashable);;

let rec typerep_arraya _A t = Typerep ("Heap.array", [typerep _A Type]);;

let countable_array = (() : ('a array) countable);;

let rec typerep_array _A =
  ({typerep = typerep_arraya _A} : ('a array) typerep);;

let rec heap_array _A =
  ({countable_heap = countable_array; typerep_heap = (typerep_array _A)} :
    ('a array) heap);;

type 'a dBMEntry = Le of 'a | Lt of 'a | INF;;

let rec typerep_DBMEntrya _A t = Typerep ("DBM.DBMEntry", [typerep _A Type]);;

let rec countable_DBMEntry _A = (() : 'a dBMEntry countable);;

let rec typerep_DBMEntry _A =
  ({typerep = typerep_DBMEntrya _A} : 'a dBMEntry typerep);;

let rec heap_DBMEntry _A =
  ({countable_heap = (countable_DBMEntry _A.countable_heap);
     typerep_heap = (typerep_DBMEntry _A.typerep_heap)}
    : 'a dBMEntry heap);;

let rec dbm_add _A
  x0 uu = match x0, uu with INF, uu -> INF
    | Le v, INF -> INF
    | Lt v, INF -> INF
    | Le a, Le b ->
        Le (plus _A.ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add.ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le.cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add.ab_semigroup_add_cancel_ab_semigroup_add.semigroup_add_ab_semigroup_add.plus_semigroup_add
             a b)
    | Le a, Lt b ->
        Lt (plus _A.ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add.ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le.cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add.ab_semigroup_add_cancel_ab_semigroup_add.semigroup_add_ab_semigroup_add.plus_semigroup_add
             a b)
    | Lt a, Le b ->
        Lt (plus _A.ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add.ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le.cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add.ab_semigroup_add_cancel_ab_semigroup_add.semigroup_add_ab_semigroup_add.plus_semigroup_add
             a b)
    | Lt a, Lt b ->
        Lt (plus _A.ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add.ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le.cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add.ab_semigroup_add_cancel_ab_semigroup_add.semigroup_add_ab_semigroup_add.plus_semigroup_add
             a b);;

let rec plus_DBMEntrya _A
  = dbm_add
      _A.linordered_cancel_ab_semigroup_add_linordered_cancel_ab_monoid_add;;

let rec plus_DBMEntry _A = ({plus = plus_DBMEntrya _A} : 'a dBMEntry plus);;

let rec zero_DBMEntrya _A = Le (zero _A);;

let rec zero_DBMEntry _A = ({zero = zero_DBMEntrya _A} : 'a dBMEntry zero);;

let rec equal_DBMEntry _A x0 x1 = match x0, x1 with Lt x2, INF -> false
                            | INF, Lt x2 -> false
                            | Le x1, INF -> false
                            | INF, Le x1 -> false
                            | Le x1, Lt x2 -> false
                            | Lt x2, Le x1 -> false
                            | Lt x2, Lt y2 -> eq _A x2 y2
                            | Le x1, Le y1 -> eq _A x1 y1
                            | INF, INF -> true;;

let rec dbm_lt _A
  xa0 x = match xa0, x with INF, x -> false
    | Lt a, Lt b -> less _A.order_linorder.preorder_order.ord_preorder a b
    | Lt a, Le b -> less_eq _A.order_linorder.preorder_order.ord_preorder a b
    | Le a, Lt b -> less _A.order_linorder.preorder_order.ord_preorder a b
    | Le a, Le b -> less _A.order_linorder.preorder_order.ord_preorder a b
    | Le a, INF -> true
    | Lt a, INF -> true;;

let rec dbm_le (_A1, _A2) a b = equal_DBMEntry _A1 a b || dbm_lt _A2 a b;;

let rec less_eq_DBMEntry (_A1, _A2) = dbm_le (_A1, _A2);;

let rec less_DBMEntry _A = dbm_lt _A;;

let rec ord_DBMEntry (_A1, _A2) =
  ({less_eq = less_eq_DBMEntry (_A1, _A2); less = less_DBMEntry _A2} :
    'a dBMEntry ord);;

let rec preorder_DBMEntry (_A1, _A2) =
  ({ord_preorder = (ord_DBMEntry (_A1, _A2))} : 'a dBMEntry preorder);;

let rec order_DBMEntry (_A1, _A2) =
  ({preorder_order = (preorder_DBMEntry (_A1, _A2))} : 'a dBMEntry order);;

let rec semigroup_add_DBMEntry _A =
  ({plus_semigroup_add = (plus_DBMEntry _A)} : 'a dBMEntry semigroup_add);;

let rec monoid_add_DBMEntry _A =
  ({semigroup_add_monoid_add = (semigroup_add_DBMEntry _A);
     zero_monoid_add =
       (zero_DBMEntry
         _A.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.ordered_comm_monoid_add_linordered_ab_monoid_add.comm_monoid_add_ordered_comm_monoid_add.monoid_add_comm_monoid_add.zero_monoid_add)}
    : 'a dBMEntry monoid_add);;

let rec linorder_DBMEntry (_A1, _A2) =
  ({order_linorder = (order_DBMEntry (_A1, _A2))} : 'a dBMEntry linorder);;

let rec ab_semigroup_add_DBMEntry _A =
  ({semigroup_add_ab_semigroup_add = (semigroup_add_DBMEntry _A)} :
    'a dBMEntry ab_semigroup_add);;

let rec comm_monoid_add_DBMEntry _A =
  ({ab_semigroup_add_comm_monoid_add = (ab_semigroup_add_DBMEntry _A);
     monoid_add_comm_monoid_add = (monoid_add_DBMEntry _A)}
    : 'a dBMEntry comm_monoid_add);;

let rec ordered_ab_semigroup_add_DBMEntry (_A1, _A2) =
  ({ab_semigroup_add_ordered_ab_semigroup_add = (ab_semigroup_add_DBMEntry _A1);
     order_ordered_ab_semigroup_add =
       (order_DBMEntry
         (_A2, _A1.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.linordered_ab_semigroup_add_linordered_ab_monoid_add.linorder_linordered_ab_semigroup_add))}
    : 'a dBMEntry ordered_ab_semigroup_add);;

let rec ordered_comm_monoid_add_DBMEntry (_A1, _A2) =
  ({comm_monoid_add_ordered_comm_monoid_add = (comm_monoid_add_DBMEntry _A1);
     ordered_ab_semigroup_add_ordered_comm_monoid_add =
       (ordered_ab_semigroup_add_DBMEntry (_A1, _A2))}
    : 'a dBMEntry ordered_comm_monoid_add);;

let rec linordered_ab_semigroup_add_DBMEntry (_A1, _A2) =
  ({ordered_ab_semigroup_add_linordered_ab_semigroup_add =
      (ordered_ab_semigroup_add_DBMEntry (_A1, _A2));
     linorder_linordered_ab_semigroup_add =
       (linorder_DBMEntry
         (_A2, _A1.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.linordered_ab_semigroup_add_linordered_ab_monoid_add.linorder_linordered_ab_semigroup_add))}
    : 'a dBMEntry linordered_ab_semigroup_add);;

let rec linordered_ab_monoid_add_DBMEntry (_A1, _A2) =
  ({linordered_ab_semigroup_add_linordered_ab_monoid_add =
      (linordered_ab_semigroup_add_DBMEntry (_A1, _A2));
     ordered_comm_monoid_add_linordered_ab_monoid_add =
       (ordered_comm_monoid_add_DBMEntry (_A1, _A2))}
    : 'a dBMEntry linordered_ab_monoid_add);;

let rec equal_optiona _A x0 x1 = match x0, x1 with None, Some x2 -> false
                           | Some x2, None -> false
                           | Some x2, Some y2 -> eq _A x2 y2
                           | None, None -> true;;

let rec equal_option _A = ({equal = equal_optiona _A} : ('a option) equal);;

let rec equal_bool p pa = match p, pa with p, true -> p
                     | p, false -> not p
                     | true, p -> p
                     | false, p -> not p;;

type instr = JMPZ of nat | ADD | NOT | AND | LT | LE | EQ | PUSH of int | POP |
  LID of nat | STORE | STOREI of nat * int | COPY | CALL | RETURN | HALT |
  STOREC of nat * int | SETF of bool;;

let rec equal_instra
  x0 x1 = match x0, x1 with STOREC (x171, x172), SETF x18 -> false
    | SETF x18, STOREC (x171, x172) -> false
    | HALT, SETF x18 -> false
    | SETF x18, HALT -> false
    | HALT, STOREC (x171, x172) -> false
    | STOREC (x171, x172), HALT -> false
    | RETURN, SETF x18 -> false
    | SETF x18, RETURN -> false
    | RETURN, STOREC (x171, x172) -> false
    | STOREC (x171, x172), RETURN -> false
    | RETURN, HALT -> false
    | HALT, RETURN -> false
    | CALL, SETF x18 -> false
    | SETF x18, CALL -> false
    | CALL, STOREC (x171, x172) -> false
    | STOREC (x171, x172), CALL -> false
    | CALL, HALT -> false
    | HALT, CALL -> false
    | CALL, RETURN -> false
    | RETURN, CALL -> false
    | COPY, SETF x18 -> false
    | SETF x18, COPY -> false
    | COPY, STOREC (x171, x172) -> false
    | STOREC (x171, x172), COPY -> false
    | COPY, HALT -> false
    | HALT, COPY -> false
    | COPY, RETURN -> false
    | RETURN, COPY -> false
    | COPY, CALL -> false
    | CALL, COPY -> false
    | STOREI (x121, x122), SETF x18 -> false
    | SETF x18, STOREI (x121, x122) -> false
    | STOREI (x121, x122), STOREC (x171, x172) -> false
    | STOREC (x171, x172), STOREI (x121, x122) -> false
    | STOREI (x121, x122), HALT -> false
    | HALT, STOREI (x121, x122) -> false
    | STOREI (x121, x122), RETURN -> false
    | RETURN, STOREI (x121, x122) -> false
    | STOREI (x121, x122), CALL -> false
    | CALL, STOREI (x121, x122) -> false
    | STOREI (x121, x122), COPY -> false
    | COPY, STOREI (x121, x122) -> false
    | STORE, SETF x18 -> false
    | SETF x18, STORE -> false
    | STORE, STOREC (x171, x172) -> false
    | STOREC (x171, x172), STORE -> false
    | STORE, HALT -> false
    | HALT, STORE -> false
    | STORE, RETURN -> false
    | RETURN, STORE -> false
    | STORE, CALL -> false
    | CALL, STORE -> false
    | STORE, COPY -> false
    | COPY, STORE -> false
    | STORE, STOREI (x121, x122) -> false
    | STOREI (x121, x122), STORE -> false
    | LID x10, SETF x18 -> false
    | SETF x18, LID x10 -> false
    | LID x10, STOREC (x171, x172) -> false
    | STOREC (x171, x172), LID x10 -> false
    | LID x10, HALT -> false
    | HALT, LID x10 -> false
    | LID x10, RETURN -> false
    | RETURN, LID x10 -> false
    | LID x10, CALL -> false
    | CALL, LID x10 -> false
    | LID x10, COPY -> false
    | COPY, LID x10 -> false
    | LID x10, STOREI (x121, x122) -> false
    | STOREI (x121, x122), LID x10 -> false
    | LID x10, STORE -> false
    | STORE, LID x10 -> false
    | POP, SETF x18 -> false
    | SETF x18, POP -> false
    | POP, STOREC (x171, x172) -> false
    | STOREC (x171, x172), POP -> false
    | POP, HALT -> false
    | HALT, POP -> false
    | POP, RETURN -> false
    | RETURN, POP -> false
    | POP, CALL -> false
    | CALL, POP -> false
    | POP, COPY -> false
    | COPY, POP -> false
    | POP, STOREI (x121, x122) -> false
    | STOREI (x121, x122), POP -> false
    | POP, STORE -> false
    | STORE, POP -> false
    | POP, LID x10 -> false
    | LID x10, POP -> false
    | PUSH x8, SETF x18 -> false
    | SETF x18, PUSH x8 -> false
    | PUSH x8, STOREC (x171, x172) -> false
    | STOREC (x171, x172), PUSH x8 -> false
    | PUSH x8, HALT -> false
    | HALT, PUSH x8 -> false
    | PUSH x8, RETURN -> false
    | RETURN, PUSH x8 -> false
    | PUSH x8, CALL -> false
    | CALL, PUSH x8 -> false
    | PUSH x8, COPY -> false
    | COPY, PUSH x8 -> false
    | PUSH x8, STOREI (x121, x122) -> false
    | STOREI (x121, x122), PUSH x8 -> false
    | PUSH x8, STORE -> false
    | STORE, PUSH x8 -> false
    | PUSH x8, LID x10 -> false
    | LID x10, PUSH x8 -> false
    | PUSH x8, POP -> false
    | POP, PUSH x8 -> false
    | EQ, SETF x18 -> false
    | SETF x18, EQ -> false
    | EQ, STOREC (x171, x172) -> false
    | STOREC (x171, x172), EQ -> false
    | EQ, HALT -> false
    | HALT, EQ -> false
    | EQ, RETURN -> false
    | RETURN, EQ -> false
    | EQ, CALL -> false
    | CALL, EQ -> false
    | EQ, COPY -> false
    | COPY, EQ -> false
    | EQ, STOREI (x121, x122) -> false
    | STOREI (x121, x122), EQ -> false
    | EQ, STORE -> false
    | STORE, EQ -> false
    | EQ, LID x10 -> false
    | LID x10, EQ -> false
    | EQ, POP -> false
    | POP, EQ -> false
    | EQ, PUSH x8 -> false
    | PUSH x8, EQ -> false
    | LE, SETF x18 -> false
    | SETF x18, LE -> false
    | LE, STOREC (x171, x172) -> false
    | STOREC (x171, x172), LE -> false
    | LE, HALT -> false
    | HALT, LE -> false
    | LE, RETURN -> false
    | RETURN, LE -> false
    | LE, CALL -> false
    | CALL, LE -> false
    | LE, COPY -> false
    | COPY, LE -> false
    | LE, STOREI (x121, x122) -> false
    | STOREI (x121, x122), LE -> false
    | LE, STORE -> false
    | STORE, LE -> false
    | LE, LID x10 -> false
    | LID x10, LE -> false
    | LE, POP -> false
    | POP, LE -> false
    | LE, PUSH x8 -> false
    | PUSH x8, LE -> false
    | LE, EQ -> false
    | EQ, LE -> false
    | LT, SETF x18 -> false
    | SETF x18, LT -> false
    | LT, STOREC (x171, x172) -> false
    | STOREC (x171, x172), LT -> false
    | LT, HALT -> false
    | HALT, LT -> false
    | LT, RETURN -> false
    | RETURN, LT -> false
    | LT, CALL -> false
    | CALL, LT -> false
    | LT, COPY -> false
    | COPY, LT -> false
    | LT, STOREI (x121, x122) -> false
    | STOREI (x121, x122), LT -> false
    | LT, STORE -> false
    | STORE, LT -> false
    | LT, LID x10 -> false
    | LID x10, LT -> false
    | LT, POP -> false
    | POP, LT -> false
    | LT, PUSH x8 -> false
    | PUSH x8, LT -> false
    | LT, EQ -> false
    | EQ, LT -> false
    | LT, LE -> false
    | LE, LT -> false
    | AND, SETF x18 -> false
    | SETF x18, AND -> false
    | AND, STOREC (x171, x172) -> false
    | STOREC (x171, x172), AND -> false
    | AND, HALT -> false
    | HALT, AND -> false
    | AND, RETURN -> false
    | RETURN, AND -> false
    | AND, CALL -> false
    | CALL, AND -> false
    | AND, COPY -> false
    | COPY, AND -> false
    | AND, STOREI (x121, x122) -> false
    | STOREI (x121, x122), AND -> false
    | AND, STORE -> false
    | STORE, AND -> false
    | AND, LID x10 -> false
    | LID x10, AND -> false
    | AND, POP -> false
    | POP, AND -> false
    | AND, PUSH x8 -> false
    | PUSH x8, AND -> false
    | AND, EQ -> false
    | EQ, AND -> false
    | AND, LE -> false
    | LE, AND -> false
    | AND, LT -> false
    | LT, AND -> false
    | NOT, SETF x18 -> false
    | SETF x18, NOT -> false
    | NOT, STOREC (x171, x172) -> false
    | STOREC (x171, x172), NOT -> false
    | NOT, HALT -> false
    | HALT, NOT -> false
    | NOT, RETURN -> false
    | RETURN, NOT -> false
    | NOT, CALL -> false
    | CALL, NOT -> false
    | NOT, COPY -> false
    | COPY, NOT -> false
    | NOT, STOREI (x121, x122) -> false
    | STOREI (x121, x122), NOT -> false
    | NOT, STORE -> false
    | STORE, NOT -> false
    | NOT, LID x10 -> false
    | LID x10, NOT -> false
    | NOT, POP -> false
    | POP, NOT -> false
    | NOT, PUSH x8 -> false
    | PUSH x8, NOT -> false
    | NOT, EQ -> false
    | EQ, NOT -> false
    | NOT, LE -> false
    | LE, NOT -> false
    | NOT, LT -> false
    | LT, NOT -> false
    | NOT, AND -> false
    | AND, NOT -> false
    | ADD, SETF x18 -> false
    | SETF x18, ADD -> false
    | ADD, STOREC (x171, x172) -> false
    | STOREC (x171, x172), ADD -> false
    | ADD, HALT -> false
    | HALT, ADD -> false
    | ADD, RETURN -> false
    | RETURN, ADD -> false
    | ADD, CALL -> false
    | CALL, ADD -> false
    | ADD, COPY -> false
    | COPY, ADD -> false
    | ADD, STOREI (x121, x122) -> false
    | STOREI (x121, x122), ADD -> false
    | ADD, STORE -> false
    | STORE, ADD -> false
    | ADD, LID x10 -> false
    | LID x10, ADD -> false
    | ADD, POP -> false
    | POP, ADD -> false
    | ADD, PUSH x8 -> false
    | PUSH x8, ADD -> false
    | ADD, EQ -> false
    | EQ, ADD -> false
    | ADD, LE -> false
    | LE, ADD -> false
    | ADD, LT -> false
    | LT, ADD -> false
    | ADD, AND -> false
    | AND, ADD -> false
    | ADD, NOT -> false
    | NOT, ADD -> false
    | JMPZ x1, SETF x18 -> false
    | SETF x18, JMPZ x1 -> false
    | JMPZ x1, STOREC (x171, x172) -> false
    | STOREC (x171, x172), JMPZ x1 -> false
    | JMPZ x1, HALT -> false
    | HALT, JMPZ x1 -> false
    | JMPZ x1, RETURN -> false
    | RETURN, JMPZ x1 -> false
    | JMPZ x1, CALL -> false
    | CALL, JMPZ x1 -> false
    | JMPZ x1, COPY -> false
    | COPY, JMPZ x1 -> false
    | JMPZ x1, STOREI (x121, x122) -> false
    | STOREI (x121, x122), JMPZ x1 -> false
    | JMPZ x1, STORE -> false
    | STORE, JMPZ x1 -> false
    | JMPZ x1, LID x10 -> false
    | LID x10, JMPZ x1 -> false
    | JMPZ x1, POP -> false
    | POP, JMPZ x1 -> false
    | JMPZ x1, PUSH x8 -> false
    | PUSH x8, JMPZ x1 -> false
    | JMPZ x1, EQ -> false
    | EQ, JMPZ x1 -> false
    | JMPZ x1, LE -> false
    | LE, JMPZ x1 -> false
    | JMPZ x1, LT -> false
    | LT, JMPZ x1 -> false
    | JMPZ x1, AND -> false
    | AND, JMPZ x1 -> false
    | JMPZ x1, NOT -> false
    | NOT, JMPZ x1 -> false
    | JMPZ x1, ADD -> false
    | ADD, JMPZ x1 -> false
    | SETF x18, SETF y18 -> equal_bool x18 y18
    | STOREC (x171, x172), STOREC (y171, y172) ->
        equal_nata x171 y171 && equal_inta x172 y172
    | STOREI (x121, x122), STOREI (y121, y122) ->
        equal_nata x121 y121 && equal_inta x122 y122
    | LID x10, LID y10 -> equal_nata x10 y10
    | PUSH x8, PUSH y8 -> equal_inta x8 y8
    | JMPZ x1, JMPZ y1 -> equal_nata x1 y1
    | HALT, HALT -> true
    | RETURN, RETURN -> true
    | CALL, CALL -> true
    | COPY, COPY -> true
    | STORE, STORE -> true
    | POP, POP -> true
    | EQ, EQ -> true
    | LE, LE -> true
    | LT, LT -> true
    | AND, AND -> true
    | NOT, NOT -> true
    | ADD, ADD -> true;;

let equal_instr = ({equal = equal_instra} : instr equal);;

let rec equal_proda _A _B (x1, x2) (y1, y2) = eq _A x1 y1 && eq _B x2 y2;;

let rec equal_prod _A _B = ({equal = equal_proda _A _B} : ('a * 'b) equal);;

let rec typerep_proda _A _B
  t = Typerep ("Product_Type.prod", [typerep _A Type; typerep _B Type]);;

let rec countable_prod _A _B = (() : ('a * 'b) countable);;

let rec typerep_prod _A _B =
  ({typerep = typerep_proda _A _B} : ('a * 'b) typerep);;

let rec heap_prod _A _B =
  ({countable_heap = (countable_prod _A.countable_heap _B.countable_heap);
     typerep_heap = (typerep_prod _A.typerep_heap _B.typerep_heap)}
    : ('a * 'b) heap);;

let rec def_hashmap_size_prod _A _B
  = (fun _ -> plus_nata (def_hashmap_size _A Type) (def_hashmap_size _B Type));;

let rec hashcode_prod _A _B
  x = Int32.add
        (Int32.mul (hashcode _A (fst x)) (uint32 (Big_int.big_int_of_int 33)))
        (hashcode _B (snd x));;

let rec hashable_prod _A _B =
  ({hashcode = hashcode_prod _A _B;
     def_hashmap_size = def_hashmap_size_prod _A _B}
    : ('a * 'b) hashable);;

let one_integera : Big_int.big_int = (Big_int.big_int_of_int 1);;

let one_integer = ({one = one_integera} : Big_int.big_int one);;

let zero_integer = ({zero = Big_int.zero_big_int} : Big_int.big_int zero);;

type 'a zero_neq_one =
  {one_zero_neq_one : 'a one; zero_zero_neq_one : 'a zero};;

let zero_neq_one_integer =
  ({one_zero_neq_one = one_integer; zero_zero_neq_one = zero_integer} :
    Big_int.big_int zero_neq_one);;

type ('a, 'b) acconstraint = LTa of 'a * 'b | LEa of 'a * 'b | EQa of 'a * 'b |
  GT of 'a * 'b | GE of 'a * 'b;;

let rec equal_acconstrainta _A _B
  x0 x1 = match x0, x1 with GT (x41, x42), GE (x51, x52) -> false
    | GE (x51, x52), GT (x41, x42) -> false
    | EQa (x31, x32), GE (x51, x52) -> false
    | GE (x51, x52), EQa (x31, x32) -> false
    | EQa (x31, x32), GT (x41, x42) -> false
    | GT (x41, x42), EQa (x31, x32) -> false
    | LEa (x21, x22), GE (x51, x52) -> false
    | GE (x51, x52), LEa (x21, x22) -> false
    | LEa (x21, x22), GT (x41, x42) -> false
    | GT (x41, x42), LEa (x21, x22) -> false
    | LEa (x21, x22), EQa (x31, x32) -> false
    | EQa (x31, x32), LEa (x21, x22) -> false
    | LTa (x11, x12), GE (x51, x52) -> false
    | GE (x51, x52), LTa (x11, x12) -> false
    | LTa (x11, x12), GT (x41, x42) -> false
    | GT (x41, x42), LTa (x11, x12) -> false
    | LTa (x11, x12), EQa (x31, x32) -> false
    | EQa (x31, x32), LTa (x11, x12) -> false
    | LTa (x11, x12), LEa (x21, x22) -> false
    | LEa (x21, x22), LTa (x11, x12) -> false
    | GE (x51, x52), GE (y51, y52) -> eq _A x51 y51 && eq _B x52 y52
    | GT (x41, x42), GT (y41, y42) -> eq _A x41 y41 && eq _B x42 y42
    | EQa (x31, x32), EQa (y31, y32) -> eq _A x31 y31 && eq _B x32 y32
    | LEa (x21, x22), LEa (y21, y22) -> eq _A x21 y21 && eq _B x22 y22
    | LTa (x11, x12), LTa (y11, y12) -> eq _A x11 y11 && eq _B x12 y12;;

type 'a instrc = INSTR of instr | CEXP of (nat, 'a) acconstraint;;

let rec equal_instrca _A
  x0 x1 = match x0, x1 with INSTR x1, CEXP x2 -> false
    | CEXP x2, INSTR x1 -> false
    | CEXP x2, CEXP y2 -> equal_acconstrainta equal_nat _A x2 y2
    | INSTR x1, INSTR y1 -> equal_instra x1 y1;;

let rec equal_instrc _A = ({equal = equal_instrca _A} : 'a instrc equal);;

let rec equal_acconstraint _A _B =
  ({equal = equal_acconstrainta _A _B} : ('a, 'b) acconstraint equal);;

type 'a set = Set of 'a list | Coset of 'a list;;

type 'a act = In of 'a | Out of 'a | Sil of 'a;;

type 'a iarray = IArray of 'a list;;

type message = ExploredState;;

type ('a, 'b) hashtable = HashTable of (('a * 'b) list) array * nat;;

type ('a, 'b) hashmap =
  HashMap of (('a * 'b) list) FArray.IsabelleMapping.array_type * nat;;

type bexp = Not of bexp | And of bexp * bexp | Or of bexp * bexp |
  Imply of bexp * bexp | Loc of nat * nat | Eq of nat * int | Lea of nat * int |
  Lta of nat * int | Ge of nat * int | Gt of nat * int;;

type formula = EX of bexp | EG of bexp | AX of bexp | AG of bexp |
  Leadsto of bexp * bexp;;

type ('a, 'b, 'c, 'd) gen_g_impl_ext = Gen_g_impl_ext of 'a * 'b * 'c * 'd;;

let rec id x = (fun xa -> xa) x;;

let rec suc n = plus_nata n one_nata;;

let rec minus_nat
  m n = Nat (max ord_integer Big_int.zero_big_int
              (Big_int.sub_big_int (integer_of_nat m) (integer_of_nat n)));;

let rec nth
  (x :: xs) n =
    (if equal_nata n zero_nata then x else nth xs (minus_nat n one_nata));;

let rec fold f x1 s = match f, x1, s with f, x :: xs, s -> fold f xs (f x s)
               | f, [], s -> s;;

let rec rev xs = fold (fun a b -> a :: b) xs [];;

let rec upt i j = (if less_nat i j then i :: upt (suc i) j else []);;

let rec list_all p x1 = match p, x1 with p, [] -> true
                   | p, x :: xs -> p x && list_all p xs;;

let rec ball (Set xs) p = list_all p xs;;

let rec len _A
  a = (fun f_ () -> f_ (((fun () -> Big_int.big_int_of_int (Array.length a)))
        ()) ())
        (fun i -> (fun () -> (nat_of_integer i)));;

let rec newa _A
  = comp (fun a b -> (fun () -> Array.make (Big_int.int_of_big_int a) b))
      integer_of_nat;;

let rec ntha _A
  a n = (fun () -> Array.get a (Big_int.int_of_big_int (integer_of_nat n)));;

let rec upd _A
  i x a =
    (fun f_ () -> f_
      (((fun () -> Array.set a (Big_int.int_of_big_int (integer_of_nat i)) x))
      ()) ())
      (fun _ -> (fun () -> a));;

let rec maps f x1 = match f, x1 with f, [] -> []
               | f, x :: xs -> f x @ maps f xs;;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec image f (Set xs) = Set (map f xs);;

let rec make _A
  n f = (fun () -> Array.init (Big_int.int_of_big_int (integer_of_nat n))
          (fun k_ -> (comp f nat_of_integer) (Big_int.big_int_of_int k_)));;

let rec suba (IArray asa, n) = nth asa (nat_of_integer n);;

let rec sub asa n = suba (asa, integer_of_nat n);;

let rec foldr f x1 = match f, x1 with f, [] -> id
                | f, x :: xs -> comp (f x) (foldr f xs);;

let rec filtera
  p x1 = match p, x1 with p, [] -> []
    | p, x :: xs -> (if p x then x :: filtera p xs else filtera p xs);;

let rec filter p (Set xs) = Set (filtera p xs);;

let rec removeAll _A
  x xa1 = match x, xa1 with x, [] -> []
    | x, y :: xs ->
        (if eq _A x y then removeAll _A x xs else y :: removeAll _A x xs);;

let rec membera _A x0 y = match x0, y with [], y -> false
                     | x :: xs, y -> eq _A x y || membera _A xs y;;

let rec inserta _A x xs = (if membera _A xs x then xs else x :: xs);;

let rec insert _A
  x xa1 = match x, xa1 with x, Coset xs -> Coset (removeAll _A x xs)
    | x, Set xs -> Set (inserta _A x xs);;

let rec member _A
  x xa1 = match x, xa1 with x, Coset xs -> not (membera _A xs x)
    | x, Set xs -> membera _A xs x;;

let rec remove _A
  x xa1 = match x, xa1 with x, Coset xs -> Coset (inserta _A x xs)
    | x, Set xs -> Set (removeAll _A x xs);;

let rec concat xss = foldr (fun a b -> a @ b) xss [];;

let rec foldli
  x0 c f sigma = match x0, c, f, sigma with [], c, f, sigma -> sigma
    | x :: xs, c, f, sigma ->
        (if c sigma then foldli xs c f (f x sigma) else sigma);;

let rec hd (x21 :: x22) = x21;;

let rec tl = function [] -> []
             | x21 :: x22 -> x22;;

let rec remdups _A
  = function [] -> []
    | x :: xs ->
        (if membera _A xs x then remdups _A xs else x :: remdups _A xs);;

let rec trace m x = (let _ = (fun x -> Tracing.count_up ()) m in x);;

let rec replicate
  n x = (if equal_nata n zero_nata then []
          else x :: replicate (minus_nat n one_nata) x);;

let rec is_none = function Some x -> false
                  | None -> true;;

let rec print x = ();;

let rec of_bool _A = function true -> one _A.one_zero_neq_one
                     | false -> zero _A.zero_zero_neq_one;;

let rec integer_of_char
  (Chara (b0, b1, b2, b3, b4, b5, b6, b7)) =
    Big_int.add_big_int
      (Big_int.mult_big_int
        (Big_int.add_big_int
          (Big_int.mult_big_int
            (Big_int.add_big_int
              (Big_int.mult_big_int
                (Big_int.add_big_int
                  (Big_int.mult_big_int
                    (Big_int.add_big_int
                      (Big_int.mult_big_int
                        (Big_int.add_big_int
                          (Big_int.mult_big_int
                            (Big_int.add_big_int
                              (Big_int.mult_big_int
                                (of_bool zero_neq_one_integer b7)
                                (Big_int.big_int_of_int 2))
                              (of_bool zero_neq_one_integer b6))
                            (Big_int.big_int_of_int 2))
                          (of_bool zero_neq_one_integer b5))
                        (Big_int.big_int_of_int 2))
                      (of_bool zero_neq_one_integer b4))
                    (Big_int.big_int_of_int 2))
                  (of_bool zero_neq_one_integer b3))
                (Big_int.big_int_of_int 2))
              (of_bool zero_neq_one_integer b2))
            (Big_int.big_int_of_int 2))
          (of_bool zero_neq_one_integer b1))
        (Big_int.big_int_of_int 2))
      (of_bool zero_neq_one_integer b0);;

let rec implode
  cs = (let ks = (map integer_of_char
                   cs) in let res = Bytes.create (List.length ks) in let rec imp i = function | [] -> res | k :: ks ->
      let l = Big_int.int_of_big_int k in if 0 <= l && l < 128 then Bytes.set res i (Char.chr l) else failwith "Non-ASCII character in literal"; imp (i + 1) ks in imp 0 ks);;

let rec tracea x = trace ExploredState x;;

let rec blit _A
  src si dst di len =
    (fun () -> 
      Array.blit src (Big_int.to_int (integer_of_nat
                                       si)) dst (Big_int.to_int (integer_of_nat
                          di)) (Big_int.to_int (integer_of_nat len)));;

let rec v_dbm (_A1, _A2, _A3) _B
  n = (fun (i, j) ->
        (if eq _A2 i j ||
              (eq _A2 i (zero _A1) && less _A3 (zero _A1) j ||
                (less _A3 n i || less _A3 n j))
          then zero_DBMEntrya _B else INF));;

let rec imp_fora
  i u f s =
    (if less_eq_nat u i then (fun () -> s)
      else (fun f_ () -> f_ ((f i s) ()) ())
             (imp_fora (plus_nata i one_nata) u f));;

let rec mtx_set _A
  m mtx e v = upd _A (plus_nata (times_nat (fst e) m) (snd e)) v mtx;;

let rec mtx_get _A
  m mtx e = ntha _A mtx (plus_nata (times_nat (fst e) m) (snd e));;

let rec min _A a b = (if less_eq _A a b then a else b);;

let rec fw_upd_impl (_A1, _A2)
  n = (fun ai bib bia bi ->
        (fun f_ () -> f_ ((mtx_get _A2 (suc n) ai (bia, bi)) ()) ())
          (fun x ->
            (fun f_ () -> f_ ((mtx_get _A2 (suc n) ai (bia, bib)) ()) ())
              (fun xa ->
                (fun f_ () -> f_ ((mtx_get _A2 (suc n) ai (bib, bi)) ()) ())
                  (fun xb ->
                    mtx_set _A2 (suc n) ai (bia, bi)
                      (min _A1.linordered_ab_semigroup_add_linordered_ab_monoid_add.linorder_linordered_ab_semigroup_add.order_linorder.preorder_order.ord_preorder
                        x (plus _A1.ordered_comm_monoid_add_linordered_ab_monoid_add.comm_monoid_add_ordered_comm_monoid_add.monoid_add_comm_monoid_add.semigroup_add_monoid_add.plus_semigroup_add
                            xa xb))))));;

let rec fw_impl (_A1, _A2)
  n = imp_fora zero_nata (plus_nata n one_nata)
        (fun xb ->
          imp_fora zero_nata (plus_nata n one_nata)
            (fun xd ->
              imp_fora zero_nata (plus_nata n one_nata)
                (fun xf sigma -> fw_upd_impl (_A1, _A2) n sigma xb xd xf)));;

let rec gen_length n x1 = match n, x1 with n, x :: xs -> gen_length (suc n) xs
                     | n, [] -> n;;

let rec map_filter
  f x1 = match f, x1 with f, [] -> []
    | f, x :: xs ->
        (match f x with None -> map_filter f xs
          | Some y -> y :: map_filter f xs);;

let cODE_ABORT _ = failwith "Misc.CODE_ABORT";;

let one_int : int = Int_of_integer (Big_int.big_int_of_int 1);;

let rec int_of x = (if x then one_int else zero_inta);;

let rec list_update
  x0 i y = match x0, i, y with [], i, y -> []
    | x :: xs, i, y ->
        (if equal_nata i zero_nata then y :: xs
          else x :: list_update xs (minus_nat i one_nata) y);;

let rec step
  x0 uv = match x0, uv with
    JMPZ q, (pc, (st, (m, (f, rs)))) ->
      Some ((if f then plus_nata pc one_nata else q), (st, (m, (f, rs))))
    | ADD, (pc, (a :: b :: st, (m, (f, rs)))) ->
        Some (plus_nata pc one_nata, (plus_inta a b :: st, (m, (f, rs))))
    | NOT, (pc, (b :: st, (m, (f, rs)))) ->
        Some (plus_nata pc one_nata, (st, (m, (not f, rs))))
    | AND, (pc, (b :: st, (m, (f, rs)))) ->
        (if equal_inta b zero_inta || equal_inta b one_int
          then Some (plus_nata pc one_nata,
                      (st, (m, (equal_inta b one_int && f, rs))))
          else None)
    | LT, (pc, (a :: b :: st, (m, (f, rs)))) ->
        Some (plus_nata pc one_nata, (st, (m, (less_int a b, rs))))
    | LE, (pc, (a :: b :: st, (m, (f, rs)))) ->
        Some (plus_nata pc one_nata, (st, (m, (less_eq_int a b, rs))))
    | EQ, (pc, (a :: b :: st, (m, (f, rs)))) ->
        Some (plus_nata pc one_nata, (st, (m, (equal_inta a b, rs))))
    | PUSH v, (pc, (st, (m, (f, rs)))) ->
        Some (plus_nata pc one_nata, (v :: st, (m, (f, rs))))
    | POP, (pc, (v :: st, (m, (f, rs)))) ->
        Some (plus_nata pc one_nata, (st, (m, (f, rs))))
    | LID r, (pc, (st, (m, (f, rs)))) ->
        Some (plus_nata pc one_nata, (nth m r :: st, (m, (f, rs))))
    | STORE, (pc, (v :: r :: st, (m, (f, rs)))) ->
        (if less_eq_int zero_inta r
          then Some (plus_nata pc one_nata,
                      (st, (list_update m (nat r) v, (f, rs))))
          else None)
    | STOREI (r, v), (pc, (st, (m, (f, rs)))) ->
        Some (plus_nata pc one_nata, (st, (list_update m r v, (f, rs))))
    | COPY, (pc, (st, (m, (f, rs)))) ->
        Some (plus_nata pc one_nata, (int_of f :: st, (m, (f, rs))))
    | CALL, (pc, (q :: st, (m, (f, rs)))) ->
        (if less_eq_int zero_inta q
          then Some (nat q, (int_of_nat pc :: st, (m, (f, rs)))) else None)
    | RETURN, (pc, (q :: st, (m, (f, rs)))) ->
        (if less_eq_int zero_inta q
          then Some (plus_nata (nat q) one_nata, (st, (m, (f, rs)))) else None)
    | STOREC (c, d), (pc, (st, (m, (f, rs)))) ->
        (if equal_inta d zero_inta
          then Some (plus_nata pc one_nata, (st, (m, (f, c :: rs)))) else None)
    | SETF b, (pc, (st, (m, (f, rs)))) ->
        Some (plus_nata pc one_nata, (st, (m, (b, rs))))
    | ADD, (v, ([], vc)) -> None
    | ADD, (v, ([vd], vc)) -> None
    | NOT, (v, ([], vc)) -> None
    | AND, (v, ([], vc)) -> None
    | LT, (v, ([], vc)) -> None
    | LT, (v, ([vd], vc)) -> None
    | LE, (v, ([], vc)) -> None
    | LE, (v, ([vd], vc)) -> None
    | EQ, (v, ([], vc)) -> None
    | EQ, (v, ([vd], vc)) -> None
    | POP, (v, ([], vc)) -> None
    | STORE, (v, ([], vc)) -> None
    | STORE, (v, ([vd], vc)) -> None
    | CALL, (v, ([], vc)) -> None
    | RETURN, (v, ([], vc)) -> None
    | HALT, uv -> None;;

let rec exec
  prog n (pc, (st, (m, (f, rs)))) pcs =
    (if equal_nata n zero_nata then None
      else (match prog pc with None -> None
             | Some instr ->
               (if equal_instra instr HALT
                 then Some ((pc, (st, (m, (f, rs)))), pc :: pcs)
                 else (match step instr (pc, (st, (m, (f, rs))))
                        with None -> None
                        | Some s ->
                          exec prog (minus_nat n one_nata) s (pc :: pcs)))));;

let rec fwi_impl (_A1, _A2)
  n = (fun ai bi ->
        imp_fora zero_nata (plus_nata n one_nata)
          (fun xa ->
            imp_fora zero_nata (plus_nata n one_nata)
              (fun xc sigma -> fw_upd_impl (_A1, _A2) n sigma bi xa xc))
          ai);;

let rec the (Some x2) = x2;;

let rec gen_pick
  it s =
    the (it s (fun a -> (match a with None -> true | Some _ -> false))
           (fun x _ -> Some x)
          None);;

let rec println x = print (x ^ "\092");;

let rec of_phantom (Phantom x) = x;;

let rec size_list x = gen_length zero_nata x;;

let rec card (_A1, _A2)
  = function
    Coset xs ->
      minus_nat (of_phantom (card_UNIV _A1)) (size_list (remdups _A2 xs))
    | Set xs -> size_list (remdups _A2 xs);;

let rec ht_new_sz (_A1, _A2) _B
  n = (let l = replicate n [] in
        (fun f_ () -> f_ (((fun () -> Array.of_list l)) ()) ())
          (fun a -> (fun () -> (HashTable (a, zero_nata)))));;

let rec ht_new (_A1, _A2) _B
  = ht_new_sz (_A1, _A2) _B (def_hashmap_size _A1 Type);;

let rec bitOR_integer
  i j = (if Big_int.le_big_int Big_int.zero_big_int i
          then (if Big_int.le_big_int Big_int.zero_big_int j
                 then Big_int.or_big_int i j else Bits_Integer.or_pninteger i j)
          else (if Big_int.lt_big_int j Big_int.zero_big_int
                 then bitNOT_integer
                        (Big_int.and_big_int (bitNOT_integer i)
                          (bitNOT_integer j))
                 else Bits_Integer.or_pninteger j i));;

let rec test_bit_uint32
  x n = less_nat n (nat_of_integer (Big_int.big_int_of_int 32)) &&
          Uint32.test_bit x (integer_of_nat n);;

let rec integer_of_uint32
  n = (if test_bit_uint32 n (nat_of_integer (Big_int.big_int_of_int 31))
        then bitOR_integer
               (Big_int.big_int_of_int32
                 (Int32.logand n
                   (uint32 (Big_int.big_int_of_string "2147483647"))))
               (Big_int.big_int_of_string "2147483648")
        else Big_int.big_int_of_int32 n);;

let rec nat_of_uint32 x = nat_of_integer (integer_of_uint32 x);;

let rec nat_of_hashcode x = nat_of_uint32 x;;

let rec bounded_hashcode_nat _A
  n x = modulo_nat (nat_of_hashcode (hashcode _A x)) n;;

let rec the_array (HashTable (a, uu)) = a;;

let rec ls_update _A
  k v x2 = match k, v, x2 with k, v, [] -> ([(k, v)], false)
    | k, v, (l, w) :: ls ->
        (if eq _A k l then ((k, v) :: ls, true)
          else (let r = ls_update _A k v ls in ((l, w) :: fst r, snd r)));;

let rec the_size (HashTable (uu, n)) = n;;

let rec ht_upd (_A1, _A2, _A3) _B
  k v ht =
    (fun f_ () -> f_ ((len (heap_list (heap_prod _A3 _B)) (the_array ht)) ())
      ())
      (fun m ->
        (let i = bounded_hashcode_nat _A2 m k in
          (fun f_ () -> f_
            ((ntha (heap_list (heap_prod _A3 _B)) (the_array ht) i) ()) ())
            (fun l ->
              (let la = ls_update _A1 k v l in
                (fun f_ () -> f_
                  ((upd (heap_list (heap_prod _A3 _B)) i (fst la)
                     (the_array ht))
                  ()) ())
                  (fun _ ->
                    (let n = (if snd la then the_size ht else suc (the_size ht))
                       in
                      (fun () -> (HashTable (the_array ht, n)))))))));;

let top_set : 'a set = Coset [];;

let rec eq_set (_A1, _A2)
  x0 x1 = match x0, x1 with
    Coset xs, Coset ys ->
      list_all (membera _A2 ys) xs && list_all (membera _A2 xs) ys
    | Set xs, Set ys ->
        list_all (membera _A2 ys) xs && list_all (membera _A2 xs) ys
    | Set ys, Coset xs ->
        (let n = card (_A1, _A2) top_set in
          (if equal_nata n zero_nata then false
            else (let xsa = remdups _A2 xs in
                  let ysa = remdups _A2 ys in
                   equal_nata (plus_nata (size_list xsa) (size_list ysa)) n &&
                     (list_all (fun x -> not (membera _A2 ysa x)) xsa &&
                       list_all (fun y -> not (membera _A2 xsa y)) ysa))))
    | Coset xs, Set ys ->
        (let n = card (_A1, _A2) top_set in
          (if equal_nata n zero_nata then false
            else (let xsa = remdups _A2 xs in
                  let ysa = remdups _A2 ys in
                   equal_nata (plus_nata (size_list xsa) (size_list ysa)) n &&
                     (list_all (fun x -> not (membera _A2 ysa x)) xsa &&
                       list_all (fun y -> not (membera _A2 xsa y)) ysa))));;

let rec ht_insls (_A1, _A2, _A3) _B
  x0 ht = match x0, ht with [], ht -> (fun () -> ht)
    | (k, v) :: l, ht ->
        (fun f_ () -> f_ ((ht_upd (_A1, _A2, _A3) _B k v ht) ()) ())
          (ht_insls (_A1, _A2, _A3) _B l);;

let rec ht_copy (_A1, _A2, _A3) _B
  n src dst =
    (if equal_nata n zero_nata then (fun () -> dst)
      else (fun f_ () -> f_
             ((ntha (heap_list (heap_prod _A3 _B)) (the_array src)
                (minus_nat n one_nata))
             ()) ())
             (fun l ->
               (fun f_ () -> f_ ((ht_insls (_A1, _A2, _A3) _B l dst) ()) ())
                 (ht_copy (_A1, _A2, _A3) _B (minus_nat n one_nata) src)));;

let rec app f a = f a;;

let rec hm_isEmpty ht = (fun () -> (equal_nata (the_size ht) zero_nata));;

let tRACE_impl : (unit -> unit) = (fun () -> (tracea ()));;

let rec array_get a = comp (FArray.IsabelleMapping.array_get a) integer_of_nat;;

let rec array_set a = comp (FArray.IsabelleMapping.array_set a) integer_of_nat;;

let rec new_array v = comp (FArray.IsabelleMapping.new_array v) integer_of_nat;;

let rec ls_delete _A
  k x1 = match k, x1 with k, [] -> ([], false)
    | k, (l, w) :: ls ->
        (if eq _A k l then (ls, true)
          else (let r = ls_delete _A k ls in ((l, w) :: fst r, snd r)));;

let rec ht_delete (_A1, _A2, _A3) _B
  k ht =
    (fun f_ () -> f_ ((len (heap_list (heap_prod _A3 _B)) (the_array ht)) ())
      ())
      (fun m ->
        (let i = bounded_hashcode_nat _A2 m k in
          (fun f_ () -> f_
            ((ntha (heap_list (heap_prod _A3 _B)) (the_array ht) i) ()) ())
            (fun l ->
              (let la = ls_delete _A1 k l in
                (fun f_ () -> f_
                  ((upd (heap_list (heap_prod _A3 _B)) i (fst la)
                     (the_array ht))
                  ()) ())
                  (fun _ ->
                    (let n =
                       (if snd la then minus_nat (the_size ht) one_nata
                         else the_size ht)
                       in
                      (fun () -> (HashTable (the_array ht, n)))))))));;

let rec ls_lookup _A
  x xa1 = match x, xa1 with x, [] -> None
    | x, (k, v) :: l -> (if eq _A x k then Some v else ls_lookup _A x l);;

let rec ht_lookup (_A1, _A2, _A3) _B
  x ht =
    (fun f_ () -> f_ ((len (heap_list (heap_prod _A3 _B)) (the_array ht)) ())
      ())
      (fun m ->
        (let i = bounded_hashcode_nat _A2 m x in
          (fun f_ () -> f_
            ((ntha (heap_list (heap_prod _A3 _B)) (the_array ht) i) ()) ())
            (fun l -> (fun () -> (ls_lookup _A1 x l)))));;

let rec ht_rehash (_A1, _A2, _A3) _B
  ht = (fun f_ () -> f_ ((len (heap_list (heap_prod _A3 _B)) (the_array ht)) ())
         ())
         (fun n ->
           (fun f_ () -> f_
             ((ht_new_sz (_A2, _A3) _B
                (times_nat (nat_of_integer (Big_int.big_int_of_int 2)) n))
             ()) ())
             (ht_copy (_A1, _A2, _A3) _B n ht));;

let load_factor : nat = nat_of_integer (Big_int.big_int_of_int 75);;

let rec ht_update (_A1, _A2, _A3) _B
  k v ht =
    (fun f_ () -> f_ ((len (heap_list (heap_prod _A3 _B)) (the_array ht)) ())
      ())
      (fun m ->
        (fun f_ () -> f_
          ((if less_eq_nat (times_nat m load_factor)
                 (times_nat (the_size ht)
                   (nat_of_integer (Big_int.big_int_of_int 100)))
             then ht_rehash (_A1, _A2, _A3) _B ht else (fun () -> ht))
          ()) ())
          (ht_upd (_A1, _A2, _A3) _B k v));;

let rec op_list_tl x = tl x;;

let bot_set : 'a set = Set [];;

let rec set_act _A = function In x1 -> insert _A x1 bot_set
                     | Out x2 -> insert _A x2 bot_set
                     | Sil x3 -> insert _A x3 bot_set;;

let rec array_copy _A
  a = (fun f_ () -> f_ ((len _A a) ()) ())
        (fun l ->
          (if equal_nata l zero_nata then (fun () -> Array.of_list [])
            else (fun f_ () -> f_ ((ntha _A a zero_nata) ()) ())
                   (fun s ->
                     (fun f_ () -> f_ ((newa _A l s) ()) ())
                       (fun aa ->
                         (fun f_ () -> f_ ((blit _A a zero_nata aa zero_nata l)
                           ()) ())
                           (fun _ -> (fun () -> aa))))));;

let rec array_grow
  a = comp (FArray.IsabelleMapping.array_grow a) integer_of_nat;;

let rec hm_it_adjust (_A1, _A2) _B
  v ht =
    (if equal_nata v zero_nata then (fun () -> zero_nata)
      else (fun f_ () -> f_
             ((ntha (heap_list (heap_prod _A2 _B)) (the_array ht)
                (suc (minus_nat v one_nata)))
             ()) ())
             (fun a ->
               (match a
                 with [] ->
                   hm_it_adjust (_A1, _A2) _B
                     (minus_nat (suc (minus_nat v one_nata)) one_nata) ht
                 | _ :: _ -> (fun () -> (suc (minus_nat v one_nata))))));;

let rec op_list_rev x = rev x;;

let rec all_interval_nat
  p i j = less_eq_nat j i || p i && all_interval_nat p (suc i) j;;

let rec pred_act _A = (fun p x -> ball (set_act _A x) p);;

let rec neg_dbm_entry _A = function Le a -> Lt (uminus _A a)
                           | Lt a -> Le (uminus _A a)
                           | INF -> INF;;

let rec imp_for
  i u c f s =
    (if less_eq_nat u i then (fun () -> s)
      else (fun f_ () -> f_ ((c s) ()) ())
             (fun ctn ->
               (if ctn
                 then (fun f_ () -> f_ ((f i s) ()) ())
                        (imp_for (plus_nata i one_nata) u c f)
                 else (fun () -> s))));;

let rec whilea b c s = (if b s then whilea b c (c s) else s);;

let rec down_impl (_A1, _A2, _A3)
  n = imp_fora one_nata (suc n)
        (fun xb sigma ->
          (fun f_ () -> f_
            ((imp_fora one_nata (suc n)
               (fun xe sigmaa ->
                 (fun f_ () -> f_
                   ((mtx_get (heap_DBMEntry _A3) (suc n) sigma (xe, xb)) ()) ())
                   (fun x_f ->
                     (fun () ->
                       (min (ord_DBMEntry
                              (_A2, _A1.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.linordered_ab_semigroup_add_linordered_ab_monoid_add.linorder_linordered_ab_semigroup_add))
                         x_f sigmaa))))
               (Le (zero _A1.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.ordered_comm_monoid_add_linordered_ab_monoid_add.comm_monoid_add_ordered_comm_monoid_add.monoid_add_comm_monoid_add.zero_monoid_add)))
            ()) ())
            (mtx_set (heap_DBMEntry _A3) (suc n) sigma (zero_nata, xb)));;

let rec free_impl (_A1, _A2)
  n = (fun ai bi ->
        (fun f_ () -> f_
          ((imp_fora zero_nata (suc n)
             (fun xa sigma ->
               (if not (equal_nata xa bi)
                 then (fun f_ () -> f_
                        ((mtx_get (heap_DBMEntry _A2) (suc n) sigma
                           (xa, zero_nata))
                        ()) ())
                        (mtx_set (heap_DBMEntry _A2) (suc n) sigma (xa, bi))
                 else (fun () -> sigma)))
             ai)
          ()) ())
          (imp_fora zero_nata (suc n)
            (fun xb sigma ->
              (if not (equal_nata xb bi)
                then mtx_set (heap_DBMEntry _A2) (suc n) sigma (bi, xb) INF
                else (fun () -> sigma)))));;

let rec array_length
  x = comp nat_of_integer FArray.IsabelleMapping.array_length x;;

let rec array_shrink
  a = comp (FArray.IsabelleMapping.array_shrink a) integer_of_nat;;

let op_list_empty : 'a list = [];;

let rec as_get s i = (let a = s in
                      let (aa, _) = a in
                       array_get aa i);;

let rec as_shrink
  s = (let a = s in
       let (aa, n) = a in
       let ab =
         (if less_eq_nat
               (times_nat (nat_of_integer (Big_int.big_int_of_int 128)) n)
               (array_length aa) &&
               less_nat (nat_of_integer (Big_int.big_int_of_int 4)) n
           then array_shrink aa n else aa)
         in
        (ab, n));;

let rec as_pop s = (let a = s in
                    let (aa, n) = a in
                     as_shrink (aa, minus_nat n one_nata));;

let rec as_set s i x = (let a = s in
                        let (aa, b) = a in
                         (array_set aa i x, b));;

let rec as_top s = (let a = s in
                    let (aa, n) = a in
                     array_get aa (minus_nat n one_nata));;

let rec hm_it_next_key (_A1, _A2) _B
  ht = (fun f_ () -> f_ ((len (heap_list (heap_prod _A2 _B)) (the_array ht)) ())
         ())
         (fun n ->
           (if equal_nata n zero_nata then failwith "Map is empty!"
             else (fun f_ () -> f_
                    ((hm_it_adjust (_A1, _A2) _B (minus_nat n one_nata) ht) ())
                    ())
                    (fun i ->
                      (fun f_ () -> f_
                        ((ntha (heap_list (heap_prod _A2 _B)) (the_array ht) i)
                        ()) ())
                        (fun a ->
                          (match a with [] -> failwith "Map is empty!"
                            | x :: _ -> (fun () -> (fst x)))))));;

let rec heap_WHILET
  b f s =
    (fun f_ () -> f_ ((b s) ()) ())
      (fun bv ->
        (if bv then (fun f_ () -> f_ ((f s) ()) ()) (heap_WHILET b f)
          else (fun () -> s)));;

let rec imp_nfoldli
  x0 c f s = match x0, c, f, s with
    x :: ls, c, f, s ->
      (fun f_ () -> f_ ((c s) ()) ())
        (fun b ->
          (if b then (fun f_ () -> f_ ((f x s) ()) ()) (imp_nfoldli ls c f)
            else (fun () -> s)))
    | [], c, f, s -> (fun () -> s);;

let rec lso_bex_impl
  pi li =
    imp_nfoldli li (fun sigma -> (fun () -> (not sigma))) (fun xa _ -> pi xa)
      false;;

let rec op_list_is_empty x = null x;;

let rec op_list_prepend x = (fun a -> x :: a);;

let rec hms_extract
  lookup delete k m =
    (fun f_ () -> f_ ((lookup k m) ()) ())
      (fun a ->
        (match a with None -> (fun () -> (None, m))
          | Some v ->
            (fun f_ () -> f_ ((delete k m) ()) ())
              (fun ma -> (fun () -> (Some v, ma)))));;

let rec pw_impl _A (_B1, _B2, _B3)
  keyi copyi tracei lei a_0i fi succsi emptyi =
    (fun f_ () -> f_ (a_0i ()) ())
      (fun x ->
        (fun f_ () -> f_ ((emptyi x) ()) ())
          (fun xa ->
            (fun f_ () -> f_ (a_0i ()) ())
              (fun xaa ->
                (fun f_ () -> f_ ((fi xaa) ()) ())
                  (fun xab ->
                    (fun f_ () -> f_
                      ((if not xa && xab
                         then (fun f_ () -> f_
                                ((ht_new (_B2, _B3) (heap_list _A)) ()) ())
                                (fun x_b -> (fun () -> (true, x_b)))
                         else (fun f_ () -> f_ (a_0i ()) ())
                                (fun xb ->
                                  (fun f_ () -> f_ ((emptyi xb) ()) ())
                                    (fun x_a ->
                                      (if x_a
then (fun f_ () -> f_ ((ht_new (_B2, _B3) (heap_list _A)) ()) ())
       (fun x_c -> (fun () -> (false, x_c)))
else (fun f_ () -> f_ (a_0i ()) ())
       (fun xc ->
         (fun f_ () -> f_ ((keyi xc) ()) ())
           (fun xd ->
             (fun f_ () -> f_ (a_0i ()) ())
               (fun xac ->
                 (fun f_ () -> f_ ((ht_new (_B2, _B3) (heap_list _A)) ()) ())
                   (fun xba ->
                     (fun f_ () -> f_
                       ((ht_update (_B1, _B2, _B3) (heap_list _A) xd [xac] xba)
                       ()) ())
                       (fun xe ->
                         (fun f_ () -> f_ (a_0i ()) ())
                           (fun xad ->
                             (let (a1, a2) = (xe, op_list_prepend xad []) in
                               (fun f_ () -> f_
                                 ((heap_WHILET
                                    (fun (_, (a1b, a2b)) ->
                                      (fun () ->
(not a2b && not (op_list_is_empty a1b))))
                                    (fun (a1a, (a1b, a2b)) ->
                                      (let (a1c, a2c) =
 (match a1b with [] -> cODE_ABORT (fun _ -> (hd a1b, tl a1b))
   | a :: b -> (a, b))
 in
(fun f_ () -> f_ ((emptyi a1c) ()) ())
  (fun x_e ->
    (if x_e then (fun () -> (a1a, (a2c, a2b)))
      else (fun f_ () -> f_ (tRACE_impl ()) ())
             (fun _ ->
               (fun f_ () -> f_
                 ((tracei
                     [Chara (true, false, true, false, false, false, true,
                              false);
                       Chara (false, false, false, true, true, true, true,
                               false);
                       Chara (false, false, false, false, true, true, true,
                               false);
                       Chara (false, false, true, true, false, true, true,
                               false);
                       Chara (true, true, true, true, false, true, true, false);
                       Chara (false, true, false, false, true, true, true,
                               false);
                       Chara (true, false, true, false, false, true, true,
                               false);
                       Chara (false, false, true, false, false, true, true,
                               false)]
                    a1c)
                 ()) ())
                 (fun _ ->
                   (fun f_ () -> f_ ((succsi a1c) ()) ())
                     (fun x_h ->
                       imp_nfoldli x_h (fun (_, (_, b)) -> (fun () -> (not b)))
                         (fun xl (a1d, (a1e, _)) ->
                           (fun f_ () -> f_ ((emptyi xl) ()) ())
                             (fun x_k ->
                               (if x_k then (fun () -> (a1d, (a1e, false)))
                                 else (fun f_ () -> f_ ((fi xl) ()) ())
(fun x_l ->
  (if x_l then (fun () -> (a1d, (a1e, true)))
    else (fun f_ () -> f_ ((keyi xl) ()) ())
           (fun x_m ->
             (fun f_ () -> f_
               ((hms_extract (ht_lookup (_B1, _B2, _B3) (heap_list _A))
                  (ht_delete (_B1, _B2, _B3) (heap_list _A)) x_m a1d)
               ()) ())
               (fun a ->
                 (match a
                   with (None, a2f) ->
                     (fun f_ () -> f_ ((copyi xl) ()) ())
                       (fun xf ->
                         (fun f_ () -> f_
                           ((ht_update (_B1, _B2, _B3) (heap_list _A) x_m [xf]
                              a2f)
                           ()) ())
                           (fun x_o ->
                             (fun () ->
                               (x_o, (op_list_prepend xl a1e, false)))))
                   | (Some x_o, a2f) ->
                     (fun f_ () -> f_ ((lso_bex_impl (lei xl) x_o) ()) ())
                       (fun x_p ->
                         (if x_p
                           then (fun f_ () -> f_
                                  ((ht_update (_B1, _B2, _B3) (heap_list _A) x_m
                                     x_o a2f)
                                  ()) ())
                                  (fun x_q -> (fun () -> (x_q, (a1e, false))))
                           else (fun f_ () -> f_ ((copyi xl) ()) ())
                                  (fun xf ->
                                    (fun f_ () -> f_
                                      ((ht_update (_B1, _B2, _B3) (heap_list _A)
 x_m (xf :: x_o) a2f)
                                      ()) ())
                                      (fun x_q ->
(fun () -> (x_q, (op_list_prepend xl a1e, false)))))))))))))))
                         (a1a, (a2c, false)))))))))
                                    (a1, (a2, false)))
                                 ()) ())
                                 (fun (a1a, (_, a2b)) ->
                                   (fun () -> (a2b, a1a))))))))))))))
                      ()) ())
                      (fun (a1, _) -> (fun () -> a1))))));;

let rec mtx_tabulate (_A1, _A2, _A3) (_B1, _B2)
  n m c =
    (fun f_ () -> f_ ((newa _B2 (times_nat n m) (zero _B1)) ()) ())
      (fun ma ->
        (fun f_ () -> f_
          ((imp_fora zero_nata (times_nat n m)
             (fun k (i, (j, maa)) ->
               (fun f_ () -> f_ ((upd _B2 k (c (i, j)) maa) ()) ())
                 (fun _ ->
                   (let ja = plus_nata j one_nata in
                     (if less_nat ja m then (fun () -> (i, (ja, maa)))
                       else (fun () ->
                              (plus _A2 i (one _A1), (zero_nata, maa)))))))
             (zero _A3, (zero_nata, ma)))
          ()) ())
          (fun (_, a) -> (let (_, aa) = a in (fun () -> aa))));;

let rec v_dbm_impl (_A1, _A2)
  n = mtx_tabulate (one_nat, plus_nat, zero_nat)
        ((zero_DBMEntry
           _A1.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.ordered_comm_monoid_add_linordered_ab_monoid_add.comm_monoid_add_ordered_comm_monoid_add.monoid_add_comm_monoid_add.zero_monoid_add),
          (heap_DBMEntry _A2))
        (suc n) (suc n)
        (v_dbm (zero_nat, equal_nat, ord_nat)
          _A1.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.ordered_comm_monoid_add_linordered_ab_monoid_add.comm_monoid_add_ordered_comm_monoid_add.monoid_add_comm_monoid_add.zero_monoid_add
          n);;

let rec stat_stop x = (fun _ -> ()) x;;

let rec as_push
  s x = (let a = s in
         let (aa, n) = a in
         let ab =
           (if equal_nata n (array_length aa)
             then array_grow aa
                    (max ord_nat (nat_of_integer (Big_int.big_int_of_int 4))
                      (times_nat (nat_of_integer (Big_int.big_int_of_int 2)) n))
                    x
             else aa)
           in
         let ac = array_set ab n x in
          (ac, plus_nata n one_nata));;

let rec as_take
  m s = (let a = s in
         let (aa, n) = a in
          (if less_nat m n then as_shrink (aa, m) else (aa, n)));;

let rec rev_append x0 ac = match x0, ac with [], ac -> ac
                     | x :: xs, ac -> rev_append xs (x :: ac);;

let rec ran_of_map_impl (_A1, _A2, _A3) _B
  = (fun xi ->
      (fun f_ () -> f_
        ((heap_WHILET
           (fun (_, a2) ->
             (fun f_ () -> f_ ((hm_isEmpty a2) ()) ())
               (fun x_a -> (fun () -> (not x_a))))
           (fun (a1, a2) ->
             (fun f_ () -> f_ ((hm_it_next_key (_A2, _A3) _B a2) ()) ())
               (fun x_a ->
                 (fun f_ () -> f_
                   ((hms_extract (ht_lookup (_A1, _A2, _A3) _B)
                      (ht_delete (_A1, _A2, _A3) _B) x_a a2)
                   ()) ())
                   (fun (a1a, b) -> (fun () -> (the a1a :: a1, b)))))
           ([], xi))
        ()) ())
        (fun (a1, _) -> (fun () -> a1)));;

let rec map_option f x1 = match f, x1 with f, None -> None
                     | f, Some x2 -> Some (f x2);;

let rec sup_set _A
  x0 a = match x0, a with
    Coset xs, a -> Coset (filtera (fun x -> not (member _A x a)) xs)
    | Set xs, a -> fold (insert _A) xs a;;

let rec stripf = function INSTR instr -> instr
                 | CEXP v -> SETF false;;

let rec stript = function INSTR instr -> instr
                 | CEXP v -> SETF true;;

let rec collect_store
  prog =
    Set (map_filter
          (fun a ->
            (match a with None -> None | Some (INSTR (JMPZ _)) -> None
              | Some (INSTR ADD) -> None | Some (INSTR NOT) -> None
              | Some (INSTR AND) -> None | Some (INSTR LT) -> None
              | Some (INSTR LE) -> None | Some (INSTR EQ) -> None
              | Some (INSTR (PUSH _)) -> None | Some (INSTR POP) -> None
              | Some (INSTR (LID _)) -> None | Some (INSTR STORE) -> None
              | Some (INSTR (STOREI (_, _))) -> None | Some (INSTR COPY) -> None
              | Some (INSTR CALL) -> None | Some (INSTR RETURN) -> None
              | Some (INSTR HALT) -> None
              | Some (INSTR (STOREC (c, x))) -> Some (c, x)
              | Some (INSTR (SETF _)) -> None | Some (CEXP _) -> None))
          prog);;

let rec check_resets
  prog = ball (collect_store prog) (fun (_, x) -> equal_inta x zero_inta);;

let rec collect_cexp
  prog =
    Set (map_filter
          (fun a ->
            (match a with None -> None
              | Some aa ->
                (match aa with INSTR _ -> None | CEXP ab -> Some ab)))
          prog);;

let rec sup_seta _A (Set xs) = fold (sup_set _A) xs bot_set;;

let rec constraint_pair = function LTa (x, m) -> (x, m)
                          | LEa (x, m) -> (x, m)
                          | EQa (x, m) -> (x, m)
                          | GE (x, m) -> (x, m)
                          | GT (x, m) -> (x, m);;

let rec collect_clock_pairs cc = image constraint_pair (Set cc);;

let rec clkp_seta
  inv prog =
    sup_set (equal_prod equal_nat equal_int)
      (sup_seta (equal_prod equal_nat equal_int)
        (image collect_clock_pairs (Set (concat inv))))
      (image constraint_pair (collect_cexp prog));;

let rec clk_set
  inv prog =
    sup_set equal_nat (image fst (clkp_seta inv prog))
      (image fst (collect_store prog));;

let rec pre_checks
  x = (fun p m inv pred trans prog ->
        [("Length of invariant is p", equal_nata (size_list inv) p);
          ("Length of transitions is p", equal_nata (size_list trans) p);
          ("Length of predicate is p",
            all_interval_nat
              (fun i ->
                equal_nata (size_list (nth pred i)) (size_list (nth trans i)) &&
                  equal_nata (size_list (nth inv i)) (size_list (nth trans i)))
              zero_nata p);
          ("Transitions, predicates, and invariants are of the right length per process",
            all_interval_nat
              (fun i ->
                equal_nata (size_list (nth pred i)) (size_list (nth trans i)) &&
                  equal_nata (size_list (nth inv i)) (size_list (nth trans i)))
              zero_nata p);
          ("Edge targets are in bounds",
            list_all
              (fun t ->
                list_all
                  (list_all (fun (_, (_, (_, l))) -> less_nat l (size_list t)))
                  t)
              trans);
          ("p > 0", less_nat zero_nata p); ("m > 0", less_nat zero_nata m);
          ("Every process has at least one transition",
            all_interval_nat (fun i -> not (null (nth trans i))) zero_nata p);
          ("The initial state of each process has a transition",
            all_interval_nat (fun q -> not (null (nth (nth trans q) zero_nata)))
              zero_nata p);
          ("Clocks >= 0",
            ball (clkp_seta inv prog) (fun (_, a) -> less_eq_int zero_inta a));
          ("Set of clocks is {1..m}",
            eq_set (card_UNIV_nat, equal_nat) (clk_set inv prog)
              (Set (upt one_nata (suc m))));
          ("Resets correct", check_resets prog)])
        x;;

let rec stat_start x = (fun _ -> ()) x;;

let rec idx_iteratei_aux
  get sz i l c f sigma =
    (if equal_nata i zero_nata || not (c sigma) then sigma
      else idx_iteratei_aux get sz (minus_nat i one_nata) l c f
             (f (get l (minus_nat sz i)) sigma));;

let rec idx_iteratei
  get sz l c f sigma = idx_iteratei_aux get (sz l) (sz l) l c f sigma;;

let rec as_empty _B uu = (FArray.IsabelleMapping.array_of_list [], zero _B);;

let rec leadsto_impl_0 _A (_B1, _B2, _B3)
  copyia succsia leia keyia x =
    (let (a1, (a1a, a2a)) = x in
      (fun f_ () -> f_ ((keyia a2a) ()) ())
        (fun xa ->
          (fun f_ () -> f_
            ((hms_extract (ht_lookup (_B1, _B2, _B3) (heap_list _A))
               (ht_delete (_B1, _B2, _B3) (heap_list _A)) xa a1a)
            ()) ())
            (fun xaa ->
              (fun f_ () -> f_
                ((match xaa with (None, a2b) -> (fun () -> (a2b, false))
                   | (Some x_c, a2b) ->
                     (fun f_ () -> f_
                       ((imp_nfoldli x_c (fun sigma -> (fun () -> (not sigma)))
                          (fun xe sigma ->
                            (fun f_ () -> f_ ((leia xe a2a) ()) ())
                              (fun x_f -> (fun () -> (x_f || sigma))))
                          false)
                       ()) ())
                       (fun x_d ->
                         (fun f_ () -> f_
                           ((ht_update (_B1, _B2, _B3) (heap_list _A) xa x_c
                              a2b)
                           ()) ())
                           (fun x_e -> (fun () -> (x_e, x_d)))))
                ()) ())
                (fun a ->
                  (match a with (a1b, true) -> (fun () -> (a1, (a1b, true)))
                    | (a1b, false) ->
                      (fun f_ () -> f_ ((keyia a2a) ()) ())
                        (fun xb ->
                          (fun f_ () -> f_
                            ((hms_extract
                               (ht_lookup (_B1, _B2, _B3) (heap_list _A))
                               (ht_delete (_B1, _B2, _B3) (heap_list _A)) xb a1)
                            ()) ())
                            (fun xab ->
                              (fun f_ () -> f_
                                ((match xab
                                   with (None, a2c) -> (fun () -> (a2c, false))
                                   | (Some x_e, a2c) ->
                                     (fun f_ () -> f_
                                       ((lso_bex_impl (leia a2a) x_e) ()) ())
                                       (fun x_f ->
 (fun f_ () -> f_ ((ht_update (_B1, _B2, _B3) (heap_list _A) xb x_e a2c) ()) ())
   (fun x_g -> (fun () -> (x_g, x_f)))))
                                ()) ())
                                (fun aa ->
                                  (match aa
                                    with (a1c, true) ->
                                      (fun () -> (a1c, (a1b, false)))
                                    | (a1c, false) ->
                                      (fun f_ () -> f_ ((copyia a2a) ()) ())
(fun xc ->
  (fun f_ () -> f_ ((keyia xc) ()) ())
    (fun xd ->
      (fun f_ () -> f_
        ((hms_extract (ht_lookup (_B1, _B2, _B3) (heap_list _A))
           (ht_delete (_B1, _B2, _B3) (heap_list _A)) xd a1b)
        ()) ())
        (fun xac ->
          (fun f_ () -> f_
            ((match xac
               with (None, a2d) ->
                 (fun f_ () -> f_ ((copyia a2a) ()) ())
                   (fun xad ->
                     (fun f_ () -> f_
                       ((ht_update (_B1, _B2, _B3) (heap_list _A) xd
                          (op_list_prepend xad []) a2d)
                       ()) ())
                       (fun x_h -> (fun () -> ((), x_h))))
               | (Some x_g, a2d) ->
                 (fun f_ () -> f_ ((copyia a2a) ()) ())
                   (fun xad ->
                     (fun f_ () -> f_
                       ((ht_update (_B1, _B2, _B3) (heap_list _A) xd
                          (op_list_prepend xad x_g) a2d)
                       ()) ())
                       (fun x_i -> (fun () -> ((), x_i)))))
            ()) ())
            (fun (_, a2d) ->
              (fun f_ () -> f_ ((succsia a2a) ()) ())
                (fun xe ->
                  (fun f_ () -> f_
                    ((imp_nfoldli xe (fun (_, (_, b)) -> (fun () -> (not b)))
                       (fun xi (a1e, (a1f, _)) ->
                         leadsto_impl_0 _A (_B1, _B2, _B3) copyia succsia leia
                           keyia (a1e, (a1f, xi)))
                       (a1c, (a2d, false)))
                    ()) ())
                    (fun (a1e, (a1f, a2f)) ->
                      (fun f_ () -> f_ ((copyia a2a) ()) ())
                        (fun xf ->
                          (fun f_ () -> f_ ((keyia xf) ()) ())
                            (fun xg ->
                              (fun f_ () -> f_
                                ((hms_extract
                                   (ht_lookup (_B1, _B2, _B3) (heap_list _A))
                                   (ht_delete (_B1, _B2, _B3) (heap_list _A)) xg
                                   a1f)
                                ()) ())
                                (fun xad ->
                                  (fun f_ () -> f_
                                    ((match xad
                                       with (None, a2g) ->
 (fun f_ () -> f_ ((ht_update (_B1, _B2, _B3) (heap_list _A) xg [] a2g) ()) ())
   (fun x_k -> (fun () -> ((), x_k)))
                                       | (Some x_j, a2g) ->
 (fun f_ () -> f_
   ((ht_update (_B1, _B2, _B3) (heap_list _A) xg
      (if op_list_is_empty x_j then [] else op_list_tl x_j) a2g)
   ()) ())
   (fun x_l -> (fun () -> ((), x_l))))
                                    ()) ())
                                    (fun (_, a2g) ->
                                      (fun f_ () -> f_ ((copyia a2a) ()) ())
(fun xh ->
  (fun f_ () -> f_ ((keyia xh) ()) ())
    (fun xi ->
      (fun f_ () -> f_
        ((hms_extract (ht_lookup (_B1, _B2, _B3) (heap_list _A))
           (ht_delete (_B1, _B2, _B3) (heap_list _A)) xi a1e)
        ()) ())
        (fun xae ->
          (fun f_ () -> f_
            ((match xae
               with (None, a2h) ->
                 (fun f_ () -> f_ ((copyia a2a) ()) ())
                   (fun xaf ->
                     (fun f_ () -> f_
                       ((ht_update (_B1, _B2, _B3) (heap_list _A) xi [xaf] a2h)
                       ()) ())
                       (fun x_m -> (fun () -> ((), x_m))))
               | (Some x_l, a2h) ->
                 (fun f_ () -> f_ ((copyia a2a) ()) ())
                   (fun xaf ->
                     (fun f_ () -> f_
                       ((ht_update (_B1, _B2, _B3) (heap_list _A) xi
                          (xaf :: x_l) a2h)
                       ()) ())
                       (fun x_n -> (fun () -> ((), x_n)))))
            ()) ())
            (fun (_, a2h) ->
              (fun f_ () -> f_ (tRACE_impl ()) ())
                (fun _ ->
                  (fun () -> (a2h, (a2g, a2f)))))))))))))))))))))))))));;

let rec leadsto_impl _A (_B1, _B2, _B3)
  copyia succsia a_0ia leia keyia succs1i emptyi pi qi tracei =
    (fun f_ () -> f_ (a_0ia ()) ())
      (fun x ->
        (fun f_ () -> f_ ((emptyi x) ()) ())
          (fun xa ->
            (fun f_ () -> f_ (a_0ia ()) ())
              (fun _ ->
                (fun f_ () -> f_
                  ((if not xa && false
                     then (fun f_ () -> f_ ((ht_new (_B2, _B3) (heap_list _A))
                            ()) ())
                            (fun x_b -> (fun () -> (true, x_b)))
                     else (fun f_ () -> f_ (a_0ia ()) ())
                            (fun xb ->
                              (fun f_ () -> f_ ((emptyi xb) ()) ())
                                (fun x_a ->
                                  (if x_a
                                    then (fun f_ () -> f_
   ((ht_new (_B2, _B3) (heap_list _A)) ()) ())
   (fun x_c -> (fun () -> (false, x_c)))
                                    else (fun f_ () -> f_ (a_0ia ()) ())
   (fun xc ->
     (fun f_ () -> f_ ((keyia xc) ()) ())
       (fun xd ->
         (fun f_ () -> f_ (a_0ia ()) ())
           (fun xaa ->
             (fun f_ () -> f_ ((ht_new (_B2, _B3) (heap_list _A)) ()) ())
               (fun xba ->
                 (fun f_ () -> f_
                   ((ht_update (_B1, _B2, _B3) (heap_list _A) xd [xaa] xba) ())
                   ())
                   (fun xe ->
                     (fun f_ () -> f_ (a_0ia ()) ())
                       (fun xab ->
                         (fun f_ () -> f_
                           ((heap_WHILET
                              (fun (_, (a1b, a2b)) ->
                                (fun () ->
                                  (not a2b && not (op_list_is_empty a1b))))
                              (fun (a1a, (a1b, a2b)) ->
                                (let (a1c, a2c) =
                                   (match a1b
                                     with [] ->
                                       cODE_ABORT (fun _ -> (hd a1b, tl a1b))
                                     | a :: b -> (a, b))
                                   in
                                  (fun f_ () -> f_ ((emptyi a1c) ()) ())
                                    (fun x_e ->
                                      (if x_e then (fun () -> (a1a, (a2c, a2b)))
else (fun f_ () -> f_ (tRACE_impl ()) ())
       (fun _ ->
         (fun f_ () -> f_
           ((tracei
               [Chara (true, false, true, false, false, false, true, false);
                 Chara (false, false, false, true, true, true, true, false);
                 Chara (false, false, false, false, true, true, true, false);
                 Chara (false, false, true, true, false, true, true, false);
                 Chara (true, true, true, true, false, true, true, false);
                 Chara (false, true, false, false, true, true, true, false);
                 Chara (true, false, true, false, false, true, true, false);
                 Chara (false, false, true, false, false, true, true, false)]
              a1c)
           ()) ())
           (fun _ ->
             (fun f_ () -> f_ ((succs1i a1c) ()) ())
               (fun x_h ->
                 imp_nfoldli x_h (fun (_, (_, b)) -> (fun () -> (not b)))
                   (fun xl (a1d, (a1e, _)) ->
                     (fun f_ () -> f_ ((emptyi xl) ()) ())
                       (fun x_k ->
                         (if x_k then (fun () -> (a1d, (a1e, false)))
                           else (fun f_ () -> f_ ((keyia xl) ()) ())
                                  (fun x_m ->
                                    (fun f_ () -> f_
                                      ((hms_extract
 (ht_lookup (_B1, _B2, _B3) (heap_list _A))
 (ht_delete (_B1, _B2, _B3) (heap_list _A)) x_m a1d)
                                      ()) ())
                                      (fun a ->
(match a
  with (None, a2f) ->
    (fun f_ () -> f_ ((copyia xl) ()) ())
      (fun xf ->
        (fun f_ () -> f_
          ((ht_update (_B1, _B2, _B3) (heap_list _A) x_m [xf] a2f) ()) ())
          (fun x_o -> (fun () -> (x_o, (op_list_prepend xl a1e, false)))))
  | (Some x_o, a2f) ->
    (fun f_ () -> f_ ((lso_bex_impl (leia xl) x_o) ()) ())
      (fun x_p ->
        (if x_p
          then (fun f_ () -> f_
                 ((ht_update (_B1, _B2, _B3) (heap_list _A) x_m x_o a2f) ()) ())
                 (fun x_q -> (fun () -> (x_q, (a1e, false))))
          else (fun f_ () -> f_ ((copyia xl) ()) ())
                 (fun xf ->
                   (fun f_ () -> f_
                     ((ht_update (_B1, _B2, _B3) (heap_list _A) x_m (xf :: x_o)
                        a2f)
                     ()) ())
                     (fun x_q ->
                       (fun () ->
                         (x_q, (op_list_prepend xl a1e, false)))))))))))))
                   (a1a, (a2c, false)))))))))
                              (xe, (op_list_prepend xab [], false)))
                           ()) ())
                           (fun (a1a, (_, a2b)) ->
                             (fun () -> (a2b, a1a)))))))))))))
                  ()) ())
                  (fun (_, a2) ->
                    (fun f_ () -> f_
                      ((ran_of_map_impl (_B1, _B2, _B3) (heap_list _A) a2) ())
                      ())
                      (fun x_a ->
                        (fun f_ () -> f_ ((ht_new (_B2, _B3) (heap_list _A)) ())
                          ())
                          (fun xb ->
                            (fun f_ () -> f_
                              ((imp_nfoldli x_a
                                 (fun (a1a, _) -> (fun () -> (not a1a)))
                                 (fun xd (_, a2a) ->
                                   imp_nfoldli xd
                                     (fun (a1b, _) -> (fun () -> (not a1b)))
                                     (fun xg (_, a2b) ->
                                       (fun f_ () -> f_ ((pi xg) ()) ())
 (fun xc ->
   (fun f_ () -> f_ ((qi xg) ()) ())
     (fun xaa ->
       (if xc && xaa
         then (fun f_ () -> f_ ((ht_new (_B2, _B3) (heap_list _A)) ()) ())
                (fun xe ->
                  (fun f_ () -> f_
                    ((leadsto_impl_0 _A (_B1, _B2, _B3) copyia succsia leia
                       keyia (a2b, (xe, xg)))
                    ()) ())
                    (fun (a1, (_, a2aa)) -> (fun () -> (a2aa, a1))))
         else (fun () -> (false, a2b))))))
                                     (false, a2a))
                                 (false, xb))
                              ()) ())
                              (fun (a1a, _) -> (fun () -> a1a))))))));;

let rec more_checks
  x = (fun trans na ->
        [("Legal actions",
           list_all
             (list_all
               (list_all
                 (fun (_, a) ->
                   (let (aa, _) = a in
                     pred_act equal_nat (fun ab -> less_nat ab na) aa))))
             trans)])
        x;;

let rec as_length x = snd x;;

let rec last_seg_tr _A
  s = (let (a, (aa, (_, _))) = s in
       let (_, bc) =
         whilea
           (fun (xe, _) ->
             less_nat xe
               (if equal_nata
                     (plus_nata (minus_nat (as_length aa) one_nata) one_nata)
                     (as_length aa)
                 then as_length a
                 else as_get aa
                        (plus_nata (minus_nat (as_length aa) one_nata)
                          one_nata)))
           (fun (ac, bc) -> (let xa = as_get a ac in (suc ac, xa :: bc)))
           (as_get aa (minus_nat (as_length aa) one_nata), [])
         in
        bc);;

let rec list_map_update_aux
  eq k v x3 accu = match eq, k, v, x3, accu with
    eq, k, v, [], accu -> (k, v) :: accu
    | eq, k, v, x :: xs, accu ->
        (if eq (fst x) k then (k, v) :: xs @ accu
          else list_map_update_aux eq k v xs (x :: accu));;

let rec list_map_update eq k v m = list_map_update_aux eq k v m [];;

let rec list_map_lookup
  eq uu x2 = match eq, uu, x2 with eq, uu, [] -> None
    | eq, k, y :: ys ->
        (if eq (fst y) k then Some (snd y) else list_map_lookup eq k ys);;

let rec ahm_update_aux
  eq bhc (HashMap (a, n)) k v =
    (let h = bhc (array_length a) k in
     let m = array_get a h in
     let insert = is_none (list_map_lookup eq k m) in
      HashMap
        (array_set a h (list_map_update eq k v m),
          (if insert then plus_nata n one_nata else n)));;

let rec ahm_iteratei_aux
  a c f sigma =
    idx_iteratei array_get array_length a c (fun x -> foldli x c f) sigma;;

let rec ahm_rehash_auxa
  bhc n kv a = (let h = bhc n (fst kv) in array_set a h (kv :: array_get a h));;

let rec ahm_rehash_aux
  bhc a sz =
    ahm_iteratei_aux a (fun _ -> true) (ahm_rehash_auxa bhc sz)
      (new_array [] sz);;

let rec ahm_rehash
  bhc (HashMap (a, n)) sz = HashMap (ahm_rehash_aux bhc a sz, n);;

let load_factora : nat = nat_of_integer (Big_int.big_int_of_int 75);;

let rec ahm_filled
  (HashMap (a, n)) =
    less_eq_nat (times_nat (array_length a) load_factora)
      (times_nat n (nat_of_integer (Big_int.big_int_of_int 100)));;

let rec hm_grow
  (HashMap (a, n)) =
    plus_nata
      (times_nat (nat_of_integer (Big_int.big_int_of_int 2)) (array_length a))
      (nat_of_integer (Big_int.big_int_of_int 3));;

let rec ahm_update
  eq bhc k v hm =
    (let hma = ahm_update_aux eq bhc hm k v in
      (if ahm_filled hma then ahm_rehash bhc hma (hm_grow hma) else hma));;

let rec pop_tr (_A1, _A2)
  s = (let (a, (aa, (ab, bb))) = s in
       let x = minus_nat (as_length aa) one_nata in
       let xa =
         (let (_, bc) =
            whilea
              (fun (xe, _) ->
                less_nat xe
                  (if equal_nata (plus_nata x one_nata) (as_length aa)
                    then as_length a else as_get aa (plus_nata x one_nata)))
              (fun (ac, bc) ->
                (suc ac,
                  ahm_update (eq _A1) (bounded_hashcode_nat _A2) (as_get a ac)
                    (uminus_inta one_int) bc))
              (as_get aa x, ab)
            in
           bc)
         in
       let xb = as_take (as_top aa) a in
       let xc = as_pop aa in
        (xb, (xc, (xa, bb))));;

let rec glist_delete_aux
  eq x xa2 asa = match eq, x, xa2, asa with eq, x, [], asa -> asa
    | eq, x, y :: ys, asa ->
        (if eq x y then rev_append asa ys
          else glist_delete_aux eq x ys (y :: asa));;

let rec glist_delete eq x l = glist_delete_aux eq x l [];;

let rec showsp_prod
  s1 s2 p (x, y) =
    comp (comp (comp (comp (shows_string
                             [Chara (false, false, false, true, false, true,
                                      false, false)])
                       (s1 one_nata x))
                 (shows_string
                   [Chara (false, false, true, true, false, true, false, false);
                     Chara (false, false, false, false, false, true, false,
                             false)]))
           (s2 one_nata y))
      (shows_string
        [Chara (true, false, false, true, false, true, false, false)]);;

let rec is_Nil a = (match a with [] -> true | _ :: _ -> false);;

let rec abstra_upd_impl (_A1, _A2, _A3, _A4)
  n = (fun ai bi ->
        (match ai
          with LTa (x41a, x42a) ->
            (fun f_ () -> f_
              ((mtx_get (heap_DBMEntry _A4) (suc n) bi (x41a, zero_nata)) ())
              ())
              (fun x ->
                mtx_set (heap_DBMEntry _A4) (suc n) bi (x41a, zero_nata)
                  (min (ord_DBMEntry
                         (_A3, _A1.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.linordered_ab_semigroup_add_linordered_ab_monoid_add.linorder_linordered_ab_semigroup_add))
                    x (Lt x42a)))
          | LEa (x41a, x42a) ->
            (fun f_ () -> f_
              ((mtx_get (heap_DBMEntry _A4) (suc n) bi (x41a, zero_nata)) ())
              ())
              (fun x ->
                mtx_set (heap_DBMEntry _A4) (suc n) bi (x41a, zero_nata)
                  (min (ord_DBMEntry
                         (_A3, _A1.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.linordered_ab_semigroup_add_linordered_ab_monoid_add.linorder_linordered_ab_semigroup_add))
                    x (Le x42a)))
          | EQa (x41a, x42a) ->
            (fun f_ () -> f_
              ((mtx_get (heap_DBMEntry _A4) (suc n) bi (zero_nata, x41a)) ())
              ())
              (fun x ->
                (fun f_ () -> f_
                  ((mtx_get (heap_DBMEntry _A4) (suc n) bi (x41a, zero_nata))
                  ()) ())
                  (fun x_a ->
                    (fun f_ () -> f_
                      ((mtx_set (heap_DBMEntry _A4) (suc n) bi (zero_nata, x41a)
                         (min (ord_DBMEntry
                                (_A3, _A1.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.linordered_ab_semigroup_add_linordered_ab_monoid_add.linorder_linordered_ab_semigroup_add))
                           x (Le (uminus _A2 x42a))))
                      ()) ())
                      (fun x_b ->
                        mtx_set (heap_DBMEntry _A4) (suc n) x_b
                          (x41a, zero_nata)
                          (min (ord_DBMEntry
                                 (_A3, _A1.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.linordered_ab_semigroup_add_linordered_ab_monoid_add.linorder_linordered_ab_semigroup_add))
                            x_a (Le x42a)))))
          | GT (x41a, x42a) ->
            (fun f_ () -> f_
              ((mtx_get (heap_DBMEntry _A4) (suc n) bi (zero_nata, x41a)) ())
              ())
              (fun x ->
                mtx_set (heap_DBMEntry _A4) (suc n) bi (zero_nata, x41a)
                  (min (ord_DBMEntry
                         (_A3, _A1.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.linordered_ab_semigroup_add_linordered_ab_monoid_add.linorder_linordered_ab_semigroup_add))
                    x (Lt (uminus _A2 x42a))))
          | GE (x41a, x42a) ->
            (fun f_ () -> f_
              ((mtx_get (heap_DBMEntry _A4) (suc n) bi (zero_nata, x41a)) ())
              ())
              (fun x ->
                mtx_set (heap_DBMEntry _A4) (suc n) bi (zero_nata, x41a)
                  (min (ord_DBMEntry
                         (_A3, _A1.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.linordered_ab_semigroup_add_linordered_ab_monoid_add.linorder_linordered_ab_semigroup_add))
                    x (Le (uminus _A2 x42a))))));;

let rec abstr_upd_impl (_A1, _A2, _A3, _A4)
  n = (fun ai ->
        imp_nfoldli ai (fun _ -> (fun () -> true))
          (abstra_upd_impl (_A1, _A2, _A3, _A4) n));;

let rec abstr_FW_impl (_A1, _A2, _A3, _A4)
  n = (fun ai bi ->
        (fun f_ () -> f_ ((abstr_upd_impl (_A1, _A2, _A3, _A4) n ai bi) ()) ())
          (fw_impl
            ((linordered_ab_monoid_add_DBMEntry (_A1, _A3)),
              (heap_DBMEntry _A4))
            n));;

let rec check_conj_blocka _A
  prog pc =
    (if less_eq_nat (size_list prog) pc then None
      else (if equal_optiona (equal_instrc _A) (nth prog pc) (Some (INSTR HALT))
             then Some pc
             else (if equal_optiona (equal_instrc _A) (nth prog pc)
                        (Some (INSTR COPY)) &&
                        ((match nth prog (plus_nata pc one_nata)
                           with None -> false | Some (INSTR _) -> false
                           | Some (CEXP _) -> true) &&
                          equal_optiona (equal_instrc _A)
                            (nth prog
                              (plus_nata pc
                                (nat_of_integer (Big_int.big_int_of_int 2))))
                            (Some (INSTR AND)))
                    then check_conj_blocka _A prog
                           (plus_nata pc
                             (nat_of_integer (Big_int.big_int_of_int 3)))
                    else (if equal_optiona (equal_instrc _A) (nth prog pc)
                               (Some (INSTR COPY)) &&
                               ((match
                                  nth prog
                                    (plus_nata pc
                                      (nat_of_integer
(Big_int.big_int_of_int 2)))
                                  with None -> false | Some (INSTR _) -> false
                                  | Some (CEXP _) -> true) &&
                                 (equal_optiona (equal_instrc _A)
                                    (nth prog
                                      (plus_nata pc
(nat_of_integer (Big_int.big_int_of_int 3))))
                                    (Some (INSTR AND)) &&
                                   (match nth prog (plus_nata pc one_nata)
                                     with None -> false
                                     | Some (INSTR (JMPZ _)) -> true
                                     | Some (INSTR ADD) -> false
                                     | Some (INSTR NOT) -> false
                                     | Some (INSTR AND) -> false
                                     | Some (INSTR LT) -> false
                                     | Some (INSTR LE) -> false
                                     | Some (INSTR EQ) -> false
                                     | Some (INSTR (PUSH _)) -> false
                                     | Some (INSTR POP) -> false
                                     | Some (INSTR (LID _)) -> false
                                     | Some (INSTR STORE) -> false
                                     | Some (INSTR (STOREI (_, _))) -> false
                                     | Some (INSTR COPY) -> false
                                     | Some (INSTR CALL) -> false
                                     | Some (INSTR RETURN) -> false
                                     | Some (INSTR HALT) -> false
                                     | Some (INSTR (STOREC (_, _))) -> false
                                     | Some (INSTR (SETF _)) -> false
                                     | Some (CEXP _) -> false)))
                           then (match
                                  (nth prog (plus_nata pc one_nata),
                                    check_conj_blocka _A prog
                                      (plus_nata pc
(nat_of_integer (Big_int.big_int_of_int 4))))
                                  with (None, _) -> None
                                  | (Some (INSTR (JMPZ _)), None) -> None
                                  | (Some (INSTR (JMPZ pcb)), Some pca) ->
                                    (if equal_nata pcb pca then Some pcb
                                      else None)
                                  | (Some (INSTR ADD), _) -> None
                                  | (Some (INSTR NOT), _) -> None
                                  | (Some (INSTR AND), _) -> None
                                  | (Some (INSTR LT), _) -> None
                                  | (Some (INSTR LE), _) -> None
                                  | (Some (INSTR EQ), _) -> None
                                  | (Some (INSTR (PUSH _)), _) -> None
                                  | (Some (INSTR POP), _) -> None
                                  | (Some (INSTR (LID _)), _) -> None
                                  | (Some (INSTR STORE), _) -> None
                                  | (Some (INSTR (STOREI (_, _))), _) -> None
                                  | (Some (INSTR COPY), _) -> None
                                  | (Some (INSTR CALL), _) -> None
                                  | (Some (INSTR RETURN), _) -> None
                                  | (Some (INSTR HALT), _) -> None
                                  | (Some (INSTR (STOREC (_, _))), _) -> None
                                  | (Some (INSTR (SETF _)), _) -> None
                                  | (Some (CEXP _), _) -> None)
                           else None))));;

let rec check_conj_block
  p pca pc =
    (match nth p pca with None -> false | Some (INSTR _) -> false
      | Some (CEXP _) -> true) &&
      equal_optiona equal_nat
        (check_conj_blocka equal_int p (plus_nata pca one_nata)) (Some pc) ||
      (match nth p pca with None -> false | Some (INSTR _) -> false
        | Some (CEXP _) -> true) &&
        (equal_optiona (equal_instrc equal_int) (nth p (plus_nata pca one_nata))
           (Some (INSTR AND)) &&
          equal_optiona equal_nat
            (check_conj_blocka equal_int p
              (plus_nata pca (nat_of_integer (Big_int.big_int_of_int 2))))
            (Some pc));;

let rec mina _A
  (Set (x :: xs)) =
    fold (min _A.order_linorder.preorder_order.ord_preorder) xs x;;

let rec maxa _A
  (Set (x :: xs)) =
    fold (max _A.order_linorder.preorder_order.ord_preorder) xs x;;

let rec steps_approx
  n prog pc =
    (if equal_nata n zero_nata
      then (if less_nat pc (size_list prog) then insert equal_nat pc bot_set
             else bot_set)
      else (if less_eq_nat (size_list prog) pc then bot_set
             else (match nth prog pc with None -> insert equal_nat pc bot_set
                    | Some cmd ->
                      (let succs =
                         (match cmd
                           with INSTR (JMPZ pca) ->
                             insert equal_nat (plus_nata pc one_nata)
                               (insert equal_nat pca bot_set)
                           | INSTR ADD ->
                             insert equal_nat (plus_nata pc one_nata) bot_set
                           | INSTR NOT ->
                             insert equal_nat (plus_nata pc one_nata) bot_set
                           | INSTR AND ->
                             insert equal_nat (plus_nata pc one_nata) bot_set
                           | INSTR LT ->
                             insert equal_nat (plus_nata pc one_nata) bot_set
                           | INSTR LE ->
                             insert equal_nat (plus_nata pc one_nata) bot_set
                           | INSTR EQ ->
                             insert equal_nat (plus_nata pc one_nata) bot_set
                           | INSTR (PUSH _) ->
                             insert equal_nat (plus_nata pc one_nata) bot_set
                           | INSTR POP ->
                             insert equal_nat (plus_nata pc one_nata) bot_set
                           | INSTR (LID _) ->
                             insert equal_nat (plus_nata pc one_nata) bot_set
                           | INSTR STORE ->
                             insert equal_nat (plus_nata pc one_nata) bot_set
                           | INSTR (STOREI (_, _)) ->
                             insert equal_nat (plus_nata pc one_nata) bot_set
                           | INSTR COPY ->
                             insert equal_nat (plus_nata pc one_nata) bot_set
                           | INSTR CALL -> Set (upt zero_nata (size_list prog))
                           | INSTR RETURN ->
                             Set (upt zero_nata (size_list prog))
                           | INSTR HALT -> bot_set
                           | INSTR (STOREC (_, _)) ->
                             insert equal_nat (plus_nata pc one_nata) bot_set
                           | INSTR (SETF _) ->
                             insert equal_nat (plus_nata pc one_nata) bot_set
                           | CEXP _ ->
                             insert equal_nat (plus_nata pc one_nata) bot_set)
                         in
                        sup_set equal_nat (insert equal_nat pc bot_set)
                          (sup_seta equal_nat
                            (image (steps_approx (minus_nat n one_nata) prog)
                              succs))))));;

let rec conjunction_check
  p pc_s n =
    (let s = steps_approx n p pc_s in
     let sa =
       filter
         (fun pc ->
           (match nth p pc with None -> false | Some (INSTR _) -> false
             | Some (CEXP _) -> true))
         s
       in
      eq_set (card_UNIV_nat, equal_nat) sa bot_set ||
        check_conj_block p (mina linorder_nat sa) (maxa linorder_nat s));;

let rec conjunction_check2
  x = (fun trans prog max_steps ->
        list_all
          (list_all
            (list_all
              (fun (pc_g, (_, (_, _))) ->
                conjunction_check prog pc_g max_steps)))
          trans)
        x;;

let rec is_instr = function INSTR uu -> true
                   | CEXP v -> false;;

let rec time_indep_check
  prog pc n =
    ball (steps_approx n prog pc)
      (fun pca ->
        (if less_nat pca (size_list prog)
          then (match nth prog pca with None -> true | Some a -> is_instr a)
          else true));;

let rec time_indep_check2
  x = (fun trans prog max_steps ->
        list_all
          (list_all
            (list_all
              (fun (_, (_, (pc_u, _))) ->
                time_indep_check prog pc_u max_steps)))
          trans)
        x;;

let rec time_indep_check1
  x = (fun pred prog max_steps ->
        list_all (list_all (fun pc -> time_indep_check prog pc max_steps)) pred)
        x;;

let rec init p = map (fun _ -> zero_nata) (upt zero_nata p);;

let rec prog
  prog pc = (if less_nat pc (size_list prog) then nth prog pc else None);;

let rec stripfp p = comp (map_option stripf) p;;

let rec init_pred_check
  x = (fun p proga max_steps pred s_0 ->
        all_interval_nat
          (fun q ->
            (match
              exec (stripfp (prog proga)) max_steps
                (nth (nth pred q) (nth (init p) q), ([], (s_0, (true, [])))) []
              with None -> false | Some ((_, (_, (_, (true, _)))), _) -> true
              | Some ((_, (_, (_, (false, _)))), _) -> false))
          zero_nata p)
        x;;

let rec bounded _A
  bounds s =
    equal_nata (size_list s) (size_list bounds) &&
      all_interval_nat
        (fun i ->
          less _A (fst (nth bounds i)) (nth s i) &&
            less _A (nth s i) (snd (nth bounds i)))
        zero_nata (size_list s);;

let rec start_checks
  x = (fun p max_steps trans prog bounds pred s_0 ->
        [("Termination of predicates",
           init_pred_check p prog max_steps pred s_0);
          ("Boundedness", bounded ord_int bounds s_0);
          ("Predicates are independent of time",
            time_indep_check1 pred prog max_steps);
          ("Updates are independent of time",
            time_indep_check2 trans prog max_steps);
          ("Conjunction check", conjunction_check2 trans prog max_steps)])
        x;;

let rec find_max_nat
  n uu =
    (if equal_nata n zero_nata then zero_nata
      else (if uu (minus_nat n one_nata) then minus_nat n one_nata
             else find_max_nat (minus_nat n one_nata) uu));;

let rec stat_newnode x = (fun _ -> ()) x;;

let rec amtx_copy _A = array_copy _A;;

let rec amtx_dflt _A n m v = make _A (times_nat n m) (fun _ -> v);;

let rec norm_lower _A e t = (if dbm_lt _A e (Lt t) then Lt t else e);;

let rec norm_upper _A e t = (if dbm_lt _A (Le t) e then INF else e);;

let rec uPPAAL_Reachability_Problem_precompiled_start_state_axioms
  x = (fun p max_steps trans prog bounds pred s_0 ->
        init_pred_check p prog max_steps pred s_0 &&
          (bounded ord_int bounds s_0 &&
            (time_indep_check1 pred prog max_steps &&
              (time_indep_check2 trans prog max_steps &&
                conjunction_check2 trans prog max_steps))))
        x;;

let rec check_pre
  p m inv pred trans prog =
    equal_nata (size_list inv) p &&
      (equal_nata (size_list trans) p &&
        (equal_nata (size_list pred) p &&
          (all_interval_nat
             (fun i ->
               equal_nata (size_list (nth pred i)) (size_list (nth trans i)) &&
                 equal_nata (size_list (nth inv i)) (size_list (nth trans i)))
             zero_nata p &&
            (list_all
               (fun t ->
                 list_all
                   (list_all (fun (_, (_, (_, l))) -> less_nat l (size_list t)))
                   t)
               trans &&
              (less_nat zero_nata p &&
                (less_nat zero_nata m &&
                  (all_interval_nat (fun i -> not (null (nth trans i)))
                     zero_nata p &&
                    (all_interval_nat
                       (fun q -> not (null (nth (nth trans q) zero_nata)))
                       zero_nata p &&
                      (ball (clkp_seta inv prog)
                         (fun (_, a) -> less_eq_int zero_inta a) &&
                        (eq_set (card_UNIV_nat, equal_nat) (clk_set inv prog)
                           (Set (upt one_nata (suc m))) &&
                          check_resets prog))))))))));;

let rec uPPAAL_Reachability_Problem_precompiled
  p m inv pred trans prog = check_pre p m inv pred trans prog;;

let rec uPPAAL_Reachability_Problem_precompiled_start_state
  p m max_steps inv trans prog bounds pred s_0 =
    uPPAAL_Reachability_Problem_precompiled p m inv pred trans prog &&
      uPPAAL_Reachability_Problem_precompiled_start_state_axioms p max_steps
        trans prog bounds pred s_0;;

let rec sup_option _A
  x y = match x, y with Some x, Some y -> Some (sup _A x y)
    | x, None -> x
    | None, y -> y;;

let rec find_resets_start
  prog pc =
    (if less_nat pc (size_list prog)
      then (match nth prog pc with None -> None | Some (INSTR (JMPZ _)) -> None
             | Some (INSTR ADD) -> None | Some (INSTR NOT) -> None
             | Some (INSTR AND) -> None | Some (INSTR LT) -> None
             | Some (INSTR LE) -> None | Some (INSTR EQ) -> None
             | Some (INSTR (PUSH _)) -> None | Some (INSTR POP) -> None
             | Some (INSTR (LID _)) -> None | Some (INSTR STORE) -> None
             | Some (INSTR (STOREI (_, _))) -> None | Some (INSTR COPY) -> None
             | Some (INSTR CALL) -> None | Some (INSTR RETURN) -> None
             | Some (INSTR HALT) -> None
             | Some (INSTR (STOREC (_, _))) ->
               sup_option sup_nat (Some pc)
                 (find_resets_start prog (plus_nata pc one_nata))
             | Some (INSTR (SETF _)) -> None | Some (CEXP _) -> None)
      else None);;

let rec collect_storea
  prog pc =
    (match find_resets_start prog pc with None -> bot_set
      | Some pca ->
        sup_seta (equal_prod equal_nat equal_int)
          (image
            (fun a ->
              (match a with None -> bot_set | Some (INSTR (JMPZ _)) -> bot_set
                | Some (INSTR ADD) -> bot_set | Some (INSTR NOT) -> bot_set
                | Some (INSTR AND) -> bot_set | Some (INSTR LT) -> bot_set
                | Some (INSTR LE) -> bot_set | Some (INSTR EQ) -> bot_set
                | Some (INSTR (PUSH _)) -> bot_set | Some (INSTR POP) -> bot_set
                | Some (INSTR (LID _)) -> bot_set
                | Some (INSTR STORE) -> bot_set
                | Some (INSTR (STOREI (_, _))) -> bot_set
                | Some (INSTR COPY) -> bot_set | Some (INSTR CALL) -> bot_set
                | Some (INSTR RETURN) -> bot_set | Some (INSTR HALT) -> bot_set
                | Some (INSTR (STOREC (c, x))) ->
                  insert (equal_prod equal_nat equal_int) (c, x) bot_set
                | Some (INSTR (SETF _)) -> bot_set | Some (CEXP _) -> bot_set))
            (image (nth prog) (Set (upt pc (suc pca))))));;

let rec collect_cexpa
  max_steps prog pc =
    sup_seta (equal_acconstraint equal_nat equal_int)
      (image
        (fun a ->
          (match a with None -> bot_set | Some (INSTR _) -> bot_set
            | Some (CEXP ac) ->
              insert (equal_acconstraint equal_nat equal_int) ac bot_set))
        (image (nth prog) (steps_approx max_steps prog pc)));;

let rec clkp_set
  max_steps inv trans prog i l =
    sup_set (equal_prod equal_nat equal_int)
      (collect_clock_pairs (nth (nth inv i) l))
      (sup_seta (equal_prod equal_nat equal_int)
        (image
          (fun (g, _) -> image constraint_pair (collect_cexpa max_steps prog g))
          (Set (nth (nth trans i) l))));;

let rec find_next_halt
  prog pc =
    (if less_nat pc (size_list prog)
      then (match nth prog pc
             with None -> find_next_halt prog (plus_nata pc one_nata)
             | Some (INSTR (JMPZ _)) ->
               find_next_halt prog (plus_nata pc one_nata)
             | Some (INSTR ADD) -> find_next_halt prog (plus_nata pc one_nata)
             | Some (INSTR NOT) -> find_next_halt prog (plus_nata pc one_nata)
             | Some (INSTR AND) -> find_next_halt prog (plus_nata pc one_nata)
             | Some (INSTR LT) -> find_next_halt prog (plus_nata pc one_nata)
             | Some (INSTR LE) -> find_next_halt prog (plus_nata pc one_nata)
             | Some (INSTR EQ) -> find_next_halt prog (plus_nata pc one_nata)
             | Some (INSTR (PUSH _)) ->
               find_next_halt prog (plus_nata pc one_nata)
             | Some (INSTR POP) -> find_next_halt prog (plus_nata pc one_nata)
             | Some (INSTR (LID _)) ->
               find_next_halt prog (plus_nata pc one_nata)
             | Some (INSTR STORE) -> find_next_halt prog (plus_nata pc one_nata)
             | Some (INSTR (STOREI (_, _))) ->
               find_next_halt prog (plus_nata pc one_nata)
             | Some (INSTR COPY) -> find_next_halt prog (plus_nata pc one_nata)
             | Some (INSTR CALL) -> find_next_halt prog (plus_nata pc one_nata)
             | Some (INSTR RETURN) ->
               find_next_halt prog (plus_nata pc one_nata)
             | Some (INSTR HALT) -> Some pc
             | Some (INSTR (STOREC (_, _))) ->
               find_next_halt prog (plus_nata pc one_nata)
             | Some (INSTR (SETF _)) ->
               find_next_halt prog (plus_nata pc one_nata)
             | Some (CEXP _) -> find_next_halt prog (plus_nata pc one_nata))
      else None);;

let rec guaranteed_execution_cond _A
  prog pc_s n =
    (match find_next_halt prog pc_s with None -> false
      | Some pc_t ->
        all_interval_nat
          (fun pc ->
            not (is_none (nth prog pc)) &&
              (not (member (equal_option (equal_instrc _A)) (nth prog pc)
                     (image (fun a -> Some a)
                       (image (fun a -> INSTR a)
                         (insert equal_instr STORE
                           (insert equal_instr HALT
                             (insert equal_instr POP
                               (insert equal_instr CALL
                                 (insert equal_instr RETURN
                                   (insert equal_instr AND
                                     (insert equal_instr NOT
                                       (insert equal_instr ADD
 (insert equal_instr LT
   (insert equal_instr LE (insert equal_instr EQ bot_set)))))))))))))) &&
                (match nth prog pc with None -> true
                  | Some (INSTR (JMPZ _)) -> true | Some (INSTR ADD) -> true
                  | Some (INSTR NOT) -> true | Some (INSTR AND) -> true
                  | Some (INSTR LT) -> true | Some (INSTR LE) -> true
                  | Some (INSTR EQ) -> true | Some (INSTR (PUSH _)) -> true
                  | Some (INSTR POP) -> true | Some (INSTR (LID _)) -> true
                  | Some (INSTR STORE) -> true
                  | Some (INSTR (STOREI (_, _))) -> true
                  | Some (INSTR COPY) -> true | Some (INSTR CALL) -> true
                  | Some (INSTR RETURN) -> true | Some (INSTR HALT) -> true
                  | Some (INSTR (STOREC (_, d))) -> equal_inta d zero_inta
                  | Some (INSTR (SETF _)) -> true | Some (CEXP _) -> true)))
          pc_s pc_t &&
          (all_interval_nat
             (fun pc ->
               (match nth prog pc with None -> true
                 | Some (INSTR (JMPZ pca)) ->
                   less_nat pc pca && less_eq_nat pca pc_t
                 | Some (INSTR ADD) -> true | Some (INSTR NOT) -> true
                 | Some (INSTR AND) -> true | Some (INSTR LT) -> true
                 | Some (INSTR LE) -> true | Some (INSTR EQ) -> true
                 | Some (INSTR (PUSH _)) -> true | Some (INSTR POP) -> true
                 | Some (INSTR (LID _)) -> true | Some (INSTR STORE) -> true
                 | Some (INSTR (STOREI (_, _))) -> true
                 | Some (INSTR COPY) -> true | Some (INSTR CALL) -> true
                 | Some (INSTR RETURN) -> true | Some (INSTR HALT) -> true
                 | Some (INSTR (STOREC (_, _))) -> true
                 | Some (INSTR (SETF _)) -> true | Some (CEXP _) -> true))
             pc_s pc_t &&
            less_nat (minus_nat pc_t pc_s) n));;

let rec minus_set _A
  a x1 = match a, x1 with
    a, Coset xs -> Set (filtera (fun x -> member _A x a) xs)
    | a, Set xs -> fold (remove _A) xs a;;

let rec uPPAAL_Reachability_Problem_precompiled_ceiling_axioms
  p m max_steps inv trans prog k =
    all_interval_nat
      (fun i ->
        all_interval_nat
          (fun l ->
            ball (clkp_set max_steps inv trans prog i l)
              (fun (x, ma) ->
                less_eq_int ma (int_of_nat (nth (nth (nth k i) l) x))))
          zero_nata (size_list (nth trans i)))
      zero_nata p &&
      all_interval_nat
        (fun i ->
          all_interval_nat
            (fun l ->
              ball (collect_clock_pairs (nth (nth inv i) l))
                (fun (x, ma) ->
                  less_eq_int ma (int_of_nat (nth (nth (nth k i) l) x))))
            zero_nata (size_list (nth trans i)))
        zero_nata p &&
      (all_interval_nat
         (fun i ->
           all_interval_nat
             (fun l ->
               list_all
                 (fun (_, (_, (r, la))) ->
                   ball (minus_set equal_nat
                          (Set (upt zero_nata (plus_nata m one_nata)))
                          (image fst (collect_storea prog r)))
                     (fun c ->
                       less_eq_nat (nth (nth (nth k i) la) c)
                         (nth (nth (nth k i) l) c)))
                 (nth (nth trans i) l))
             zero_nata (size_list (nth trans i)))
         zero_nata p &&
        equal_nata (size_list k) p) &&
      (all_interval_nat
         (fun i -> equal_nata (size_list (nth k i)) (size_list (nth trans i)))
         zero_nata p &&
         list_all
           (list_all
             (fun xxs -> equal_nata (size_list xxs) (plus_nata m one_nata)))
           k &&
        (all_interval_nat
           (fun i ->
             all_interval_nat
               (fun l -> equal_nata (nth (nth (nth k i) l) zero_nata) zero_nata)
               zero_nata (size_list (nth trans i)))
           zero_nata p &&
          all_interval_nat
            (fun i ->
              all_interval_nat
                (fun l ->
                  list_all
                    (fun (_, (_, (r, _))) ->
                      guaranteed_execution_cond equal_int prog r max_steps)
                    (nth (nth trans i) l))
                zero_nata (size_list (nth trans i)))
            zero_nata p));;

let rec check_ceiling
  p m max_steps inv trans prog k =
    uPPAAL_Reachability_Problem_precompiled_ceiling_axioms p m max_steps inv
      trans prog k;;

let rec uPPAAL_Reachability_Problem_precompiled_ceiling
  p m max_steps inv pred trans prog k =
    check_pre p m inv pred trans prog &&
      check_ceiling p m max_steps inv trans prog k;;

let rec uPPAAL_Reachability_Problem_precompiled_axioms
  trans na =
    list_all
      (list_all
        (list_all
          (fun (_, a) ->
            (let (aa, _) = a in
              pred_act equal_nat (fun ab -> less_nat ab na) aa))))
      trans;;

let rec uPPAAL_Reachability_Problem_precompileda
  p m max_steps inv trans prog bounds pred s_0 na k =
    uPPAAL_Reachability_Problem_precompiled_start_state p m max_steps inv trans
      prog bounds pred s_0 &&
      (uPPAAL_Reachability_Problem_precompiled_ceiling p m max_steps inv pred
         trans prog k &&
        uPPAAL_Reachability_Problem_precompiled_axioms trans na);;

let rec actions_by_state
  i = fold (fun t acc ->
             list_update acc (fst (snd t)) ((i, t) :: nth acc (fst (snd t))));;

let rec all_actions_by_state_impl
  upt_p empty_ran i l =
    fold (fun ia -> actions_by_state ia (sub (sub i ia) (nth l ia))) upt_p
      empty_ran;;

let rec run_impl
  max_steps program pc s =
    exec program max_steps (pc, ([], (s, (true, [])))) [];;

let rec make_reset_impl
  max_steps program m1 s =
    (match run_impl max_steps program m1 s with None -> []
      | Some ((_, (_, (_, (_, r1)))), _) -> r1);;

let rec check_pred_impl
  p max_steps pred program bnds l s =
    all_interval_nat
      (fun q ->
        (match run_impl max_steps program (nth (nth pred q) (nth l q)) s
          with None -> false
          | Some ((_, (_, (_, (f, _)))), _) ->
            f && all_interval_nat
                   (fun i ->
                     less_int (fst (sub bnds i)) (nth s i) &&
                       less_int (nth s i) (snd (sub bnds i)))
                   zero_nata (size_list s)))
      zero_nata p;;

let rec make_cconstr_impl
  program pcs =
    map_filter
      (fun pc ->
        (match program pc with None -> None
          | Some a -> (match a with INSTR _ -> None | CEXP aa -> Some aa)))
      pcs;;

let rec check_g_impl
  max_steps programf program pc s =
    (match run_impl max_steps programf pc s with None -> None
      | Some ((_, (_, (_, (true, _)))), pcs) ->
        Some (make_cconstr_impl program pcs)
      | Some ((_, (_, (_, (false, _)))), _) -> None);;

let rec pairs_by_action_impl
  p max_steps pred pf pt porig bnds =
    (fun (l, s) out ->
      comp concat
        (map (fun (i, (g1, (_, (m1, l1)))) ->
               map_filter
                 (fun (j, a) ->
                   (let (g2, aa) = a in
                    let (ab, (m2, l2)) = aa in
                     (if equal_nata i j then None
                       else (match
                              (check_g_impl max_steps pt porig g1 s,
                                check_g_impl max_steps pt porig g2 s)
                              with (None, _) -> None | (Some _, None) -> None
                              | (Some cc1, Some cc2) ->
                                (match run_impl max_steps pf m2 s
                                  with None -> None
                                  | Some ((_, (_, (s1, (_, r2)))), _) ->
                                    (match run_impl max_steps pf m1 s1
                                      with None -> None
                                      | Some ((_, (_, (sa, (_, _)))), _) ->
(if check_pred_impl p max_steps pred pf bnds
      (list_update (list_update l i l1) j l2) sa
  then Some (cc1 @ cc2,
              (ab, (make_reset_impl max_steps pf m1 s @ r2,
                     (list_update (list_update l i l1) j l2, sa))))
  else None)))))))
                 out)));;

let rec trans_i_from_impl
  p max_steps pred bounds programf programt program bnds trans_i_array =
    (fun (l, s) i ->
      map_filter
        (fun (g, a) ->
          (let (aa, (m, la)) = a in
            (match check_g_impl max_steps programt program g s with None -> None
              | Some cc ->
                (match run_impl max_steps programf m s with None -> None
                  | Some ((_, (_, (sa, (_, r)))), _) ->
                    (if check_pred_impl p max_steps pred programf
                          (IArray bounds) (list_update l i la) sa
                      then Some (cc, (aa, (r, (list_update l i la, sa))))
                      else None)))))
        (sub (sub trans_i_array i) (nth l i)));;

let rec trans_out_map
  trans =
    map (map (comp (map (fun (g, a) ->
                          (let (aa, (m, l)) = a in
                           let Out ab = aa in
                            (g, (ab, (m, l))))))
               (filtera
                 (fun a ->
                   (match a with (_, (In _, (_, _))) -> false
                     | (_, (Out _, (_, _))) -> true
                     | (_, (Sil _, (_, _))) -> false)))))
      trans;;

let rec trans_in_map
  trans =
    map (map (comp (map (fun (g, a) ->
                          (let (aa, (m, l)) = a in
                           let In ab = aa in
                            (g, (ab, (m, l))))))
               (filtera
                 (fun a ->
                   (match a with (_, (In _, (_, _))) -> true
                     | (_, (Out _, (_, _))) -> false
                     | (_, (Sil _, (_, _))) -> false)))))
      trans;;

let rec trans_i_map
  trans =
    map (map (map_filter
               (fun (g, a) ->
                 (let (aa, (m, l)) = a in
                   (match aa with In _ -> None | Out _ -> None
                     | Sil ab -> Some (g, (ab, (m, l))))))))
      trans;;

let rec make_string (_A1, _A2, _A3)
  show_clock show_num e i j =
    (if equal_nata i j
      then (if less_DBMEntry
                 _A1.linordered_cancel_ab_monoid_add_linordered_ab_group_add.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.linordered_ab_semigroup_add_linordered_ab_monoid_add.linorder_linordered_ab_semigroup_add
                 e (zero_DBMEntrya
                     _A1.ordered_ab_group_add_linordered_ab_group_add.ab_group_add_ordered_ab_group_add.group_add_ab_group_add.monoid_add_group_add.zero_monoid_add)
             then Some [Chara (true, false, true, false, false, false, true,
                                false);
                         Chara (true, false, true, true, false, false, true,
                                 false);
                         Chara (false, false, false, false, true, false, true,
                                 false);
                         Chara (false, false, true, false, true, false, true,
                                 false);
                         Chara (true, false, false, true, true, false, true,
                                 false)]
             else None)
      else (if equal_nata i zero_nata
             then (match e
                    with Le a ->
                      (if eq _A2 a
                            (zero _A1.ordered_ab_group_add_linordered_ab_group_add.ab_group_add_ordered_ab_group_add.group_add_ab_group_add.monoid_add_group_add.zero_monoid_add)
                        then None
                        else Some (show_clock j @
                                    [Chara (false, false, false, false, false,
     true, false, false);
                                      Chara
(false, true, true, true, true, true, false, false);
                                      Chara
(true, false, true, true, true, true, false, false);
                                      Chara
(false, false, false, false, false, true, false, false)] @
                                      show_num
(uminus
  _A1.ordered_ab_group_add_linordered_ab_group_add.ab_group_add_ordered_ab_group_add.group_add_ab_group_add.uminus_group_add
  a)))
                    | Lt a ->
                      Some (show_clock j @
                             [Chara (false, false, false, false, false, true,
                                      false, false);
                               Chara (false, true, true, true, true, true,
                                       false, false);
                               Chara (false, false, false, false, false, true,
                                       false, false)] @
                               show_num
                                 (uminus
                                   _A1.ordered_ab_group_add_linordered_ab_group_add.ab_group_add_ordered_ab_group_add.group_add_ab_group_add.uminus_group_add
                                   a))
                    | INF -> None)
             else (if equal_nata j zero_nata
                    then (match e
                           with Le a ->
                             Some (show_clock i @
                                    [Chara (false, false, false, false, false,
     true, false, false);
                                      Chara
(false, false, true, true, true, true, false, false);
                                      Chara
(true, false, true, true, true, true, false, false);
                                      Chara
(false, false, false, false, false, true, false, false)] @
                                      show_num a)
                           | Lt a ->
                             Some (show_clock i @
                                    [Chara (false, false, false, false, false,
     true, false, false);
                                      Chara
(false, false, true, true, true, true, false, false);
                                      Chara
(false, false, false, false, false, true, false, false)] @
                                      show_num a)
                           | INF -> None)
                    else (match e
                           with Le a ->
                             Some (show_clock i @
                                    [Chara (false, false, false, false, false,
     true, false, false);
                                      Chara
(true, false, true, true, false, true, false, false);
                                      Chara
(false, false, false, false, false, true, false, false)] @
                                      show_clock j @
[Chara (false, false, false, false, false, true, false, false);
  Chara (false, false, true, true, true, true, false, false);
  Chara (true, false, true, true, true, true, false, false);
  Chara (false, false, false, false, false, true, false, false)] @
  show_num a)
                           | Lt a ->
                             Some (show_clock i @
                                    [Chara (false, false, false, false, false,
     true, false, false);
                                      Chara
(true, false, true, true, false, true, false, false);
                                      Chara
(false, false, false, false, false, true, false, false)] @
                                      show_clock j @
[Chara (false, false, false, false, false, true, false, false);
  Chara (false, false, true, true, true, true, false, false);
  Chara (false, false, false, false, false, true, false, false)] @
  show_num a)
                           | INF -> None))));;

let rec intersperse
  sep x1 = match sep, x1 with
    sep, x :: y :: xs -> x :: sep :: intersperse sep (y :: xs)
    | uu, [] -> []
    | uu, [v] -> [v];;

let rec dbm_list_to_string (_A1, _A2, _A3)
  n show_clock show_num xs =
    app (comp (comp (comp (comp concat
                            (intersperse
                              [Chara (false, false, true, true, false, true,
                                       false, false);
                                Chara (false, false, false, false, false, true,
false, false)]))
                      rev)
                snd)
          snd)
      (fold (fun e (i, (j, acc)) ->
              (let v = make_string (_A1, _A2, _A3) show_clock show_num e i j in
               let ja = modulo_nat (plus_nata j one_nata) (plus_nata n one_nata)
                 in
               let ia =
                 (if equal_nata ja zero_nata then plus_nata i one_nata else i)
                 in
                (match v with None -> (ia, (ja, acc))
                  | Some s -> (ia, (ja, s :: acc)))))
        xs (zero_nata, (zero_nata, [])));;

let rec dbm_to_list_impl (_A1, _A2)
  n = (fun xi ->
        (fun f_ () -> f_
          ((imp_fora zero_nata (suc n)
             (fun xc ->
               imp_fora zero_nata (suc n)
                 (fun xe sigma ->
                   (fun f_ () -> f_ ((mtx_get _A2 (suc n) xi (xc, xe)) ()) ())
                     (fun x_e -> (fun () -> (x_e :: sigma)))))
             [])
          ()) ())
          (fun x -> (fun () -> (op_list_rev x))));;

let rec show_dbm_impl (_A1, _A2, _A3)
  n show_clock show_num =
    (fun xi ->
      (fun f_ () -> f_
        ((dbm_to_list_impl
           ((linordered_ab_monoid_add_DBMEntry
              (_A1.linordered_cancel_ab_monoid_add_linordered_ab_group_add,
                _A2)),
             (heap_DBMEntry _A3))
           n xi)
        ()) ())
        (fun x ->
          (fun () ->
            (dbm_list_to_string (_A1, _A2, _A3) n show_clock show_num x))));;

let rec tracei (_B1, _B2, _B3, _B4)
  n show_state show_clock typea =
    (fun (l, m) ->
      (let st = show_state l in
        (fun f_ () -> f_
          ((show_dbm_impl (_B1, _B2, _B3) n show_clock
             (fun x -> shows_prec _B4 zero_nata x []) m)
          ()) ())
          (fun ma ->
            (let s =
               typea @
                 [Chara (false, true, false, true, true, true, false, false);
                   Chara (false, false, false, false, false, true, false,
                           false);
                   Chara (false, false, false, true, false, true, false,
                           false)] @
                   st @ [Chara (false, false, true, true, false, true, false,
                                 false);
                          Chara (false, false, false, false, false, true, false,
                                  false);
                          Chara (false, false, true, true, true, true, false,
                                  false)] @
                          ma @ [Chara (false, true, true, true, true, true,
false, false);
                                 Chara (true, false, false, true, false, true,
 false, false)]
               in
             let sa = implode s in
             let _ = println sa in
              (fun () -> ())))));;

let rec repair_pair_impl (_A1, _A2)
  n = (fun ai bia bi ->
        (fun f_ () -> f_ ((fwi_impl (_A1, _A2) n ai bi) ()) ())
          (fun x -> fwi_impl (_A1, _A2) n x bia));;

let rec reset_canonical_upd_impl (_A1, _A2, _A3)
  n = (fun ai bib bia bi ->
        (fun f_ () -> f_
          ((mtx_set (heap_DBMEntry _A3) (suc n) ai (bia, zero_nata) (Le bi)) ())
          ())
          (fun x ->
            (fun f_ () -> f_
              ((mtx_set (heap_DBMEntry _A3) (suc n) x (zero_nata, bia)
                 (Le (uminus _A2 bi)))
              ()) ())
              (imp_fora one_nata (plus_nata bib one_nata)
                (fun xb sigma ->
                  (if equal_nata xb bia then (fun () -> sigma)
                    else (fun f_ () -> f_
                           ((mtx_get (heap_DBMEntry _A3) (suc n) sigma
                              (zero_nata, xb))
                           ()) ())
                           (fun x_d ->
                             (fun f_ () -> f_
                               ((mtx_get (heap_DBMEntry _A3) (suc n) sigma
                                  (xb, zero_nata))
                               ()) ())
                               (fun x_e ->
                                 (fun f_ () -> f_
                                   ((mtx_set (heap_DBMEntry _A3) (suc n) sigma
                                      (bia, xb)
                                      (plus_DBMEntrya _A1 (Le bi) x_d))
                                   ()) ())
                                   (fun x_f ->
                                     mtx_set (heap_DBMEntry _A3) (suc n) x_f
                                       (xb, bia)
                                       (plus_DBMEntrya _A1 (Le (uminus _A2 bi))
 x_e)))))))));;

let rec up_canonical_upd_impl (_A1, _A2)
  n = (fun ai bi ->
        imp_fora one_nata (plus_nata bi one_nata)
          (fun xa sigma ->
            mtx_set (heap_DBMEntry _A2) (suc n) sigma (xa, zero_nata) INF)
          ai);;

let rec dbm_add_int x0 uu = match x0, uu with INF, uu -> INF
                      | Le v, INF -> INF
                      | Lt v, INF -> INF
                      | Le a, Le b -> Le (plus_inta a b)
                      | Le a, Lt b -> Lt (plus_inta a b)
                      | Lt a, Le b -> Lt (plus_inta a b)
                      | Lt a, Lt b -> Lt (plus_inta a b);;

let rec fw_upd_impl_int
  n = (fun ai bib bia bi ->
        (fun f_ () -> f_
          ((mtx_get (heap_DBMEntry heap_int) (suc n) ai (bia, bi)) ()) ())
          (fun x ->
            (fun f_ () -> f_
              ((mtx_get (heap_DBMEntry heap_int) (suc n) ai (bia, bib)) ()) ())
              (fun xa ->
                (fun f_ () -> f_
                  ((mtx_get (heap_DBMEntry heap_int) (suc n) ai (bib, bi)) ())
                  ())
                  (fun xb ->
                    mtx_set (heap_DBMEntry heap_int) (suc n) ai (bia, bi)
                      (min (ord_DBMEntry (equal_int, linorder_int)) x
                        (dbm_add_int xa xb))))));;

let rec fw_impl_int
  n = imp_fora zero_nata (plus_nata n one_nata)
        (fun xb ->
          imp_fora zero_nata (plus_nata n one_nata)
            (fun xd ->
              imp_fora zero_nata (plus_nata n one_nata)
                (fun xf sigma -> fw_upd_impl_int n sigma xb xd xf)));;

let rec shows_prec_prod _A _B = showsp_prod (shows_prec _A) (shows_prec _B);;

let rec dbm_subset_impl (_A1, _A2, _A3)
  n = (fun ai bi ->
        imp_for zero_nata (suc n) (fun a -> (fun () -> a))
          (fun xb _ ->
            imp_for zero_nata (suc n) (fun a -> (fun () -> a))
              (fun xe _ ->
                (fun f_ () -> f_
                  ((mtx_get (heap_DBMEntry _A3) (suc n) ai (xb, xe)) ()) ())
                  (fun x_f ->
                    (fun f_ () -> f_
                      ((mtx_get (heap_DBMEntry _A3) (suc n) bi (xb, xe)) ()) ())
                      (fun x_g ->
                        (fun () ->
                          (less_eq_DBMEntry
                            (_A2, _A1.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.linordered_ab_semigroup_add_linordered_ab_monoid_add.linorder_linordered_ab_semigroup_add)
                            x_f x_g)))))
              true)
          true);;

let rec check_diag_impla (_A1, _A2)
  n = (fun ai bi ->
        imp_for zero_nata (suc ai) (fun sigma -> (fun () -> (not sigma)))
          (fun xb sigma ->
            (fun f_ () -> f_ ((mtx_get (heap_DBMEntry _A2) (suc n) bi (xb, xb))
              ()) ())
              (fun x ->
                (fun () ->
                  (less_DBMEntry
                     _A1.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.linordered_ab_semigroup_add_linordered_ab_monoid_add.linorder_linordered_ab_semigroup_add
                     x (Le (zero _A1.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.ordered_comm_monoid_add_linordered_ab_monoid_add.comm_monoid_add_ordered_comm_monoid_add.monoid_add_comm_monoid_add.zero_monoid_add)) ||
                    sigma))))
          false);;

let rec check_diag_impl (_A1, _A2)
  n = (fun xi ->
        imp_for zero_nata (suc n) (fun sigma -> (fun () -> (not sigma)))
          (fun xc sigma ->
            (fun f_ () -> f_ ((mtx_get (heap_DBMEntry _A2) (suc n) xi (xc, xc))
              ()) ())
              (fun x ->
                (fun () ->
                  (less_DBMEntry
                     _A1.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.linordered_ab_semigroup_add_linordered_ab_monoid_add.linorder_linordered_ab_semigroup_add
                     x (Le (zero _A1.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.ordered_comm_monoid_add_linordered_ab_monoid_add.comm_monoid_add_ordered_comm_monoid_add.monoid_add_comm_monoid_add.zero_monoid_add)) ||
                    sigma))))
          false);;

let rec norm_upd_impl (_A1, _A2)
  n = (fun ai bia bi ->
        (fun f_ () -> f_
          ((mtx_get (heap_DBMEntry _A2) (suc n) ai (zero_nata, zero_nata)) ())
          ())
          (fun x ->
            (fun f_ () -> f_
              ((mtx_set (heap_DBMEntry _A2) (suc n) ai (zero_nata, zero_nata)
                 (norm_lower
                   _A1.linordered_cancel_ab_monoid_add_linordered_ab_group_add.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.linordered_ab_semigroup_add_linordered_ab_monoid_add.linorder_linordered_ab_semigroup_add
                   (norm_upper
                     _A1.linordered_cancel_ab_monoid_add_linordered_ab_group_add.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.linordered_ab_semigroup_add_linordered_ab_monoid_add.linorder_linordered_ab_semigroup_add
                     x (zero _A1.ordered_ab_group_add_linordered_ab_group_add.ab_group_add_ordered_ab_group_add.group_add_ab_group_add.monoid_add_group_add.zero_monoid_add))
                   (zero _A1.ordered_ab_group_add_linordered_ab_group_add.ab_group_add_ordered_ab_group_add.group_add_ab_group_add.monoid_add_group_add.zero_monoid_add)))
              ()) ())
              (fun xa ->
                (fun f_ () -> f_
                  ((imp_fora one_nata (suc bi)
                     (fun xc sigma ->
                       (fun f_ () -> f_
                         ((mtx_get (heap_DBMEntry _A2) (suc n) sigma
                            (zero_nata, xc))
                         ()) ())
                         (fun xb ->
                           mtx_set (heap_DBMEntry _A2) (suc n) sigma
                             (zero_nata, xc)
                             (norm_lower
                               _A1.linordered_cancel_ab_monoid_add_linordered_ab_group_add.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.linordered_ab_semigroup_add_linordered_ab_monoid_add.linorder_linordered_ab_semigroup_add
                               (norm_upper
                                 _A1.linordered_cancel_ab_monoid_add_linordered_ab_group_add.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.linordered_ab_semigroup_add_linordered_ab_monoid_add.linorder_linordered_ab_semigroup_add
                                 xb (zero _A1.ordered_ab_group_add_linordered_ab_group_add.ab_group_add_ordered_ab_group_add.group_add_ab_group_add.monoid_add_group_add.zero_monoid_add))
                               (uminus
                                 _A1.ordered_ab_group_add_linordered_ab_group_add.ab_group_add_ordered_ab_group_add.group_add_ab_group_add.uminus_group_add
                                 (sub bia xc)))))
                     xa)
                  ()) ())
                  (imp_fora one_nata (suc bi)
                    (fun xb sigma ->
                      (fun f_ () -> f_
                        ((mtx_get (heap_DBMEntry _A2) (suc n) sigma
                           (xb, zero_nata))
                        ()) ())
                        (fun xc ->
                          (fun f_ () -> f_
                            ((mtx_set (heap_DBMEntry _A2) (suc n) sigma
                               (xb, zero_nata)
                               (norm_lower
                                 _A1.linordered_cancel_ab_monoid_add_linordered_ab_group_add.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.linordered_ab_semigroup_add_linordered_ab_monoid_add.linorder_linordered_ab_semigroup_add
                                 (norm_upper
                                   _A1.linordered_cancel_ab_monoid_add_linordered_ab_group_add.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.linordered_ab_semigroup_add_linordered_ab_monoid_add.linorder_linordered_ab_semigroup_add
                                   xc (sub bia xb))
                                 (zero _A1.ordered_ab_group_add_linordered_ab_group_add.ab_group_add_ordered_ab_group_add.group_add_ab_group_add.monoid_add_group_add.zero_monoid_add)))
                            ()) ())
                            (imp_fora one_nata (suc bi)
                              (fun xe sigmaa ->
                                (fun f_ () -> f_
                                  ((mtx_get (heap_DBMEntry _A2) (suc n) sigmaa
                                     (xb, xe))
                                  ()) ())
                                  (fun xd ->
                                    mtx_set (heap_DBMEntry _A2) (suc n) sigmaa
                                      (xb, xe)
                                      (norm_lower
_A1.linordered_cancel_ab_monoid_add_linordered_ab_group_add.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.linordered_ab_semigroup_add_linordered_ab_monoid_add.linorder_linordered_ab_semigroup_add
(norm_upper
  _A1.linordered_cancel_ab_monoid_add_linordered_ab_group_add.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.linordered_ab_semigroup_add_linordered_ab_monoid_add.linorder_linordered_ab_semigroup_add
  xd (sub bia xb))
(uminus
  _A1.ordered_ab_group_add_linordered_ab_group_add.ab_group_add_ordered_ab_group_add.group_add_ab_group_add.uminus_group_add
  (sub bia xe))))))))))));;

let rec and_entry_impl
  n = (fun ai bib bia bi ->
        (fun f_ () -> f_
          ((mtx_get (heap_DBMEntry heap_int) (suc n) bi (ai, bib)) ()) ())
          (fun x ->
            mtx_set (heap_DBMEntry heap_int) (suc n) bi (ai, bib)
              (min (ord_DBMEntry (equal_int, linorder_int)) x bia)));;

let rec restrict_zero_impl
  n = (fun ai bi ->
        (fun f_ () -> f_ ((and_entry_impl n bi zero_nata (Le zero_inta) ai) ())
          ())
          (fun x ->
            (fun f_ () -> f_ ((and_entry_impl n zero_nata bi (Le zero_inta) x)
              ()) ())
              (fun x_a ->
                repair_pair_impl
                  ((linordered_ab_monoid_add_DBMEntry
                     (linordered_cancel_ab_monoid_add_int, equal_int)),
                    (heap_DBMEntry heap_int))
                  n x_a bi zero_nata)));;

let rec pre_reset_impl
  n = (fun ai bi ->
        (fun f_ () -> f_ ((restrict_zero_impl n ai bi) ()) ())
          (fun x ->
            free_impl (linordered_cancel_ab_monoid_add_int, heap_int) n x bi));;

let rec pre_reset_list_impl
  n = (fun ai bi ->
        imp_nfoldli bi (fun _ -> (fun () -> true))
          (fun x sigma -> pre_reset_impl n sigma x) ai);;

let rec dbm_subset_impla (_A1, _A2, _A3)
  n = (fun ai bia bi ->
        imp_for zero_nata (suc ai) (fun a -> (fun () -> a))
          (fun xb _ ->
            imp_for zero_nata (suc ai) (fun a -> (fun () -> a))
              (fun xe _ ->
                (fun f_ () -> f_
                  ((mtx_get (heap_DBMEntry _A3) (suc n) bia (xb, xe)) ()) ())
                  (fun x_f ->
                    (fun f_ () -> f_
                      ((mtx_get (heap_DBMEntry _A3) (suc n) bi (xb, xe)) ()) ())
                      (fun x_g ->
                        (fun () ->
                          (less_eq_DBMEntry
                            (_A2, _A1.linordered_ab_monoid_add_linordered_cancel_ab_monoid_add.linordered_ab_semigroup_add_linordered_ab_monoid_add.linorder_linordered_ab_semigroup_add)
                            x_f x_g)))))
              true)
          true);;

let rec and_entry_repair_impl
  n = (fun ai bib bia bi ->
        (fun f_ () -> f_ ((and_entry_impl n ai bib bia bi) ()) ())
          (fun x ->
            repair_pair_impl
              ((linordered_ab_monoid_add_DBMEntry
                 (linordered_cancel_ab_monoid_add_int, equal_int)),
                (heap_DBMEntry heap_int))
              n x ai bib));;

let rec upd_entry_impl
  n = (fun ai bib bia bi ->
        (fun f_ () -> f_
          ((mtx_get (heap_DBMEntry heap_int) (suc n) bi (ai, bib)) ()) ())
          (fun x ->
            (fun f_ () -> f_ ((amtx_copy (heap_DBMEntry heap_int) bia) ()) ())
              (and_entry_repair_impl n bib ai (neg_dbm_entry uminus_int x))));;

let rec upd_entries_impl
  n = (fun ai bib bia bi ->
        (fun f_ () -> f_
          ((imp_nfoldli bi (fun _ -> (fun () -> true))
             (fun xa sigma ->
               (fun f_ () -> f_ ((upd_entry_impl n ai bib xa bia) ()) ())
                 (fun x_b -> (fun () -> (x_b :: sigma))))
             op_list_empty)
          ()) ())
          (fun x ->
            imp_nfoldli x (fun _ -> (fun () -> true))
              (fun xb sigma -> (fun () -> (xb :: sigma))) op_list_empty));;

let rec get_entries_impl (_A1, _A2, _A3)
  n = (fun xi ->
        (fun f_ () -> f_
          ((imp_fora zero_nata (suc n)
             (fun xc sigma ->
               (fun f_ () -> f_
                 ((imp_fora zero_nata (suc n)
                    (fun xf sigmaa ->
                      (fun f_ () -> f_
                        ((mtx_get (heap_DBMEntry _A3) (suc n) xi (xc, xf)) ())
                        ())
                        (fun x ->
                          (fun () ->
                            ((if (less_nat zero_nata xc ||
                                   less_nat zero_nata xf) &&
                                   (less_eq_nat xc n &&
                                     (less_eq_nat xf n &&
                                       not (equal_DBMEntry _A2 x INF)))
                               then op_list_prepend (xc, xf) op_list_empty
                               else op_list_empty) ::
                              sigmaa))))
                    op_list_empty)
                 ()) ())
                 (fun x ->
                   (fun f_ () -> f_
                     ((imp_nfoldli (op_list_rev (op_list_rev x))
                        (fun _ -> (fun () -> true))
                        (fun xf sigmaa -> (fun () -> (xf @ sigmaa)))
                        op_list_empty)
                     ()) ())
                     (fun x_c -> (fun () -> (x_c :: sigma)))))
             op_list_empty)
          ()) ())
          (fun x ->
            imp_nfoldli (op_list_rev (op_list_rev x))
              (fun _ -> (fun () -> true))
              (fun xc sigma -> (fun () -> (xc @ sigma))) op_list_empty));;

let rec dbm_minus_canonical_impl
  n = (fun ai bi ->
        (fun f_ () -> f_
          ((get_entries_impl
             (linordered_cancel_ab_monoid_add_int, equal_int, heap_int) n bi)
          ()) ())
          (fun x ->
            (fun f_ () -> f_
              ((imp_nfoldli x (fun _ -> (fun () -> true))
                 (fun xb sigma ->
                   (fun f_ () -> f_
                     ((upd_entries_impl n (fst xb) (snd xb) bi ai) ()) ())
                     (fun xa ->
                       (fun f_ () -> f_
                         ((imp_nfoldli xa (fun _ -> (fun () -> true))
                            (fun xe sigmaa -> (fun () -> (xe :: sigmaa)))
                            op_list_empty)
                         ()) ())
                         (fun x_c -> (fun () -> (x_c @ sigma)))))
                 op_list_empty)
              ()) ())
              (fun xa ->
                (fun f_ () -> f_
                  ((imp_nfoldli xa (fun _ -> (fun () -> true))
                     (fun xb sigma -> (fun () -> (xb :: sigma))) op_list_empty)
                  ()) ())
                  (fun xb ->
                    (fun f_ () -> f_
                      ((imp_nfoldli xb (fun _ -> (fun () -> true))
                         (fun xba sigma ->
                           (fun f_ () -> f_
                             ((check_diag_impla
                                (linordered_cancel_ab_monoid_add_int, heap_int)
                                n n xba)
                             ()) ())
                             (fun xc ->
                               (fun () ->
                                 (if not xc then op_list_prepend xba sigma
                                   else sigma))))
                         op_list_empty)
                      ()) ())
                      (fun xc ->
                        imp_nfoldli xc (fun _ -> (fun () -> true))
                          (fun xba sigma -> (fun () -> (xba :: sigma)))
                          op_list_empty)))));;

let rec dbm_subset_fed_impl
  n = (fun ai bi ->
        (fun f_ () -> f_
          ((imp_nfoldli bi (fun _ -> (fun () -> true))
             (fun xa sigma ->
               (fun f_ () -> f_
                 ((check_diag_impla
                    (linordered_cancel_ab_monoid_add_int, heap_int) n n xa)
                 ()) ())
                 (fun x ->
                   (fun () ->
                     (if not x then op_list_prepend xa sigma else sigma))))
             op_list_empty)
          ()) ())
          (fun x ->
            (let xa = op_list_rev x in
              (if op_list_is_empty xa
                then check_diag_impla
                       (linordered_cancel_ab_monoid_add_int, heap_int) n n ai
                else (fun f_ () -> f_
                       ((imp_nfoldli xa (fun sigma -> (fun () -> (not sigma)))
                          (fun xc sigma ->
                            (fun f_ () -> f_
                              ((dbm_subset_impla
                                 (linordered_cancel_ab_monoid_add_int,
                                   equal_int, heap_int)
                                 n n ai xc)
                              ()) ())
                              (fun x_d ->
                                (fun () -> (if x_d then true else sigma))))
                          false)
                       ()) ())
                       (fun x_b ->
                         (if x_b then (fun () -> true)
                           else (fun f_ () -> f_
                                  ((imp_nfoldli xa (fun _ -> (fun () -> true))
                                     (fun xd sigma ->
                                       dbm_minus_canonical_impl n sigma xd)
                                     (op_list_prepend ai op_list_empty))
                                  ()) ())
                                  (fun x_c ->
                                    (fun () -> (op_list_is_empty x_c)))))))));;

let rec check_passed_impl _A (_B1, _B2, _B3)
  succsi a_0i fi lei emptyi keyi copyi tracei qi =
    (fun f_ () -> f_ (a_0i ()) ())
      (fun x ->
        (fun f_ () -> f_ ((emptyi x) ()) ())
          (fun xa ->
            (fun f_ () -> f_ (a_0i ()) ())
              (fun xaa ->
                (fun f_ () -> f_ ((fi xaa) ()) ())
                  (fun xab ->
                    (fun f_ () -> f_
                      ((if not xa && xab
                         then (fun f_ () -> f_
                                ((ht_new (_B2, _B3) (heap_list _A)) ()) ())
                                (fun x_b -> (fun () -> (true, x_b)))
                         else (fun f_ () -> f_ (a_0i ()) ())
                                (fun xb ->
                                  (fun f_ () -> f_ ((emptyi xb) ()) ())
                                    (fun x_a ->
                                      (if x_a
then (fun f_ () -> f_ ((ht_new (_B2, _B3) (heap_list _A)) ()) ())
       (fun x_c -> (fun () -> (false, x_c)))
else (fun f_ () -> f_ (a_0i ()) ())
       (fun xc ->
         (fun f_ () -> f_ ((keyi xc) ()) ())
           (fun xd ->
             (fun f_ () -> f_ (a_0i ()) ())
               (fun xac ->
                 (fun f_ () -> f_ ((ht_new (_B2, _B3) (heap_list _A)) ()) ())
                   (fun xba ->
                     (fun f_ () -> f_
                       ((ht_update (_B1, _B2, _B3) (heap_list _A) xd [xac] xba)
                       ()) ())
                       (fun xe ->
                         (fun f_ () -> f_ (a_0i ()) ())
                           (fun xad ->
                             (fun f_ () -> f_
                               ((heap_WHILET
                                  (fun (_, (a1b, a2b)) ->
                                    (fun () ->
                                      (not a2b && not (op_list_is_empty a1b))))
                                  (fun (a1a, (a1b, a2b)) ->
                                    (let (a1c, a2c) =
                                       (match a1b
 with [] -> cODE_ABORT (fun _ -> (hd a1b, tl a1b)) | a :: b -> (a, b))
                                       in
                                      (fun f_ () -> f_ ((emptyi a1c) ()) ())
(fun x_e ->
  (if x_e then (fun () -> (a1a, (a2c, a2b)))
    else (fun f_ () -> f_ (tRACE_impl ()) ())
           (fun _ ->
             (fun f_ () -> f_
               ((tracei
                   [Chara (true, false, true, false, false, false, true, false);
                     Chara (false, false, false, true, true, true, true, false);
                     Chara (false, false, false, false, true, true, true,
                             false);
                     Chara (false, false, true, true, false, true, true, false);
                     Chara (true, true, true, true, false, true, true, false);
                     Chara (false, true, false, false, true, true, true, false);
                     Chara (true, false, true, false, false, true, true, false);
                     Chara (false, false, true, false, false, true, true,
                             false)]
                  a1c)
               ()) ())
               (fun _ ->
                 (fun f_ () -> f_ ((succsi a1c) ()) ())
                   (fun x_h ->
                     imp_nfoldli x_h (fun (_, (_, b)) -> (fun () -> (not b)))
                       (fun xl (a1d, (a1e, _)) ->
                         (fun f_ () -> f_ ((emptyi xl) ()) ())
                           (fun x_k ->
                             (if x_k then (fun () -> (a1d, (a1e, false)))
                               else (fun f_ () -> f_ ((fi xl) ()) ())
                                      (fun x_l ->
(if x_l then (fun () -> (a1d, (a1e, true)))
  else (fun f_ () -> f_ ((keyi xl) ()) ())
         (fun x_m ->
           (fun f_ () -> f_
             ((hms_extract (ht_lookup (_B1, _B2, _B3) (heap_list _A))
                (ht_delete (_B1, _B2, _B3) (heap_list _A)) x_m a1d)
             ()) ())
             (fun a ->
               (match a
                 with (None, a2f) ->
                   (fun f_ () -> f_ ((copyi xl) ()) ())
                     (fun xf ->
                       (fun f_ () -> f_
                         ((ht_update (_B1, _B2, _B3) (heap_list _A) x_m [xf]
                            a2f)
                         ()) ())
                         (fun x_o ->
                           (fun () -> (x_o, (op_list_prepend xl a1e, false)))))
                 | (Some x_o, a2f) ->
                   (fun f_ () -> f_ ((lso_bex_impl (lei xl) x_o) ()) ())
                     (fun x_p ->
                       (if x_p
                         then (fun f_ () -> f_
                                ((ht_update (_B1, _B2, _B3) (heap_list _A) x_m
                                   x_o a2f)
                                ()) ())
                                (fun x_q -> (fun () -> (x_q, (a1e, false))))
                         else (fun f_ () -> f_ ((copyi xl) ()) ())
                                (fun xf ->
                                  (fun f_ () -> f_
                                    ((ht_update (_B1, _B2, _B3) (heap_list _A)
                                       x_m (xf :: x_o) a2f)
                                    ()) ())
                                    (fun x_q ->
                                      (fun () ->
(x_q, (op_list_prepend xl a1e, false)))))))))))))))
                       (a1a, (a2c, false)))))))))
                                  (xe, (op_list_prepend xad [], false)))
                               ()) ())
                               (fun (a1a, (_, a2b)) ->
                                 (fun () -> (a2b, a1a)))))))))))))
                      ()) ())
                      (fun (_, a2) ->
                        (fun f_ () -> f_
                          ((ran_of_map_impl (_B1, _B2, _B3) (heap_list _A) a2)
                          ()) ())
                          (fun x_a ->
                            imp_nfoldli x_a
                              (fun sigma -> (fun () -> (not sigma)))
                              (fun xd _ ->
                                imp_nfoldli xd
                                  (fun sigma -> (fun () -> (not sigma)))
                                  (fun xg _ ->
                                    (fun f_ () -> f_ ((qi xg) ()) ())
                                      (fun x_g ->
(fun () -> (if x_g then true else false))))
                                  false)
                              false))))));;

let rec constraint_clk = function LTa (c, uu) -> c
                         | LEa (c, uv) -> c
                         | EQa (c, uw) -> c
                         | GE (c, ux) -> c
                         | GT (c, uy) -> c;;

let rec deadlock_checker
  p m max_steps inv trans prog bounds pred s_0 na k =
    (let num_clocks_ran = upt zero_nata (plus_nata m one_nata) in
     let num_processes_ran = Set (upt zero_nata p) in
     let num_actions_ran = upt zero_nata na in
     let p_ran = upt zero_nata p in
     let prog_array = IArray prog in
     let prog_t = IArray (map (map_option stript) prog) in
     let prog_f = IArray (map (map_option stripf) prog) in
     let len_prog = size_list prog in
     let proga =
       (fun pc -> (if less_nat pc len_prog then sub prog_array pc else None)) in
     let pt = (fun pc -> (if less_nat pc len_prog then sub prog_t pc else None))
       in
     let pf = (fun pc -> (if less_nat pc len_prog then sub prog_f pc else None))
       in
     let bounds_array = IArray bounds in
     let trans_internal = IArray (map (fun a -> IArray a) (trans_i_map trans))
       in
     let trans_in = IArray (map (fun a -> IArray a) (trans_in_map trans)) in
     let trans_out = IArray (map (fun a -> IArray a) (trans_out_map trans)) in
     let inv_array = IArray (map (fun a -> IArray a) inv) in
     let transa =
       (fun l ->
         (let (la, s) = l in
          let ina =
            all_actions_by_state_impl p_ran (map (fun _ -> []) num_actions_ran)
              trans_in la
            in
          let out =
            all_actions_by_state_impl p_ran (map (fun _ -> []) num_actions_ran)
              trans_out la
            in
           maps (fun a ->
                  pairs_by_action_impl p max_steps pred pf pt proga bounds_array
                    (la, s) (nth out a) (nth ina a))
             num_actions_ran) @
           maps (trans_i_from_impl p max_steps pred bounds pf pt proga
                  bounds_array trans_internal l)
             p_ran)
       in
     let inva =
       (fun (l, _) -> maps (fun i -> sub (sub inv_array i) (nth l i)) p_ran) in
     let ceiling =
       IArray
         (map (comp (fun a -> IArray a)
                (map (comp (fun a -> IArray a) (map int_of_nat))))
           k)
       in
     let key = comp (fun a -> (fun () -> a)) fst in
     let suba =
       (fun ai bi ->
         (let (a1, a2) = ai in
          let (a1a, a2a) = bi in
           (if equal_proda (equal_list equal_nat) (equal_list equal_int) a1 a1a
             then dbm_subset_impl
                    (linordered_cancel_ab_monoid_add_int, equal_int, heap_int) m
                    a2 a2a
             else (fun () -> false))))
       in
     let copy =
       (fun (a1, a2) ->
         (fun f_ () -> f_ ((amtx_copy (heap_DBMEntry heap_int) a2) ()) ())
           (fun x -> (fun () -> (a1, x))))
       in
     let start =
       (fun f_ () -> f_
         ((amtx_dflt (heap_DBMEntry heap_int) (suc m) (suc m) (Le zero_inta))
         ()) ())
         (fun x_a -> (fun () -> ((init p, s_0), x_a)))
       in
     let final = (fun _ -> (fun () -> false)) in
     let succs =
       (fun (a1, a2) ->
         imp_nfoldli (transa a1) (fun _ -> (fun () -> true))
           (fun xc sigma ->
             (let (a1a, (_, (a1c, a2c))) = xc in
               (fun f_ () -> f_ ((amtx_copy (heap_DBMEntry heap_int) a2) ()) ())
                 (fun x ->
                   (fun f_ () -> f_
                     (((fun f_ () -> f_
                         ((up_canonical_upd_impl
                            (linordered_cancel_ab_monoid_add_int, heap_int) m x
                            m)
                         ()) ())
                        (fun xa ->
                          (fun f_ () -> f_
                            ((imp_nfoldli (inva a1) (fun _ -> (fun () -> true))
                               (fun ai bi ->
                                 (fun f_ () -> f_
                                   ((abstra_upd_impl
                                      (linordered_cancel_ab_monoid_add_int,
uminus_int, equal_int, heap_int)
                                      m ai bi)
                                   ()) ())
                                   (fun xb ->
                                     repair_pair_impl
                                       ((linordered_ab_monoid_add_DBMEntry
  (linordered_cancel_ab_monoid_add_int, equal_int)),
 (heap_DBMEntry heap_int))
                                       m xb zero_nata (constraint_clk ai)))
                               xa)
                            ()) ())
                            (fun xb ->
                              (fun f_ () -> f_
                                ((check_diag_impla
                                   (linordered_cancel_ab_monoid_add_int,
                                     heap_int)
                                   m m xb)
                                ()) ())
                                (fun xaa ->
                                  (fun f_ () -> f_
                                    ((if xaa then (fun () -> xb)
                                       else imp_nfoldli a1a
      (fun _ -> (fun () -> true))
      (fun ai bi ->
        (fun f_ () -> f_
          ((abstra_upd_impl
             (linordered_cancel_ab_monoid_add_int, uminus_int, equal_int,
               heap_int)
             m ai bi)
          ()) ())
          (fun xd ->
            repair_pair_impl
              ((linordered_ab_monoid_add_DBMEntry
                 (linordered_cancel_ab_monoid_add_int, equal_int)),
                (heap_DBMEntry heap_int))
              m xd zero_nata (constraint_clk ai)))
      xb)
                                    ()) ())
                                    (fun x_a ->
                                      (fun f_ () -> f_
((check_diag_impla (linordered_cancel_ab_monoid_add_int, heap_int) m m x_a) ())
())
(fun xd ->
  (fun f_ () -> f_
    ((if xd then (fun () -> x_a)
       else (fun f_ () -> f_
              ((imp_nfoldli a1c (fun _ -> (fun () -> true))
                 (fun xca sigmaa ->
                   reset_canonical_upd_impl
                     (linordered_cancel_ab_monoid_add_int, uminus_int, heap_int)
                     m sigmaa m xca zero_inta)
                 x_a)
              ()) ())
              (imp_nfoldli (inva a2c) (fun _ -> (fun () -> true))
                (fun ai bi ->
                  (fun f_ () -> f_
                    ((abstra_upd_impl
                       (linordered_cancel_ab_monoid_add_int, uminus_int,
                         equal_int, heap_int)
                       m ai bi)
                    ()) ())
                    (fun xe ->
                      repair_pair_impl
                        ((linordered_ab_monoid_add_DBMEntry
                           (linordered_cancel_ab_monoid_add_int, equal_int)),
                          (heap_DBMEntry heap_int))
                        m xe zero_nata (constraint_clk ai)))))
    ()) ())
    (fun x_b ->
      (fun f_ () -> f_
        ((check_diag_impla (linordered_cancel_ab_monoid_add_int, heap_int) m m
           x_b)
        ()) ())
        (fun x_c ->
          (if x_c then (fun () -> x_b)
            else (fun f_ () -> f_
                   ((norm_upd_impl (linordered_ab_group_add_int, heap_int) m x_b
                      (let (l, _) = a2c in
                        IArray
                          (map (fun c ->
                                 maxa linorder_int
                                   (image
                                     (fun i ->
                                       sub (sub (sub ceiling i) (nth l i)) c)
                                     num_processes_ran))
                            num_clocks_ran))
                      m)
                   ()) ())
                   (fw_impl_int m))))))))))
                     ()) ())
                     (fun xa ->
                       (fun () -> (op_list_prepend (a2c, xa) sigma))))))
           [])
       in
     let empty =
       (fun (_, a) ->
         check_diag_impl (linordered_cancel_ab_monoid_add_int, heap_int) m a)
       in
     let pa =
       (fun (a1, a2) ->
         (fun f_ () -> f_
           (((fun f_ () -> f_
               ((imp_nfoldli (transa a1) (fun _ -> (fun () -> true))
                  (fun xb sigma ->
                    (fun f_ () -> f_
                      ((v_dbm_impl
                         (linordered_cancel_ab_monoid_add_int, heap_int) m)
                      ()) ())
                      (fun x ->
                        (fun f_ () -> f_
                          ((abstr_FW_impl
                             (linordered_cancel_ab_monoid_add_int, uminus_int,
                               equal_int, heap_int)
                             m (inva (snd (snd (snd xb)))) x)
                          ()) ())
                          (fun xa ->
                            (fun f_ () -> f_
                              ((pre_reset_list_impl m xa (fst (snd (snd xb))))
                              ()) ())
                              (fun xc ->
                                (fun f_ () -> f_
                                  ((abstr_FW_impl
                                     (linordered_cancel_ab_monoid_add_int,
                                       uminus_int, equal_int, heap_int)
                                     m (fst xb) xc)
                                  ()) ())
                                  (fun xd ->
                                    (fun f_ () -> f_
                                      ((abstr_FW_impl
 (linordered_cancel_ab_monoid_add_int, uminus_int, equal_int, heap_int) m
 (inva a1) xd)
                                      ()) ())
                                      (fun xe ->
(fun f_ () -> f_
  ((down_impl (linordered_cancel_ab_monoid_add_int, equal_int, heap_int) m xe)
  ()) ())
  (fun x_c -> (fun () -> (x_c :: sigma)))))))))
                  [])
               ()) ())
              (fun x -> dbm_subset_fed_impl m a2 (op_list_rev x)))
           ()) ())
           (fun x -> (fun () -> (not x))))
       in
     let trace =
       tracei (linordered_ab_group_add_int, equal_int, heap_int, show_int) m
         (fun x ->
           shows_prec_prod (show_list show_nat) (show_list show_int) zero_nata x
             [])
         (fun x -> shows_prec_nat zero_nata x [])
       in
      (fun f_ () -> f_
        ((fun () -> (not (op_list_is_empty (transa (init p, s_0))))) ()) ())
        (fun r1 ->
          (if r1
            then (fun f_ () -> f_
                   ((check_passed_impl
                      (heap_prod
                        (heap_prod (heap_list heap_nat) (heap_list heap_int))
                        (heap_array (typerep_DBMEntry typerep_int)))
                      ((equal_prod (equal_list equal_nat)
                         (equal_list equal_int)),
                        (hashable_prod (hashable_list hashable_nat)
                          (hashable_list hashable_int)),
                        (heap_prod (heap_list heap_nat) (heap_list heap_int)))
                      succs start final suba empty key copy trace pa)
                   ()) ())
                   (fun a -> (fun () -> a))
            else (fun () -> true))));;

let rec precond_dc
  num_processes num_clocks clock_ceiling max_steps i t prog bounds program s_0
    num_actions =
    (if uPPAAL_Reachability_Problem_precompileda num_processes num_clocks
          max_steps i t prog bounds program s_0 num_actions clock_ceiling
      then (fun f_ () -> f_
             ((deadlock_checker num_processes num_clocks max_steps i t prog
                bounds program s_0 num_actions clock_ceiling)
             ()) ())
             (fun x -> (fun () -> (Some x)))
      else (fun () -> None));;

let rec gi_E (Gen_g_impl_ext (gi_V, gi_E, gi_V0, more)) = gi_E;;

let rec more (Gen_g_impl_ext (gi_V, gi_E, gi_V0, more)) = more;;

let rec as_is_empty s = equal_nata (snd s) zero_nata;;

let rec gi_V0 (Gen_g_impl_ext (gi_V, gi_E, gi_V0, more)) = gi_V0;;

let rec ceiling_checks
  x = (fun p m max_steps inv trans prog k ->
        [("Length of ceilig", equal_nata (size_list k) p);
          ("1", all_interval_nat
                  (fun i ->
                    all_interval_nat
                      (fun l ->
                        ball (clkp_set max_steps inv trans prog i l)
                          (fun (xa, ma) ->
                            less_eq_int ma
                              (int_of_nat (nth (nth (nth k i) l) xa))))
                      zero_nata (size_list (nth trans i)))
                  zero_nata p);
          ("2", all_interval_nat
                  (fun i ->
                    all_interval_nat
                      (fun l ->
                        ball (collect_clock_pairs (nth (nth inv i) l))
                          (fun (xa, ma) ->
                            less_eq_int ma
                              (int_of_nat (nth (nth (nth k i) l) xa))))
                      zero_nata (size_list (nth trans i)))
                  zero_nata p);
          ("3", all_interval_nat
                  (fun i ->
                    all_interval_nat
                      (fun l ->
                        list_all
                          (fun (_, (_, (r, la))) ->
                            ball (minus_set equal_nat
                                   (Set (upt zero_nata (plus_nata m one_nata)))
                                   (image fst (collect_storea prog r)))
                              (fun c ->
                                less_eq_nat (nth (nth (nth k i) la) c)
                                  (nth (nth (nth k i) l) c)))
                          (nth (nth trans i) l))
                      zero_nata (size_list (nth trans i)))
                  zero_nata p);
          ("4", all_interval_nat
                  (fun i ->
                    equal_nata (size_list (nth k i)) (size_list (nth trans i)))
                  zero_nata p);
          ("5", list_all
                  (list_all
                    (fun xxs ->
                      equal_nata (size_list xxs) (plus_nata m one_nata)))
                  k);
          ("6", all_interval_nat
                  (fun i ->
                    all_interval_nat
                      (fun l ->
                        equal_nata (nth (nth (nth k i) l) zero_nata) zero_nata)
                      zero_nata (size_list (nth trans i)))
                  zero_nata p);
          ("7", all_interval_nat
                  (fun i ->
                    all_interval_nat
                      (fun l ->
                        list_all
                          (fun (_, (_, (r, _))) ->
                            guaranteed_execution_cond equal_int prog r
                              max_steps)
                          (nth (nth trans i) l))
                      zero_nata (size_list (nth trans i)))
                  zero_nata p)])
        x;;

let rec select_edge_tr (_A1, _A2)
  s = (let (a, (aa, (ab, bb))) = s in
        (if as_is_empty bb then (None, (a, (aa, (ab, bb))))
          else (let (ac, bc) = as_top bb in
                 (if less_eq_nat (as_get aa (minus_nat (as_length aa) one_nata))
                       ac
                   then (let xa = gen_pick (fun x -> foldli (id x)) bc in
                         let xb = glist_delete (eq _A1) xa bc in
                         let xc =
                           (if is_Nil xb then as_pop bb
                             else as_set bb (minus_nat (as_length bb) one_nata)
                                    (ac, xb))
                           in
                          (Some xa, (a, (aa, (ab, xc)))))
                   else (None, (a, (aa, (ab, bb))))))));;

let rec ahm_lookup_aux
  eq bhc k a = list_map_lookup eq k (array_get a (bhc (array_length a) k));;

let rec ahm_lookup eq bhc k (HashMap (a, uu)) = ahm_lookup_aux eq bhc k a;;

let rec idx_of_tr (_A1, _A2)
  s v = (let (_, (aa, (ab, _))) = v in
         let x =
           (let Some i = ahm_lookup (eq _A1) (bounded_hashcode_nat _A2) s ab in
            let true = less_eq_int zero_inta i in
             nat i)
           in
         let xa =
           find_max_nat (as_length aa) (fun j -> less_eq_nat (as_get aa j) x) in
          xa);;

let rec collapse_tr (_A1, _A2)
  v s = (let (a, (aa, (ab, bb))) = s in
         let x = idx_of_tr (_A1, _A2) v (a, (aa, (ab, bb))) in
         let xa = as_take (plus_nata x one_nata) aa in
          (a, (xa, (ab, bb))));;

let rec as_singleton _B x = (FArray.IsabelleMapping.array_of_list [x], one _B);;

let rec new_hashmap_with size = HashMap (new_array [] size, zero_nata);;

let rec ahm_empty def_size = new_hashmap_with def_size;;

let rec push_code (_A1, _A2)
  g_impl =
    (fun x (xa, (xb, (xc, xd))) ->
      (let _ = stat_newnode () in
       let y_a = as_length xa in
       let y_b = as_push xa x in
       let y_c = as_push xb y_a in
       let y_d =
         ahm_update (eq _A1) (bounded_hashcode_nat _A2) x (int_of_nat y_a) xc in
       let y_e =
         (if is_Nil (gi_E g_impl x) then xd
           else as_push xd (y_a, gi_E g_impl x))
         in
        (y_b, (y_c, (y_d, y_e)))));;

let rec compute_SCC_tr (_A1, _A2)
  g = (let _ = stat_start () in
       let xa = ([], ahm_empty (def_hashmap_size _A2 Type)) in
       let a =
         foldli (id (gi_V0 g)) (fun _ -> true)
           (fun xb (a, b) ->
             (if not (match ahm_lookup (eq _A1) (bounded_hashcode_nat _A2) xb b
                       with None -> false
                       | Some i ->
                         (if less_eq_int zero_inta i then false else true))
               then (let xc =
                       (a, (as_singleton one_nat xb,
                             (as_singleton one_nat zero_nata,
                               (ahm_update (eq _A1) (bounded_hashcode_nat _A2)
                                  xb (int_of_nat zero_nata) b,
                                 (if is_Nil (gi_E g xb)
                                   then as_empty zero_nat ()
                                   else as_singleton one_nat
  (zero_nata, gi_E g xb))))))
                       in
                     let (aa, (_, (_, (ad, _)))) =
                       whilea
                         (fun (_, xf) ->
                           not (as_is_empty (let (xg, (_, (_, _))) = xf in xg)))
                         (fun (aa, ba) ->
                           (match select_edge_tr (_A1, _A2) ba
                             with (None, bb) ->
                               (let xf = last_seg_tr _A2 bb in
                                let xg = pop_tr (_A1, _A2) bb in
                                let xh = xf :: aa in
                                 (xh, xg))
                             | (Some xf, bb) ->
                               (if (match
                                     ahm_lookup (eq _A1)
                                       (bounded_hashcode_nat _A2) xf
                                       (let (_, (_, (xl, _))) = bb in xl)
                                     with None -> false
                                     | Some i ->
                                       (if less_eq_int zero_inta i then true
 else false))
                                 then (let ab = collapse_tr (_A1, _A2) xf bb in
(aa, ab))
                                 else (if not
    (match
      ahm_lookup (eq _A1) (bounded_hashcode_nat _A2) xf
        (let (_, (_, (xl, _))) = bb in xl)
      with None -> false
      | Some i -> (if less_eq_int zero_inta i then false else true))
then (aa, push_code (_A1, _A2) g xf bb) else (aa, bb)))))
                         xc
                       in
                      (aa, ad))
               else (a, b)))
           xa
         in
       let (aa, _) = a in
       let _ = stat_stop () in
        aa);;

let rec check_bexp
  x0 l s = match x0, l, s with Not a, l, s -> not (check_bexp a l s)
    | And (a, b), l, s -> check_bexp a l s && check_bexp b l s
    | Or (a, b), l, s -> check_bexp a l s || check_bexp b l s
    | Imply (a, b), l, s ->
        (if check_bexp a l s then check_bexp b l s else true)
    | Loc (p, la), l, uu -> equal_nata (nth l p) la
    | Eq (i, x), uv, s -> equal_inta (nth s i) x
    | Lea (i, x), uw, s -> less_eq_int (nth s i) x
    | Lta (i, x), ux, s -> less_int (nth s i) x
    | Ge (i, x), uy, s -> less_eq_int x (nth s i)
    | Gt (i, x), uz, s -> less_int x (nth s i);;

let rec hd_of_formula = function EX phi -> check_bexp phi
                        | EG phi -> check_bexp phi
                        | AX phi -> (fun x -> comp not (check_bexp phi x))
                        | AG phi -> (fun x -> comp not (check_bexp phi x))
                        | Leadsto (phi, uu) -> check_bexp phi;;

let rec reachability_checker
  p m max_steps inv trans prog bounds pred s_0 na k formula =
    (let x = upt zero_nata (plus_nata m one_nata) in
     let xa = Set (upt zero_nata p) in
     let xb = upt zero_nata na in
     let xc = upt zero_nata p in
     let prog_ia = IArray prog in
     let progt_ia = IArray (map (map_option stript) prog) in
     let progf_ia = IArray (map (map_option stripf) prog) in
     let len_prog = size_list prog in
     let proga =
       (fun pc -> (if less_nat pc len_prog then sub prog_ia pc else None)) in
     let pt =
       (fun pc -> (if less_nat pc len_prog then sub progt_ia pc else None)) in
     let pf =
       (fun pc -> (if less_nat pc len_prog then sub progf_ia pc else None)) in
     let bounds_ia = IArray bounds in
     let trans_i_mapa = IArray (map (fun a -> IArray a) (trans_i_map trans)) in
     let trans_in_mapa = IArray (map (fun a -> IArray a) (trans_in_map trans))
       in
     let trans_out_mapa = IArray (map (fun a -> IArray a) (trans_out_map trans))
       in
     let inv_ia = IArray (map (fun a -> IArray a) inv) in
     let trans_fun =
       (fun l ->
         (let (la, s) = l in
          let ina =
            all_actions_by_state_impl xc (map (fun _ -> []) xb) trans_in_mapa la
            in
          let out =
            all_actions_by_state_impl xc (map (fun _ -> []) xb) trans_out_mapa
              la
            in
           maps (fun a ->
                  pairs_by_action_impl p max_steps pred pf pt proga bounds_ia
                    (la, s) (nth out a) (nth ina a))
             xb) @
           maps (trans_i_from_impl p max_steps pred bounds pf pt proga bounds_ia
                  trans_i_mapa l)
             xc)
       in
     let k_i =
       IArray
         (map (comp (fun a -> IArray a)
                (map (comp (fun a -> IArray a) (map int_of_nat))))
           k)
       in
      (fun f_ () -> f_
        ((let key = comp (fun a -> (fun () -> a)) fst in
          let suba =
            (fun ai bi ->
              (let (a1, a2) = ai in
               let (a1a, a2a) = bi in
                (if equal_proda (equal_list equal_nat) (equal_list equal_int) a1
                      a1a
                  then dbm_subset_impl
                         (linordered_cancel_ab_monoid_add_int, equal_int,
                           heap_int)
                         m a2 a2a
                  else (fun () -> false))))
            in
          let copy =
            (fun (a1, a2) ->
              (fun f_ () -> f_ ((amtx_copy (heap_DBMEntry heap_int) a2) ()) ())
                (fun xd -> (fun () -> (a1, xd))))
            in
          let start =
            (fun f_ () -> f_
              ((amtx_dflt (heap_DBMEntry heap_int) (suc m) (suc m)
                 (Le zero_inta))
              ()) ())
              (fun x_a -> (fun () -> ((init p, s_0), x_a)))
            in
          let final =
            (fun xi ->
              (fun () -> (let ((a, b), _) = xi in hd_of_formula formula a b)))
            in
          let succs =
            (fun (a1, a2) ->
              imp_nfoldli (trans_fun a1) (fun _ -> (fun () -> true))
                (fun xca sigma ->
                  (let (a1a, (_, (a1c, a2c))) = xca in
                    (fun f_ () -> f_ ((amtx_copy (heap_DBMEntry heap_int) a2)
                      ()) ())
                      (fun xba ->
                        (fun f_ () -> f_
                          (((fun f_ () -> f_
                              ((up_canonical_upd_impl
                                 (linordered_cancel_ab_monoid_add_int, heap_int)
                                 m xba m)
                              ()) ())
                             (fun xbb ->
                               (fun f_ () -> f_
                                 ((imp_nfoldli
                                    (let (l, _) = a1 in
                                      maps
(fun i -> sub (sub inv_ia i) (nth l i)) xc)
                                    (fun _ -> (fun () -> true))
                                    (fun ai bi ->
                                      (fun f_ () -> f_
((abstra_upd_impl
   (linordered_cancel_ab_monoid_add_int, uminus_int, equal_int, heap_int) m ai
   bi)
()) ())
(fun xd ->
  repair_pair_impl
    ((linordered_ab_monoid_add_DBMEntry
       (linordered_cancel_ab_monoid_add_int, equal_int)),
      (heap_DBMEntry heap_int))
    m xd zero_nata (constraint_clk ai)))
                                    xbb)
                                 ()) ())
                                 (fun xbc ->
                                   (fun f_ () -> f_
                                     ((check_diag_impla
(linordered_cancel_ab_monoid_add_int, heap_int) m m xbc)
                                     ()) ())
                                     (fun xd ->
                                       (fun f_ () -> f_
 ((if xd then (fun () -> xbc)
    else imp_nfoldli a1a (fun _ -> (fun () -> true))
           (fun ai bi ->
             (fun f_ () -> f_
               ((abstra_upd_impl
                  (linordered_cancel_ab_monoid_add_int, uminus_int, equal_int,
                    heap_int)
                  m ai bi)
               ()) ())
               (fun xe ->
                 repair_pair_impl
                   ((linordered_ab_monoid_add_DBMEntry
                      (linordered_cancel_ab_monoid_add_int, equal_int)),
                     (heap_DBMEntry heap_int))
                   m xe zero_nata (constraint_clk ai)))
           xbc)
 ()) ())
 (fun x_a ->
   (fun f_ () -> f_
     ((check_diag_impla (linordered_cancel_ab_monoid_add_int, heap_int) m m x_a)
     ()) ())
     (fun xbd ->
       (fun f_ () -> f_
         ((if xbd then (fun () -> x_a)
            else (fun f_ () -> f_
                   ((imp_nfoldli a1c (fun _ -> (fun () -> true))
                      (fun xcb sigmaa ->
                        reset_canonical_upd_impl
                          (linordered_cancel_ab_monoid_add_int, uminus_int,
                            heap_int)
                          m sigmaa m xcb zero_inta)
                      x_a)
                   ()) ())
                   (imp_nfoldli
                     (let (l, _) = a2c in
                       maps (fun i -> sub (sub inv_ia i) (nth l i)) xc)
                     (fun _ -> (fun () -> true))
                     (fun ai bi ->
                       (fun f_ () -> f_
                         ((abstra_upd_impl
                            (linordered_cancel_ab_monoid_add_int, uminus_int,
                              equal_int, heap_int)
                            m ai bi)
                         ()) ())
                         (fun xe ->
                           repair_pair_impl
                             ((linordered_ab_monoid_add_DBMEntry
                                (linordered_cancel_ab_monoid_add_int,
                                  equal_int)),
                               (heap_DBMEntry heap_int))
                             m xe zero_nata (constraint_clk ai)))))
         ()) ())
         (fun x_b ->
           (fun f_ () -> f_
             ((check_diag_impla (linordered_cancel_ab_monoid_add_int, heap_int)
                m m x_b)
             ()) ())
             (fun x_c ->
               (if x_c then (fun () -> x_b)
                 else (fun f_ () -> f_
                        ((norm_upd_impl (linordered_ab_group_add_int, heap_int)
                           m x_b
                           (let (l, _) = a2c in
                             IArray
                               (map (fun c ->
                                      maxa linorder_int
(image (fun i -> sub (sub (sub k_i i) (nth l i)) c) xa))
                                 x))
                           m)
                        ()) ())
                        (fw_impl_int m))))))))))
                          ()) ())
                          (fun xd ->
                            (fun () -> (op_list_prepend (a2c, xd) sigma))))))
                [])
            in
          let empty =
            (fun (_, a) ->
              check_diag_impl (linordered_cancel_ab_monoid_add_int, heap_int) m
                a)
            in
          let traceia =
            tracei (linordered_ab_group_add_int, equal_int, heap_int, show_int)
              m (fun xd ->
                  shows_prec_prod (show_list show_nat) (show_list show_int)
                    zero_nata xd [])
              (fun xd -> shows_prec_nat zero_nata xd [])
            in
           pw_impl
             (heap_prod (heap_prod (heap_list heap_nat) (heap_list heap_int))
               (heap_array (typerep_DBMEntry typerep_int)))
             ((equal_prod (equal_list equal_nat) (equal_list equal_int)),
               (hashable_prod (hashable_list hashable_nat)
                 (hashable_list hashable_int)),
               (heap_prod (heap_list heap_nat) (heap_list heap_int)))
             key copy traceia suba start final succs empty)
        ()) ())
        (fun xd ->
          (fun f_ () -> f_ ((fun () -> ()) ()) ()) (fun _ -> (fun () -> xd))));;

let rec leadsto_checker
  p m max_steps inv trans prog bounds pred s_0 na k formula =
    (let x = upt zero_nata (plus_nata m one_nata) in
     let xa = Set (upt zero_nata p) in
     let xb = upt zero_nata na in
     let xc = upt zero_nata p in
     let prog_ia = IArray prog in
     let progt_ia = IArray (map (map_option stript) prog) in
     let progf_ia = IArray (map (map_option stripf) prog) in
     let len_prog = size_list prog in
     let proga =
       (fun pc -> (if less_nat pc len_prog then sub prog_ia pc else None)) in
     let pt =
       (fun pc -> (if less_nat pc len_prog then sub progt_ia pc else None)) in
     let pf =
       (fun pc -> (if less_nat pc len_prog then sub progf_ia pc else None)) in
     let bounds_ia = IArray bounds in
     let trans_i_mapa = IArray (map (fun a -> IArray a) (trans_i_map trans)) in
     let trans_in_mapa = IArray (map (fun a -> IArray a) (trans_in_map trans))
       in
     let trans_out_mapa = IArray (map (fun a -> IArray a) (trans_out_map trans))
       in
     let inv_ia = IArray (map (fun a -> IArray a) inv) in
     let trans_fun =
       (fun l ->
         (let (la, s) = l in
          let ina =
            all_actions_by_state_impl xc (map (fun _ -> []) xb) trans_in_mapa la
            in
          let out =
            all_actions_by_state_impl xc (map (fun _ -> []) xb) trans_out_mapa
              la
            in
           maps (fun a ->
                  pairs_by_action_impl p max_steps pred pf pt proga bounds_ia
                    (la, s) (nth out a) (nth ina a))
             xb) @
           maps (trans_i_from_impl p max_steps pred bounds pf pt proga bounds_ia
                  trans_i_mapa l)
             xc)
       in
     let k_i =
       IArray
         (map (comp (fun a -> IArray a)
                (map (comp (fun a -> IArray a) (map int_of_nat))))
           k)
       in
      (fun psi ->
        (fun f_ () -> f_
          ((let key = comp (fun a -> (fun () -> a)) fst in
            let suba =
              (fun ai bi ->
                (let (a1, a2) = ai in
                 let (a1a, a2a) = bi in
                  (if equal_proda (equal_list equal_nat) (equal_list equal_int)
                        a1 a1a
                    then dbm_subset_impl
                           (linordered_cancel_ab_monoid_add_int, equal_int,
                             heap_int)
                           m a2 a2a
                    else (fun () -> false))))
              in
            let copy =
              (fun (a1, a2) ->
                (fun f_ () -> f_ ((amtx_copy (heap_DBMEntry heap_int) a2) ())
                  ())
                  (fun xd -> (fun () -> (a1, xd))))
              in
            let start =
              (fun f_ () -> f_
                ((amtx_dflt (heap_DBMEntry heap_int) (suc m) (suc m)
                   (Le zero_inta))
                ()) ())
                (fun x_a -> (fun () -> ((init p, s_0), x_a)))
              in
            let final =
              (fun xi ->
                (fun () -> (let ((a, b), _) = xi in hd_of_formula formula a b)))
              in
            let finala =
              (fun xi ->
                (fun () -> (let ((l, s), _) = xi in not (check_bexp psi l s))))
              in
            let succs =
              (fun xi ->
                (fun f_ () -> f_
                  ((let (a1, a2) = xi in
                     imp_nfoldli (trans_fun a1) (fun _ -> (fun () -> true))
                       (fun xca sigma ->
                         (let (a1a, (_, (a1c, a2c))) = xca in
                           (if (let (l, s) = a2c in not (check_bexp psi l s))
                             then (fun f_ () -> f_
                                    ((amtx_copy (heap_DBMEntry heap_int) a2) ())
                                    ())
                                    (fun xba ->
                                      (fun f_ () -> f_
(((fun f_ () -> f_
    ((up_canonical_upd_impl (linordered_cancel_ab_monoid_add_int, heap_int) m
       xba m)
    ()) ())
   (fun xbb ->
     (fun f_ () -> f_
       ((imp_nfoldli
          (let (l, _) = a1 in maps (fun i -> sub (sub inv_ia i) (nth l i)) xc)
          (fun _ -> (fun () -> true))
          (fun ai bi ->
            (fun f_ () -> f_
              ((abstra_upd_impl
                 (linordered_cancel_ab_monoid_add_int, uminus_int, equal_int,
                   heap_int)
                 m ai bi)
              ()) ())
              (fun xd ->
                repair_pair_impl
                  ((linordered_ab_monoid_add_DBMEntry
                     (linordered_cancel_ab_monoid_add_int, equal_int)),
                    (heap_DBMEntry heap_int))
                  m xd zero_nata (constraint_clk ai)))
          xbb)
       ()) ())
       (fun xbc ->
         (fun f_ () -> f_
           ((check_diag_impla (linordered_cancel_ab_monoid_add_int, heap_int) m
              m xbc)
           ()) ())
           (fun xd ->
             (fun f_ () -> f_
               ((if xd then (fun () -> xbc)
                  else imp_nfoldli a1a (fun _ -> (fun () -> true))
                         (fun ai bi ->
                           (fun f_ () -> f_
                             ((abstra_upd_impl
                                (linordered_cancel_ab_monoid_add_int,
                                  uminus_int, equal_int, heap_int)
                                m ai bi)
                             ()) ())
                             (fun xe ->
                               repair_pair_impl
                                 ((linordered_ab_monoid_add_DBMEntry
                                    (linordered_cancel_ab_monoid_add_int,
                                      equal_int)),
                                   (heap_DBMEntry heap_int))
                                 m xe zero_nata (constraint_clk ai)))
                         xbc)
               ()) ())
               (fun x_a ->
                 (fun f_ () -> f_
                   ((check_diag_impla
                      (linordered_cancel_ab_monoid_add_int, heap_int) m m x_a)
                   ()) ())
                   (fun xbd ->
                     (fun f_ () -> f_
                       ((if xbd then (fun () -> x_a)
                          else (fun f_ () -> f_
                                 ((imp_nfoldli a1c (fun _ -> (fun () -> true))
                                    (fun xcb sigmaa ->
                                      reset_canonical_upd_impl
(linordered_cancel_ab_monoid_add_int, uminus_int, heap_int) m sigmaa m xcb
zero_inta)
                                    x_a)
                                 ()) ())
                                 (imp_nfoldli
                                   (let (l, _) = a2c in
                                     maps (fun i ->
    sub (sub inv_ia i) (nth l i))
                                       xc)
                                   (fun _ -> (fun () -> true))
                                   (fun ai bi ->
                                     (fun f_ () -> f_
                                       ((abstra_upd_impl
  (linordered_cancel_ab_monoid_add_int, uminus_int, equal_int, heap_int) m ai
  bi)
                                       ()) ())
                                       (fun xe ->
 repair_pair_impl
   ((linordered_ab_monoid_add_DBMEntry
      (linordered_cancel_ab_monoid_add_int, equal_int)),
     (heap_DBMEntry heap_int))
   m xe zero_nata (constraint_clk ai)))))
                       ()) ())
                       (fun x_b ->
                         (fun f_ () -> f_
                           ((check_diag_impla
                              (linordered_cancel_ab_monoid_add_int, heap_int) m
                              m x_b)
                           ()) ())
                           (fun x_c ->
                             (if x_c then (fun () -> x_b)
                               else (fun f_ () -> f_
                                      ((norm_upd_impl
 (linordered_ab_group_add_int, heap_int) m x_b
 (let (l, _) = a2c in
   IArray
     (map (fun c ->
            maxa linorder_int
              (image (fun i -> sub (sub (sub k_i i) (nth l i)) c) xa))
       x))
 m)
                                      ()) ())
                                      (fw_impl_int m))))))))))
()) ())
(fun xd -> (fun () -> (op_list_prepend (a2c, xd) sigma))))
                             else (fun () -> sigma))))
                       [])
                  ()) ())
                  (fun xd ->
                    (fun f_ () -> f_
                      ((imp_nfoldli xd (fun _ -> (fun () -> true))
                         (fun xca sigma ->
                           (fun f_ () -> f_
                             ((let (_, a2) = xca in
                                (fun f_ () -> f_
                                  ((check_diag_impl
                                     (linordered_cancel_ab_monoid_add_int,
                                       heap_int)
                                     m a2)
                                  ()) ())
                                  (fun x_c -> (fun () -> (not x_c))))
                             ()) ())
                             (fun x_c ->
                               (fun () ->
                                 (if x_c then op_list_prepend xca sigma
                                   else sigma))))
                         [])
                      ()) ())
                      (fun xe -> (fun () -> (op_list_rev xe)))))
              in
            let succsa =
              (fun xi ->
                (fun f_ () -> f_
                  ((let (a1, a2) = xi in
                     imp_nfoldli (trans_fun a1) (fun _ -> (fun () -> true))
                       (fun xca sigma ->
                         (let (a1a, (_, (a1c, a2c))) = xca in
                           (fun f_ () -> f_
                             ((amtx_copy (heap_DBMEntry heap_int) a2) ()) ())
                             (fun xba ->
                               (fun f_ () -> f_
                                 (((fun f_ () -> f_
                                     ((up_canonical_upd_impl
(linordered_cancel_ab_monoid_add_int, heap_int) m xba m)
                                     ()) ())
                                    (fun xbb ->
                                      (fun f_ () -> f_
((imp_nfoldli
   (let (l, _) = a1 in maps (fun i -> sub (sub inv_ia i) (nth l i)) xc)
   (fun _ -> (fun () -> true))
   (fun ai bi ->
     (fun f_ () -> f_
       ((abstra_upd_impl
          (linordered_cancel_ab_monoid_add_int, uminus_int, equal_int, heap_int)
          m ai bi)
       ()) ())
       (fun xd ->
         repair_pair_impl
           ((linordered_ab_monoid_add_DBMEntry
              (linordered_cancel_ab_monoid_add_int, equal_int)),
             (heap_DBMEntry heap_int))
           m xd zero_nata (constraint_clk ai)))
   xbb)
()) ())
(fun xbc ->
  (fun f_ () -> f_
    ((check_diag_impla (linordered_cancel_ab_monoid_add_int, heap_int) m m xbc)
    ()) ())
    (fun xd ->
      (fun f_ () -> f_
        ((if xd then (fun () -> xbc)
           else imp_nfoldli a1a (fun _ -> (fun () -> true))
                  (fun ai bi ->
                    (fun f_ () -> f_
                      ((abstra_upd_impl
                         (linordered_cancel_ab_monoid_add_int, uminus_int,
                           equal_int, heap_int)
                         m ai bi)
                      ()) ())
                      (fun xe ->
                        repair_pair_impl
                          ((linordered_ab_monoid_add_DBMEntry
                             (linordered_cancel_ab_monoid_add_int, equal_int)),
                            (heap_DBMEntry heap_int))
                          m xe zero_nata (constraint_clk ai)))
                  xbc)
        ()) ())
        (fun x_a ->
          (fun f_ () -> f_
            ((check_diag_impla (linordered_cancel_ab_monoid_add_int, heap_int) m
               m x_a)
            ()) ())
            (fun xbd ->
              (fun f_ () -> f_
                ((if xbd then (fun () -> x_a)
                   else (fun f_ () -> f_
                          ((imp_nfoldli a1c (fun _ -> (fun () -> true))
                             (fun xcb sigmaa ->
                               reset_canonical_upd_impl
                                 (linordered_cancel_ab_monoid_add_int,
                                   uminus_int, heap_int)
                                 m sigmaa m xcb zero_inta)
                             x_a)
                          ()) ())
                          (imp_nfoldli
                            (let (l, _) = a2c in
                              maps (fun i -> sub (sub inv_ia i) (nth l i)) xc)
                            (fun _ -> (fun () -> true))
                            (fun ai bi ->
                              (fun f_ () -> f_
                                ((abstra_upd_impl
                                   (linordered_cancel_ab_monoid_add_int,
                                     uminus_int, equal_int, heap_int)
                                   m ai bi)
                                ()) ())
                                (fun xe ->
                                  repair_pair_impl
                                    ((linordered_ab_monoid_add_DBMEntry
                                       (linordered_cancel_ab_monoid_add_int,
 equal_int)),
                                      (heap_DBMEntry heap_int))
                                    m xe zero_nata (constraint_clk ai)))))
                ()) ())
                (fun x_b ->
                  (fun f_ () -> f_
                    ((check_diag_impla
                       (linordered_cancel_ab_monoid_add_int, heap_int) m m x_b)
                    ()) ())
                    (fun x_c ->
                      (if x_c then (fun () -> x_b)
                        else (fun f_ () -> f_
                               ((norm_upd_impl
                                  (linordered_ab_group_add_int, heap_int) m x_b
                                  (let (l, _) = a2c in
                                    IArray
                                      (map
(fun c ->
  maxa linorder_int (image (fun i -> sub (sub (sub k_i i) (nth l i)) c) xa))
x))
                                  m)
                               ()) ())
                               (fw_impl_int m))))))))))
                                 ()) ())
                                 (fun xd ->
                                   (fun () ->
                                     (op_list_prepend (a2c, xd) sigma))))))
                       [])
                  ()) ())
                  (fun xd ->
                    (fun f_ () -> f_
                      ((imp_nfoldli xd (fun _ -> (fun () -> true))
                         (fun xca sigma ->
                           (fun f_ () -> f_
                             ((let (_, a2) = xca in
                                (fun f_ () -> f_
                                  ((check_diag_impl
                                     (linordered_cancel_ab_monoid_add_int,
                                       heap_int)
                                     m a2)
                                  ()) ())
                                  (fun x_c -> (fun () -> (not x_c))))
                             ()) ())
                             (fun x_c ->
                               (fun () ->
                                 (if x_c then op_list_prepend xca sigma
                                   else sigma))))
                         [])
                      ()) ())
                      (fun xe -> (fun () -> (op_list_rev xe)))))
              in
            let empty =
              (fun (_, a) ->
                check_diag_impl (linordered_cancel_ab_monoid_add_int, heap_int)
                  m a)
              in
            let a =
              tracei
                (linordered_ab_group_add_int, equal_int, heap_int, show_int) m
                (fun xd ->
                  shows_prec_prod (show_list show_nat) (show_list show_int)
                    zero_nata xd [])
                (fun xd -> shows_prec_nat zero_nata xd [])
              in
             leadsto_impl
               (heap_prod (heap_prod (heap_list heap_nat) (heap_list heap_int))
                 (heap_array (typerep_DBMEntry typerep_int)))
               ((equal_prod (equal_list equal_nat) (equal_list equal_int)),
                 (hashable_prod (hashable_list hashable_nat)
                   (hashable_list hashable_int)),
                 (heap_prod (heap_list heap_nat) (heap_list heap_int)))
               copy succs start suba key succsa empty final finala a)
          ()) ())
          (fun r -> (fun () -> (not r)))));;

let rec dfs_map_impl_0 _A (_B1, _B2, _B3)
  succsi lei keyi copyi x =
    (let (a1, (a1a, a2a)) = x in
      (fun f_ () -> f_ ((keyi a2a) ()) ())
        (fun xa ->
          (fun f_ () -> f_
            ((hms_extract (ht_lookup (_B1, _B2, _B3) (heap_list _A))
               (ht_delete (_B1, _B2, _B3) (heap_list _A)) xa a1a)
            ()) ())
            (fun xaa ->
              (fun f_ () -> f_
                ((match xaa with (None, a2b) -> (fun () -> (a2b, false))
                   | (Some x_c, a2b) ->
                     (fun f_ () -> f_
                       ((imp_nfoldli x_c (fun sigma -> (fun () -> (not sigma)))
                          (fun xf sigma ->
                            (fun f_ () -> f_ ((lei xf a2a) ()) ())
                              (fun x_f -> (fun () -> (x_f || sigma))))
                          false)
                       ()) ())
                       (fun x_d ->
                         (fun f_ () -> f_
                           ((ht_update (_B1, _B2, _B3) (heap_list _A) xa x_c
                              a2b)
                           ()) ())
                           (fun x_e -> (fun () -> (x_e, x_d)))))
                ()) ())
                (fun a ->
                  (match a with (a1b, true) -> (fun () -> (a1, (a1b, true)))
                    | (a1b, false) ->
                      (fun f_ () -> f_ ((keyi a2a) ()) ())
                        (fun xb ->
                          (fun f_ () -> f_
                            ((hms_extract
                               (ht_lookup (_B1, _B2, _B3) (heap_list _A))
                               (ht_delete (_B1, _B2, _B3) (heap_list _A)) xb a1)
                            ()) ())
                            (fun xab ->
                              (fun f_ () -> f_
                                ((match xab
                                   with (None, a2c) -> (fun () -> (a2c, false))
                                   | (Some x_e, a2c) ->
                                     (fun f_ () -> f_
                                       ((lso_bex_impl (lei a2a) x_e) ()) ())
                                       (fun x_f ->
 (fun f_ () -> f_ ((ht_update (_B1, _B2, _B3) (heap_list _A) xb x_e a2c) ()) ())
   (fun x_g -> (fun () -> (x_g, x_f)))))
                                ()) ())
                                (fun aa ->
                                  (match aa
                                    with (a1c, true) ->
                                      (fun () -> (a1c, (a1b, false)))
                                    | (a1c, false) ->
                                      (fun f_ () -> f_ ((copyi a2a) ()) ())
(fun xc ->
  (fun f_ () -> f_ ((keyi xc) ()) ())
    (fun xd ->
      (fun f_ () -> f_
        ((hms_extract (ht_lookup (_B1, _B2, _B3) (heap_list _A))
           (ht_delete (_B1, _B2, _B3) (heap_list _A)) xd a1b)
        ()) ())
        (fun xac ->
          (fun f_ () -> f_
            ((match xac
               with (None, a2d) ->
                 (fun f_ () -> f_ ((copyi a2a) ()) ())
                   (fun xad ->
                     (fun f_ () -> f_
                       ((ht_update (_B1, _B2, _B3) (heap_list _A) xd
                          (op_list_prepend xad []) a2d)
                       ()) ())
                       (fun x_h -> (fun () -> ((), x_h))))
               | (Some x_g, a2d) ->
                 (fun f_ () -> f_ ((copyi a2a) ()) ())
                   (fun xad ->
                     (fun f_ () -> f_
                       ((ht_update (_B1, _B2, _B3) (heap_list _A) xd
                          (op_list_prepend xad x_g) a2d)
                       ()) ())
                       (fun x_i -> (fun () -> ((), x_i)))))
            ()) ())
            (fun (_, a2d) ->
              (fun f_ () -> f_ ((succsi a2a) ()) ())
                (fun xe ->
                  (fun f_ () -> f_
                    ((imp_nfoldli xe (fun (_, (_, b)) -> (fun () -> (not b)))
                       (fun xk (a1e, (a1f, _)) ->
                         dfs_map_impl_0 _A (_B1, _B2, _B3) succsi lei keyi copyi
                           (a1e, (a1f, xk)))
                       (a1c, (a2d, false)))
                    ()) ())
                    (fun (a1e, (a1f, a2f)) ->
                      (fun f_ () -> f_ ((copyi a2a) ()) ())
                        (fun xf ->
                          (fun f_ () -> f_ ((keyi xf) ()) ())
                            (fun xg ->
                              (fun f_ () -> f_
                                ((hms_extract
                                   (ht_lookup (_B1, _B2, _B3) (heap_list _A))
                                   (ht_delete (_B1, _B2, _B3) (heap_list _A)) xg
                                   a1f)
                                ()) ())
                                (fun xad ->
                                  (fun f_ () -> f_
                                    ((match xad
                                       with (None, a2g) ->
 (fun f_ () -> f_ ((ht_update (_B1, _B2, _B3) (heap_list _A) xg [] a2g) ()) ())
   (fun x_k -> (fun () -> ((), x_k)))
                                       | (Some x_j, a2g) ->
 (fun f_ () -> f_
   ((ht_update (_B1, _B2, _B3) (heap_list _A) xg
      (if op_list_is_empty x_j then [] else op_list_tl x_j) a2g)
   ()) ())
   (fun x_l -> (fun () -> ((), x_l))))
                                    ()) ())
                                    (fun (_, a2g) ->
                                      (fun f_ () -> f_ ((copyi a2a) ()) ())
(fun xh ->
  (fun f_ () -> f_ ((keyi xh) ()) ())
    (fun xi ->
      (fun f_ () -> f_
        ((hms_extract (ht_lookup (_B1, _B2, _B3) (heap_list _A))
           (ht_delete (_B1, _B2, _B3) (heap_list _A)) xi a1e)
        ()) ())
        (fun xae ->
          (fun f_ () -> f_
            ((match xae
               with (None, a2h) ->
                 (fun f_ () -> f_ ((copyi a2a) ()) ())
                   (fun xaf ->
                     (fun f_ () -> f_
                       ((ht_update (_B1, _B2, _B3) (heap_list _A) xi [xaf] a2h)
                       ()) ())
                       (fun x_m -> (fun () -> ((), x_m))))
               | (Some x_l, a2h) ->
                 (fun f_ () -> f_ ((copyi a2a) ()) ())
                   (fun xaf ->
                     (fun f_ () -> f_
                       ((ht_update (_B1, _B2, _B3) (heap_list _A) xi
                          (xaf :: x_l) a2h)
                       ()) ())
                       (fun x_n -> (fun () -> ((), x_n)))))
            ()) ())
            (fun (_, a2h) ->
              (fun f_ () -> f_ (tRACE_impl ()) ())
                (fun _ ->
                  (fun () -> (a2h, (a2g, a2f)))))))))))))))))))))))))));;

let rec dfs_map_impl _A (_B1, _B2, _B3)
  succsi a_0i lei keyi copyi =
    (fun f_ () -> f_ ((ht_new (_B2, _B3) (heap_list _A)) ()) ())
      (fun x ->
        (fun f_ () -> f_ ((ht_new (_B2, _B3) (heap_list _A)) ()) ())
          (fun xa ->
            (fun f_ () -> f_ (a_0i ()) ())
              (fun xb ->
                (fun f_ () -> f_
                  ((dfs_map_impl_0 _A (_B1, _B2, _B3) succsi lei keyi copyi
                     (x, (xa, xb)))
                  ()) ())
                  (fun xc ->
                    (fun f_ () -> f_
                      ((let (a1, (_, a2a)) = xc in (fun () -> (a2a, a1))) ())
                      ())
                      (fun (a1, _) -> (fun () -> a1))))));;

let rec alw_ev_checker
  p m max_steps inv trans prog bounds pred s_0 na k formula =
    (let x = upt zero_nata (plus_nata m one_nata) in
     let xa = Set (upt zero_nata p) in
     let xb = upt zero_nata na in
     let xc = upt zero_nata p in
     let proga = IArray prog in
     let progt_ia = IArray (map (map_option stript) prog) in
     let progf_ia = IArray (map (map_option stripf) prog) in
     let len_prog = size_list prog in
     let progb =
       (fun pc -> (if less_nat pc len_prog then sub proga pc else None)) in
     let pt =
       (fun pc -> (if less_nat pc len_prog then sub progt_ia pc else None)) in
     let pf =
       (fun pc -> (if less_nat pc len_prog then sub progf_ia pc else None)) in
     let boundsa = IArray bounds in
     let trans_i_mapa = IArray (map (fun a -> IArray a) (trans_i_map trans)) in
     let trans_in_mapa = IArray (map (fun a -> IArray a) (trans_in_map trans))
       in
     let trans_out_mapa = IArray (map (fun a -> IArray a) (trans_out_map trans))
       in
     let inv_ia = IArray (map (fun a -> IArray a) inv) in
     let trans_fun =
       (fun l ->
         (let (la, s) = l in
          let ina =
            all_actions_by_state_impl xc (map (fun _ -> []) xb) trans_in_mapa la
            in
          let out =
            all_actions_by_state_impl xc (map (fun _ -> []) xb) trans_out_mapa
              la
            in
           maps (fun a ->
                  pairs_by_action_impl p max_steps pred pf pt progb boundsa
                    (la, s) (nth out a) (nth ina a))
             xb) @
           maps (trans_i_from_impl p max_steps pred bounds pf pt progb boundsa
                  trans_i_mapa l)
             xc)
       in
     let k_i =
       IArray
         (map (comp (fun a -> IArray a)
                (map (comp (fun a -> IArray a) (map int_of_nat))))
           k)
       in
      (fun f_ () -> f_
        ((let key = comp (fun a -> (fun () -> a)) fst in
          let suba =
            (fun ai bi ->
              (let (a1, a2) = ai in
               let (a1a, a2a) = bi in
                (if equal_proda (equal_list equal_nat) (equal_list equal_int) a1
                      a1a
                  then dbm_subset_impl
                         (linordered_cancel_ab_monoid_add_int, equal_int,
                           heap_int)
                         m a2 a2a
                  else (fun () -> false))))
            in
          let copy =
            (fun (a1, a2) ->
              (fun f_ () -> f_ ((amtx_copy (heap_DBMEntry heap_int) a2) ()) ())
                (fun xd -> (fun () -> (a1, xd))))
            in
          let start =
            (fun f_ () -> f_
              ((amtx_dflt (heap_DBMEntry heap_int) (suc m) (suc m)
                 (Le zero_inta))
              ()) ())
              (fun x_a -> (fun () -> ((init p, s_0), x_a)))
            in
          let succs =
            (fun xi ->
              (fun f_ () -> f_
                ((let (a1, a2) = xi in
                   imp_nfoldli (trans_fun a1) (fun _ -> (fun () -> true))
                     (fun xca sigma ->
                       (let (a1a, (_, (a1c, a2c))) = xca in
                         (if (let (a, b) = a2c in hd_of_formula formula a b)
                           then (fun f_ () -> f_
                                  ((amtx_copy (heap_DBMEntry heap_int) a2) ())
                                  ())
                                  (fun xba ->
                                    (fun f_ () -> f_
                                      (((fun f_ () -> f_
  ((up_canonical_upd_impl (linordered_cancel_ab_monoid_add_int, heap_int) m xba
     m)
  ()) ())
 (fun xbb ->
   (fun f_ () -> f_
     ((imp_nfoldli
        (let (l, _) = a1 in maps (fun i -> sub (sub inv_ia i) (nth l i)) xc)
        (fun _ -> (fun () -> true))
        (fun ai bi ->
          (fun f_ () -> f_
            ((abstra_upd_impl
               (linordered_cancel_ab_monoid_add_int, uminus_int, equal_int,
                 heap_int)
               m ai bi)
            ()) ())
            (fun xd ->
              repair_pair_impl
                ((linordered_ab_monoid_add_DBMEntry
                   (linordered_cancel_ab_monoid_add_int, equal_int)),
                  (heap_DBMEntry heap_int))
                m xd zero_nata (constraint_clk ai)))
        xbb)
     ()) ())
     (fun xbc ->
       (fun f_ () -> f_
         ((check_diag_impla (linordered_cancel_ab_monoid_add_int, heap_int) m m
            xbc)
         ()) ())
         (fun xd ->
           (fun f_ () -> f_
             ((if xd then (fun () -> xbc)
                else imp_nfoldli a1a (fun _ -> (fun () -> true))
                       (fun ai bi ->
                         (fun f_ () -> f_
                           ((abstra_upd_impl
                              (linordered_cancel_ab_monoid_add_int, uminus_int,
                                equal_int, heap_int)
                              m ai bi)
                           ()) ())
                           (fun xe ->
                             repair_pair_impl
                               ((linordered_ab_monoid_add_DBMEntry
                                  (linordered_cancel_ab_monoid_add_int,
                                    equal_int)),
                                 (heap_DBMEntry heap_int))
                               m xe zero_nata (constraint_clk ai)))
                       xbc)
             ()) ())
             (fun x_a ->
               (fun f_ () -> f_
                 ((check_diag_impla
                    (linordered_cancel_ab_monoid_add_int, heap_int) m m x_a)
                 ()) ())
                 (fun xbd ->
                   (fun f_ () -> f_
                     ((if xbd then (fun () -> x_a)
                        else (fun f_ () -> f_
                               ((imp_nfoldli a1c (fun _ -> (fun () -> true))
                                  (fun xcb sigmaa ->
                                    reset_canonical_upd_impl
                                      (linordered_cancel_ab_monoid_add_int,
uminus_int, heap_int)
                                      m sigmaa m xcb zero_inta)
                                  x_a)
                               ()) ())
                               (imp_nfoldli
                                 (let (l, _) = a2c in
                                   maps (fun i -> sub (sub inv_ia i) (nth l i))
                                     xc)
                                 (fun _ -> (fun () -> true))
                                 (fun ai bi ->
                                   (fun f_ () -> f_
                                     ((abstra_upd_impl
(linordered_cancel_ab_monoid_add_int, uminus_int, equal_int, heap_int) m ai bi)
                                     ()) ())
                                     (fun xe ->
                                       repair_pair_impl
 ((linordered_ab_monoid_add_DBMEntry
    (linordered_cancel_ab_monoid_add_int, equal_int)),
   (heap_DBMEntry heap_int))
 m xe zero_nata (constraint_clk ai)))))
                     ()) ())
                     (fun x_b ->
                       (fun f_ () -> f_
                         ((check_diag_impla
                            (linordered_cancel_ab_monoid_add_int, heap_int) m m
                            x_b)
                         ()) ())
                         (fun x_c ->
                           (if x_c then (fun () -> x_b)
                             else (fun f_ () -> f_
                                    ((norm_upd_impl
                                       (linordered_ab_group_add_int, heap_int) m
                                       x_b (let (l, _) = a2c in
     IArray
       (map (fun c ->
              maxa linorder_int
                (image (fun i -> sub (sub (sub k_i i) (nth l i)) c) xa))
         x))
                                       m)
                                    ()) ())
                                    (fw_impl_int m))))))))))
                                      ()) ())
                                      (fun xd ->
(fun () -> (op_list_prepend (a2c, xd) sigma))))
                           else (fun () -> sigma))))
                     [])
                ()) ())
                (fun xd ->
                  (fun f_ () -> f_
                    ((imp_nfoldli xd (fun _ -> (fun () -> true))
                       (fun xca sigma ->
                         (fun f_ () -> f_
                           ((let (_, a2) = xca in
                              (fun f_ () -> f_
                                ((check_diag_impl
                                   (linordered_cancel_ab_monoid_add_int,
                                     heap_int)
                                   m a2)
                                ()) ())
                                (fun x_c -> (fun () -> (not x_c))))
                           ()) ())
                           (fun x_c ->
                             (fun () ->
                               (if x_c then op_list_prepend xca sigma
                                 else sigma))))
                       [])
                    ()) ())
                    (fun xe -> (fun () -> (op_list_rev xe)))))
            in
           dfs_map_impl
             (heap_prod (heap_prod (heap_list heap_nat) (heap_list heap_int))
               (heap_array (typerep_DBMEntry typerep_int)))
             ((equal_prod (equal_list equal_nat) (equal_list equal_int)),
               (hashable_prod (hashable_list hashable_nat)
                 (hashable_list hashable_int)),
               (heap_prod (heap_list heap_nat) (heap_list heap_int)))
             succs start suba key copy)
        ()) ())
        (fun xd ->
          (fun f_ () -> f_ ((fun () -> ()) ()) ()) (fun _ -> (fun () -> xd))));;

let rec model_checker
  p m max_steps inv trans prog bounds pred s_0 na k formula =
    (match formula
      with EX _ ->
        reachability_checker p m max_steps inv trans prog bounds pred s_0 na k
          formula
      | EG _ ->
        (if (let (a, b) = (init p, s_0) in hd_of_formula formula a b)
          then alw_ev_checker p m max_steps inv trans prog bounds pred s_0 na k
                 formula
          else (fun () -> false))
      | AX _ ->
        (fun f_ () -> f_
          ((if (let (a, b) = (init p, s_0) in hd_of_formula formula a b)
             then alw_ev_checker p m max_steps inv trans prog bounds pred s_0 na
                    k formula
             else (fun () -> false))
          ()) ())
          (fun r -> (fun () -> (not r)))
      | AG _ ->
        (fun f_ () -> f_
          ((reachability_checker p m max_steps inv trans prog bounds pred s_0 na
             k formula)
          ()) ())
          (fun r -> (fun () -> (not r)))
      | Leadsto (_, a) ->
        leadsto_checker p m max_steps inv trans prog bounds pred s_0 na k
          formula a);;

let rec precond_mc
  pa m k max_steps i t prog final bounds p s_0 na =
    (if uPPAAL_Reachability_Problem_precompileda pa m max_steps i t prog bounds
          p s_0 na k
      then (fun f_ () -> f_
             ((model_checker pa m max_steps i t prog bounds p s_0 na k final)
             ()) ())
             (fun x -> (fun () -> (Some x)))
      else (fun () -> None));;

let rec calc_shortest_scc_paths (_A1, _A2, _A3)
  g n = (let sccs = compute_SCC_tr (equal_nat, hashable_nat) g in
         let d = map (fun _ -> None) (upt zero_nata n) @ [Some (zero _A2)] in
         let da =
           fold (fold (fun u ->
                        fold (fun v da ->
                               (match nth da u with None -> da
                                 | Some du ->
                                   (match nth da v
                                     with None ->
                                       list_update da v
 (Some (plus _A1 du (more g u v)))
                                     | Some dv ->
                                       (if less _A3 (plus _A1 du (more g u v))
     dv
 then list_update da v (Some (plus _A1 du (more g u v))) else da))))
                          (gi_E g u)))
             sccs d
           in
         let db =
           fold (fun vs db ->
                  (let dscc =
                     fold (fun v dscc ->
                            (match dscc with None -> nth db v
                              | Some daa ->
                                (match nth db v with None -> dscc
                                  | Some dv -> Some (min _A3 dv daa))))
                       vs None
                     in
                    fold (fun v dc -> list_update dc v dscc) vs db))
             sccs da
           in
          db);;

let rec resets
  trans prog q c l =
    fold (fun (_, (_, (r, la))) xs ->
           (if membera equal_nat xs la ||
                 member equal_nat c (image fst (collect_storea prog r))
             then xs else la :: xs))
      (nth (nth trans q) l) [];;

let rec ea trans prog q c l = resets trans prog q c l;;

let rec n trans q = size_list (nth trans q);;

let rec e
  trans prog q c l =
    (if equal_nata l (n trans q) then upt zero_nata (n trans q)
      else filtera (fun la -> membera equal_nat (ea trans prog q c la) l)
             (upt zero_nata (n trans q)));;

let rec bound_inv
  inv q c l =
    maxa linorder_int
      (sup_set equal_int (insert equal_int zero_inta bot_set)
        (sup_seta equal_int
          (image
            (fun (x, d) ->
              (if equal_nata x c then insert equal_int d bot_set else bot_set))
            (collect_clock_pairs (nth (nth inv q) l)))));;

let rec bound_g
  max_steps inv trans prog q c l =
    maxa linorder_int
      (sup_set equal_int (insert equal_int zero_inta bot_set)
        (sup_seta equal_int
          (image
            (fun (x, d) ->
              (if equal_nata x c then insert equal_int d bot_set else bot_set))
            (clkp_set max_steps inv trans prog q l))));;

let rec bound
  max_steps inv trans prog q c l =
    max ord_int (bound_g max_steps inv trans prog q c l) (bound_inv inv q c l);;

let rec w
  max_steps inv trans prog q c la l =
    (if equal_nata la (n trans q)
      then uminus_inta (bound max_steps inv trans prog q c l) else zero_inta);;

let rec v trans q = (fun v -> less_eq_nat v (n trans q));;

let rec g
  max_steps inv trans prog q c =
    Gen_g_impl_ext
      (v trans q, e trans prog q c, [n trans q],
        w max_steps inv trans prog q c);;

let rec local_ceiling
  max_steps inv trans prog q c =
    (let a =
       calc_shortest_scc_paths (plus_int, zero_int, ord_int)
         (g max_steps inv trans prog q c) (n trans q)
       in
      map (fun aa ->
            (match aa with None -> zero_inta | Some ab -> uminus_inta ab))
        a);;

let rec k
  p m max_steps inv trans prog =
    app rev
      (fold (fun q xs ->
              app (fun x -> rev x :: xs)
                (fold (fun l xsa ->
                        app (fun x -> (zero_inta :: rev x) :: xsa)
                          (fold (fun c ->
                                  (fun a ->
                                    nth (local_ceiling max_steps inv trans prog
  q c)
                                      l ::
                                      a))
                            (upt one_nata (suc m)) []))
                  (upt zero_nata (n trans q)) []))
        (upt zero_nata p) []);;

end;; (*struct Model_Checker*)

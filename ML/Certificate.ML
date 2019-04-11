
structure Uint : sig
  val set_bit : Word.word -> IntInf.int -> bool -> Word.word
  val shiftl : Word.word -> IntInf.int -> Word.word
  val shiftr : Word.word -> IntInf.int -> Word.word
  val shiftr_signed : Word.word -> IntInf.int -> Word.word
  val test_bit : Word.word -> IntInf.int -> bool
end = struct

fun set_bit x n b =
  let val mask = Word.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))
  in if b then Word.orb (x, mask)
     else Word.andb (x, Word.notb mask)
  end

fun shiftl x n =
  Word.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word.andb (x, Word.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word.fromInt 0

end; (* struct Uint *)


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


(* Test that words can handle numbers between 0 and 31 *)
val _ = if 5 <= Word.wordSize then () else raise (Fail ("wordSize less than 5"));

structure Uint32 : sig
  val set_bit : Word32.word -> IntInf.int -> bool -> Word32.word
  val shiftl : Word32.word -> IntInf.int -> Word32.word
  val shiftr : Word32.word -> IntInf.int -> Word32.word
  val shiftr_signed : Word32.word -> IntInf.int -> Word32.word
  val test_bit : Word32.word -> IntInf.int -> bool
end = struct

fun set_bit x n b =
  let val mask = Word32.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))
  in if b then Word32.orb (x, mask)
     else Word32.andb (x, Word32.notb mask)
  end

fun shiftl x n =
  Word32.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word32.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word32.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word32.andb (x, Word32.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word32.fromInt 0

end; (* struct Uint32 *)


structure Integer: sig
  val div_mod: int -> int -> int * int
end = struct
  fun div_mod i j = (i div j, i mod j)
end



structure STArray = struct

datatype 'a Cell = Invalid | Value of 'a array;

exception AccessedOldVersion;

type 'a array = 'a Cell Unsynchronized.ref;

fun fromList l = Unsynchronized.ref (Value (Array.fromList l));
fun array (size, v) = Unsynchronized.ref (Value (Array.array (size,v)));
fun tabulate (size, f) = Unsynchronized.ref (Value (Array.tabulate(size, f)));
fun sub (Unsynchronized.ref Invalid, idx) = raise AccessedOldVersion |
    sub (Unsynchronized.ref (Value a), idx) = Array.sub (a,idx);
fun update (aref,idx,v) =
  case aref of
    (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
    (Unsynchronized.ref (Value a)) => (
      aref := Invalid;
      Array.update (a,idx,v);
      Unsynchronized.ref (Value a)
    );

fun length (Unsynchronized.ref Invalid) = raise AccessedOldVersion |
    length (Unsynchronized.ref (Value a)) = Array.length a

fun grow (aref, i, x) = case aref of
  (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
  (Unsynchronized.ref (Value a)) => (
    let val len=Array.length a;
        val na = Array.array (len+i,x)
    in
      aref := Invalid;
      Array.copy {src=a, dst=na, di=0};
      Unsynchronized.ref (Value na)
    end
    );

fun shrink (aref, sz) = case aref of
  (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
  (Unsynchronized.ref (Value a)) => (
    if sz > Array.length a then
      raise Size
    else (
      aref:=Invalid;
      Unsynchronized.ref (Value (Array.tabulate (sz,fn i => Array.sub (a,i))))
    )
  );

structure IsabelleMapping = struct
type 'a ArrayType = 'a array;

fun new_array (a:'a) (n:IntInf.int) = array (IntInf.toInt n, a);

fun array_length (a:'a ArrayType) = IntInf.fromInt (length a);

fun array_get (a:'a ArrayType) (i:IntInf.int) = sub (a, IntInf.toInt i);

fun array_set (a:'a ArrayType) (i:IntInf.int) (e:'a) = update (a, IntInf.toInt i, e);

fun array_of_list (xs:'a list) = fromList xs;

fun array_grow (a:'a ArrayType) (i:IntInf.int) (x:'a) = grow (a, IntInf.toInt i, x);

fun array_shrink (a:'a ArrayType) (sz:IntInf.int) = shrink (a,IntInf.toInt sz);

end;

end;

structure FArray = struct
  datatype 'a Cell = Value of 'a Array.array | Upd of (int*'a*'a Cell Unsynchronized.ref);

  type 'a array = 'a Cell Unsynchronized.ref;

  fun array (size,v) = Unsynchronized.ref (Value (Array.array (size,v)));
  fun tabulate (size, f) = Unsynchronized.ref (Value (Array.tabulate(size, f)));
  fun fromList l = Unsynchronized.ref (Value (Array.fromList l));

  fun sub (Unsynchronized.ref (Value a), idx) = Array.sub (a,idx) |
      sub (Unsynchronized.ref (Upd (i,v,cr)),idx) =
        if i=idx then v
        else sub (cr,idx);

  fun length (Unsynchronized.ref (Value a)) = Array.length a |
      length (Unsynchronized.ref (Upd (i,v,cr))) = length cr;

  fun realize_aux (aref, v) =
    case aref of
      (Unsynchronized.ref (Value a)) => (
        let
          val len = Array.length a;
          val a' = Array.array (len,v);
        in
          Array.copy {src=a, dst=a', di=0};
          Unsynchronized.ref (Value a')
        end
      ) |
      (Unsynchronized.ref (Upd (i,v,cr))) => (
        let val res=realize_aux (cr,v) in
          case res of
            (Unsynchronized.ref (Value a)) => (Array.update (a,i,v); res)
        end
      );

  fun realize aref =
    case aref of
      (Unsynchronized.ref (Value _)) => aref |
      (Unsynchronized.ref (Upd (i,v,cr))) => realize_aux(aref,v);

  fun update (aref,idx,v) =
    case aref of
      (Unsynchronized.ref (Value a)) => (
        let val nref=Unsynchronized.ref (Value a) in
          aref := Upd (idx,Array.sub(a,idx),nref);
          Array.update (a,idx,v);
          nref
        end
      ) |
      (Unsynchronized.ref (Upd _)) =>
        let val ra = realize_aux(aref,v) in
          case ra of
            (Unsynchronized.ref (Value a)) => Array.update (a,idx,v);
          ra
        end
      ;

  fun grow (aref, inc, x) = case aref of
    (Unsynchronized.ref (Value a)) => (
      let val len=Array.length a;
          val na = Array.array (len+inc,x)
      in
        Array.copy {src=a, dst=na, di=0};
        Unsynchronized.ref (Value na)
      end
      )
  | (Unsynchronized.ref (Upd _)) => (
    grow (realize aref, inc, x)
  );

  fun shrink (aref, sz) = case aref of
    (Unsynchronized.ref (Value a)) => (
      if sz > Array.length a then
        raise Size
      else (
        Unsynchronized.ref (Value (Array.tabulate (sz,fn i => Array.sub (a,i))))
      )
    ) |
    (Unsynchronized.ref (Upd _)) => (
      shrink (realize aref,sz)
    );

structure IsabelleMapping = struct
type 'a ArrayType = 'a array;

fun new_array (a:'a) (n:IntInf.int) = array (IntInf.toInt n, a);

fun array_length (a:'a ArrayType) = IntInf.fromInt (length a);

fun array_get (a:'a ArrayType) (i:IntInf.int) = sub (a, IntInf.toInt i);

fun array_set (a:'a ArrayType) (i:IntInf.int) (e:'a) = update (a, IntInf.toInt i, e);

fun array_of_list (xs:'a list) = fromList xs;

fun array_grow (a:'a ArrayType) (i:IntInf.int) (x:'a) = grow (a, IntInf.toInt i, x);

fun array_shrink (a:'a ArrayType) (sz:IntInf.int) = shrink (a,IntInf.toInt sz);

fun array_get_oo (d:'a) (a:'a ArrayType) (i:IntInf.int) =
  sub (a,IntInf.toInt i) handle Subscript => d

fun array_set_oo (d:(unit->'a ArrayType)) (a:'a ArrayType) (i:IntInf.int) (e:'a) =
  update (a, IntInf.toInt i, e) handle Subscript => d ()

end;
end;





structure Tracing : sig
  val count_up : unit -> unit
  val get_count : unit -> int
end = struct
  val counter = Unsynchronized.ref 0;
  fun count_up () = (counter := !counter + 1);
  fun get_count () = !counter;
end



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



   fun array_blit src si dst di len = (
      src=dst andalso raise Fail ("array_blit: Same arrays");
      ArraySlice.copy {
        di = IntInf.toInt di,
        src = ArraySlice.slice (src,IntInf.toInt si,SOME (IntInf.toInt len)),
        dst = dst})

    fun array_nth_oo v a i () = Array.sub(a,IntInf.toInt i) handle Subscript => v | Overflow => v
    fun array_upd_oo f i x a () = 
      (Array.update(a,IntInf.toInt i,x); a) handle Subscript => f () | Overflow => f ()

    


  structure Statistics : sig
    type stat_entry = string * (unit -> bool) * (unit -> string)
  
    val register_stat : stat_entry -> unit
    val get_active_stats : unit -> (string * string) list
    val pretty_stats : (string * string) list -> string

  end = struct
    type stat_entry = string * (unit -> bool) * (unit -> string)
    val stats : stat_entry list Unsynchronized.ref = Unsynchronized.ref []
  
    fun register_stat e = stats := e :: !stats

    fun get_active_stats () = let
      fun flt [] = []
        | flt ((n,a,s)::l) = if a () then (n,s ()) :: flt l else flt l

    in flt (!stats)
    end

    fun pretty_stats [] = ""
      | pretty_stats ((n,s)::l) = "=== " ^ n ^ " ===\n" ^ s ^ "\n" ^ pretty_stats l
  end

(* Argh! Functors not compatible with ML_val command!
  functor Timer () : sig 
    val reset : unit -> unit
    val start : unit -> unit
    val stop : unit -> unit
    val set : Time.time -> unit
    val get : unit -> Time.time
    val pretty : unit -> string
  end = struct

    open Time;

    val time : Time.time Unsynchronized.ref = Unsynchronized.ref Time.zeroTime
    val running : bool Unsynchronized.ref = Unsynchronized.ref false
    val start_time : Time.time Unsynchronized.ref = Unsynchronized.ref Time.zeroTime
        
    fun reset () = (
      time := Time.zeroTime;
      running := false;
      start_time := Time.zeroTime
    )

    fun start () = 
      if !running then 
        () 
      else (
        running := true;
        start_time := Time.now ()
      )

    fun this_runs_time () = 
      if !running then 
        Time.now () - !start_time 
      else 
        Time.zeroTime

    fun stop () = (
      time := !time + this_runs_time ();
      running := false
    )

    fun get () = !time + this_runs_time ()
    fun set t = time := t - this_runs_time ()
  
    fun pretty () = Time.toString (!time) ^ "s"
  end
  *)





structure Gabow_Skeleton_Statistics = struct end

structure Model_Checker : sig
  datatype inta = Int_of_integer of int
  type nat
  val nat_of_integer : int -> nat
  type char
  datatype 'a dBMEntry = Le of 'a | Lt of 'a | INF
  type 'a act
  type ('a, 'b) bexp
  type ('a, 'b) exp
  type ('a, 'b) acconstraint
  type 'a set
  type ('a, 'b) sum
  type json
  type time
  datatype 'a result = Result of 'a | Error of string list
  type 'a len_list
  type resulta
  datatype mode = Impl1 | Impl2 | Impl3
  type ('a, 'b, 'c, 'd) formula
  val e_op_impl :
    nat ->
      (nat, inta) acconstraint list ->
        nat list ->
          (nat, inta) acconstraint list ->
            (nat, inta) acconstraint list ->
              inta dBMEntry array -> (unit -> (inta dBMEntry array))
  val parse_convert_check :
    mode ->
      nat ->
        bool ->
          string ->
            string ->
              ((inta list * inta list) * (inta dBMEntry list) list) list ->
                (unit -> unit)
  val parse_convert_run_check : mode -> nat -> bool -> string -> (unit -> unit)
  val parse_convert_run_print : bool -> string -> (unit -> unit)
end = struct

datatype inta = Int_of_integer of int;

fun integer_of_int (Int_of_integer k) = k;

fun equal_inta k l = integer_of_int k = integer_of_int l;

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_int = {equal = equal_inta} : inta equal;

datatype typerepa = Typerep of string * typerepa list;

datatype 'a itself = Type;

fun typerep_inta t = Typerep ("Int.int", []);

type 'a typerep = {typerep : 'a itself -> typerepa};
val typerep = #typerep : 'a typerep -> 'a itself -> typerepa;

type 'a countable = {};

type 'a heap = {countable_heap : 'a countable, typerep_heap : 'a typerep};
val countable_heap = #countable_heap : 'a heap -> 'a countable;
val typerep_heap = #typerep_heap : 'a heap -> 'a typerep;

val countable_int = {} : inta countable;

val typerep_int = {typerep = typerep_inta} : inta typerep;

val heap_int = {countable_heap = countable_int, typerep_heap = typerep_int} :
  inta heap;

fun uminus_inta k = Int_of_integer (~ (integer_of_int k));

val zero_inta : inta = Int_of_integer (0 : IntInf.int);

datatype num = One | Bit0 of num | Bit1 of num;

fun sgn_integer k =
  (if k = (0 : IntInf.int) then (0 : IntInf.int)
    else (if k < (0 : IntInf.int) then (~1 : IntInf.int)
           else (1 : IntInf.int)));

fun apsnd f (x, y) = (x, f y);

fun divmod_integer k l =
  (if k = (0 : IntInf.int) then ((0 : IntInf.int), (0 : IntInf.int))
    else (if l = (0 : IntInf.int) then ((0 : IntInf.int), k)
           else (apsnd o (fn a => fn b => a * b) o sgn_integer) l
                  (if sgn_integer k = sgn_integer l
                    then Integer.div_mod (abs k) (abs l)
                    else let
                           val (r, s) = Integer.div_mod (abs k) (abs l);
                         in
                           (if s = (0 : IntInf.int) then (~ r, (0 : IntInf.int))
                             else (~ r - (1 : IntInf.int), abs l - s))
                         end)));

fun snd (x1, x2) = x2;

fun modulo_integer k l = snd (divmod_integer k l);

datatype nat = Nat of int;

fun integer_of_nat (Nat x) = x;

fun modulo_nat m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

fun fst (x1, x2) = x1;

fun divide_integer k l = fst (divmod_integer k l);

fun divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

fun equal_nata m n = integer_of_nat m = integer_of_nat n;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun max A_ a b = (if less_eq A_ a b then b else a);

val ord_integer =
  {less_eq = (fn a => fn b => a <= b), less = (fn a => fn b => a < b)} :
  int ord;

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

val zero_nata : nat = Nat (0 : IntInf.int);

val one_nata : nat = Nat (1 : IntInf.int);

datatype char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;

fun string_of_digit n =
  (if equal_nata n zero_nata
    then [Chara (false, false, false, false, true, true, false, false)]
    else (if equal_nata n one_nata
           then [Chara (true, false, false, false, true, true, false, false)]
           else (if equal_nata n (nat_of_integer (2 : IntInf.int))
                  then [Chara (false, true, false, false, true, true, false,
                                false)]
                  else (if equal_nata n (nat_of_integer (3 : IntInf.int))
                         then [Chara (true, true, false, false, true, true,
                                       false, false)]
                         else (if equal_nata n (nat_of_integer (4 : IntInf.int))
                                then [Chara
(false, false, true, false, true, true, false, false)]
                                else (if equal_nata n
   (nat_of_integer (5 : IntInf.int))
                                       then [Chara
       (true, false, true, false, true, true, false, false)]
                                       else (if equal_nata n
          (nat_of_integer (6 : IntInf.int))
      then [Chara (false, true, true, false, true, true, false, false)]
      else (if equal_nata n (nat_of_integer (7 : IntInf.int))
             then [Chara (true, true, true, false, true, true, false, false)]
             else (if equal_nata n (nat_of_integer (8 : IntInf.int))
                    then [Chara (false, false, false, true, true, true, false,
                                  false)]
                    else [Chara (true, false, false, true, true, true, false,
                                  false)])))))))));

fun less_nat m n = integer_of_nat m < integer_of_nat n;

fun shows_string x = (fn a => x @ a);

fun showsp_nat p n =
  (if less_nat n (nat_of_integer (10 : IntInf.int))
    then shows_string (string_of_digit n)
    else showsp_nat p (divide_nat n (nat_of_integer (10 : IntInf.int))) o
           shows_string
             (string_of_digit
               (modulo_nat n (nat_of_integer (10 : IntInf.int)))));

fun less_int k l = integer_of_int k < integer_of_int l;

fun nat k = Nat (max ord_integer (0 : IntInf.int) (integer_of_int k));

fun showsp_int p i =
  (if less_int i zero_inta
    then shows_string
           [Chara (true, false, true, true, false, true, false, false)] o
           showsp_nat p (nat (uminus_inta i))
    else showsp_nat p (nat i));

fun shows_prec_int x = showsp_int x;

fun shows_sep s sep [] = shows_string []
  | shows_sep s sep [x] = s x
  | shows_sep s sep (x :: v :: va) = s x o sep o shows_sep s sep (v :: va);

fun null [] = true
  | null (x :: xs) = false;

fun shows_list_gen showsx e l s r xs =
  (if null xs then shows_string e
    else shows_string l o shows_sep showsx (shows_string s) xs o
           shows_string r);

fun showsp_list s p xs =
  shows_list_gen (s zero_nata)
    [Chara (true, true, false, true, true, false, true, false),
      Chara (true, false, true, true, true, false, true, false)]
    [Chara (true, true, false, true, true, false, true, false)]
    [Chara (false, false, true, true, false, true, false, false),
      Chara (false, false, false, false, false, true, false, false)]
    [Chara (true, false, true, true, true, false, true, false)] xs;

fun shows_list_int x = showsp_list shows_prec_int zero_nata x;

type 'a show =
  {shows_prec : nat -> 'a -> char list -> char list,
    shows_list : 'a list -> char list -> char list};
val shows_prec = #shows_prec : 'a show -> nat -> 'a -> char list -> char list;
val shows_list = #shows_list : 'a show -> 'a list -> char list -> char list;

val show_int = {shows_prec = shows_prec_int, shows_list = shows_list_int} :
  inta show;

fun plus_inta k l = Int_of_integer (integer_of_int k + integer_of_int l);

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_int = {plus = plus_inta} : inta plus;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_int = {zero = zero_inta} : inta zero;

fun minus_inta k l = Int_of_integer (integer_of_int k - integer_of_int l);

type 'a minus = {minus : 'a -> 'a -> 'a};
val minus = #minus : 'a minus -> 'a -> 'a -> 'a;

val minus_int = {minus = minus_inta} : inta minus;

type 'a uminus = {uminus : 'a -> 'a};
val uminus = #uminus : 'a uminus -> 'a -> 'a;

val uminus_int = {uminus = uminus_inta} : inta uminus;

fun less_eq_int k l = integer_of_int k <= integer_of_int l;

val ord_int = {less_eq = less_eq_int, less = less_int} : inta ord;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

val preorder_int = {ord_preorder = ord_int} : inta preorder;

val order_int = {preorder_order = preorder_int} : inta order;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a cancel_semigroup_add =
  {semigroup_add_cancel_semigroup_add : 'a semigroup_add};
val semigroup_add_cancel_semigroup_add = #semigroup_add_cancel_semigroup_add :
  'a cancel_semigroup_add -> 'a semigroup_add;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add, zero_monoid_add : 'a zero};
val semigroup_add_monoid_add = #semigroup_add_monoid_add :
  'a monoid_add -> 'a semigroup_add;
val zero_monoid_add = #zero_monoid_add : 'a monoid_add -> 'a zero;

type 'a group_add =
  {cancel_semigroup_add_group_add : 'a cancel_semigroup_add,
    minus_group_add : 'a minus, monoid_add_group_add : 'a monoid_add,
    uminus_group_add : 'a uminus};
val cancel_semigroup_add_group_add = #cancel_semigroup_add_group_add :
  'a group_add -> 'a cancel_semigroup_add;
val minus_group_add = #minus_group_add : 'a group_add -> 'a minus;
val monoid_add_group_add = #monoid_add_group_add :
  'a group_add -> 'a monoid_add;
val uminus_group_add = #uminus_group_add : 'a group_add -> 'a uminus;

val semigroup_add_int = {plus_semigroup_add = plus_int} : inta semigroup_add;

val cancel_semigroup_add_int =
  {semigroup_add_cancel_semigroup_add = semigroup_add_int} :
  inta cancel_semigroup_add;

val monoid_add_int =
  {semigroup_add_monoid_add = semigroup_add_int, zero_monoid_add = zero_int} :
  inta monoid_add;

val group_add_int =
  {cancel_semigroup_add_group_add = cancel_semigroup_add_int,
    minus_group_add = minus_int, monoid_add_group_add = monoid_add_int,
    uminus_group_add = uminus_int}
  : inta group_add;

fun def_hashmap_size_int x = (fn _ => nat_of_integer (16 : IntInf.int)) x;

type 'a hashable =
  {hashcode : 'a -> Word32.word, def_hashmap_size : 'a itself -> nat};
val hashcode = #hashcode : 'a hashable -> 'a -> Word32.word;
val def_hashmap_size = #def_hashmap_size : 'a hashable -> 'a itself -> nat;

fun uint32_of_int i = Word32.fromLargeInt (IntInf.toLarge (integer_of_int i));

fun hashcode_int i = uint32_of_int i;

val hashable_int =
  {hashcode = hashcode_int, def_hashmap_size = def_hashmap_size_int} :
  inta hashable;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

val linorder_int = {order_linorder = order_int} : inta linorder;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};
val semigroup_add_ab_semigroup_add = #semigroup_add_ab_semigroup_add :
  'a ab_semigroup_add -> 'a semigroup_add;

type 'a cancel_ab_semigroup_add =
  {ab_semigroup_add_cancel_ab_semigroup_add : 'a ab_semigroup_add,
    cancel_semigroup_add_cancel_ab_semigroup_add : 'a cancel_semigroup_add,
    minus_cancel_ab_semigroup_add : 'a minus};
val ab_semigroup_add_cancel_ab_semigroup_add =
  #ab_semigroup_add_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a ab_semigroup_add;
val cancel_semigroup_add_cancel_ab_semigroup_add =
  #cancel_semigroup_add_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a cancel_semigroup_add;
val minus_cancel_ab_semigroup_add = #minus_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a minus;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add,
    monoid_add_comm_monoid_add : 'a monoid_add};
val ab_semigroup_add_comm_monoid_add = #ab_semigroup_add_comm_monoid_add :
  'a comm_monoid_add -> 'a ab_semigroup_add;
val monoid_add_comm_monoid_add = #monoid_add_comm_monoid_add :
  'a comm_monoid_add -> 'a monoid_add;

type 'a cancel_comm_monoid_add =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add : 'a cancel_ab_semigroup_add,
    comm_monoid_add_cancel_comm_monoid_add : 'a comm_monoid_add};
val cancel_ab_semigroup_add_cancel_comm_monoid_add =
  #cancel_ab_semigroup_add_cancel_comm_monoid_add :
  'a cancel_comm_monoid_add -> 'a cancel_ab_semigroup_add;
val comm_monoid_add_cancel_comm_monoid_add =
  #comm_monoid_add_cancel_comm_monoid_add :
  'a cancel_comm_monoid_add -> 'a comm_monoid_add;

type 'a ab_group_add =
  {cancel_comm_monoid_add_ab_group_add : 'a cancel_comm_monoid_add,
    group_add_ab_group_add : 'a group_add};
val cancel_comm_monoid_add_ab_group_add = #cancel_comm_monoid_add_ab_group_add :
  'a ab_group_add -> 'a cancel_comm_monoid_add;
val group_add_ab_group_add = #group_add_ab_group_add :
  'a ab_group_add -> 'a group_add;

val ab_semigroup_add_int = {semigroup_add_ab_semigroup_add = semigroup_add_int}
  : inta ab_semigroup_add;

val cancel_ab_semigroup_add_int =
  {ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_int,
    cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_int,
    minus_cancel_ab_semigroup_add = minus_int}
  : inta cancel_ab_semigroup_add;

val comm_monoid_add_int =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_int,
    monoid_add_comm_monoid_add = monoid_add_int}
  : inta comm_monoid_add;

val cancel_comm_monoid_add_int =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add = cancel_ab_semigroup_add_int,
    comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_int}
  : inta cancel_comm_monoid_add;

val ab_group_add_int =
  {cancel_comm_monoid_add_ab_group_add = cancel_comm_monoid_add_int,
    group_add_ab_group_add = group_add_int}
  : inta ab_group_add;

type 'a ordered_ab_semigroup_add =
  {ab_semigroup_add_ordered_ab_semigroup_add : 'a ab_semigroup_add,
    order_ordered_ab_semigroup_add : 'a order};
val ab_semigroup_add_ordered_ab_semigroup_add =
  #ab_semigroup_add_ordered_ab_semigroup_add :
  'a ordered_ab_semigroup_add -> 'a ab_semigroup_add;
val order_ordered_ab_semigroup_add = #order_ordered_ab_semigroup_add :
  'a ordered_ab_semigroup_add -> 'a order;

type 'a strict_ordered_ab_semigroup_add =
  {ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add :
     'a ordered_ab_semigroup_add};
val ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add =
  #ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add :
  'a strict_ordered_ab_semigroup_add -> 'a ordered_ab_semigroup_add;

type 'a ordered_cancel_ab_semigroup_add =
  {cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
     'a cancel_ab_semigroup_add,
    strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
      'a strict_ordered_ab_semigroup_add};
val cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
  #cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
  'a ordered_cancel_ab_semigroup_add -> 'a cancel_ab_semigroup_add;
val strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
  #strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
  'a ordered_cancel_ab_semigroup_add -> 'a strict_ordered_ab_semigroup_add;

type 'a ordered_ab_semigroup_add_imp_le =
  {ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le :
     'a ordered_cancel_ab_semigroup_add};
val ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le =
  #ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le :
  'a ordered_ab_semigroup_add_imp_le -> 'a ordered_cancel_ab_semigroup_add;

type 'a strict_ordered_comm_monoid_add =
  {comm_monoid_add_strict_ordered_comm_monoid_add : 'a comm_monoid_add,
    strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add :
      'a strict_ordered_ab_semigroup_add};
val comm_monoid_add_strict_ordered_comm_monoid_add =
  #comm_monoid_add_strict_ordered_comm_monoid_add :
  'a strict_ordered_comm_monoid_add -> 'a comm_monoid_add;
val strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add =
  #strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add :
  'a strict_ordered_comm_monoid_add -> 'a strict_ordered_ab_semigroup_add;

type 'a ordered_comm_monoid_add =
  {comm_monoid_add_ordered_comm_monoid_add : 'a comm_monoid_add,
    ordered_ab_semigroup_add_ordered_comm_monoid_add :
      'a ordered_ab_semigroup_add};
val comm_monoid_add_ordered_comm_monoid_add =
  #comm_monoid_add_ordered_comm_monoid_add :
  'a ordered_comm_monoid_add -> 'a comm_monoid_add;
val ordered_ab_semigroup_add_ordered_comm_monoid_add =
  #ordered_ab_semigroup_add_ordered_comm_monoid_add :
  'a ordered_comm_monoid_add -> 'a ordered_ab_semigroup_add;

type 'a ordered_cancel_comm_monoid_add =
  {ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add :
     'a ordered_cancel_ab_semigroup_add,
    ordered_comm_monoid_add_ordered_cancel_comm_monoid_add :
      'a ordered_comm_monoid_add,
    strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add :
      'a strict_ordered_comm_monoid_add};
val ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add =
  #ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add :
  'a ordered_cancel_comm_monoid_add -> 'a ordered_cancel_ab_semigroup_add;
val ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
  #ordered_comm_monoid_add_ordered_cancel_comm_monoid_add :
  'a ordered_cancel_comm_monoid_add -> 'a ordered_comm_monoid_add;
val strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
  #strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add :
  'a ordered_cancel_comm_monoid_add -> 'a strict_ordered_comm_monoid_add;

type 'a ordered_ab_semigroup_monoid_add_imp_le =
  {cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le :
     'a cancel_comm_monoid_add,
    ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le :
      'a ordered_ab_semigroup_add_imp_le,
    ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le :
      'a ordered_cancel_comm_monoid_add};
val cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
  #cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le :
  'a ordered_ab_semigroup_monoid_add_imp_le -> 'a cancel_comm_monoid_add;
val ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le =
  #ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le :
  'a ordered_ab_semigroup_monoid_add_imp_le ->
    'a ordered_ab_semigroup_add_imp_le;
val ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
  #ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le :
  'a ordered_ab_semigroup_monoid_add_imp_le ->
    'a ordered_cancel_comm_monoid_add;

type 'a ordered_ab_group_add =
  {ab_group_add_ordered_ab_group_add : 'a ab_group_add,
    ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add :
      'a ordered_ab_semigroup_monoid_add_imp_le};
val ab_group_add_ordered_ab_group_add = #ab_group_add_ordered_ab_group_add :
  'a ordered_ab_group_add -> 'a ab_group_add;
val ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add =
  #ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add :
  'a ordered_ab_group_add -> 'a ordered_ab_semigroup_monoid_add_imp_le;

val ordered_ab_semigroup_add_int =
  {ab_semigroup_add_ordered_ab_semigroup_add = ab_semigroup_add_int,
    order_ordered_ab_semigroup_add = order_int}
  : inta ordered_ab_semigroup_add;

val strict_ordered_ab_semigroup_add_int =
  {ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add =
     ordered_ab_semigroup_add_int}
  : inta strict_ordered_ab_semigroup_add;

val ordered_cancel_ab_semigroup_add_int =
  {cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
     cancel_ab_semigroup_add_int,
    strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
      strict_ordered_ab_semigroup_add_int}
  : inta ordered_cancel_ab_semigroup_add;

val ordered_ab_semigroup_add_imp_le_int =
  {ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le =
     ordered_cancel_ab_semigroup_add_int}
  : inta ordered_ab_semigroup_add_imp_le;

val strict_ordered_comm_monoid_add_int =
  {comm_monoid_add_strict_ordered_comm_monoid_add = comm_monoid_add_int,
    strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add =
      strict_ordered_ab_semigroup_add_int}
  : inta strict_ordered_comm_monoid_add;

val ordered_comm_monoid_add_int =
  {comm_monoid_add_ordered_comm_monoid_add = comm_monoid_add_int,
    ordered_ab_semigroup_add_ordered_comm_monoid_add =
      ordered_ab_semigroup_add_int}
  : inta ordered_comm_monoid_add;

val ordered_cancel_comm_monoid_add_int =
  {ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add =
     ordered_cancel_ab_semigroup_add_int,
    ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
      ordered_comm_monoid_add_int,
    strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
      strict_ordered_comm_monoid_add_int}
  : inta ordered_cancel_comm_monoid_add;

val ordered_ab_semigroup_monoid_add_imp_le_int =
  {cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
     cancel_comm_monoid_add_int,
    ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le =
      ordered_ab_semigroup_add_imp_le_int,
    ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
      ordered_cancel_comm_monoid_add_int}
  : inta ordered_ab_semigroup_monoid_add_imp_le;

val ordered_ab_group_add_int =
  {ab_group_add_ordered_ab_group_add = ab_group_add_int,
    ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add =
      ordered_ab_semigroup_monoid_add_imp_le_int}
  : inta ordered_ab_group_add;

type 'a linordered_ab_semigroup_add =
  {ordered_ab_semigroup_add_linordered_ab_semigroup_add :
     'a ordered_ab_semigroup_add,
    linorder_linordered_ab_semigroup_add : 'a linorder};
val ordered_ab_semigroup_add_linordered_ab_semigroup_add =
  #ordered_ab_semigroup_add_linordered_ab_semigroup_add :
  'a linordered_ab_semigroup_add -> 'a ordered_ab_semigroup_add;
val linorder_linordered_ab_semigroup_add = #linorder_linordered_ab_semigroup_add
  : 'a linordered_ab_semigroup_add -> 'a linorder;

type 'a linordered_cancel_ab_semigroup_add =
  {linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add :
     'a linordered_ab_semigroup_add,
    ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add :
      'a ordered_ab_semigroup_add_imp_le};
val linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add =
  #linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add :
  'a linordered_cancel_ab_semigroup_add -> 'a linordered_ab_semigroup_add;
val ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add =
  #ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add :
  'a linordered_cancel_ab_semigroup_add -> 'a ordered_ab_semigroup_add_imp_le;

type 'a linordered_ab_monoid_add =
  {linordered_ab_semigroup_add_linordered_ab_monoid_add :
     'a linordered_ab_semigroup_add,
    ordered_comm_monoid_add_linordered_ab_monoid_add :
      'a ordered_comm_monoid_add};
val linordered_ab_semigroup_add_linordered_ab_monoid_add =
  #linordered_ab_semigroup_add_linordered_ab_monoid_add :
  'a linordered_ab_monoid_add -> 'a linordered_ab_semigroup_add;
val ordered_comm_monoid_add_linordered_ab_monoid_add =
  #ordered_comm_monoid_add_linordered_ab_monoid_add :
  'a linordered_ab_monoid_add -> 'a ordered_comm_monoid_add;

type 'a linordered_cancel_ab_monoid_add =
  {linordered_ab_monoid_add_linordered_cancel_ab_monoid_add :
     'a linordered_ab_monoid_add,
    linordered_cancel_ab_semigroup_add_linordered_cancel_ab_monoid_add :
      'a linordered_cancel_ab_semigroup_add};
val linordered_ab_monoid_add_linordered_cancel_ab_monoid_add =
  #linordered_ab_monoid_add_linordered_cancel_ab_monoid_add :
  'a linordered_cancel_ab_monoid_add -> 'a linordered_ab_monoid_add;
val linordered_cancel_ab_semigroup_add_linordered_cancel_ab_monoid_add =
  #linordered_cancel_ab_semigroup_add_linordered_cancel_ab_monoid_add :
  'a linordered_cancel_ab_monoid_add -> 'a linordered_cancel_ab_semigroup_add;

type 'a linordered_ab_group_add =
  {linordered_cancel_ab_monoid_add_linordered_ab_group_add :
     'a linordered_cancel_ab_monoid_add,
    ordered_ab_group_add_linordered_ab_group_add : 'a ordered_ab_group_add};
val linordered_cancel_ab_monoid_add_linordered_ab_group_add =
  #linordered_cancel_ab_monoid_add_linordered_ab_group_add :
  'a linordered_ab_group_add -> 'a linordered_cancel_ab_monoid_add;
val ordered_ab_group_add_linordered_ab_group_add =
  #ordered_ab_group_add_linordered_ab_group_add :
  'a linordered_ab_group_add -> 'a ordered_ab_group_add;

val linordered_ab_semigroup_add_int =
  {ordered_ab_semigroup_add_linordered_ab_semigroup_add =
     ordered_ab_semigroup_add_int,
    linorder_linordered_ab_semigroup_add = linorder_int}
  : inta linordered_ab_semigroup_add;

val linordered_cancel_ab_semigroup_add_int =
  {linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add =
     linordered_ab_semigroup_add_int,
    ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add =
      ordered_ab_semigroup_add_imp_le_int}
  : inta linordered_cancel_ab_semigroup_add;

val linordered_ab_monoid_add_int =
  {linordered_ab_semigroup_add_linordered_ab_monoid_add =
     linordered_ab_semigroup_add_int,
    ordered_comm_monoid_add_linordered_ab_monoid_add =
      ordered_comm_monoid_add_int}
  : inta linordered_ab_monoid_add;

val linordered_cancel_ab_monoid_add_int =
  {linordered_ab_monoid_add_linordered_cancel_ab_monoid_add =
     linordered_ab_monoid_add_int,
    linordered_cancel_ab_semigroup_add_linordered_cancel_ab_monoid_add =
      linordered_cancel_ab_semigroup_add_int}
  : inta linordered_cancel_ab_monoid_add;

val linordered_ab_group_add_int =
  {linordered_cancel_ab_monoid_add_linordered_ab_group_add =
     linordered_cancel_ab_monoid_add_int,
    ordered_ab_group_add_linordered_ab_group_add = ordered_ab_group_add_int}
  : inta linordered_ab_group_add;

val equal_nat = {equal = equal_nata} : nat equal;

fun typerep_nata t = Typerep ("Nat.nat", []);

val countable_nat = {} : nat countable;

val typerep_nat = {typerep = typerep_nata} : nat typerep;

val heap_nat = {countable_heap = countable_nat, typerep_heap = typerep_nat} :
  nat heap;

fun shows_prec_nat x = showsp_nat x;

fun shows_list_nat x = showsp_list shows_prec_nat zero_nata x;

val show_nat = {shows_prec = shows_prec_nat, shows_list = shows_list_nat} :
  nat show;

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_nat = {one = one_nata} : nat one;

fun plus_nata m n = Nat (integer_of_nat m + integer_of_nat n);

val plus_nat = {plus = plus_nata} : nat plus;

val zero_nat = {zero = zero_nata} : nat zero;

fun times_nata m n = Nat (integer_of_nat m * integer_of_nat n);

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

val times_nat = {times = times_nata} : nat times;

val power_nat = {one_power = one_nat, times_power = times_nat} : nat power;

fun less_eq_nat m n = integer_of_nat m <= integer_of_nat n;

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

val preorder_nat = {ord_preorder = ord_nat} : nat preorder;

val order_nat = {preorder_order = preorder_nat} : nat order;

val semigroup_add_nat = {plus_semigroup_add = plus_nat} : nat semigroup_add;

val monoid_add_nat =
  {semigroup_add_monoid_add = semigroup_add_nat, zero_monoid_add = zero_nat} :
  nat monoid_add;

fun def_hashmap_size_nat x = (fn _ => nat_of_integer (16 : IntInf.int)) x;

fun int_of_nat n = Int_of_integer (integer_of_nat n);

fun hashcode_nat n = uint32_of_int (int_of_nat n);

val hashable_nat =
  {hashcode = hashcode_nat, def_hashmap_size = def_hashmap_size_nat} :
  nat hashable;

val linorder_nat = {order_linorder = order_nat} : nat linorder;

datatype ('a, 'b) phantom = Phantom of 'b;

val finite_UNIV_nata : (nat, bool) phantom = Phantom false;

val card_UNIV_nata : (nat, nat) phantom = Phantom zero_nata;

type 'a finite_UNIV = {finite_UNIV : ('a, bool) phantom};
val finite_UNIV = #finite_UNIV : 'a finite_UNIV -> ('a, bool) phantom;

type 'a card_UNIV =
  {finite_UNIV_card_UNIV : 'a finite_UNIV, card_UNIV : ('a, nat) phantom};
val finite_UNIV_card_UNIV = #finite_UNIV_card_UNIV :
  'a card_UNIV -> 'a finite_UNIV;
val card_UNIV = #card_UNIV : 'a card_UNIV -> ('a, nat) phantom;

val finite_UNIV_nat = {finite_UNIV = finite_UNIV_nata} : nat finite_UNIV;

val card_UNIV_nat =
  {finite_UNIV_card_UNIV = finite_UNIV_nat, card_UNIV = card_UNIV_nata} :
  nat card_UNIV;

fun eq A_ a b = equal A_ a b;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

fun typerep_lista A_ t = Typerep ("List.list", [typerep A_ Type]);

fun countable_list A_ = {} : ('a list) countable;

fun typerep_list A_ = {typerep = typerep_lista A_} : ('a list) typerep;

fun heap_list A_ =
  {countable_heap = countable_list (countable_heap A_),
    typerep_heap = typerep_list (typerep_heap A_)}
  : ('a list) heap;

fun shows_prec_list A_ p xs = shows_list A_ xs;

fun shows_list_list A_ xss = showsp_list (shows_prec_list A_) zero_nata xss;

fun show_list A_ =
  {shows_prec = shows_prec_list A_, shows_list = shows_list_list A_} :
  ('a list) show;

fun def_hashmap_size_list A_ =
  (fn _ =>
    times_nata (nat_of_integer (2 : IntInf.int)) (def_hashmap_size A_ Type));

fun foldl f a [] = a
  | foldl f a (x :: xs) = foldl f (f a x) xs;

fun hashcode_list A_ =
  foldl (fn h => fn x =>
          Word32.+ (Word32.* (h, Word32.fromLargeInt (IntInf.toLarge (33 : IntInf.int))), hashcode
            A_ x))
    (Word32.fromLargeInt (IntInf.toLarge (5381 : IntInf.int)));

fun hashable_list A_ =
  {hashcode = hashcode_list A_, def_hashmap_size = def_hashmap_size_list A_} :
  ('a list) hashable;

fun typerep_arraya A_ t = Typerep ("Heap.array", [typerep A_ Type]);

val countable_array = {} : ('a array) countable;

fun typerep_array A_ = {typerep = typerep_arraya A_} : ('a array) typerep;

fun heap_array A_ =
  {countable_heap = countable_array, typerep_heap = typerep_array A_} :
  ('a array) heap;

fun equal_bool p true = p
  | equal_bool p false = not p
  | equal_bool true p = p
  | equal_bool false p = not p;

fun equal_chara (Chara (x1, x2, x3, x4, x5, x6, x7, x8))
  (Chara (y1, y2, y3, y4, y5, y6, y7, y8)) =
  equal_bool x1 y1 andalso
    (equal_bool x2 y2 andalso
      (equal_bool x3 y3 andalso
        (equal_bool x4 y4 andalso
          (equal_bool x5 y5 andalso
            (equal_bool x6 y6 andalso
              (equal_bool x7 y7 andalso equal_bool x8 y8))))));

val equal_char = {equal = equal_chara} : char equal;

fun shows_prec_char p c = (fn a => c :: a);

fun shows_list_char cs = shows_string cs;

val show_char = {shows_prec = shows_prec_char, shows_list = shows_list_char} :
  char show;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

fun of_bool A_ true = one (one_zero_neq_one A_)
  | of_bool A_ false = zero (zero_zero_neq_one A_);

val one_integera : int = (1 : IntInf.int);

val zero_integer = {zero = (0 : IntInf.int)} : int zero;

val one_integer = {one = one_integera} : int one;

val zero_neq_one_integer =
  {one_zero_neq_one = one_integer, zero_zero_neq_one = zero_integer} :
  int zero_neq_one;

fun integer_of_char (Chara (b0, b1, b2, b3, b4, b5, b6, b7)) =
  ((((((of_bool zero_neq_one_integer b7 * (2 : IntInf.int) +
         of_bool zero_neq_one_integer b6) *
         (2 : IntInf.int) +
        of_bool zero_neq_one_integer b5) *
        (2 : IntInf.int) +
       of_bool zero_neq_one_integer b4) *
       (2 : IntInf.int) +
      of_bool zero_neq_one_integer b3) *
      (2 : IntInf.int) +
     of_bool zero_neq_one_integer b2) *
     (2 : IntInf.int) +
    of_bool zero_neq_one_integer b1) *
    (2 : IntInf.int) +
    of_bool zero_neq_one_integer b0;

fun nat_of_char c = Nat (integer_of_char c);

fun less_eq_char c1 c2 = less_eq_nat (nat_of_char c1) (nat_of_char c2);

fun less_char c1 c2 = less_nat (nat_of_char c1) (nat_of_char c2);

val ord_char = {less_eq = less_eq_char, less = less_char} : char ord;

val preorder_char = {ord_preorder = ord_char} : char preorder;

val order_char = {preorder_order = preorder_char} : char order;

val linorder_char = {order_linorder = order_char} : char linorder;

datatype 'a dBMEntry = Le of 'a | Lt of 'a | INF;

fun typerep_DBMEntrya A_ t = Typerep ("DBM.DBMEntry", [typerep A_ Type]);

fun countable_DBMEntry A_ = {} : 'a dBMEntry countable;

fun typerep_DBMEntry A_ = {typerep = typerep_DBMEntrya A_} :
  'a dBMEntry typerep;

fun heap_DBMEntry A_ =
  {countable_heap = countable_DBMEntry (countable_heap A_),
    typerep_heap = typerep_DBMEntry (typerep_heap A_)}
  : 'a dBMEntry heap;

fun dbm_add A_ INF uu = INF
  | dbm_add A_ (Le v) INF = INF
  | dbm_add A_ (Lt v) INF = INF
  | dbm_add A_ (Le a) (Le b) =
    Le (plus ((plus_semigroup_add o semigroup_add_ab_semigroup_add o
                ab_semigroup_add_cancel_ab_semigroup_add o
                cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add o
                ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le o
                ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add)
               A_)
         a b)
  | dbm_add A_ (Le a) (Lt b) =
    Lt (plus ((plus_semigroup_add o semigroup_add_ab_semigroup_add o
                ab_semigroup_add_cancel_ab_semigroup_add o
                cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add o
                ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le o
                ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add)
               A_)
         a b)
  | dbm_add A_ (Lt a) (Le b) =
    Lt (plus ((plus_semigroup_add o semigroup_add_ab_semigroup_add o
                ab_semigroup_add_cancel_ab_semigroup_add o
                cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add o
                ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le o
                ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add)
               A_)
         a b)
  | dbm_add A_ (Lt a) (Lt b) =
    Lt (plus ((plus_semigroup_add o semigroup_add_ab_semigroup_add o
                ab_semigroup_add_cancel_ab_semigroup_add o
                cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add o
                ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le o
                ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add)
               A_)
         a b);

fun plus_DBMEntrya A_ =
  dbm_add
    (linordered_cancel_ab_semigroup_add_linordered_cancel_ab_monoid_add A_);

fun plus_DBMEntry A_ = {plus = plus_DBMEntrya A_} : 'a dBMEntry plus;

fun zero_DBMEntrya A_ = Le (zero A_);

fun zero_DBMEntry A_ = {zero = zero_DBMEntrya A_} : 'a dBMEntry zero;

fun equal_DBMEntry A_ (Lt x2) INF = false
  | equal_DBMEntry A_ INF (Lt x2) = false
  | equal_DBMEntry A_ (Le x1) INF = false
  | equal_DBMEntry A_ INF (Le x1) = false
  | equal_DBMEntry A_ (Le x1) (Lt x2) = false
  | equal_DBMEntry A_ (Lt x2) (Le x1) = false
  | equal_DBMEntry A_ (Lt x2) (Lt y2) = eq A_ x2 y2
  | equal_DBMEntry A_ (Le x1) (Le y1) = eq A_ x1 y1
  | equal_DBMEntry A_ INF INF = true;

fun dbm_lt A_ INF x = false
  | dbm_lt A_ (Lt a) (Lt b) =
    less ((ord_preorder o preorder_order o order_linorder) A_) a b
  | dbm_lt A_ (Lt a) (Le b) =
    less_eq ((ord_preorder o preorder_order o order_linorder) A_) a b
  | dbm_lt A_ (Le a) (Lt b) =
    less ((ord_preorder o preorder_order o order_linorder) A_) a b
  | dbm_lt A_ (Le a) (Le b) =
    less ((ord_preorder o preorder_order o order_linorder) A_) a b
  | dbm_lt A_ (Le a) INF = true
  | dbm_lt A_ (Lt a) INF = true;

fun dbm_le (A1_, A2_) a b = equal_DBMEntry A1_ a b orelse dbm_lt A2_ a b;

fun less_eq_DBMEntry (A1_, A2_) = dbm_le (A1_, A2_);

fun less_DBMEntry A_ = dbm_lt A_;

fun ord_DBMEntry (A1_, A2_) =
  {less_eq = less_eq_DBMEntry (A1_, A2_), less = less_DBMEntry A2_} :
  'a dBMEntry ord;

fun preorder_DBMEntry (A1_, A2_) = {ord_preorder = ord_DBMEntry (A1_, A2_)} :
  'a dBMEntry preorder;

fun order_DBMEntry (A1_, A2_) = {preorder_order = preorder_DBMEntry (A1_, A2_)}
  : 'a dBMEntry order;

fun semigroup_add_DBMEntry A_ = {plus_semigroup_add = plus_DBMEntry A_} :
  'a dBMEntry semigroup_add;

fun monoid_add_DBMEntry A_ =
  {semigroup_add_monoid_add = semigroup_add_DBMEntry A_,
    zero_monoid_add =
      zero_DBMEntry
        ((zero_monoid_add o monoid_add_comm_monoid_add o
           comm_monoid_add_ordered_comm_monoid_add o
           ordered_comm_monoid_add_linordered_ab_monoid_add o
           linordered_ab_monoid_add_linordered_cancel_ab_monoid_add)
          A_)}
  : 'a dBMEntry monoid_add;

fun linorder_DBMEntry (A1_, A2_) = {order_linorder = order_DBMEntry (A1_, A2_)}
  : 'a dBMEntry linorder;

fun ab_semigroup_add_DBMEntry A_ =
  {semigroup_add_ab_semigroup_add = semigroup_add_DBMEntry A_} :
  'a dBMEntry ab_semigroup_add;

fun comm_monoid_add_DBMEntry A_ =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_DBMEntry A_,
    monoid_add_comm_monoid_add = monoid_add_DBMEntry A_}
  : 'a dBMEntry comm_monoid_add;

fun ordered_ab_semigroup_add_DBMEntry (A1_, A2_) =
  {ab_semigroup_add_ordered_ab_semigroup_add = ab_semigroup_add_DBMEntry A1_,
    order_ordered_ab_semigroup_add =
      order_DBMEntry
        (A2_, (linorder_linordered_ab_semigroup_add o
                linordered_ab_semigroup_add_linordered_ab_monoid_add o
                linordered_ab_monoid_add_linordered_cancel_ab_monoid_add)
                A1_)}
  : 'a dBMEntry ordered_ab_semigroup_add;

fun ordered_comm_monoid_add_DBMEntry (A1_, A2_) =
  {comm_monoid_add_ordered_comm_monoid_add = comm_monoid_add_DBMEntry A1_,
    ordered_ab_semigroup_add_ordered_comm_monoid_add =
      ordered_ab_semigroup_add_DBMEntry (A1_, A2_)}
  : 'a dBMEntry ordered_comm_monoid_add;

fun linordered_ab_semigroup_add_DBMEntry (A1_, A2_) =
  {ordered_ab_semigroup_add_linordered_ab_semigroup_add =
     ordered_ab_semigroup_add_DBMEntry (A1_, A2_),
    linorder_linordered_ab_semigroup_add =
      linorder_DBMEntry
        (A2_, (linorder_linordered_ab_semigroup_add o
                linordered_ab_semigroup_add_linordered_ab_monoid_add o
                linordered_ab_monoid_add_linordered_cancel_ab_monoid_add)
                A1_)}
  : 'a dBMEntry linordered_ab_semigroup_add;

fun linordered_ab_monoid_add_DBMEntry (A1_, A2_) =
  {linordered_ab_semigroup_add_linordered_ab_monoid_add =
     linordered_ab_semigroup_add_DBMEntry (A1_, A2_),
    ordered_comm_monoid_add_linordered_ab_monoid_add =
      ordered_comm_monoid_add_DBMEntry (A1_, A2_)}
  : 'a dBMEntry linordered_ab_monoid_add;

fun shows_space x =
  shows_prec_char zero_nata
    (Chara (false, false, false, false, false, true, false, false)) x;

datatype 'a act = In of 'a | Out of 'a | Sil of 'a;

fun id x = (fn xa => xa) x;

fun shows_pr p =
  (if less_nat zero_nata p
    then shows_prec_char zero_nata
           (Chara (true, false, false, true, false, true, false, false))
    else id);

fun shows_pl p =
  (if less_nat zero_nata p
    then shows_prec_char zero_nata
           (Chara (false, false, false, true, false, true, false, false))
    else id);

fun showsp_act show_a p (Sil x) =
  shows_pl p o
    shows_string
      [Chara (true, true, false, false, true, false, true, false),
        Chara (true, false, false, true, false, true, true, false),
        Chara (false, false, true, true, false, true, true, false)] o
    shows_space o
    show_a one_nata x o
    shows_pr p
  | showsp_act show_a p (Out x) =
    shows_pl p o
      shows_string
        [Chara (true, true, true, true, false, false, true, false),
          Chara (true, false, true, false, true, true, true, false),
          Chara (false, false, true, false, true, true, true, false)] o
      shows_space o
      show_a one_nata x o
      shows_pr p
  | showsp_act show_a p (In x) =
    shows_pl p o
      shows_string
        [Chara (true, false, false, true, false, false, true, false),
          Chara (false, true, true, true, false, true, true, false)] o
      shows_space o
      show_a one_nata x o
      shows_pr p;

fun shows_prec_act A_ = showsp_act (shows_prec A_);

fun shows_list_act A_ = showsp_list (shows_prec_act A_) zero_nata;

fun show_act A_ =
  {shows_prec = shows_prec_act A_, shows_list = shows_list_act A_} :
  'a act show;

val equal_literal = {equal = (fn a => fn b => ((a : string) = b))} :
  string equal;

fun bit_cut_integer k =
  (if k = (0 : IntInf.int) then ((0 : IntInf.int), false)
    else let
           val (r, s) = Integer.div_mod (abs k) (abs (2 : IntInf.int));
         in
           ((if (0 : IntInf.int) < k then r else ~ r - s), s = (1 : IntInf.int))
         end);

fun char_of_integer k = let
                          val (q0, b0) = bit_cut_integer k;
                          val (q1, b1) = bit_cut_integer q0;
                          val (q2, b2) = bit_cut_integer q1;
                          val (q3, b3) = bit_cut_integer q2;
                          val (q4, b4) = bit_cut_integer q3;
                          val (q5, b5) = bit_cut_integer q4;
                          val (q6, b6) = bit_cut_integer q5;
                          val a = bit_cut_integer q6;
                          val (_, aa) = a;
                        in
                          Chara (b0, b1, b2, b3, b4, b5, b6, aa)
                        end;

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun explode s =
  map char_of_integer
    ((map (fn c => let val k = Char.ord c in if k < 128 then IntInf.fromInt k else raise Fail "Non-ASCII character in literal" end) 
       o String.explode)
      s);

fun shows_prec_literal p s rest = explode s @ rest;

fun intersperse sep (x :: y :: xs) = x :: sep :: intersperse sep (y :: xs)
  | intersperse uu [] = []
  | intersperse uu [v] = [v];

fun foldr f [] = id
  | foldr f (x :: xs) = f x o foldr f xs;

fun concat xss = foldr (fn a => fn b => a @ b) xss [];

fun shows_list_literal cs s =
  [Chara (true, true, false, true, true, false, true, false)] @
    concat
      (intersperse
        [Chara (false, false, true, true, false, true, false, false),
          Chara (false, false, false, false, false, true, false, false)]
        (map explode cs)) @
      [Chara (true, false, true, true, true, false, true, false)] @ s;

val show_literal =
  {shows_prec = shows_prec_literal, shows_list = shows_list_literal} :
  string show;

val countable_literal = {} : string countable;

val finite_UNIV_literala : (string, bool) phantom = Phantom false;

val card_UNIV_literala : (string, nat) phantom = Phantom zero_nata;

val finite_UNIV_literal = {finite_UNIV = finite_UNIV_literala} :
  string finite_UNIV;

val card_UNIV_literal =
  {finite_UNIV_card_UNIV = finite_UNIV_literal, card_UNIV = card_UNIV_literala}
  : string card_UNIV;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

fun typerep_proda A_ B_ t =
  Typerep ("Product_Type.prod", [typerep A_ Type, typerep B_ Type]);

fun countable_prod A_ B_ = {} : ('a * 'b) countable;

fun typerep_prod A_ B_ = {typerep = typerep_proda A_ B_} : ('a * 'b) typerep;

fun heap_prod A_ B_ =
  {countable_heap = countable_prod (countable_heap A_) (countable_heap B_),
    typerep_heap = typerep_prod (typerep_heap A_) (typerep_heap B_)}
  : ('a * 'b) heap;

fun showsp_prod s1 s2 p (x, y) =
  shows_string [Chara (false, false, false, true, false, true, false, false)] o
    s1 one_nata x o
    shows_string
      [Chara (false, false, true, true, false, true, false, false),
        Chara (false, false, false, false, false, true, false, false)] o
    s2 one_nata y o
    shows_string [Chara (true, false, false, true, false, true, false, false)];

fun shows_prec_prod A_ B_ = showsp_prod (shows_prec A_) (shows_prec B_);

fun shows_list_prod A_ B_ = showsp_list (shows_prec_prod A_ B_) zero_nata;

fun show_prod A_ B_ =
  {shows_prec = shows_prec_prod A_ B_, shows_list = shows_list_prod A_ B_} :
  ('a * 'b) show;

fun def_hashmap_size_prod A_ B_ =
  (fn _ => plus_nata (def_hashmap_size A_ Type) (def_hashmap_size B_ Type));

fun hashcode_prod A_ B_ x =
  Word32.+ (Word32.* (hashcode A_
                        (fst x), Word32.fromLargeInt (IntInf.toLarge (33 : IntInf.int))), hashcode
            B_ (snd x));

fun hashable_prod A_ B_ =
  {hashcode = hashcode_prod A_ B_,
    def_hashmap_size = def_hashmap_size_prod A_ B_}
  : ('a * 'b) hashable;

datatype ('a, 'b) bexp = True | Not of ('a, 'b) bexp |
  And of ('a, 'b) bexp * ('a, 'b) bexp | Or of ('a, 'b) bexp * ('a, 'b) bexp |
  Imply of ('a, 'b) bexp * ('a, 'b) bexp | Eq of ('a, 'b) exp * ('a, 'b) exp |
  Lea of ('a, 'b) exp * ('a, 'b) exp | Lta of ('a, 'b) exp * ('a, 'b) exp |
  Ge of ('a, 'b) exp * ('a, 'b) exp | Gt of ('a, 'b) exp * ('a, 'b) exp
and ('a, 'b) exp = Const of 'b | Var of 'a |
  If_then_else of ('a, 'b) bexp * ('a, 'b) exp * ('a, 'b) exp |
  Binop of ('b -> 'b -> 'b) * ('a, 'b) exp * ('a, 'b) exp |
  Unop of ('b -> 'b) * ('a, 'b) exp;

fun shows_exp A_ B_ (Const c) = shows_prec B_ zero_nata c []
  | shows_exp A_ B_ (Var v) = shows_prec A_ zero_nata v []
  | shows_exp A_ B_ (If_then_else (b, e1, e2)) =
    shows_bexp A_ B_ b @
      [Chara (false, false, false, false, false, true, false, false),
        Chara (true, true, true, true, true, true, false, false),
        Chara (false, false, false, false, false, true, false, false)] @
        shows_exp A_ B_ e1 @
          [Chara (false, false, false, false, false, true, false, false),
            Chara (false, true, false, true, true, true, false, false),
            Chara (false, false, false, false, false, true, false, false)] @
            shows_exp A_ B_ e2
  | shows_exp A_ B_ (Binop (uu, e1, e2)) =
    [Chara (false, true, false, false, false, true, true, false),
      Chara (true, false, false, true, false, true, true, false),
      Chara (false, true, true, true, false, true, true, false),
      Chara (true, true, true, true, false, true, true, false),
      Chara (false, false, false, false, true, true, true, false),
      Chara (false, false, false, false, false, true, false, false)] @
      shows_exp A_ B_ e1 @
        [Chara (false, false, false, false, false, true, false, false)] @
          shows_exp A_ B_ e2
  | shows_exp A_ B_ (Unop (uv, e)) =
    [Chara (true, false, true, false, true, true, true, false),
      Chara (false, true, true, true, false, true, true, false),
      Chara (true, true, true, true, false, true, true, false),
      Chara (false, false, false, false, true, true, true, false),
      Chara (false, false, false, false, false, true, false, false)] @
      shows_exp A_ B_ e
and shows_bexp A_ B_ (Lta (a, b)) =
  shows_exp A_ B_ a @
    [Chara (false, false, false, false, false, true, false, false),
      Chara (false, false, true, true, true, true, false, false),
      Chara (false, false, false, false, false, true, false, false)] @
      shows_exp A_ B_ b
  | shows_bexp A_ B_ (Lea (a, b)) =
    shows_exp A_ B_ a @
      [Chara (false, false, false, false, false, true, false, false),
        Chara (false, false, true, true, true, true, false, false),
        Chara (true, false, true, true, true, true, false, false),
        Chara (false, false, false, false, false, true, false, false)] @
        shows_exp A_ B_ b
  | shows_bexp A_ B_ (Eq (a, b)) =
    shows_exp A_ B_ a @
      [Chara (false, false, false, false, false, true, false, false),
        Chara (true, false, true, true, true, true, false, false),
        Chara (false, false, false, false, false, true, false, false)] @
        shows_exp A_ B_ b
  | shows_bexp A_ B_ (Ge (a, b)) =
    shows_exp A_ B_ a @
      [Chara (false, false, false, false, false, true, false, false),
        Chara (false, true, true, true, true, true, false, false),
        Chara (true, false, true, true, true, true, false, false),
        Chara (false, false, false, false, false, true, false, false)] @
        shows_exp A_ B_ b
  | shows_bexp A_ B_ (Gt (a, b)) =
    shows_exp A_ B_ a @
      [Chara (false, false, false, false, false, true, false, false),
        Chara (false, true, true, true, true, true, false, false),
        Chara (false, false, false, false, false, true, false, false)] @
        shows_exp A_ B_ b
  | shows_bexp A_ B_ True =
    [Chara (false, false, true, false, true, true, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (true, false, true, false, true, true, true, false),
      Chara (true, false, true, false, false, true, true, false)]
  | shows_bexp A_ B_ (Not b) =
    [Chara (true, false, false, false, false, true, false, false),
      Chara (false, false, false, false, false, true, false, false)] @
      shows_bexp A_ B_ b
  | shows_bexp A_ B_ (And (a, b)) =
    shows_bexp A_ B_ a @
      [Chara (false, false, false, false, false, true, false, false),
        Chara (false, true, true, false, false, true, false, false),
        Chara (false, true, true, false, false, true, false, false),
        Chara (false, false, false, false, false, true, false, false)] @
        shows_bexp A_ B_ b
  | shows_bexp A_ B_ (Or (a, b)) =
    shows_bexp A_ B_ a @
      [Chara (false, false, false, false, false, true, false, false),
        Chara (false, false, true, true, true, true, true, false),
        Chara (false, false, true, true, true, true, true, false),
        Chara (false, false, false, false, false, true, false, false)] @
        shows_bexp A_ B_ b
  | shows_bexp A_ B_ (Imply (a, b)) =
    shows_bexp A_ B_ a @
      [Chara (false, false, false, false, false, true, false, false),
        Chara (true, false, true, true, false, true, false, false),
        Chara (false, true, true, true, true, true, false, false),
        Chara (false, false, false, false, false, true, false, false)] @
        shows_bexp A_ B_ b;

fun shows_prec_exp A_ B_ p e rest = shows_exp A_ B_ e @ rest;

fun shows_list_exp A_ B_ es s =
  [Chara (true, true, false, true, true, false, true, false)] @
    concat
      (intersperse
        [Chara (false, false, true, true, false, true, false, false),
          Chara (false, false, false, false, false, true, false, false)]
        (map (shows_exp A_ B_) es)) @
      [Chara (true, false, true, true, true, false, true, false)] @ s;

fun show_exp A_ B_ =
  {shows_prec = shows_prec_exp A_ B_, shows_list = shows_list_exp A_ B_} :
  ('a, 'b) exp show;

datatype ('a, 'b) acconstraint = LT of 'a * 'b | LE of 'a * 'b | EQ of 'a * 'b |
  GT of 'a * 'b | GE of 'a * 'b;

fun showsp_acconstraint show_c show_t p (GE (x, y)) =
  shows_pl p o
    shows_string
      [Chara (true, true, true, false, false, false, true, false),
        Chara (true, false, true, false, false, false, true, false)] o
    shows_space o
    show_c one_nata x o
    shows_space o
    show_t one_nata y o
    shows_pr p
  | showsp_acconstraint show_c show_t p (GT (x, y)) =
    shows_pl p o
      shows_string
        [Chara (true, true, true, false, false, false, true, false),
          Chara (false, false, true, false, true, false, true, false)] o
      shows_space o
      show_c one_nata x o
      shows_space o
      show_t one_nata y o
      shows_pr p
  | showsp_acconstraint show_c show_t p (EQ (x, y)) =
    shows_pl p o
      shows_string
        [Chara (true, false, true, false, false, false, true, false),
          Chara (true, false, false, false, true, false, true, false)] o
      shows_space o
      show_c one_nata x o
      shows_space o
      show_t one_nata y o
      shows_pr p
  | showsp_acconstraint show_c show_t p (LE (x, y)) =
    shows_pl p o
      shows_string
        [Chara (false, false, true, true, false, false, true, false),
          Chara (true, false, true, false, false, false, true, false)] o
      shows_space o
      show_c one_nata x o
      shows_space o
      show_t one_nata y o
      shows_pr p
  | showsp_acconstraint show_c show_t p (LT (x, y)) =
    shows_pl p o
      shows_string
        [Chara (false, false, true, true, false, false, true, false),
          Chara (false, false, true, false, true, false, true, false)] o
      shows_space o
      show_c one_nata x o
      shows_space o
      show_t one_nata y o
      shows_pr p;

fun shows_prec_acconstraint A_ B_ =
  showsp_acconstraint (shows_prec A_) (shows_prec B_);

fun shows_list_acconstraint A_ B_ =
  showsp_list (shows_prec_acconstraint A_ B_) zero_nata;

fun show_acconstraint A_ B_ =
  {shows_prec = shows_prec_acconstraint A_ B_,
    shows_list = shows_list_acconstraint A_ B_}
  : ('a, 'b) acconstraint show;

fun shows_prec_bexp A_ B_ p e rest = shows_bexp A_ B_ e @ rest;

fun shows_list_bexp A_ B_ es s =
  [Chara (true, true, false, true, true, false, true, false)] @
    concat
      (intersperse
        [Chara (false, false, true, true, false, true, false, false),
          Chara (false, false, false, false, false, true, false, false)]
        (map (shows_bexp A_ B_) es)) @
      [Chara (true, false, true, true, true, false, true, false)] @ s;

fun show_bexp A_ B_ =
  {shows_prec = shows_prec_bexp A_ B_, shows_list = shows_list_bexp A_ B_} :
  ('a, 'b) bexp show;

datatype rat = Frct of (inta * inta);

datatype 'a set = Set of 'a list | Coset of 'a list;

datatype ('a, 'b) sum = Inl of 'a | Inr of 'b;

datatype message = ExploredState;

datatype json = Object of (char list * json) list | Arraya of json list |
  String of char list | Int of inta | Nata of nat | Rat of rat | Boolean of bool
  | Null;

datatype time = Time of inta;

datatype ('a, 'b) hashtable = HashTable of (('a * 'b) list) array * nat;

datatype 'a result = Result of 'a | Error of string list;

datatype 'a len_list = LL of nat * 'a list;

datatype ('a, 'b) hashmap =
  HashMap of (('a * 'b) list) FArray.IsabelleMapping.ArrayType * nat;

datatype 'a label = Del | Internal of 'a | Bin of 'a | Broad of 'a;

datatype ('a, 'b, 'c, 'd) gen_g_impl_ext = Gen_g_impl_ext of 'a * 'b * 'c * 'd;

datatype resulta = Renaming_Failed | Preconds_Unsat | Sat | Unsat;

datatype ('a, 'b, 'c, 'd) sexp = Truea | Nota of ('a, 'b, 'c, 'd) sexp |
  Anda of ('a, 'b, 'c, 'd) sexp * ('a, 'b, 'c, 'd) sexp |
  Ora of ('a, 'b, 'c, 'd) sexp * ('a, 'b, 'c, 'd) sexp |
  Implya of ('a, 'b, 'c, 'd) sexp * ('a, 'b, 'c, 'd) sexp | Eqa of 'c * 'd |
  Leb of 'c * 'd | Ltb of 'c * 'd | Gea of 'c * 'd | Gta of 'c * 'd |
  Loc of 'a * 'b;

datatype mode = Impl1 | Impl2 | Impl3;

datatype ('a, 'b, 'c, 'd) formula = EX of ('a, 'b, 'c, 'd) sexp |
  EG of ('a, 'b, 'c, 'd) sexp | AX of ('a, 'b, 'c, 'd) sexp |
  AG of ('a, 'b, 'c, 'd) sexp |
  Leadsto of ('a, 'b, 'c, 'd) sexp * ('a, 'b, 'c, 'd) sexp;

fun suc n = plus_nata n one_nata;

fun list_ex p [] = false
  | list_ex p (x :: xs) = p x orelse list_ex p xs;

fun bex (Set xs) p = list_ex p xs;

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int) (integer_of_nat m - integer_of_nat n));

fun nth (x :: xs) n =
  (if equal_nata n zero_nata then x else nth xs (minus_nat n one_nata));

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun rev xs = fold (fn a => fn b => a :: b) xs [];

fun upt i j = (if less_nat i j then i :: upt (suc i) j else []);

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

fun ball (Set xs) p = list_all p xs;

fun len A_ a =
  (fn f_ => fn () => f_ (((fn () => IntInf.fromInt (Array.length a))) ()) ())
    (fn i => (fn () => (nat_of_integer i)));

fun new A_ =
  (fn a => fn b => (fn () => Array.array (IntInf.toInt a, b))) o integer_of_nat;

fun ntha A_ a n = (fn () => Array.sub (a, IntInf.toInt (integer_of_nat n)));

fun upd A_ i x a =
  (fn f_ => fn () => f_
    (((fn () => Array.update (a, IntInf.toInt (integer_of_nat i), x))) ()) ())
    (fn _ => (fn () => a));

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun take n [] = []
  | take n (x :: xs) =
    (if equal_nata n zero_nata then []
      else x :: take (minus_nat n one_nata) xs);

fun divide_int k l =
  Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));

val one_int : inta = Int_of_integer (1 : IntInf.int);

fun gcd_integer k l =
  abs (if l = (0 : IntInf.int) then k
        else gcd_integer l (modulo_integer (abs k) (abs l)));

fun gcd_int (Int_of_integer x) (Int_of_integer y) =
  Int_of_integer (gcd_integer x y);

fun normalize p =
  (if less_int zero_inta (snd p)
    then let
           val a = gcd_int (fst p) (snd p);
         in
           (divide_int (fst p) a, divide_int (snd p) a)
         end
    else (if equal_inta (snd p) zero_inta then (zero_inta, one_int)
           else let
                  val a = uminus_inta (gcd_int (fst p) (snd p));
                in
                  (divide_int (fst p) a, divide_int (snd p) a)
                end));

fun fract a b = Frct (normalize (a, b));

fun image f (Set xs) = Set (map f xs);

fun make A_ n f =
  (fn () => Array.tabulate (IntInf.toInt (integer_of_nat n),
    (f o nat_of_integer) o IntInf.fromInt));

fun inj_on A_ B_ f a =
  ball a
    (fn x => ball a (fn y => (if eq B_ (f x) (f y) then eq A_ x y else true)));

fun sub asa n =
  (Vector.sub o (fn (a, b) => (a, IntInf.toInt b))) (asa, integer_of_nat n);

fun map_of A_ ((l, v) :: ps) k = (if eq A_ l k then SOME v else map_of A_ ps k)
  | map_of A_ [] k = NONE;

fun of_int a = Frct (a, one_int);

fun removeAll A_ x [] = []
  | removeAll A_ x (y :: xs) =
    (if eq A_ x y then removeAll A_ x xs else y :: removeAll A_ x xs);

fun membera A_ [] y = false
  | membera A_ (x :: xs) y = eq A_ x y orelse membera A_ xs y;

fun inserta A_ x xs = (if membera A_ xs x then xs else x :: xs);

fun insert A_ x (Coset xs) = Coset (removeAll A_ x xs)
  | insert A_ x (Set xs) = Set (inserta A_ x xs);

fun member A_ x (Coset xs) = not (membera A_ xs x)
  | member A_ x (Set xs) = membera A_ xs x;

fun remove A_ x (Coset xs) = Coset (inserta A_ x xs)
  | remove A_ x (Set xs) = Set (removeAll A_ x xs);

fun fun_upd A_ f a b = (fn x => (if eq A_ x a then b else f x));

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun foldli [] c f sigma = sigma
  | foldli (x :: xs) c f sigma =
    (if c sigma then foldli xs c f (f x sigma) else sigma);

fun hd (x21 :: x22) = x21;

fun tl [] = []
  | tl (x21 :: x22) = x22;

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if membera A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun uncurry f = (fn (a, b) => f a b);

fun distinct A_ [] = true
  | distinct A_ (x :: xs) = not (membera A_ xs x) andalso distinct A_ xs;

fun trace m x = let
                  val _ = (fn x => Tracing.count_up ()) m;
                in
                  x
                end;

fun replicate n x =
  (if equal_nata n zero_nata then []
    else x :: replicate (minus_nat n one_nata) x);

fun is_none (SOME x) = false
  | is_none NONE = true;

fun implode cs =
  (String.implode
    o map (fn k => if 0 <= k andalso k < 128 then (Char.chr o IntInf.toInt) k else raise Fail "Non-ASCII character in literal"))
    (map integer_of_char cs);

fun tracea x = trace ExploredState x;

fun v_dbm (A1_, A2_, A3_) B_ n =
  (fn (i, j) =>
    (if eq A2_ i j orelse
          (eq A2_ i (zero A1_) andalso less A3_ (zero A1_) j orelse
            (less A3_ n i orelse less A3_ n j))
      then zero_DBMEntrya B_ else INF));

fun gen_length n (x :: xs) = gen_length (suc n) xs
  | gen_length n [] = n;

fun map_filter f [] = []
  | map_filter f (x :: xs) =
    (case f x of NONE => map_filter f xs | SOME y => y :: map_filter f xs);

fun cODE_ABORT _ = raise Fail "Misc.CODE_ABORT";

fun quotient_of (Frct x) = x;

fun bind m f = (case m of Inl a => Inl a | Inr a => f a);

fun the (SOME x2) = x2;

fun gen_pick it s =
  the (it s (fn a => (case a of NONE => true | SOME _ => false))
         (fn x => fn _ => SOME x)
        NONE);

fun ll_fuel (LL (x1, x2)) = x1;

fun ensure_cparser p =
  (fn ts =>
    bind (p ts)
      (fn (x, tsa) =>
        (if less_nat (ll_fuel tsa) (ll_fuel ts) then Inr (x, tsa)
          else Inl (fn _ =>
                     shows_prec_list show_char zero_nata
                       [Chara (false, false, true, false, false, false, true,
                                false),
                         Chara (true, false, false, true, true, true, true,
                                 false),
                         Chara (false, true, true, true, false, true, true,
                                 false),
                         Chara (true, false, false, false, false, true, true,
                                 false),
                         Chara (true, false, true, true, false, true, true,
                                 false),
                         Chara (true, false, false, true, false, true, true,
                                 false),
                         Chara (true, true, false, false, false, true, true,
                                 false),
                         Chara (false, false, false, false, false, true, false,
                                 false),
                         Chara (false, false, false, false, true, true, true,
                                 false),
                         Chara (true, false, false, false, false, true, true,
                                 false),
                         Chara (false, true, false, false, true, true, true,
                                 false),
                         Chara (true, true, false, false, true, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false),
                         Chara (false, true, false, false, true, true, true,
                                 false),
                         Chara (false, false, false, false, false, true, false,
                                 false),
                         Chara (true, true, false, false, false, true, true,
                                 false),
                         Chara (false, false, false, true, false, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false),
                         Chara (true, true, false, false, false, true, true,
                                 false),
                         Chara (true, true, false, true, false, true, true,
                                 false),
                         Chara (false, false, false, false, false, true, false,
                                 false),
                         Chara (false, true, true, false, false, true, true,
                                 false),
                         Chara (true, false, false, false, false, true, true,
                                 false),
                         Chara (true, false, false, true, false, true, true,
                                 false),
                         Chara (false, false, true, true, false, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false),
                         Chara (false, false, true, false, false, true, true,
                                 false)]))));

fun sum_join (Inl x) = x
  | sum_join (Inr x) = x;

fun return x = (fn ts => Inr (x, ts));

fun ensure_parser p =
  (fn ts =>
    bind (p ts)
      (fn (x, tsa) =>
        (if less_eq_nat (ll_fuel tsa) (ll_fuel ts) then Inr (x, tsa)
          else Inl (fn _ =>
                     shows_prec_list show_char zero_nata
                       [Chara (false, false, true, false, false, false, true,
                                false),
                         Chara (true, false, false, true, true, true, true,
                                 false),
                         Chara (false, true, true, true, false, true, true,
                                 false),
                         Chara (true, false, false, false, false, true, true,
                                 false),
                         Chara (true, false, true, true, false, true, true,
                                 false),
                         Chara (true, false, false, true, false, true, true,
                                 false),
                         Chara (true, true, false, false, false, true, true,
                                 false),
                         Chara (false, false, false, false, false, true, false,
                                 false),
                         Chara (false, false, false, false, true, true, true,
                                 false),
                         Chara (true, false, false, false, false, true, true,
                                 false),
                         Chara (false, true, false, false, true, true, true,
                                 false),
                         Chara (true, true, false, false, true, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false),
                         Chara (false, true, false, false, true, true, true,
                                 false),
                         Chara (false, false, false, false, false, true, false,
                                 false),
                         Chara (true, true, false, false, false, true, true,
                                 false),
                         Chara (false, false, false, true, false, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false),
                         Chara (true, true, false, false, false, true, true,
                                 false),
                         Chara (true, true, false, true, false, true, true,
                                 false),
                         Chara (false, false, false, false, false, true, false,
                                 false),
                         Chara (false, true, true, false, false, true, true,
                                 false),
                         Chara (true, false, false, false, false, true, true,
                                 false),
                         Chara (true, false, false, true, false, true, true,
                                 false),
                         Chara (false, false, true, true, false, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false),
                         Chara (false, false, true, false, false, true, true,
                                 false)]))));

fun bindb m f =
  (fn ts => bind (ensure_parser m ts) (fn (x, a) => ensure_parser (f x) a));

fun catch_error m f = (case m of Inl a => f a | Inr a => Inr a);

fun alt p1 p2 l =
  catch_error (bind (p1 l) (fn (r, la) => Inr (Inl r, la)))
    (fn e1 =>
      catch_error (bind (p2 l) (fn (r, la) => Inr (Inr r, la)))
        (fn e2 =>
          Inl (fn _ =>
                e1 () o
                  shows_prec_list show_char zero_nata
                    [Chara (false, true, false, true, false, false, false,
                             false),
                      Chara (false, false, false, false, false, true, false,
                              false),
                      Chara (false, false, false, false, false, true, false,
                              false),
                      Chara (false, false, true, true, true, true, true, false),
                      Chara (false, false, false, false, false, true, false,
                              false)] o
                  e2 ())));

fun repeat p l =
  bindb (alt (bindb (ensure_cparser p)
               (fn a => bindb (repeat p) (fn b => return (a :: b))))
          (return []))
    (fn x => return (sum_join x)) l;

fun ll_list (LL (x1, x2)) = x2;

fun get_tokens x = (fn ll => Inr (ll_list ll, ll)) x;

fun error_aux e = (fn _ => Inl e);

fun shows_quote s =
  shows_prec_char zero_nata
    (Chara (true, true, true, false, false, true, false, false)) o
    s o
    shows_prec_char zero_nata
      (Chara (true, true, true, false, false, true, false, false));

fun err_expecting_aux A_ msg =
  bindb get_tokens
    (fn ts =>
      error_aux
        (fn _ =>
          shows_string
            [Chara (true, false, true, false, false, true, true, false),
              Chara (false, false, false, true, true, true, true, false),
              Chara (false, false, false, false, true, true, true, false),
              Chara (true, false, true, false, false, true, true, false),
              Chara (true, true, false, false, false, true, true, false),
              Chara (false, false, true, false, true, true, true, false),
              Chara (true, false, false, true, false, true, true, false),
              Chara (false, true, true, true, false, true, true, false),
              Chara (true, true, true, false, false, true, true, false),
              Chara (false, false, false, false, false, true, false, false)] o
            msg () o
            shows_string
              [Chara (false, false, true, true, false, true, false, false),
                Chara (false, false, false, false, false, true, false, false),
                Chara (false, true, false, false, false, true, true, false),
                Chara (true, false, true, false, true, true, true, false),
                Chara (false, false, true, false, true, true, true, false),
                Chara (false, false, false, false, false, true, false, false),
                Chara (false, true, true, false, false, true, true, false),
                Chara (true, true, true, true, false, true, true, false),
                Chara (true, false, true, false, true, true, true, false),
                Chara (false, true, true, true, false, true, true, false),
                Chara (false, false, true, false, false, true, true, false),
                Chara (false, true, false, true, true, true, false, false),
                Chara (false, false, false, false, false, true, false, false)] o
            shows_quote
              (shows_prec_list A_ zero_nata
                (take (nat_of_integer (100 : IntInf.int)) ts))));

fun get ll =
  let
    val LL (nat, lista) = ll;
  in
    (if equal_nata nat zero_nata
      then Inl (fn _ =>
                 shows_string
                   [Chara (true, false, true, false, false, false, true, false),
                     Chara (false, false, false, true, true, true, true, false),
                     Chara (false, false, false, false, true, true, true,
                             false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (true, true, false, false, false, true, true, false),
                     Chara (false, false, true, false, true, true, true, false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (true, true, true, false, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, false, true, true, false, true, true, false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (false, true, false, false, true, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (false, false, false, false, true, true, true,
                             false),
                     Chara (true, false, true, false, true, true, true, false),
                     Chara (false, false, true, false, true, true, true,
                             false)])
      else (case lista
             of [] =>
               Inl (fn _ =>
                     shows_string
                       [Chara (true, false, true, false, false, false, true,
                                false),
                         Chara (false, false, false, true, true, true, true,
                                 false),
                         Chara (false, false, false, false, true, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false),
                         Chara (true, true, false, false, false, true, true,
                                 false),
                         Chara (false, false, true, false, true, true, true,
                                 false),
                         Chara (true, false, false, true, false, true, true,
                                 false),
                         Chara (false, true, true, true, false, true, true,
                                 false),
                         Chara (true, true, true, false, false, true, true,
                                 false),
                         Chara (false, false, false, false, false, true, false,
                                 false),
                         Chara (true, false, true, true, false, true, true,
                                 false),
                         Chara (true, true, true, true, false, true, true,
                                 false),
                         Chara (false, true, false, false, true, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false),
                         Chara (false, false, false, false, false, true, false,
                                 false),
                         Chara (true, false, false, true, false, true, true,
                                 false),
                         Chara (false, true, true, true, false, true, true,
                                 false),
                         Chara (false, false, false, false, true, true, true,
                                 false),
                         Chara (true, false, true, false, true, true, true,
                                 false),
                         Chara (false, false, true, false, true, true, true,
                                 false)])
             | x :: xs => Inr (x, LL (minus_nat nat one_nata, xs))))
  end;

fun any (A1_, A2_) ts =
  bindb get
    (fn t =>
      (if membera A1_ ts t then return t
        else err_expecting_aux A2_
               (fn _ =>
                 shows_string
                   [Chara (true, true, true, true, false, false, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (false, true, true, false, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false)] o
                   shows_prec_list A2_ zero_nata ts)));

fun lx_ws x =
  repeat
    (any (equal_char, show_char)
      [Chara (false, false, false, false, false, true, false, false),
        Chara (false, true, false, true, false, false, false, false),
        Chara (true, false, false, true, false, false, false, false),
        Chara (true, false, true, true, false, false, false, false)])
    x;

fun exactly (A1_, A2_) ts =
  bindb (alt (foldr
               (fn t => fn p =>
                 bindb get
                   (fn x =>
                     (if eq A1_ x t then bindb p (fn xa => return (x :: xa))
                       else error_aux (fn _ => id))))
               ts (return []))
          (err_expecting_aux A2_
            (fn _ =>
              shows_string
                [Chara (true, false, true, false, false, false, true, false),
                  Chara (false, false, false, true, true, true, true, false),
                  Chara (true, false, false, false, false, true, true, false),
                  Chara (true, true, false, false, false, true, true, false),
                  Chara (false, false, true, false, true, true, true, false),
                  Chara (false, false, true, true, false, true, true, false),
                  Chara (true, false, false, true, true, true, true, false),
                  Chara (false, false, false, false, false, true, false,
                          false)] o
                shows_prec_list A2_ zero_nata ts)))
    (fn x => return (sum_join x));

fun bracket_close x =
  bindb lx_ws
    (fn _ =>
      exactly (equal_char, show_char)
        [Chara (true, false, true, true, true, false, true, false)])
    x;

fun bracket_open x =
  bindb lx_ws
    (fn _ =>
      exactly (equal_char, show_char)
        [Chara (true, true, false, true, true, false, true, false)])
    x;

fun chainL1 a f =
  bindb a
    (fn x =>
      bindb (repeat
              (bindb f (fn aa => bindb a (fn b => return (fn ab => aa ab b)))))
        (fn xs => return (foldl (fn aa => fn fa => fa aa) x xs)));

fun comma x =
  bindb lx_ws
    (fn _ =>
      exactly (equal_char, show_char)
        [Chara (false, false, true, true, false, true, false, false)])
    x;

fun parse_list a =
  chainL1 (bindb a (fn x => return [x]))
    (bindb comma (fn _ => return (fn aa => fn b => aa @ b)));

fun brace_close x =
  bindb lx_ws
    (fn _ =>
      exactly (equal_char, show_char)
        [Chara (true, false, true, true, true, true, true, false)])
    x;

fun json_character x =
  bindb get
    (fn xa =>
      (if not (membera equal_char
                [Chara (false, true, false, false, false, true, false, false),
                  Chara (false, true, false, false, true, false, false, true),
                  Chara (false, true, false, true, false, false, false, false)]
                xa)
        then return xa
        else err_expecting_aux show_char
               (fn _ =>
                 shows_string
                   [Chara (false, true, false, true, false, false, true, false),
                     Chara (true, true, false, false, true, false, true, false),
                     Chara (true, true, true, true, false, false, true, false),
                     Chara (false, true, true, true, false, false, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, true, false, false, true, true, true, false),
                     Chara (false, false, true, false, true, true, true, false),
                     Chara (false, true, false, false, true, true, true, false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (true, true, true, false, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, true, false, false, false, true, true, false),
                     Chara (false, false, false, true, false, true, true,
                             false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (false, true, false, false, true, true, true, false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (true, true, false, false, false, true, true, false),
                     Chara (false, false, true, false, true, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, true, false, false, true, true, true,
                             false)])))
    x;

fun identifier x =
  bindb (exactly (equal_char, show_char)
          [Chara (false, true, false, false, false, true, false, false)])
    (fn _ =>
      bindb json_character
        (fn xa =>
          bindb (repeat json_character)
            (fn xaa =>
              bindb (exactly (equal_char, show_char)
                      [Chara (false, true, false, false, false, true, false,
                               false)])
                (fn _ => return (xa :: xaa)))))
    x;

fun brace_open x =
  bindb lx_ws
    (fn _ =>
      exactly (equal_char, show_char)
        [Chara (true, true, false, true, true, true, true, false)])
    x;

fun colon x =
  bindb lx_ws
    (fn _ =>
      exactly (equal_char, show_char)
        [Chara (false, true, false, true, true, true, false, false)])
    x;

fun range (A1_, A2_) a b =
  bindb get
    (fn x =>
      (if less_eq ((ord_preorder o preorder_order o order_linorder) A1_) a
            x andalso
            less_eq ((ord_preorder o preorder_order o order_linorder) A1_) x b
        then return x
        else err_expecting_aux A2_
               (fn _ =>
                 shows_string
                   [Chara (false, false, true, false, true, false, true, false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (true, true, false, true, false, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (false, true, false, false, true, true, true, false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (true, true, true, false, false, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false)] o
                   shows_prec A2_ zero_nata a o
                   shows_string
                     [Chara (false, false, false, false, false, true, false,
                              false),
                       Chara (true, false, true, true, false, true, false,
                               false),
                       Chara (false, false, false, false, false, true, false,
                               false)] o
                   shows_prec A2_ zero_nata b)));

fun lx_digit x =
  range (linorder_char, show_char)
    (Chara (false, false, false, false, true, true, false, false))
    (Chara (true, false, false, true, true, true, false, false)) x;

fun lx_nat_aux acc l =
  bindb (alt (bindb lx_digit
               (fn x =>
                 lx_nat_aux
                   (plus_nata
                     (times_nata (nat_of_integer (10 : IntInf.int)) acc)
                     (minus_nat (nat_of_char x)
                       (nat_of_char
                         (Chara
                           (false, false, false, false, true, true, false,
                             false)))))))
          (return acc))
    (fn x => return (sum_join x)) l;

fun lx_nat x =
  bindb lx_digit
    (fn xa =>
      lx_nat_aux
        (minus_nat (nat_of_char xa)
          (nat_of_char
            (Chara (false, false, false, false, true, true, false, false)))))
    x;

fun lx_int x =
  bindb (alt (bindb
               (exactly (equal_char, show_char)
                 [Chara (true, false, true, true, false, true, false, false)])
               (fn _ =>
                 bindb lx_nat
                   (fn xa => return ((uminus_inta o int_of_nat) xa))))
          (bindb lx_nat (fn xa => return (int_of_nat xa))))
    (fn xa => return (sum_join xa)) x;

fun json_string x =
  bindb (exactly (equal_char, show_char)
          [Chara (false, true, false, false, false, true, false, false)])
    (fn _ =>
      bindb (repeat json_character)
        (fn a =>
          bindb (exactly (equal_char, show_char)
                  [Chara (false, true, false, false, false, true, false,
                           false)])
            (fn _ => return a)))
    x;

fun times_int k l = Int_of_integer (integer_of_int k * integer_of_int l);

fun minus_rat p q =
  Frct let
         val a = quotient_of p;
         val (aa, c) = a;
         val b = quotient_of q;
         val (ba, d) = b;
       in
         normalize (minus_inta (times_int aa d) (times_int ba c), times_int c d)
       end;

fun plus_rat p q =
  Frct let
         val a = quotient_of p;
         val (aa, c) = a;
         val b = quotient_of q;
         val (ba, d) = b;
       in
         normalize (plus_inta (times_int aa d) (times_int ba c), times_int c d)
       end;

fun size_list x = gen_length zero_nata x;

fun nats_to_nat x [] = x
  | nats_to_nat x (n :: ns) =
    nats_to_nat (plus_nata (times_nata (nat_of_integer (10 : IntInf.int)) x) n)
      ns;

fun power A_ a n =
  (if equal_nata n zero_nata then one (one_power A_)
    else times (times_power A_) a (power A_ a (minus_nat n one_nata)));

fun lx_rat_fract x =
  bindb lx_digit
    (fn xa =>
      bindb (repeat
              (bindb lx_digit
                (fn xb =>
                  return
                    (minus_nat (nat_of_char xb)
                      (nat_of_char
                        (Chara
                          (false, false, false, false, true, true, false,
                            false)))))))
        (fn xaa =>
          return
            (fract
              (int_of_nat
                (nats_to_nat zero_nata
                  (minus_nat (nat_of_char xa)
                     (nat_of_char
                       (Chara
                         (false, false, false, false, true, true, false,
                           false))) ::
                    xaa)))
              (int_of_nat
                (power power_nat (nat_of_integer (10 : IntInf.int))
                  (size_list
                    (minus_nat (nat_of_char xa)
                       (nat_of_char
                         (Chara
                           (false, false, false, false, true, true, false,
                             false))) ::
                      xaa)))))))
    x;

fun lx_rat x =
  bindb lx_int
    (fn xa =>
      bindb (exactly (equal_char, show_char)
              [Chara (false, true, true, true, false, true, false, false)])
        (fn _ =>
          bindb lx_rat_fract
            (fn xaa =>
              return
                (if less_eq_int zero_inta xa then plus_rat (of_int xa) xaa
                  else minus_rat (of_int xa) xaa))))
    x;

fun atom x =
  bindb lx_ws
    (fn _ =>
      bindb (alt (bindb json_string (fn xa => return (String xa)))
              (bindb
                (alt (bindb lx_rat (fn xa => return (Rat xa)))
                  (bindb
                    (alt (bindb lx_nat (fn xa => return (Nata xa)))
                      (bindb
                        (alt (bindb lx_int (fn xa => return (Int xa)))
                          (bindb
                            (alt (bindb
                                   (exactly (equal_char, show_char)
                                     [Chara
(false, false, true, false, true, true, true, false),
                                       Chara
 (false, true, false, false, true, true, true, false),
                                       Chara
 (true, false, true, false, true, true, true, false),
                                       Chara
 (true, false, true, false, false, true, true, false)])
                                   (fn _ => return (Boolean true)))
                              (bindb
                                (alt (bindb
                                       (exactly (equal_char, show_char)
 [Chara (false, true, true, false, false, true, true, false),
   Chara (true, false, false, false, false, true, true, false),
   Chara (false, false, true, true, false, true, true, false),
   Chara (true, true, false, false, true, true, true, false),
   Chara (true, false, true, false, false, true, true, false)])
                                       (fn _ => return (Boolean false)))
                                  (bindb
                                    (exactly (equal_char, show_char)
                                      [Chara
 (false, true, true, true, false, true, true, false),
Chara (true, false, true, false, true, true, true, false),
Chara (false, false, true, true, false, true, true, false),
Chara (false, false, true, true, false, true, true, false)])
                                    (fn _ => return Null)))
                                (fn xa => return (sum_join xa))))
                            (fn xa => return (sum_join xa))))
                        (fn xa => return (sum_join xa))))
                    (fn xa => return (sum_join xa))))
                (fn xa => return (sum_join xa))))
        (fn xa => return (sum_join xa)))
    x;

fun seq l =
  bindb bracket_open
    (fn _ =>
      bindb (alt (parse_list json) (bindb lx_ws (fn _ => return [])))
        (fn x => bindb bracket_close (fn _ => return (Arraya (sum_join x)))))
    l
and json l =
  bindb (alt atom (bindb (alt seq dict) (fn x => return (sum_join x))))
    (fn x => return (sum_join x)) l
and dict l =
  bindb brace_open
    (fn _ =>
      bindb (alt (parse_list
                   (bindb lx_ws
                     (fn _ =>
                       bindb identifier
                         (fn a =>
                           bindb colon
                             (fn _ => bindb json (fn b => return (a, b)))))))
              (bindb lx_ws (fn _ => return [])))
        (fn x => bindb brace_close (fn _ => return (Object (sum_join x)))))
    l;

fun list_update [] i y = []
  | list_update (x :: xs) i y =
    (if equal_nata i zero_nata then y :: xs
      else x :: list_update xs (minus_nat i one_nata) y);

fun find_index uu [] = zero_nata
  | find_index p (x :: xs) =
    (if p x then zero_nata else plus_nata (find_index p xs) one_nata);

fun index A_ xs = (fn a => find_index (fn x => eq A_ x a) xs);

fun of_phantom (Phantom x) = x;

fun card (A1_, A2_) (Coset xs) =
  minus_nat (of_phantom (card_UNIV A1_)) (size_list (remdups A2_ xs))
  | card (A1_, A2_) (Set xs) = size_list (remdups A2_ xs);

fun ht_new_sz (A1_, A2_) B_ n =
  let
    val l = replicate n [];
  in
    (fn f_ => fn () => f_ (((fn () => Array.fromList l)) ()) ())
      (fn a => (fn () => (HashTable (a, zero_nata))))
  end;

fun ht_new (A1_, A2_) B_ = ht_new_sz (A1_, A2_) B_ (def_hashmap_size A1_ Type);

fun nat_of_uint32 x =
  nat_of_integer (IntInf.fromLarge (Word32.toLargeInt x) : IntInf.int);

fun nat_of_hashcode x = nat_of_uint32 x;

fun bounded_hashcode_nat A_ n x =
  modulo_nat (nat_of_hashcode (hashcode A_ x)) n;

fun the_array (HashTable (a, uu)) = a;

fun ls_update A_ k v [] = ([(k, v)], false)
  | ls_update A_ k v ((l, w) :: ls) =
    (if eq A_ k l then ((k, v) :: ls, true)
      else let
             val r = ls_update A_ k v ls;
           in
             ((l, w) :: fst r, snd r)
           end);

fun the_size (HashTable (uu, n)) = n;

fun ht_upd (A1_, A2_, A3_) B_ k v ht =
  (fn f_ => fn () => f_ ((len (heap_list (heap_prod A3_ B_)) (the_array ht)) ())
    ())
    (fn m =>
      let
        val i = bounded_hashcode_nat A2_ m k;
      in
        (fn f_ => fn () => f_
          ((ntha (heap_list (heap_prod A3_ B_)) (the_array ht) i) ()) ())
          (fn l =>
            let
              val la = ls_update A1_ k v l;
            in
              (fn f_ => fn () => f_
                ((upd (heap_list (heap_prod A3_ B_)) i (fst la) (the_array ht))
                ()) ())
                (fn _ =>
                  let
                    val n = (if snd la then the_size ht else suc (the_size ht));
                  in
                    (fn () => (HashTable (the_array ht, n)))
                  end)
            end)
      end);

val top_set : 'a set = Coset [];

fun eq_set (A1_, A2_) (Coset xs) (Coset ys) =
  list_all (membera A2_ ys) xs andalso list_all (membera A2_ xs) ys
  | eq_set (A1_, A2_) (Set xs) (Set ys) =
    list_all (membera A2_ ys) xs andalso list_all (membera A2_ xs) ys
  | eq_set (A1_, A2_) (Set ys) (Coset xs) =
    let
      val n = card (A1_, A2_) top_set;
    in
      (if equal_nata n zero_nata then false
        else let
               val xsa = remdups A2_ xs;
               val ysa = remdups A2_ ys;
             in
               equal_nata (plus_nata (size_list xsa) (size_list ysa)) n andalso
                 (list_all (fn x => not (membera A2_ ysa x)) xsa andalso
                   list_all (fn y => not (membera A2_ xsa y)) ysa)
             end)
    end
  | eq_set (A1_, A2_) (Coset xs) (Set ys) =
    let
      val n = card (A1_, A2_) top_set;
    in
      (if equal_nata n zero_nata then false
        else let
               val xsa = remdups A2_ xs;
               val ysa = remdups A2_ ys;
             in
               equal_nata (plus_nata (size_list xsa) (size_list ysa)) n andalso
                 (list_all (fn x => not (membera A2_ ysa x)) xsa andalso
                   list_all (fn y => not (membera A2_ xsa y)) ysa)
             end)
    end;

fun map_default b f a = (case f a of NONE => b | SOME ba => ba);

fun ht_insls (A1_, A2_, A3_) B_ [] ht = (fn () => ht)
  | ht_insls (A1_, A2_, A3_) B_ ((k, v) :: l) ht =
    (fn f_ => fn () => f_ ((ht_upd (A1_, A2_, A3_) B_ k v ht) ()) ())
      (ht_insls (A1_, A2_, A3_) B_ l);

fun ht_copy (A1_, A2_, A3_) B_ n src dst =
  (if equal_nata n zero_nata then (fn () => dst)
    else (fn f_ => fn () => f_
           ((ntha (heap_list (heap_prod A3_ B_)) (the_array src)
              (minus_nat n one_nata))
           ()) ())
           (fn l =>
             (fn f_ => fn () => f_ ((ht_insls (A1_, A2_, A3_) B_ l dst) ()) ())
               (ht_copy (A1_, A2_, A3_) B_ (minus_nat n one_nata) src)));

fun product_lists [] = [[]]
  | product_lists (xs :: xss) =
    maps (fn x => map (fn a => x :: a) (product_lists xss)) xs;

fun app f a = f a;

fun subset (A1_, A2_) (Coset xs) (Set ys) =
  let
    val n = card (A1_, A2_) top_set;
  in
    less_nat zero_nata n andalso equal_nata (card (A1_, A2_) (Set (xs @ ys))) n
  end
  | subset (A1_, A2_) (Set ys) b = list_all (fn y => member A2_ y b) ys
  | subset (A1_, A2_) a (Coset ys) = list_all (fn y => not (member A2_ y a)) ys;

fun hm_isEmpty ht = (fn () => (equal_nata (the_size ht) zero_nata));

fun fold_map f [] = (fn () => [])
  | fold_map f (x :: xs) =
    (fn f_ => fn () => f_ ((f x) ()) ())
      (fn y =>
        (fn f_ => fn () => f_ ((fold_map f xs) ()) ())
          (fn ys => (fn () => (y :: ys))));

val tRACE_impl : (unit -> unit) = (fn () => (tracea ()));

fun array_get a = FArray.IsabelleMapping.array_get a o integer_of_nat;

fun array_set a = FArray.IsabelleMapping.array_set a o integer_of_nat;

fun new_array v = FArray.IsabelleMapping.new_array v o integer_of_nat;

fun ls_delete A_ k [] = ([], false)
  | ls_delete A_ k ((l, w) :: ls) =
    (if eq A_ k l then (ls, true) else let
 val r = ls_delete A_ k ls;
                                       in
 ((l, w) :: fst r, snd r)
                                       end);

fun ht_delete (A1_, A2_, A3_) B_ k ht =
  (fn f_ => fn () => f_ ((len (heap_list (heap_prod A3_ B_)) (the_array ht)) ())
    ())
    (fn m =>
      let
        val i = bounded_hashcode_nat A2_ m k;
      in
        (fn f_ => fn () => f_
          ((ntha (heap_list (heap_prod A3_ B_)) (the_array ht) i) ()) ())
          (fn l =>
            let
              val la = ls_delete A1_ k l;
            in
              (fn f_ => fn () => f_
                ((upd (heap_list (heap_prod A3_ B_)) i (fst la) (the_array ht))
                ()) ())
                (fn _ =>
                  let
                    val n =
                      (if snd la then minus_nat (the_size ht) one_nata
                        else the_size ht);
                  in
                    (fn () => (HashTable (the_array ht, n)))
                  end)
            end)
      end);

fun ls_lookup A_ x [] = NONE
  | ls_lookup A_ x ((k, v) :: l) =
    (if eq A_ x k then SOME v else ls_lookup A_ x l);

fun ht_lookup (A1_, A2_, A3_) B_ x ht =
  (fn f_ => fn () => f_ ((len (heap_list (heap_prod A3_ B_)) (the_array ht)) ())
    ())
    (fn m =>
      let
        val i = bounded_hashcode_nat A2_ m x;
      in
        (fn f_ => fn () => f_
          ((ntha (heap_list (heap_prod A3_ B_)) (the_array ht) i) ()) ())
          (fn l => (fn () => (ls_lookup A1_ x l)))
      end);

fun ht_rehash (A1_, A2_, A3_) B_ ht =
  (fn f_ => fn () => f_ ((len (heap_list (heap_prod A3_ B_)) (the_array ht)) ())
    ())
    (fn n =>
      (fn f_ => fn () => f_
        ((ht_new_sz (A2_, A3_) B_
           (times_nata (nat_of_integer (2 : IntInf.int)) n))
        ()) ())
        (ht_copy (A1_, A2_, A3_) B_ n ht));

val load_factor : nat = nat_of_integer (75 : IntInf.int);

fun ht_update (A1_, A2_, A3_) B_ k v ht =
  (fn f_ => fn () => f_ ((len (heap_list (heap_prod A3_ B_)) (the_array ht)) ())
    ())
    (fn m =>
      (fn f_ => fn () => f_
        ((if less_eq_nat (times_nata m load_factor)
               (times_nata (the_size ht) (nat_of_integer (100 : IntInf.int)))
           then ht_rehash (A1_, A2_, A3_) B_ ht else (fn () => ht))
        ()) ())
        (ht_upd (A1_, A2_, A3_) B_ k v));

fun map_act f (In x1) = In (f x1)
  | map_act f (Out x2) = Out (f x2)
  | map_act f (Sil x3) = Sil (f x3);

val bot_set : 'a set = Set [];

fun set_act A_ (In x1) = insert A_ x1 bot_set
  | set_act A_ (Out x2) = insert A_ x2 bot_set
  | set_act A_ (Sil x3) = insert A_ x3 bot_set;

fun uncurry0 c = (fn _ => c);

fun time_it s f = let
                    val _ = Timing.start_timer ();
                    val r = f ();
                    val _ = Timing.save_time s;
                  in
                    r
                  end;

fun array_copy A_ a =
  (fn a => fn () =>
  if Array.length a = 0
  then Array.fromList []
  else
    let
      val x = Array.sub(a, 0)
      val n = Array.array (Array.length a, x)
      val _ = Array.copy {src=a,dst=n,di=0}
    in n end
) a;

fun array_grow a = FArray.IsabelleMapping.array_grow a o integer_of_nat;

fun binda m f = (case m of Result a => f a | Error a => Error a);

fun hm_it_adjust (A1_, A2_) B_ v ht =
  (if equal_nata v zero_nata then (fn () => zero_nata)
    else (fn f_ => fn () => f_
           ((ntha (heap_list (heap_prod A2_ B_)) (the_array ht)
              (suc (minus_nat v one_nata)))
           ()) ())
           (fn a =>
             (case a
               of [] =>
                 hm_it_adjust (A1_, A2_) B_
                   (minus_nat (suc (minus_nat v one_nata)) one_nata) ht
               | _ :: _ => (fn () => (suc (minus_nat v one_nata))))));

fun op_list_rev x = rev x;

fun all_interval_nat p i j =
  less_eq_nat j i orelse p i andalso all_interval_nat p (suc i) j;

fun map_index n f [] = []
  | map_index n f (x :: xs) = f n x :: map_index (suc n) f xs;

fun pred_act A_ = (fn p => fn x => ball (set_act A_ x) p);

fun eoi A_ =
  bindb get_tokens
    (fn tks =>
      (if null tks then return ()
        else err_expecting_aux A_
               (fn _ =>
                 shows_string
                   [Chara (true, false, true, false, false, true, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (false, false, true, false, false, true, true,
                             false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (false, true, true, false, false, true, true, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (false, false, false, false, true, true, true,
                             false),
                     Chara (true, false, true, false, true, true, true, false),
                     Chara (false, false, true, false, true, true, true,
                             false)])));

fun pR_CONST x = x;

fun op_map_lookup x = (fn k => fn m => m k) x;

fun swap p = (snd p, fst p);

fun whilea b c s = (if b s then whilea b c (c s) else s);

fun array_length x = (nat_of_integer o FArray.IsabelleMapping.array_length) x;

fun array_shrink a = FArray.IsabelleMapping.array_shrink a o integer_of_nat;

fun assert b m = (if b then Result () else Error [m]);

val op_list_empty : 'a list = [];

fun as_get s i = let
                   val a = s;
                   val (aa, _) = a;
                 in
                   array_get aa i
                 end;

fun as_shrink s =
  let
    val a = s;
    val (aa, n) = a;
    val ab =
      (if less_eq_nat (times_nata (nat_of_integer (128 : IntInf.int)) n)
            (array_length aa) andalso
            less_nat (nat_of_integer (4 : IntInf.int)) n
        then array_shrink aa n else aa);
  in
    (ab, n)
  end;

fun as_pop s = let
                 val a = s;
                 val (aa, n) = a;
               in
                 as_shrink (aa, minus_nat n one_nata)
               end;

fun as_set s i x = let
                     val a = s;
                     val (aa, b) = a;
                   in
                     (array_set aa i x, b)
                   end;

fun as_top s = let
                 val a = s;
                 val (aa, n) = a;
               in
                 array_get aa (minus_nat n one_nata)
               end;

fun hm_it_next_key (A1_, A2_) B_ ht =
  (fn f_ => fn () => f_ ((len (heap_list (heap_prod A2_ B_)) (the_array ht)) ())
    ())
    (fn n =>
      (if equal_nata n zero_nata then (raise Fail "Map is empty!")
        else (fn f_ => fn () => f_
               ((hm_it_adjust (A1_, A2_) B_ (minus_nat n one_nata) ht) ()) ())
               (fn i =>
                 (fn f_ => fn () => f_
                   ((ntha (heap_list (heap_prod A2_ B_)) (the_array ht) i) ())
                   ())
                   (fn a =>
                     (case a of [] => (raise Fail "Map is empty!")
                       | x :: _ => (fn () => (fst x)))))));

fun min A_ a b = (if less_eq A_ a b then a else b);

fun imp_for_inta i u f s =
  imp_fora_inner (integer_of_nat i) (integer_of_nat u) (f o nat_of_integer) s;

fun mtx_tabulate (A1_, A2_, A3_) (B1_, B2_) n m c =
  (fn f_ => fn () => f_ ((new B2_ (times_nata n m) (zero B1_)) ()) ())
    (fn ma =>
      (fn f_ => fn () => f_
        ((imp_for_inta zero_nata (times_nata n m)
           (fn k => fn (i, (j, maa)) =>
             (fn f_ => fn () => f_ ((upd B2_ k (c (i, j)) maa) ()) ())
               (fn _ =>
                 let
                   val ja = plus_nata j one_nata;
                 in
                   (if less_nat ja m then (fn () => (i, (ja, maa)))
                     else (fn () => (plus A2_ i (one A1_), (zero_nata, maa))))
                 end))
           (zero A3_, (zero_nata, ma)))
        ()) ())
        (fn (_, a) => let
                        val (_, aa) = a;
                      in
                        (fn () => aa)
                      end));

fun v_dbm_impl (A1_, A2_) n =
  mtx_tabulate (one_nat, plus_nat, zero_nat)
    (zero_DBMEntry
       ((zero_monoid_add o monoid_add_comm_monoid_add o
          comm_monoid_add_ordered_comm_monoid_add o
          ordered_comm_monoid_add_linordered_ab_monoid_add o
          linordered_ab_monoid_add_linordered_cancel_ab_monoid_add)
         A1_),
      heap_DBMEntry A2_)
    (suc n) (suc n)
    (v_dbm (zero_nat, equal_nat, ord_nat)
      ((zero_monoid_add o monoid_add_comm_monoid_add o
         comm_monoid_add_ordered_comm_monoid_add o
         ordered_comm_monoid_add_linordered_ab_monoid_add o
         linordered_ab_monoid_add_linordered_cancel_ab_monoid_add)
        A1_)
      n);

fun combine2_gen comb (Error e1) (Error e2) = Error (e1 @ e2)
  | combine2_gen comb (Error e) (Result uu) = Error e
  | combine2_gen comb (Result uv) (Error e) = Error e
  | combine2_gen comb (Result a) (Result b) = comb a b;

fun combine [] = Result []
  | combine (x :: xs) =
    combine2_gen (fn xa => fn xsa => Result (xa :: xsa)) x (combine xs);

fun err_msg m (Error es) = Error (m :: es)
  | err_msg m (Result v) = Result v;

fun hms_lookup lookup copy k m =
  (fn f_ => fn () => f_ ((lookup k m) ()) ())
    (fn a =>
      (case a of NONE => (fn () => NONE)
        | SOME v =>
          (fn f_ => fn () => f_ ((copy v) ()) ())
            (fn va => (fn () => (SOME va)))));

fun as_push s x =
  let
    val a = s;
    val (aa, n) = a;
    val ab =
      (if equal_nata n (array_length aa)
        then array_grow aa
               (max ord_nat (nat_of_integer (4 : IntInf.int))
                 (times_nata (nat_of_integer (2 : IntInf.int)) n))
               x
        else aa);
    val ac = array_set ab n x;
  in
    (ac, plus_nata n one_nata)
  end;

fun as_take m s = let
                    val a = s;
                    val (aa, n) = a;
                  in
                    (if less_nat m n then as_shrink (aa, m) else (aa, n))
                  end;

fun rev_append [] ac = ac
  | rev_append (x :: xs) ac = rev_append xs (x :: ac);

fun sup_set A_ (Coset xs) a = Coset (filter (fn x => not (member A_ x a)) xs)
  | sup_set A_ (Set xs) a = fold (insert A_) xs a;

fun combine2 x = combine2_gen (fn a => fn b => Result (a, b)) x;

fun hms_extract lookup delete k m =
  (fn f_ => fn () => f_ ((lookup k m) ()) ())
    (fn a =>
      (case a of NONE => (fn () => (NONE, m))
        | SOME v =>
          (fn f_ => fn () => f_ ((delete k m) ()) ())
            (fn ma => (fn () => (SOME v, ma)))));

fun mtx_get A_ m mtx e = ntha A_ mtx (plus_nata (times_nata (fst e) m) (snd e));

fun mtx_set A_ m mtx e v =
  upd A_ (plus_nata (times_nata (fst e) m) (snd e)) v mtx;

fun op_list_prepend x = (fn a => x :: a);

fun idx_iteratei_aux get sz i l c f sigma =
  (if equal_nata i zero_nata orelse not (c sigma) then sigma
    else idx_iteratei_aux get sz (minus_nat i one_nata) l c f
           (f (get l (minus_nat sz i)) sigma));

fun idx_iteratei get sz l c f sigma =
  idx_iteratei_aux get (sz l) (sz l) l c f sigma;

fun as_empty B_ uu = (FArray.IsabelleMapping.array_of_list [], zero B_);

fun as_length x = snd x;

fun last_seg_tr A_ s =
  let
    val (a, (aa, (_, _))) = s;
    val (_, bc) =
      whilea
        (fn (xe, _) =>
          less_nat xe
            (if equal_nata
                  (plus_nata (minus_nat (as_length aa) one_nata) one_nata)
                  (as_length aa)
              then as_length a
              else as_get aa
                     (plus_nata (minus_nat (as_length aa) one_nata) one_nata)))
        (fn (ac, bc) => let
                          val xa = as_get a ac;
                        in
                          (suc ac, xa :: bc)
                        end)
        (as_get aa (minus_nat (as_length aa) one_nata), []);
  in
    bc
  end;

fun list_map_update_aux eq k v [] accu = (k, v) :: accu
  | list_map_update_aux eq k v (x :: xs) accu =
    (if eq (fst x) k then (k, v) :: xs @ accu
      else list_map_update_aux eq k v xs (x :: accu));

fun list_map_update eq k v m = list_map_update_aux eq k v m [];

fun list_map_lookup eq uu [] = NONE
  | list_map_lookup eq k (y :: ys) =
    (if eq (fst y) k then SOME (snd y) else list_map_lookup eq k ys);

fun ahm_update_aux eq bhc (HashMap (a, n)) k v =
  let
    val h = bhc (array_length a) k;
    val m = array_get a h;
    val insert = is_none (list_map_lookup eq k m);
  in
    HashMap
      (array_set a h (list_map_update eq k v m),
        (if insert then plus_nata n one_nata else n))
  end;

fun ahm_iteratei_aux a c f sigma =
  idx_iteratei array_get array_length a c (fn x => foldli x c f) sigma;

fun ahm_rehash_auxa bhc n kv a = let
                                   val h = bhc n (fst kv);
                                 in
                                   array_set a h (kv :: array_get a h)
                                 end;

fun ahm_rehash_aux bhc a sz =
  ahm_iteratei_aux a (fn _ => true) (ahm_rehash_auxa bhc sz) (new_array [] sz);

fun ahm_rehash bhc (HashMap (a, n)) sz = HashMap (ahm_rehash_aux bhc a sz, n);

val load_factora : nat = nat_of_integer (75 : IntInf.int);

fun ahm_filled (HashMap (a, n)) =
  less_eq_nat (times_nata (array_length a) load_factora)
    (times_nata n (nat_of_integer (100 : IntInf.int)));

fun hm_grow (HashMap (a, n)) =
  plus_nata (times_nata (nat_of_integer (2 : IntInf.int)) (array_length a))
    (nat_of_integer (3 : IntInf.int));

fun ahm_update eq bhc k v hm =
  let
    val hma = ahm_update_aux eq bhc hm k v;
  in
    (if ahm_filled hma then ahm_rehash bhc hma (hm_grow hma) else hma)
  end;

fun pop_tr (A1_, A2_) s =
  let
    val (a, (aa, (ab, bb))) = s;
    val x = minus_nat (as_length aa) one_nata;
    val xa =
      let
        val (_, bc) =
          whilea
            (fn (xe, _) =>
              less_nat xe
                (if equal_nata (plus_nata x one_nata) (as_length aa)
                  then as_length a else as_get aa (plus_nata x one_nata)))
            (fn (ac, bc) =>
              (suc ac,
                ahm_update (eq A1_) (bounded_hashcode_nat A2_) (as_get a ac)
                  (uminus_inta one_int) bc))
            (as_get aa x, ab);
      in
        bc
      end;
    val xb = as_take (as_top aa) a;
    val xc = as_pop aa;
  in
    (xb, (xc, (xa, bb)))
  end;

fun op_list_is_empty x = null x;

fun glist_delete_aux eq x [] asa = asa
  | glist_delete_aux eq x (y :: ys) asa =
    (if eq x y then rev_append asa ys else glist_delete_aux eq x ys (y :: asa));

fun glist_delete eq x l = glist_delete_aux eq x l [];

fun lx_uppercase x =
  range (linorder_char, show_char)
    (Chara (true, false, false, false, false, false, true, false))
    (Chara (false, true, false, true, true, false, true, false)) x;

fun lx_lowercase x =
  range (linorder_char, show_char)
    (Chara (true, false, false, false, false, true, true, false))
    (Chara (false, true, false, true, true, true, true, false)) x;

fun lx_alpha x =
  bindb (alt lx_lowercase lx_uppercase) (fn xa => return (sum_join xa)) x;

fun imp_nfoldli (x :: ls) c f s =
  (fn f_ => fn () => f_ ((c s) ()) ())
    (fn b =>
      (if b then (fn f_ => fn () => f_ ((f x s) ()) ()) (imp_nfoldli ls c f)
        else (fn () => s)))
  | imp_nfoldli [] c f s = (fn () => s);

fun is_Nil a = (case a of [] => true | _ :: _ => false);

fun fold_error f [] a = Result a
  | fold_error f (x :: xs) a = binda (f x a) (fold_error f xs);

fun the_errors (Error es) = es;

fun find_max_nat n uu =
  (if equal_nata n zero_nata then zero_nata
    else (if uu (minus_nat n one_nata) then minus_nat n one_nata
           else find_max_nat (minus_nat n one_nata) uu));

fun amtx_copy A_ = array_copy A_;

fun amtx_dflt A_ n m v = make A_ (times_nata n m) (fn _ => v);

fun lso_bex_impl pi li =
  imp_nfoldli li (fn sigma => (fn () => (not sigma))) (fn xa => fn _ => pi xa)
    false;

fun gen_token ws p = bindb ws (fn _ => p);

fun ll_from_list l = LL (size_list l, l);

fun show_pres (Inr (ll, uu)) = Inr ll
  | show_pres (Inl e) = Inl e;

fun parse_all ws p =
  show_pres o
    bindb p
      (fn a => bindb ws (fn _ => bindb (eoi show_char) (fn _ => return a))) o
    ll_from_list o
    explode;

fun save_time_impl x =
  ((fn a => (fn () => a)) o (fn a => Timing.save_time a)) x;

fun norm_lower A_ e t = (if dbm_lt A_ e (Lt t) then Lt t else e);

fun norm_upper A_ e t = (if dbm_lt A_ (Le t) e then INF else e);

fun min_int_entry (Lt x) (Lt y) = (if less_eq_int x y then Lt x else Lt y)
  | min_int_entry (Lt x) (Le y) = (if less_eq_int x y then Lt x else Le y)
  | min_int_entry (Le x) (Lt y) = (if less_int x y then Le x else Lt y)
  | min_int_entry (Le x) (Le y) = (if less_eq_int x y then Le x else Le y)
  | min_int_entry INF x = x
  | min_int_entry (Le v) INF = Le v
  | min_int_entry (Lt v) INF = Lt v;

fun and_entry_impl x =
  (fn n => fn ai => fn bib => fn bia => fn bi =>
    (fn f_ => fn () => f_
      ((mtx_get (heap_DBMEntry heap_int) (suc n) bi (ai, bib)) ()) ())
      (fn xa =>
        mtx_set (heap_DBMEntry heap_int) (suc n) bi (ai, bib)
          (min_int_entry xa bia)))
    x;

fun free_impl_int x =
  (fn n => fn ai => fn bi =>
    (fn f_ => fn () => f_
      ((imp_for_inta zero_nata (suc n)
         (fn xa => fn sigma =>
           (if not (equal_nata xa bi)
             then (fn f_ => fn () => f_
                    ((mtx_get (heap_DBMEntry heap_int) (suc n) sigma
                       (xa, zero_nata))
                    ()) ())
                    (mtx_set (heap_DBMEntry heap_int) (suc n) sigma (xa, bi))
             else (fn () => sigma)))
         ai)
      ()) ())
      (imp_for_inta zero_nata (suc n)
        (fn xb => fn sigma =>
          (if not (equal_nata xb bi)
            then mtx_set (heap_DBMEntry heap_int) (suc n) sigma (bi, xb) INF
            else (fn () => sigma)))))
    x;

fun dbm_lt_int (Le a) (Le b) = less_int a b
  | dbm_lt_int (Le a) (Lt b) = less_int a b
  | dbm_lt_int (Lt a) (Le b) = less_eq_int a b
  | dbm_lt_int (Lt a) (Lt b) = less_int a b
  | dbm_lt_int INF uu = false
  | dbm_lt_int (Le v) INF = true
  | dbm_lt_int (Lt v) INF = true;

fun dbm_add_int INF uu = INF
  | dbm_add_int (Le v) INF = INF
  | dbm_add_int (Lt v) INF = INF
  | dbm_add_int (Le a) (Le b) = Le (plus_inta a b)
  | dbm_add_int (Le a) (Lt b) = Lt (plus_inta a b)
  | dbm_add_int (Lt a) (Le b) = Lt (plus_inta a b)
  | dbm_add_int (Lt a) (Lt b) = Lt (plus_inta a b);

fun fw_upd_impl_integer n a k i j =
  let
    val na = n + (1 : IntInf.int);
    val ia = i * na + j;
  in
    (fn f_ => fn () => f_ (((fn () => Array.sub (a, IntInf.toInt ia))) ()) ())
      (fn x =>
        (fn f_ => fn () => f_
          (((fn () => Array.sub (a, IntInf.toInt (i * na + k)))) ()) ())
          (fn y =>
            (fn f_ => fn () => f_
              (((fn () => Array.sub (a, IntInf.toInt (k * na + j)))) ()) ())
              (fn z =>
                let
                  val m = dbm_add_int y z;
                in
                  (if dbm_lt_int m x
                    then (fn a => fn () => (Array.update (a, IntInf.toInt ia, m); a)) a
                    else (fn () => a))
                end)))
  end;

fun fwi_impl_int n a k =
  let
    val na = integer_of_nat n;
    val n_plus_1 = na + (1 : IntInf.int);
  in
    imp_fora_inner (0 : IntInf.int) n_plus_1
      (fn i =>
        imp_fora_inner (0 : IntInf.int) n_plus_1
          (fn ia => fn xa => fw_upd_impl_integer na xa (integer_of_nat k) i ia))
      a
  end;

fun repair_pair_impl_int x =
  (fn n => fn ai => fn bia => fn bi =>
    (fn f_ => fn () => f_ ((fwi_impl_int n ai bi) ()) ())
      (fn xa => fwi_impl_int n xa bia))
    x;

fun restrict_zero_impl n =
  (fn ai => fn bi =>
    (fn f_ => fn () => f_ ((and_entry_impl n bi zero_nata (Le zero_inta) ai) ())
      ())
      (fn x =>
        (fn f_ => fn () => f_ ((and_entry_impl n zero_nata bi (Le zero_inta) x)
          ()) ())
          (fn x_a => repair_pair_impl_int n x_a bi zero_nata)));

fun pre_reset_impl n =
  (fn ai => fn bi =>
    (fn f_ => fn () => f_ ((restrict_zero_impl n ai bi) ()) ())
      (fn x => free_impl_int n x bi));

fun gi_E (Gen_g_impl_ext (gi_V, gi_E, gi_V0, more)) = gi_E;

fun more (Gen_g_impl_ext (gi_V, gi_E, gi_V0, more)) = more;

fun combine_map f xs = combine (map f xs);

fun as_is_empty s = equal_nata (snd s) zero_nata;

fun part B_ f pivot (x :: xs) =
  let
    val (lts, (eqs, gts)) = part B_ f pivot xs;
    val xa = f x;
  in
    (if less ((ord_preorder o preorder_order o order_linorder) B_) xa pivot
      then (x :: lts, (eqs, gts))
      else (if less ((ord_preorder o preorder_order o order_linorder) B_) pivot
                 xa
             then (lts, (eqs, x :: gts)) else (lts, (x :: eqs, gts))))
  end
  | part B_ f pivot [] = ([], ([], []));

fun sort_key B_ f xs =
  (case xs of [] => [] | [_] => xs
    | [x, y] =>
      (if less_eq ((ord_preorder o preorder_order o order_linorder) B_) (f x)
            (f y)
        then xs else [y, x])
    | _ :: _ :: _ :: _ =>
      let
        val (lts, (eqs, gts)) =
          part B_ f
            (f (nth xs
                 (divide_nat (size_list xs) (nat_of_integer (2 : IntInf.int)))))
            xs;
      in
        sort_key B_ f lts @ eqs @ sort_key B_ f gts
      end);

fun heap_WHILET b f s =
  (fn f_ => fn () => f_ ((b s) ()) ())
    (fn bv =>
      (if bv then (fn f_ => fn () => f_ ((f s) ()) ()) (heap_WHILET b f)
        else (fn () => s)));

fun minus_set A_ a (Coset xs) = Set (filter (fn x => member A_ x a) xs)
  | minus_set A_ a (Set xs) = fold (remove A_) xs a;

fun gi_V0 (Gen_g_impl_ext (gi_V, gi_E, gi_V0, more)) = gi_V0;

fun select_edge_tr (A1_, A2_) s =
  let
    val (a, (aa, (ab, bb))) = s;
  in
    (if as_is_empty bb then (NONE, (a, (aa, (ab, bb))))
      else let
             val (ac, bc) = as_top bb;
           in
             (if less_eq_nat (as_get aa (minus_nat (as_length aa) one_nata)) ac
               then let
                      val xa = gen_pick (fn x => foldli (id x)) bc;
                      val xb = glist_delete (eq A1_) xa bc;
                      val xc =
                        (if is_Nil xb then as_pop bb
                          else as_set bb (minus_nat (as_length bb) one_nata)
                                 (ac, xb));
                    in
                      (SOME xa, (a, (aa, (ab, xc))))
                    end
               else (NONE, (a, (aa, (ab, bb)))))
           end)
  end;

fun ahm_lookup_aux eq bhc k a =
  list_map_lookup eq k (array_get a (bhc (array_length a) k));

fun ahm_lookup eq bhc k (HashMap (a, uu)) = ahm_lookup_aux eq bhc k a;

fun idx_of_tr (A1_, A2_) s v =
  let
    val (_, (aa, (ab, _))) = v;
    val x = let
              val SOME i = ahm_lookup (eq A1_) (bounded_hashcode_nat A2_) s ab;
              val true = less_eq_int zero_inta i;
            in
              nat i
            end;
    val xa = find_max_nat (as_length aa) (fn j => less_eq_nat (as_get aa j) x);
  in
    xa
  end;

fun collapse_tr (A1_, A2_) v s =
  let
    val (a, (aa, (ab, bb))) = s;
    val x = idx_of_tr (A1_, A2_) v (a, (aa, (ab, bb)));
    val xa = as_take (plus_nata x one_nata) aa;
  in
    (a, (xa, (ab, bb)))
  end;

fun as_singleton B_ x = (FArray.IsabelleMapping.array_of_list [x], one B_);

fun new_hashmap_with size = HashMap (new_array [] size, zero_nata);

fun ahm_empty def_size = new_hashmap_with def_size;

fun push_code (A1_, A2_) g_impl =
  (fn x => fn (xa, (xb, (xc, xd))) =>
    let
      val _ = (fn x => ()) ();
      val y_a = as_length xa;
      val y_b = as_push xa x;
      val y_c = as_push xb y_a;
      val y_d =
        ahm_update (eq A1_) (bounded_hashcode_nat A2_) x (int_of_nat y_a) xc;
      val y_e =
        (if is_Nil (gi_E g_impl x) then xd
          else as_push xd (y_a, gi_E g_impl x));
    in
      (y_b, (y_c, (y_d, y_e)))
    end);

fun compute_SCC_tr (A1_, A2_) g =
  let
    val _ = (fn x => ()) ();
    val xa = ([], ahm_empty (def_hashmap_size A2_ Type));
    val a =
      foldli (id (gi_V0 g)) (fn _ => true)
        (fn xb => fn (a, b) =>
          (if not (case ahm_lookup (eq A1_) (bounded_hashcode_nat A2_) xb b
                    of NONE => false
                    | SOME i =>
                      (if less_eq_int zero_inta i then false else true))
            then let
                   val xc =
                     (a, (as_singleton one_nat xb,
                           (as_singleton one_nat zero_nata,
                             (ahm_update (eq A1_) (bounded_hashcode_nat A2_) xb
                                (int_of_nat zero_nata) b,
                               (if is_Nil (gi_E g xb) then as_empty zero_nat ()
                                 else as_singleton one_nat
(zero_nata, gi_E g xb))))));
                   val (aa, (_, (_, (ad, _)))) =
                     whilea
                       (fn (_, xf) =>
                         not (as_is_empty let
    val (xg, (_, (_, _))) = xf;
  in
    xg
  end))
                       (fn (aa, ba) =>
                         (case select_edge_tr (A1_, A2_) ba
                           of (NONE, bb) => let
      val xf = last_seg_tr A2_ bb;
      val xg = pop_tr (A1_, A2_) bb;
      val xh = xf :: aa;
    in
      (xh, xg)
    end
                           | (SOME xf, bb) =>
                             (if (case ahm_lookup (eq A1_)
 (bounded_hashcode_nat A2_) xf let
                                 val (_, (_, (xl, _))) = bb;
                               in
                                 xl
                               end
                                   of NONE => false
                                   | SOME i =>
                                     (if less_eq_int zero_inta i then true
                                       else false))
                               then let
                                      val ab = collapse_tr (A1_, A2_) xf bb;
                                    in
                                      (aa, ab)
                                    end
                               else (if not
  (case ahm_lookup (eq A1_) (bounded_hashcode_nat A2_) xf
          let
            val (_, (_, (xl, _))) = bb;
          in
            xl
          end
    of NONE => false
    | SOME i => (if less_eq_int zero_inta i then false else true))
                                      then (aa, push_code (A1_, A2_) g xf bb)
                                      else (aa, bb)))))
                       xc;
                 in
                   (aa, ad)
                 end
            else (a, b)))
        xa;
    val (aa, _) = a;
    val _ = (fn x => ()) ();
  in
    aa
  end;

fun constraint_clk (LT (c, uu)) = c
  | constraint_clk (LE (c, uv)) = c
  | constraint_clk (EQ (c, uw)) = c
  | constraint_clk (GE (c, ux)) = c
  | constraint_clk (GT (c, uy)) = c;

fun start_timer_impl x =
  ((fn a => (fn () => a)) o (fn a => Timing.start_timer a)) x;

fun neg_dbm_entry_int (Le a) = Lt (uminus_inta a)
  | neg_dbm_entry_int (Lt a) = Le (uminus_inta a)
  | neg_dbm_entry_int INF = INF;

fun and_entry_repair_impl x =
  (fn n => fn ai => fn bib => fn bia => fn bi =>
    (fn f_ => fn () => f_ ((and_entry_impl n ai bib bia bi) ()) ())
      (fn xa => repair_pair_impl_int n xa ai bib))
    x;

fun upd_entry_impl_int x =
  (fn n => fn ai => fn bib => fn bia => fn bi =>
    (fn f_ => fn () => f_
      ((mtx_get (heap_DBMEntry heap_int) (suc n) bi (ai, bib)) ()) ())
      (fn xa =>
        (fn f_ => fn () => f_ ((amtx_copy (heap_DBMEntry heap_int) bia) ()) ())
          (and_entry_repair_impl n bib ai (neg_dbm_entry_int xa))))
    x;

fun upd_entries_impl x =
  (fn n => fn ai => fn bib => fn bia => fn bi =>
    (fn f_ => fn () => f_
      ((imp_nfoldli bi (fn _ => (fn () => true))
         (fn xa => fn sigma =>
           (fn f_ => fn () => f_ ((upd_entry_impl_int n ai bib xa bia) ()) ())
             (fn x_b => (fn () => (x_b :: sigma))))
         op_list_empty)
      ()) ())
      (fn xa =>
        imp_nfoldli xa (fn _ => (fn () => true))
          (fn xb => fn sigma => (fn () => (xb :: sigma))) op_list_empty))
    x;

fun constraint_pair (LT (x, m)) = (x, m)
  | constraint_pair (LE (x, m)) = (x, m)
  | constraint_pair (EQ (x, m)) = (x, m)
  | constraint_pair (GE (x, m)) = (x, m)
  | constraint_pair (GT (x, m)) = (x, m);

fun maxa A_ (Set (x :: xs)) =
  fold (max ((ord_preorder o preorder_order o order_linorder) A_)) xs x;

fun dbm_lt_0 INF = false
  | dbm_lt_0 (Lt x) = less_eq_int x zero_inta
  | dbm_lt_0 (Le x) = less_int x zero_inta;

fun imp_for_int i u c f s =
  imp_for_inner (integer_of_nat i) (integer_of_nat u) c (f o nat_of_integer) s;

fun check_diag_impl_inta x =
  (fn n => fn ai => fn bi =>
    imp_for_int zero_nata (suc ai) (fn sigma => (fn () => (not sigma)))
      (fn xb => fn sigma =>
        (fn f_ => fn () => f_
          ((mtx_get (heap_DBMEntry heap_int) (suc n) bi (xb, xb)) ()) ())
          (fn xa => (fn () => (dbm_lt_0 xa orelse sigma))))
      false)
    x;

fun dbm_le_int (Lt a) (Lt b) = less_eq_int a b
  | dbm_le_int (Lt a) (Le b) = less_eq_int a b
  | dbm_le_int (Le a) (Lt b) = less_int a b
  | dbm_le_int (Le a) (Le b) = less_eq_int a b
  | dbm_le_int uu INF = true
  | dbm_le_int INF (Le v) = false
  | dbm_le_int INF (Lt v) = false;

fun dbm_subset_impl_inta x =
  (fn m => fn a => fn b =>
    imp_for_int zero_nata
      (times_nata (plus_nata m one_nata) (plus_nata m one_nata))
      (fn aa => (fn () => aa))
      (fn i => fn _ =>
        (fn f_ => fn () => f_ ((ntha (heap_DBMEntry heap_int) a i) ()) ())
          (fn xa =>
            (fn f_ => fn () => f_ ((ntha (heap_DBMEntry heap_int) b i) ()) ())
              (fn y => (fn () => (dbm_le_int xa y)))))
      true)
    x;

fun get_entries_impl_int x =
  (fn n => fn xi =>
    (fn f_ => fn () => f_
      ((imp_for_inta zero_nata (suc n)
         (fn xc => fn sigma =>
           (fn f_ => fn () => f_
             ((imp_for_inta zero_nata (suc n)
                (fn xf => fn sigmaa =>
                  (fn f_ => fn () => f_
                    ((mtx_get (heap_DBMEntry heap_int) (suc n) xi (xc, xf)) ())
                    ())
                    (fn xa =>
                      (fn () =>
                        ((if (less_nat zero_nata xc orelse
                               less_nat zero_nata xf) andalso
                               (less_eq_nat xc n andalso
                                 (less_eq_nat xf n andalso
                                   not (equal_DBMEntry equal_int xa INF)))
                           then op_list_prepend (xc, xf) op_list_empty
                           else op_list_empty) ::
                          sigmaa))))
                op_list_empty)
             ()) ())
             (fn xa =>
               (fn f_ => fn () => f_
                 ((imp_nfoldli (op_list_rev (op_list_rev xa))
                    (fn _ => (fn () => true))
                    (fn xf => fn sigmaa => (fn () => (xf @ sigmaa)))
                    op_list_empty)
                 ()) ())
                 (fn x_c => (fn () => (x_c :: sigma)))))
         op_list_empty)
      ()) ())
      (fn xa =>
        imp_nfoldli (op_list_rev (op_list_rev xa)) (fn _ => (fn () => true))
          (fn xc => fn sigma => (fn () => (xc @ sigma))) op_list_empty))
    x;

fun dbm_minus_canonical_impl x =
  (fn n => fn ai => fn bi =>
    (fn f_ => fn () => f_ ((get_entries_impl_int n bi) ()) ())
      (fn xa =>
        (fn f_ => fn () => f_
          ((imp_nfoldli xa (fn _ => (fn () => true))
             (fn xb => fn sigma =>
               (fn f_ => fn () => f_
                 ((upd_entries_impl n (fst xb) (snd xb) bi ai) ()) ())
                 (fn xc =>
                   (fn f_ => fn () => f_
                     ((imp_nfoldli xc (fn _ => (fn () => true))
                        (fn xe => fn sigmaa => (fn () => (xe :: sigmaa)))
                        op_list_empty)
                     ()) ())
                     (fn x_c => (fn () => (x_c @ sigma)))))
             op_list_empty)
          ()) ())
          (fn xb =>
            (fn f_ => fn () => f_
              ((imp_nfoldli xb (fn _ => (fn () => true))
                 (fn xba => fn sigma => (fn () => (xba :: sigma)))
                 op_list_empty)
              ()) ())
              (fn xc =>
                (fn f_ => fn () => f_
                  ((imp_nfoldli xc (fn _ => (fn () => true))
                     (fn xba => fn sigma =>
                       (fn f_ => fn () => f_ ((check_diag_impl_inta n n xba) ())
                         ())
                         (fn xd =>
                           (fn () =>
                             (if not xd then op_list_prepend xba sigma
                               else sigma))))
                     op_list_empty)
                  ()) ())
                  (fn xd =>
                    imp_nfoldli xd (fn _ => (fn () => true))
                      (fn xba => fn sigma => (fn () => (xba :: sigma)))
                      op_list_empty)))))
    x;

fun dbm_subset_fed_impl n =
  (fn ai => fn bi =>
    (fn f_ => fn () => f_
      ((imp_nfoldli bi (fn _ => (fn () => true))
         (fn xa => fn sigma =>
           (fn f_ => fn () => f_ ((check_diag_impl_inta n n xa) ()) ())
             (fn x =>
               (fn () => (if not x then op_list_prepend xa sigma else sigma))))
         op_list_empty)
      ()) ())
      (fn x =>
        let
          val xa = op_list_rev x;
        in
          (if op_list_is_empty xa then check_diag_impl_inta n n ai
            else (fn f_ => fn () => f_
                   ((imp_nfoldli xa (fn sigma => (fn () => (not sigma)))
                      (fn xc => fn sigma =>
                        (fn f_ => fn () => f_ ((dbm_subset_impl_inta n ai xc)
                          ()) ())
                          (fn x_d => (fn () => (if x_d then true else sigma))))
                      false)
                   ()) ())
                   (fn x_b =>
                     (if x_b then (fn () => true)
                       else (fn f_ => fn () => f_
                              ((imp_nfoldli xa (fn _ => (fn () => true))
                                 (fn xd => fn sigma =>
                                   dbm_minus_canonical_impl n sigma xd)
                                 (op_list_prepend ai op_list_empty))
                              ()) ())
                              (fn x_c => (fn () => (op_list_is_empty x_c))))))
        end));

fun pre_reset_list_impl n =
  (fn ai => fn bi =>
    imp_nfoldli bi (fn _ => (fn () => true))
      (fn x => fn sigma => pre_reset_impl n sigma x) ai);

fun is_result (Result x1) = true
  | is_result (Error x2) = false;

fun tk_div x =
  gen_token lx_ws
    (exactly (equal_char, show_char)
      [Chara (true, true, true, true, false, true, false, false)])
    x;

fun tk_plus x =
  gen_token lx_ws
    (exactly (equal_char, show_char)
      [Chara (true, true, false, true, false, true, false, false)])
    x;

fun collect_clock_pairs cc = image constraint_pair (Set cc);

fun tk_minus x =
  gen_token lx_ws
    (exactly (equal_char, show_char)
      [Chara (true, false, true, true, false, true, false, false)])
    x;

fun tk_times x =
  gen_token lx_ws
    (exactly (equal_char, show_char)
      [Chara (false, true, false, true, false, true, false, false)])
    x;

fun map_exp f (Const x1) = Const x1
  | map_exp f (Var x2) = Var (f x2)
  | map_exp f (If_then_else (x31, x32, x33)) =
    If_then_else (map_bexp f x31, map_exp f x32, map_exp f x33)
  | map_exp f (Binop (x41, x42, x43)) =
    Binop (x41, map_exp f x42, map_exp f x43)
  | map_exp f (Unop (x51, x52)) = Unop (x51, map_exp f x52)
and map_bexp f True = True
  | map_bexp f (Not x2) = Not (map_bexp f x2)
  | map_bexp f (And (x31, x32)) = And (map_bexp f x31, map_bexp f x32)
  | map_bexp f (Or (x41, x42)) = Or (map_bexp f x41, map_bexp f x42)
  | map_bexp f (Imply (x51, x52)) = Imply (map_bexp f x51, map_bexp f x52)
  | map_bexp f (Eq (x61, x62)) = Eq (map_exp f x61, map_exp f x62)
  | map_bexp f (Lea (x71, x72)) = Lea (map_exp f x71, map_exp f x72)
  | map_bexp f (Lta (x81, x82)) = Lta (map_exp f x81, map_exp f x82)
  | map_bexp f (Ge (x91, x92)) = Ge (map_exp f x91, map_exp f x92)
  | map_bexp f (Gt (x101, x102)) = Gt (map_exp f x101, map_exp f x102);

fun set_exp A_ (Const x1) = bot_set
  | set_exp A_ (Var x2) = insert A_ x2 bot_set
  | set_exp A_ (If_then_else (x31, x32, x33)) =
    sup_set A_ (sup_set A_ (set_bexp A_ x31) (set_exp A_ x32)) (set_exp A_ x33)
  | set_exp A_ (Binop (x41, x42, x43)) =
    sup_set A_ (set_exp A_ x42) (set_exp A_ x43)
  | set_exp A_ (Unop (x51, x52)) = set_exp A_ x52
and set_bexp A_ True = bot_set
  | set_bexp A_ (Not x2) = set_bexp A_ x2
  | set_bexp A_ (And (x31, x32)) =
    sup_set A_ (set_bexp A_ x31) (set_bexp A_ x32)
  | set_bexp A_ (Or (x41, x42)) = sup_set A_ (set_bexp A_ x41) (set_bexp A_ x42)
  | set_bexp A_ (Imply (x51, x52)) =
    sup_set A_ (set_bexp A_ x51) (set_bexp A_ x52)
  | set_bexp A_ (Eq (x61, x62)) = sup_set A_ (set_exp A_ x61) (set_exp A_ x62)
  | set_bexp A_ (Lea (x71, x72)) = sup_set A_ (set_exp A_ x71) (set_exp A_ x72)
  | set_bexp A_ (Lta (x81, x82)) = sup_set A_ (set_exp A_ x81) (set_exp A_ x82)
  | set_bexp A_ (Ge (x91, x92)) = sup_set A_ (set_exp A_ x91) (set_exp A_ x92)
  | set_bexp A_ (Gt (x101, x102)) =
    sup_set A_ (set_exp A_ x101) (set_exp A_ x102);

fun list_of_map_impl (A1_, A2_, A3_) B_ =
  (fn xi =>
    (fn f_ => fn () => f_
      ((heap_WHILET
         (fn (_, a2) =>
           (fn f_ => fn () => f_ ((hm_isEmpty a2) ()) ())
             (fn x_a => (fn () => (not x_a))))
         (fn (a1, a2) =>
           (fn f_ => fn () => f_ ((hm_it_next_key (A2_, A3_) B_ a2) ()) ())
             (fn x_a =>
               (fn f_ => fn () => f_
                 ((hms_extract (ht_lookup (A1_, A2_, A3_) B_)
                    (ht_delete (A1_, A2_, A3_) B_) x_a a2)
                 ()) ())
                 (fn (a1a, b) => (fn () => ((x_a, the a1a) :: a1, b)))))
         ([], xi))
      ()) ())
      (fn (a1, _) => (fn () => a1)));

fun tk_lparen x =
  gen_token lx_ws
    (exactly (equal_char, show_char)
      [Chara (false, false, false, true, false, true, false, false)])
    x;

fun tk_rparen x =
  gen_token lx_ws
    (exactly (equal_char, show_char)
      [Chara (true, false, false, true, false, true, false, false)])
    x;

fun sum_list A_ xs =
  foldr (plus ((plus_semigroup_add o semigroup_add_monoid_add) A_)) xs
    (zero (zero_monoid_add A_));

fun heap_map copy xs =
  (fn f_ => fn () => f_
    ((imp_nfoldli xs (fn _ => (fn () => true))
       (fn x => fn xsa =>
         (fn f_ => fn () => f_ ((copy x) ()) ())
           (fn xa => (fn () => (xa :: xsa))))
       [])
    ()) ())
    (fn xsa => (fn () => (rev xsa)));

fun sup_seta A_ (Set xs) = fold (sup_set A_) xs bot_set;

fun geta A_ m x =
  (case m x
    of NONE =>
      Error ["(Get) key not found: " ^ implode (shows_prec A_ zero_nata x [])]
    | SOME a => Result a);

fun norm_upd_impl (A1_, A2_) n =
  (fn ai => fn bia => fn bi =>
    (fn f_ => fn () => f_
      ((mtx_get (heap_DBMEntry A2_) (suc n) ai (zero_nata, zero_nata)) ()) ())
      (fn x =>
        (fn f_ => fn () => f_
          ((mtx_set (heap_DBMEntry A2_) (suc n) ai (zero_nata, zero_nata)
             (norm_lower
               ((linorder_linordered_ab_semigroup_add o
                  linordered_ab_semigroup_add_linordered_ab_monoid_add o
                  linordered_ab_monoid_add_linordered_cancel_ab_monoid_add o
                  linordered_cancel_ab_monoid_add_linordered_ab_group_add)
                 A1_)
               (norm_upper
                 ((linorder_linordered_ab_semigroup_add o
                    linordered_ab_semigroup_add_linordered_ab_monoid_add o
                    linordered_ab_monoid_add_linordered_cancel_ab_monoid_add o
                    linordered_cancel_ab_monoid_add_linordered_ab_group_add)
                   A1_)
                 x (zero ((zero_monoid_add o monoid_add_group_add o
                            group_add_ab_group_add o
                            ab_group_add_ordered_ab_group_add o
                            ordered_ab_group_add_linordered_ab_group_add)
                           A1_)))
               (zero ((zero_monoid_add o monoid_add_group_add o
                        group_add_ab_group_add o
                        ab_group_add_ordered_ab_group_add o
                        ordered_ab_group_add_linordered_ab_group_add)
                       A1_))))
          ()) ())
          (fn xa =>
            (fn f_ => fn () => f_
              ((imp_for_inta one_nata (suc bi)
                 (fn xc => fn sigma =>
                   (fn f_ => fn () => f_
                     ((mtx_get (heap_DBMEntry A2_) (suc n) sigma
                        (zero_nata, xc))
                     ()) ())
                     (fn xb =>
                       mtx_set (heap_DBMEntry A2_) (suc n) sigma (zero_nata, xc)
                         (norm_lower
                           ((linorder_linordered_ab_semigroup_add o
                              linordered_ab_semigroup_add_linordered_ab_monoid_add o
                              linordered_ab_monoid_add_linordered_cancel_ab_monoid_add o
                              linordered_cancel_ab_monoid_add_linordered_ab_group_add)
                             A1_)
                           (norm_upper
                             ((linorder_linordered_ab_semigroup_add o
                                linordered_ab_semigroup_add_linordered_ab_monoid_add o
                                linordered_ab_monoid_add_linordered_cancel_ab_monoid_add o
                                linordered_cancel_ab_monoid_add_linordered_ab_group_add)
                               A1_)
                             xb (zero ((zero_monoid_add o monoid_add_group_add o
 group_add_ab_group_add o ab_group_add_ordered_ab_group_add o
 ordered_ab_group_add_linordered_ab_group_add)
A1_)))
                           (uminus
                             ((uminus_group_add o group_add_ab_group_add o
                                ab_group_add_ordered_ab_group_add o
                                ordered_ab_group_add_linordered_ab_group_add)
                               A1_)
                             (sub bia xc)))))
                 xa)
              ()) ())
              (imp_for_inta one_nata (suc bi)
                (fn xb => fn sigma =>
                  (fn f_ => fn () => f_
                    ((mtx_get (heap_DBMEntry A2_) (suc n) sigma (xb, zero_nata))
                    ()) ())
                    (fn xc =>
                      (fn f_ => fn () => f_
                        ((mtx_set (heap_DBMEntry A2_) (suc n) sigma
                           (xb, zero_nata)
                           (norm_lower
                             ((linorder_linordered_ab_semigroup_add o
                                linordered_ab_semigroup_add_linordered_ab_monoid_add o
                                linordered_ab_monoid_add_linordered_cancel_ab_monoid_add o
                                linordered_cancel_ab_monoid_add_linordered_ab_group_add)
                               A1_)
                             (norm_upper
                               ((linorder_linordered_ab_semigroup_add o
                                  linordered_ab_semigroup_add_linordered_ab_monoid_add o
                                  linordered_ab_monoid_add_linordered_cancel_ab_monoid_add o
                                  linordered_cancel_ab_monoid_add_linordered_ab_group_add)
                                 A1_)
                               xc (sub bia xb))
                             (zero ((zero_monoid_add o monoid_add_group_add o
                                      group_add_ab_group_add o
                                      ab_group_add_ordered_ab_group_add o
                                      ordered_ab_group_add_linordered_ab_group_add)
                                     A1_))))
                        ()) ())
                        (imp_for_inta one_nata (suc bi)
                          (fn xe => fn sigmaa =>
                            (fn f_ => fn () => f_
                              ((mtx_get (heap_DBMEntry A2_) (suc n) sigmaa
                                 (xb, xe))
                              ()) ())
                              (fn xd =>
                                mtx_set (heap_DBMEntry A2_) (suc n) sigmaa
                                  (xb, xe)
                                  (norm_lower
                                    ((linorder_linordered_ab_semigroup_add o
                                       linordered_ab_semigroup_add_linordered_ab_monoid_add o
                                       linordered_ab_monoid_add_linordered_cancel_ab_monoid_add o
                                       linordered_cancel_ab_monoid_add_linordered_ab_group_add)
                                      A1_)
                                    (norm_upper
                                      ((linorder_linordered_ab_semigroup_add o
 linordered_ab_semigroup_add_linordered_ab_monoid_add o
 linordered_ab_monoid_add_linordered_cancel_ab_monoid_add o
 linordered_cancel_ab_monoid_add_linordered_ab_group_add)
A1_)
                                      xd (sub bia xb))
                                    (uminus
                                      ((uminus_group_add o
 group_add_ab_group_add o ab_group_add_ordered_ab_group_add o
 ordered_ab_group_add_linordered_ab_group_add)
A1_)
                                      (sub bia xe))))))))))));

fun scan_parens lparen rparen inner =
  bindb (gen_token lx_ws (exactly (equal_char, show_char) lparen))
    (fn _ =>
      bindb (gen_token lx_ws inner)
        (fn a =>
          bindb (gen_token lx_ws (exactly (equal_char, show_char) rparen))
            (fn _ => return a)));

fun lx_underscore x =
  bindb (exactly (equal_char, show_char)
          [Chara (true, true, true, true, true, false, true, false)])
    (fn _ => return (Chara (true, true, true, true, true, false, true, false)))
    x;

fun lx_hyphen x =
  bindb (exactly (equal_char, show_char)
          [Chara (true, false, true, true, false, true, false, false)])
    (fn _ =>
      return (Chara (true, false, true, true, false, true, false, false)))
    x;

fun ta_var_ident x =
  bindb (alt (bindb (alt lx_alpha lx_digit) (fn xa => return (sum_join xa)))
          lx_underscore)
    (fn xa =>
      bindb (repeat
              (bindb
                (alt (bindb (alt lx_alpha lx_digit)
                       (fn xb => return (sum_join xb)))
                  (bindb (alt lx_underscore lx_hyphen)
                    (fn xb => return (sum_join xb))))
                (fn xb => return (sum_join xb))))
        (fn xaa =>
          return (uncurry (fn a => fn b => a :: b) (sum_join xa, xaa))))
    x;

fun scan_var x = ta_var_ident x;

fun scan_infix_pair a b s =
  bindb (gen_token lx_ws a)
    (fn aa =>
      bindb (gen_token lx_ws (exactly (equal_char, show_char) s))
        (fn _ => bindb (gen_token lx_ws b) (fn ba => return (aa, ba))));

fun aexp l =
  bindb (alt (bindb (gen_token lx_ws lx_int) (fn x => return (Const x)))
          (bindb
            (alt (bindb (gen_token lx_ws scan_var)
                   (fn x => return ((Var o implode) x)))
              (bindb
                (alt (bindb
                       (scan_parens
                         [Chara (false, false, false, true, false, true, false,
                                  false)]
                         [Chara (true, false, false, true, false, true, false,
                                  false)]
                         (bindb (gen_token lx_ws scan_exp)
                           (fn a =>
                             bindb (gen_token lx_ws
                                     (exactly (equal_char, show_char)
                                       [Chara
  (true, true, true, true, true, true, false, false)]))
                               (fn _ =>
                                 bindb (gen_token lx_ws scan_7)
                                   (fn x =>
                                     bindb (gen_token lx_ws
     (exactly (equal_char, show_char)
       [Chara (false, true, false, true, true, true, false, false)]))
                                       (fn _ =>
 bindb scan_exp (fn xa => return (a, (x, xa)))))))))
                       (fn x => return let
 val (e1, a) = x;
 val (b, aa) = a;
                                       in
 If_then_else (b, e1, aa)
                                       end))
                  (bindb (gen_token lx_ws tk_lparen)
                    (fn _ =>
                      bindb (gen_token lx_ws scan_exp)
                        (fn a => bindb tk_rparen (fn _ => return a)))))
                (fn x => return (sum_join x))))
            (fn x => return (sum_join x))))
    (fn x => return (sum_join x)) l
and mexp l =
  chainL1 aexp
    (bindb
      (alt (bindb tk_times (fn _ => return times_int))
        (bindb tk_div (fn _ => return divide_int)))
      (fn x => return (fn a => fn b => Binop (sum_join x, a, b))))
    l
and scan_exp l =
  chainL1 mexp
    (bindb
      (alt (bindb tk_plus (fn _ => return plus_inta))
        (bindb tk_minus (fn _ => return minus_inta)))
      (fn x => return (fn a => fn b => Binop (sum_join x, a, b))))
    l
and scan_0 l =
  bindb (alt (bindb
               (gen_token lx_ws
                 (bindb
                   (alt (exactly (equal_char, show_char)
                          [Chara (false, true, true, true, true, true, true,
                                   false)])
                     (exactly (equal_char, show_char)
                       [Chara (true, false, false, false, false, true, false,
                                false)]))
                   (fn x => return (sum_join x))))
               (fn _ =>
                 bindb (scan_parens
                         [Chara (false, false, false, true, false, true, false,
                                  false)]
                         [Chara (true, false, false, true, false, true, false,
                                  false)]
                         scan_7)
                   (fn x => return (Not x))))
          (bindb
            (alt (bindb
                   (gen_token lx_ws
                     (exactly (equal_char, show_char)
                       [Chara (false, false, true, false, true, true, true,
                                false),
                         Chara (false, true, false, false, true, true, true,
                                 false),
                         Chara (true, false, true, false, true, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false)]))
                   (fn _ => return True))
              (bindb
                (alt (bindb
                       (scan_infix_pair aexp aexp
                         [Chara (false, false, true, true, true, true, false,
                                  false),
                           Chara (true, false, true, true, true, true, false,
                                   false)])
                       (fn x =>
                         return (uncurry (fn a => fn b => Lea (a, b)) x)))
                  (bindb
                    (alt (bindb
                           (scan_infix_pair aexp aexp
                             [Chara (false, false, true, true, true, true,
                                      false, false)])
                           (fn x =>
                             return (uncurry (fn a => fn b => Lta (a, b)) x)))
                      (bindb
                        (alt (bindb
                               (scan_infix_pair aexp aexp
                                 [Chara (true, false, true, true, true, true,
  false, false),
                                   Chara (true, false, true, true, true, true,
   false, false)])
                               (fn x =>
                                 return
                                   (uncurry (fn a => fn b => Eq (a, b)) x)))
                          (bindb
                            (alt (bindb
                                   (scan_infix_pair aexp aexp
                                     [Chara
(false, true, true, true, true, true, false, false)])
                                   (fn x =>
                                     return
                                       (uncurry (fn a => fn b => Gt (a, b)) x)))
                              (bindb
                                (alt (bindb
                                       (scan_infix_pair aexp aexp
 [Chara (false, true, true, true, true, true, false, false),
   Chara (true, false, true, true, true, true, false, false)])
                                       (fn x =>
 return (uncurry (fn a => fn b => Ge (a, b)) x)))
                                  (scan_parens
                                    [Chara (false, false, false, true, false,
     true, false, false)]
                                    [Chara (true, false, false, true, false,
     true, false, false)]
                                    scan_7))
                                (fn x => return (sum_join x))))
                            (fn x => return (sum_join x))))
                        (fn x => return (sum_join x))))
                    (fn x => return (sum_join x))))
                (fn x => return (sum_join x))))
            (fn x => return (sum_join x))))
    (fn x => return (sum_join x)) l
and scan_6 l =
  bindb (alt (bindb
               (scan_infix_pair scan_0 scan_6
                 [Chara (false, true, true, false, false, true, false, false),
                   Chara (false, true, true, false, false, true, false, false)])
               (fn x => return (uncurry (fn a => fn b => And (a, b)) x)))
          scan_0)
    (fn x => return (sum_join x)) l
and scan_7 l =
  bindb (alt (bindb
               (scan_infix_pair scan_6 scan_7
                 [Chara (true, false, true, true, false, true, false, false),
                   Chara (false, true, true, true, true, true, false, false)])
               (fn x => return (uncurry (fn a => fn b => Imply (a, b)) x)))
          (bindb
            (alt (bindb
                   (scan_infix_pair scan_6 scan_7
                     [Chara (false, false, true, true, true, true, true, false),
                       Chara (false, false, true, true, true, true, true,
                               false)])
                   (fn x => return (uncurry (fn a => fn b => Or (a, b)) x)))
              scan_6)
            (fn x => return (sum_join x))))
    (fn x => return (sum_join x)) l;

fun vars_of_exp A_ (Const c) = bot_set
  | vars_of_exp A_ (Var x) = insert A_ x bot_set
  | vars_of_exp A_ (If_then_else (b, e1, e2)) =
    sup_set A_ (sup_set A_ (vars_of_bexp A_ b) (vars_of_exp A_ e1))
      (vars_of_exp A_ e2)
  | vars_of_exp A_ (Binop (uu, e1, e2)) =
    sup_set A_ (vars_of_exp A_ e1) (vars_of_exp A_ e2)
  | vars_of_exp A_ (Unop (uv, e)) = vars_of_exp A_ e
and vars_of_bexp A_ (Not e) = vars_of_bexp A_ e
  | vars_of_bexp A_ (And (e1, e2)) =
    sup_set A_ (vars_of_bexp A_ e1) (vars_of_bexp A_ e2)
  | vars_of_bexp A_ (Or (e1, e2)) =
    sup_set A_ (vars_of_bexp A_ e1) (vars_of_bexp A_ e2)
  | vars_of_bexp A_ (Imply (e1, e2)) =
    sup_set A_ (vars_of_bexp A_ e1) (vars_of_bexp A_ e2)
  | vars_of_bexp A_ (Eq (i, x)) =
    sup_set A_ (vars_of_exp A_ i) (vars_of_exp A_ x)
  | vars_of_bexp A_ (Lea (i, x)) =
    sup_set A_ (vars_of_exp A_ i) (vars_of_exp A_ x)
  | vars_of_bexp A_ (Lta (i, x)) =
    sup_set A_ (vars_of_exp A_ i) (vars_of_exp A_ x)
  | vars_of_bexp A_ (Ge (i, x)) =
    sup_set A_ (vars_of_exp A_ i) (vars_of_exp A_ x)
  | vars_of_bexp A_ (Gt (i, x)) =
    sup_set A_ (vars_of_exp A_ i) (vars_of_exp A_ x)
  | vars_of_bexp A_ True = bot_set;

fun print_check s b = writeln (s ^ ": " ^ (if b then "passed" else "failed"));

fun parse parser s =
  (case parse_all lx_ws parser s
    of Inl e =>
      Error [implode
               (e () [Chara (false, false, false, false, true, false, true,
                              false),
                       Chara (true, false, false, false, false, true, true,
                               false),
                       Chara (false, true, false, false, true, true, true,
                               false),
                       Chara (true, true, false, false, true, true, true,
                               false),
                       Chara (true, false, true, false, false, true, true,
                               false),
                       Chara (false, true, false, false, true, true, true,
                               false),
                       Chara (false, true, false, true, true, true, false,
                               false),
                       Chara (false, false, false, false, false, true, false,
                               false)])]
    | Inr a => Result a);

fun bvali (A1_, A2_) s True = true
  | bvali (A1_, A2_) s (Not e) = not (bvali (A1_, A2_) s e)
  | bvali (A1_, A2_) s (And (e1, e2)) =
    bvali (A1_, A2_) s e1 andalso bvali (A1_, A2_) s e2
  | bvali (A1_, A2_) s (Or (e1, e2)) =
    bvali (A1_, A2_) s e1 orelse bvali (A1_, A2_) s e2
  | bvali (A1_, A2_) s (Imply (e1, e2)) =
    (if bvali (A1_, A2_) s e1 then bvali (A1_, A2_) s e2 else true)
  | bvali (A1_, A2_) s (Eq (i, x)) =
    eq A1_ (evali (A1_, A2_) s i) (evali (A1_, A2_) s x)
  | bvali (A1_, A2_) s (Lea (i, x)) =
    less_eq ((ord_preorder o preorder_order o order_linorder) A2_)
      (evali (A1_, A2_) s i) (evali (A1_, A2_) s x)
  | bvali (A1_, A2_) s (Lta (i, x)) =
    less ((ord_preorder o preorder_order o order_linorder) A2_)
      (evali (A1_, A2_) s i) (evali (A1_, A2_) s x)
  | bvali (A1_, A2_) s (Ge (i, x)) =
    less_eq ((ord_preorder o preorder_order o order_linorder) A2_)
      (evali (A1_, A2_) s x) (evali (A1_, A2_) s i)
  | bvali (A1_, A2_) s (Gt (i, x)) =
    less ((ord_preorder o preorder_order o order_linorder) A2_)
      (evali (A1_, A2_) s x) (evali (A1_, A2_) s i)
and evali (A1_, A2_) s (Const c) = c
  | evali (A1_, A2_) s (Var x) = nth s x
  | evali (A1_, A2_) s (If_then_else (b, e1, e2)) =
    (if bvali (A1_, A2_) s b then evali (A1_, A2_) s e1
      else evali (A1_, A2_) s e2)
  | evali (A1_, A2_) s (Binop (f, e1, e2)) =
    f (evali (A1_, A2_) s e1) (evali (A1_, A2_) s e2)
  | evali (A1_, A2_) s (Unop (f, e)) = f (evali (A1_, A2_) s e);

fun map_sexp uu uv uw Truea = Truea
  | map_sexp f g h (Nota e) = Nota (map_sexp f g h e)
  | map_sexp f g h (Anda (e1, e2)) = Anda (map_sexp f g h e1, map_sexp f g h e2)
  | map_sexp f g h (Ora (e1, e2)) = Ora (map_sexp f g h e1, map_sexp f g h e2)
  | map_sexp f g h (Implya (e1, e2)) =
    Implya (map_sexp f g h e1, map_sexp f g h e2)
  | map_sexp f g h (Eqa (i, x)) = Eqa (g i, h x)
  | map_sexp f g h (Ltb (i, x)) = Ltb (g i, h x)
  | map_sexp f g h (Leb (i, x)) = Leb (g i, h x)
  | map_sexp f g h (Gea (i, x)) = Gea (g i, h x)
  | map_sexp f g h (Gta (i, x)) = Gta (g i, h x)
  | map_sexp f g h (Loc (i, x)) = Loc (i, f i x);

fun run_map_heap f xs = Par_List.map ((fn a => (fn f => f ()) a) o f) xs;

fun of_nat json =
  (case json of Object _ => Error ["of_nat: expected natural number"]
    | Arraya _ => Error ["of_nat: expected natural number"]
    | String _ => Error ["of_nat: expected natural number"]
    | Int _ => Error ["of_nat: expected natural number"] | Nata a => Result a
    | Rat _ => Error ["of_nat: expected natural number"]
    | Boolean _ => Error ["of_nat: expected natural number"]
    | Null => Error ["of_nat: expected natural number"]);

fun dbm_subset_impl (A1_, A2_, A3_) n =
  (fn ai => fn bi =>
    imp_for_int zero_nata (suc n) (fn a => (fn () => a))
      (fn xb => fn _ =>
        imp_for_int zero_nata (suc n) (fn a => (fn () => a))
          (fn xe => fn _ =>
            (fn f_ => fn () => f_
              ((mtx_get (heap_DBMEntry A3_) (suc n) ai (xb, xe)) ()) ())
              (fn x_f =>
                (fn f_ => fn () => f_
                  ((mtx_get (heap_DBMEntry A3_) (suc n) bi (xb, xe)) ()) ())
                  (fn x_g =>
                    (fn () =>
                      (less_eq_DBMEntry
                        (A2_, (linorder_linordered_ab_semigroup_add o
                                linordered_ab_semigroup_add_linordered_ab_monoid_add o
                                linordered_ab_monoid_add_linordered_cancel_ab_monoid_add)
                                A1_)
                        x_f x_g)))))
          true)
      true);

fun dbm_to_list_impl (A1_, A2_) n =
  (fn xi =>
    (fn f_ => fn () => f_
      ((imp_for_inta zero_nata (suc n)
         (fn xc =>
           imp_for_inta zero_nata (suc n)
             (fn xe => fn sigma =>
               (fn f_ => fn () => f_ ((mtx_get A2_ (suc n) xi (xc, xe)) ()) ())
                 (fn x_e => (fn () => (x_e :: sigma)))))
         [])
      ()) ())
      (fn x => (fn () => (op_list_rev x))));

fun map_sexpa f1 f2 f3 f4 Truea = Truea
  | map_sexpa f1 f2 f3 f4 (Nota x2) = Nota (map_sexpa f1 f2 f3 f4 x2)
  | map_sexpa f1 f2 f3 f4 (Anda (x31, x32)) =
    Anda (map_sexpa f1 f2 f3 f4 x31, map_sexpa f1 f2 f3 f4 x32)
  | map_sexpa f1 f2 f3 f4 (Ora (x41, x42)) =
    Ora (map_sexpa f1 f2 f3 f4 x41, map_sexpa f1 f2 f3 f4 x42)
  | map_sexpa f1 f2 f3 f4 (Implya (x51, x52)) =
    Implya (map_sexpa f1 f2 f3 f4 x51, map_sexpa f1 f2 f3 f4 x52)
  | map_sexpa f1 f2 f3 f4 (Eqa (x61, x62)) = Eqa (f3 x61, f4 x62)
  | map_sexpa f1 f2 f3 f4 (Leb (x71, x72)) = Leb (f3 x71, f4 x72)
  | map_sexpa f1 f2 f3 f4 (Ltb (x81, x82)) = Ltb (f3 x81, f4 x82)
  | map_sexpa f1 f2 f3 f4 (Gea (x91, x92)) = Gea (f3 x91, f4 x92)
  | map_sexpa f1 f2 f3 f4 (Gta (x101, x102)) = Gta (f3 x101, f4 x102)
  | map_sexpa f1 f2 f3 f4 (Loc (x111, x112)) = Loc (f1 x111, f2 x112);

fun map_formulaa f1 f2 f3 f4 (EX x1) = EX (map_sexpa f1 f2 f3 f4 x1)
  | map_formulaa f1 f2 f3 f4 (EG x2) = EG (map_sexpa f1 f2 f3 f4 x2)
  | map_formulaa f1 f2 f3 f4 (AX x3) = AX (map_sexpa f1 f2 f3 f4 x3)
  | map_formulaa f1 f2 f3 f4 (AG x4) = AG (map_sexpa f1 f2 f3 f4 x4)
  | map_formulaa f1 f2 f3 f4 (Leadsto (x51, x52)) =
    Leadsto (map_sexpa f1 f2 f3 f4 x51, map_sexpa f1 f2 f3 f4 x52);

fun rename_locs_sexp f (Nota a) =
  binda (rename_locs_sexp f a) (fn aa => Result (Nota aa))
  | rename_locs_sexp f (Implya (a, b)) =
    binda (rename_locs_sexp f a)
      (fn aa =>
        binda (rename_locs_sexp f b) (fn ba => Result (Implya (aa, ba))))
  | rename_locs_sexp f (Ora (a, b)) =
    binda (rename_locs_sexp f a)
      (fn aa => binda (rename_locs_sexp f b) (fn ba => Result (Ora (aa, ba))))
  | rename_locs_sexp f (Anda (a, b)) =
    binda (rename_locs_sexp f a)
      (fn aa => binda (rename_locs_sexp f b) (fn ba => Result (Anda (aa, ba))))
  | rename_locs_sexp f (Loc (n, x)) =
    binda (f n x) (fn xa => Result (Loc (n, xa)))
  | rename_locs_sexp f (Eqa (a, b)) = Result (Eqa (a, b))
  | rename_locs_sexp f (Ltb (a, b)) = Result (Ltb (a, b))
  | rename_locs_sexp f (Leb (a, b)) = Result (Leb (a, b))
  | rename_locs_sexp f (Gea (a, b)) = Result (Gea (a, b))
  | rename_locs_sexp f (Gta (a, b)) = Result (Gta (a, b));

fun rename_locs_formula f (EX phi) =
  binda (rename_locs_sexp f phi) (Result o EX)
  | rename_locs_formula f (EG phi) =
    binda (rename_locs_sexp f phi) (Result o EG)
  | rename_locs_formula f (AX phi) =
    binda (rename_locs_sexp f phi) (Result o AX)
  | rename_locs_formula f (AG phi) =
    binda (rename_locs_sexp f phi) (Result o AG)
  | rename_locs_formula f (Leadsto (phi, psi)) =
    binda (rename_locs_sexp f phi)
      (fn phia =>
        binda (rename_locs_sexp f psi)
          (fn psia => Result (Leadsto (phia, psia))));

fun locs_of_sexp A_ (Nota e) = locs_of_sexp A_ e
  | locs_of_sexp A_ (Anda (e1, e2)) =
    sup_set A_ (locs_of_sexp A_ e1) (locs_of_sexp A_ e2)
  | locs_of_sexp A_ (Ora (e1, e2)) =
    sup_set A_ (locs_of_sexp A_ e1) (locs_of_sexp A_ e2)
  | locs_of_sexp A_ (Implya (e1, e2)) =
    sup_set A_ (locs_of_sexp A_ e1) (locs_of_sexp A_ e2)
  | locs_of_sexp A_ (Loc (i, x)) = insert A_ i bot_set
  | locs_of_sexp A_ Truea = bot_set
  | locs_of_sexp A_ (Eqa (v, va)) = bot_set
  | locs_of_sexp A_ (Leb (v, va)) = bot_set
  | locs_of_sexp A_ (Ltb (v, va)) = bot_set
  | locs_of_sexp A_ (Gea (v, va)) = bot_set
  | locs_of_sexp A_ (Gta (v, va)) = bot_set;

fun locs_of_formula A_ (EX phi) = locs_of_sexp A_ phi
  | locs_of_formula A_ (EG phi) = locs_of_sexp A_ phi
  | locs_of_formula A_ (AX phi) = locs_of_sexp A_ phi
  | locs_of_formula A_ (AG phi) = locs_of_sexp A_ phi
  | locs_of_formula A_ (Leadsto (phi, psi)) =
    sup_set A_ (locs_of_sexp A_ phi) (locs_of_sexp A_ psi);

fun sexp_to_acconstraint (Ltb (a, b)) = LT (a, b)
  | sexp_to_acconstraint (Leb (a, b)) = LE (a, b)
  | sexp_to_acconstraint (Eqa (a, b)) = EQ (a, b)
  | sexp_to_acconstraint (Gea (a, b)) = GE (a, b)
  | sexp_to_acconstraint (Gta (a, b)) = GT (a, b);

fun sexp_to_bexp (Ltb (a, b)) = Result (Lta (Var a, Const b))
  | sexp_to_bexp (Leb (a, b)) = Result (Lea (Var a, Const b))
  | sexp_to_bexp (Eqa (a, b)) = Result (Eq (Var a, Const b))
  | sexp_to_bexp (Gea (a, b)) = Result (Ge (Var a, Const b))
  | sexp_to_bexp (Gta (a, b)) = Result (Gt (Var a, Const b))
  | sexp_to_bexp (Anda (a, b)) =
    binda (sexp_to_bexp a)
      (fn aa => binda (sexp_to_bexp b) (fn ba => Result (And (aa, ba))))
  | sexp_to_bexp (Ora (a, b)) =
    binda (sexp_to_bexp a)
      (fn aa => binda (sexp_to_bexp b) (fn ba => Result (Or (aa, ba))))
  | sexp_to_bexp (Implya (a, b)) =
    binda (sexp_to_bexp a)
      (fn aa => binda (sexp_to_bexp b) (fn ba => Result (Imply (aa, ba))))
  | sexp_to_bexp Truea = Error ["Illegal construct in binary operation"]
  | sexp_to_bexp (Nota v) = Error ["Illegal construct in binary operation"]
  | sexp_to_bexp (Loc (v, va)) =
    Error ["Illegal construct in binary operation"];

fun chop_sexp A_ clocks (Anda (a, b)) (cs, es) =
  chop_sexp A_ clocks b (chop_sexp A_ clocks a (cs, es))
  | chop_sexp A_ clocks (Eqa (a, b)) (cs, es) =
    (if membera A_ clocks a then (Eqa (a, b) :: cs, es)
      else (cs, Eqa (a, b) :: es))
  | chop_sexp A_ clocks (Leb (a, b)) (cs, es) =
    (if membera A_ clocks a then (Leb (a, b) :: cs, es)
      else (cs, Leb (a, b) :: es))
  | chop_sexp A_ clocks (Ltb (a, b)) (cs, es) =
    (if membera A_ clocks a then (Ltb (a, b) :: cs, es)
      else (cs, Ltb (a, b) :: es))
  | chop_sexp A_ clocks (Gea (a, b)) (cs, es) =
    (if membera A_ clocks a then (Gea (a, b) :: cs, es)
      else (cs, Gea (a, b) :: es))
  | chop_sexp A_ clocks (Gta (a, b)) (cs, es) =
    (if membera A_ clocks a then (Gta (a, b) :: cs, es)
      else (cs, Gta (a, b) :: es))
  | chop_sexp A_ clocks Truea (cs, es) = (cs, Truea :: es)
  | chop_sexp A_ clocks (Nota v) (cs, es) = (cs, Nota v :: es)
  | chop_sexp A_ clocks (Ora (v, va)) (cs, es) = (cs, Ora (v, va) :: es)
  | chop_sexp A_ clocks (Implya (v, va)) (cs, es) = (cs, Implya (v, va) :: es)
  | chop_sexp A_ clocks (Loc (v, va)) (cs, es) = (cs, Loc (v, va) :: es);

fun compile_invariant clocks vars inv =
  let
    val (cs, es) = chop_sexp equal_literal clocks inv ([], []);
    val g = map sexp_to_acconstraint cs;
  in
    (if null es then Result (g, True)
      else let
             val e = fold (fn a => fn b => Anda (a, b)) (tl es) (hd es);
           in
             binda (sexp_to_bexp e)
               (fn b =>
                 binda (assert
                         (subset (card_UNIV_literal, equal_literal)
                           (set_bexp equal_literal b) (Set vars))
                         (implode
                           ([Chara (true, false, true, false, true, false, true,
                                     false),
                              Chara (false, true, true, true, false, true, true,
                                      false),
                              Chara (true, true, false, true, false, true, true,
                                      false),
                              Chara (false, true, true, true, false, true, true,
                                      false),
                              Chara (true, true, true, true, false, true, true,
                                      false),
                              Chara (true, true, true, false, true, true, true,
                                      false),
                              Chara (false, true, true, true, false, true, true,
                                      false),
                              Chara (false, false, false, false, false, true,
                                      false, false),
                              Chara (false, true, true, false, true, true, true,
                                      false),
                              Chara (true, false, false, false, false, true,
                                      true, false),
                              Chara (false, true, false, false, true, true,
                                      true, false),
                              Chara (true, false, false, true, false, true,
                                      true, false),
                              Chara (true, false, false, false, false, true,
                                      true, false),
                              Chara (false, true, false, false, false, true,
                                      true, false),
                              Chara (false, false, true, true, false, true,
                                      true, false),
                              Chara (true, false, true, false, false, true,
                                      true, false),
                              Chara (false, false, false, false, false, true,
                                      false, false),
                              Chara (true, false, false, true, false, true,
                                      true, false),
                              Chara (false, true, true, true, false, true, true,
                                      false),
                              Chara (false, false, false, false, false, true,
                                      false, false),
                              Chara (false, true, false, false, false, true,
                                      true, false),
                              Chara (true, false, true, false, false, true,
                                      true, false),
                              Chara (false, false, false, true, true, true,
                                      true, false),
                              Chara (false, false, false, false, true, true,
                                      true, false),
                              Chara (false, true, false, true, true, true,
                                      false, false),
                              Chara (false, false, false, false, false, true,
                                      false, false)] @
                             shows_prec_bexp show_literal show_int zero_nata b
                               [])))
                   (fn _ => Result (g, b)))
           end)
  end;

fun scan_acconstraint x =
  bindb (alt (bindb (gen_token lx_ws scan_var)
               (fn xa =>
                 bindb (gen_token lx_ws
                         (exactly (equal_char, show_char)
                           [Chara (false, false, true, true, true, true, false,
                                    false)]))
                   (fn _ =>
                     bindb (gen_token lx_ws lx_int)
                       (fn xaa => return (Ltb (implode xa, xaa))))))
          (bindb
            (alt (bindb (gen_token lx_ws scan_var)
                   (fn xa =>
                     bindb (gen_token lx_ws
                             (exactly (equal_char, show_char)
                               [Chara (false, false, true, true, true, true,
false, false),
                                 Chara (true, false, true, true, true, true,
 false, false)]))
                       (fn _ =>
                         bindb (gen_token lx_ws lx_int)
                           (fn xaa => return (Leb (implode xa, xaa))))))
              (bindb
                (alt (bindb (gen_token lx_ws scan_var)
                       (fn xa =>
                         bindb (gen_token lx_ws
                                 (exactly (equal_char, show_char)
                                   [Chara (true, false, true, true, true, true,
    false, false),
                                     Chara (true, false, true, true, true, true,
     false, false)]))
                           (fn _ =>
                             bindb (gen_token lx_ws lx_int)
                               (fn xaa => return (Eqa (implode xa, xaa))))))
                  (bindb
                    (alt (bindb (gen_token lx_ws scan_var)
                           (fn xa =>
                             bindb (gen_token lx_ws
                                     (exactly (equal_char, show_char)
                                       [Chara
  (true, false, true, true, true, true, false, false)]))
                               (fn _ =>
                                 bindb (gen_token lx_ws lx_int)
                                   (fn xaa => return (Eqa (implode xa, xaa))))))
                      (bindb
                        (alt (bindb (gen_token lx_ws scan_var)
                               (fn xa =>
                                 bindb (gen_token lx_ws
 (exactly (equal_char, show_char)
   [Chara (false, true, true, true, true, true, false, false),
     Chara (true, false, true, true, true, true, false, false)]))
                                   (fn _ =>
                                     bindb (gen_token lx_ws lx_int)
                                       (fn xaa =>
 return (Gea (implode xa, xaa))))))
                          (bindb (gen_token lx_ws scan_var)
                            (fn xa =>
                              bindb (gen_token lx_ws
                                      (exactly (equal_char, show_char)
[Chara (false, true, true, true, true, true, false, false)]))
                                (fn _ =>
                                  bindb (gen_token lx_ws lx_int)
                                    (fn xaa =>
                                      return (Gta (implode xa, xaa)))))))
                        (fn xa => return (sum_join xa))))
                    (fn xa => return (sum_join xa))))
                (fn xa => return (sum_join xa))))
            (fn xa => return (sum_join xa))))
    (fn xa => return (sum_join xa)) x;

fun scan_loc x =
  bindb (gen_token lx_ws scan_var)
    (fn xa =>
      bindb (exactly (equal_char, show_char)
              [Chara (false, true, true, true, false, true, false, false)])
        (fn _ =>
          bindb scan_var (fn xaa => return (Loc (implode xa, implode xaa)))))
    x;

fun scan_bexp_elem x =
  bindb (alt scan_acconstraint scan_loc) (fn xa => return (sum_join xa)) x;

fun scan_7a elem imply or anda nota l =
  bindb (alt (bindb
               (scan_infix_pair (scan_6a elem imply or anda nota)
                 (scan_7a elem imply or anda nota)
                 [Chara (true, false, true, true, false, true, false, false),
                   Chara (false, true, true, true, true, true, false, false)])
               (fn x => return (uncurry imply x)))
          (bindb
            (alt (bindb
                   (scan_infix_pair (scan_6a elem imply or anda nota)
                     (scan_7a elem imply or anda nota)
                     [Chara (false, false, true, true, true, true, true, false),
                       Chara (false, false, true, true, true, true, true,
                               false)])
                   (fn x => return (uncurry or x)))
              (scan_6a elem imply or anda nota))
            (fn x => return (sum_join x))))
    (fn x => return (sum_join x)) l
and scan_0a elem imply or anda nota l =
  bindb (alt (bindb
               (gen_token lx_ws
                 (bindb
                   (alt (exactly (equal_char, show_char)
                          [Chara (false, true, true, true, true, true, true,
                                   false)])
                     (exactly (equal_char, show_char)
                       [Chara (true, false, false, false, false, true, false,
                                false)]))
                   (fn x => return (sum_join x))))
               (fn _ =>
                 bindb (scan_parens
                         [Chara (false, false, false, true, false, true, false,
                                  false)]
                         [Chara (true, false, false, true, false, true, false,
                                  false)]
                         (scan_7a elem imply or anda nota))
                   (fn x => return (nota x))))
          (bindb
            (alt elem
              (scan_parens
                [Chara (false, false, false, true, false, true, false, false)]
                [Chara (true, false, false, true, false, true, false, false)]
                (scan_7a elem imply or anda nota)))
            (fn x => return (sum_join x))))
    (fn x => return (sum_join x)) l
and scan_6a elem imply or anda nota l =
  bindb (alt (bindb
               (scan_infix_pair (scan_0a elem imply or anda nota)
                 (scan_6a elem imply or anda nota)
                 [Chara (false, true, true, false, false, true, false, false),
                   Chara (false, true, true, false, false, true, false, false)])
               (fn x => return (uncurry anda x)))
          (scan_0a elem imply or anda nota))
    (fn x => return (sum_join x)) l;

fun compile_invarianta clocks vars inv =
  (if ((inv : string) = "") then Result ([], True)
    else binda (err_msg ("Failed to parse guard in " ^ inv)
                 (parse
                   (scan_7a scan_bexp_elem (fn a => fn b => Implya (a, b))
                     (fn a => fn b => Ora (a, b)) (fn a => fn b => Anda (a, b))
                     Nota)
                   inv))
           (compile_invariant clocks vars));

fun of_string json =
  (case json of Object _ => Error ["of_array: expected sequence"]
    | Arraya _ => Error ["of_array: expected sequence"]
    | String s => Result (implode s)
    | Int _ => Error ["of_array: expected sequence"]
    | Nata _ => Error ["of_array: expected sequence"]
    | Rat _ => Error ["of_array: expected sequence"]
    | Boolean _ => Error ["of_array: expected sequence"]
    | Null => Error ["of_array: expected sequence"]);

fun of_object json =
  (case json of Object asa => Result (map_of (equal_list equal_char) asa)
    | Arraya _ => Error ["json_to_map: expected object"]
    | String _ => Error ["json_to_map: expected object"]
    | Int _ => Error ["json_to_map: expected object"]
    | Nata _ => Error ["json_to_map: expected object"]
    | Rat _ => Error ["json_to_map: expected object"]
    | Boolean _ => Error ["json_to_map: expected object"]
    | Null => Error ["json_to_map: expected object"]);

fun convert_node clocks vars n =
  binda (of_object n)
    (fn na =>
      binda (binda
              (geta (show_list show_char) na
                [Chara (true, false, false, true, false, true, true, false),
                  Chara (false, false, true, false, false, true, true, false)])
              of_nat)
        (fn id =>
          binda (binda
                  (geta (show_list show_char) na
                    [Chara (false, true, true, true, false, true, true, false),
                      Chara (true, false, false, false, false, true, true,
                              false),
                      Chara (true, false, true, true, false, true, true, false),
                      Chara (true, false, true, false, false, true, true,
                              false)])
                  of_string)
            (fn name =>
              binda (binda
                      (geta (show_list show_char) na
                        [Chara (true, false, false, true, false, true, true,
                                 false),
                          Chara (false, true, true, true, false, true, true,
                                  false),
                          Chara (false, true, true, false, true, true, true,
                                  false),
                          Chara (true, false, false, false, false, true, true,
                                  false),
                          Chara (false, true, false, false, true, true, true,
                                  false),
                          Chara (true, false, false, true, false, true, true,
                                  false),
                          Chara (true, false, false, false, false, true, true,
                                  false),
                          Chara (false, true, true, true, false, true, true,
                                  false),
                          Chara (false, false, true, false, true, true, true,
                                  false)])
                      of_string)
                (fn inv =>
                  binda (err_msg "Failed to parse invariant!"
                          (compile_invarianta clocks vars inv))
                    (fn (inva, inv_vars) =>
                      binda (assert
                              (case inv_vars of True => true | Not _ => false
                                | And (_, _) => false | Or (_, _) => false
                                | Imply (_, _) => false | Eq (_, _) => false
                                | Lea (_, _) => false | Lta (_, _) => false
                                | Ge (_, _) => false | Gt (_, _) => false)
                              "State invariants on nodes are not supported")
                        (fn _ => Result ((name, id), inva)))))));

fun scan_update x =
  bindb (gen_token lx_ws scan_var)
    (fn xa =>
      bindb (gen_token lx_ws
              (bindb
                (alt (exactly (equal_char, show_char)
                       [Chara (true, false, true, true, true, true, false,
                                false)])
                  (exactly (equal_char, show_char)
                    [Chara (false, true, false, true, true, true, false, false),
                      Chara (true, false, true, true, true, true, false,
                              false)]))
                (fn xb => return (sum_join xb))))
        (fn _ => bindb scan_exp (fn xaa => return (implode xa, xaa))))
    x;

fun scan_action x =
  bindb (alt (bindb scan_var
               (fn xa =>
                 bindb (gen_token lx_ws
                         (exactly (equal_char, show_char)
                           [Chara (true, true, true, true, true, true, false,
                                    false)]))
                   (fn _ => return ((In o implode) xa))))
          (bindb
            (alt (bindb scan_var
                   (fn xa =>
                     bindb (gen_token lx_ws
                             (exactly (equal_char, show_char)
                               [Chara (true, false, false, false, false, true,
false, false)]))
                       (fn _ => return ((Out o implode) xa))))
              (bindb scan_var (fn xa => return ((Sil o implode) xa))))
            (fn xa => return (sum_join xa))))
    (fn xa => return (sum_join xa)) x;

fun convert_edge clocks vars e =
  binda (of_object e)
    (fn ea =>
      binda (binda
              (geta (show_list show_char) ea
                [Chara (true, true, false, false, true, true, true, false),
                  Chara (true, true, true, true, false, true, true, false),
                  Chara (true, false, true, false, true, true, true, false),
                  Chara (false, true, false, false, true, true, true, false),
                  Chara (true, true, false, false, false, true, true, false),
                  Chara (true, false, true, false, false, true, true, false)])
              of_nat)
        (fn source =>
          binda (binda
                  (geta (show_list show_char) ea
                    [Chara (false, false, true, false, true, true, true, false),
                      Chara (true, false, false, false, false, true, true,
                              false),
                      Chara (false, true, false, false, true, true, true,
                              false),
                      Chara (true, true, true, false, false, true, true, false),
                      Chara (true, false, true, false, false, true, true,
                              false),
                      Chara (false, false, true, false, true, true, true,
                              false)])
                  of_nat)
            (fn target =>
              binda (binda
                      (geta (show_list show_char) ea
                        [Chara (true, true, true, false, false, true, true,
                                 false),
                          Chara (true, false, true, false, true, true, true,
                                  false),
                          Chara (true, false, false, false, false, true, true,
                                  false),
                          Chara (false, true, false, false, true, true, true,
                                  false),
                          Chara (false, false, true, false, false, true, true,
                                  false)])
                      of_string)
                (fn guard =>
                  binda (binda
                          (geta (show_list show_char) ea
                            [Chara (false, false, true, true, false, true, true,
                                     false),
                              Chara (true, false, false, false, false, true,
                                      true, false),
                              Chara (false, true, false, false, false, true,
                                      true, false),
                              Chara (true, false, true, false, false, true,
                                      true, false),
                              Chara (false, false, true, true, false, true,
                                      true, false)])
                          of_string)
                    (fn label =>
                      binda (binda
                              (geta (show_list show_char) ea
                                [Chara (true, false, true, false, true, true,
 true, false),
                                  Chara (false, false, false, false, true, true,
  true, false),
                                  Chara (false, false, true, false, false, true,
  true, false),
                                  Chara (true, false, false, false, false, true,
  true, false),
                                  Chara (false, false, true, false, true, true,
  true, false),
                                  Chara (true, false, true, false, false, true,
  true, false)])
                              of_string)
                        (fn update =>
                          binda (if ((label : string) = "") then Result (Sil "")
                                  else err_msg
 ("Failed to parse label in " ^ label) (parse scan_action label))
                            (fn labela =>
                              binda (err_msg "Failed to parse guard!"
                                      (compile_invarianta clocks vars guard))
                                (fn (g, check) =>
                                  binda (if ((update : string) = "")
  then Result []
  else err_msg ("Failed to parse update in " ^ update)
         (parse (parse_list scan_update) update))
                                    (fn upd =>
                                      let
val resets = filter (fn x => membera equal_literal clocks (fst x)) upd;
                                      in
binda (assert (list_all (fn (_, Const x) => equal_inta x zero_inta) resets)
        "Clock resets to values different from zero are not supported")
  (fn _ =>
    let
      val resetsa = map fst resets;
      val upds =
        filter (fn x => not (membera equal_literal clocks (fst x))) upd;
    in
      binda (assert (list_all (fn (x, _) => membera equal_literal vars x) upds)
              ("Unknown variable in update: " ^ update))
        (fn _ =>
          Result (source, (check, (g, (labela, (upds, (resetsa, target)))))))
    end)
                                      end)))))))));

fun of_array json =
  (case json of Object _ => Error ["of_array: expected sequence"]
    | Arraya a => Result a | String _ => Error ["of_array: expected sequence"]
    | Int _ => Error ["of_array: expected sequence"]
    | Nata _ => Error ["of_array: expected sequence"]
    | Rat _ => Error ["of_array: expected sequence"]
    | Boolean _ => Error ["of_array: expected sequence"]
    | Null => Error ["of_array: expected sequence"]);

fun default def x = (case x of Result s => s | Error _ => def);

fun convert_automaton clocks vars a =
  binda (binda
          (geta (show_list show_char) a
            [Chara (false, true, true, true, false, true, true, false),
              Chara (true, true, true, true, false, true, true, false),
              Chara (false, false, true, false, false, true, true, false),
              Chara (true, false, true, false, false, true, true, false),
              Chara (true, true, false, false, true, true, true, false)])
          of_array)
    (fn nodes =>
      binda (binda
              (geta (show_list show_char) a
                [Chara (true, false, true, false, false, true, true, false),
                  Chara (false, false, true, false, false, true, true, false),
                  Chara (true, true, true, false, false, true, true, false),
                  Chara (true, false, true, false, false, true, true, false),
                  Chara (true, true, false, false, true, true, true, false)])
              of_array)
        (fn edges =>
          binda (combine_map (convert_node clocks vars) nodes)
            (fn nodesa =>
              let
                val invs = map (fn (aa, b) => let
        val (_, ab) = aa;
      in
        (fn ba => (ab, ba))
      end
        b)
                             nodesa;
                val names_to_ids = map fst nodesa;
              in
                binda (assert
                        (distinct equal_literal
                          (filter (fn s => not ((s : string) = ""))
                            (map fst names_to_ids)))
                        ("Node names are ambiguous" ^
                          implode
                            (shows_prec_list show_literal zero_nata
                              (map fst names_to_ids) [])))
                  (fn _ =>
                    binda (assert (distinct equal_nat (map snd names_to_ids))
                            "Duplicate node id")
                      (fn _ =>
                        let
                          val ids_to_names =
                            map_of equal_nat (map swap names_to_ids);
                          val names_to_idsa = map_of equal_literal names_to_ids;
                          val committed =
                            default []
                              (binda
                                (geta (show_list show_char) a
                                  [Chara (true, true, false, false, false, true,
   true, false),
                                    Chara (true, true, true, true, false, true,
    true, false),
                                    Chara (true, false, true, true, false, true,
    true, false),
                                    Chara (true, false, true, true, false, true,
    true, false),
                                    Chara (true, false, false, true, false,
    true, true, false),
                                    Chara (false, false, true, false, true,
    true, true, false),
                                    Chara (false, false, true, false, true,
    true, true, false),
                                    Chara (true, false, true, false, false,
    true, true, false),
                                    Chara (false, false, true, false, false,
    true, true, false)])
                                of_array);
                        in
                          binda (combine_map of_nat committed)
                            (fn committeda =>
                              binda (combine_map (convert_edge clocks vars)
                                      edges)
                                (fn edgesa =>
                                  Result
                                    (names_to_idsa,
                                      (ids_to_names,
(committeda, (edgesa, invs))))))
                        end))
              end)));

fun scan_prefix p head =
  bindb (gen_token lx_ws (exactly (equal_char, show_char) head)) (fn _ => p);

fun scan_formula x =
  bindb (alt (bindb
               (scan_prefix
                 (scan_7a scan_bexp_elem (fn a => fn b => Implya (a, b))
                   (fn a => fn b => Ora (a, b)) (fn a => fn b => Anda (a, b))
                   Nota)
                 [Chara (true, false, true, false, false, false, true, false),
                   Chara (false, false, true, true, true, true, false, false),
                   Chara (false, true, true, true, true, true, false, false)])
               (fn xa => return (EX xa)))
          (bindb
            (alt (bindb
                   (scan_prefix
                     (scan_7a scan_bexp_elem (fn a => fn b => Implya (a, b))
                       (fn a => fn b => Ora (a, b))
                       (fn a => fn b => Anda (a, b)) Nota)
                     [Chara (true, false, true, false, false, false, true,
                              false),
                       Chara (true, true, false, true, true, false, true,
                               false),
                       Chara (true, false, true, true, true, false, true,
                               false)])
                   (fn xa => return (EG xa)))
              (bindb
                (alt (bindb
                       (scan_prefix
                         (scan_7a scan_bexp_elem (fn a => fn b => Implya (a, b))
                           (fn a => fn b => Ora (a, b))
                           (fn a => fn b => Anda (a, b)) Nota)
                         [Chara (true, false, false, false, false, false, true,
                                  false),
                           Chara (false, false, true, true, true, true, false,
                                   false),
                           Chara (false, true, true, true, true, true, false,
                                   false)])
                       (fn xa => return (AX xa)))
                  (bindb
                    (alt (bindb
                           (scan_prefix
                             (scan_7a scan_bexp_elem
                               (fn a => fn b => Implya (a, b))
                               (fn a => fn b => Ora (a, b))
                               (fn a => fn b => Anda (a, b)) Nota)
                             [Chara (true, false, false, false, false, false,
                                      true, false),
                               Chara (true, true, false, true, true, false,
                                       true, false),
                               Chara (true, false, true, true, true, false,
                                       true, false)])
                           (fn xa => return (AG xa)))
                      (bindb
                        (scan_infix_pair
                          (scan_7a scan_bexp_elem
                            (fn a => fn b => Implya (a, b))
                            (fn a => fn b => Ora (a, b))
                            (fn a => fn b => Anda (a, b)) Nota)
                          (scan_7a scan_bexp_elem
                            (fn a => fn b => Implya (a, b))
                            (fn a => fn b => Ora (a, b))
                            (fn a => fn b => Anda (a, b)) Nota)
                          [Chara (true, false, true, true, false, true, false,
                                   false),
                            Chara (true, false, true, true, false, true, false,
                                    false),
                            Chara (false, true, true, true, true, true, false,
                                    false)])
                        (fn xa =>
                          return
                            (uncurry (fn a => fn b => Leadsto (a, b)) xa))))
                    (fn xa => return (sum_join xa))))
                (fn xa => return (sum_join xa))))
            (fn xa => return (sum_join xa))))
    (fn xa => return (sum_join xa)) x;

fun parse_bound x =
  bindb ta_var_ident
    (fn a =>
      bindb (exactly (equal_char, show_char)
              [Chara (true, true, false, true, true, false, true, false)])
        (fn _ =>
          bindb lx_int
            (fn xa =>
              bindb (exactly (equal_char, show_char)
                      [Chara (false, true, false, true, true, true, false,
                               false)])
                (fn _ =>
                  bindb lx_int
                    (fn xaa =>
                      bindb (exactly (equal_char, show_char)
                              [Chara (true, false, true, true, true, false,
                                       true, false)])
                        (fn _ => return (a, (xa, xaa))))))))
    x;

fun parse_bounds x =
  bindb (alt (parse_list
               (bindb lx_ws
                 (fn _ =>
                   bindb parse_bound (fn xa => return let
                val (s, a) = xa;
              in
                (implode s, a)
              end))))
          (bindb lx_ws (fn _ => return [])))
    (fn xa => return (sum_join xa)) x;

fun convert json =
  binda (of_object json)
    (fn all =>
      binda (geta (show_list show_char) all
              [Chara (true, false, false, false, false, true, true, false),
                Chara (true, false, true, false, true, true, true, false),
                Chara (false, false, true, false, true, true, true, false),
                Chara (true, true, true, true, false, true, true, false),
                Chara (true, false, true, true, false, true, true, false),
                Chara (true, false, false, false, false, true, true, false),
                Chara (false, false, true, false, true, true, true, false),
                Chara (true, false, false, false, false, true, true, false)])
        (fn automata =>
          binda (of_array automata)
            (fn automataa =>
              let
                val broadcast =
                  default []
                    (binda
                      (geta (show_list show_char) all
                        [Chara (false, true, false, false, false, true, true,
                                 false),
                          Chara (false, true, false, false, true, true, true,
                                  false),
                          Chara (true, true, true, true, false, true, true,
                                  false),
                          Chara (true, false, false, false, false, true, true,
                                  false),
                          Chara (false, false, true, false, false, true, true,
                                  false),
                          Chara (true, true, false, false, false, true, true,
                                  false),
                          Chara (true, false, false, false, false, true, true,
                                  false),
                          Chara (true, true, false, false, true, true, true,
                                  false),
                          Chara (false, false, true, false, true, true, true,
                                  false)])
                      of_array);
              in
                binda (combine_map of_string broadcast)
                  (fn broadcasta =>
                    let
                      val _ =
                        writeln ("Broadcast channels " ^
                                  implode
                                    (shows_prec_list show_literal zero_nata
                                      broadcasta []));
                      val bounds =
                        default ""
                          (binda
                            (geta (show_list show_char) all
                              [Chara (false, true, true, false, true, true,
                                       true, false),
                                Chara (true, false, false, false, false, true,
true, false),
                                Chara (false, true, false, false, true, true,
true, false),
                                Chara (true, true, false, false, true, true,
true, false)])
                            of_string);
                    in
                      binda (err_msg "Failed to parse bounds"
                              (parse parse_bounds bounds))
                        (fn boundsa =>
                          binda (geta (show_list show_char) all
                                  [Chara (true, true, false, false, false, true,
   true, false),
                                    Chara (false, false, true, true, false,
    true, true, false),
                                    Chara (true, true, true, true, false, true,
    true, false),
                                    Chara (true, true, false, false, false,
    true, true, false),
                                    Chara (true, true, false, true, false, true,
    true, false),
                                    Chara (true, true, false, false, true, true,
    true, false)])
                            (fn clocks =>
                              binda (of_string clocks)
                                (fn clocksa =>
                                  binda (err_msg "Failed to parse clocks"
  (parse
    (parse_list
      (bindb lx_ws (fn _ => bindb ta_var_ident (fn x => return (implode x)))))
    clocksa))
                                    (fn clocksb =>
                                      binda
(geta (show_list show_char) all
  [Chara (false, true, true, false, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, false, true, true, false, true, true, false),
    Chara (true, false, true, false, true, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (true, false, false, false, false, true, true, false)])
(fn formula =>
  binda (of_string formula)
    (fn formulaa =>
      binda (err_msg "Failed to parse formula" (parse scan_formula formulaa))
        (fn formulab =>
          binda (combine_map of_object automataa)
            (fn automatab =>
              binda (combine_map
                      (fn a =>
                        binda (geta (show_list show_char) a
                                [Chara (false, true, true, true, false, true,
 true, false),
                                  Chara (true, false, false, false, false, true,
  true, false),
                                  Chara (true, false, true, true, false, true,
  true, false),
                                  Chara (true, false, true, false, false, true,
  true, false)])
                          of_string)
                      automatab)
                (fn process_names =>
                  binda (assert (distinct equal_literal process_names)
                          "Process names are ambiguous")
                    (fn _ =>
                      binda (assert
                              (subset (card_UNIV_literal, equal_literal)
                                (locs_of_formula equal_literal formulab)
                                (Set process_names))
                              "Unknown process name in formula")
                        (fn _ =>
                          let
                            val process_names_to_index =
                              index equal_literal process_names;
                          in
                            binda (combine_map
                                    (fn a =>
                                      binda
(geta (show_list show_char) a
  [Chara (true, false, false, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, false, true, true, false, true, true, false)])
(fn x => binda (of_nat x) Result))
                                    automatab)
                              (fn init_locs =>
                                let
                                  val formulac =
                                    map_formulaa process_names_to_index id id id
                                      formulab;
                                  val vars = map fst boundsa;
                                  val init_vars =
                                    map (fn x => (x, zero_inta)) vars;
                                in
                                  binda (combine_map
  (convert_automaton clocksb vars) automatab)
                                    (fn names_automata =>
                                      let
val automatac = map (snd o snd) names_automata;
val names = map fst names_automata;
val ids_to_names = map (fst o snd) names_automata;
val ids_to_namesa =
  (fn p => fn i =>
    (case nth ids_to_names p i
      of NONE => implode (shows_prec_nat zero_nata i []) | SOME n => n));
                                      in
binda (rename_locs_formula (fn i => geta show_literal (nth names i)) formulac)
  (fn formulad =>
    Result
      (ids_to_namesa,
        (process_names_to_index,
          (broadcasta,
            (automatac, (boundsa, (formulad, (init_locs, init_vars))))))))
                                      end)
                                end)
                          end)))))))))))
                    end)
              end)));

fun default_map_of B_ a xs = map_default a (map_of B_ xs);

fun extract_certificate_impl A_ (B1_, B2_, B3_) succsi a_0i fi lei emptyi keyi
  copyi tracei =
  uncurry0
    ((fn f_ => fn () => f_ (a_0i ()) ())
      (fn x =>
        (fn f_ => fn () => f_ ((emptyi x) ()) ())
          (fn xa =>
            (fn f_ => fn () => f_ (a_0i ()) ())
              (fn xaa =>
                (fn f_ => fn () => f_ ((fi xaa) ()) ())
                  (fn xab =>
                    (fn f_ => fn () => f_
                      ((if not xa andalso xab
                         then (fn f_ => fn () => f_
                                ((ht_new (B2_, B3_) (heap_list A_)) ()) ())
                                (fn x_b => (fn () => (true, x_b)))
                         else (fn f_ => fn () => f_ (a_0i ()) ())
                                (fn xb =>
                                  (fn f_ => fn () => f_ ((emptyi xb) ()) ())
                                    (fn x_a =>
                                      (if x_a
then (fn f_ => fn () => f_ ((ht_new (B2_, B3_) (heap_list A_)) ()) ())
       (fn x_c => (fn () => (false, x_c)))
else (fn f_ => fn () => f_ (a_0i ()) ())
       (fn xc =>
         (fn f_ => fn () => f_ ((keyi xc) ()) ())
           (fn xd =>
             (fn f_ => fn () => f_ (a_0i ()) ())
               (fn xac =>
                 (fn f_ => fn () => f_ ((ht_new (B2_, B3_) (heap_list A_)) ())
                   ())
                   (fn xba =>
                     (fn f_ => fn () => f_
                       ((ht_update (B1_, B2_, B3_) (heap_list A_) xd [xac] xba)
                       ()) ())
                       (fn xe =>
                         (fn f_ => fn () => f_ (a_0i ()) ())
                           (fn xad =>
                             (fn f_ => fn () => f_
                               ((heap_WHILET
                                  (fn (_, (a1b, a2b)) =>
                                    (fn () =>
                                      (not a2b andalso
not (op_list_is_empty a1b))))
                                  (fn (a1a, (a1b, a2b)) =>
                                    let
                                      val (a1c, a2c) =
(case a1b of [] => cODE_ABORT (fn _ => (hd a1b, tl a1b)) | a :: b => (a, b));
                                    in
                                      (fn f_ => fn () => f_ ((emptyi a1c) ())
())
(fn x_e =>
  (if x_e then (fn () => (a1a, (a2c, a2b)))
    else (fn f_ => fn () => f_ (tRACE_impl ()) ())
           (fn _ =>
             (fn f_ => fn () => f_
               ((tracei
                   [Chara (true, false, true, false, false, false, true, false),
                     Chara (false, false, false, true, true, true, true, false),
                     Chara (false, false, false, false, true, true, true,
                             false),
                     Chara (false, false, true, true, false, true, true, false),
                     Chara (true, true, true, true, false, true, true, false),
                     Chara (false, true, false, false, true, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, false, true, false, false, true, true,
                             false)]
                  a1c)
               ()) ())
               (fn _ =>
                 (fn f_ => fn () => f_ ((succsi a1c) ()) ())
                   (fn x_h =>
                     imp_nfoldli x_h (fn (_, (_, b)) => (fn () => (not b)))
                       (fn xl => fn (a1d, (a1e, _)) =>
                         (fn f_ => fn () => f_ ((emptyi xl) ()) ())
                           (fn x_k =>
                             (if x_k then (fn () => (a1d, (a1e, false)))
                               else (fn f_ => fn () => f_ ((fi xl) ()) ())
                                      (fn x_l =>
(if x_l then (fn () => (a1d, (a1e, true)))
  else (fn f_ => fn () => f_ ((keyi xl) ()) ())
         (fn x_m =>
           (fn f_ => fn () => f_
             ((hms_extract (ht_lookup (B1_, B2_, B3_) (heap_list A_))
                (ht_delete (B1_, B2_, B3_) (heap_list A_)) x_m a1d)
             ()) ())
             (fn a =>
               (case a
                 of (NONE, a2f) =>
                   (fn f_ => fn () => f_ ((copyi xl) ()) ())
                     (fn xf =>
                       (fn f_ => fn () => f_
                         ((ht_update (B1_, B2_, B3_) (heap_list A_) x_m [xf]
                            a2f)
                         ()) ())
                         (fn x_o =>
                           (fn () => (x_o, (op_list_prepend xl a1e, false)))))
                 | (SOME x_o, a2f) =>
                   (fn f_ => fn () => f_ ((lso_bex_impl (lei xl) x_o) ()) ())
                     (fn x_p =>
                       (if x_p
                         then (fn f_ => fn () => f_
                                ((ht_update (B1_, B2_, B3_) (heap_list A_) x_m
                                   x_o a2f)
                                ()) ())
                                (fn x_q => (fn () => (x_q, (a1e, false))))
                         else (fn f_ => fn () => f_ ((copyi xl) ()) ())
                                (fn xf =>
                                  (fn f_ => fn () => f_
                                    ((ht_update (B1_, B2_, B3_) (heap_list A_)
                                       x_m (xf :: x_o) a2f)
                                    ()) ())
                                    (fn x_q =>
                                      (fn () =>
(x_q, (op_list_prepend xl a1e, false)))))))))))))))
                       (a1a, (a2c, false)))))))
                                    end)
                                  (xe, (op_list_prepend xad [], false)))
                               ()) ())
                               (fn (a1a, (_, a2b)) =>
                                 (fn () => (a2b, a1a)))))))))))))
                      ()) ())
                      (fn (_, a) =>
                        list_of_map_impl (B1_, B2_, B3_) (heap_list A_) a))))));

fun mk_updsi s upds =
  fold (fn (x, upd) => fn sa =>
         list_update sa x (evali (equal_int, linorder_int) s upd))
    upds s;

fun map_formula f g h (EX phi) = EX (map_sexp f g h phi)
  | map_formula f g h (EG phi) = EG (map_sexp f g h phi)
  | map_formula f g h (AX phi) = AX (map_sexp f g h phi)
  | map_formula f g h (AG phi) = AG (map_sexp f g h phi)
  | map_formula f g h (Leadsto (phi, psi)) =
    Leadsto (map_sexp f g h phi, map_sexp f g h psi);

fun map_acconstraint f1 f2 (LT (x11, x12)) = LT (f1 x11, f2 x12)
  | map_acconstraint f1 f2 (LE (x21, x22)) = LE (f1 x21, f2 x22)
  | map_acconstraint f1 f2 (EQ (x31, x32)) = EQ (f1 x31, f2 x32)
  | map_acconstraint f1 f2 (GT (x41, x42)) = GT (f1 x41, f2 x42)
  | map_acconstraint f1 f2 (GE (x51, x52)) = GE (f1 x51, f2 x52);

fun print_line_impl x = (fn xi => (fn () => (writeln xi))) x;

fun mem_assoc A_ x = list_ex (fn (y, _) => eq A_ x y);

fun show_locs B_ inv_renum_states =
  (fn x => shows_prec_list B_ zero_nata x []) o
    map_index zero_nata inv_renum_states;

fun show_vars A_ B_ inv_renum_vars =
  (fn x => shows_prec_list (show_list show_char) zero_nata x []) o
    map_index zero_nata
      (fn i => fn v =>
        shows_prec A_ zero_nata (inv_renum_vars i) [] @
          [Chara (true, false, true, true, true, true, false, false)] @
            shows_prec B_ zero_nata v []);

fun fw_upd_impl_int n =
  (fn ai => fn bib => fn bia => fn bi =>
    (fn f_ => fn () => f_
      ((mtx_get (heap_DBMEntry heap_int) (suc n) ai (bia, bi)) ()) ())
      (fn x =>
        (fn f_ => fn () => f_
          ((mtx_get (heap_DBMEntry heap_int) (suc n) ai (bia, bib)) ()) ())
          (fn xa =>
            (fn f_ => fn () => f_
              ((mtx_get (heap_DBMEntry heap_int) (suc n) ai (bib, bi)) ()) ())
              (fn xb =>
                mtx_set (heap_DBMEntry heap_int) (suc n) ai (bia, bi)
                  (min_int_entry x (dbm_add_int xa xb))))));

fun fw_impl_int n =
  imp_for_inta zero_nata (plus_nata n one_nata)
    (fn xb =>
      imp_for_inta zero_nata (plus_nata n one_nata)
        (fn xd =>
          imp_for_inta zero_nata (plus_nata n one_nata)
            (fn xf => fn sigma => fw_upd_impl_int n sigma xb xd xf)));

fun check_final_impl (A1_, A2_, A3_) B_ fi copyi =
  (fn ai => fn bi =>
    imp_nfoldli ai (fn a => (fn () => a))
      (fn xb => fn _ =>
        (fn f_ => fn () => f_
          ((hms_lookup (ht_lookup (A1_, A2_, A3_) (heap_list B_))
             (heap_map copyi) xb bi)
          ()) ())
          (fn a =>
            (case a of NONE => (fn () => true)
              | SOME x_e =>
                imp_nfoldli x_e (fn aa => (fn () => aa))
                  (fn xh => fn _ =>
                    (fn f_ => fn () => f_ ((fi (xb, xh)) ()) ())
                      (fn x_i => (fn () => (not x_i))))
                  true)))
      true);

fun print_check_impl x = (fn ai => fn bi => (fn () => (print_check ai bi))) x;

fun distr (A1_, A2_) xs =
  let
    val (m, d) =
      fold (fn x => fn (m, d) =>
             (case m x of NONE => (fun_upd A1_ m x (SOME one_nata), x :: d)
               | SOME y => (fun_upd A1_ m x (SOME (plus_nata y one_nata)), d)))
        xs ((fn _ => NONE), []);
  in
    map (fn x => (x, the (m x))) (sort_key A2_ (fn x => x) d)
  end;

fun show_state B_ C_ D_ inv_renum_states inv_renum_vars =
  (fn (l, vs) =>
    let
      val la = show_locs B_ inv_renum_states l;
      val vsa = show_vars C_ D_ inv_renum_vars vs;
    in
      [Chara (false, false, true, true, true, true, false, false)] @
        la @ [Chara (false, true, true, true, true, true, false, false),
               Chara (false, false, true, true, false, true, false, false),
               Chara (false, false, false, false, false, true, false, false),
               Chara (false, false, true, true, true, true, false, false)] @
               vsa @ [Chara (false, true, true, true, true, true, false, false)]
    end);

fun bounds_map bounds = the o map_of equal_nat bounds;

fun check_boundedi bounds s =
  all_interval_nat
    (fn x =>
      less_eq_int (fst (bounds_map bounds x)) (nth s x) andalso
        less_eq_int (nth s x) (snd (bounds_map bounds x)))
    zero_nata (size_list s);

fun pairs_by_action_impl bounds l s out ina =
  maps (fn (p, (b1, (g1, (a1, (f1, (r1, l1)))))) =>
         map_filter
           (fn (q, (b2, (g2, (_, (f2, (r2, l2)))))) =>
             (if equal_nata p q then NONE
               else let
                      val sa = mk_updsi (mk_updsi s f1) f2;
                    in
                      (if bvali (equal_int, linorder_int) s b1 andalso
                            (bvali (equal_int, linorder_int) s b2 andalso
                              check_boundedi bounds sa)
                        then SOME (g1 @ g2,
                                    (Bin a1,
                                      (r1 @ r2,
(list_update (list_update l p l1) q l2, sa))))
                        else NONE)
                    end))
           out)
    ina;

fun actions_by_state i =
  fold (fn t => fn acc =>
         list_update acc (fst (snd (snd t)))
           ((i, t) :: nth acc (fst (snd (snd t)))));

fun all_actions_from_vec num_actions t vec =
  fold (fn (p, l) => actions_by_state p (t p l)) vec
    (map (fn _ => []) (upt zero_nata num_actions));

fun all_actions_by_state broadcast bounds automata num_actions t l =
  fold (fn i => actions_by_state i (t i (nth l i)))
    (upt zero_nata (size_list automata))
    (map (fn _ => []) (upt zero_nata num_actions));

fun compute_upds_impl bounds init =
  map_filter
    (fn comb =>
      let
        val a =
          fold (fn (q, (_, (g2, (_, (f2, (r2, l2)))))) => fn (g1, a) =>
                 let
                   val (aa, (r1, (l, s))) = a;
                 in
                   (g1 @ g2,
                     (aa, (r1 @ r2, (list_update l q l2, mk_updsi s f2))))
                 end)
            comb init;
        val (g, aa) = a;
        val (ab, (r, (l, s))) = aa;
      in
        (if check_boundedi bounds s then SOME (g, (ab, (r, (l, s)))) else NONE)
      end);

fun actions_by_statea num_actions xs =
  fold (fn t => fn acc =>
         list_update acc (fst (snd (snd t))) (t :: nth acc (fst (snd (snd t)))))
    xs (map (fn _ => []) (upt zero_nata num_actions));

fun get_commited broadcast bounds automata l =
  map_filter
    (fn p =>
      let
        val la = nth l p;
      in
        (if membera equal_nat (fst (nth automata p)) la then SOME (p, la)
          else NONE)
      end)
    (upt zero_nata (size_list automata));

fun bin_actions broadcast num_actions =
  filter (fn a => not (membera equal_nat broadcast a))
    (upt zero_nata num_actions);

fun make_combs broadcast bounds automata p a xs =
  let
    val ys =
      map_filter
        (fn i =>
          (if equal_nata i p then NONE
            else (if null (nth (nth xs i) a) then NONE
                   else SOME (map (fn aa => (i, aa)) (nth (nth xs i) a)))))
        (upt zero_nata (size_list automata));
  in
    (if null ys then [] else product_lists ys)
  end;

fun union_map_of A_ xs =
  fold (fn (x, y) => fn m =>
         (case m x of NONE => fun_upd A_ m x (SOME [y])
           | SOME ys => fun_upd A_ m x (SOME (y :: ys))))
    xs (fn _ => NONE);

fun trans_map automata i =
  let
    val m = union_map_of equal_nat (fst (snd (nth automata i)));
  in
    (fn j => (case m j of NONE => [] | SOME xs => xs))
  end;

fun reset_canonical_upd_impl_int x =
  (fn n => fn ai => fn bib => fn bia => fn bi =>
    (fn f_ => fn () => f_
      ((mtx_set (heap_DBMEntry heap_int) (suc n) ai (bia, zero_nata) (Le bi))
      ()) ())
      (fn xa =>
        (fn f_ => fn () => f_
          ((mtx_set (heap_DBMEntry heap_int) (suc n) xa (zero_nata, bia)
             (Le (uminus_inta bi)))
          ()) ())
          (imp_for_inta one_nata (plus_nata bib one_nata)
            (fn xb => fn sigma =>
              (if equal_nata xb bia then (fn () => sigma)
                else (fn f_ => fn () => f_
                       ((mtx_get (heap_DBMEntry heap_int) (suc n) sigma
                          (zero_nata, xb))
                       ()) ())
                       (fn x_d =>
                         (fn f_ => fn () => f_
                           ((mtx_get (heap_DBMEntry heap_int) (suc n) sigma
                              (xb, zero_nata))
                           ()) ())
                           (fn x_e =>
                             (fn f_ => fn () => f_
                               ((mtx_set (heap_DBMEntry heap_int) (suc n) sigma
                                  (bia, xb) (dbm_add_int (Le bi) x_d))
                               ()) ())
                               (fn x_f =>
                                 mtx_set (heap_DBMEntry heap_int) (suc n) x_f
                                   (xb, bia)
                                   (dbm_add_int (Le (uminus_inta bi))
                                     x_e)))))))))
    x;

fun up_canonical_upd_impl_int x =
  (fn n => fn ai => fn bi =>
    imp_for_inta one_nata (plus_nata bi one_nata)
      (fn xa => fn sigma =>
        mtx_set (heap_DBMEntry heap_int) (suc n) sigma (xa, zero_nata) INF)
      ai)
    x;

fun check_diag_impl_int x =
  (fn n => fn xi =>
    imp_for_int zero_nata (suc n) (fn sigma => (fn () => (not sigma)))
      (fn xc => fn sigma =>
        (fn f_ => fn () => f_
          ((mtx_get (heap_DBMEntry heap_int) (suc n) xi (xc, xc)) ()) ())
          (fn xa => (fn () => (dbm_lt_0 xa orelse sigma))))
      false)
    x;

fun abstra_upd_impl_int x =
  (fn n => fn ai => fn bi =>
    (case ai
      of LT (x41a, x42a) =>
        (fn f_ => fn () => f_
          ((mtx_get (heap_DBMEntry heap_int) (suc n) bi (x41a, zero_nata)) ())
          ())
          (fn xa =>
            mtx_set (heap_DBMEntry heap_int) (suc n) bi (x41a, zero_nata)
              (min_int_entry xa (Lt x42a)))
      | LE (x41a, x42a) =>
        (fn f_ => fn () => f_
          ((mtx_get (heap_DBMEntry heap_int) (suc n) bi (x41a, zero_nata)) ())
          ())
          (fn xa =>
            mtx_set (heap_DBMEntry heap_int) (suc n) bi (x41a, zero_nata)
              (min_int_entry xa (Le x42a)))
      | EQ (x41a, x42a) =>
        (fn f_ => fn () => f_
          ((mtx_get (heap_DBMEntry heap_int) (suc n) bi (zero_nata, x41a)) ())
          ())
          (fn xa =>
            (fn f_ => fn () => f_
              ((mtx_get (heap_DBMEntry heap_int) (suc n) bi (x41a, zero_nata))
              ()) ())
              (fn x_a =>
                (fn f_ => fn () => f_
                  ((mtx_set (heap_DBMEntry heap_int) (suc n) bi
                     (zero_nata, x41a)
                     (min_int_entry xa (Le (uminus_inta x42a))))
                  ()) ())
                  (fn x_b =>
                    mtx_set (heap_DBMEntry heap_int) (suc n) x_b
                      (x41a, zero_nata) (min_int_entry x_a (Le x42a)))))
      | GT (x41a, x42a) =>
        (fn f_ => fn () => f_
          ((mtx_get (heap_DBMEntry heap_int) (suc n) bi (zero_nata, x41a)) ())
          ())
          (fn xa =>
            mtx_set (heap_DBMEntry heap_int) (suc n) bi (zero_nata, x41a)
              (min_int_entry xa (Lt (uminus_inta x42a))))
      | GE (x41a, x42a) =>
        (fn f_ => fn () => f_
          ((mtx_get (heap_DBMEntry heap_int) (suc n) bi (zero_nata, x41a)) ())
          ())
          (fn xa =>
            mtx_set (heap_DBMEntry heap_int) (suc n) bi (zero_nata, x41a)
              (min_int_entry xa (Le (uminus_inta x42a))))))
    x;

fun check_sexpi A_ Truea uu uv = true
  | check_sexpi A_ (Nota e) l s = not (check_sexpi A_ e l s)
  | check_sexpi A_ (Anda (e1, e2)) l s =
    check_sexpi A_ e1 l s andalso check_sexpi A_ e2 l s
  | check_sexpi A_ (Ora (e1, e2)) l s =
    check_sexpi A_ e1 l s orelse check_sexpi A_ e2 l s
  | check_sexpi A_ (Implya (e1, e2)) l s =
    (if check_sexpi A_ e1 l s then check_sexpi A_ e2 l s else true)
  | check_sexpi A_ (Eqa (i, x)) l s = equal_inta (nth s i) x
  | check_sexpi A_ (Leb (i, x)) l s = less_eq_int (nth s i) x
  | check_sexpi A_ (Ltb (i, x)) l s = less_int (nth s i) x
  | check_sexpi A_ (Gea (i, x)) l s = less_eq_int x (nth s i)
  | check_sexpi A_ (Gta (i, x)) l s = less_int x (nth s i)
  | check_sexpi A_ (Loc (i, x)) l s = eq A_ (nth l i) x;

fun hd_of_formulai A_ (EX phi) l s = check_sexpi A_ phi l s
  | hd_of_formulai A_ (EG phi) l s = check_sexpi A_ phi l s
  | hd_of_formulai A_ (AX phi) l s = not (check_sexpi A_ phi l s)
  | hd_of_formulai A_ (AG phi) l s = not (check_sexpi A_ phi l s)
  | hd_of_formulai A_ (Leadsto (phi, uu)) l s = check_sexpi A_ phi l s;

fun n_vs bounds = size_list bounds;

fun state_space broadcast bounds automata m num_states num_actions k l_0 s_0
  formula show_clock show_state =
  let
    val succsi =
      let
        val n_ps = size_list automata;
        val k_i =
          Vector.fromList
            (map (Vector.fromList o map (Vector.fromList o map int_of_nat)) k);
        val invs =
          Vector.fromList
            (map (fn i =>
                   let
                     val ma =
                       default_map_of equal_nat [] (snd (snd (nth automata i)));
                     val mb =
                       Vector.fromList (map ma (upt zero_nata (num_states i)));
                   in
                     mb
                   end)
              (upt zero_nata n_ps));
        val inv_fun =
          (fn (l, _) =>
            maps (fn i => sub (sub invs i) (nth l i)) (upt zero_nata n_ps));
        val trans_mapa = trans_map automata;
        val trans_i_map =
          (fn i => fn j =>
            map_filter
              (fn (b, a) =>
                let
                  val (g, aa) = a;
                  val (ab, (ma, l)) = aa;
                in
                  (case ab of In _ => NONE | Out _ => NONE
                    | Sil ac => SOME (b, (g, (ac, (ma, l)))))
                end)
              (trans_mapa i j));
        val int_trans_from_loc_impl =
          (fn p => fn l => fn la => fn s =>
            let
              val a = trans_i_map p l;
            in
              map_filter
                (fn (b, aa) =>
                  let
                    val (g, ab) = aa;
                    val (ac, (f, (r, lb))) = ab;
                    val sa = mk_updsi s f;
                  in
                    (if bvali (equal_int, linorder_int) s b andalso
                          check_boundedi bounds sa
                      then SOME (g, (Internal ac,
                                      (r, (list_update la p lb, sa))))
                      else NONE)
                  end)
                a
            end);
        val int_trans_from_vec_impl =
          (fn pairs => fn l => fn s =>
            maps (fn (p, la) => int_trans_from_loc_impl p la l s) pairs);
        val int_trans_from_all_impl =
          (fn l => fn s =>
            maps (fn p => int_trans_from_loc_impl p (nth l p) l s)
              (upt zero_nata n_ps));
        val trans_out_map =
          (fn i => fn j =>
            map_filter
              (fn (b, a) =>
                let
                  val (g, aa) = a;
                  val (ab, (ma, l)) = aa;
                in
                  (case ab of In _ => NONE
                    | Out ac => SOME (b, (g, (ac, (ma, l)))) | Sil _ => NONE)
                end)
              (trans_mapa i j));
        val trans_in_map =
          (fn i => fn j =>
            map_filter
              (fn (b, a) =>
                let
                  val (g, aa) = a;
                  val (ab, (ma, l)) = aa;
                in
                  (case ab of In ac => SOME (b, (g, (ac, (ma, l))))
                    | Out _ => NONE | Sil _ => NONE)
                end)
              (trans_mapa i j));
        val trans_out_broad_grouped =
          (fn i => fn j =>
            actions_by_statea num_actions
              (map_filter
                (fn (b, a) =>
                  let
                    val (g, aa) = a;
                    val (ab, (ma, l)) = aa;
                  in
                    (case ab of In _ => NONE
                      | Out ac =>
                        (if membera equal_nat broadcast ac
                          then SOME (b, (g, (ac, (ma, l)))) else NONE)
                      | Sil _ => NONE)
                  end)
                (trans_mapa i j)));
        val trans_in_broad_grouped =
          (fn i => fn j =>
            actions_by_statea num_actions
              (map_filter
                (fn (b, a) =>
                  let
                    val (g, aa) = a;
                    val (ab, (ma, l)) = aa;
                  in
                    (case ab
                      of In ac =>
                        (if membera equal_nat broadcast ac
                          then SOME (b, (g, (ac, (ma, l)))) else NONE)
                      | Out _ => NONE | Sil _ => NONE)
                  end)
                (trans_mapa i j)));
        val broad_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_commited broadcast bounds automata l;
              val ina =
                map (fn p => trans_in_broad_grouped p (nth l p))
                  (upt zero_nata n_ps);
              val out =
                map (fn p => trans_out_broad_grouped p (nth l p))
                  (upt zero_nata n_ps);
              val inb =
                map (map (filter
                           (fn (b, _) => bvali (equal_int, linorder_int) s b)))
                  ina;
              val outa =
                map (map (filter
                           (fn (b, _) => bvali (equal_int, linorder_int) s b)))
                  out;
            in
              (if null pairs
                then maps (fn a =>
                            maps (fn p =>
                                   let
                                     val outs = nth (nth outa p) a;
                                   in
                                     (if null outs then []
                                       else let
      val combs = make_combs broadcast bounds automata p a inb;
      val outsa = map (fn aa => (p, aa)) outs;
      val combsa =
        (if null combs then map (fn x => [x]) outsa
          else maps (fn x => map (fn aa => x :: aa) combs) outsa);
      val init = ([], (Broad a, ([], (l, s))));
    in
      compute_upds_impl bounds init combsa
    end)
                                   end)
                              (upt zero_nata n_ps))
                       (upt zero_nata num_actions)
                else maps (fn a =>
                            let
                              val ins_commited =
                                map_filter
                                  (fn (p, _) =>
                                    (if not (null (nth (nth inb p) a))
                                      then SOME p else NONE))
                                  pairs;
                              val always_commited =
                                less_nat one_nata (size_list ins_commited);
                            in
                              maps (fn p =>
                                     let
                                       val outs = nth (nth outa p) a;
                                     in
                                       (if null outs then []
 else (if not always_commited andalso
            ((equal_lista equal_nat ins_commited [p] orelse
               null ins_commited) andalso
              not (list_ex (fn (q, _) => equal_nata q p) pairs))
        then []
        else let
               val combs = make_combs broadcast bounds automata p a inb;
               val outsa = map (fn aa => (p, aa)) outs;
               val combsa =
                 (if null combs then map (fn x => [x]) outsa
                   else maps (fn x => map (fn aa => x :: aa) combs) outsa);
               val init = ([], (Broad a, ([], (l, s))));
             in
               compute_upds_impl bounds init combsa
             end))
                                     end)
                                (upt zero_nata n_ps)
                            end)
                       (upt zero_nata num_actions))
            end);
        val bin_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_commited broadcast bounds automata l;
              val ina =
                all_actions_by_state broadcast bounds automata num_actions
                  trans_in_map l;
              val out =
                all_actions_by_state broadcast bounds automata num_actions
                  trans_out_map l;
            in
              (if null pairs
                then maps (fn a =>
                            pairs_by_action_impl bounds l s (nth out a)
                              (nth ina a))
                       (bin_actions broadcast num_actions)
                else let
                       val in2 =
                         all_actions_from_vec num_actions trans_in_map pairs;
                       val out2 =
                         all_actions_from_vec num_actions trans_out_map pairs;
                     in
                       maps (fn a =>
                              pairs_by_action_impl bounds l s (nth out a)
                                (nth in2 a))
                         (bin_actions broadcast num_actions) @
                         maps (fn a =>
                                pairs_by_action_impl bounds l s (nth out2 a)
                                  (nth ina a))
                           (bin_actions broadcast num_actions)
                     end)
            end);
        val int_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_commited broadcast bounds automata l;
            in
              (if null pairs then int_trans_from_all_impl l s
                else int_trans_from_vec_impl pairs l s)
            end);
        val trans_impl =
          (fn st =>
            int_trans_impl st @ bin_trans_impl st @ broad_trans_impl st);
        val e_op_impl =
          (fn ai => fn bic => fn bib => fn bia => fn bi =>
            (fn f_ => fn () => f_ ((up_canonical_upd_impl_int m bi m) ()) ())
              (fn x =>
                (fn f_ => fn () => f_
                  ((imp_nfoldli (inv_fun ai) (fn _ => (fn () => true))
                     (fn aia => fn bid =>
                       (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid)
                         ()) ())
                         (fn xa =>
                           repair_pair_impl_int m xa zero_nata
                             (constraint_clk aia)))
                     x)
                  ()) ())
                  (fn xa =>
                    (fn f_ => fn () => f_ ((check_diag_impl_inta m m xa) ()) ())
                      (fn xaa =>
                        (fn f_ => fn () => f_
                          ((if xaa
                             then mtx_set (heap_DBMEntry heap_int) (suc m) xa
                                    (zero_nata, zero_nata) (Lt zero_inta)
                             else imp_nfoldli bib (fn _ => (fn () => true))
                                    (fn aia => fn bid =>
                                      (fn f_ => fn () => f_
((abstra_upd_impl_int m aia bid) ()) ())
(fn xb => repair_pair_impl_int m xb zero_nata (constraint_clk aia)))
                                    xa)
                          ()) ())
                          (fn x_a =>
                            (fn f_ => fn () => f_
                              ((check_diag_impl_inta m m x_a) ()) ())
                              (fn xb =>
                                (fn f_ => fn () => f_
                                  ((if xb
                                     then mtx_set (heap_DBMEntry heap_int)
    (suc m) x_a (zero_nata, zero_nata) (Lt zero_inta)
                                     else (fn f_ => fn () => f_
    ((imp_nfoldli bic (fn _ => (fn () => true))
       (fn xc => fn sigma =>
         reset_canonical_upd_impl_int m sigma m xc zero_inta)
       x_a)
    ()) ())
    (imp_nfoldli (inv_fun bia) (fn _ => (fn () => true))
      (fn aia => fn bid =>
        (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid) ()) ())
          (fn xc => repair_pair_impl_int m xc zero_nata (constraint_clk aia)))))
                                  ()) ())
                                  (fn x_b =>
                                    (fn f_ => fn () => f_
                                      ((check_diag_impl_inta m m x_b) ()) ())
                                      (fn x_c =>
(if x_c
  then mtx_set (heap_DBMEntry heap_int) (suc m) x_b (zero_nata, zero_nata)
         (Lt zero_inta)
  else (fn f_ => fn () => f_
         ((norm_upd_impl (linordered_ab_group_add_int, heap_int) m x_b
            let
              val (l, _) = bia;
            in
              Vector.fromList
                (map (fn c =>
                       maxa linorder_int
                         (image (fn i => sub (sub (sub k_i i) (nth l i)) c)
                           (Set (upt zero_nata n_ps))))
                  (upt zero_nata (plus_nata m one_nata)))
            end
            m)
         ()) ())
         (fw_impl_int m))))))))));
      in
        (fn (a1, a2) =>
          imp_nfoldli (trans_impl a1) (fn _ => (fn () => true))
            (fn xc => fn sigma =>
              let
                val (a1a, (_, (a1c, a2c))) = xc;
              in
                (fn f_ => fn () => f_ ((amtx_copy (heap_DBMEntry heap_int) a2)
                  ()) ())
                  (fn x =>
                    (fn f_ => fn () => f_ ((e_op_impl a1 a1c a1a a2c x) ()) ())
                      (fn xa => (fn () => (op_list_prepend (a2c, xa) sigma))))
              end)
            [])
      end;
    val a_0i =
      (fn f_ => fn () => f_
        ((amtx_dflt (heap_DBMEntry heap_int) (suc m) (suc m) (Le zero_inta)) ())
        ())
        (fn x_a =>
          (fn () =>
            ((l_0, map (the o map_of equal_nat s_0)
                     (upt zero_nata (n_vs bounds))),
              x_a)));
    val fi = (fn xi => (fn () => let
                                   val ((a, b), _) = xi;
                                 in
                                   hd_of_formulai equal_nat formula a b
                                 end));
    val lei =
      (fn ai => fn bi =>
        let
          val (a1, a2) = ai;
          val (a1a, a2a) = bi;
        in
          (if equal_proda (equal_list equal_nat) (equal_list equal_int) a1 a1a
            then dbm_subset_impl
                   (linordered_cancel_ab_monoid_add_int, equal_int, heap_int) m
                   a2 a2a
            else (fn () => false))
        end);
    val emptyi = (fn (_, a) => check_diag_impl_int m a);
    val keyi = (fn a => (fn () => a)) o fst;
    val copyi =
      (fn (a1, a2) =>
        (fn f_ => fn () => f_ ((amtx_copy (heap_DBMEntry heap_int) a2) ()) ())
          (fn x => (fn () => (a1, x))));
    val a =
      (fn a => fn b =>
        (fn n => fn showmstate => fn showshow_stateclock => fn typ => fn x => ()) show_clock a b);
  in
    extract_certificate_impl
      (heap_prod (heap_prod (heap_list heap_nat) (heap_list heap_int))
        (heap_array (typerep_DBMEntry typerep_int)))
      (equal_prod (equal_list equal_nat) (equal_list equal_int),
        hashable_prod (hashable_list hashable_nat) (hashable_list hashable_int),
        heap_prod (heap_list heap_nat) (heap_list heap_int))
      succsi a_0i fi lei emptyi keyi copyi a
  end;

fun list_of_set A_ xs = remdups A_ ((fn Set xs => xs) xs);

fun mk_renaming A_ str xs =
  binda (fold_error
          (fn x => fn m =>
            (if mem_assoc A_ x m then Error ["Duplicate name: " ^ str x]
              else Result ((x, size_list m) :: m)))
          xs [])
    (fn mapping =>
      Result
        let
          val m = map_of A_ mapping;
          val f =
            (fn x =>
              (case m x of NONE => raise Fail "empty case" | SOME v => v));
          val ma = map_of equal_nat (map swap mapping);
          val a =
            (fn x =>
              (case ma x of NONE => raise Fail "empty case" | SOME v => v));
        in
          (f, a)
        end);

fun imp_map f (x :: xs) =
  (fn f_ => fn () => f_ ((f x) ()) ())
    (fn y =>
      (fn f_ => fn () => f_ ((imp_map f xs) ()) ())
        (fn ys => (fn () => (y :: ys))))
  | imp_map f [] = (fn () => []);

fun automaton_of C_ =
  (fn (commited, (trans, inv)) =>
    (Set commited, (Set trans, default_map_of C_ [] inv)));

fun set2_sexp B_ Truea = bot_set
  | set2_sexp B_ (Nota x2) = set2_sexp B_ x2
  | set2_sexp B_ (Anda (x31, x32)) =
    sup_set B_ (set2_sexp B_ x31) (set2_sexp B_ x32)
  | set2_sexp B_ (Ora (x41, x42)) =
    sup_set B_ (set2_sexp B_ x41) (set2_sexp B_ x42)
  | set2_sexp B_ (Implya (x51, x52)) =
    sup_set B_ (set2_sexp B_ x51) (set2_sexp B_ x52)
  | set2_sexp B_ (Eqa (x61, x62)) = bot_set
  | set2_sexp B_ (Leb (x71, x72)) = bot_set
  | set2_sexp B_ (Ltb (x81, x82)) = bot_set
  | set2_sexp B_ (Gea (x91, x92)) = bot_set
  | set2_sexp B_ (Gta (x101, x102)) = bot_set
  | set2_sexp B_ (Loc (x111, x112)) = insert B_ x112 bot_set;

fun set2_formula B_ (EX x1) = set2_sexp B_ x1
  | set2_formula B_ (EG x2) = set2_sexp B_ x2
  | set2_formula B_ (AX x3) = set2_sexp B_ x3
  | set2_formula B_ (AG x4) = set2_sexp B_ x4
  | set2_formula B_ (Leadsto (x51, x52)) =
    sup_set B_ (set2_sexp B_ x51) (set2_sexp B_ x52);

fun clkp_set C_ automata =
  sup_set (equal_prod C_ equal_int)
    (sup_seta (equal_prod C_ equal_int)
      (image
        (fn a =>
          sup_seta (equal_prod C_ equal_int)
            (image (collect_clock_pairs o snd) (Set (snd (snd a)))))
        (Set automata)))
    (sup_seta (equal_prod C_ equal_int)
      (image
        (fn a =>
          sup_seta (equal_prod C_ equal_int)
            (image (fn (_, (_, (g, _))) => collect_clock_pairs g)
              (Set (fst (snd a)))))
        (Set automata)));

fun clk_set C_ automata =
  sup_set C_ (image fst (clkp_set C_ automata))
    (sup_seta C_
      (image
        (fn a =>
          sup_seta C_
            (image (fn (_, (_, (_, (_, (_, (r, _)))))) => Set r)
              (Set (fst (snd a)))))
        (Set automata)));

fun vars_of_sexp C_ (Nota e) = vars_of_sexp C_ e
  | vars_of_sexp C_ (Anda (e1, e2)) =
    sup_set C_ (vars_of_sexp C_ e1) (vars_of_sexp C_ e2)
  | vars_of_sexp C_ (Ora (e1, e2)) =
    sup_set C_ (vars_of_sexp C_ e1) (vars_of_sexp C_ e2)
  | vars_of_sexp C_ (Implya (e1, e2)) =
    sup_set C_ (vars_of_sexp C_ e1) (vars_of_sexp C_ e2)
  | vars_of_sexp C_ (Eqa (i, x)) = insert C_ i bot_set
  | vars_of_sexp C_ (Ltb (i, x)) = insert C_ i bot_set
  | vars_of_sexp C_ (Leb (i, x)) = insert C_ i bot_set
  | vars_of_sexp C_ (Gea (i, x)) = insert C_ i bot_set
  | vars_of_sexp C_ (Gta (i, x)) = insert C_ i bot_set
  | vars_of_sexp C_ Truea = bot_set
  | vars_of_sexp C_ (Loc (v, va)) = bot_set;

fun vars_of_formula C_ (EX phi) = vars_of_sexp C_ phi
  | vars_of_formula C_ (EG phi) = vars_of_sexp C_ phi
  | vars_of_formula C_ (AX phi) = vars_of_sexp C_ phi
  | vars_of_formula C_ (AG phi) = vars_of_sexp C_ phi
  | vars_of_formula C_ (Leadsto (phi, psi)) =
    sup_set C_ (vars_of_sexp C_ phi) (vars_of_sexp C_ psi);

fun check_renaming broadcast bounds renum_acts renum_vars renum_clocks
  renum_states automata phi l_0 s_0 =
  combine
    [assert
       (all_interval_nat
         (fn i =>
           ball (sup_seta equal_nat
                  (image
                    (fn (_, (t, _)) =>
                      sup_seta equal_nat
                        (image
                          (fn (l, (_, (_, (_, (_, (_, la)))))) =>
                            insert equal_nat l (insert equal_nat la bot_set))
                          (Set t)))
                    (Set automata)))
             (fn x =>
               ball (sup_seta equal_nat
                      (image
                        (fn (_, (t, _)) =>
                          sup_seta equal_nat
                            (image
                              (fn (l, (_, (_, (_, (_, (_, la)))))) =>
                                insert equal_nat l
                                  (insert equal_nat la bot_set))
                              (Set t)))
                        (Set automata)))
                 (fn y =>
                   (if equal_nata (renum_states i x) (renum_states i y)
                     then equal_nata x y else true))))
         zero_nata (size_list automata))
       "Location renamings are injective",
      assert
        (inj_on equal_literal equal_nat renum_clocks
          (clk_set equal_literal automata))
        "Clock renaming is injective",
      assert
        (inj_on equal_literal equal_nat renum_vars
          (sup_set equal_literal
            (sup_seta equal_literal
              (image
                (fn s =>
                  sup_seta equal_literal (image (vars_of_bexp equal_literal) s))
                (image (fn t => image (fst o snd) (Set t))
                  (image (fn (_, (t, _)) => t) (Set automata)))))
            (sup_seta equal_literal
              (image
                (fn s =>
                  sup_seta equal_literal
                    (image
                      (fn f =>
                        sup_seta equal_literal
                          (image
                            (fn (x, e) =>
                              sup_set equal_literal
                                (insert equal_literal x bot_set)
                                (vars_of_exp equal_literal e))
                            (Set f)))
                      s))
                (image (fn t => image (fst o snd o snd o snd o snd) (Set t))
                  (image (fn (_, (t, _)) => t) (Set automata)))))))
        "Variable renaming is injective",
      assert
        (inj_on equal_literal equal_nat renum_acts
          (sup_set equal_literal
            (sup_seta equal_literal
              (image
                (fn (_, (t, _)) =>
                  sup_seta equal_literal
                    (image (fn (_, a) => let
   val (_, aa) = a;
   val (_, ab) = aa;
   val (ac, _) = ab;
 in
   set_act equal_literal ac
 end)
                      (Set t)))
                (Set automata)))
            (Set broadcast)))
        "Action renaming is injective",
      assert
        (eq_set (card_UNIV_literal, equal_literal) (image fst (Set bounds))
          (sup_set equal_literal
            (sup_seta equal_literal
              (image
                (fn s =>
                  sup_seta equal_literal (image (vars_of_bexp equal_literal) s))
                (image (fn t => image (fst o snd) (Set t))
                  (image (fn (_, (t, _)) => t) (Set automata)))))
            (sup_seta equal_literal
              (image
                (fn s =>
                  sup_seta equal_literal
                    (image
                      (fn f =>
                        sup_seta equal_literal
                          (image
                            (fn (x, e) =>
                              sup_set equal_literal
                                (insert equal_literal x bot_set)
                                (vars_of_exp equal_literal e))
                            (Set f)))
                      s))
                (image (fn t => image (fst o snd o snd o snd o snd) (Set t))
                  (image (fn (_, (t, _)) => t) (Set automata)))))))
        "Bound set is exactly the variable set",
      assert
        (subset (card_UNIV_nat, equal_nat)
          (sup_seta equal_nat
            (image (fn g => image fst (Set g))
              (Set (map (snd o snd) automata))))
          (sup_seta equal_nat
            (image
              (fn (_, (t, _)) =>
                sup_seta equal_nat
                  (image
                    (fn (l, (_, (_, (_, (_, (_, la)))))) =>
                      insert equal_nat l (insert equal_nat la bot_set))
                    (Set t)))
              (Set automata))))
        "Invariant locations are contained in the location set",
      assert
        (subset (card_UNIV_nat, equal_nat)
          (sup_seta equal_nat (image (Set o fst) (Set automata)))
          (sup_seta equal_nat
            (image
              (fn (_, (t, _)) =>
                sup_seta equal_nat
                  (image
                    (fn (l, (_, (_, (_, (_, (_, la)))))) =>
                      insert equal_nat l (insert equal_nat la bot_set))
                    (Set t)))
              (Set automata))))
        "Broadcast locations are containted in the location set",
      assert
        (equal_nata (size_list l_0) (size_list automata) andalso
          all_interval_nat
            (fn i =>
              bex (fst (snd (nth (fst (snd
(Set broadcast,
  (map (automaton_of equal_nat) automata, map_of equal_literal bounds))))
                              i)))
                (fn (l, (_, (_, (_, (_, (_, la)))))) =>
                  equal_nata (nth l_0 i) l orelse equal_nata (nth l_0 i) la))
            zero_nata (size_list automata))
        "Initial location is in the state set",
      assert
        (eq_set (card_UNIV_literal, equal_literal) (image fst (Set s_0))
          (sup_set equal_literal
            (sup_seta equal_literal
              (image
                (fn s =>
                  sup_seta equal_literal (image (vars_of_bexp equal_literal) s))
                (image (fn t => image (fst o snd) (Set t))
                  (image (fn (_, (t, _)) => t) (Set automata)))))
            (sup_seta equal_literal
              (image
                (fn s =>
                  sup_seta equal_literal
                    (image
                      (fn f =>
                        sup_seta equal_literal
                          (image
                            (fn (x, e) =>
                              sup_set equal_literal
                                (insert equal_literal x bot_set)
                                (vars_of_exp equal_literal e))
                            (Set f)))
                      s))
                (image (fn t => image (fst o snd o snd o snd o snd) (Set t))
                  (image (fn (_, (t, _)) => t) (Set automata)))))))
        "Initial state has the correct domain",
      assert (distinct equal_literal (map fst s_0))
        "Initial state is unambiguous",
      assert
        (subset (card_UNIV_nat, equal_nat) (set2_formula equal_nat phi)
          (sup_seta equal_nat
            (image
              (fn (_, (t, _)) =>
                sup_seta equal_nat
                  (image
                    (fn (l, (_, (_, (_, (_, (_, la)))))) =>
                      insert equal_nat l (insert equal_nat la bot_set))
                    (Set t)))
              (Set automata))))
        "Formula locations are contained in the location set",
      assert
        (subset (card_UNIV_nat, equal_nat) (locs_of_formula equal_nat phi)
          (Set (upt zero_nata (size_list automata))))
        "Formula automata are contained in the automata set",
      assert
        (subset (card_UNIV_literal, equal_literal)
          (vars_of_formula equal_literal phi)
          (sup_set equal_literal
            (sup_seta equal_literal
              (image
                (fn s =>
                  sup_seta equal_literal (image (vars_of_bexp equal_literal) s))
                (image (fn t => image (fst o snd) (Set t))
                  (image (fn (_, (t, _)) => t) (Set automata)))))
            (sup_seta equal_literal
              (image
                (fn s =>
                  sup_seta equal_literal
                    (image
                      (fn f =>
                        sup_seta equal_literal
                          (image
                            (fn (x, e) =>
                              sup_set equal_literal
                                (insert equal_literal x bot_set)
                                (vars_of_exp equal_literal e))
                            (Set f)))
                      s))
                (image (fn t => image (fst o snd o snd o snd o snd) (Set t))
                  (image (fn (_, (t, _)) => t) (Set automata)))))))
        "Variables of the formula are contained in the variable set"];

fun check_precond2 broadcast bounds automata m num_states k l_0 s_0 formula =
  let
    val _ =
      writeln (implode
                (shows_prec_list (show_list (show_list show_nat)) zero_nata k
                  []));
  in
    combine
      [assert
         (all_interval_nat
           (fn i =>
             list_all
               (fn (l, g) =>
                 ball (collect_clock_pairs g)
                   (fn (x, ma) =>
                     less_eq_int ma (int_of_nat (nth (nth (nth k i) l) x))))
               ((snd o snd) (nth automata i)))
           zero_nata (size_list automata))
         "Ceiling invariants",
        assert
          (all_interval_nat
            (fn i =>
              list_all
                (fn (l, (_, (g, _))) =>
                  ball (collect_clock_pairs g)
                    (fn (x, ma) =>
                      less_eq_int ma (int_of_nat (nth (nth (nth k i) l) x))))
                ((fst o snd) (nth automata i)))
            zero_nata (size_list automata))
          "Ceiling transitions",
        assert
          (all_interval_nat
            (fn i =>
              list_all
                (fn (l, (_, (_, (_, (_, (r, la)))))) =>
                  ball (minus_set equal_nat
                         (Set (upt zero_nata (plus_nata m one_nata))) (Set r))
                    (fn c =>
                      less_eq_nat (nth (nth (nth k i) la) c)
                        (nth (nth (nth k i) l) c)))
                ((fst o snd) (nth automata i)))
            zero_nata (size_list automata))
          "Ceiling resets",
        assert (equal_nata (size_list k) (size_list automata)) "Ceiling length",
        assert
          (all_interval_nat
            (fn i => equal_nata (size_list (nth k i)) (num_states i)) zero_nata
            (size_list automata))
          "Ceiling length automata)",
        assert
          (list_all
            (list_all
              (fn xxs => equal_nata (size_list xxs) (plus_nata m one_nata)))
            k)
          "Ceiling length clocks",
        assert
          (all_interval_nat
            (fn i =>
              all_interval_nat
                (fn l => equal_nata (nth (nth (nth k i) l) zero_nata) zero_nata)
                zero_nata (num_states i))
            zero_nata (size_list automata))
          "Ceiling zero clock",
        assert
          (list_all (fn (_, (_, inv)) => distinct equal_nat (map fst inv))
            automata)
          "Unambiguous invariants",
        assert
          (eq_set (card_UNIV_nat, equal_nat) (image fst (Set s_0))
             (image fst (Set bounds)) andalso
            ball (image fst (Set s_0))
              (fn x =>
                less_eq_int (fst (the (map_of equal_nat bounds x)))
                  (the (map_of equal_nat s_0 x)) andalso
                  less_eq_int (the (map_of equal_nat s_0 x))
                    (snd (the (map_of equal_nat bounds x)))))
          "Initial state bounded",
        assert (equal_nata (size_list l_0) (size_list automata))
          "Length of initial state",
        assert
          (all_interval_nat
            (fn i =>
              member equal_nat (nth l_0 i)
                (image fst (Set ((fst o snd) (nth automata i)))))
            zero_nata (size_list automata))
          "Initial state has outgoing transitions",
        assert
          (subset (card_UNIV_nat, equal_nat) (vars_of_formula equal_nat formula)
            (Set (upt zero_nata (n_vs bounds))))
          "Variable set of formula"]
  end;

fun check_precond1 broadcast bounds automata m num_states num_actions =
  combine
    [assert (less_nat zero_nata m) "At least one clock",
      assert (less_nat zero_nata (size_list automata)) "At least one automaton",
      assert
        (all_interval_nat
          (fn i =>
            let
              val (_, (trans, _)) = nth automata i;
            in
              list_all
                (fn (l, (_, (_, (_, (_, (_, la)))))) =>
                  less_nat l (num_states i) andalso less_nat la (num_states i))
                trans
            end)
          zero_nata (size_list automata))
        "Number of states is correct (transitions)",
      assert
        (all_interval_nat
          (fn i => let
                     val a = nth automata i;
                     val (_, aa) = a;
                     val (_, ab) = aa;
                   in
                     list_all (fn (x, _) => less_nat x (num_states i)) ab
                   end)
          zero_nata (size_list automata))
        "Number of states is correct (invariants)",
      assert
        (list_all
          (fn (_, (trans, _)) =>
            list_all
              (fn (_, (_, (_, (_, (f, (_, _)))))) =>
                list_all
                  (fn (x, upd) =>
                    less_nat x (n_vs bounds) andalso
                      ball (vars_of_exp equal_nat upd)
                        (fn i => less_nat i (n_vs bounds)))
                  f)
              trans)
          automata)
        "Variable set bounded (updates)",
      assert
        (list_all
          (fn (_, (trans, _)) =>
            list_all
              (fn (_, (b, (_, (_, (_, (_, _)))))) =>
                ball (vars_of_bexp equal_nat b)
                  (fn i => less_nat i (n_vs bounds)))
              trans)
          automata)
        "Variable set bounded (guards)",
      assert
        (all_interval_nat (fn i => equal_nata (fst (nth bounds i)) i) zero_nata
          (n_vs bounds))
        "Bounds first index",
      assert (list_all (fn a => less_nat a num_actions) broadcast)
        "Broadcast actions bounded",
      assert
        (list_all
          (fn (_, (trans, _)) =>
            list_all
              (fn (_, a) =>
                let
                  val (_, aa) = a;
                  val (_, ab) = aa;
                  val (ac, (_, (_, _))) = ab;
                in
                  pred_act equal_nat (fn ad => less_nat ad num_actions) ac
                end)
              trans)
          automata)
        "Actions bounded (transitions)",
      assert
        (list_all
          (fn (_, (trans, _)) =>
            list_all
              (fn (_, (_, (g, (_, (_, (r, _)))))) =>
                list_all (fn c => less_nat zero_nata c andalso less_eq_nat c m)
                  r andalso
                  ball (collect_clock_pairs g)
                    (fn (c, x) =>
                      less_nat zero_nata c andalso
                        (less_eq_nat c m andalso less_eq_int zero_inta x)))
              trans)
          automata)
        "Clock set bounded (transitions)",
      assert
        (list_all
          (fn (_, a) =>
            let
              val (_, aa) = a;
            in
              list_all
                (fn (_, g) =>
                  ball (collect_clock_pairs g)
                    (fn (c, x) =>
                      less_nat zero_nata c andalso
                        (less_eq_nat c m andalso less_eq_int zero_inta x)))
                aa
            end)
          automata)
        "Clock set bounded (invariants)",
      assert
        (list_all
          (fn (_, (trans, _)) =>
            list_all
              (fn (_, a) =>
                let
                  val (_, aa) = a;
                  val (g, ab) = aa;
                  val (ac, (_, (_, _))) = ab;
                in
                  (case ac
                    of In ad =>
                      (if membera equal_nat broadcast ad then null g else true)
                    | Out _ => true | Sil _ => true)
                end)
              trans)
          automata)
        "Broadcast receivers are unguarded"];

fun check_precond broadcast bounds automata m num_states num_actions k l_0 s_0
  formula =
  combine2 (check_precond1 broadcast bounds automata m num_states num_actions)
    (check_precond2 broadcast bounds automata m num_states k l_0 s_0 formula);

fun map_cconstraint f g xs = map (map_acconstraint f g) xs;

fun renum_cconstraint A_ renum_clocks = map_cconstraint renum_clocks id;

fun renum_reset A_ renum_clocks = map renum_clocks;

fun renum_bexp A_ renum_vars = map_bexp renum_vars;

fun renum_exp A_ renum_vars = map_exp renum_vars;

fun renum_upd A_ renum_vars =
  map (fn (x, upd) => (renum_vars x, renum_exp A_ renum_vars upd));

fun renum_act A_ renum_acts = map_act renum_acts;

fun renum_automaton A_ B_ C_ D_ renum_acts renum_vars renum_clocks renum_states
  i = (fn (commited, (trans, inv)) =>
        let
          val commiteda = map (renum_states i) commited;
          val transa =
            map (fn (l, a) =>
                  let
                    val (b, aa) = a;
                    val (g, ab) = aa;
                    val (ac, (upd, (r, la))) = ab;
                  in
                    (renum_states i l,
                      (renum_bexp B_ renum_vars b,
                        (renum_cconstraint C_ renum_clocks g,
                          (renum_act A_ renum_acts ac,
                            (renum_upd B_ renum_vars upd,
                              (renum_reset C_ renum_clocks r,
                                renum_states i la))))))
                  end)
              trans;
          val inva =
            map (fn (l, g) =>
                  (renum_states i l, renum_cconstraint C_ renum_clocks g))
              inv;
        in
          (commiteda, (transa, inva))
        end);

fun rename_network A_ B_ E_ G_ broadcast bounds automata renum_acts renum_vars
  renum_clocks renum_states =
  let
    val automataa =
      map_index zero_nata
        (renum_automaton A_ B_ G_ E_ renum_acts renum_vars renum_clocks
          renum_states)
        automata;
    val broadcasta = map renum_acts broadcast;
    val boundsa = map (fn (a, b) => let
                                      val (ba, c) = b;
                                    in
                                      (renum_vars a, (ba, c))
                                    end)
                    bounds;
  in
    (broadcasta, (automataa, boundsa))
  end;

fun do_rename_mc C_ E_ F_ G_ f dc broadcast bounds automata k l_0 s_0 formula m
  num_states num_actions renum_acts renum_vars renum_clocks renum_states
  inv_renum_states inv_renum_vars inv_renum_clocks =
  let
    val _ = writeln "Checking renaming";
    val formulaa = (if dc then EX (Nota Truea) else formula);
    val renaming_valid =
      check_renaming broadcast bounds renum_acts renum_vars renum_clocks
        renum_states automata formulaa l_0 s_0;
    val _ = writeln "Renaming network";
    val (broadcasta, (automataa, boundsa)) =
      rename_network countable_literal countable_literal countable_nat
        countable_literal broadcast bounds automata renum_acts renum_vars
        renum_clocks renum_states;
    val _ = writeln "Automata after renaming";
    val _ =
      map (fn a =>
            writeln (implode
                      (shows_prec_prod (show_list show_nat)
                        (show_prod
                          (show_list
                            (show_prod show_nat
                              (show_prod (show_bexp show_nat show_int)
                                (show_prod
                                  (show_list
                                    (show_acconstraint show_nat show_int))
                                  (show_prod (show_act show_nat)
                                    (show_prod
                                      (show_list
(show_prod show_nat (show_exp show_nat show_int)))
                                      (show_prod (show_list show_nat)
show_nat)))))))
                          (show_list
                            (show_prod show_nat
                              (show_list
                                (show_acconstraint show_nat show_int)))))
                        zero_nata a [])))
        automataa;
    val _ = writeln "Renaming formula";
    val formulab =
      (if dc then EX (Nota Truea)
        else map_formula renum_states renum_vars id formulaa);
    val _ = writeln "Renaming state";
    val l_0a = map_index zero_nata renum_states l_0;
    val s_0a = map (fn (x, a) => (renum_vars x, a)) s_0;
    val show_clock = (fn x => shows_prec G_ zero_nata x []) o inv_renum_clocks;
    val show_statea = show_state E_ F_ C_ inv_renum_states inv_renum_vars;
  in
    (if is_result renaming_valid
      then let
             val _ = writeln "Checking preconditions";
             val r =
               check_precond broadcasta boundsa automataa m num_states
                 num_actions k l_0a s_0a formulab;
             val _ =
               (case r of Result _ => [()]
                 | Error es =>
                   let
                     val _ =
                       writeln "The following pre-conditions were not satisified";
                   in
                     map (fn a => writeln a) es
                   end);
             val _ = writeln "Running precond_mc";
             val a =
               f show_clock show_statea broadcasta boundsa automataa m
                 num_states
                 num_actions
                 k
                 l_0a
                 s_0a
                 formulab;
           in
             SOME a
           end
      else let
             val _ =
               writeln "The following conditions on the renaming were not satisfied:";
             val _ = map (fn a => writeln a) (the_errors renaming_valid);
           in
             NONE
           end)
  end;

fun mk_renaminga (A1_, A2_) xs =
  mk_renaming A1_ (implode o (fn x => shows_prec A2_ zero_nata x [])) xs;

fun show_lit A_ = implode o (fn x => shows_prec A_ zero_nata x []);

fun show_str A_ = implode o (fn x => shows_prec A_ zero_nata x []);

fun extend_domain A_ (B1_, B2_) m d n =
  let
    val (_, xs) =
      fold (fn x => fn (i, xs) =>
             (if membera A_ d x
               then (plus B2_ i (one B1_), (x, plus B2_ i (one B1_)) :: xs)
               else (i, xs)))
        d (n, []);
    val ma = map_of A_ xs;
  in
    (fn x => (if membera A_ d x then the (ma x) else m x))
  end;

fun action_set D_ automata broadcast =
  sup_set D_
    (sup_seta D_
      (image
        (fn (_, (trans, _)) =>
          sup_seta D_
            (image (fn (_, a) => let
                                   val (_, aa) = a;
                                   val (_, ab) = aa;
                                   val (ac, (_, (_, _))) = ab;
                                 in
                                   set_act D_ ac
                                 end)
              (Set trans)))
        (Set automata)))
    (Set broadcast);

fun loc_set A_ automata p =
  sup_seta A_
    (image
      (fn (l, (_, (_, (_, (_, (_, la)))))) =>
        insert A_ l (insert A_ la bot_set))
      (Set (fst (snd (nth automata p)))));

fun make_renaming (A1_, A2_) =
  (fn broadcast => fn automata => fn _ =>
    let
      val action_seta =
        list_of_set equal_literal (action_set equal_literal automata broadcast);
      val clk_seta = list_of_set equal_literal (clk_set equal_literal automata);
      val loc_seta = (fn i => list_of_set A1_ (loc_set A1_ automata i));
      val loc_setaa =
        sup_seta A1_
          (image
            (fn (_, (t, _)) =>
              sup_seta A1_
                (image
                  (fn (l, (_, (_, (_, (_, (_, la)))))) =>
                    insert A1_ l (insert A1_ la bot_set))
                  (Set t)))
            (Set automata));
      val loc_set_diff =
        (fn i =>
          list_of_set A1_ (minus_set A1_ loc_setaa (loc_set A1_ automata i)));
      val _ = list_of_set A1_ loc_setaa;
      val var_set =
        list_of_set equal_literal
          (sup_set equal_literal
            (sup_seta equal_literal
              (image
                (fn s =>
                  sup_seta equal_literal (image (vars_of_bexp equal_literal) s))
                (image (fn t => image (fst o snd) (Set t))
                  (image (fn (_, (t, _)) => t) (Set automata)))))
            (sup_seta equal_literal
              (image
                (fn s =>
                  sup_seta equal_literal
                    (image
                      (fn f =>
                        sup_seta equal_literal
                          (image
                            (fn (x, e) =>
                              sup_set equal_literal
                                (insert equal_literal x bot_set)
                                (vars_of_exp equal_literal e))
                            (Set f)))
                      s))
                (image (fn t => image (fst o snd o snd o snd o snd) (Set t))
                  (image (fn (_, (t, _)) => t) (Set automata))))));
      val n_ps = size_list automata;
      val num_actions = size_list action_seta;
      val m = size_list (remdups equal_literal clk_seta);
      val num_states_list =
        map (fn i => size_list (remdups A1_ (loc_seta i))) (upt zero_nata n_ps);
      val num_states = nth num_states_list;
      val mk_renamingb = mk_renaming equal_literal (fn x => x);
    in
      binda (combine2 (mk_renamingb action_seta)
              (combine2 (mk_renamingb clk_seta) (mk_renamingb var_set)))
        (fn (a, b) =>
          let
            val (renum_acts, _) = a;
          in
            (fn (aa, ba) =>
              let
                val (renum_clocks, inv_renum_clocks) = aa;
              in
                (fn (renum_vars, inv_renum_vars) =>
                  let
                    val renum_clocksa = suc o renum_clocks;
                    val inv_renum_clocksa =
                      (fn c =>
                        (if equal_nata c zero_nata then "0"
                          else inv_renum_clocks (minus_nat c one_nata)));
                  in
                    binda (combine_map
                            (fn i => mk_renaminga (A1_, A2_) (loc_seta i))
                            (upt zero_nata n_ps))
                      (fn renum_states_list =>
                        let
                          val renum_states_lista = map fst renum_states_list;
                          val renum_states_listaa =
                            map_index zero_nata
                              (fn i => fn ma =>
                                extend_domain A1_ (one_nat, plus_nat) ma
                                  (loc_set_diff i) (size_list (loc_seta i)))
                              renum_states_lista;
                          val renum_states = nth renum_states_listaa;
                          val inv_renum_states =
                            nth (map snd renum_states_list);
                        in
                          Result
                            (m, (num_states,
                                  (num_actions,
                                    (renum_acts,
                                      (renum_vars,
(renum_clocksa,
  (renum_states, (inv_renum_states, (inv_renum_vars, inv_renum_clocksa)))))))))
                        end)
                  end)
              end
                ba)
          end
            b)
    end);

fun split_size f width uu acc [] = [acc]
  | split_size f width n acc (x :: xs) =
    let
      val k = f x;
    in
      (if less_nat n width then split_size f width (plus_nata n k) (x :: acc) xs
        else acc :: split_size f width k [x] xs)
    end;

fun split_k k xs =
  let
    val width =
      divide_nat (sum_list monoid_add_nat (map (size_list o snd) xs)) k;
    val widtha =
      (if equal_nata (modulo_nat (size_list xs) k) zero_nata then width
        else plus_nata width one_nata);
  in
    split_size (size_list o snd) widtha zero_nata [] xs
  end;

fun split_eq_width n = split_size (fn _ => one_nata) n zero_nata [];

fun split_ka k xs =
  let
    val width = divide_nat (size_list xs) k;
    val widtha =
      (if equal_nata (modulo_nat (size_list xs) k) zero_nata then width
        else plus_nata width one_nata);
  in
    split_eq_width widtha xs
  end;

fun simple_Network_Impl_nat broadcast bounds automata m num_states num_actions =
  less_nat zero_nata m andalso
    (less_nat zero_nata (size_list automata) andalso
      all_interval_nat
        (fn i =>
          let
            val (_, (trans, _)) = nth automata i;
          in
            list_all
              (fn (l, (_, (_, (_, (_, (_, la)))))) =>
                less_nat l (num_states i) andalso less_nat la (num_states i))
              trans
          end)
        zero_nata (size_list automata)) andalso
    (all_interval_nat
       (fn i => let
                  val a = nth automata i;
                  val (_, aa) = a;
                  val (_, ab) = aa;
                in
                  list_all (fn (x, _) => less_nat x (num_states i)) ab
                end)
       zero_nata (size_list automata) andalso
      (list_all
         (fn (_, (trans, _)) =>
           list_all
             (fn (_, (_, (_, (_, (f, (_, _)))))) =>
               list_all
                 (fn (x, upd) =>
                   less_nat x (n_vs bounds) andalso
                     ball (vars_of_exp equal_nat upd)
                       (fn i => less_nat i (n_vs bounds)))
                 f)
             trans)
         automata andalso
        list_all
          (fn (_, (trans, _)) =>
            list_all
              (fn (_, (b, (_, (_, (_, (_, _)))))) =>
                ball (vars_of_bexp equal_nat b)
                  (fn i => less_nat i (n_vs bounds)))
              trans)
          automata)) andalso
    (all_interval_nat (fn i => equal_nata (fst (nth bounds i)) i) zero_nata
       (n_vs bounds) andalso
       (list_all (fn a => less_nat a num_actions) broadcast andalso
         list_all
           (fn (_, (trans, _)) =>
             list_all
               (fn (_, a) =>
                 let
                   val (_, aa) = a;
                   val (_, ab) = aa;
                   val (ac, (_, (_, _))) = ab;
                 in
                   pred_act equal_nat (fn ad => less_nat ad num_actions) ac
                 end)
               trans)
           automata) andalso
      (list_all
         (fn (_, (trans, _)) =>
           list_all
             (fn (_, (_, (g, (_, (_, (r, _)))))) =>
               list_all (fn c => less_nat zero_nata c andalso less_eq_nat c m)
                 r andalso
                 ball (collect_clock_pairs g)
                   (fn (c, x) =>
                     less_nat zero_nata c andalso
                       (less_eq_nat c m andalso less_eq_int zero_inta x)))
             trans)
         automata andalso
        (list_all
           (fn (_, a) =>
             let
               val (_, aa) = a;
             in
               list_all
                 (fn (_, g) =>
                   ball (collect_clock_pairs g)
                     (fn (c, x) =>
                       less_nat zero_nata c andalso
                         (less_eq_nat c m andalso less_eq_int zero_inta x)))
                 aa
             end)
           automata andalso
          list_all
            (fn (_, (trans, _)) =>
              list_all
                (fn (_, a) =>
                  let
                    val (_, aa) = a;
                    val (g, ab) = aa;
                    val (ac, (_, (_, _))) = ab;
                  in
                    (case ac
                      of In ad =>
                        (if membera equal_nat broadcast ad then null g
                          else true)
                      | Out _ => true | Sil _ => true)
                  end)
                trans)
            automata)));

fun split_kb k xs =
  let
    val width =
      divide_nat (sum_list monoid_add_nat (map (size_list o snd) xs)) k;
    val widtha =
      (if equal_nata (modulo_nat (size_list xs) k) zero_nata then width
        else plus_nata width one_nata);
  in
    map (map fst) (split_size (size_list o snd) widtha zero_nata [] xs)
  end;

fun map_of_debug (A1_, A2_) m =
  let
    val ma = map_of A1_ m;
  in
    (fn x =>
      (case ma x of NONE => let
                              val _ = writeln ("Key error: " ^ show_lit A2_ x);
                            in
                              NONE
                            end
        | SOME a => SOME a))
  end;

fun print_errors es =
  (fn f_ => fn () => f_ ((fold_map print_line_impl es) ()) ())
    (fn _ => (fn () => ()));

fun abstr_repair_impl_int x =
  (fn m => fn ai =>
    imp_nfoldli ai (fn _ => (fn () => true))
      (fn aia => fn bi =>
        (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bi) ()) ())
          (fn xa => repair_pair_impl_int m xa zero_nata (constraint_clk aia))))
    x;

fun e_op_impl x =
  (fn m => fn l_inv => fn r => fn g => fn l_inva => fn ma =>
    (fn f_ => fn () => f_ ((up_canonical_upd_impl_int m ma m) ()) ())
      (fn m1 =>
        (fn f_ => fn () => f_ ((abstr_repair_impl_int m l_inv m1) ()) ())
          (fn m2 =>
            (fn f_ => fn () => f_ ((check_diag_impl_int m m2) ()) ())
              (fn is_empty1 =>
                (fn f_ => fn () => f_
                  ((if is_empty1
                     then mtx_set (heap_DBMEntry heap_int) (suc m) m2
                            (zero_nata, zero_nata) (Lt zero_inta)
                     else abstr_repair_impl_int m g m2)
                  ()) ())
                  (fn m3 =>
                    (fn f_ => fn () => f_ ((check_diag_impl_int m m3) ()) ())
                      (fn is_empty3 =>
                        (if is_empty3
                          then mtx_set (heap_DBMEntry heap_int) (suc m) m3
                                 (zero_nata, zero_nata) (Lt zero_inta)
                          else (fn f_ => fn () => f_
                                 ((imp_nfoldli r (fn _ => (fn () => true))
                                    (fn xc => fn sigma =>
                                      reset_canonical_upd_impl_int m sigma m xc
zero_inta)
                                    m3)
                                 ()) ())
                                 (abstr_repair_impl_int m l_inva))))))))
    x;

fun certify_unreachable_impl2 (A1_, A2_, A3_) B_ fi pi copyi lei l_0i s_0i
  succsi splitteri l_list m_table =
  let
    val _ = Timing.start_timer ();
    val b1 =
      (fn f => f ()) ((fn f_ => fn () => f_ (m_table ()) ())
                       (fn m =>
                         (fn f_ => fn () => f_ (l_0i ()) ())
                           (fn x =>
                             (fn f_ => fn () => f_
                               ((imp_nfoldli l_list
                                  (fn sigma => (fn () => (not sigma)))
                                  (fn xb => fn _ => (fn () => (eq A1_ xb x)))
                                  false)
                               ()) ())
                               (fn xa =>
                                 (fn f_ => fn () => f_ (l_0i ()) ())
                                   (fn xaa =>
                                     (fn f_ => fn () => f_ (s_0i ()) ())
                                       (fn xb =>
 (fn f_ => fn () => f_ ((pi (xaa, xb)) ()) ())
   (fn x_a =>
     (fn f_ => fn () => f_ (l_0i ()) ())
       (fn xab =>
         (fn f_ => fn () => f_
           ((hms_lookup (ht_lookup (A1_, A2_, A3_) (heap_list B_))
              (heap_map copyi) xab m)
           ()) ())
           (fn a =>
             (case a of NONE => (fn () => false)
               | SOME x_d =>
                 (fn f_ => fn () => f_
                   ((imp_nfoldli x_d (fn sigma => (fn () => (not sigma)))
                      (fn xg => fn _ =>
                        (fn f_ => fn () => f_ (s_0i ()) ())
                          (fn x_h => lei x_h xg))
                      false)
                   ()) ())
                   (fn x_f =>
                     (fn f_ => fn () => f_
                       ((imp_nfoldli l_list (fn aa => (fn () => aa))
                          (fn xba => fn _ =>
                            (fn f_ => fn () => f_
                              ((hms_lookup
                                 (ht_lookup (A1_, A2_, A3_) (heap_list B_))
                                 (heap_map copyi) xba m)
                              ()) ())
                              (fn aa =>
                                (case aa of NONE => (fn () => true)
                                  | SOME x_e =>
                                    imp_nfoldli x_e (fn ab => (fn () => ab))
                                      (fn xh => fn _ => pi (xba, xh)) true)))
                          true)
                       ()) ())
                       (fn x_g =>
                         (fn f_ => fn () => f_
                           ((print_check_impl "Start state is in state list" xa)
                           ()) ())
                           (fn _ =>
                             (fn f_ => fn () => f_
                               ((print_check_impl
                                  "Start state fulfills property" x_a)
                               ()) ())
                               (fn _ =>
                                 (fn f_ => fn () => f_
                                   ((print_check_impl "Start state is subsumed"
                                      x_f)
                                   ()) ())
                                   (fn _ =>
                                     (fn f_ => fn () => f_
                                       ((print_check_impl "Check property" x_g)
                                       ()) ())
                                       (fn _ =>
 (fn () => (xa andalso (x_a andalso (x_f andalso x_g))))))))))))))))))));
    val _ = Timing.save_time "Time for checking basic preconditions";
    val _ = Timing.start_timer ();
    val xs =
      run_map_heap
        (fn li =>
          (fn f_ => fn () => f_ (m_table ()) ())
            (fn m =>
              imp_nfoldli li (fn a => (fn () => a))
                (fn xa => fn _ =>
                  (fn f_ => fn () => f_
                    ((hms_lookup (ht_lookup (A1_, A2_, A3_) (heap_list B_))
                       (heap_map copyi) xa m)
                    ()) ())
                    (fn a =>
                      (case a of NONE => (fn () => true)
                        | SOME x_c =>
                          (fn f_ => fn () => f_ ((succsi xa x_c) ()) ())
                            (fn x_d =>
                              imp_nfoldli x_d (fn aa => (fn () => aa))
                                (fn xg => fn _ =>
                                  let
                                    val (a1, a2) = xg;
                                  in
                                    (if op_list_is_empty a2 then (fn () => true)
                                      else (fn f_ => fn () => f_
     ((hms_lookup (ht_lookup (A1_, A2_, A3_) (heap_list B_)) (heap_map copyi) a1
        m)
     ()) ())
     (fn aa =>
       (case aa of NONE => (fn () => false)
         | SOME x_k =>
           imp_nfoldli a2 (fn ab => (fn () => ab))
             (fn xn => fn _ =>
               imp_nfoldli x_k (fn sigma => (fn () => (not sigma)))
                 (fn xp => fn _ => lei xn xp) false)
             true)))
                                  end)
                                true))))
                true))
        (splitteri l_list);
    val b2 = list_all id xs;
    val _ = Timing.save_time "Time for state space invariant check";
    val _ = print_check "State set invariant check" b2;
    val _ = Timing.start_timer ();
    val b3 =
      (fn f => f ()) ((fn f_ => fn () => f_ (m_table ()) ())
                       (check_final_impl (A1_, A2_, A3_) B_ fi copyi l_list));
    val _ = Timing.save_time "Time to check final state predicate";
    val _ = print_check "All check: " (b1 andalso b2);
    val _ = print_check "Target property check: " b3;
  in
    b1 andalso (b2 andalso b3)
  end;

fun array_all2 n p asa bs =
  all_interval_nat (fn i => p (sub asa i) (sub bs i)) zero_nata n;

fun succs_impl broadcast bounds automata m num_actions =
  let
    val trans_impl =
      let
        val trans_mapa = trans_map automata;
        val trans_i_map =
          (fn i => fn j =>
            map_filter
              (fn (b, a) =>
                let
                  val (g, aa) = a;
                  val (ab, (ma, l)) = aa;
                in
                  (case ab of In _ => NONE | Out _ => NONE
                    | Sil ac => SOME (b, (g, (ac, (ma, l)))))
                end)
              (trans_mapa i j));
        val int_trans_from_loc_impl =
          (fn p => fn l => fn la => fn s =>
            let
              val a = trans_i_map p l;
            in
              map_filter
                (fn (b, aa) =>
                  let
                    val (g, ab) = aa;
                    val (ac, (f, (r, lb))) = ab;
                    val sa = mk_updsi s f;
                  in
                    (if bvali (equal_int, linorder_int) s b andalso
                          check_boundedi bounds sa
                      then SOME (g, (Internal ac,
                                      (r, (list_update la p lb, sa))))
                      else NONE)
                  end)
                a
            end);
        val int_trans_from_vec_impl =
          (fn pairs => fn l => fn s =>
            maps (fn (p, la) => int_trans_from_loc_impl p la l s) pairs);
        val int_trans_from_all_impl =
          (fn l => fn s =>
            maps (fn p => int_trans_from_loc_impl p (nth l p) l s)
              (upt zero_nata (size_list automata)));
        val trans_out_map =
          (fn i => fn j =>
            map_filter
              (fn (b, a) =>
                let
                  val (g, aa) = a;
                  val (ab, (ma, l)) = aa;
                in
                  (case ab of In _ => NONE
                    | Out ac => SOME (b, (g, (ac, (ma, l)))) | Sil _ => NONE)
                end)
              (trans_mapa i j));
        val trans_in_map =
          (fn i => fn j =>
            map_filter
              (fn (b, a) =>
                let
                  val (g, aa) = a;
                  val (ab, (ma, l)) = aa;
                in
                  (case ab of In ac => SOME (b, (g, (ac, (ma, l))))
                    | Out _ => NONE | Sil _ => NONE)
                end)
              (trans_mapa i j));
        val trans_out_broad_grouped =
          (fn i => fn j =>
            actions_by_statea num_actions
              (map_filter
                (fn (b, a) =>
                  let
                    val (g, aa) = a;
                    val (ab, (ma, l)) = aa;
                  in
                    (case ab of In _ => NONE
                      | Out ac =>
                        (if membera equal_nat broadcast ac
                          then SOME (b, (g, (ac, (ma, l)))) else NONE)
                      | Sil _ => NONE)
                  end)
                (trans_mapa i j)));
        val trans_in_broad_grouped =
          (fn i => fn j =>
            actions_by_statea num_actions
              (map_filter
                (fn (b, a) =>
                  let
                    val (g, aa) = a;
                    val (ab, (ma, l)) = aa;
                  in
                    (case ab
                      of In ac =>
                        (if membera equal_nat broadcast ac
                          then SOME (b, (g, (ac, (ma, l)))) else NONE)
                      | Out _ => NONE | Sil _ => NONE)
                  end)
                (trans_mapa i j)));
        val broad_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_commited broadcast bounds automata l;
              val ina =
                map (fn p => trans_in_broad_grouped p (nth l p))
                  (upt zero_nata (size_list automata));
              val out =
                map (fn p => trans_out_broad_grouped p (nth l p))
                  (upt zero_nata (size_list automata));
              val inb =
                map (map (filter
                           (fn (b, _) => bvali (equal_int, linorder_int) s b)))
                  ina;
              val outa =
                map (map (filter
                           (fn (b, _) => bvali (equal_int, linorder_int) s b)))
                  out;
            in
              (if null pairs
                then maps (fn a =>
                            maps (fn p =>
                                   let
                                     val outs = nth (nth outa p) a;
                                   in
                                     (if null outs then []
                                       else let
      val combs = make_combs broadcast bounds automata p a inb;
      val outsa = map (fn aa => (p, aa)) outs;
      val combsa =
        (if null combs then map (fn x => [x]) outsa
          else maps (fn x => map (fn aa => x :: aa) combs) outsa);
      val init = ([], (Broad a, ([], (l, s))));
    in
      compute_upds_impl bounds init combsa
    end)
                                   end)
                              (upt zero_nata (size_list automata)))
                       (upt zero_nata num_actions)
                else maps (fn a =>
                            let
                              val ins_commited =
                                map_filter
                                  (fn (p, _) =>
                                    (if not (null (nth (nth inb p) a))
                                      then SOME p else NONE))
                                  pairs;
                              val always_commited =
                                less_nat one_nata (size_list ins_commited);
                            in
                              maps (fn p =>
                                     let
                                       val outs = nth (nth outa p) a;
                                     in
                                       (if null outs then []
 else (if not always_commited andalso
            ((equal_lista equal_nat ins_commited [p] orelse
               null ins_commited) andalso
              not (list_ex (fn (q, _) => equal_nata q p) pairs))
        then []
        else let
               val combs = make_combs broadcast bounds automata p a inb;
               val outsa = map (fn aa => (p, aa)) outs;
               val combsa =
                 (if null combs then map (fn x => [x]) outsa
                   else maps (fn x => map (fn aa => x :: aa) combs) outsa);
               val init = ([], (Broad a, ([], (l, s))));
             in
               compute_upds_impl bounds init combsa
             end))
                                     end)
                                (upt zero_nata (size_list automata))
                            end)
                       (upt zero_nata num_actions))
            end);
        val bin_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_commited broadcast bounds automata l;
              val ina =
                all_actions_by_state broadcast bounds automata num_actions
                  trans_in_map l;
              val out =
                all_actions_by_state broadcast bounds automata num_actions
                  trans_out_map l;
            in
              (if null pairs
                then maps (fn a =>
                            pairs_by_action_impl bounds l s (nth out a)
                              (nth ina a))
                       (bin_actions broadcast num_actions)
                else let
                       val in2 =
                         all_actions_from_vec num_actions trans_in_map pairs;
                       val out2 =
                         all_actions_from_vec num_actions trans_out_map pairs;
                     in
                       maps (fn a =>
                              pairs_by_action_impl bounds l s (nth out a)
                                (nth in2 a))
                         (bin_actions broadcast num_actions) @
                         maps (fn a =>
                                pairs_by_action_impl bounds l s (nth out2 a)
                                  (nth ina a))
                           (bin_actions broadcast num_actions)
                     end)
            end);
        val int_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_commited broadcast bounds automata l;
            in
              (if null pairs then int_trans_from_all_impl l s
                else int_trans_from_vec_impl pairs l s)
            end);
      in
        (fn st => int_trans_impl st @ bin_trans_impl st @ broad_trans_impl st)
      end;
  in
    (fn n_ps => fn invs =>
      let
        val inv_fun =
          (fn (l, _) =>
            maps (fn i => sub (sub invs i) (nth l i)) (upt zero_nata n_ps));
        val e_op_impla =
          (fn l => fn r => fn g => fn la =>
            e_op_impl m (inv_fun l) r g (inv_fun la));
      in
        (fn l_s => fn ma =>
          (if null ma then (fn () => [])
            else imp_nfoldli (trans_impl l_s) (fn _ => (fn () => true))
                   (fn c => fn sigma =>
                     let
                       val (g, (_, (r, l_sa))) = c;
                     in
                       (fn f_ => fn () => f_
                         ((heap_map (amtx_copy (heap_DBMEntry heap_int)) ma) ())
                         ())
                         (fn maa =>
                           (fn f_ => fn () => f_
                             ((imp_nfoldli maa (fn _ => (fn () => true))
                                (fn xb => fn sigmaa =>
                                  (fn f_ => fn () => f_
                                    ((e_op_impla l_s r g l_sa xb) ()) ())
                                    (fn x_c =>
                                      (fn f_ => fn () => f_
((check_diag_impl_int m x_c) ()) ())
(fn x_e => (fn () => (if x_e then sigmaa else op_list_prepend x_c sigmaa)))))
                                [])
                             ()) ())
                             (fn ms =>
                               (fn () => (op_list_prepend (l_sa, ms) sigma))))
                     end)
                   []))
      end)
  end;

fun check_subsumed (A1_, A2_, A3_) n xs i m =
  (fn f_ => fn () => f_
    ((imp_nfoldli xs (fn (_, b) => (fn () => (not b)))
       (fn ma => fn (j, b) =>
         (if equal_inta i j then (fn () => (plus_inta j one_int, b))
           else (fn f_ => fn () => f_ ((dbm_subset_impl (A1_, A2_, A3_) n m ma)
                  ()) ())
                  (fn ba =>
                    (if ba then (fn () => (j, true))
                      else (fn () => (plus_inta j one_int, false))))))
       (zero_inta, false))
    ()) ())
    (fn (_, a) => (fn () => a));

fun fw_upd_impl_inta x =
  (fn n => fn ai => fn bib => fn bia => fn bi =>
    (fn f_ => fn () => f_
      ((mtx_get (heap_DBMEntry heap_int) (suc n) ai (bia, bi)) ()) ())
      (fn xa =>
        (fn f_ => fn () => f_
          ((mtx_get (heap_DBMEntry heap_int) (suc n) ai (bia, bib)) ()) ())
          (fn xaa =>
            (fn f_ => fn () => f_
              ((mtx_get (heap_DBMEntry heap_int) (suc n) ai (bib, bi)) ()) ())
              (fn xb =>
                mtx_set (heap_DBMEntry heap_int) (suc n) ai (bia, bi)
                  (min_int_entry xa (dbm_add_int xaa xb))))))
    x;

fun fw_impl_inta x =
  (fn n =>
    imp_for_inta zero_nata (plus_nata n one_nata)
      (fn xb =>
        imp_for_inta zero_nata (plus_nata n one_nata)
          (fn xd =>
            imp_for_inta zero_nata (plus_nata n one_nata)
              (fn xf => fn sigma => fw_upd_impl_inta n sigma xb xd xf))))
    x;

fun imp_filter_index p xs =
  (fn f_ => fn () => f_
    ((imp_nfoldli xs (fn _ => (fn () => true))
       (fn x => fn (i, xsa) =>
         (fn f_ => fn () => f_ ((p i x) ()) ())
           (fn b =>
             (fn () => (plus_nata i one_nata, (if b then x :: xsa else xsa)))))
       (zero_nata, []))
    ()) ())
    (fn (_, xsa) => (fn () => (rev xsa)));

fun filter_dbm_list (A1_, A2_, A3_) n xs =
  imp_filter_index
    (fn x => fn m =>
      (fn f_ => fn () => f_
        ((check_subsumed (A1_, A2_, A3_) n xs (int_of_nat x) m) ()) ())
        (fn b => (fn () => (not b))))
    xs;

fun array_freeze A_ a = (fn () => Array.vector a);

fun make_string (A1_, A2_) show_clock show_num e i j =
  let
    val ia =
      (if less_nat zero_nata i then show_clock i
        else [Chara (false, false, false, false, true, true, false, false)]);
    val ja =
      (if less_nat zero_nata j then show_clock j
        else [Chara (false, false, false, false, true, true, false, false)]);
  in
    (case e
      of Le a =>
        ia @ [Chara (false, false, false, false, false, true, false, false),
               Chara (true, false, true, true, false, true, false, false),
               Chara (false, false, false, false, false, true, false, false)] @
               ja @ [Chara (false, false, false, false, false, true, false,
                             false),
                      Chara (false, false, true, true, true, true, false,
                              false),
                      Chara (true, false, true, true, true, true, false, false),
                      Chara (false, false, false, false, false, true, false,
                              false)] @
                      show_num a
      | Lt a =>
        ia @ [Chara (false, false, false, false, false, true, false, false),
               Chara (true, false, true, true, false, true, false, false),
               Chara (false, false, false, false, false, true, false, false)] @
               ja @ [Chara (false, false, false, false, false, true, false,
                             false),
                      Chara (false, false, true, true, true, true, false,
                              false),
                      Chara (false, false, false, false, false, true, false,
                              false)] @
                      show_num a
      | INF =>
        ia @ [Chara (false, false, false, false, false, true, false, false),
               Chara (true, false, true, true, false, true, false, false),
               Chara (false, false, false, false, false, true, false, false)] @
               ja @ [Chara (false, false, false, false, false, true, false,
                             false),
                      Chara (false, false, true, true, true, true, false,
                              false),
                      Chara (false, false, false, false, false, true, false,
                              false),
                      Chara (true, false, false, true, false, true, true,
                              false),
                      Chara (false, true, true, true, false, true, true, false),
                      Chara (false, true, true, false, false, true, true,
                              false)])
  end;

fun simple_Network_Impl_nat_ceiling_start_state_axioms broadcast bounds automata
  m num_states k l_0 s_0 formula =
  all_interval_nat
    (fn i =>
      list_all
        (fn (l, g) =>
          ball (collect_clock_pairs g)
            (fn (x, ma) =>
              less_eq_int ma (int_of_nat (nth (nth (nth k i) l) x))))
        ((snd o snd) (nth automata i)))
    zero_nata (size_list automata) andalso
    (all_interval_nat
       (fn i =>
         list_all
           (fn (l, (_, (g, _))) =>
             ball (collect_clock_pairs g)
               (fn (x, ma) =>
                 less_eq_int ma (int_of_nat (nth (nth (nth k i) l) x))))
           ((fst o snd) (nth automata i)))
       zero_nata (size_list automata) andalso
      all_interval_nat
        (fn i =>
          list_all
            (fn (l, (_, (_, (_, (_, (r, la)))))) =>
              ball (minus_set equal_nat
                     (Set (upt zero_nata (plus_nata m one_nata))) (Set r))
                (fn c =>
                  less_eq_nat (nth (nth (nth k i) la) c)
                    (nth (nth (nth k i) l) c)))
            ((fst o snd) (nth automata i)))
        zero_nata (size_list automata)) andalso
    (equal_nata (size_list k) (size_list automata) andalso
      (all_interval_nat
         (fn i => equal_nata (size_list (nth k i)) (num_states i)) zero_nata
         (size_list automata) andalso
        list_all
          (list_all
            (fn xxs => equal_nata (size_list xxs) (plus_nata m one_nata)))
          k)) andalso
    (all_interval_nat
       (fn i =>
         all_interval_nat
           (fn l => equal_nata (nth (nth (nth k i) l) zero_nata) zero_nata)
           zero_nata (num_states i))
       zero_nata (size_list automata) andalso
       (list_all (fn (_, (_, inv)) => distinct equal_nat (map fst inv))
          automata andalso
         (eq_set (card_UNIV_nat, equal_nat) (image fst (Set s_0))
            (image fst (Set bounds)) andalso
           ball (image fst (Set s_0))
             (fn x =>
               less_eq_int (fst (the (map_of equal_nat bounds x)))
                 (the (map_of equal_nat s_0 x)) andalso
                 less_eq_int (the (map_of equal_nat s_0 x))
                   (snd (the (map_of equal_nat bounds x)))))) andalso
      (equal_nata (size_list l_0) (size_list automata) andalso
        (all_interval_nat
           (fn i =>
             member equal_nat (nth l_0 i)
               (image fst (Set ((fst o snd) (nth automata i)))))
           zero_nata (size_list automata) andalso
          subset (card_UNIV_nat, equal_nat) (vars_of_formula equal_nat formula)
            (Set (upt zero_nata (n_vs bounds))))));

fun simple_Network_Impl_nat_ceiling_start_state broadcast bounds automata m
  num_states num_actions k l_0 s_0 formula =
  simple_Network_Impl_nat broadcast bounds automata m num_states
    num_actions andalso
    simple_Network_Impl_nat_ceiling_start_state_axioms broadcast bounds automata
      m num_states k l_0 s_0 formula;

fun states_i automata i =
  sup_seta equal_nat
    (image
      (fn (l, (_, (_, (_, (_, (_, la)))))) =>
        insert equal_nat l (insert equal_nat la bot_set))
      (Set (fst (snd (nth automata i)))));

fun certificate_checker_pre l_list m_list broadcast bounds automata m num_states
  num_actions k l_0 s_0 formula =
  let
    val _ = Timing.start_timer ();
    val check1 =
      simple_Network_Impl_nat_ceiling_start_state broadcast bounds automata m
        num_states num_actions k l_0 s_0 formula;
    val _ = Timing.save_time "Time to check ceiling";
    val n_ps = size_list automata;
    val n_vsa = n_vs bounds;
    val states_ia = map (states_i automata) (upt zero_nata n_ps);
    val _ = Timing.start_timer ();
    val check2 =
      list_all
        (fn (l, s) =>
          equal_nata (size_list l) n_ps andalso
            (all_interval_nat
               (fn i => member equal_nat (nth l i) (nth states_ia i)) zero_nata
               n_ps andalso
              (equal_nata (size_list s) n_vsa andalso check_boundedi bounds s)))
        l_list;
    val _ = Timing.save_time "Time to check states";
    val _ = Timing.start_timer ();
    val n_sq = times_nata (suc m) (suc m);
    val check3 =
      list_all
        (fn (_, a) => list_all (fn ma => equal_nata (size_list ma) n_sq) a)
        m_list;
    val _ = Timing.save_time "Time to check DBMs";
    val check4 =
      (case formula of EX _ => true | EG _ => false | AX _ => false
        | AG _ => false | Leadsto (_, _) => false);
  in
    check1 andalso (check2 andalso (check3 andalso check4))
  end;

fun dbm_subset_impl_int x =
  (fn n => fn ai => fn bi =>
    (fn f_ => fn () => f_ ((check_diag_impl_inta n n ai) ()) ())
      (fn xa => (if xa then (fn () => true) else dbm_subset_impl_inta n ai bi)))
    x;

fun certify_unreachable_impl_inner (A1_, A2_, A3_) B_ fi pi copyi lei l_0i s_0i
  succsi splitteri =
  (fn ai => fn bi =>
    (fn f_ => fn () => f_ ((start_timer_impl ()) ()) ())
      (fn _ =>
        (fn f_ => fn () => f_ (l_0i ()) ())
          (fn x =>
            (fn f_ => fn () => f_
              ((imp_nfoldli ai (fn sigma => (fn () => (not sigma)))
                 (fn xb => fn _ => (fn () => (eq A1_ xb x))) false)
              ()) ())
              (fn xa =>
                (fn f_ => fn () => f_ (l_0i ()) ())
                  (fn xaa =>
                    (fn f_ => fn () => f_ (s_0i ()) ())
                      (fn xb =>
                        (fn f_ => fn () => f_ ((pi (xaa, xb)) ()) ())
                          (fn xab =>
                            (fn f_ => fn () => f_ (l_0i ()) ())
                              (fn xba =>
                                (fn f_ => fn () => f_
                                  ((hms_lookup
                                     (ht_lookup (A1_, A2_, A3_) (heap_list B_))
                                     (heap_map copyi) xba bi)
                                  ()) ())
                                  (fn xbb =>
                                    (fn f_ => fn () => f_
                                      ((case xbb of NONE => (fn () => false)
 | SOME x_d =>
   (fn f_ => fn () => f_
     ((imp_nfoldli x_d (fn sigma => (fn () => (not sigma)))
        (fn xg => fn _ =>
          (fn f_ => fn () => f_ (s_0i ()) ()) (fn x_h => lei x_h xg))
        false)
     ()) ())
     (fn x_f =>
       (fn f_ => fn () => f_
         ((imp_nfoldli ai (fn a => (fn () => a))
            (fn xbc => fn _ =>
              (fn f_ => fn () => f_
                ((hms_lookup (ht_lookup (A1_, A2_, A3_) (heap_list B_))
                   (heap_map copyi) xbc bi)
                ()) ())
                (fn a =>
                  (case a of NONE => (fn () => true)
                    | SOME x_e =>
                      imp_nfoldli x_e (fn aa => (fn () => aa))
                        (fn xh => fn _ => pi (xbc, xh)) true)))
            true)
         ()) ())
         (fn x_g =>
           (fn f_ => fn () => f_
             ((print_check_impl "Start state is in state list" xa) ()) ())
             (fn _ =>
               (fn f_ => fn () => f_
                 ((print_check_impl "Start state fulfills property" xab) ()) ())
                 (fn _ =>
                   (fn f_ => fn () => f_
                     ((print_check_impl "Start state is subsumed" x_f) ()) ())
                     (fn _ =>
                       (fn f_ => fn () => f_
                         ((print_check_impl "Check property" x_g) ()) ())
                         (fn _ =>
                           (fn () =>
                             (xa andalso
                               (xab andalso (x_f andalso x_g)))))))))))
                                      ()) ())
                                      (fn xc =>
(fn f_ => fn () => f_
  ((if xc
     then (fn f_ => fn () => f_
            (((fn f_ => fn () => f_
                (((fn f => fn xs => fn () => Par_List.map (fn x => f x ()) xs) (fn
  l =>
 imp_nfoldli l (fn a => (fn () => a))
   (fn xac => fn _ =>
     (fn f_ => fn () => f_
       ((hms_lookup (ht_lookup (A1_, A2_, A3_) (heap_list B_)) (heap_map copyi)
          xac bi)
       ()) ())
       (fn a =>
         (case a of NONE => (fn () => true)
           | SOME x_c =>
             (fn f_ => fn () => f_ ((succsi xac x_c) ()) ())
               (fn x_d =>
                 imp_nfoldli x_d (fn aa => (fn () => aa))
                   (fn xg => fn _ =>
                     let
                       val (a1, a2) = xg;
                     in
                       (if op_list_is_empty a2 then (fn () => true)
                         else (fn f_ => fn () => f_
                                ((hms_lookup
                                   (ht_lookup (A1_, A2_, A3_) (heap_list B_))
                                   (heap_map copyi) a1 bi)
                                ()) ())
                                (fn aa =>
                                  (case aa of NONE => (fn () => false)
                                    | SOME x_k =>
                                      imp_nfoldli a2 (fn ab => (fn () => ab))
(fn xn => fn _ =>
  imp_nfoldli x_k (fn sigma => (fn () => (not sigma)))
    (fn xp => fn _ => lei xn xp) false)
true)))
                     end)
                   true))))
   true) (splitteri ai))
                ()) ())
               (fn bs => (fn () => (list_all id bs))))
            ()) ())
            (fn x_b =>
              (fn f_ => fn () => f_
                ((print_check_impl "State set invariant check" x_b) ()) ())
                (fn _ => (fn () => x_b)))
     else (fn () => false))
  ()) ())
  (fn x_a =>
    (fn f_ => fn () => f_
      ((save_time_impl "Time for state space invariant check") ()) ())
      (fn _ =>
        (fn f_ => fn () => f_ ((start_timer_impl ()) ()) ())
          (fn _ =>
            (fn f_ => fn () => f_
              ((imp_nfoldli ai (fn a => (fn () => a))
                 (fn xbc => fn _ =>
                   (fn f_ => fn () => f_
                     ((hms_lookup (ht_lookup (A1_, A2_, A3_) (heap_list B_))
                        (heap_map copyi) xbc bi)
                     ()) ())
                     (fn a =>
                       (case a of NONE => (fn () => true)
                         | SOME x_e =>
                           imp_nfoldli x_e (fn aa => (fn () => aa))
                             (fn xh => fn _ =>
                               (fn f_ => fn () => f_ ((fi (xbc, xh)) ()) ())
                                 (fn x_i => (fn () => (not x_i))))
                             true)))
                 true)
              ()) ())
              (fn x_d =>
                (fn f_ => fn () => f_
                  ((save_time_impl "Time to check final state predicate") ())
                  ())
                  (fn _ =>
                    (fn f_ => fn () => f_ ((print_check_impl "All check: " x_a)
                      ()) ())
                      (fn _ =>
                        (fn f_ => fn () => f_
                          ((print_check_impl "Target property check: " x_d) ())
                          ())
                          (fn _ =>
                            (fn () => (x_a andalso x_d)))))))))))))))))));

fun unreachability_checker broadcast bounds automata m num_states num_actions
  l_0 s_0 formula l_list m_list num_split =
  let
    val states_ia =
      map (states_i automata) (upt zero_nata (size_list automata));
    val check_states =
      (fn (l, s) =>
        equal_nata (size_list l) (size_list automata) andalso
          all_interval_nat
            (fn i => member equal_nat (nth l i) (nth states_ia i)) zero_nata
            (size_list automata) andalso
          (equal_nata (size_list s) (n_vs bounds) andalso
            check_boundedi bounds s));
    val fi = (fn xi => (fn () => let
                                   val ((a, b), _) = xi;
                                 in
                                   hd_of_formulai equal_nat formula a b
                                 end));
    val pi =
      (fn (a1, a2) =>
        (fn f_ => fn () => f_
          ((imp_for_int zero_nata (plus_nata m one_nata) (fn a => (fn () => a))
             (fn xc => fn _ =>
               imp_for_int zero_nata (plus_nata m one_nata)
                 (fn a => (fn () => a))
                 (fn xf => fn _ =>
                   imp_for_int zero_nata (plus_nata m one_nata)
                     (fn a => (fn () => a))
                     (fn xj => fn _ =>
                       (fn f_ => fn () => f_
                         ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (xc, xj))
                         ()) ())
                         (fn x_i =>
                           (fn f_ => fn () => f_
                             ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                (xc, xf))
                             ()) ())
                             (fn x =>
                               (fn f_ => fn () => f_
                                 ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                    (xf, xj))
                                 ()) ())
                                 (fn xa =>
                                   (fn () =>
                                     (dbm_le_int x_i (dbm_add_int x xa)))))))
                     true)
                 true)
             true)
          ()) ())
          (fn x =>
            (fn f_ => fn () => f_ ((check_diag_impl_int m a2) ()) ())
              (fn xa =>
                (fn f_ => fn () => f_
                  ((imp_for_int zero_nata (plus_nata m one_nata)
                     (fn a => (fn () => a))
                     (fn xc => fn _ =>
                       (fn f_ => fn () => f_
                         ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (xc, xc))
                         ()) ())
                         (fn x_d => (fn () => (dbm_le_int x_d (Le zero_inta)))))
                     true)
                  ()) ())
                  (fn xb =>
                    (fn f_ => fn () => f_
                      ((imp_for_int zero_nata (plus_nata m one_nata)
                         (fn a => (fn () => a))
                         (fn xc => fn _ =>
                           (fn f_ => fn () => f_
                             ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                (zero_nata, xc))
                             ()) ())
                             (fn x_e =>
                               (fn () => (dbm_le_int x_e (Le zero_inta)))))
                         true)
                      ()) ())
                      (fn xc =>
                        (fn () =>
                          (check_states a1 andalso
                            ((x orelse xa) andalso (xb andalso xc)))))))));
    val copyi = amtx_copy (heap_DBMEntry heap_int);
    val lei = dbm_subset_impl_int m;
    val l_0i =
      (fn () =>
        (l_0, map (the o map_of equal_nat s_0) (upt zero_nata (n_vs bounds))));
    val s_0i =
      amtx_dflt (heap_DBMEntry heap_int) (suc m) (suc m) (Le zero_inta);
    val succsi =
      let
        val n_ps = size_list automata;
        val invs =
          Vector.fromList
            (map (fn i =>
                   let
                     val ma =
                       default_map_of equal_nat [] (snd (snd (nth automata i)));
                     val mb =
                       Vector.fromList (map ma (upt zero_nata (num_states i)));
                   in
                     mb
                   end)
              (upt zero_nata n_ps));
        val inv_fun =
          (fn (l, _) =>
            maps (fn i => sub (sub invs i) (nth l i)) (upt zero_nata n_ps));
        val trans_mapa = trans_map automata;
        val trans_i_map =
          (fn i => fn j =>
            map_filter
              (fn (b, a) =>
                let
                  val (g, aa) = a;
                  val (ab, (ma, l)) = aa;
                in
                  (case ab of In _ => NONE | Out _ => NONE
                    | Sil ac => SOME (b, (g, (ac, (ma, l)))))
                end)
              (trans_mapa i j));
        val int_trans_from_loc_impl =
          (fn p => fn l => fn la => fn s =>
            let
              val a = trans_i_map p l;
            in
              map_filter
                (fn (b, aa) =>
                  let
                    val (g, ab) = aa;
                    val (ac, (f, (r, lb))) = ab;
                    val sa = mk_updsi s f;
                  in
                    (if bvali (equal_int, linorder_int) s b andalso
                          check_boundedi bounds sa
                      then SOME (g, (Internal ac,
                                      (r, (list_update la p lb, sa))))
                      else NONE)
                  end)
                a
            end);
        val int_trans_from_vec_impl =
          (fn pairs => fn l => fn s =>
            maps (fn (p, la) => int_trans_from_loc_impl p la l s) pairs);
        val int_trans_from_all_impl =
          (fn l => fn s =>
            maps (fn p => int_trans_from_loc_impl p (nth l p) l s)
              (upt zero_nata n_ps));
        val trans_out_map =
          (fn i => fn j =>
            map_filter
              (fn (b, a) =>
                let
                  val (g, aa) = a;
                  val (ab, (ma, l)) = aa;
                in
                  (case ab of In _ => NONE
                    | Out ac => SOME (b, (g, (ac, (ma, l)))) | Sil _ => NONE)
                end)
              (trans_mapa i j));
        val trans_in_map =
          (fn i => fn j =>
            map_filter
              (fn (b, a) =>
                let
                  val (g, aa) = a;
                  val (ab, (ma, l)) = aa;
                in
                  (case ab of In ac => SOME (b, (g, (ac, (ma, l))))
                    | Out _ => NONE | Sil _ => NONE)
                end)
              (trans_mapa i j));
        val trans_out_broad_grouped =
          (fn i => fn j =>
            actions_by_statea num_actions
              (map_filter
                (fn (b, a) =>
                  let
                    val (g, aa) = a;
                    val (ab, (ma, l)) = aa;
                  in
                    (case ab of In _ => NONE
                      | Out ac =>
                        (if membera equal_nat broadcast ac
                          then SOME (b, (g, (ac, (ma, l)))) else NONE)
                      | Sil _ => NONE)
                  end)
                (trans_mapa i j)));
        val trans_in_broad_grouped =
          (fn i => fn j =>
            actions_by_statea num_actions
              (map_filter
                (fn (b, a) =>
                  let
                    val (g, aa) = a;
                    val (ab, (ma, l)) = aa;
                  in
                    (case ab
                      of In ac =>
                        (if membera equal_nat broadcast ac
                          then SOME (b, (g, (ac, (ma, l)))) else NONE)
                      | Out _ => NONE | Sil _ => NONE)
                  end)
                (trans_mapa i j)));
        val broad_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_commited broadcast bounds automata l;
              val ina =
                map (fn p => trans_in_broad_grouped p (nth l p))
                  (upt zero_nata n_ps);
              val out =
                map (fn p => trans_out_broad_grouped p (nth l p))
                  (upt zero_nata n_ps);
              val inb =
                map (map (filter
                           (fn (b, _) => bvali (equal_int, linorder_int) s b)))
                  ina;
              val outa =
                map (map (filter
                           (fn (b, _) => bvali (equal_int, linorder_int) s b)))
                  out;
            in
              (if null pairs
                then maps (fn a =>
                            maps (fn p =>
                                   let
                                     val outs = nth (nth outa p) a;
                                   in
                                     (if null outs then []
                                       else let
      val combs = make_combs broadcast bounds automata p a inb;
      val outsa = map (fn aa => (p, aa)) outs;
      val combsa =
        (if null combs then map (fn x => [x]) outsa
          else maps (fn x => map (fn aa => x :: aa) combs) outsa);
      val init = ([], (Broad a, ([], (l, s))));
    in
      compute_upds_impl bounds init combsa
    end)
                                   end)
                              (upt zero_nata n_ps))
                       (upt zero_nata num_actions)
                else maps (fn a =>
                            let
                              val ins_commited =
                                map_filter
                                  (fn (p, _) =>
                                    (if not (null (nth (nth inb p) a))
                                      then SOME p else NONE))
                                  pairs;
                              val always_commited =
                                less_nat one_nata (size_list ins_commited);
                            in
                              maps (fn p =>
                                     let
                                       val outs = nth (nth outa p) a;
                                     in
                                       (if null outs then []
 else (if not always_commited andalso
            ((equal_lista equal_nat ins_commited [p] orelse
               null ins_commited) andalso
              not (list_ex (fn (q, _) => equal_nata q p) pairs))
        then []
        else let
               val combs = make_combs broadcast bounds automata p a inb;
               val outsa = map (fn aa => (p, aa)) outs;
               val combsa =
                 (if null combs then map (fn x => [x]) outsa
                   else maps (fn x => map (fn aa => x :: aa) combs) outsa);
               val init = ([], (Broad a, ([], (l, s))));
             in
               compute_upds_impl bounds init combsa
             end))
                                     end)
                                (upt zero_nata n_ps)
                            end)
                       (upt zero_nata num_actions))
            end);
        val bin_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_commited broadcast bounds automata l;
              val ina =
                all_actions_by_state broadcast bounds automata num_actions
                  trans_in_map l;
              val out =
                all_actions_by_state broadcast bounds automata num_actions
                  trans_out_map l;
            in
              (if null pairs
                then maps (fn a =>
                            pairs_by_action_impl bounds l s (nth out a)
                              (nth ina a))
                       (bin_actions broadcast num_actions)
                else let
                       val in2 =
                         all_actions_from_vec num_actions trans_in_map pairs;
                       val out2 =
                         all_actions_from_vec num_actions trans_out_map pairs;
                     in
                       maps (fn a =>
                              pairs_by_action_impl bounds l s (nth out a)
                                (nth in2 a))
                         (bin_actions broadcast num_actions) @
                         maps (fn a =>
                                pairs_by_action_impl bounds l s (nth out2 a)
                                  (nth ina a))
                           (bin_actions broadcast num_actions)
                     end)
            end);
        val int_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_commited broadcast bounds automata l;
            in
              (if null pairs then int_trans_from_all_impl l s
                else int_trans_from_vec_impl pairs l s)
            end);
        val trans_impl =
          (fn st =>
            int_trans_impl st @ bin_trans_impl st @ broad_trans_impl st);
        val e_op_impl =
          (fn ai => fn bic => fn bib => fn bia => fn bi =>
            (fn f_ => fn () => f_ ((up_canonical_upd_impl_int m bi m) ()) ())
              (fn x =>
                (fn f_ => fn () => f_
                  ((imp_nfoldli (inv_fun ai) (fn _ => (fn () => true))
                     (fn aia => fn bid =>
                       (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid)
                         ()) ())
                         (fn xa =>
                           repair_pair_impl_int m xa zero_nata
                             (constraint_clk aia)))
                     x)
                  ()) ())
                  (fn xa =>
                    (fn f_ => fn () => f_ ((check_diag_impl_int m xa) ()) ())
                      (fn xaa =>
                        (fn f_ => fn () => f_
                          ((if xaa
                             then mtx_set (heap_DBMEntry heap_int) (suc m) xa
                                    (zero_nata, zero_nata) (Lt zero_inta)
                             else imp_nfoldli bib (fn _ => (fn () => true))
                                    (fn aia => fn bid =>
                                      (fn f_ => fn () => f_
((abstra_upd_impl_int m aia bid) ()) ())
(fn xb => repair_pair_impl_int m xb zero_nata (constraint_clk aia)))
                                    xa)
                          ()) ())
                          (fn x_a =>
                            (fn f_ => fn () => f_ ((check_diag_impl_int m x_a)
                              ()) ())
                              (fn x_b =>
                                (if x_b
                                  then mtx_set (heap_DBMEntry heap_int) (suc m)
 x_a (zero_nata, zero_nata) (Lt zero_inta)
                                  else (fn f_ => fn () => f_
 ((imp_nfoldli bic (fn _ => (fn () => true))
    (fn xc => fn sigma => reset_canonical_upd_impl_int m sigma m xc zero_inta)
    x_a)
 ()) ())
 (imp_nfoldli (inv_fun bia) (fn _ => (fn () => true))
   (fn aia => fn bid =>
     (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid) ()) ())
       (fn xb =>
         repair_pair_impl_int m xb zero_nata (constraint_clk aia)))))))))));
      in
        (fn ai => fn bi =>
          (if null bi then (fn () => [])
            else imp_nfoldli (trans_impl ai) (fn _ => (fn () => true))
                   (fn xc => fn sigma =>
                     let
                       val (a1, (_, (a1b, a2b))) = xc;
                     in
                       (fn f_ => fn () => f_
                         ((heap_map (amtx_copy (heap_DBMEntry heap_int)) bi) ())
                         ())
                         (fn x =>
                           (fn f_ => fn () => f_
                             ((imp_nfoldli x (fn _ => (fn () => true))
                                (fn xb => fn sigmaa =>
                                  (fn f_ => fn () => f_
                                    ((pR_CONST e_op_impl ai a1b a1 a2b xb) ())
                                    ())
                                    (fn x_c =>
                                      (fn f_ => fn () => f_
((check_diag_impl_int m x_c) ()) ())
(fn x_e => (fn () => (if x_e then sigmaa else op_list_prepend x_c sigmaa)))))
                                [])
                             ()) ())
                             (fn x_d =>
                               (fn () => (op_list_prepend (a2b, x_d) sigma))))
                     end)
                   []))
      end;
    val _ = Timing.start_timer ();
  in
    (fn f_ => fn () => f_
      (((fn f_ => fn () => f_
          ((ht_new
             (hashable_prod (hashable_list hashable_nat)
                (hashable_list hashable_int),
               heap_prod (heap_list heap_nat) (heap_list heap_int))
             (heap_list (heap_array (typerep_DBMEntry typerep_int))))
          ()) ())
         (imp_nfoldli m_list (fn _ => (fn () => true))
           (fn xc => fn sigma =>
             (fn f_ => fn () => f_
               ((imp_nfoldli (snd xc) (fn _ => (fn () => true))
                  (fn xg => fn sigmaa =>
                    (fn f_ => fn () => f_ (((fn () => Array.fromList xg)) ())
                      ())
                      (fn x_g => (fn () => (x_g :: sigmaa))))
                  [])
               ()) ())
               (fn x_e =>
                 ht_update
                   (equal_prod (equal_list equal_nat) (equal_list equal_int),
                     hashable_prod (hashable_list hashable_nat)
                       (hashable_list hashable_int),
                     heap_prod (heap_list heap_nat) (heap_list heap_int))
                   (heap_list (heap_array (typerep_DBMEntry typerep_int)))
                   (fst xc) x_e sigma))))
      ()) ())
      (fn m_table =>
        let
          val _ = Timing.save_time "Time for loading certificate";
        in
          (fn f_ => fn () => f_
            ((certify_unreachable_impl_inner
               (equal_prod (equal_list equal_nat) (equal_list equal_int),
                 hashable_prod (hashable_list hashable_nat)
                   (hashable_list hashable_int),
                 heap_prod (heap_list heap_nat) (heap_list heap_int))
               (heap_array (typerep_DBMEntry typerep_int)) fi pi copyi lei l_0i
               s_0i succsi (split_ka num_split) l_list m_table)
            ()) ())
            (fn a => (fn () => a))
        end)
  end;

fun abstr_upd_impl_int x =
  (fn n => fn ai =>
    imp_nfoldli ai (fn _ => (fn () => true)) (abstra_upd_impl_int n))
    x;

fun abstr_FW_impl_int x =
  (fn n => fn ai => fn bi =>
    (fn f_ => fn () => f_ ((abstr_upd_impl_int n ai bi) ()) ())
      (fw_impl_inta n))
    x;

fun down_impl_int x =
  (fn n =>
    imp_for_inta one_nata (suc n)
      (fn xb => fn sigma =>
        (fn f_ => fn () => f_
          ((imp_for_inta one_nata (suc n)
             (fn xe => fn sigmaa =>
               (fn f_ => fn () => f_
                 ((mtx_get (heap_DBMEntry heap_int) (suc n) sigma (xe, xb)) ())
                 ())
                 (fn x_f => (fn () => (min_int_entry x_f sigmaa))))
             (Le zero_inta))
          ()) ())
          (mtx_set (heap_DBMEntry heap_int) (suc n) sigma (zero_nata, xb))))
    x;

fun no_deadlock_certifier broadcast bounds automata m num_states num_actions l_0
  s_0 l_list m_list num_split =
  let
    val states_ia =
      map (states_i automata) (upt zero_nata (size_list automata));
    val check_states =
      (fn (l, s) =>
        equal_nata (size_list l) (size_list automata) andalso
          all_interval_nat
            (fn i => member equal_nat (nth l i) (nth states_ia i)) zero_nata
            (size_list automata) andalso
          (equal_nata (size_list s) (n_vs bounds) andalso
            check_boundedi bounds s));
    val fi =
      (fn (l, ma) =>
        (fn f_ => fn () => f_
          ((let
              val n_ps = size_list automata;
              val invs =
                Vector.fromList
                  (map (fn i =>
                         let
                           val mb =
                             default_map_of equal_nat []
                               (snd (snd (nth automata i)));
                           val mc =
                             Vector.fromList
                               (map mb (upt zero_nata (num_states i)));
                         in
                           mc
                         end)
                    (upt zero_nata n_ps));
              val inv_fun =
                (fn (la, _) =>
                  maps (fn i => sub (sub invs i) (nth la i))
                    (upt zero_nata n_ps));
              val trans_impl =
                let
                  val trans_mapa = trans_map automata;
                  val trans_i_map =
                    (fn i => fn j =>
                      map_filter
                        (fn (b, a) =>
                          let
                            val (g, aa) = a;
                            val (ab, (mb, la)) = aa;
                          in
                            (case ab of In _ => NONE | Out _ => NONE
                              | Sil ac => SOME (b, (g, (ac, (mb, la)))))
                          end)
                        (trans_mapa i j));
                  val int_trans_from_loc_impl =
                    (fn p => fn la => fn laa => fn s =>
                      let
                        val a = trans_i_map p la;
                      in
                        map_filter
                          (fn (b, aa) =>
                            let
                              val (g, ab) = aa;
                              val (ac, (f, (r, lb))) = ab;
                              val sa = mk_updsi s f;
                            in
                              (if bvali (equal_int, linorder_int) s b andalso
                                    check_boundedi bounds sa
                                then SOME (g,
    (Internal ac, (r, (list_update laa p lb, sa))))
                                else NONE)
                            end)
                          a
                      end);
                  val int_trans_from_vec_impl =
                    (fn pairs => fn la => fn s =>
                      maps (fn (p, laa) => int_trans_from_loc_impl p laa la s)
                        pairs);
                  val int_trans_from_all_impl =
                    (fn la => fn s =>
                      maps (fn p => int_trans_from_loc_impl p (nth la p) la s)
                        (upt zero_nata n_ps));
                  val trans_out_map =
                    (fn i => fn j =>
                      map_filter
                        (fn (b, a) =>
                          let
                            val (g, aa) = a;
                            val (ab, (mb, la)) = aa;
                          in
                            (case ab of In _ => NONE
                              | Out ac => SOME (b, (g, (ac, (mb, la))))
                              | Sil _ => NONE)
                          end)
                        (trans_mapa i j));
                  val trans_in_map =
                    (fn i => fn j =>
                      map_filter
                        (fn (b, a) =>
                          let
                            val (g, aa) = a;
                            val (ab, (mb, la)) = aa;
                          in
                            (case ab of In ac => SOME (b, (g, (ac, (mb, la))))
                              | Out _ => NONE | Sil _ => NONE)
                          end)
                        (trans_mapa i j));
                  val trans_out_broad_grouped =
                    (fn i => fn j =>
                      actions_by_statea num_actions
                        (map_filter
                          (fn (b, a) =>
                            let
                              val (g, aa) = a;
                              val (ab, (mb, la)) = aa;
                            in
                              (case ab of In _ => NONE
                                | Out ac =>
                                  (if membera equal_nat broadcast ac
                                    then SOME (b, (g, (ac, (mb, la))))
                                    else NONE)
                                | Sil _ => NONE)
                            end)
                          (trans_mapa i j)));
                  val trans_in_broad_grouped =
                    (fn i => fn j =>
                      actions_by_statea num_actions
                        (map_filter
                          (fn (b, a) =>
                            let
                              val (g, aa) = a;
                              val (ab, (mb, la)) = aa;
                            in
                              (case ab
                                of In ac =>
                                  (if membera equal_nat broadcast ac
                                    then SOME (b, (g, (ac, (mb, la))))
                                    else NONE)
                                | Out _ => NONE | Sil _ => NONE)
                            end)
                          (trans_mapa i j)));
                  val broad_trans_impl =
                    (fn (la, s) =>
                      let
                        val pairs = get_commited broadcast bounds automata la;
                        val ina =
                          map (fn p => trans_in_broad_grouped p (nth la p))
                            (upt zero_nata n_ps);
                        val out =
                          map (fn p => trans_out_broad_grouped p (nth la p))
                            (upt zero_nata n_ps);
                        val inb =
                          map (map (filter
                                     (fn (b, _) =>
                                       bvali (equal_int, linorder_int) s b)))
                            ina;
                        val outa =
                          map (map (filter
                                     (fn (b, _) =>
                                       bvali (equal_int, linorder_int) s b)))
                            out;
                      in
                        (if null pairs
                          then maps (fn a =>
                                      maps
(fn p =>
  let
    val outs = nth (nth outa p) a;
  in
    (if null outs then []
      else let
             val combs = make_combs broadcast bounds automata p a inb;
             val outsa = map (fn aa => (p, aa)) outs;
             val combsa =
               (if null combs then map (fn x => [x]) outsa
                 else maps (fn x => map (fn aa => x :: aa) combs) outsa);
             val init = ([], (Broad a, ([], (la, s))));
           in
             compute_upds_impl bounds init combsa
           end)
  end)
(upt zero_nata n_ps))
                                 (upt zero_nata num_actions)
                          else maps (fn a =>
                                      let
val ins_commited =
  map_filter
    (fn (p, _) => (if not (null (nth (nth inb p) a)) then SOME p else NONE))
    pairs;
val always_commited = less_nat one_nata (size_list ins_commited);
                                      in
maps (fn p =>
       let
         val outs = nth (nth outa p) a;
       in
         (if null outs then []
           else (if not always_commited andalso
                      ((equal_lista equal_nat ins_commited [p] orelse
                         null ins_commited) andalso
                        not (list_ex (fn (q, _) => equal_nata q p) pairs))
                  then []
                  else let
                         val combs =
                           make_combs broadcast bounds automata p a inb;
                         val outsa = map (fn aa => (p, aa)) outs;
                         val combsa =
                           (if null combs then map (fn x => [x]) outsa
                             else maps (fn x => map (fn aa => x :: aa) combs)
                                    outsa);
                         val init = ([], (Broad a, ([], (la, s))));
                       in
                         compute_upds_impl bounds init combsa
                       end))
       end)
  (upt zero_nata n_ps)
                                      end)
                                 (upt zero_nata num_actions))
                      end);
                  val bin_trans_impl =
                    (fn (la, s) =>
                      let
                        val pairs = get_commited broadcast bounds automata la;
                        val ina =
                          all_actions_by_state broadcast bounds automata
                            num_actions trans_in_map la;
                        val out =
                          all_actions_by_state broadcast bounds automata
                            num_actions trans_out_map la;
                      in
                        (if null pairs
                          then maps (fn a =>
                                      pairs_by_action_impl bounds la s
(nth out a) (nth ina a))
                                 (bin_actions broadcast num_actions)
                          else let
                                 val in2 =
                                   all_actions_from_vec num_actions trans_in_map
                                     pairs;
                                 val out2 =
                                   all_actions_from_vec num_actions
                                     trans_out_map pairs;
                               in
                                 maps (fn a =>
pairs_by_action_impl bounds la s (nth out a) (nth in2 a))
                                   (bin_actions broadcast num_actions) @
                                   maps (fn a =>
  pairs_by_action_impl bounds la s (nth out2 a) (nth ina a))
                                     (bin_actions broadcast num_actions)
                               end)
                      end);
                  val int_trans_impl =
                    (fn (la, s) =>
                      let
                        val pairs = get_commited broadcast bounds automata la;
                      in
                        (if null pairs then int_trans_from_all_impl la s
                          else int_trans_from_vec_impl pairs la s)
                      end);
                in
                  (fn st =>
                    int_trans_impl st @ bin_trans_impl st @ broad_trans_impl st)
                end;
            in
              (fn ai => fn bi =>
                (fn f_ => fn () => f_
                  ((imp_nfoldli (trans_impl ai) (fn _ => (fn () => true))
                     (fn xb => fn sigma =>
                       (fn f_ => fn () => f_
                         ((v_dbm_impl
                            (linordered_cancel_ab_monoid_add_int, heap_int) m)
                         ()) ())
                         (fn x =>
                           (fn f_ => fn () => f_
                             ((abstr_FW_impl_int m
                                (inv_fun (snd (snd (snd xb)))) x)
                             ()) ())
                             (fn xa =>
                               (fn f_ => fn () => f_
                                 ((pre_reset_list_impl m xa
                                    (fst (snd (snd xb))))
                                 ()) ())
                                 (fn xc =>
                                   (fn f_ => fn () => f_
                                     ((abstr_FW_impl_int m (fst xb) xc) ()) ())
                                     (fn xd =>
                                       (fn f_ => fn () => f_
 ((abstr_FW_impl_int m (inv_fun ai) xd) ()) ())
 (fn xe =>
   (fn f_ => fn () => f_ ((down_impl_int m xe) ()) ())
     (fn x_c => (fn () => (x_c :: sigma)))))))))
                     [])
                  ()) ())
                  (fn x => dbm_subset_fed_impl m bi (op_list_rev x)))
            end
              l
             ma)
          ()) ())
          (fn r => (fn () => (not r))));
    val pi =
      (fn (a1, a2) =>
        (fn f_ => fn () => f_
          ((imp_for_int zero_nata (plus_nata m one_nata) (fn a => (fn () => a))
             (fn xc => fn _ =>
               imp_for_int zero_nata (plus_nata m one_nata)
                 (fn a => (fn () => a))
                 (fn xf => fn _ =>
                   imp_for_int zero_nata (plus_nata m one_nata)
                     (fn a => (fn () => a))
                     (fn xj => fn _ =>
                       (fn f_ => fn () => f_
                         ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (xc, xj))
                         ()) ())
                         (fn x_i =>
                           (fn f_ => fn () => f_
                             ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                (xc, xf))
                             ()) ())
                             (fn x =>
                               (fn f_ => fn () => f_
                                 ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                    (xf, xj))
                                 ()) ())
                                 (fn xa =>
                                   (fn () =>
                                     (dbm_le_int x_i (dbm_add_int x xa)))))))
                     true)
                 true)
             true)
          ()) ())
          (fn x =>
            (fn f_ => fn () => f_ ((check_diag_impl_int m a2) ()) ())
              (fn xa =>
                (fn f_ => fn () => f_
                  ((imp_for_int zero_nata (plus_nata m one_nata)
                     (fn a => (fn () => a))
                     (fn xc => fn _ =>
                       (fn f_ => fn () => f_
                         ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (xc, xc))
                         ()) ())
                         (fn x_d => (fn () => (dbm_le_int x_d (Le zero_inta)))))
                     true)
                  ()) ())
                  (fn xb =>
                    (fn f_ => fn () => f_
                      ((imp_for_int zero_nata (plus_nata m one_nata)
                         (fn a => (fn () => a))
                         (fn xc => fn _ =>
                           (fn f_ => fn () => f_
                             ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                (zero_nata, xc))
                             ()) ())
                             (fn x_e =>
                               (fn () => (dbm_le_int x_e (Le zero_inta)))))
                         true)
                      ()) ())
                      (fn xc =>
                        (fn () =>
                          (check_states a1 andalso
                            ((x orelse xa) andalso (xb andalso xc)))))))));
    val copyi = amtx_copy (heap_DBMEntry heap_int);
    val lei = dbm_subset_impl_int m;
    val l_0i =
      (fn () =>
        (l_0, map (the o map_of equal_nat s_0) (upt zero_nata (n_vs bounds))));
    val s_0i =
      amtx_dflt (heap_DBMEntry heap_int) (suc m) (suc m) (Le zero_inta);
    val succsi =
      let
        val n_ps = size_list automata;
        val invs =
          Vector.fromList
            (map (fn i =>
                   let
                     val ma =
                       default_map_of equal_nat [] (snd (snd (nth automata i)));
                     val mb =
                       Vector.fromList (map ma (upt zero_nata (num_states i)));
                   in
                     mb
                   end)
              (upt zero_nata n_ps));
        val inv_fun =
          (fn (l, _) =>
            maps (fn i => sub (sub invs i) (nth l i)) (upt zero_nata n_ps));
        val trans_mapa = trans_map automata;
        val trans_i_map =
          (fn i => fn j =>
            map_filter
              (fn (b, a) =>
                let
                  val (g, aa) = a;
                  val (ab, (ma, l)) = aa;
                in
                  (case ab of In _ => NONE | Out _ => NONE
                    | Sil ac => SOME (b, (g, (ac, (ma, l)))))
                end)
              (trans_mapa i j));
        val int_trans_from_loc_impl =
          (fn p => fn l => fn la => fn s =>
            let
              val a = trans_i_map p l;
            in
              map_filter
                (fn (b, aa) =>
                  let
                    val (g, ab) = aa;
                    val (ac, (f, (r, lb))) = ab;
                    val sa = mk_updsi s f;
                  in
                    (if bvali (equal_int, linorder_int) s b andalso
                          check_boundedi bounds sa
                      then SOME (g, (Internal ac,
                                      (r, (list_update la p lb, sa))))
                      else NONE)
                  end)
                a
            end);
        val int_trans_from_vec_impl =
          (fn pairs => fn l => fn s =>
            maps (fn (p, la) => int_trans_from_loc_impl p la l s) pairs);
        val int_trans_from_all_impl =
          (fn l => fn s =>
            maps (fn p => int_trans_from_loc_impl p (nth l p) l s)
              (upt zero_nata n_ps));
        val trans_out_map =
          (fn i => fn j =>
            map_filter
              (fn (b, a) =>
                let
                  val (g, aa) = a;
                  val (ab, (ma, l)) = aa;
                in
                  (case ab of In _ => NONE
                    | Out ac => SOME (b, (g, (ac, (ma, l)))) | Sil _ => NONE)
                end)
              (trans_mapa i j));
        val trans_in_map =
          (fn i => fn j =>
            map_filter
              (fn (b, a) =>
                let
                  val (g, aa) = a;
                  val (ab, (ma, l)) = aa;
                in
                  (case ab of In ac => SOME (b, (g, (ac, (ma, l))))
                    | Out _ => NONE | Sil _ => NONE)
                end)
              (trans_mapa i j));
        val trans_out_broad_grouped =
          (fn i => fn j =>
            actions_by_statea num_actions
              (map_filter
                (fn (b, a) =>
                  let
                    val (g, aa) = a;
                    val (ab, (ma, l)) = aa;
                  in
                    (case ab of In _ => NONE
                      | Out ac =>
                        (if membera equal_nat broadcast ac
                          then SOME (b, (g, (ac, (ma, l)))) else NONE)
                      | Sil _ => NONE)
                  end)
                (trans_mapa i j)));
        val trans_in_broad_grouped =
          (fn i => fn j =>
            actions_by_statea num_actions
              (map_filter
                (fn (b, a) =>
                  let
                    val (g, aa) = a;
                    val (ab, (ma, l)) = aa;
                  in
                    (case ab
                      of In ac =>
                        (if membera equal_nat broadcast ac
                          then SOME (b, (g, (ac, (ma, l)))) else NONE)
                      | Out _ => NONE | Sil _ => NONE)
                  end)
                (trans_mapa i j)));
        val broad_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_commited broadcast bounds automata l;
              val ina =
                map (fn p => trans_in_broad_grouped p (nth l p))
                  (upt zero_nata n_ps);
              val out =
                map (fn p => trans_out_broad_grouped p (nth l p))
                  (upt zero_nata n_ps);
              val inb =
                map (map (filter
                           (fn (b, _) => bvali (equal_int, linorder_int) s b)))
                  ina;
              val outa =
                map (map (filter
                           (fn (b, _) => bvali (equal_int, linorder_int) s b)))
                  out;
            in
              (if null pairs
                then maps (fn a =>
                            maps (fn p =>
                                   let
                                     val outs = nth (nth outa p) a;
                                   in
                                     (if null outs then []
                                       else let
      val combs = make_combs broadcast bounds automata p a inb;
      val outsa = map (fn aa => (p, aa)) outs;
      val combsa =
        (if null combs then map (fn x => [x]) outsa
          else maps (fn x => map (fn aa => x :: aa) combs) outsa);
      val init = ([], (Broad a, ([], (l, s))));
    in
      compute_upds_impl bounds init combsa
    end)
                                   end)
                              (upt zero_nata n_ps))
                       (upt zero_nata num_actions)
                else maps (fn a =>
                            let
                              val ins_commited =
                                map_filter
                                  (fn (p, _) =>
                                    (if not (null (nth (nth inb p) a))
                                      then SOME p else NONE))
                                  pairs;
                              val always_commited =
                                less_nat one_nata (size_list ins_commited);
                            in
                              maps (fn p =>
                                     let
                                       val outs = nth (nth outa p) a;
                                     in
                                       (if null outs then []
 else (if not always_commited andalso
            ((equal_lista equal_nat ins_commited [p] orelse
               null ins_commited) andalso
              not (list_ex (fn (q, _) => equal_nata q p) pairs))
        then []
        else let
               val combs = make_combs broadcast bounds automata p a inb;
               val outsa = map (fn aa => (p, aa)) outs;
               val combsa =
                 (if null combs then map (fn x => [x]) outsa
                   else maps (fn x => map (fn aa => x :: aa) combs) outsa);
               val init = ([], (Broad a, ([], (l, s))));
             in
               compute_upds_impl bounds init combsa
             end))
                                     end)
                                (upt zero_nata n_ps)
                            end)
                       (upt zero_nata num_actions))
            end);
        val bin_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_commited broadcast bounds automata l;
              val ina =
                all_actions_by_state broadcast bounds automata num_actions
                  trans_in_map l;
              val out =
                all_actions_by_state broadcast bounds automata num_actions
                  trans_out_map l;
            in
              (if null pairs
                then maps (fn a =>
                            pairs_by_action_impl bounds l s (nth out a)
                              (nth ina a))
                       (bin_actions broadcast num_actions)
                else let
                       val in2 =
                         all_actions_from_vec num_actions trans_in_map pairs;
                       val out2 =
                         all_actions_from_vec num_actions trans_out_map pairs;
                     in
                       maps (fn a =>
                              pairs_by_action_impl bounds l s (nth out a)
                                (nth in2 a))
                         (bin_actions broadcast num_actions) @
                         maps (fn a =>
                                pairs_by_action_impl bounds l s (nth out2 a)
                                  (nth ina a))
                           (bin_actions broadcast num_actions)
                     end)
            end);
        val int_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_commited broadcast bounds automata l;
            in
              (if null pairs then int_trans_from_all_impl l s
                else int_trans_from_vec_impl pairs l s)
            end);
        val trans_impl =
          (fn st =>
            int_trans_impl st @ bin_trans_impl st @ broad_trans_impl st);
        val e_op_impl =
          (fn ai => fn bic => fn bib => fn bia => fn bi =>
            (fn f_ => fn () => f_ ((up_canonical_upd_impl_int m bi m) ()) ())
              (fn x =>
                (fn f_ => fn () => f_
                  ((imp_nfoldli (inv_fun ai) (fn _ => (fn () => true))
                     (fn aia => fn bid =>
                       (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid)
                         ()) ())
                         (fn xa =>
                           repair_pair_impl_int m xa zero_nata
                             (constraint_clk aia)))
                     x)
                  ()) ())
                  (fn xa =>
                    (fn f_ => fn () => f_ ((check_diag_impl_int m xa) ()) ())
                      (fn xaa =>
                        (fn f_ => fn () => f_
                          ((if xaa
                             then mtx_set (heap_DBMEntry heap_int) (suc m) xa
                                    (zero_nata, zero_nata) (Lt zero_inta)
                             else imp_nfoldli bib (fn _ => (fn () => true))
                                    (fn aia => fn bid =>
                                      (fn f_ => fn () => f_
((abstra_upd_impl_int m aia bid) ()) ())
(fn xb => repair_pair_impl_int m xb zero_nata (constraint_clk aia)))
                                    xa)
                          ()) ())
                          (fn x_a =>
                            (fn f_ => fn () => f_ ((check_diag_impl_int m x_a)
                              ()) ())
                              (fn x_b =>
                                (if x_b
                                  then mtx_set (heap_DBMEntry heap_int) (suc m)
 x_a (zero_nata, zero_nata) (Lt zero_inta)
                                  else (fn f_ => fn () => f_
 ((imp_nfoldli bic (fn _ => (fn () => true))
    (fn xc => fn sigma => reset_canonical_upd_impl_int m sigma m xc zero_inta)
    x_a)
 ()) ())
 (imp_nfoldli (inv_fun bia) (fn _ => (fn () => true))
   (fn aia => fn bid =>
     (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid) ()) ())
       (fn xb =>
         repair_pair_impl_int m xb zero_nata (constraint_clk aia)))))))))));
      in
        (fn ai => fn bi =>
          (if null bi then (fn () => [])
            else imp_nfoldli (trans_impl ai) (fn _ => (fn () => true))
                   (fn xc => fn sigma =>
                     let
                       val (a1, (_, (a1b, a2b))) = xc;
                     in
                       (fn f_ => fn () => f_
                         ((heap_map (amtx_copy (heap_DBMEntry heap_int)) bi) ())
                         ())
                         (fn x =>
                           (fn f_ => fn () => f_
                             ((imp_nfoldli x (fn _ => (fn () => true))
                                (fn xb => fn sigmaa =>
                                  (fn f_ => fn () => f_
                                    ((pR_CONST e_op_impl ai a1b a1 a2b xb) ())
                                    ())
                                    (fn x_c =>
                                      (fn f_ => fn () => f_
((check_diag_impl_int m x_c) ()) ())
(fn x_e => (fn () => (if x_e then sigmaa else op_list_prepend x_c sigmaa)))))
                                [])
                             ()) ())
                             (fn x_d =>
                               (fn () => (op_list_prepend (a2b, x_d) sigma))))
                     end)
                   []))
      end;
    val _ = Timing.start_timer ();
  in
    (fn f_ => fn () => f_
      (((fn f_ => fn () => f_
          ((ht_new
             (hashable_prod (hashable_list hashable_nat)
                (hashable_list hashable_int),
               heap_prod (heap_list heap_nat) (heap_list heap_int))
             (heap_list (heap_array (typerep_DBMEntry typerep_int))))
          ()) ())
         (imp_nfoldli m_list (fn _ => (fn () => true))
           (fn xc => fn sigma =>
             (fn f_ => fn () => f_
               ((imp_nfoldli (snd xc) (fn _ => (fn () => true))
                  (fn xg => fn sigmaa =>
                    (fn f_ => fn () => f_ (((fn () => Array.fromList xg)) ())
                      ())
                      (fn x_g => (fn () => (x_g :: sigmaa))))
                  [])
               ()) ())
               (fn x_e =>
                 ht_update
                   (equal_prod (equal_list equal_nat) (equal_list equal_int),
                     hashable_prod (hashable_list hashable_nat)
                       (hashable_list hashable_int),
                     heap_prod (heap_list heap_nat) (heap_list heap_int))
                   (heap_list (heap_array (typerep_DBMEntry typerep_int)))
                   (fst xc) x_e sigma))))
      ()) ())
      (fn m_table =>
        let
          val _ = Timing.save_time "Time for loading certificate";
        in
          (fn f_ => fn () => f_
            ((certify_unreachable_impl_inner
               (equal_prod (equal_list equal_nat) (equal_list equal_int),
                 hashable_prod (hashable_list hashable_nat)
                   (hashable_list hashable_int),
                 heap_prod (heap_list heap_nat) (heap_list heap_int))
               (heap_array (typerep_DBMEntry typerep_int)) fi pi copyi lei l_0i
               s_0i succsi (split_ka num_split) l_list m_table)
            ()) ())
            (fn a => (fn () => a))
        end)
  end;

fun certificate_checker num_split dc m_list broadcast bounds automata m
  num_states num_actions k l_0 s_0 formula =
  let
    val l_list = map fst m_list;
  in
    (case certificate_checker_pre l_list m_list broadcast bounds automata m
            num_states num_actions k l_0 s_0 formula
      of true =>
        (fn f_ => fn () => f_
          ((if dc
             then no_deadlock_certifier broadcast bounds automata m num_states
                    num_actions l_0 s_0 l_list m_list num_split
             else unreachability_checker broadcast bounds automata m num_states
                    num_actions l_0 s_0 formula l_list m_list num_split)
          ()) ())
          (fn r => (fn () => (SOME r)))
      | false => (fn () => NONE))
  end;

fun rename_check num_split dc broadcast bounds automata k l_0 s_0 formula m
  num_states num_actions renum_acts renum_vars renum_clocks renum_states
  state_space =
  (case do_rename_mc show_int (show_list show_char) (show_list show_char)
          (show_list show_char)
          (fn _ => fn _ => certificate_checker num_split dc state_space) dc
          broadcast bounds automata k l_0 s_0 formula m num_states num_actions
          renum_acts renum_vars renum_clocks renum_states
          (fn _ => fn _ =>
            [Chara (false, false, false, false, false, true, false, false)])
          (fn _ =>
            [Chara (false, false, false, false, false, true, false, false)])
          (fn _ =>
            [Chara (false, false, false, false, false, true, false, false)])
    of NONE => (fn () => Renaming_Failed)
    | SOME r =>
      (fn f_ => fn () => f_ (r ()) ())
        (fn a =>
          (case a of NONE => (fn () => Preconds_Unsat)
            | SOME true => (fn () => Sat) | SOME false => (fn () => Unsat))));

fun list_of_json_object obj =
  (case obj of Object a => Result a | Arraya _ => Error ["Not an object"]
    | String _ => Error ["Not an object"] | Int _ => Error ["Not an object"]
    | Nata _ => Error ["Not an object"] | Rat _ => Error ["Not an object"]
    | Boolean _ => Error ["Not an object"] | Null => Error ["Not an object"]);

fun nat_renaming_of_json max_id json =
  binda (list_of_json_object json)
    (fn vars =>
      binda (combine_map
              (fn (a, b) =>
                binda (parse lx_nat (implode a))
                  (fn aa => binda (of_nat b) (fn ba => Result (aa, ba))))
              vars)
        (fn varsa =>
          let
            val ids = image fst (Set varsa);
            val missing =
              filter (fn i => not (member equal_nat i ids))
                (upt zero_nata max_id);
            val m = the o map_of_debug (equal_nat, show_nat) varsa;
            val a =
              extend_domain equal_nat (one_nat, plus_nat) m missing
                (size_list varsa);
          in
            Result a
          end));

fun renaming_of_json json =
  binda (list_of_json_object json)
    (fn vars =>
      binda (combine_map
              (fn (a, b) => binda (of_nat b) (fn ba => Result (implode a, ba)))
              vars)
        (fn varsa =>
          Result (the o map_of_debug (equal_literal, show_literal) varsa)));

fun convert_renaming ids_to_names process_names_to_index json =
  binda (of_object json)
    (fn jsona =>
      binda (geta (show_list show_char) jsona
              [Chara (false, true, true, false, true, true, true, false),
                Chara (true, false, false, false, false, true, true, false),
                Chara (false, true, false, false, true, true, true, false),
                Chara (true, true, false, false, true, true, true, false)])
        (fn vars =>
          binda (renaming_of_json vars)
            (fn var_renaming =>
              binda (geta (show_list show_char) jsona
                      [Chara (true, true, false, false, false, true, true,
                               false),
                        Chara (false, false, true, true, false, true, true,
                                false),
                        Chara (true, true, true, true, false, true, true,
                                false),
                        Chara (true, true, false, false, false, true, true,
                                false),
                        Chara (true, true, false, true, false, true, true,
                                false),
                        Chara (true, true, false, false, true, true, true,
                                false)])
                (fn clocks =>
                  binda (renaming_of_json clocks)
                    (fn clock_renaming =>
                      binda (geta (show_list show_char) jsona
                              [Chara (false, false, false, false, true, true,
                                       true, false),
                                Chara (false, true, false, false, true, true,
true, false),
                                Chara (true, true, true, true, false, true,
true, false),
                                Chara (true, true, false, false, false, true,
true, false),
                                Chara (true, false, true, false, false, true,
true, false),
                                Chara (true, true, false, false, true, true,
true, false),
                                Chara (true, true, false, false, true, true,
true, false),
                                Chara (true, false, true, false, false, true,
true, false),
                                Chara (true, true, false, false, true, true,
true, false)])
                        (fn processes =>
                          binda (renaming_of_json processes)
                            (fn process_renaming =>
                              binda (geta (show_list show_char) jsona
                                      [Chara
 (false, false, true, true, false, true, true, false),
Chara (true, true, true, true, false, true, true, false),
Chara (true, true, false, false, false, true, true, false),
Chara (true, false, false, false, false, true, true, false),
Chara (false, false, true, false, true, true, true, false),
Chara (true, false, false, true, false, true, true, false),
Chara (true, true, true, true, false, true, true, false),
Chara (false, true, true, true, false, true, true, false),
Chara (true, true, false, false, true, true, true, false)])
                                (fn locations =>
                                  binda (list_of_json_object locations)
                                    (fn locationsa =>
                                      binda
(combine_map
  (fn (name, renaming) =>
    let
      val p_num = process_names_to_index (implode name);
    in
      binda (assert (equal_nata (process_renaming (implode name)) p_num)
              ("Process renamings do not agree on " ^ implode name))
        (fn _ =>
          let
            val max_id = nat_of_integer (1000 : IntInf.int);
          in
            binda (nat_renaming_of_json max_id renaming)
              (fn renaminga => Result (p_num, renaminga))
          end)
    end)
  locationsa)
(fn locationsb =>
  let
    val location_renaming = the o map_of equal_nat locationsb;
  in
    Result (var_renaming, (clock_renaming, location_renaming))
  end))))))))));

fun unreachability_checker2 broadcast bounds automata m num_states num_actions
  l_0 s_0 formula l_list m_list num_split =
  let
    val states_ia =
      map (states_i automata) (upt zero_nata (size_list automata));
    val check_states =
      (fn (l, s) =>
        equal_nata (size_list l) (size_list automata) andalso
          all_interval_nat
            (fn i => member equal_nat (nth l i) (nth states_ia i)) zero_nata
            (size_list automata) andalso
          (equal_nata (size_list s) (n_vs bounds) andalso
            check_boundedi bounds s));
    val fi = (fn xi => (fn () => let
                                   val ((a, b), _) = xi;
                                 in
                                   hd_of_formulai equal_nat formula a b
                                 end));
    val pi =
      (fn (a1, a2) =>
        (fn f_ => fn () => f_
          ((imp_for_int zero_nata (plus_nata m one_nata) (fn a => (fn () => a))
             (fn xc => fn _ =>
               imp_for_int zero_nata (plus_nata m one_nata)
                 (fn a => (fn () => a))
                 (fn xf => fn _ =>
                   imp_for_int zero_nata (plus_nata m one_nata)
                     (fn a => (fn () => a))
                     (fn xj => fn _ =>
                       (fn f_ => fn () => f_
                         ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (xc, xj))
                         ()) ())
                         (fn x_i =>
                           (fn f_ => fn () => f_
                             ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                (xc, xf))
                             ()) ())
                             (fn x =>
                               (fn f_ => fn () => f_
                                 ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                    (xf, xj))
                                 ()) ())
                                 (fn xa =>
                                   (fn () =>
                                     (dbm_le_int x_i (dbm_add_int x xa)))))))
                     true)
                 true)
             true)
          ()) ())
          (fn x =>
            (fn f_ => fn () => f_ ((check_diag_impl_int m a2) ()) ())
              (fn xa =>
                (fn f_ => fn () => f_
                  ((imp_for_int zero_nata (plus_nata m one_nata)
                     (fn a => (fn () => a))
                     (fn xc => fn _ =>
                       (fn f_ => fn () => f_
                         ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (xc, xc))
                         ()) ())
                         (fn x_d => (fn () => (dbm_le_int x_d (Le zero_inta)))))
                     true)
                  ()) ())
                  (fn xb =>
                    (fn f_ => fn () => f_
                      ((imp_for_int zero_nata (plus_nata m one_nata)
                         (fn a => (fn () => a))
                         (fn xc => fn _ =>
                           (fn f_ => fn () => f_
                             ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                (zero_nata, xc))
                             ()) ())
                             (fn x_e =>
                               (fn () => (dbm_le_int x_e (Le zero_inta)))))
                         true)
                      ()) ())
                      (fn xc =>
                        (fn () =>
                          (check_states a1 andalso
                            ((x orelse xa) andalso (xb andalso xc)))))))));
    val copyi = amtx_copy (heap_DBMEntry heap_int);
    val lei = dbm_subset_impl_int m;
    val l_0i =
      (fn () =>
        (l_0, map (the o map_of equal_nat s_0) (upt zero_nata (n_vs bounds))));
    val s_0i =
      amtx_dflt (heap_DBMEntry heap_int) (suc m) (suc m) (Le zero_inta);
    val succsi =
      let
        val n_ps = size_list automata;
        val invs =
          Vector.fromList
            (map (fn i =>
                   let
                     val ma =
                       default_map_of equal_nat [] (snd (snd (nth automata i)));
                     val mb =
                       Vector.fromList (map ma (upt zero_nata (num_states i)));
                   in
                     mb
                   end)
              (upt zero_nata n_ps));
        val inv_fun =
          (fn (l, _) =>
            maps (fn i => sub (sub invs i) (nth l i)) (upt zero_nata n_ps));
        val trans_mapa = trans_map automata;
        val trans_i_map =
          (fn i => fn j =>
            map_filter
              (fn (b, a) =>
                let
                  val (g, aa) = a;
                  val (ab, (ma, l)) = aa;
                in
                  (case ab of In _ => NONE | Out _ => NONE
                    | Sil ac => SOME (b, (g, (ac, (ma, l)))))
                end)
              (trans_mapa i j));
        val int_trans_from_loc_impl =
          (fn p => fn l => fn la => fn s =>
            let
              val a = trans_i_map p l;
            in
              map_filter
                (fn (b, aa) =>
                  let
                    val (g, ab) = aa;
                    val (ac, (f, (r, lb))) = ab;
                    val sa = mk_updsi s f;
                  in
                    (if bvali (equal_int, linorder_int) s b andalso
                          check_boundedi bounds sa
                      then SOME (g, (Internal ac,
                                      (r, (list_update la p lb, sa))))
                      else NONE)
                  end)
                a
            end);
        val int_trans_from_vec_impl =
          (fn pairs => fn l => fn s =>
            maps (fn (p, la) => int_trans_from_loc_impl p la l s) pairs);
        val int_trans_from_all_impl =
          (fn l => fn s =>
            maps (fn p => int_trans_from_loc_impl p (nth l p) l s)
              (upt zero_nata n_ps));
        val trans_out_map =
          (fn i => fn j =>
            map_filter
              (fn (b, a) =>
                let
                  val (g, aa) = a;
                  val (ab, (ma, l)) = aa;
                in
                  (case ab of In _ => NONE
                    | Out ac => SOME (b, (g, (ac, (ma, l)))) | Sil _ => NONE)
                end)
              (trans_mapa i j));
        val trans_in_map =
          (fn i => fn j =>
            map_filter
              (fn (b, a) =>
                let
                  val (g, aa) = a;
                  val (ab, (ma, l)) = aa;
                in
                  (case ab of In ac => SOME (b, (g, (ac, (ma, l))))
                    | Out _ => NONE | Sil _ => NONE)
                end)
              (trans_mapa i j));
        val trans_out_broad_grouped =
          (fn i => fn j =>
            actions_by_statea num_actions
              (map_filter
                (fn (b, a) =>
                  let
                    val (g, aa) = a;
                    val (ab, (ma, l)) = aa;
                  in
                    (case ab of In _ => NONE
                      | Out ac =>
                        (if membera equal_nat broadcast ac
                          then SOME (b, (g, (ac, (ma, l)))) else NONE)
                      | Sil _ => NONE)
                  end)
                (trans_mapa i j)));
        val trans_in_broad_grouped =
          (fn i => fn j =>
            actions_by_statea num_actions
              (map_filter
                (fn (b, a) =>
                  let
                    val (g, aa) = a;
                    val (ab, (ma, l)) = aa;
                  in
                    (case ab
                      of In ac =>
                        (if membera equal_nat broadcast ac
                          then SOME (b, (g, (ac, (ma, l)))) else NONE)
                      | Out _ => NONE | Sil _ => NONE)
                  end)
                (trans_mapa i j)));
        val broad_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_commited broadcast bounds automata l;
              val ina =
                map (fn p => trans_in_broad_grouped p (nth l p))
                  (upt zero_nata n_ps);
              val out =
                map (fn p => trans_out_broad_grouped p (nth l p))
                  (upt zero_nata n_ps);
              val inb =
                map (map (filter
                           (fn (b, _) => bvali (equal_int, linorder_int) s b)))
                  ina;
              val outa =
                map (map (filter
                           (fn (b, _) => bvali (equal_int, linorder_int) s b)))
                  out;
            in
              (if null pairs
                then maps (fn a =>
                            maps (fn p =>
                                   let
                                     val outs = nth (nth outa p) a;
                                   in
                                     (if null outs then []
                                       else let
      val combs = make_combs broadcast bounds automata p a inb;
      val outsa = map (fn aa => (p, aa)) outs;
      val combsa =
        (if null combs then map (fn x => [x]) outsa
          else maps (fn x => map (fn aa => x :: aa) combs) outsa);
      val init = ([], (Broad a, ([], (l, s))));
    in
      compute_upds_impl bounds init combsa
    end)
                                   end)
                              (upt zero_nata n_ps))
                       (upt zero_nata num_actions)
                else maps (fn a =>
                            let
                              val ins_commited =
                                map_filter
                                  (fn (p, _) =>
                                    (if not (null (nth (nth inb p) a))
                                      then SOME p else NONE))
                                  pairs;
                              val always_commited =
                                less_nat one_nata (size_list ins_commited);
                            in
                              maps (fn p =>
                                     let
                                       val outs = nth (nth outa p) a;
                                     in
                                       (if null outs then []
 else (if not always_commited andalso
            ((equal_lista equal_nat ins_commited [p] orelse
               null ins_commited) andalso
              not (list_ex (fn (q, _) => equal_nata q p) pairs))
        then []
        else let
               val combs = make_combs broadcast bounds automata p a inb;
               val outsa = map (fn aa => (p, aa)) outs;
               val combsa =
                 (if null combs then map (fn x => [x]) outsa
                   else maps (fn x => map (fn aa => x :: aa) combs) outsa);
               val init = ([], (Broad a, ([], (l, s))));
             in
               compute_upds_impl bounds init combsa
             end))
                                     end)
                                (upt zero_nata n_ps)
                            end)
                       (upt zero_nata num_actions))
            end);
        val bin_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_commited broadcast bounds automata l;
              val ina =
                all_actions_by_state broadcast bounds automata num_actions
                  trans_in_map l;
              val out =
                all_actions_by_state broadcast bounds automata num_actions
                  trans_out_map l;
            in
              (if null pairs
                then maps (fn a =>
                            pairs_by_action_impl bounds l s (nth out a)
                              (nth ina a))
                       (bin_actions broadcast num_actions)
                else let
                       val in2 =
                         all_actions_from_vec num_actions trans_in_map pairs;
                       val out2 =
                         all_actions_from_vec num_actions trans_out_map pairs;
                     in
                       maps (fn a =>
                              pairs_by_action_impl bounds l s (nth out a)
                                (nth in2 a))
                         (bin_actions broadcast num_actions) @
                         maps (fn a =>
                                pairs_by_action_impl bounds l s (nth out2 a)
                                  (nth ina a))
                           (bin_actions broadcast num_actions)
                     end)
            end);
        val int_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_commited broadcast bounds automata l;
            in
              (if null pairs then int_trans_from_all_impl l s
                else int_trans_from_vec_impl pairs l s)
            end);
        val trans_impl =
          (fn st =>
            int_trans_impl st @ bin_trans_impl st @ broad_trans_impl st);
        val e_op_impl =
          (fn ai => fn bic => fn bib => fn bia => fn bi =>
            (fn f_ => fn () => f_ ((up_canonical_upd_impl_int m bi m) ()) ())
              (fn x =>
                (fn f_ => fn () => f_
                  ((imp_nfoldli (inv_fun ai) (fn _ => (fn () => true))
                     (fn aia => fn bid =>
                       (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid)
                         ()) ())
                         (fn xa =>
                           repair_pair_impl_int m xa zero_nata
                             (constraint_clk aia)))
                     x)
                  ()) ())
                  (fn xa =>
                    (fn f_ => fn () => f_ ((check_diag_impl_int m xa) ()) ())
                      (fn xaa =>
                        (fn f_ => fn () => f_
                          ((if xaa
                             then mtx_set (heap_DBMEntry heap_int) (suc m) xa
                                    (zero_nata, zero_nata) (Lt zero_inta)
                             else imp_nfoldli bib (fn _ => (fn () => true))
                                    (fn aia => fn bid =>
                                      (fn f_ => fn () => f_
((abstra_upd_impl_int m aia bid) ()) ())
(fn xb => repair_pair_impl_int m xb zero_nata (constraint_clk aia)))
                                    xa)
                          ()) ())
                          (fn x_a =>
                            (fn f_ => fn () => f_ ((check_diag_impl_int m x_a)
                              ()) ())
                              (fn x_b =>
                                (if x_b
                                  then mtx_set (heap_DBMEntry heap_int) (suc m)
 x_a (zero_nata, zero_nata) (Lt zero_inta)
                                  else (fn f_ => fn () => f_
 ((imp_nfoldli bic (fn _ => (fn () => true))
    (fn xc => fn sigma => reset_canonical_upd_impl_int m sigma m xc zero_inta)
    x_a)
 ()) ())
 (imp_nfoldli (inv_fun bia) (fn _ => (fn () => true))
   (fn aia => fn bid =>
     (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid) ()) ())
       (fn xb =>
         repair_pair_impl_int m xb zero_nata (constraint_clk aia)))))))))));
      in
        (fn ai => fn bi =>
          (if null bi then (fn () => [])
            else imp_nfoldli (trans_impl ai) (fn _ => (fn () => true))
                   (fn xc => fn sigma =>
                     let
                       val (a1, (_, (a1b, a2b))) = xc;
                     in
                       (fn f_ => fn () => f_
                         ((heap_map (amtx_copy (heap_DBMEntry heap_int)) bi) ())
                         ())
                         (fn x =>
                           (fn f_ => fn () => f_
                             ((imp_nfoldli x (fn _ => (fn () => true))
                                (fn xb => fn sigmaa =>
                                  (fn f_ => fn () => f_
                                    ((pR_CONST e_op_impl ai a1b a1 a2b xb) ())
                                    ())
                                    (fn x_c =>
                                      (fn f_ => fn () => f_
((check_diag_impl_int m x_c) ()) ())
(fn x_e => (fn () => (if x_e then sigmaa else op_list_prepend x_c sigmaa)))))
                                [])
                             ()) ())
                             (fn x_d =>
                               (fn () => (op_list_prepend (a2b, x_d) sigma))))
                     end)
                   []))
      end;
    val a =
      (fn f_ => fn () => f_
        ((ht_new
           (hashable_prod (hashable_list hashable_nat)
              (hashable_list hashable_int),
             heap_prod (heap_list heap_nat) (heap_list heap_int))
           (heap_list (heap_array (typerep_DBMEntry typerep_int))))
        ()) ())
        (imp_nfoldli m_list (fn _ => (fn () => true))
          (fn xc => fn sigma =>
            (fn f_ => fn () => f_
              ((imp_nfoldli (snd xc) (fn _ => (fn () => true))
                 (fn xg => fn sigmaa =>
                   (fn f_ => fn () => f_ (((fn () => Array.fromList xg)) ()) ())
                     (fn x_g => (fn () => (x_g :: sigmaa))))
                 [])
              ()) ())
              (fn x_e =>
                ht_update
                  (equal_prod (equal_list equal_nat) (equal_list equal_int),
                    hashable_prod (hashable_list hashable_nat)
                      (hashable_list hashable_int),
                    heap_prod (heap_list heap_nat) (heap_list heap_int))
                  (heap_list (heap_array (typerep_DBMEntry typerep_int)))
                  (fst xc) x_e sigma)));
  in
    certify_unreachable_impl2
      (equal_prod (equal_list equal_nat) (equal_list equal_int),
        hashable_prod (hashable_list hashable_nat) (hashable_list hashable_int),
        heap_prod (heap_list heap_nat) (heap_list heap_int))
      (heap_array (typerep_DBMEntry typerep_int)) fi pi copyi lei l_0i s_0i
      succsi (split_ka num_split) l_list a
  end;

fun no_deadlock_certifier2 broadcast bounds automata m num_states num_actions
  l_0 s_0 l_list m_list num_split =
  let
    val states_ia =
      map (states_i automata) (upt zero_nata (size_list automata));
    val check_states =
      (fn (l, s) =>
        equal_nata (size_list l) (size_list automata) andalso
          all_interval_nat
            (fn i => member equal_nat (nth l i) (nth states_ia i)) zero_nata
            (size_list automata) andalso
          (equal_nata (size_list s) (n_vs bounds) andalso
            check_boundedi bounds s));
    val fi =
      (fn (l, ma) =>
        (fn f_ => fn () => f_
          ((let
              val n_ps = size_list automata;
              val invs =
                Vector.fromList
                  (map (fn i =>
                         let
                           val mb =
                             default_map_of equal_nat []
                               (snd (snd (nth automata i)));
                           val mc =
                             Vector.fromList
                               (map mb (upt zero_nata (num_states i)));
                         in
                           mc
                         end)
                    (upt zero_nata n_ps));
              val inv_fun =
                (fn (la, _) =>
                  maps (fn i => sub (sub invs i) (nth la i))
                    (upt zero_nata n_ps));
              val trans_impl =
                let
                  val trans_mapa = trans_map automata;
                  val trans_i_map =
                    (fn i => fn j =>
                      map_filter
                        (fn (b, a) =>
                          let
                            val (g, aa) = a;
                            val (ab, (mb, la)) = aa;
                          in
                            (case ab of In _ => NONE | Out _ => NONE
                              | Sil ac => SOME (b, (g, (ac, (mb, la)))))
                          end)
                        (trans_mapa i j));
                  val int_trans_from_loc_impl =
                    (fn p => fn la => fn laa => fn s =>
                      let
                        val a = trans_i_map p la;
                      in
                        map_filter
                          (fn (b, aa) =>
                            let
                              val (g, ab) = aa;
                              val (ac, (f, (r, lb))) = ab;
                              val sa = mk_updsi s f;
                            in
                              (if bvali (equal_int, linorder_int) s b andalso
                                    check_boundedi bounds sa
                                then SOME (g,
    (Internal ac, (r, (list_update laa p lb, sa))))
                                else NONE)
                            end)
                          a
                      end);
                  val int_trans_from_vec_impl =
                    (fn pairs => fn la => fn s =>
                      maps (fn (p, laa) => int_trans_from_loc_impl p laa la s)
                        pairs);
                  val int_trans_from_all_impl =
                    (fn la => fn s =>
                      maps (fn p => int_trans_from_loc_impl p (nth la p) la s)
                        (upt zero_nata n_ps));
                  val trans_out_map =
                    (fn i => fn j =>
                      map_filter
                        (fn (b, a) =>
                          let
                            val (g, aa) = a;
                            val (ab, (mb, la)) = aa;
                          in
                            (case ab of In _ => NONE
                              | Out ac => SOME (b, (g, (ac, (mb, la))))
                              | Sil _ => NONE)
                          end)
                        (trans_mapa i j));
                  val trans_in_map =
                    (fn i => fn j =>
                      map_filter
                        (fn (b, a) =>
                          let
                            val (g, aa) = a;
                            val (ab, (mb, la)) = aa;
                          in
                            (case ab of In ac => SOME (b, (g, (ac, (mb, la))))
                              | Out _ => NONE | Sil _ => NONE)
                          end)
                        (trans_mapa i j));
                  val trans_out_broad_grouped =
                    (fn i => fn j =>
                      actions_by_statea num_actions
                        (map_filter
                          (fn (b, a) =>
                            let
                              val (g, aa) = a;
                              val (ab, (mb, la)) = aa;
                            in
                              (case ab of In _ => NONE
                                | Out ac =>
                                  (if membera equal_nat broadcast ac
                                    then SOME (b, (g, (ac, (mb, la))))
                                    else NONE)
                                | Sil _ => NONE)
                            end)
                          (trans_mapa i j)));
                  val trans_in_broad_grouped =
                    (fn i => fn j =>
                      actions_by_statea num_actions
                        (map_filter
                          (fn (b, a) =>
                            let
                              val (g, aa) = a;
                              val (ab, (mb, la)) = aa;
                            in
                              (case ab
                                of In ac =>
                                  (if membera equal_nat broadcast ac
                                    then SOME (b, (g, (ac, (mb, la))))
                                    else NONE)
                                | Out _ => NONE | Sil _ => NONE)
                            end)
                          (trans_mapa i j)));
                  val broad_trans_impl =
                    (fn (la, s) =>
                      let
                        val pairs = get_commited broadcast bounds automata la;
                        val ina =
                          map (fn p => trans_in_broad_grouped p (nth la p))
                            (upt zero_nata n_ps);
                        val out =
                          map (fn p => trans_out_broad_grouped p (nth la p))
                            (upt zero_nata n_ps);
                        val inb =
                          map (map (filter
                                     (fn (b, _) =>
                                       bvali (equal_int, linorder_int) s b)))
                            ina;
                        val outa =
                          map (map (filter
                                     (fn (b, _) =>
                                       bvali (equal_int, linorder_int) s b)))
                            out;
                      in
                        (if null pairs
                          then maps (fn a =>
                                      maps
(fn p =>
  let
    val outs = nth (nth outa p) a;
  in
    (if null outs then []
      else let
             val combs = make_combs broadcast bounds automata p a inb;
             val outsa = map (fn aa => (p, aa)) outs;
             val combsa =
               (if null combs then map (fn x => [x]) outsa
                 else maps (fn x => map (fn aa => x :: aa) combs) outsa);
             val init = ([], (Broad a, ([], (la, s))));
           in
             compute_upds_impl bounds init combsa
           end)
  end)
(upt zero_nata n_ps))
                                 (upt zero_nata num_actions)
                          else maps (fn a =>
                                      let
val ins_commited =
  map_filter
    (fn (p, _) => (if not (null (nth (nth inb p) a)) then SOME p else NONE))
    pairs;
val always_commited = less_nat one_nata (size_list ins_commited);
                                      in
maps (fn p =>
       let
         val outs = nth (nth outa p) a;
       in
         (if null outs then []
           else (if not always_commited andalso
                      ((equal_lista equal_nat ins_commited [p] orelse
                         null ins_commited) andalso
                        not (list_ex (fn (q, _) => equal_nata q p) pairs))
                  then []
                  else let
                         val combs =
                           make_combs broadcast bounds automata p a inb;
                         val outsa = map (fn aa => (p, aa)) outs;
                         val combsa =
                           (if null combs then map (fn x => [x]) outsa
                             else maps (fn x => map (fn aa => x :: aa) combs)
                                    outsa);
                         val init = ([], (Broad a, ([], (la, s))));
                       in
                         compute_upds_impl bounds init combsa
                       end))
       end)
  (upt zero_nata n_ps)
                                      end)
                                 (upt zero_nata num_actions))
                      end);
                  val bin_trans_impl =
                    (fn (la, s) =>
                      let
                        val pairs = get_commited broadcast bounds automata la;
                        val ina =
                          all_actions_by_state broadcast bounds automata
                            num_actions trans_in_map la;
                        val out =
                          all_actions_by_state broadcast bounds automata
                            num_actions trans_out_map la;
                      in
                        (if null pairs
                          then maps (fn a =>
                                      pairs_by_action_impl bounds la s
(nth out a) (nth ina a))
                                 (bin_actions broadcast num_actions)
                          else let
                                 val in2 =
                                   all_actions_from_vec num_actions trans_in_map
                                     pairs;
                                 val out2 =
                                   all_actions_from_vec num_actions
                                     trans_out_map pairs;
                               in
                                 maps (fn a =>
pairs_by_action_impl bounds la s (nth out a) (nth in2 a))
                                   (bin_actions broadcast num_actions) @
                                   maps (fn a =>
  pairs_by_action_impl bounds la s (nth out2 a) (nth ina a))
                                     (bin_actions broadcast num_actions)
                               end)
                      end);
                  val int_trans_impl =
                    (fn (la, s) =>
                      let
                        val pairs = get_commited broadcast bounds automata la;
                      in
                        (if null pairs then int_trans_from_all_impl la s
                          else int_trans_from_vec_impl pairs la s)
                      end);
                in
                  (fn st =>
                    int_trans_impl st @ bin_trans_impl st @ broad_trans_impl st)
                end;
            in
              (fn ai => fn bi =>
                (fn f_ => fn () => f_
                  ((imp_nfoldli (trans_impl ai) (fn _ => (fn () => true))
                     (fn xb => fn sigma =>
                       (fn f_ => fn () => f_
                         ((v_dbm_impl
                            (linordered_cancel_ab_monoid_add_int, heap_int) m)
                         ()) ())
                         (fn x =>
                           (fn f_ => fn () => f_
                             ((abstr_FW_impl_int m
                                (inv_fun (snd (snd (snd xb)))) x)
                             ()) ())
                             (fn xa =>
                               (fn f_ => fn () => f_
                                 ((pre_reset_list_impl m xa
                                    (fst (snd (snd xb))))
                                 ()) ())
                                 (fn xc =>
                                   (fn f_ => fn () => f_
                                     ((abstr_FW_impl_int m (fst xb) xc) ()) ())
                                     (fn xd =>
                                       (fn f_ => fn () => f_
 ((abstr_FW_impl_int m (inv_fun ai) xd) ()) ())
 (fn xe =>
   (fn f_ => fn () => f_ ((down_impl_int m xe) ()) ())
     (fn x_c => (fn () => (x_c :: sigma)))))))))
                     [])
                  ()) ())
                  (fn x => dbm_subset_fed_impl m bi (op_list_rev x)))
            end
              l
             ma)
          ()) ())
          (fn r => (fn () => (not r))));
    val pi =
      (fn (a1, a2) =>
        (fn f_ => fn () => f_
          ((imp_for_int zero_nata (plus_nata m one_nata) (fn a => (fn () => a))
             (fn xc => fn _ =>
               imp_for_int zero_nata (plus_nata m one_nata)
                 (fn a => (fn () => a))
                 (fn xf => fn _ =>
                   imp_for_int zero_nata (plus_nata m one_nata)
                     (fn a => (fn () => a))
                     (fn xj => fn _ =>
                       (fn f_ => fn () => f_
                         ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (xc, xj))
                         ()) ())
                         (fn x_i =>
                           (fn f_ => fn () => f_
                             ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                (xc, xf))
                             ()) ())
                             (fn x =>
                               (fn f_ => fn () => f_
                                 ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                    (xf, xj))
                                 ()) ())
                                 (fn xa =>
                                   (fn () =>
                                     (dbm_le_int x_i (dbm_add_int x xa)))))))
                     true)
                 true)
             true)
          ()) ())
          (fn x =>
            (fn f_ => fn () => f_ ((check_diag_impl_int m a2) ()) ())
              (fn xa =>
                (fn f_ => fn () => f_
                  ((imp_for_int zero_nata (plus_nata m one_nata)
                     (fn a => (fn () => a))
                     (fn xc => fn _ =>
                       (fn f_ => fn () => f_
                         ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (xc, xc))
                         ()) ())
                         (fn x_d => (fn () => (dbm_le_int x_d (Le zero_inta)))))
                     true)
                  ()) ())
                  (fn xb =>
                    (fn f_ => fn () => f_
                      ((imp_for_int zero_nata (plus_nata m one_nata)
                         (fn a => (fn () => a))
                         (fn xc => fn _ =>
                           (fn f_ => fn () => f_
                             ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                (zero_nata, xc))
                             ()) ())
                             (fn x_e =>
                               (fn () => (dbm_le_int x_e (Le zero_inta)))))
                         true)
                      ()) ())
                      (fn xc =>
                        (fn () =>
                          (check_states a1 andalso
                            ((x orelse xa) andalso (xb andalso xc)))))))));
    val copyi = amtx_copy (heap_DBMEntry heap_int);
    val lei = dbm_subset_impl_int m;
    val l_0i =
      (fn () =>
        (l_0, map (the o map_of equal_nat s_0) (upt zero_nata (n_vs bounds))));
    val s_0i =
      amtx_dflt (heap_DBMEntry heap_int) (suc m) (suc m) (Le zero_inta);
    val succsi =
      let
        val n_ps = size_list automata;
        val invs =
          Vector.fromList
            (map (fn i =>
                   let
                     val ma =
                       default_map_of equal_nat [] (snd (snd (nth automata i)));
                     val mb =
                       Vector.fromList (map ma (upt zero_nata (num_states i)));
                   in
                     mb
                   end)
              (upt zero_nata n_ps));
        val inv_fun =
          (fn (l, _) =>
            maps (fn i => sub (sub invs i) (nth l i)) (upt zero_nata n_ps));
        val trans_mapa = trans_map automata;
        val trans_i_map =
          (fn i => fn j =>
            map_filter
              (fn (b, a) =>
                let
                  val (g, aa) = a;
                  val (ab, (ma, l)) = aa;
                in
                  (case ab of In _ => NONE | Out _ => NONE
                    | Sil ac => SOME (b, (g, (ac, (ma, l)))))
                end)
              (trans_mapa i j));
        val int_trans_from_loc_impl =
          (fn p => fn l => fn la => fn s =>
            let
              val a = trans_i_map p l;
            in
              map_filter
                (fn (b, aa) =>
                  let
                    val (g, ab) = aa;
                    val (ac, (f, (r, lb))) = ab;
                    val sa = mk_updsi s f;
                  in
                    (if bvali (equal_int, linorder_int) s b andalso
                          check_boundedi bounds sa
                      then SOME (g, (Internal ac,
                                      (r, (list_update la p lb, sa))))
                      else NONE)
                  end)
                a
            end);
        val int_trans_from_vec_impl =
          (fn pairs => fn l => fn s =>
            maps (fn (p, la) => int_trans_from_loc_impl p la l s) pairs);
        val int_trans_from_all_impl =
          (fn l => fn s =>
            maps (fn p => int_trans_from_loc_impl p (nth l p) l s)
              (upt zero_nata n_ps));
        val trans_out_map =
          (fn i => fn j =>
            map_filter
              (fn (b, a) =>
                let
                  val (g, aa) = a;
                  val (ab, (ma, l)) = aa;
                in
                  (case ab of In _ => NONE
                    | Out ac => SOME (b, (g, (ac, (ma, l)))) | Sil _ => NONE)
                end)
              (trans_mapa i j));
        val trans_in_map =
          (fn i => fn j =>
            map_filter
              (fn (b, a) =>
                let
                  val (g, aa) = a;
                  val (ab, (ma, l)) = aa;
                in
                  (case ab of In ac => SOME (b, (g, (ac, (ma, l))))
                    | Out _ => NONE | Sil _ => NONE)
                end)
              (trans_mapa i j));
        val trans_out_broad_grouped =
          (fn i => fn j =>
            actions_by_statea num_actions
              (map_filter
                (fn (b, a) =>
                  let
                    val (g, aa) = a;
                    val (ab, (ma, l)) = aa;
                  in
                    (case ab of In _ => NONE
                      | Out ac =>
                        (if membera equal_nat broadcast ac
                          then SOME (b, (g, (ac, (ma, l)))) else NONE)
                      | Sil _ => NONE)
                  end)
                (trans_mapa i j)));
        val trans_in_broad_grouped =
          (fn i => fn j =>
            actions_by_statea num_actions
              (map_filter
                (fn (b, a) =>
                  let
                    val (g, aa) = a;
                    val (ab, (ma, l)) = aa;
                  in
                    (case ab
                      of In ac =>
                        (if membera equal_nat broadcast ac
                          then SOME (b, (g, (ac, (ma, l)))) else NONE)
                      | Out _ => NONE | Sil _ => NONE)
                  end)
                (trans_mapa i j)));
        val broad_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_commited broadcast bounds automata l;
              val ina =
                map (fn p => trans_in_broad_grouped p (nth l p))
                  (upt zero_nata n_ps);
              val out =
                map (fn p => trans_out_broad_grouped p (nth l p))
                  (upt zero_nata n_ps);
              val inb =
                map (map (filter
                           (fn (b, _) => bvali (equal_int, linorder_int) s b)))
                  ina;
              val outa =
                map (map (filter
                           (fn (b, _) => bvali (equal_int, linorder_int) s b)))
                  out;
            in
              (if null pairs
                then maps (fn a =>
                            maps (fn p =>
                                   let
                                     val outs = nth (nth outa p) a;
                                   in
                                     (if null outs then []
                                       else let
      val combs = make_combs broadcast bounds automata p a inb;
      val outsa = map (fn aa => (p, aa)) outs;
      val combsa =
        (if null combs then map (fn x => [x]) outsa
          else maps (fn x => map (fn aa => x :: aa) combs) outsa);
      val init = ([], (Broad a, ([], (l, s))));
    in
      compute_upds_impl bounds init combsa
    end)
                                   end)
                              (upt zero_nata n_ps))
                       (upt zero_nata num_actions)
                else maps (fn a =>
                            let
                              val ins_commited =
                                map_filter
                                  (fn (p, _) =>
                                    (if not (null (nth (nth inb p) a))
                                      then SOME p else NONE))
                                  pairs;
                              val always_commited =
                                less_nat one_nata (size_list ins_commited);
                            in
                              maps (fn p =>
                                     let
                                       val outs = nth (nth outa p) a;
                                     in
                                       (if null outs then []
 else (if not always_commited andalso
            ((equal_lista equal_nat ins_commited [p] orelse
               null ins_commited) andalso
              not (list_ex (fn (q, _) => equal_nata q p) pairs))
        then []
        else let
               val combs = make_combs broadcast bounds automata p a inb;
               val outsa = map (fn aa => (p, aa)) outs;
               val combsa =
                 (if null combs then map (fn x => [x]) outsa
                   else maps (fn x => map (fn aa => x :: aa) combs) outsa);
               val init = ([], (Broad a, ([], (l, s))));
             in
               compute_upds_impl bounds init combsa
             end))
                                     end)
                                (upt zero_nata n_ps)
                            end)
                       (upt zero_nata num_actions))
            end);
        val bin_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_commited broadcast bounds automata l;
              val ina =
                all_actions_by_state broadcast bounds automata num_actions
                  trans_in_map l;
              val out =
                all_actions_by_state broadcast bounds automata num_actions
                  trans_out_map l;
            in
              (if null pairs
                then maps (fn a =>
                            pairs_by_action_impl bounds l s (nth out a)
                              (nth ina a))
                       (bin_actions broadcast num_actions)
                else let
                       val in2 =
                         all_actions_from_vec num_actions trans_in_map pairs;
                       val out2 =
                         all_actions_from_vec num_actions trans_out_map pairs;
                     in
                       maps (fn a =>
                              pairs_by_action_impl bounds l s (nth out a)
                                (nth in2 a))
                         (bin_actions broadcast num_actions) @
                         maps (fn a =>
                                pairs_by_action_impl bounds l s (nth out2 a)
                                  (nth ina a))
                           (bin_actions broadcast num_actions)
                     end)
            end);
        val int_trans_impl =
          (fn (l, s) =>
            let
              val pairs = get_commited broadcast bounds automata l;
            in
              (if null pairs then int_trans_from_all_impl l s
                else int_trans_from_vec_impl pairs l s)
            end);
        val trans_impl =
          (fn st =>
            int_trans_impl st @ bin_trans_impl st @ broad_trans_impl st);
        val e_op_impl =
          (fn ai => fn bic => fn bib => fn bia => fn bi =>
            (fn f_ => fn () => f_ ((up_canonical_upd_impl_int m bi m) ()) ())
              (fn x =>
                (fn f_ => fn () => f_
                  ((imp_nfoldli (inv_fun ai) (fn _ => (fn () => true))
                     (fn aia => fn bid =>
                       (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid)
                         ()) ())
                         (fn xa =>
                           repair_pair_impl_int m xa zero_nata
                             (constraint_clk aia)))
                     x)
                  ()) ())
                  (fn xa =>
                    (fn f_ => fn () => f_ ((check_diag_impl_int m xa) ()) ())
                      (fn xaa =>
                        (fn f_ => fn () => f_
                          ((if xaa
                             then mtx_set (heap_DBMEntry heap_int) (suc m) xa
                                    (zero_nata, zero_nata) (Lt zero_inta)
                             else imp_nfoldli bib (fn _ => (fn () => true))
                                    (fn aia => fn bid =>
                                      (fn f_ => fn () => f_
((abstra_upd_impl_int m aia bid) ()) ())
(fn xb => repair_pair_impl_int m xb zero_nata (constraint_clk aia)))
                                    xa)
                          ()) ())
                          (fn x_a =>
                            (fn f_ => fn () => f_ ((check_diag_impl_int m x_a)
                              ()) ())
                              (fn x_b =>
                                (if x_b
                                  then mtx_set (heap_DBMEntry heap_int) (suc m)
 x_a (zero_nata, zero_nata) (Lt zero_inta)
                                  else (fn f_ => fn () => f_
 ((imp_nfoldli bic (fn _ => (fn () => true))
    (fn xc => fn sigma => reset_canonical_upd_impl_int m sigma m xc zero_inta)
    x_a)
 ()) ())
 (imp_nfoldli (inv_fun bia) (fn _ => (fn () => true))
   (fn aia => fn bid =>
     (fn f_ => fn () => f_ ((abstra_upd_impl_int m aia bid) ()) ())
       (fn xb =>
         repair_pair_impl_int m xb zero_nata (constraint_clk aia)))))))))));
      in
        (fn ai => fn bi =>
          (if null bi then (fn () => [])
            else imp_nfoldli (trans_impl ai) (fn _ => (fn () => true))
                   (fn xc => fn sigma =>
                     let
                       val (a1, (_, (a1b, a2b))) = xc;
                     in
                       (fn f_ => fn () => f_
                         ((heap_map (amtx_copy (heap_DBMEntry heap_int)) bi) ())
                         ())
                         (fn x =>
                           (fn f_ => fn () => f_
                             ((imp_nfoldli x (fn _ => (fn () => true))
                                (fn xb => fn sigmaa =>
                                  (fn f_ => fn () => f_
                                    ((pR_CONST e_op_impl ai a1b a1 a2b xb) ())
                                    ())
                                    (fn x_c =>
                                      (fn f_ => fn () => f_
((check_diag_impl_int m x_c) ()) ())
(fn x_e => (fn () => (if x_e then sigmaa else op_list_prepend x_c sigmaa)))))
                                [])
                             ()) ())
                             (fn x_d =>
                               (fn () => (op_list_prepend (a2b, x_d) sigma))))
                     end)
                   []))
      end;
    val a =
      (fn f_ => fn () => f_
        ((ht_new
           (hashable_prod (hashable_list hashable_nat)
              (hashable_list hashable_int),
             heap_prod (heap_list heap_nat) (heap_list heap_int))
           (heap_list (heap_array (typerep_DBMEntry typerep_int))))
        ()) ())
        (imp_nfoldli m_list (fn _ => (fn () => true))
          (fn xc => fn sigma =>
            (fn f_ => fn () => f_
              ((imp_nfoldli (snd xc) (fn _ => (fn () => true))
                 (fn xg => fn sigmaa =>
                   (fn f_ => fn () => f_ (((fn () => Array.fromList xg)) ()) ())
                     (fn x_g => (fn () => (x_g :: sigmaa))))
                 [])
              ()) ())
              (fn x_e =>
                ht_update
                  (equal_prod (equal_list equal_nat) (equal_list equal_int),
                    hashable_prod (hashable_list hashable_nat)
                      (hashable_list hashable_int),
                    heap_prod (heap_list heap_nat) (heap_list heap_int))
                  (heap_list (heap_array (typerep_DBMEntry typerep_int)))
                  (fst xc) x_e sigma)));
  in
    certify_unreachable_impl2
      (equal_prod (equal_list equal_nat) (equal_list equal_int),
        hashable_prod (hashable_list hashable_nat) (hashable_list hashable_int),
        heap_prod (heap_list heap_nat) (heap_list heap_int))
      (heap_array (typerep_DBMEntry typerep_int)) fi pi copyi lei l_0i s_0i
      succsi (split_ka num_split) l_list a
  end;

fun certificate_checker2 num_split dc m_list broadcast bounds automata m
  num_states num_actions k l_0 s_0 formula =
  let
    val l_list = map fst m_list;
  in
    (case certificate_checker_pre l_list m_list broadcast bounds automata m
            num_states num_actions k l_0 s_0 formula
      of true =>
        (if dc
          then no_deadlock_certifier2 broadcast bounds automata m num_states
                 num_actions l_0 s_0 l_list m_list num_split
          else unreachability_checker2 broadcast bounds automata m num_states
                 num_actions l_0 s_0 formula l_list m_list num_split)
      | false => false)
  end;

fun rename_check2 num_split dc broadcast bounds automata k l_0 s_0 formula m
  num_states num_actions renum_acts renum_vars renum_clocks renum_states
  state_space =
  (case do_rename_mc show_int (show_list show_char) (show_list show_char)
          (show_list show_char)
          (fn _ => fn _ => certificate_checker2 num_split dc state_space) dc
          broadcast bounds automata k l_0 s_0 formula m num_states num_actions
          renum_acts renum_vars renum_clocks renum_states
          (fn _ => fn _ =>
            [Chara (false, false, false, false, false, true, false, false)])
          (fn _ =>
            [Chara (false, false, false, false, false, true, false, false)])
          (fn _ =>
            [Chara (false, false, false, false, false, true, false, false)])
    of NONE => Renaming_Failed | SOME true => Sat | SOME false => Unsat);

fun hashmap_of_list (A1_, A2_) m =
  fold (fn (a, b) => ahm_update (eq A1_) (bounded_hashcode_nat A2_) a b) m
    (ahm_empty (def_hashmap_size A2_ Type));

fun certify_unreachable_impl_pure get_succs mi li lei pi l_0i s_0i fi li_split =
  let
    val check_all_pre_impl =
      time_it "Time for state set preconditions check"
        (fn _ =>
          (case mi l_0i of NONE => false
            | SOME xs =>
              not (is_none (mi l_0i)) andalso
                (pi (l_0i, s_0i) andalso
                  (list_ex (lei s_0i) xs andalso
                    list_all
                      (fn l =>
                        (case op_map_lookup l mi of NONE => true
                          | SOME a => list_all (fn s => pi (l, s)) a))
                      li))));
    val check_final =
      time_it "Time to check final state predicate"
        (fn _ =>
          list_all id
            (Par_List.map
              (list_all
                (fn l =>
                  (case op_map_lookup l mi of NONE => true
                    | SOME a => list_all (fn s => not (fi (l, s))) a)))
              li_split));
    val check_invariant =
      time_it "Time for state space invariant check"
        (fn _ =>
          list_all id
            (Par_List.map
              (list_all
                (fn l =>
                  (case mi l of NONE => true
                    | SOME asa =>
                      list_all
                        (fn (la, xs) =>
                          (if null xs then true
                            else (case mi la of NONE => false
                                   | SOME ys =>
                                     list_all (fn x => list_ex (lei x) ys) xs)))
                        (get_succs l asa))))
              li_split));
  in
    (if (if check_all_pre_impl then check_invariant else false) then check_final
      else false)
  end;

fun array_unfreeze A_ a =
  (fn a => fn () =>
  if Vector.length a = 0
  then Array.fromList []
  else
    let
      val x = Vector.sub(a, 0)
      val n = Array.array (Vector.length a, x)
      val _ = Array.copyVec {src=a,dst=n,di=0}
    in n end
) a;

fun unreachability_checker3 broadcast bounds automata m num_states num_actions
  l_0 s_0 formula l_list m_list num_split =
  let
    val n_vsa = n_vs bounds;
    val n_ps = size_list automata;
    val invs =
      Vector.fromList
        (map (fn i =>
               let
                 val ma =
                   default_map_of equal_nat [] (snd (snd (nth automata i)));
                 val mb =
                   Vector.fromList (map ma (upt zero_nata (num_states i)));
               in
                 mb
               end)
          (upt zero_nata n_ps));
    val succsi = succs_impl broadcast bounds automata m num_actions n_ps invs;
    val states_ia = map (states_i automata) (upt zero_nata n_ps);
    val check_state =
      (fn (l, s) =>
        equal_nata (size_list l) n_ps andalso
          all_interval_nat
            (fn i => member equal_nat (nth l i) (nth states_ia i)) zero_nata
            n_ps andalso
          (equal_nata (size_list s) n_vsa andalso check_boundedi bounds s));
    val mi =
      hashmap_of_list
        (equal_prod (equal_list equal_nat) (equal_list equal_int),
          hashable_prod (hashable_list hashable_nat)
            (hashable_list hashable_int))
        (map (fn (k, dbms) => (k, map Vector.fromList dbms)) m_list);
    val init_dbm =
      amtx_dflt (heap_DBMEntry heap_int) (suc m) (suc m) (Le zero_inta);
  in
    certify_unreachable_impl_pure
      (fn x =>
        (fn a => (fn f => f ()) a) o
          (fn xs =>
            let
              val li = id x;
            in
              (fn f_ => fn () => f_
                ((fold_map (array_unfreeze (heap_DBMEntry heap_int)) xs) ()) ())
                (fn xsi =>
                  (fn f_ => fn () => f_ ((succsi li xsi) ()) ())
                    (fold_map
                      (fn (lia, xsia) =>
                        (fn f_ => fn () => f_
                          ((fold_map (array_freeze (heap_DBMEntry heap_int))
                             xsia)
                          ()) ())
                          (fn xsa => (fn () => (id lia, xsa))))))
            end))
      (fn k =>
        ahm_lookup (equal_proda (equal_list equal_nat) (equal_list equal_int))
          (bounded_hashcode_nat
            (hashable_prod (hashable_list hashable_nat)
              (hashable_list hashable_int)))
          k mi)
      l_list
      (fn asa => fn bs =>
        not (all_interval_nat
              (not o
                (fn i =>
                  dbm_lt_0
                    (sub asa (plus_nata (plus_nata i (times_nata i m)) i))))
              zero_nata (suc m)) orelse
          array_all2 (times_nata (suc m) (suc m))
            (less_eq_DBMEntry (equal_int, linorder_int)) asa bs)
      (fn a =>
        (fn f => f ()) ((fn f_ => fn () => f_
                          (let
                             val (l, s) = a;
                           in
                             (fn f_ => fn () => f_
                               ((array_unfreeze (heap_DBMEntry heap_int) s) ())
                               ())
                               (fn sa => (fn () => (id l, sa)))
                           end
                          ()) ())
                         (fn (a1, a2) =>
                           (fn f_ => fn () => f_
                             ((imp_for_int zero_nata (plus_nata m one_nata)
                                (fn aa => (fn () => aa))
                                (fn xc => fn _ =>
                                  imp_for_int zero_nata (plus_nata m one_nata)
                                    (fn aa => (fn () => aa))
                                    (fn xf => fn _ =>
                                      imp_for_int zero_nata
(plus_nata m one_nata) (fn aa => (fn () => aa))
(fn xj => fn _ =>
  (fn f_ => fn () => f_ ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (xc, xj))
    ()) ())
    (fn x_i =>
      (fn f_ => fn () => f_
        ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (xc, xf)) ()) ())
        (fn x =>
          (fn f_ => fn () => f_
            ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (xf, xj)) ()) ())
            (fn xa => (fn () => (dbm_le_int x_i (dbm_add_int x xa)))))))
true)
                                    true)
                                true)
                             ()) ())
                             (fn x =>
                               (fn f_ => fn () => f_ ((check_diag_impl_int m a2)
                                 ()) ())
                                 (fn xa =>
                                   (fn f_ => fn () => f_
                                     ((imp_for_int zero_nata
(plus_nata m one_nata) (fn aa => (fn () => aa))
(fn xc => fn _ =>
  (fn f_ => fn () => f_ ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (xc, xc))
    ()) ())
    (fn x_d => (fn () => (dbm_le_int x_d (Le zero_inta)))))
true)
                                     ()) ())
                                     (fn xb =>
                                       (fn f_ => fn () => f_
 ((imp_for_int zero_nata (plus_nata m one_nata) (fn aa => (fn () => aa))
    (fn xc => fn _ =>
      (fn f_ => fn () => f_
        ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (zero_nata, xc)) ()) ())
        (fn x_e => (fn () => (dbm_le_int x_e (Le zero_inta)))))
    true)
 ()) ())
 (fn xc =>
   (fn () =>
     (check_state a1 andalso ((x orelse xa) andalso (xb andalso xc)))))))))))
      (id ((fn f => f ()) (fn () =>
                            (l_0, map (the o map_of equal_nat s_0)
                                    (upt zero_nata n_vsa)))))
      ((fn f => f ()) ((fn f_ => fn () => f_ (init_dbm ()) ())
                        (array_freeze (heap_DBMEntry heap_int))))
      (fn a =>
        (fn f => f ()) ((fn f_ => fn () => f_
                          (let
                             val (l, s) = a;
                           in
                             (fn f_ => fn () => f_
                               ((array_unfreeze (heap_DBMEntry heap_int) s) ())
                               ())
                               (fn sa => (fn () => (id l, sa)))
                           end
                          ()) ())
                         (fn xi =>
                           (fn () => let
                                       val ((aa, b), _) = xi;
                                     in
                                       hd_of_formulai equal_nat formula aa b
                                     end))))
      (split_kb num_split m_list)
  end;

fun no_deadlock_certifier3 broadcast bounds automata m num_states num_actions
  l_0 s_0 l_list m_list num_split =
  let
    val n_vsa = n_vs bounds;
    val n_ps = size_list automata;
    val invs =
      Vector.fromList
        (map (fn i =>
               let
                 val ma =
                   default_map_of equal_nat [] (snd (snd (nth automata i)));
                 val mb =
                   Vector.fromList (map ma (upt zero_nata (num_states i)));
               in
                 mb
               end)
          (upt zero_nata n_ps));
    val succsi = succs_impl broadcast bounds automata m num_actions n_ps invs;
    val states_ia = map (states_i automata) (upt zero_nata n_ps);
    val check_states =
      (fn (l, s) =>
        equal_nata (size_list l) n_ps andalso
          all_interval_nat
            (fn i => member equal_nat (nth l i) (nth states_ia i)) zero_nata
            n_ps andalso
          (equal_nata (size_list s) n_vsa andalso check_boundedi bounds s));
    val subsumption =
      (fn asa => fn bs =>
        not (all_interval_nat
              (not o
                (fn i =>
                  dbm_lt_0
                    (sub asa (plus_nata (plus_nata i (times_nata i m)) i))))
              zero_nata (suc m)) orelse
          array_all2 (times_nata (suc m) (suc m))
            (less_eq_DBMEntry (equal_int, linorder_int)) asa bs);
    val p_impl =
      (fn (a1, a2) =>
        (fn f_ => fn () => f_
          ((imp_for_int zero_nata (plus_nata m one_nata) (fn a => (fn () => a))
             (fn xc => fn _ =>
               imp_for_int zero_nata (plus_nata m one_nata)
                 (fn a => (fn () => a))
                 (fn xf => fn _ =>
                   imp_for_int zero_nata (plus_nata m one_nata)
                     (fn a => (fn () => a))
                     (fn xj => fn _ =>
                       (fn f_ => fn () => f_
                         ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (xc, xj))
                         ()) ())
                         (fn x_i =>
                           (fn f_ => fn () => f_
                             ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                (xc, xf))
                             ()) ())
                             (fn x =>
                               (fn f_ => fn () => f_
                                 ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                    (xf, xj))
                                 ()) ())
                                 (fn xa =>
                                   (fn () =>
                                     (dbm_le_int x_i (dbm_add_int x xa)))))))
                     true)
                 true)
             true)
          ()) ())
          (fn x =>
            (fn f_ => fn () => f_ ((check_diag_impl_int m a2) ()) ())
              (fn xa =>
                (fn f_ => fn () => f_
                  ((imp_for_int zero_nata (plus_nata m one_nata)
                     (fn a => (fn () => a))
                     (fn xc => fn _ =>
                       (fn f_ => fn () => f_
                         ((mtx_get (heap_DBMEntry heap_int) (suc m) a2 (xc, xc))
                         ()) ())
                         (fn x_d => (fn () => (dbm_le_int x_d (Le zero_inta)))))
                     true)
                  ()) ())
                  (fn xb =>
                    (fn f_ => fn () => f_
                      ((imp_for_int zero_nata (plus_nata m one_nata)
                         (fn a => (fn () => a))
                         (fn xc => fn _ =>
                           (fn f_ => fn () => f_
                             ((mtx_get (heap_DBMEntry heap_int) (suc m) a2
                                (zero_nata, xc))
                             ()) ())
                             (fn x_e =>
                               (fn () => (dbm_le_int x_e (Le zero_inta)))))
                         true)
                      ()) ())
                      (fn xc =>
                        (fn () =>
                          (check_states a1 andalso
                            ((x orelse xa) andalso (xb andalso xc)))))))));
    val p =
      (fn a =>
        (fn f => f ()) ((fn f_ => fn () => f_
                          (let
                             val (l, s) = a;
                           in
                             (fn f_ => fn () => f_
                               ((array_unfreeze (heap_DBMEntry heap_int) s) ())
                               ())
                               (fn sa => (fn () => (id l, sa)))
                           end
                          ()) ())
                         p_impl));
    val mi =
      hashmap_of_list
        (equal_prod (equal_list equal_nat) (equal_list equal_int),
          hashable_prod (hashable_list hashable_nat)
            (hashable_list hashable_int))
        (map (fn (k, dbms) => (k, map Vector.fromList dbms)) m_list);
    val init_dbm =
      amtx_dflt (heap_DBMEntry heap_int) (suc m) (suc m) (Le zero_inta);
    val check_deadlock =
      let
        val n_psa = n_ps;
        val invsa =
          Vector.fromList
            (map (fn i =>
                   let
                     val ma =
                       default_map_of equal_nat [] (snd (snd (nth automata i)));
                     val mb =
                       Vector.fromList (map ma (upt zero_nata (num_states i)));
                   in
                     mb
                   end)
              (upt zero_nata n_psa));
        val inv_fun =
          (fn (l, _) =>
            maps (fn i => sub (sub invsa i) (nth l i)) (upt zero_nata n_psa));
        val trans_impl =
          let
            val trans_mapa = trans_map automata;
            val trans_i_map =
              (fn i => fn j =>
                map_filter
                  (fn (b, a) =>
                    let
                      val (g, aa) = a;
                      val (ab, (ma, l)) = aa;
                    in
                      (case ab of In _ => NONE | Out _ => NONE
                        | Sil ac => SOME (b, (g, (ac, (ma, l)))))
                    end)
                  (trans_mapa i j));
            val int_trans_from_loc_impl =
              (fn pa => fn l => fn la => fn s =>
                let
                  val a = trans_i_map pa l;
                in
                  map_filter
                    (fn (b, aa) =>
                      let
                        val (g, ab) = aa;
                        val (ac, (f, (r, lb))) = ab;
                        val sa = mk_updsi s f;
                      in
                        (if bvali (equal_int, linorder_int) s b andalso
                              check_boundedi bounds sa
                          then SOME (g, (Internal ac,
  (r, (list_update la pa lb, sa))))
                          else NONE)
                      end)
                    a
                end);
            val int_trans_from_vec_impl =
              (fn pairs => fn l => fn s =>
                maps (fn (pa, la) => int_trans_from_loc_impl pa la l s) pairs);
            val int_trans_from_all_impl =
              (fn l => fn s =>
                maps (fn pa => int_trans_from_loc_impl pa (nth l pa) l s)
                  (upt zero_nata n_psa));
            val trans_out_map =
              (fn i => fn j =>
                map_filter
                  (fn (b, a) =>
                    let
                      val (g, aa) = a;
                      val (ab, (ma, l)) = aa;
                    in
                      (case ab of In _ => NONE
                        | Out ac => SOME (b, (g, (ac, (ma, l))))
                        | Sil _ => NONE)
                    end)
                  (trans_mapa i j));
            val trans_in_map =
              (fn i => fn j =>
                map_filter
                  (fn (b, a) =>
                    let
                      val (g, aa) = a;
                      val (ab, (ma, l)) = aa;
                    in
                      (case ab of In ac => SOME (b, (g, (ac, (ma, l))))
                        | Out _ => NONE | Sil _ => NONE)
                    end)
                  (trans_mapa i j));
            val trans_out_broad_grouped =
              (fn i => fn j =>
                actions_by_statea num_actions
                  (map_filter
                    (fn (b, a) =>
                      let
                        val (g, aa) = a;
                        val (ab, (ma, l)) = aa;
                      in
                        (case ab of In _ => NONE
                          | Out ac =>
                            (if membera equal_nat broadcast ac
                              then SOME (b, (g, (ac, (ma, l)))) else NONE)
                          | Sil _ => NONE)
                      end)
                    (trans_mapa i j)));
            val trans_in_broad_grouped =
              (fn i => fn j =>
                actions_by_statea num_actions
                  (map_filter
                    (fn (b, a) =>
                      let
                        val (g, aa) = a;
                        val (ab, (ma, l)) = aa;
                      in
                        (case ab
                          of In ac =>
                            (if membera equal_nat broadcast ac
                              then SOME (b, (g, (ac, (ma, l)))) else NONE)
                          | Out _ => NONE | Sil _ => NONE)
                      end)
                    (trans_mapa i j)));
            val broad_trans_impl =
              (fn (l, s) =>
                let
                  val pairs = get_commited broadcast bounds automata l;
                  val ina =
                    map (fn pa => trans_in_broad_grouped pa (nth l pa))
                      (upt zero_nata n_psa);
                  val out =
                    map (fn pa => trans_out_broad_grouped pa (nth l pa))
                      (upt zero_nata n_psa);
                  val inb =
                    map (map (filter
                               (fn (b, _) =>
                                 bvali (equal_int, linorder_int) s b)))
                      ina;
                  val outa =
                    map (map (filter
                               (fn (b, _) =>
                                 bvali (equal_int, linorder_int) s b)))
                      out;
                in
                  (if null pairs
                    then maps (fn a =>
                                maps (fn pa =>
                                       let
 val outs = nth (nth outa pa) a;
                                       in
 (if null outs then []
   else let
          val combs = make_combs broadcast bounds automata pa a inb;
          val outsa = map (fn aa => (pa, aa)) outs;
          val combsa =
            (if null combs then map (fn x => [x]) outsa
              else maps (fn x => map (fn aa => x :: aa) combs) outsa);
          val init = ([], (Broad a, ([], (l, s))));
        in
          compute_upds_impl bounds init combsa
        end)
                                       end)
                                  (upt zero_nata n_psa))
                           (upt zero_nata num_actions)
                    else maps (fn a =>
                                let
                                  val ins_commited =
                                    map_filter
                                      (fn (pa, _) =>
(if not (null (nth (nth inb pa) a)) then SOME pa else NONE))
                                      pairs;
                                  val always_commited =
                                    less_nat one_nata (size_list ins_commited);
                                in
                                  maps (fn pa =>
 let
   val outs = nth (nth outa pa) a;
 in
   (if null outs then []
     else (if not always_commited andalso
                ((equal_lista equal_nat ins_commited [pa] orelse
                   null ins_commited) andalso
                  not (list_ex (fn (q, _) => equal_nata q pa) pairs))
            then []
            else let
                   val combs = make_combs broadcast bounds automata pa a inb;
                   val outsa = map (fn aa => (pa, aa)) outs;
                   val combsa =
                     (if null combs then map (fn x => [x]) outsa
                       else maps (fn x => map (fn aa => x :: aa) combs) outsa);
                   val init = ([], (Broad a, ([], (l, s))));
                 in
                   compute_upds_impl bounds init combsa
                 end))
 end)
                                    (upt zero_nata n_psa)
                                end)
                           (upt zero_nata num_actions))
                end);
            val bin_trans_impl =
              (fn (l, s) =>
                let
                  val pairs = get_commited broadcast bounds automata l;
                  val ina =
                    all_actions_by_state broadcast bounds automata num_actions
                      trans_in_map l;
                  val out =
                    all_actions_by_state broadcast bounds automata num_actions
                      trans_out_map l;
                in
                  (if null pairs
                    then maps (fn a =>
                                pairs_by_action_impl bounds l s (nth out a)
                                  (nth ina a))
                           (bin_actions broadcast num_actions)
                    else let
                           val in2 =
                             all_actions_from_vec num_actions trans_in_map
                               pairs;
                           val out2 =
                             all_actions_from_vec num_actions trans_out_map
                               pairs;
                         in
                           maps (fn a =>
                                  pairs_by_action_impl bounds l s (nth out a)
                                    (nth in2 a))
                             (bin_actions broadcast num_actions) @
                             maps (fn a =>
                                    pairs_by_action_impl bounds l s (nth out2 a)
                                      (nth ina a))
                               (bin_actions broadcast num_actions)
                         end)
                end);
            val int_trans_impl =
              (fn (l, s) =>
                let
                  val pairs = get_commited broadcast bounds automata l;
                in
                  (if null pairs then int_trans_from_all_impl l s
                    else int_trans_from_vec_impl pairs l s)
                end);
          in
            (fn st =>
              int_trans_impl st @ bin_trans_impl st @ broad_trans_impl st)
          end;
      in
        (fn ai => fn bi =>
          (fn f_ => fn () => f_
            ((imp_nfoldli (trans_impl ai) (fn _ => (fn () => true))
               (fn xb => fn sigma =>
                 (fn f_ => fn () => f_
                   ((v_dbm_impl (linordered_cancel_ab_monoid_add_int, heap_int)
                      m)
                   ()) ())
                   (fn x =>
                     (fn f_ => fn () => f_
                       ((abstr_FW_impl_int m (inv_fun (snd (snd (snd xb)))) x)
                       ()) ())
                       (fn xa =>
                         (fn f_ => fn () => f_
                           ((pre_reset_list_impl m xa (fst (snd (snd xb)))) ())
                           ())
                           (fn xc =>
                             (fn f_ => fn () => f_
                               ((abstr_FW_impl_int m (fst xb) xc) ()) ())
                               (fn xd =>
                                 (fn f_ => fn () => f_
                                   ((abstr_FW_impl_int m (inv_fun ai) xd) ())
                                   ())
                                   (fn xe =>
                                     (fn f_ => fn () => f_ ((down_impl_int m xe)
                                       ()) ())
                                       (fn x_c =>
 (fn () => (x_c :: sigma)))))))))
               [])
            ()) ())
            (fn x => dbm_subset_fed_impl m bi (op_list_rev x)))
      end;
    val check_deadlock1 =
      (fn a =>
        (fn f => f ()) ((fn f_ => fn () => f_
                          (let
                             val (l, s) = a;
                           in
                             (fn f_ => fn () => f_
                               ((array_unfreeze (heap_DBMEntry heap_int) s) ())
                               ())
                               (fn sa => (fn () => (id l, sa)))
                           end
                          ()) ())
                         (fn (l, ma) =>
                           (fn f_ => fn () => f_ ((check_deadlock l ma) ()) ())
                             (fn r => (fn () => (not r))))));
  in
    certify_unreachable_impl_pure
      (fn x =>
        (fn a => (fn f => f ()) a) o
          (fn xs =>
            let
              val li = id x;
            in
              (fn f_ => fn () => f_
                ((fold_map (array_unfreeze (heap_DBMEntry heap_int)) xs) ()) ())
                (fn xsi =>
                  (fn f_ => fn () => f_ ((succsi li xsi) ()) ())
                    (fold_map
                      (fn (lia, xsia) =>
                        (fn f_ => fn () => f_
                          ((fold_map (array_freeze (heap_DBMEntry heap_int))
                             xsia)
                          ()) ())
                          (fn xsa => (fn () => (id lia, xsa))))))
            end))
      (fn k =>
        ahm_lookup (equal_proda (equal_list equal_nat) (equal_list equal_int))
          (bounded_hashcode_nat
            (hashable_prod (hashable_list hashable_nat)
              (hashable_list hashable_int)))
          k mi)
      l_list subsumption p
      (id ((fn f => f ()) (fn () =>
                            (l_0, map (the o map_of equal_nat s_0)
                                    (upt zero_nata n_vsa)))))
      ((fn f => f ()) ((fn f_ => fn () => f_ (init_dbm ()) ())
                        (array_freeze (heap_DBMEntry heap_int))))
      check_deadlock1 (split_kb num_split m_list)
  end;

fun certificate_checker3 num_split dc m_list broadcast bounds automata m
  num_states num_actions k l_0 s_0 formula =
  let
    val l_list = map fst m_list;
  in
    (case certificate_checker_pre l_list m_list broadcast bounds automata m
            num_states num_actions k l_0 s_0 formula
      of true =>
        (if dc
          then no_deadlock_certifier3 broadcast bounds automata m num_states
                 num_actions l_0 s_0 l_list m_list num_split
          else unreachability_checker3 broadcast bounds automata m num_states
                 num_actions l_0 s_0 formula l_list m_list num_split)
      | false => false)
  end;

fun rename_check3 num_split dc broadcast bounds automata k l_0 s_0 formula m
  num_states num_actions renum_acts renum_vars renum_clocks renum_states
  state_space =
  (case do_rename_mc show_int (show_list show_char) (show_list show_char)
          (show_list show_char)
          (fn _ => fn _ => certificate_checker3 num_split dc state_space) dc
          broadcast bounds automata k l_0 s_0 formula m num_states num_actions
          renum_acts renum_vars renum_clocks renum_states
          (fn _ => fn _ =>
            [Chara (false, false, false, false, false, true, false, false)])
          (fn _ =>
            [Chara (false, false, false, false, false, true, false, false)])
          (fn _ =>
            [Chara (false, false, false, false, false, true, false, false)])
    of NONE => Renaming_Failed | SOME true => Sat | SOME false => Unsat);

fun n num_states q = num_states q;

fun clkp_inv automata i l =
  sup_seta (equal_prod equal_nat equal_int)
    (image (collect_clock_pairs o snd)
      (Set (filter (fn (a, _) => equal_nata a l)
             (snd (snd (nth automata i))))));

fun bound_inv automata q c l =
  maxa linorder_int
    (sup_set equal_int (insert equal_int zero_inta bot_set)
      (sup_seta equal_int
        (image
          (fn (x, d) =>
            (if equal_nata x c then insert equal_int d bot_set else bot_set))
          (clkp_inv automata q l))));

fun clkp_seta automata i l =
  sup_set (equal_prod equal_nat equal_int) (clkp_inv automata i l)
    (sup_seta (equal_prod equal_nat equal_int)
      (image
        (fn (la, (_, (g, _))) =>
          (if equal_nata la l then collect_clock_pairs g else bot_set))
        (Set (fst (snd (nth automata i))))));

fun bound_g automata q c l =
  maxa linorder_int
    (sup_set equal_int (insert equal_int zero_inta bot_set)
      (sup_seta equal_int
        (image
          (fn (x, d) =>
            (if equal_nata x c then insert equal_int d bot_set else bot_set))
          (clkp_seta automata q l))));

fun bound automata q c l =
  max ord_int (bound_g automata q c l) (bound_inv automata q c l);

fun w automata num_states q c la l =
  (if equal_nata la (n num_states q) then uminus_inta (bound automata q c l)
    else zero_inta);

fun v num_states q = (fn v => less_eq_nat v (n num_states q));

fun resets automata q c l =
  fold (fn (l1, (_, (_, (_, (_, (r, la)))))) => fn xs =>
         (if not (equal_nata l1 l) orelse
               (membera equal_nat xs la orelse membera equal_nat r c)
           then xs else la :: xs))
    (fst (snd (nth automata q))) [];

fun ea automata q c l = resets automata q c l;

fun e automata num_states q c l =
  (if equal_nata l (n num_states q) then upt zero_nata (n num_states q)
    else filter (fn la => membera equal_nat (ea automata q c la) l)
           (upt zero_nata (n num_states q)));

fun g automata num_states q c =
  Gen_g_impl_ext
    (v num_states q, e automata num_states q c, [n num_states q],
      w automata num_states q c);

fun calc_shortest_scc_paths (A1_, A2_, A3_) g n =
  let
    val sccs = compute_SCC_tr (equal_nat, hashable_nat) g;
    val d = map (fn _ => NONE) (upt zero_nata n) @ [SOME (zero A2_)];
    val da =
      fold (fold (fn u =>
                   fold (fn v => fn da =>
                          (case nth da u of NONE => da
                            | SOME du =>
                              (case nth da v
                                of NONE =>
                                  list_update da v
                                    (SOME (plus A1_ du (more g u v)))
                                | SOME dv =>
                                  (if less A3_ (plus A1_ du (more g u v)) dv
                                    then list_update da v
   (SOME (plus A1_ du (more g u v)))
                                    else da))))
                     (gi_E g u)))
        sccs d;
    val db =
      fold (fn vs => fn db =>
             let
               val dscc =
                 fold (fn v => fn dscc =>
                        (case dscc of NONE => nth db v
                          | SOME daa =>
                            (case nth db v of NONE => dscc
                              | SOME dv => SOME (min A3_ dv daa))))
                   vs NONE;
             in
               fold (fn v => fn dc => list_update dc v dscc) vs db
             end)
        sccs da;
  in
    db
  end;

fun local_ceiling_single automata num_states q c =
  let
    val a =
      calc_shortest_scc_paths (plus_int, zero_int, ord_int)
        (g automata num_states q c) (n num_states q);
  in
    map (fn aa =>
          (case aa of NONE => zero_nata | SOME x => nat (uminus_inta x)))
      a
  end;

fun local_ceiling broadcast bounds automata m num_states =
  app rev
    (fold (fn q => fn xs =>
            app (fn x => rev x :: xs)
              (fold (fn l => fn xsa =>
                      app (fn x => (zero_nata :: rev x) :: xsa)
                        (fold (fn c =>
                                (fn a =>
                                  nth (local_ceiling_single automata num_states
q c)
                                    l ::
                                    a))
                          (upt one_nata (suc m)) []))
                (upt zero_nata (n num_states q)) []))
      (upt zero_nata (size_list automata)) []);

fun rename_state_space A_ =
  (fn dc => fn ids_to_names => fn (broadcast, (automata, bounds)) => fn l_0 =>
    fn s_0 => fn formula =>
    let
      val _ = writeln "Make renaming";
    in
      binda (make_renaming (equal_nat, show_nat) broadcast automata bounds)
        (fn (m, (num_states,
                  (num_actions,
                    (renum_acts,
                      (renum_vars,
                        (renum_clocks,
                          (renum_states,
                            (inv_renum_states,
                              (inv_renum_vars, inv_renum_clocks)))))))))
           =>
          let
            val _ = writeln "Renaming";
            val (broadcasta, (automataa, boundsa)) =
              rename_network countable_literal countable_literal countable_nat
                countable_literal broadcast bounds automata renum_acts
                renum_vars renum_clocks renum_states;
            val _ = writeln "Calculating ceiling";
            val k = local_ceiling broadcasta boundsa automataa m num_states;
            val _ = writeln "Running model checker";
            val inv_renum_statesa =
              (fn i => ids_to_names i o inv_renum_states i);
            val f =
              (fn show_clock => fn show_statea => fn broadcastb => fn boundsb =>
                fn automatab => fn ma => fn num_statesa => fn num_actionsa =>
                fn ka => fn l_0a => fn s_0a => fn formulaa =>
                state_space broadcastb boundsb automatab ma num_statesa
                  num_actionsa ka l_0a s_0a formulaa show_clock show_statea ());
            val r =
              do_rename_mc show_int A_ show_literal show_literal f dc broadcast
                bounds automata k l_0 s_0 formula m num_states num_actions
                renum_acts renum_vars renum_clocks renum_states
                inv_renum_statesa inv_renum_vars inv_renum_clocks;
            val show_clock =
              (fn x => shows_prec_literal zero_nata x []) o inv_renum_clocks;
            val show_statea =
              show_state show_nat show_literal show_int inv_renum_states
                inv_renum_vars;
            val renamings =
              (m, (num_states,
                    (num_actions,
                      (renum_acts,
                        (renum_vars,
                          (renum_clocks,
                            (renum_states,
                              (inv_renum_states,
                                (inv_renum_vars, inv_renum_clocks)))))))));
          in
            Result (r, (show_clock, (show_statea, (renamings, k))))
          end)
    end);

fun convert_state_space state_space =
  map (fn (a, b) => let
                      val (locs, vars) = a;
                    in
                      (fn aa => ((map nat locs, vars), aa))
                    end
                      b)
    state_space;

fun parse_convert_check1 model renaming state_space =
  binda (parse json model)
    (fn modela =>
      binda (convert modela)
        (fn (ids_to_names,
              (process_names_to_index,
                (broadcast, (automata, (bounds, (formula, (l_0, s_0)))))))
           =>
          binda (parse json renaming)
            (fn renaminga =>
              binda (convert_renaming ids_to_names process_names_to_index
                      renaminga)
                (fn (var_renaming, (clock_renaming, location_renaming)) =>
                  let
                    val t = Time.now ();
                    val state_spacea = convert_state_space state_space;
                    val ta = (fn x => fn y => Time.- (x, y)) (Time.now ()) t;
                    val _ =
                      writeln ("Time for converting state space: " ^
                                (fn x => Time.toString x) ta);
                  in
                    binda (make_renaming (equal_nat, show_nat) broadcast
                            automata bounds)
                      (fn (m, (num_states,
                                (num_actions,
                                  (renum_acts, (_, (_, (_, (_, (_, _)))))))))
                         =>
                        let
                          val renum_vars = var_renaming;
                          val renum_clocks = clock_renaming;
                          val renum_states = location_renaming;
                          val _ = writeln "Renaming";
                          val (broadcasta, (automataa, boundsa)) =
                            rename_network countable_literal countable_literal
                              countable_nat countable_literal broadcast bounds
                              automata renum_acts renum_vars renum_clocks
                              renum_states;
                          val _ = writeln "Calculating ceiling";
                          val k =
                            local_ceiling broadcasta boundsa automataa m
                              num_states;
                        in
                          Result
                            (broadcast,
                              (bounds,
                                (automata,
                                  (k, (l_0,
(s_0, (formula,
        (m, (num_states,
              (num_actions,
                (renum_acts,
                  (renum_vars,
                    (renum_clocks, (renum_states, state_spacea))))))))))))))
                        end)
                  end))));

fun parse_convert_check mode num_split dc model renaming state_space =
  (case parse_convert_check1 model renaming state_space
    of Result
         (broadcast,
           (bounds,
             (automata,
               (k, (l_0, (s_0, (formula,
                                 (m, (num_states,
                                       (num_actions,
 (renum_acts,
   (renum_vars, (renum_clocks, (renum_states, state_spacea))))))))))))))
      => let
           val _ = Timing.start_timer ();
           val _ = Timing.save_time "Time for converting DBMs in certificate";
           val _ =
             writeln ("Number of discrete states: " ^
                       show_lit show_nat (size_list state_spacea));
           val t = Time.now ();
         in
           (fn f_ => fn () => f_
             ((case mode
                of Impl1 =>
                  rename_check num_split dc broadcast bounds automata k l_0 s_0
                    formula m num_states num_actions renum_acts renum_vars
                    renum_clocks renum_states state_spacea
                | Impl2 =>
                  (fn () =>
                    (rename_check2 num_split dc broadcast bounds automata k l_0
                      s_0 formula m num_states num_actions renum_acts renum_vars
                      renum_clocks renum_states state_spacea))
                | Impl3 =>
                  (fn () =>
                    (rename_check3 num_split dc broadcast bounds automata k l_0
                      s_0 formula m num_states num_actions renum_acts renum_vars
                      renum_clocks renum_states state_spacea)))
             ()) ())
             (fn check =>
               let
                 val ta = (fn x => fn y => Time.- (x, y)) (Time.now ()) t;
                 val _ =
                   writeln ("Time for certificate checking: " ^
                             (fn x => Time.toString x) ta);
               in
                 (case check
                   of Renaming_Failed => let
   val _ = writeln "Renaming failed";
 in
   (fn () => ())
 end
                   | Preconds_Unsat =>
                     let
                       val _ = writeln "Preconditions were not met";
                     in
                       (fn () => ())
                     end
                   | Sat => let
                              val _ = writeln "Certificate was accepted";
                            in
                              (fn () => ())
                            end
                   | Unsat => let
                                val _ = writeln "Certificate was rejected";
                              in
                                (fn () => ())
                              end)
               end)
         end
    | Error es => let
                    val _ = map (fn a => writeln a) es;
                  in
                    (fn () => ())
                  end);

fun dbm_list_to_string (A1_, A2_) n show_clock show_num xs =
  app (concat o
         intersperse
           [Chara (false, false, true, true, false, true, false, false),
             Chara (false, false, false, false, false, true, false, false)] o
         rev o
         snd o
        snd)
    (fold (fn e => fn (i, (j, acc)) =>
            let
              val s = make_string (A1_, A2_) show_clock show_num e i j;
              val ja = modulo_nat (plus_nata j one_nata) (plus_nata n one_nata);
              val ia =
                (if equal_nata ja zero_nata then plus_nata i one_nata else i);
            in
              (ia, (ja, s :: acc))
            end)
      xs (zero_nata, (zero_nata, [])));

fun show_dbm_impl_all (A1_, A2_, A3_) n show_clock show_num =
  (fn xi =>
    (fn f_ => fn () => f_
      ((dbm_to_list_impl
         (linordered_ab_monoid_add_DBMEntry
            (linordered_cancel_ab_monoid_add_linordered_ab_group_add A1_, A2_),
           heap_DBMEntry A3_)
         n xi)
      ()) ())
      (fn x =>
        (fn () => (dbm_list_to_string (A1_, A3_) n show_clock show_num x))));

fun equal_mode Impl2 Impl3 = false
  | equal_mode Impl3 Impl2 = false
  | equal_mode Impl1 Impl3 = false
  | equal_mode Impl3 Impl1 = false
  | equal_mode Impl1 Impl2 = false
  | equal_mode Impl2 Impl1 = false
  | equal_mode Impl3 Impl3 = true
  | equal_mode Impl2 Impl2 = true
  | equal_mode Impl1 Impl1 = true;

fun parse_convert_run_check mode num_split dc s =
  (case binda (parse json s) convert
    of Result
         (ids_to_names,
           (_, (broadcast, (automata, (bounds, (formula, (l_0, s_0)))))))
      => let
           val a =
             rename_state_space show_literal dc ids_to_names
               (broadcast, (automata, bounds)) l_0 s_0 formula;
         in
           (case a
             of Result (r, (_, (_, (renamings, k)))) =>
               (case r of NONE => (fn () => ())
                 | SOME ra =>
                   let
                     val t = Time.now ();
                   in
                     (fn f_ => fn () => f_ (ra ()) ())
                       (fn rb =>
                         let
                           val ta =
                             (fn x => fn y => Time.- (x, y)) (Time.now ()) t;
                         in
                           (fn f_ => fn () => f_
                             ((print_line_impl
                                ("Time for model checking + certificate extraction: " ^
                                  (fn x => Time.toString x) ta))
                             ()) ())
                             (fn _ =>
                               let
                                 val (m, (num_states,
   (num_actions,
     (renum_acts, (renum_vars, (renum_clocks, (renum_states, (_, (_, _)))))))))
                                   = renamings;
                                 val _ = Timing.start_timer ();
                               in
                                 (fn f_ => fn () => f_
                                   ((fold_map
                                      (fn (sa, xs) =>
let
  val xsa = map snd xs;
in
  (fn f_ => fn () => f_
    ((fold_map
       (dbm_to_list_impl
         (linordered_ab_monoid_add_DBMEntry
            (linordered_cancel_ab_monoid_add_int, equal_int),
           heap_DBMEntry heap_int)
         m)
       xsa)
    ()) ())
    (fn xsb => (fn () => (sa, xsb)))
end)
                                      rb)
                                   ()) ())
                                   (fn state_space =>
                                     let
                                       val _ =
 Timing.save_time "Time for converting DBMs in certificate";
                                     in
                                       (fn f_ => fn () => f_
 ((print_line_impl
    ("Number of discrete states of state space: " ^
      show_lit show_nat (size_list state_space)))
 ()) ())
 (fn _ =>
   let
     val _ =
       writeln ("Size of passed list: " ^
                 show_str show_nat
                   (sum_list monoid_add_nat (map (size_list o snd) rb)));
   in
     (fn f_ => fn () => f_
       ((print_line_impl
          ("DBM list length distribution: " ^
            show_str (show_list (show_prod show_nat show_nat))
              (distr (equal_nat, linorder_nat)
                (map (size_list o snd) state_space))))
       ()) ())
       (fn _ =>
         let
           val split =
             (if equal_mode mode Impl3 then split_k num_split state_space
               else split_ka num_split state_space);
           val split_distr =
             map (sum_list monoid_add_nat o map (size_list o snd)) split;
         in
           (fn f_ => fn () => f_
             ((print_line_impl
                ("Size of passed list distribution after split: " ^
                  show_str (show_list show_nat) split_distr))
             ()) ())
             (fn _ =>
               let
                 val tb = Time.now ();
               in
                 (fn f_ => fn () => f_
                   ((case mode
                      of Impl1 =>
                        rename_check num_split dc broadcast bounds automata k
                          l_0 s_0 formula m num_states num_actions renum_acts
                          renum_vars renum_clocks renum_states state_space
                      | Impl2 =>
                        (fn () =>
                          (rename_check2 num_split dc broadcast bounds automata
                            k l_0 s_0 formula m num_states num_actions
                            renum_acts renum_vars renum_clocks renum_states
                            state_space))
                      | Impl3 =>
                        (fn () =>
                          (rename_check3 num_split dc broadcast bounds automata
                            k l_0 s_0 formula m num_states num_actions
                            renum_acts renum_vars renum_clocks renum_states
                            state_space)))
                   ()) ())
                   (fn check =>
                     let
                       val tc =
                         (fn x => fn y => Time.- (x, y)) (Time.now ()) tb;
                     in
                       (fn f_ => fn () => f_
                         ((print_line_impl
                            ("Time for certificate checking: " ^
                              (fn x => Time.toString x) tc))
                         ()) ())
                         (fn _ =>
                           (case check
                             of Renaming_Failed =>
                               print_line_impl "Renaming failed"
                             | Preconds_Unsat =>
                               print_line_impl "Preconditions were not met"
                             | Sat => print_line_impl "Certificate was accepted"
                             | Unsat =>
                               print_line_impl "Certificate was rejected"))
                     end)
               end)
         end)
   end)
                                     end)
                               end)
                         end)
                   end)
             | Error aa => print_errors aa)
         end
    | Error a => print_errors a);

fun parse_convert_run_print dc s =
  (case binda (parse json s) convert
    of Result
         (ids_to_names,
           (_, (broadcast, (automata, (bounds, (formula, (l_0, s_0)))))))
      => (case rename_state_space show_literal dc ids_to_names
                 (broadcast, (automata, bounds)) l_0 s_0 formula
           of Result (r, (show_clk, (show_st, (_, _)))) =>
             (case r of NONE => (fn () => ())
               | SOME ra =>
                 (fn f_ => fn () => f_ (ra ()) ())
                   (fn rb =>
                     let
                       val _ =
                         writeln ("Number of discrete states: " ^
                                   show_str show_nat (size_list rb));
                       val _ =
                         writeln ("Size of passed list: " ^
                                   show_str show_nat
                                     (sum_list monoid_add_nat
                                       (map (size_list o snd) rb)));
                       val n =
                         size_list
                           (list_of_set equal_literal
                             (clk_set equal_literal automata));
                     in
                       (fn f_ => fn () => f_
                         ((imp_map
                            (fn (a, b) =>
                              (fn f_ => fn () => f_
                                ((imp_map ((fn aa => (fn () => aa)) o snd) b)
                                ()) ())
                                (fn ba =>
                                  (fn f_ => fn () => f_
                                    ((filter_dbm_list
                                       (linordered_cancel_ab_monoid_add_int,
 equal_int, heap_int)
                                       n ba)
                                    ()) ())
                                    (fn bb => (fn () => (a, bb)))))
                            rb)
                         ()) ())
                         (fn rc =>
                           let
                             val _ =
                               writeln ("Number of discrete states: " ^
 show_str show_nat (size_list rc));
                             val _ =
                               writeln ("Size of passed list after removing subsumed states: " ^
 show_str show_nat (sum_list monoid_add_nat (map (size_list o snd) rc)));
                             val show_dbm =
                               (fn m =>
                                 (fn f_ => fn () => f_
                                   ((show_dbm_impl_all
                                      (linordered_ab_group_add_int, equal_int,
heap_int)
                                      n show_clk
                                      (fn x => shows_prec_int zero_nata x []) m)
                                   ()) ())
                                   (fn sa =>
                                     (fn () =>
                                       ([Chara
   (false, false, true, true, true, true, false, false)] @
 sa @ [Chara (false, true, true, true, true, true, false, false)]))));
                           in
                             (fn f_ => fn () => f_
                               ((imp_map
                                  (fn (sa, xs) =>
                                    let
                                      val sb = show_st sa;
                                    in
                                      (fn f_ => fn () => f_
((imp_map show_dbm xs) ()) ())
(fn xsa =>
  let
    val _ =
      writeln (implode
                (sb @ [Chara (false, true, false, true, true, true, false,
                               false),
                        Chara (false, false, false, false, false, true, false,
                                false)] @
                        shows_prec_list (show_list show_char) zero_nata xsa
                          []));
  in
    (fn () => ())
  end)
                                    end)
                                  rc)
                               ()) ())
                               (fn _ => (fn () => ()))
                           end)
                     end))
           | Error es => let
                           val _ = map (fn a => writeln a) es;
                         in
                           (fn () => ())
                         end)
    | Error es => let
                    val _ = map (fn a => writeln a) es;
                  in
                    (fn () => ())
                  end);

end; (*struct Model_Checker*)

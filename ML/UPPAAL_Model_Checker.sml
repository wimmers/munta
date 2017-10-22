
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

fun new_array (a:'a) (n:int) = array (n, a);

fun array_length (a:'a ArrayType) = length a;

fun array_get (a:'a ArrayType) (i:int) = sub (a, i);

fun array_set (a:'a ArrayType) (i:int) (e:'a) = update (a, i, e);

fun array_of_list (xs:'a list) = fromList xs;

fun array_grow (a:'a ArrayType) (i:int) (x:'a) = grow (a, i, x);

fun array_shrink (a:'a ArrayType) (sz:int) = shrink (a,sz);

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

fun new_array (a:'a) (n:int) = array (n, a);

fun array_length (a:'a ArrayType) = length a;

fun array_get (a:'a ArrayType) (i:int) = sub (a, i);

fun array_set (a:'a ArrayType) (i:int) (e:'a) = update (a, i, e);

fun array_of_list (xs:'a list) = fromList xs;

fun array_grow (a:'a ArrayType) (i:int) (x:'a) = grow (a, i, x);

fun array_shrink (a:'a ArrayType) (sz:int) = shrink (a,sz);

fun array_get_oo (d:'a) (a:'a ArrayType) (i:int) =
  sub (a,i) handle Subscript => d

fun array_set_oo (d:(unit->'a ArrayType)) (a:'a ArrayType) (i:int) (e:'a) =
  update (a, i, e) handle Subscript => d ()

end;
end;





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



structure Bits_Integer : sig
  val set_bit : IntInf.int -> IntInf.int -> bool -> IntInf.int
  val shiftl : IntInf.int -> IntInf.int -> IntInf.int
  val shiftr : IntInf.int -> IntInf.int -> IntInf.int
  val test_bit : IntInf.int -> IntInf.int -> bool
end = struct

val maxWord = IntInf.pow (2, Word.wordSize);

fun set_bit x n b =
  if n < maxWord then
    if b then IntInf.orb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n)))
    else IntInf.andb (x, IntInf.notb (IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))))
  else raise (Fail ("Bit index too large: " ^ IntInf.toString n));

fun shiftl x n =
  if n < maxWord then IntInf.<< (x, Word.fromLargeInt (IntInf.toLarge n))
  else raise (Fail ("Shift operand too large: " ^ IntInf.toString n));

fun shiftr x n =
  if n < maxWord then IntInf.~>> (x, Word.fromLargeInt (IntInf.toLarge n))
  else raise (Fail ("Shift operand too large: " ^ IntInf.toString n));

fun test_bit x n =
  if n < maxWord then IntInf.andb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))) <> 0
  else raise (Fail ("Bit index too large: " ^ IntInf.toString n));

end; (*struct Bits_Integer*)


    structure Gabow_Skeleton_Statistics = struct
      val active = Unsynchronized.ref false
      val num_vis = Unsynchronized.ref 0

      val time = Unsynchronized.ref Time.zeroTime

      fun is_active () = !active
      fun newnode () =
      (
        num_vis := !num_vis + 1;
        if !num_vis mod 10000 = 0 then tracing (IntInf.toString (!num_vis) ^ "\n") else ()
      )

      fun start () = (active := true; time := Time.now ())
      fun stop () = (time := Time.- (Time.now (), !time))

      fun to_string () = let
        val t = Time.toMilliseconds (!time)
        val states_per_ms = real (!num_vis) / real t
        val realStr = Real.fmt (StringCvt.FIX (SOME 2))
      in
        "Required time: " ^ IntInf.toString (t) ^ "ms\n"
      ^ "States per ms: " ^ realStr states_per_ms ^ "\n"
      ^ "# states: " ^ IntInf.toString (!num_vis) ^ "\n"
      end
        
      val _ = Statistics.register_stat ("Gabow-Skeleton",is_active,to_string)

    end


structure Model_Checker : sig
  datatype int = Int_of_integer of IntInf.int
  val integer_of_int : int -> IntInf.int
  datatype 'a itself = Type
  type nat
  val nat_of_integer : IntInf.int -> nat
  val integer_of_nat : nat -> IntInf.int
  datatype instr = JMPZ of nat | ADD | NOT | AND | LT | LE | EQ | PUSH of int |
    POP | LID of nat | STORE | STOREI of nat * int | COPY | CALL | RETURN | HALT
    | STOREC of nat * int | SETF of bool
  datatype ('a, 'b) acconstraint = LTa of 'a * 'b | LEa of 'a * 'b |
    EQa of 'a * 'b | GT of 'a * 'b | GE of 'a * 'b
  datatype 'a instrc = INSTR of instr | CEXP of (nat, 'a) acconstraint
  type 'a set
  datatype 'a act = In of 'a | Out of 'a | Sil of 'a
  datatype bexp = Not of bexp | And of bexp * bexp | Or of bexp * bexp |
    Imply of bexp * bexp | Loc of nat * nat | Eq of nat * int | Lea of nat * int
    | Lta of nat * int | Ge of nat * int | Gt of nat * int
  type formula
  datatype result = REACHABLE | UNREACHABLE | INIT_INV_ERR
  val nat : int -> nat
  val map_option : ('a -> 'b) -> 'a option -> 'b option
  val bounded_int : (int * int) list -> int list -> bool
  val conjunction_check2 :
    (((nat * ('a * ('b * 'c))) list) list) list ->
      (int instrc option) list -> nat -> bool
  val time_indep_check2 :
    ((('a * ('b * (nat * 'c))) list) list) list ->
      (int instrc option) list -> nat -> bool
  val time_indep_check1 :
    (nat list) list -> (int instrc option) list -> nat -> bool
  val init_pred_check :
    nat ->
      (int instrc option) list -> nat -> (nat list) list -> int list -> bool
  val uPPAAL_Reachability_Problem_precompiled_start_state_axioms :
    nat ->
      nat ->
        (((nat * (nat act * (nat * nat))) list) list) list ->
          (int instrc option) list ->
            (int * int) list -> (nat list) list -> int list -> bool
  val check_pre :
    nat ->
      nat ->
        (((nat, int) acconstraint list) list) list ->
          (nat list) list ->
            (((nat * (nat act * (nat * nat))) list) list) list ->
              (int instrc option) list -> bool
  val uPPAAL_Reachability_Problem_precompiled :
    nat ->
      nat ->
        (((nat, int) acconstraint list) list) list ->
          (nat list) list ->
            (((nat * (nat act * (nat * nat))) list) list) list ->
              (int instrc option) list -> bool
  val uPPAAL_Reachability_Problem_precompiled_start_state :
    nat ->
      nat ->
        nat ->
          (((nat, int) acconstraint list) list) list ->
            (((nat * (nat act * (nat * nat))) list) list) list ->
              (int instrc option) list ->
                (int * int) list -> (nat list) list -> int list -> bool
  val check_ceiling :
    nat ->
      nat ->
        nat ->
          (((nat, int) acconstraint list) list) list ->
            (((nat * (nat act * (nat * nat))) list) list) list ->
              (int instrc option) list -> ((nat list) list) list -> bool
  val precond_mc :
    'a itself ->
      'b itself ->
        'c itself ->
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

datatype int = Int_of_integer of IntInf.int;

fun integer_of_int (Int_of_integer k) = k;

fun equal_inta k l = (((integer_of_int k) : IntInf.int) = (integer_of_int l));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_int = {equal = equal_inta} : int equal;

datatype typerepa = Typerep of string * typerepa list;

datatype num = One | Bit0 of num | Bit1 of num;

datatype 'a itself = Type;

fun typerep_inta t = Typerep ("Int.int", []);

type 'a typerep = {typerep : 'a itself -> typerepa};
val typerep = #typerep : 'a typerep -> 'a itself -> typerepa;

type 'a countable = {};

type 'a heap = {countable_heap : 'a countable, typerep_heap : 'a typerep};
val countable_heap = #countable_heap : 'a heap -> 'a countable;
val typerep_heap = #typerep_heap : 'a heap -> 'a typerep;

val countable_int = {} : int countable;

val typerep_int = {typerep = typerep_inta} : int typerep;

val heap_int = {countable_heap = countable_int, typerep_heap = typerep_int} :
  int heap;

fun plus_inta k l =
  Int_of_integer (IntInf.+ (integer_of_int k, integer_of_int l));

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_int = {plus = plus_inta} : int plus;

val zero_inta : int = Int_of_integer (0 : IntInf.int);

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_int = {zero = zero_inta} : int zero;

fun minus_inta k l =
  Int_of_integer (IntInf.- (integer_of_int k, integer_of_int l));

type 'a minus = {minus : 'a -> 'a -> 'a};
val minus = #minus : 'a minus -> 'a -> 'a -> 'a;

val minus_int = {minus = minus_inta} : int minus;

fun uminus_inta k = Int_of_integer (IntInf.~ (integer_of_int k));

type 'a uminus = {uminus : 'a -> 'a};
val uminus = #uminus : 'a uminus -> 'a -> 'a;

val uminus_int = {uminus = uminus_inta} : int uminus;

fun less_eq_int k l = IntInf.<= (integer_of_int k, integer_of_int l);

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun less_int k l = IntInf.< (integer_of_int k, integer_of_int l);

val ord_int = {less_eq = less_eq_int, less = less_int} : int ord;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

val preorder_int = {ord_preorder = ord_int} : int preorder;

val order_int = {preorder_order = preorder_int} : int order;

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

val semigroup_add_int = {plus_semigroup_add = plus_int} : int semigroup_add;

val cancel_semigroup_add_int =
  {semigroup_add_cancel_semigroup_add = semigroup_add_int} :
  int cancel_semigroup_add;

val monoid_add_int =
  {semigroup_add_monoid_add = semigroup_add_int, zero_monoid_add = zero_int} :
  int monoid_add;

val group_add_int =
  {cancel_semigroup_add_group_add = cancel_semigroup_add_int,
    minus_group_add = minus_int, monoid_add_group_add = monoid_add_int,
    uminus_group_add = uminus_int}
  : int group_add;

fun max A_ a b = (if less_eq A_ a b then b else a);

datatype nat = Nat of IntInf.int;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun def_hashmap_size_int x = (fn _ => nat_of_integer (16 : IntInf.int)) x;

type 'a hashable =
  {hashcode : 'a -> Word32.word, def_hashmap_size : 'a itself -> nat};
val hashcode = #hashcode : 'a hashable -> 'a -> Word32.word;
val def_hashmap_size = #def_hashmap_size : 'a hashable -> 'a itself -> nat;

fun uint32_of_int i = Word32.fromLargeInt (IntInf.toLarge (integer_of_int i));

fun hashcode_int i = uint32_of_int i;

val hashable_int =
  {hashcode = hashcode_int, def_hashmap_size = def_hashmap_size_int} :
  int hashable;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

val linorder_int = {order_linorder = order_int} : int linorder;

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
  : int ab_semigroup_add;

val cancel_ab_semigroup_add_int =
  {ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_int,
    cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_int,
    minus_cancel_ab_semigroup_add = minus_int}
  : int cancel_ab_semigroup_add;

val comm_monoid_add_int =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_int,
    monoid_add_comm_monoid_add = monoid_add_int}
  : int comm_monoid_add;

val cancel_comm_monoid_add_int =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add = cancel_ab_semigroup_add_int,
    comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_int}
  : int cancel_comm_monoid_add;

val ab_group_add_int =
  {cancel_comm_monoid_add_ab_group_add = cancel_comm_monoid_add_int,
    group_add_ab_group_add = group_add_int}
  : int ab_group_add;

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
  : int ordered_ab_semigroup_add;

val strict_ordered_ab_semigroup_add_int =
  {ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add =
     ordered_ab_semigroup_add_int}
  : int strict_ordered_ab_semigroup_add;

val ordered_cancel_ab_semigroup_add_int =
  {cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
     cancel_ab_semigroup_add_int,
    strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
      strict_ordered_ab_semigroup_add_int}
  : int ordered_cancel_ab_semigroup_add;

val ordered_ab_semigroup_add_imp_le_int =
  {ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le =
     ordered_cancel_ab_semigroup_add_int}
  : int ordered_ab_semigroup_add_imp_le;

val strict_ordered_comm_monoid_add_int =
  {comm_monoid_add_strict_ordered_comm_monoid_add = comm_monoid_add_int,
    strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add =
      strict_ordered_ab_semigroup_add_int}
  : int strict_ordered_comm_monoid_add;

val ordered_comm_monoid_add_int =
  {comm_monoid_add_ordered_comm_monoid_add = comm_monoid_add_int,
    ordered_ab_semigroup_add_ordered_comm_monoid_add =
      ordered_ab_semigroup_add_int}
  : int ordered_comm_monoid_add;

val ordered_cancel_comm_monoid_add_int =
  {ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add =
     ordered_cancel_ab_semigroup_add_int,
    ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
      ordered_comm_monoid_add_int,
    strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
      strict_ordered_comm_monoid_add_int}
  : int ordered_cancel_comm_monoid_add;

val ordered_ab_semigroup_monoid_add_imp_le_int =
  {cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
     cancel_comm_monoid_add_int,
    ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le =
      ordered_ab_semigroup_add_imp_le_int,
    ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
      ordered_cancel_comm_monoid_add_int}
  : int ordered_ab_semigroup_monoid_add_imp_le;

val ordered_ab_group_add_int =
  {ab_group_add_ordered_ab_group_add = ab_group_add_int,
    ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add =
      ordered_ab_semigroup_monoid_add_imp_le_int}
  : int ordered_ab_group_add;

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
  : int linordered_ab_semigroup_add;

val linordered_cancel_ab_semigroup_add_int =
  {linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add =
     linordered_ab_semigroup_add_int,
    ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add =
      ordered_ab_semigroup_add_imp_le_int}
  : int linordered_cancel_ab_semigroup_add;

val linordered_ab_monoid_add_int =
  {linordered_ab_semigroup_add_linordered_ab_monoid_add =
     linordered_ab_semigroup_add_int,
    ordered_comm_monoid_add_linordered_ab_monoid_add =
      ordered_comm_monoid_add_int}
  : int linordered_ab_monoid_add;

val linordered_cancel_ab_monoid_add_int =
  {linordered_ab_monoid_add_linordered_cancel_ab_monoid_add =
     linordered_ab_monoid_add_int,
    linordered_cancel_ab_semigroup_add_linordered_cancel_ab_monoid_add =
      linordered_cancel_ab_semigroup_add_int}
  : int linordered_cancel_ab_monoid_add;

val linordered_ab_group_add_int =
  {linordered_cancel_ab_monoid_add_linordered_ab_group_add =
     linordered_cancel_ab_monoid_add_int,
    ordered_ab_group_add_linordered_ab_group_add = ordered_ab_group_add_int}
  : int linordered_ab_group_add;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

val equal_nat = {equal = equal_nata} : nat equal;

fun typerep_nata t = Typerep ("Nat.nat", []);

val countable_nat = {} : nat countable;

val typerep_nat = {typerep = typerep_nata} : nat typerep;

val heap_nat = {countable_heap = countable_nat, typerep_heap = typerep_nat} :
  nat heap;

val one_nata : nat = Nat (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_nat = {one = one_nata} : nat one;

val zero_nata : nat = Nat (0 : IntInf.int);

val zero_nat = {zero = zero_nata} : nat zero;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

fun sup_nata x = max ord_nat x;

type 'a sup = {sup : 'a -> 'a -> 'a};
val sup = #sup : 'a sup -> 'a -> 'a -> 'a;

val sup_nat = {sup = sup_nata} : nat sup;

val preorder_nat = {ord_preorder = ord_nat} : nat preorder;

val order_nat = {preorder_order = preorder_nat} : nat order;

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

fun times_nat m n = Nat (IntInf.* (integer_of_nat m, integer_of_nat n));

fun def_hashmap_size_list A_ =
  (fn _ =>
    times_nat (nat_of_integer (2 : IntInf.int)) (def_hashmap_size A_ Type));

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

fun equal_optiona A_ NONE (SOME x2) = false
  | equal_optiona A_ (SOME x2) NONE = false
  | equal_optiona A_ (SOME x2) (SOME y2) = eq A_ x2 y2
  | equal_optiona A_ NONE NONE = true;

fun equal_option A_ = {equal = equal_optiona A_} : ('a option) equal;

fun equal_bool p true = p
  | equal_bool p false = not p
  | equal_bool true p = p
  | equal_bool false p = not p;

datatype instr = JMPZ of nat | ADD | NOT | AND | LT | LE | EQ | PUSH of int |
  POP | LID of nat | STORE | STOREI of nat * int | COPY | CALL | RETURN | HALT |
  STOREC of nat * int | SETF of bool;

fun equal_instra (STOREC (x171, x172)) (SETF x18) = false
  | equal_instra (SETF x18) (STOREC (x171, x172)) = false
  | equal_instra HALT (SETF x18) = false
  | equal_instra (SETF x18) HALT = false
  | equal_instra HALT (STOREC (x171, x172)) = false
  | equal_instra (STOREC (x171, x172)) HALT = false
  | equal_instra RETURN (SETF x18) = false
  | equal_instra (SETF x18) RETURN = false
  | equal_instra RETURN (STOREC (x171, x172)) = false
  | equal_instra (STOREC (x171, x172)) RETURN = false
  | equal_instra RETURN HALT = false
  | equal_instra HALT RETURN = false
  | equal_instra CALL (SETF x18) = false
  | equal_instra (SETF x18) CALL = false
  | equal_instra CALL (STOREC (x171, x172)) = false
  | equal_instra (STOREC (x171, x172)) CALL = false
  | equal_instra CALL HALT = false
  | equal_instra HALT CALL = false
  | equal_instra CALL RETURN = false
  | equal_instra RETURN CALL = false
  | equal_instra COPY (SETF x18) = false
  | equal_instra (SETF x18) COPY = false
  | equal_instra COPY (STOREC (x171, x172)) = false
  | equal_instra (STOREC (x171, x172)) COPY = false
  | equal_instra COPY HALT = false
  | equal_instra HALT COPY = false
  | equal_instra COPY RETURN = false
  | equal_instra RETURN COPY = false
  | equal_instra COPY CALL = false
  | equal_instra CALL COPY = false
  | equal_instra (STOREI (x121, x122)) (SETF x18) = false
  | equal_instra (SETF x18) (STOREI (x121, x122)) = false
  | equal_instra (STOREI (x121, x122)) (STOREC (x171, x172)) = false
  | equal_instra (STOREC (x171, x172)) (STOREI (x121, x122)) = false
  | equal_instra (STOREI (x121, x122)) HALT = false
  | equal_instra HALT (STOREI (x121, x122)) = false
  | equal_instra (STOREI (x121, x122)) RETURN = false
  | equal_instra RETURN (STOREI (x121, x122)) = false
  | equal_instra (STOREI (x121, x122)) CALL = false
  | equal_instra CALL (STOREI (x121, x122)) = false
  | equal_instra (STOREI (x121, x122)) COPY = false
  | equal_instra COPY (STOREI (x121, x122)) = false
  | equal_instra STORE (SETF x18) = false
  | equal_instra (SETF x18) STORE = false
  | equal_instra STORE (STOREC (x171, x172)) = false
  | equal_instra (STOREC (x171, x172)) STORE = false
  | equal_instra STORE HALT = false
  | equal_instra HALT STORE = false
  | equal_instra STORE RETURN = false
  | equal_instra RETURN STORE = false
  | equal_instra STORE CALL = false
  | equal_instra CALL STORE = false
  | equal_instra STORE COPY = false
  | equal_instra COPY STORE = false
  | equal_instra STORE (STOREI (x121, x122)) = false
  | equal_instra (STOREI (x121, x122)) STORE = false
  | equal_instra (LID x10) (SETF x18) = false
  | equal_instra (SETF x18) (LID x10) = false
  | equal_instra (LID x10) (STOREC (x171, x172)) = false
  | equal_instra (STOREC (x171, x172)) (LID x10) = false
  | equal_instra (LID x10) HALT = false
  | equal_instra HALT (LID x10) = false
  | equal_instra (LID x10) RETURN = false
  | equal_instra RETURN (LID x10) = false
  | equal_instra (LID x10) CALL = false
  | equal_instra CALL (LID x10) = false
  | equal_instra (LID x10) COPY = false
  | equal_instra COPY (LID x10) = false
  | equal_instra (LID x10) (STOREI (x121, x122)) = false
  | equal_instra (STOREI (x121, x122)) (LID x10) = false
  | equal_instra (LID x10) STORE = false
  | equal_instra STORE (LID x10) = false
  | equal_instra POP (SETF x18) = false
  | equal_instra (SETF x18) POP = false
  | equal_instra POP (STOREC (x171, x172)) = false
  | equal_instra (STOREC (x171, x172)) POP = false
  | equal_instra POP HALT = false
  | equal_instra HALT POP = false
  | equal_instra POP RETURN = false
  | equal_instra RETURN POP = false
  | equal_instra POP CALL = false
  | equal_instra CALL POP = false
  | equal_instra POP COPY = false
  | equal_instra COPY POP = false
  | equal_instra POP (STOREI (x121, x122)) = false
  | equal_instra (STOREI (x121, x122)) POP = false
  | equal_instra POP STORE = false
  | equal_instra STORE POP = false
  | equal_instra POP (LID x10) = false
  | equal_instra (LID x10) POP = false
  | equal_instra (PUSH x8) (SETF x18) = false
  | equal_instra (SETF x18) (PUSH x8) = false
  | equal_instra (PUSH x8) (STOREC (x171, x172)) = false
  | equal_instra (STOREC (x171, x172)) (PUSH x8) = false
  | equal_instra (PUSH x8) HALT = false
  | equal_instra HALT (PUSH x8) = false
  | equal_instra (PUSH x8) RETURN = false
  | equal_instra RETURN (PUSH x8) = false
  | equal_instra (PUSH x8) CALL = false
  | equal_instra CALL (PUSH x8) = false
  | equal_instra (PUSH x8) COPY = false
  | equal_instra COPY (PUSH x8) = false
  | equal_instra (PUSH x8) (STOREI (x121, x122)) = false
  | equal_instra (STOREI (x121, x122)) (PUSH x8) = false
  | equal_instra (PUSH x8) STORE = false
  | equal_instra STORE (PUSH x8) = false
  | equal_instra (PUSH x8) (LID x10) = false
  | equal_instra (LID x10) (PUSH x8) = false
  | equal_instra (PUSH x8) POP = false
  | equal_instra POP (PUSH x8) = false
  | equal_instra EQ (SETF x18) = false
  | equal_instra (SETF x18) EQ = false
  | equal_instra EQ (STOREC (x171, x172)) = false
  | equal_instra (STOREC (x171, x172)) EQ = false
  | equal_instra EQ HALT = false
  | equal_instra HALT EQ = false
  | equal_instra EQ RETURN = false
  | equal_instra RETURN EQ = false
  | equal_instra EQ CALL = false
  | equal_instra CALL EQ = false
  | equal_instra EQ COPY = false
  | equal_instra COPY EQ = false
  | equal_instra EQ (STOREI (x121, x122)) = false
  | equal_instra (STOREI (x121, x122)) EQ = false
  | equal_instra EQ STORE = false
  | equal_instra STORE EQ = false
  | equal_instra EQ (LID x10) = false
  | equal_instra (LID x10) EQ = false
  | equal_instra EQ POP = false
  | equal_instra POP EQ = false
  | equal_instra EQ (PUSH x8) = false
  | equal_instra (PUSH x8) EQ = false
  | equal_instra LE (SETF x18) = false
  | equal_instra (SETF x18) LE = false
  | equal_instra LE (STOREC (x171, x172)) = false
  | equal_instra (STOREC (x171, x172)) LE = false
  | equal_instra LE HALT = false
  | equal_instra HALT LE = false
  | equal_instra LE RETURN = false
  | equal_instra RETURN LE = false
  | equal_instra LE CALL = false
  | equal_instra CALL LE = false
  | equal_instra LE COPY = false
  | equal_instra COPY LE = false
  | equal_instra LE (STOREI (x121, x122)) = false
  | equal_instra (STOREI (x121, x122)) LE = false
  | equal_instra LE STORE = false
  | equal_instra STORE LE = false
  | equal_instra LE (LID x10) = false
  | equal_instra (LID x10) LE = false
  | equal_instra LE POP = false
  | equal_instra POP LE = false
  | equal_instra LE (PUSH x8) = false
  | equal_instra (PUSH x8) LE = false
  | equal_instra LE EQ = false
  | equal_instra EQ LE = false
  | equal_instra LT (SETF x18) = false
  | equal_instra (SETF x18) LT = false
  | equal_instra LT (STOREC (x171, x172)) = false
  | equal_instra (STOREC (x171, x172)) LT = false
  | equal_instra LT HALT = false
  | equal_instra HALT LT = false
  | equal_instra LT RETURN = false
  | equal_instra RETURN LT = false
  | equal_instra LT CALL = false
  | equal_instra CALL LT = false
  | equal_instra LT COPY = false
  | equal_instra COPY LT = false
  | equal_instra LT (STOREI (x121, x122)) = false
  | equal_instra (STOREI (x121, x122)) LT = false
  | equal_instra LT STORE = false
  | equal_instra STORE LT = false
  | equal_instra LT (LID x10) = false
  | equal_instra (LID x10) LT = false
  | equal_instra LT POP = false
  | equal_instra POP LT = false
  | equal_instra LT (PUSH x8) = false
  | equal_instra (PUSH x8) LT = false
  | equal_instra LT EQ = false
  | equal_instra EQ LT = false
  | equal_instra LT LE = false
  | equal_instra LE LT = false
  | equal_instra AND (SETF x18) = false
  | equal_instra (SETF x18) AND = false
  | equal_instra AND (STOREC (x171, x172)) = false
  | equal_instra (STOREC (x171, x172)) AND = false
  | equal_instra AND HALT = false
  | equal_instra HALT AND = false
  | equal_instra AND RETURN = false
  | equal_instra RETURN AND = false
  | equal_instra AND CALL = false
  | equal_instra CALL AND = false
  | equal_instra AND COPY = false
  | equal_instra COPY AND = false
  | equal_instra AND (STOREI (x121, x122)) = false
  | equal_instra (STOREI (x121, x122)) AND = false
  | equal_instra AND STORE = false
  | equal_instra STORE AND = false
  | equal_instra AND (LID x10) = false
  | equal_instra (LID x10) AND = false
  | equal_instra AND POP = false
  | equal_instra POP AND = false
  | equal_instra AND (PUSH x8) = false
  | equal_instra (PUSH x8) AND = false
  | equal_instra AND EQ = false
  | equal_instra EQ AND = false
  | equal_instra AND LE = false
  | equal_instra LE AND = false
  | equal_instra AND LT = false
  | equal_instra LT AND = false
  | equal_instra NOT (SETF x18) = false
  | equal_instra (SETF x18) NOT = false
  | equal_instra NOT (STOREC (x171, x172)) = false
  | equal_instra (STOREC (x171, x172)) NOT = false
  | equal_instra NOT HALT = false
  | equal_instra HALT NOT = false
  | equal_instra NOT RETURN = false
  | equal_instra RETURN NOT = false
  | equal_instra NOT CALL = false
  | equal_instra CALL NOT = false
  | equal_instra NOT COPY = false
  | equal_instra COPY NOT = false
  | equal_instra NOT (STOREI (x121, x122)) = false
  | equal_instra (STOREI (x121, x122)) NOT = false
  | equal_instra NOT STORE = false
  | equal_instra STORE NOT = false
  | equal_instra NOT (LID x10) = false
  | equal_instra (LID x10) NOT = false
  | equal_instra NOT POP = false
  | equal_instra POP NOT = false
  | equal_instra NOT (PUSH x8) = false
  | equal_instra (PUSH x8) NOT = false
  | equal_instra NOT EQ = false
  | equal_instra EQ NOT = false
  | equal_instra NOT LE = false
  | equal_instra LE NOT = false
  | equal_instra NOT LT = false
  | equal_instra LT NOT = false
  | equal_instra NOT AND = false
  | equal_instra AND NOT = false
  | equal_instra ADD (SETF x18) = false
  | equal_instra (SETF x18) ADD = false
  | equal_instra ADD (STOREC (x171, x172)) = false
  | equal_instra (STOREC (x171, x172)) ADD = false
  | equal_instra ADD HALT = false
  | equal_instra HALT ADD = false
  | equal_instra ADD RETURN = false
  | equal_instra RETURN ADD = false
  | equal_instra ADD CALL = false
  | equal_instra CALL ADD = false
  | equal_instra ADD COPY = false
  | equal_instra COPY ADD = false
  | equal_instra ADD (STOREI (x121, x122)) = false
  | equal_instra (STOREI (x121, x122)) ADD = false
  | equal_instra ADD STORE = false
  | equal_instra STORE ADD = false
  | equal_instra ADD (LID x10) = false
  | equal_instra (LID x10) ADD = false
  | equal_instra ADD POP = false
  | equal_instra POP ADD = false
  | equal_instra ADD (PUSH x8) = false
  | equal_instra (PUSH x8) ADD = false
  | equal_instra ADD EQ = false
  | equal_instra EQ ADD = false
  | equal_instra ADD LE = false
  | equal_instra LE ADD = false
  | equal_instra ADD LT = false
  | equal_instra LT ADD = false
  | equal_instra ADD AND = false
  | equal_instra AND ADD = false
  | equal_instra ADD NOT = false
  | equal_instra NOT ADD = false
  | equal_instra (JMPZ x1) (SETF x18) = false
  | equal_instra (SETF x18) (JMPZ x1) = false
  | equal_instra (JMPZ x1) (STOREC (x171, x172)) = false
  | equal_instra (STOREC (x171, x172)) (JMPZ x1) = false
  | equal_instra (JMPZ x1) HALT = false
  | equal_instra HALT (JMPZ x1) = false
  | equal_instra (JMPZ x1) RETURN = false
  | equal_instra RETURN (JMPZ x1) = false
  | equal_instra (JMPZ x1) CALL = false
  | equal_instra CALL (JMPZ x1) = false
  | equal_instra (JMPZ x1) COPY = false
  | equal_instra COPY (JMPZ x1) = false
  | equal_instra (JMPZ x1) (STOREI (x121, x122)) = false
  | equal_instra (STOREI (x121, x122)) (JMPZ x1) = false
  | equal_instra (JMPZ x1) STORE = false
  | equal_instra STORE (JMPZ x1) = false
  | equal_instra (JMPZ x1) (LID x10) = false
  | equal_instra (LID x10) (JMPZ x1) = false
  | equal_instra (JMPZ x1) POP = false
  | equal_instra POP (JMPZ x1) = false
  | equal_instra (JMPZ x1) (PUSH x8) = false
  | equal_instra (PUSH x8) (JMPZ x1) = false
  | equal_instra (JMPZ x1) EQ = false
  | equal_instra EQ (JMPZ x1) = false
  | equal_instra (JMPZ x1) LE = false
  | equal_instra LE (JMPZ x1) = false
  | equal_instra (JMPZ x1) LT = false
  | equal_instra LT (JMPZ x1) = false
  | equal_instra (JMPZ x1) AND = false
  | equal_instra AND (JMPZ x1) = false
  | equal_instra (JMPZ x1) NOT = false
  | equal_instra NOT (JMPZ x1) = false
  | equal_instra (JMPZ x1) ADD = false
  | equal_instra ADD (JMPZ x1) = false
  | equal_instra (SETF x18) (SETF y18) = equal_bool x18 y18
  | equal_instra (STOREC (x171, x172)) (STOREC (y171, y172)) =
    equal_nata x171 y171 andalso equal_inta x172 y172
  | equal_instra (STOREI (x121, x122)) (STOREI (y121, y122)) =
    equal_nata x121 y121 andalso equal_inta x122 y122
  | equal_instra (LID x10) (LID y10) = equal_nata x10 y10
  | equal_instra (PUSH x8) (PUSH y8) = equal_inta x8 y8
  | equal_instra (JMPZ x1) (JMPZ y1) = equal_nata x1 y1
  | equal_instra HALT HALT = true
  | equal_instra RETURN RETURN = true
  | equal_instra CALL CALL = true
  | equal_instra COPY COPY = true
  | equal_instra STORE STORE = true
  | equal_instra POP POP = true
  | equal_instra EQ EQ = true
  | equal_instra LE LE = true
  | equal_instra LT LT = true
  | equal_instra AND AND = true
  | equal_instra NOT NOT = true
  | equal_instra ADD ADD = true;

val equal_instr = {equal = equal_instra} : instr equal;

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

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

fun def_hashmap_size_prod A_ B_ =
  (fn _ => plus_nat (def_hashmap_size A_ Type) (def_hashmap_size B_ Type));

fun snd (x1, x2) = x2;

fun fst (x1, x2) = x1;

fun hashcode_prod A_ B_ x =
  Word32.+ (Word32.* (hashcode A_
                        (fst x), Word32.fromLargeInt (IntInf.toLarge (33 : IntInf.int))), hashcode
            B_ (snd x));

fun hashable_prod A_ B_ =
  {hashcode = hashcode_prod A_ B_,
    def_hashmap_size = def_hashmap_size_prod A_ B_}
  : ('a * 'b) hashable;

datatype ('a, 'b) acconstraint = LTa of 'a * 'b | LEa of 'a * 'b |
  EQa of 'a * 'b | GT of 'a * 'b | GE of 'a * 'b;

fun equal_acconstrainta A_ B_ (GT (x41, x42)) (GE (x51, x52)) = false
  | equal_acconstrainta A_ B_ (GE (x51, x52)) (GT (x41, x42)) = false
  | equal_acconstrainta A_ B_ (EQa (x31, x32)) (GE (x51, x52)) = false
  | equal_acconstrainta A_ B_ (GE (x51, x52)) (EQa (x31, x32)) = false
  | equal_acconstrainta A_ B_ (EQa (x31, x32)) (GT (x41, x42)) = false
  | equal_acconstrainta A_ B_ (GT (x41, x42)) (EQa (x31, x32)) = false
  | equal_acconstrainta A_ B_ (LEa (x21, x22)) (GE (x51, x52)) = false
  | equal_acconstrainta A_ B_ (GE (x51, x52)) (LEa (x21, x22)) = false
  | equal_acconstrainta A_ B_ (LEa (x21, x22)) (GT (x41, x42)) = false
  | equal_acconstrainta A_ B_ (GT (x41, x42)) (LEa (x21, x22)) = false
  | equal_acconstrainta A_ B_ (LEa (x21, x22)) (EQa (x31, x32)) = false
  | equal_acconstrainta A_ B_ (EQa (x31, x32)) (LEa (x21, x22)) = false
  | equal_acconstrainta A_ B_ (LTa (x11, x12)) (GE (x51, x52)) = false
  | equal_acconstrainta A_ B_ (GE (x51, x52)) (LTa (x11, x12)) = false
  | equal_acconstrainta A_ B_ (LTa (x11, x12)) (GT (x41, x42)) = false
  | equal_acconstrainta A_ B_ (GT (x41, x42)) (LTa (x11, x12)) = false
  | equal_acconstrainta A_ B_ (LTa (x11, x12)) (EQa (x31, x32)) = false
  | equal_acconstrainta A_ B_ (EQa (x31, x32)) (LTa (x11, x12)) = false
  | equal_acconstrainta A_ B_ (LTa (x11, x12)) (LEa (x21, x22)) = false
  | equal_acconstrainta A_ B_ (LEa (x21, x22)) (LTa (x11, x12)) = false
  | equal_acconstrainta A_ B_ (GE (x51, x52)) (GE (y51, y52)) =
    eq A_ x51 y51 andalso eq B_ x52 y52
  | equal_acconstrainta A_ B_ (GT (x41, x42)) (GT (y41, y42)) =
    eq A_ x41 y41 andalso eq B_ x42 y42
  | equal_acconstrainta A_ B_ (EQa (x31, x32)) (EQa (y31, y32)) =
    eq A_ x31 y31 andalso eq B_ x32 y32
  | equal_acconstrainta A_ B_ (LEa (x21, x22)) (LEa (y21, y22)) =
    eq A_ x21 y21 andalso eq B_ x22 y22
  | equal_acconstrainta A_ B_ (LTa (x11, x12)) (LTa (y11, y12)) =
    eq A_ x11 y11 andalso eq B_ x12 y12;

datatype 'a instrc = INSTR of instr | CEXP of (nat, 'a) acconstraint;

fun equal_instrca A_ (INSTR x1) (CEXP x2) = false
  | equal_instrca A_ (CEXP x2) (INSTR x1) = false
  | equal_instrca A_ (CEXP x2) (CEXP y2) =
    equal_acconstrainta equal_nat A_ x2 y2
  | equal_instrca A_ (INSTR x1) (INSTR y1) = equal_instra x1 y1;

fun equal_instrc A_ = {equal = equal_instrca A_} : 'a instrc equal;

fun equal_acconstraint A_ B_ = {equal = equal_acconstrainta A_ B_} :
  ('a, 'b) acconstraint equal;

datatype 'a set = Set of 'a list | Coset of 'a list;

datatype 'a act = In of 'a | Out of 'a | Sil of 'a;

datatype ('a, 'b) hashtable = HashTable of (('a * 'b) list) array * nat;

datatype ('a, 'b) hashmap =
  HashMap of (('a * 'b) list) FArray.IsabelleMapping.ArrayType * nat;

datatype bexp = Not of bexp | And of bexp * bexp | Or of bexp * bexp |
  Imply of bexp * bexp | Loc of nat * nat | Eq of nat * int | Lea of nat * int |
  Lta of nat * int | Ge of nat * int | Gt of nat * int;

datatype formula = EX of bexp | EG of bexp | AX of bexp | AG of bexp |
  Leadsto of bexp * bexp;

datatype ('a, 'b, 'c, 'd) gen_g_impl_ext = Gen_g_impl_ext of 'a * 'b * 'c * 'd;

datatype result = REACHABLE | UNREACHABLE | INIT_INV_ERR;

fun id x = (fn xa => xa) x;

fun nat k = Nat (max ord_integer (0 : IntInf.int) (integer_of_int k));

fun suc n = plus_nat n one_nata;

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

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
  (fn () => let
              val i = (fn () => IntInf.fromInt
(Array.length a)) ();
            in
              nat_of_integer i
            end);

fun new A_ =
  (fn a => fn b => (fn () => Array.array 
(IntInf.toInt a, b))) o
    integer_of_nat;

fun ntha A_ a n = (fn () => Array.sub 
(a, IntInf.toInt (integer_of_nat n)));

fun upd A_ i x a =
  (fn () =>
    let
      val _ =
        (fn () => Array.update 
(a, IntInf.toInt (integer_of_nat i), x)) ();
    in
      a
    end);

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun null [] = true
  | null (x :: xs) = false;

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun image f (Set xs) = Set (map f xs);

fun make A_ n f =
  (fn () => 
Array.tabulate (IntInf.toInt (integer_of_nat n),
    (f o nat_of_integer) o IntInf.fromInt));

fun sub asa n =
  (Vector.sub o (fn (a, b) => (a, IntInf.toInt b))) (asa, integer_of_nat n);

fun foldr f [] = id
  | foldr f (x :: xs) = f x o foldr f xs;

fun filtera p [] = []
  | filtera p (x :: xs) = (if p x then x :: filtera p xs else filtera p xs);

fun filter p (Set xs) = Set (filtera p xs);

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

fun concat xss = foldr (fn a => fn b => a @ b) xss [];

fun foldli [] c f sigma = sigma
  | foldli (x :: xs) c f sigma =
    (if c sigma then foldli xs c f (f x sigma) else sigma);

fun hd (x21 :: x22) = x21;

fun tl [] = []
  | tl (x21 :: x22) = x22;

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if membera A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun replicate n x =
  (if equal_nata n zero_nata then []
    else x :: replicate (minus_nat n one_nata) x);

fun is_none (SOME x) = false
  | is_none NONE = true;

fun blit A_ src si dst di len =
  (fn () => 
    array_blit src (integer_of_nat
                     si) dst (integer_of_nat di) (integer_of_nat len));

fun gen_length n (x :: xs) = gen_length (suc n) xs
  | gen_length n [] = n;

fun map_filter f [] = []
  | map_filter f (x :: xs) =
    (case f x of NONE => map_filter f xs | SOME y => y :: map_filter f xs);

fun int_of x = (if x then Int_of_integer (1 : IntInf.int) else zero_inta);

fun list_update [] i y = []
  | list_update (x :: xs) i y =
    (if equal_nata i zero_nata then y :: xs
      else x :: list_update xs (minus_nat i one_nata) y);

fun step (JMPZ q) (pc, (st, (m, (f, rs)))) =
  SOME ((if f then plus_nat pc one_nata else q), (st, (m, (f, rs))))
  | step ADD (pc, (a :: b :: st, (m, (f, rs)))) =
    SOME (plus_nat pc one_nata, (plus_inta a b :: st, (m, (f, rs))))
  | step NOT (pc, (b :: st, (m, (f, rs)))) =
    SOME (plus_nat pc one_nata, (st, (m, (not f, rs))))
  | step AND (pc, (b :: st, (m, (f, rs)))) =
    (if equal_inta b zero_inta orelse
          equal_inta b (Int_of_integer (1 : IntInf.int))
      then SOME (plus_nat pc one_nata,
                  (st, (m, (equal_inta b
                              (Int_of_integer (1 : IntInf.int)) andalso
                              f,
                             rs))))
      else NONE)
  | step LT (pc, (a :: b :: st, (m, (f, rs)))) =
    SOME (plus_nat pc one_nata, (st, (m, (less_int a b, rs))))
  | step LE (pc, (a :: b :: st, (m, (f, rs)))) =
    SOME (plus_nat pc one_nata, (st, (m, (less_eq_int a b, rs))))
  | step EQ (pc, (a :: b :: st, (m, (f, rs)))) =
    SOME (plus_nat pc one_nata, (st, (m, (equal_inta a b, rs))))
  | step (PUSH v) (pc, (st, (m, (f, rs)))) =
    SOME (plus_nat pc one_nata, (v :: st, (m, (f, rs))))
  | step POP (pc, (v :: st, (m, (f, rs)))) =
    SOME (plus_nat pc one_nata, (st, (m, (f, rs))))
  | step (LID r) (pc, (st, (m, (f, rs)))) =
    SOME (plus_nat pc one_nata, (nth m r :: st, (m, (f, rs))))
  | step STORE (pc, (v :: r :: st, (m, (f, rs)))) =
    (if less_eq_int zero_inta r
      then SOME (plus_nat pc one_nata, (st, (list_update m (nat r) v, (f, rs))))
      else NONE)
  | step (STOREI (r, v)) (pc, (st, (m, (f, rs)))) =
    SOME (plus_nat pc one_nata, (st, (list_update m r v, (f, rs))))
  | step COPY (pc, (st, (m, (f, rs)))) =
    SOME (plus_nat pc one_nata, (int_of f :: st, (m, (f, rs))))
  | step CALL (pc, (q :: st, (m, (f, rs)))) =
    (if less_eq_int zero_inta q
      then SOME (nat q, (int_of_nat pc :: st, (m, (f, rs)))) else NONE)
  | step RETURN (pc, (q :: st, (m, (f, rs)))) =
    (if less_eq_int zero_inta q
      then SOME (plus_nat (nat q) one_nata, (st, (m, (f, rs)))) else NONE)
  | step (STOREC (c, d)) (pc, (st, (m, (f, rs)))) =
    (if equal_inta d zero_inta
      then SOME (plus_nat pc one_nata, (st, (m, (f, c :: rs)))) else NONE)
  | step (SETF b) (pc, (st, (m, (f, rs)))) =
    SOME (plus_nat pc one_nata, (st, (m, (b, rs))))
  | step ADD (v, ([], vc)) = NONE
  | step ADD (v, ([vd], vc)) = NONE
  | step NOT (v, ([], vc)) = NONE
  | step AND (v, ([], vc)) = NONE
  | step LT (v, ([], vc)) = NONE
  | step LT (v, ([vd], vc)) = NONE
  | step LE (v, ([], vc)) = NONE
  | step LE (v, ([vd], vc)) = NONE
  | step EQ (v, ([], vc)) = NONE
  | step EQ (v, ([vd], vc)) = NONE
  | step POP (v, ([], vc)) = NONE
  | step STORE (v, ([], vc)) = NONE
  | step STORE (v, ([vd], vc)) = NONE
  | step CALL (v, ([], vc)) = NONE
  | step RETURN (v, ([], vc)) = NONE
  | step HALT uv = NONE;

fun exec prog n (pc, (st, (m, (f, rs)))) pcs =
  (if equal_nata n zero_nata then NONE
    else (case prog pc of NONE => NONE
           | SOME instr =>
             (if equal_instra instr HALT
               then SOME ((pc, (st, (m, (f, rs)))), pc :: pcs)
               else (case step instr (pc, (st, (m, (f, rs)))) of NONE => NONE
                      | SOME s =>
                        exec prog (minus_nat n one_nata) s (pc :: pcs)))));

fun imp_fora i u f s =
  (if less_eq_nat u i then (fn () => s)
    else (fn () => let
                     val x = f i s ();
                   in
                     imp_fora (plus_nat i one_nata) u f x ()
                   end));

fun mtx_set A_ m mtx e v =
  upd A_ (plus_nat (times_nat (fst e) m) (snd e)) v mtx;

fun mtx_get A_ m mtx e = ntha A_ mtx (plus_nat (times_nat (fst e) m) (snd e));

fun min A_ a b = (if less_eq A_ a b then a else b);

fun fw_upd_impl (A1_, A2_) n =
  (fn ai => fn bib => fn bia => fn bi => fn () =>
    let
      val x = mtx_get A2_ (suc n) ai (bia, bi) ();
      val xa = mtx_get A2_ (suc n) ai (bia, bib) ();
      val xb = mtx_get A2_ (suc n) ai (bib, bi) ();
    in
      mtx_set A2_ (suc n) ai (bia, bi)
        (min ((ord_preorder o preorder_order o order_linorder o
                linorder_linordered_ab_semigroup_add o
                linordered_ab_semigroup_add_linordered_ab_monoid_add)
               A1_)
          x (plus ((plus_semigroup_add o semigroup_add_monoid_add o
                     monoid_add_comm_monoid_add o
                     comm_monoid_add_ordered_comm_monoid_add o
                     ordered_comm_monoid_add_linordered_ab_monoid_add)
                    A1_)
              xa xb))
        ()
    end);

fun fwi_impl (A1_, A2_) n =
  (fn ai => fn bi =>
    imp_fora zero_nata (plus_nat n one_nata)
      (fn xa =>
        imp_fora zero_nata (plus_nat n one_nata)
          (fn xc => fn sigma => fw_upd_impl (A1_, A2_) n sigma bi xa xc))
      ai);

fun the (SOME x2) = x2;

fun gen_pick it s =
  the (it s (fn a => (case a of NONE => true | SOME _ => false))
         (fn x => fn _ => SOME x)
        NONE);

fun of_phantom (Phantom x) = x;

fun size_list x = gen_length zero_nata x;

fun card (A1_, A2_) (Coset xs) =
  minus_nat (of_phantom (card_UNIV A1_)) (size_list (remdups A2_ xs))
  | card (A1_, A2_) (Set xs) = size_list (remdups A2_ xs);

fun ht_new_sz (A1_, A2_) B_ n =
  let
    val l = replicate n [];
  in
    (fn () => let
                val a = (fn () => Array.fromList l) ();
              in
                HashTable (a, zero_nata)
              end)
  end;

fun ht_new (A1_, A2_) B_ = ht_new_sz (A1_, A2_) B_ (def_hashmap_size A1_ Type);

fun sgn_integer k =
  (if ((k : IntInf.int) = (0 : IntInf.int)) then (0 : IntInf.int)
    else (if IntInf.< (k, (0 : IntInf.int)) then (~1 : IntInf.int)
           else (1 : IntInf.int)));

fun apsnd f (x, y) = (x, f y);

fun divmod_integer k l =
  (if ((k : IntInf.int) = (0 : IntInf.int))
    then ((0 : IntInf.int), (0 : IntInf.int))
    else (if ((l : IntInf.int) = (0 : IntInf.int)) then ((0 : IntInf.int), k)
           else (apsnd o (fn a => fn b => IntInf.* (a, b)) o sgn_integer) l
                  (if (((sgn_integer k) : IntInf.int) = (sgn_integer l))
                    then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                    else let
                           val (r, s) =
                             IntInf.divMod (IntInf.abs k, IntInf.abs l);
                         in
                           (if ((s : IntInf.int) = (0 : IntInf.int))
                             then (IntInf.~ r, (0 : IntInf.int))
                             else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                    IntInf.- (IntInf.abs l, s)))
                         end)));

fun modulo_integer k l = snd (divmod_integer k l);

fun modulo_nat m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

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
  (fn () =>
    let
      val m = len (heap_list (heap_prod A3_ B_)) (the_array ht) ();
    in
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
      end
        ()
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
               equal_nata (plus_nat (size_list xsa) (size_list ysa)) n andalso
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
               equal_nata (plus_nat (size_list xsa) (size_list ysa)) n andalso
                 (list_all (fn x => not (membera A2_ ysa x)) xsa andalso
                   list_all (fn y => not (membera A2_ xsa y)) ysa)
             end)
    end;

fun ht_insls (A1_, A2_, A3_) B_ [] ht = (fn () => ht)
  | ht_insls (A1_, A2_, A3_) B_ ((k, v) :: l) ht =
    (fn () => let
                val x = ht_upd (A1_, A2_, A3_) B_ k v ht ();
              in
                ht_insls (A1_, A2_, A3_) B_ l x ()
              end);

fun ht_copy (A1_, A2_, A3_) B_ n src dst =
  (if equal_nata n zero_nata then (fn () => dst)
    else (fn () =>
           let
             val l =
               ntha (heap_list (heap_prod A3_ B_)) (the_array src)
                 (minus_nat n one_nata) ();
             val x = ht_insls (A1_, A2_, A3_) B_ l dst ();
           in
             ht_copy (A1_, A2_, A3_) B_ (minus_nat n one_nata) src x ()
           end));

fun app f a = f a;

fun hm_isEmpty ht = (fn () => (equal_nata (the_size ht) zero_nata));

fun array_get a =
  (fn a => FArray.IsabelleMapping.array_get a o IntInf.toInt) a o
    integer_of_nat;

fun array_set a =
  (fn a => FArray.IsabelleMapping.array_set a o IntInf.toInt) a o
    integer_of_nat;

fun new_array v =
  (fn a => FArray.IsabelleMapping.new_array a o IntInf.toInt) v o
    integer_of_nat;

fun ls_delete A_ k [] = ([], false)
  | ls_delete A_ k ((l, w) :: ls) =
    (if eq A_ k l then (ls, true) else let
 val r = ls_delete A_ k ls;
                                       in
 ((l, w) :: fst r, snd r)
                                       end);

fun ht_delete (A1_, A2_, A3_) B_ k ht =
  (fn () =>
    let
      val m = len (heap_list (heap_prod A3_ B_)) (the_array ht) ();
    in
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
      end
        ()
    end);

fun ls_lookup A_ x [] = NONE
  | ls_lookup A_ x ((k, v) :: l) =
    (if eq A_ x k then SOME v else ls_lookup A_ x l);

fun ht_lookup (A1_, A2_, A3_) B_ x ht =
  (fn () =>
    let
      val m = len (heap_list (heap_prod A3_ B_)) (the_array ht) ();
    in
      let
        val i = bounded_hashcode_nat A2_ m x;
      in
        (fn f_ => fn () => f_
          ((ntha (heap_list (heap_prod A3_ B_)) (the_array ht) i) ()) ())
          (fn l => (fn () => (ls_lookup A1_ x l)))
      end
        ()
    end);

fun ht_rehash (A1_, A2_, A3_) B_ ht =
  (fn () =>
    let
      val n = len (heap_list (heap_prod A3_ B_)) (the_array ht) ();
      val x =
        ht_new_sz (A2_, A3_) B_ (times_nat (nat_of_integer (2 : IntInf.int)) n)
          ();
    in
      ht_copy (A1_, A2_, A3_) B_ n ht x ()
    end);

val load_factor : nat = nat_of_integer (75 : IntInf.int);

fun ht_update (A1_, A2_, A3_) B_ k v ht =
  (fn () =>
    let
      val m = len (heap_list (heap_prod A3_ B_)) (the_array ht) ();
      val x =
        (if less_eq_nat (times_nat m load_factor)
              (times_nat (the_size ht) (nat_of_integer (100 : IntInf.int)))
          then ht_rehash (A1_, A2_, A3_) B_ ht else (fn () => ht))
          ();
    in
      ht_upd (A1_, A2_, A3_) B_ k v x ()
    end);

fun op_list_tl x = tl x;

val bot_set : 'a set = Set [];

fun set_act A_ (In x1) = insert A_ x1 bot_set
  | set_act A_ (Out x2) = insert A_ x2 bot_set
  | set_act A_ (Sil x3) = insert A_ x3 bot_set;

fun array_grow a =
  (fn a => FArray.IsabelleMapping.array_grow a o IntInf.toInt) a o
    integer_of_nat;

fun hm_it_adjust (A1_, A2_) B_ v ht =
  (if equal_nata v zero_nata then (fn () => zero_nata)
    else (fn () =>
           let
             val a =
               ntha (heap_list (heap_prod A2_ B_)) (the_array ht)
                 (suc (minus_nat v one_nata)) ();
           in
             (case a
               of [] =>
                 hm_it_adjust (A1_, A2_) B_
                   (minus_nat (suc (minus_nat v one_nata)) one_nata) ht
               | _ :: _ => (fn () => (suc (minus_nat v one_nata))))
               ()
           end));

fun op_list_rev x = rev x;

fun all_interval_nat p i j =
  less_eq_nat j i orelse p i andalso all_interval_nat p (suc i) j;

fun pred_act A_ = (fn p => fn x => ball (set_act A_ x) p);

fun imp_for i u c f s =
  (if less_eq_nat u i then (fn () => s)
    else (fn () =>
           let
             val ctn = c s ();
           in
             (if ctn
               then (fn f_ => fn () => f_ ((f i s) ()) ())
                      (imp_for (plus_nat i one_nata) u c f)
               else (fn () => s))
               ()
           end));

fun cODE_ABORT _ = raise Fail "Sepref_Misc.CODE_ABORT";

fun array_copy A_ a =
  (fn () =>
    let
      val l = len A_ a ();
    in
      (if equal_nata l zero_nata then (fn () => Array.fromList [])
        else (fn f_ => fn () => f_ ((ntha A_ a zero_nata) ()) ())
               (fn s =>
                 (fn f_ => fn () => f_ ((new A_ l s) ()) ())
                   (fn aa =>
                     (fn f_ => fn () => f_ ((blit A_ a zero_nata aa zero_nata l)
                       ()) ())
                       (fn _ => (fn () => aa)))))
        ()
    end);

fun whilea b c s = (if b s then whilea b c (c s) else s);

fun array_length x =
  (nat_of_integer o IntInf.fromInt o FArray.IsabelleMapping.array_length) x;

fun array_shrink a =
  (fn a => FArray.IsabelleMapping.array_shrink a o IntInf.toInt) a o
    integer_of_nat;

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
      (if less_eq_nat (times_nat (nat_of_integer (128 : IntInf.int)) n)
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
  (fn () =>
    let
      val n = len (heap_list (heap_prod A2_ B_)) (the_array ht) ();
    in
      (if equal_nata n zero_nata then (raise Fail "Map is empty!")
        else (fn f_ => fn () => f_
               ((hm_it_adjust (A1_, A2_) B_ (minus_nat n one_nata) ht) ()) ())
               (fn i =>
                 (fn f_ => fn () => f_
                   ((ntha (heap_list (heap_prod A2_ B_)) (the_array ht) i) ())
                   ())
                   (fn a =>
                     (case a of [] => (raise Fail "Map is empty!")
                       | x :: _ => (fn () => (fst x))))))
        ()
    end);

fun heap_WHILET b f s =
  (fn () =>
    let
      val bv = b s ();
    in
      (if bv then (fn f_ => fn () => f_ ((f s) ()) ()) (heap_WHILET b f)
        else (fn () => s))
        ()
    end);

fun imp_nfoldli (x :: ls) c f s =
  (fn () =>
    let
      val b = c s ();
    in
      (if b then (fn f_ => fn () => f_ ((f x s) ()) ()) (imp_nfoldli ls c f)
        else (fn () => s))
        ()
    end)
  | imp_nfoldli [] c f s = (fn () => s);

fun lso_bex_impl pi li =
  imp_nfoldli li (fn sigma => (fn () => (not sigma))) (fn xa => fn _ => pi xa)
    false;

fun op_list_is_empty x = null x;

fun op_list_prepend x = (fn a => x :: a);

fun hms_extract lookup delete k m =
  (fn () =>
    let
      val a = lookup k m ();
    in
      (case a of NONE => (fn () => (NONE, m))
        | SOME v =>
          (fn f_ => fn () => f_ ((delete k m) ()) ())
            (fn ma => (fn () => (SOME v, ma))))
        ()
    end);

fun pw_impl A_ (B1_, B2_, B3_) keyi copyi lei a_0i fi succsi emptyi =
  (fn () =>
    let
      val x = a_0i ();
      val xa = emptyi x ();
      val xaa = a_0i ();
      val xab = fi xaa ();
      val a =
        (if not xa andalso xab
          then (fn f_ => fn () => f_ ((ht_new (B2_, B3_) (heap_list A_)) ()) ())
                 (fn x_b => (fn () => (true, x_b)))
          else (fn f_ => fn () => f_ (a_0i ()) ())
                 (fn xb =>
                   (fn f_ => fn () => f_ ((emptyi xb) ()) ())
                     (fn x_a =>
                       (if x_a
                         then (fn f_ => fn () => f_
                                ((ht_new (B2_, B3_) (heap_list A_)) ()) ())
                                (fn x_c => (fn () => (false, x_c)))
                         else (fn f_ => fn () => f_ (a_0i ()) ())
                                (fn xc =>
                                  (fn f_ => fn () => f_ ((keyi xc) ()) ())
                                    (fn xd =>
                                      (fn f_ => fn () => f_ (a_0i ()) ())
(fn xac =>
  (fn f_ => fn () => f_ ((ht_new (B2_, B3_) (heap_list A_)) ()) ())
    (fn xba =>
      (fn f_ => fn () => f_
        ((ht_update (B1_, B2_, B3_) (heap_list A_) xd [xac] xba) ()) ())
        (fn xe =>
          (fn f_ => fn () => f_ (a_0i ()) ())
            (fn xad =>
              let
                val (a1, a2) = (xe, op_list_prepend xad []);
              in
                (fn f_ => fn () => f_
                  ((heap_WHILET
                     (fn (_, (a1b, a2b)) =>
                       (fn () => (not a2b andalso not (op_list_is_empty a1b))))
                     (fn (a1a, (a1b, a2b)) =>
                       let
                         val (a1c, a2c) =
                           (case a1b
                             of [] => cODE_ABORT (fn _ => (hd a1b, tl a1b))
                             | a :: b => (a, b));
                       in
                         (fn f_ => fn () => f_ ((emptyi a1c) ()) ())
                           (fn x_e =>
                             (if x_e then (fn () => (a1a, (a2c, a2b)))
                               else (fn f_ => fn () => f_ ((succsi a1c) ()) ())
                                      (fn x_f =>
imp_nfoldli x_f (fn (_, (_, b)) => (fn () => (not b)))
  (fn xj => fn (a1d, (a1e, _)) =>
    (fn f_ => fn () => f_ ((emptyi xj) ()) ())
      (fn x_i =>
        (if x_i then (fn () => (a1d, (a1e, false)))
          else (fn f_ => fn () => f_ ((fi xj) ()) ())
                 (fn x_j =>
                   (if x_j then (fn () => (a1d, (a1e, true)))
                     else (fn f_ => fn () => f_ ((keyi xj) ()) ())
                            (fn x_k =>
                              (fn f_ => fn () => f_
                                ((hms_extract
                                   (ht_lookup (B1_, B2_, B3_) (heap_list A_))
                                   (ht_delete (B1_, B2_, B3_) (heap_list A_))
                                   x_k a1d)
                                ()) ())
                                (fn a =>
                                  (case a
                                    of (NONE, a2f) =>
                                      (fn f_ => fn () => f_ ((copyi xj) ()) ())
(fn xf =>
  (fn f_ => fn () => f_ ((ht_update (B1_, B2_, B3_) (heap_list A_) x_k [xf] a2f)
    ()) ())
    (fn x_m => (fn () => (x_m, (op_list_prepend xj a1e, false)))))
                                    | (SOME x_m, a2f) =>
                                      (fn f_ => fn () => f_
((lso_bex_impl (lei xj) x_m) ()) ())
(fn x_n =>
  (if x_n
    then (fn f_ => fn () => f_
           ((ht_update (B1_, B2_, B3_) (heap_list A_) x_k x_m a2f) ()) ())
           (fn x_o => (fn () => (x_o, (a1e, false))))
    else (fn f_ => fn () => f_ ((copyi xj) ()) ())
           (fn xf =>
             (fn f_ => fn () => f_
               ((ht_update (B1_, B2_, B3_) (heap_list A_) x_k (xf :: x_m) a2f)
               ()) ())
               (fn x_o =>
                 (fn () => (x_o, (op_list_prepend xj a1e, false)))))))))))))))
  (a1a, (a2c, false)))))
                       end)
                     (a1, (a2, false)))
                  ()) ())
                  (fn (a1a, (_, a2b)) => (fn () => (a2b, a1a)))
              end))))))))))
          ();
    in
      let
        val (a1, _) = a;
      in
        (fn () => a1)
      end
        ()
    end);

fun as_push s x =
  let
    val a = s;
    val (aa, n) = a;
    val ab =
      (if equal_nata n (array_length aa)
        then array_grow aa
               (max ord_nat (nat_of_integer (4 : IntInf.int))
                 (times_nat (nat_of_integer (2 : IntInf.int)) n))
               x
        else aa);
    val ac = array_set ab n x;
  in
    (ac, plus_nat n one_nata)
  end;

fun as_take m s = let
                    val a = s;
                    val (aa, n) = a;
                  in
                    (if less_nat m n then as_shrink (aa, m) else (aa, n))
                  end;

fun rev_append [] ac = ac
  | rev_append (x :: xs) ac = rev_append xs (x :: ac);

fun ran_of_map_impl (A1_, A2_, A3_) B_ =
  (fn xi => fn () =>
    let
      val a =
        heap_WHILET
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
                  (fn (a1a, b) =>
                    (fn () => (op_list_prepend (the a1a) a1, b)))))
          ([], xi) ();
    in
      let
        val (a1, _) = a;
      in
        (fn () => a1)
      end
        ()
    end);

fun map_option f NONE = NONE
  | map_option f (SOME x2) = SOME (f x2);

fun sup_set A_ (Coset xs) a = Coset (filtera (fn x => not (member A_ x a)) xs)
  | sup_set A_ (Set xs) a = fold (insert A_) xs a;

fun stripf (INSTR instr) = instr
  | stripf (CEXP v) = SETF false;

fun stript (INSTR instr) = instr
  | stript (CEXP v) = SETF true;

fun idx_iteratei_aux get sz i l c f sigma =
  (if equal_nata i zero_nata orelse not (c sigma) then sigma
    else idx_iteratei_aux get sz (minus_nat i one_nata) l c f
           (f (get l (minus_nat sz i)) sigma));

fun idx_iteratei get sz l c f sigma =
  idx_iteratei_aux get (sz l) (sz l) l c f sigma;

fun as_empty B_ uu = (FArray.IsabelleMapping.array_of_list [], zero B_);

fun leadsto_impl_0 D_ (E1_, E2_, E3_) Type Type Type copyia succsia leia keyia x
  = let
      val (a1, (a1a, a2a)) = x;
    in
      (fn () =>
        let
          val xa = keyia a2a ();
          val xaa =
            hms_extract (ht_lookup (E1_, E2_, E3_) (heap_list D_))
              (ht_delete (E1_, E2_, E3_) (heap_list D_)) xa a1a ();
          val a =
            (case xaa of (NONE, a2b) => (fn () => (a2b, false))
              | (SOME x_c, a2b) =>
                (fn f_ => fn () => f_
                  ((imp_nfoldli x_c (fn sigma => (fn () => (not sigma)))
                     (fn xe => fn sigma =>
                       (fn f_ => fn () => f_ ((leia xe a2a) ()) ())
                         (fn x_f => (fn () => (x_f orelse sigma))))
                     false)
                  ()) ())
                  (fn x_d =>
                    (fn f_ => fn () => f_
                      ((ht_update (E1_, E2_, E3_) (heap_list D_) xa x_c a2b) ())
                      ())
                      (fn x_e => (fn () => (x_e, x_d)))))
              ();
        in
          (case a of (a1b, true) => (fn () => (a1, (a1b, true)))
            | (a1b, false) =>
              (fn f_ => fn () => f_ ((keyia a2a) ()) ())
                (fn xb =>
                  (fn f_ => fn () => f_
                    ((hms_extract (ht_lookup (E1_, E2_, E3_) (heap_list D_))
                       (ht_delete (E1_, E2_, E3_) (heap_list D_)) xb a1)
                    ()) ())
                    (fn xab =>
                      (fn f_ => fn () => f_
                        ((case xab of (NONE, a2c) => (fn () => (a2c, false))
                           | (SOME x_e, a2c) =>
                             (fn f_ => fn () => f_
                               ((lso_bex_impl (leia a2a) x_e) ()) ())
                               (fn x_f =>
                                 (fn f_ => fn () => f_
                                   ((ht_update (E1_, E2_, E3_) (heap_list D_) xb
                                      x_e a2c)
                                   ()) ())
                                   (fn x_g => (fn () => (x_g, x_f)))))
                        ()) ())
                        (fn aa =>
                          (case aa
                            of (a1c, true) => (fn () => (a1c, (a1b, false)))
                            | (a1c, false) =>
                              (fn f_ => fn () => f_ ((copyia a2a) ()) ())
                                (fn xc =>
                                  (fn f_ => fn () => f_ ((keyia xc) ()) ())
                                    (fn xd =>
                                      (fn f_ => fn () => f_
((hms_extract (ht_lookup (E1_, E2_, E3_) (heap_list D_))
   (ht_delete (E1_, E2_, E3_) (heap_list D_)) xd a1b)
()) ())
(fn xac =>
  (fn f_ => fn () => f_
    ((case xac
       of (NONE, a2d) =>
         (fn f_ => fn () => f_ ((copyia a2a) ()) ())
           (fn xad =>
             (fn f_ => fn () => f_
               ((ht_update (E1_, E2_, E3_) (heap_list D_) xd
                  (op_list_prepend xad []) a2d)
               ()) ())
               (fn x_h => (fn () => (NONE, x_h))))
       | (SOME x_g, a2d) =>
         (fn f_ => fn () => f_ ((copyia a2a) ()) ())
           (fn xad =>
             (fn f_ => fn () => f_
               ((ht_update (E1_, E2_, E3_) (heap_list D_) xd
                  (op_list_prepend xad x_g) a2d)
               ()) ())
               (fn x_i => (fn () => (NONE, x_i)))))
    ()) ())
    (fn (_, a2d) =>
      (fn f_ => fn () => f_ ((succsia a2a) ()) ())
        (fn xe =>
          (fn f_ => fn () => f_
            ((imp_nfoldli xe (fn (_, (_, b)) => (fn () => (not b)))
               (fn xi => fn (a1e, (a1f, _)) =>
                 leadsto_impl_0 D_ (E1_, E2_, E3_) Type Type Type copyia succsia
                   leia keyia (a1e, (a1f, xi)))
               (a1c, (a2d, false)))
            ()) ())
            (fn (a1e, (a1f, a2f)) =>
              (fn f_ => fn () => f_ ((copyia a2a) ()) ())
                (fn xf =>
                  (fn f_ => fn () => f_ ((keyia xf) ()) ())
                    (fn xg =>
                      (fn f_ => fn () => f_
                        ((hms_extract (ht_lookup (E1_, E2_, E3_) (heap_list D_))
                           (ht_delete (E1_, E2_, E3_) (heap_list D_)) xg a1f)
                        ()) ())
                        (fn xad =>
                          (fn f_ => fn () => f_
                            ((case xad
                               of (NONE, a2g) =>
                                 (fn f_ => fn () => f_
                                   ((ht_update (E1_, E2_, E3_) (heap_list D_) xg
                                      [] a2g)
                                   ()) ())
                                   (fn x_k => (fn () => (NONE, x_k)))
                               | (SOME x_j, a2g) =>
                                 (fn f_ => fn () => f_
                                   ((ht_update (E1_, E2_, E3_) (heap_list D_) xg
                                      (if op_list_is_empty x_j then []
else op_list_tl x_j)
                                      a2g)
                                   ()) ())
                                   (fn x_l => (fn () => (NONE, x_l))))
                            ()) ())
                            (fn (_, a2g) =>
                              (fn f_ => fn () => f_ ((copyia a2a) ()) ())
                                (fn xh =>
                                  (fn f_ => fn () => f_ ((keyia xh) ()) ())
                                    (fn xi =>
                                      (fn f_ => fn () => f_
((hms_extract (ht_lookup (E1_, E2_, E3_) (heap_list D_))
   (ht_delete (E1_, E2_, E3_) (heap_list D_)) xi a1e)
()) ())
(fn xae =>
  (fn f_ => fn () => f_
    ((case xae
       of (NONE, a2h) =>
         (fn f_ => fn () => f_ ((copyia a2a) ()) ())
           (fn xaf =>
             (fn f_ => fn () => f_
               ((ht_update (E1_, E2_, E3_) (heap_list D_) xi [xaf] a2h) ()) ())
               (fn x_m => (fn () => (NONE, x_m))))
       | (SOME x_l, a2h) =>
         (fn f_ => fn () => f_ ((copyia a2a) ()) ())
           (fn xaf =>
             (fn f_ => fn () => f_
               ((ht_update (E1_, E2_, E3_) (heap_list D_) xi (xaf :: x_l) a2h)
               ()) ())
               (fn x_n => (fn () => (NONE, x_n)))))
    ()) ())
    (fn (_, a2h) => (fn () => (a2h, (a2g, a2f))))))))))))))))))))))
            ()
        end)
    end;

fun leadsto_impl D_ (E1_, E2_, E3_) Type Type Type copyia succsia a_0ia leia
  keyia succs1i emptyi pi qi =
  (fn () =>
    let
      val x = a_0ia ();
      val xa = emptyi x ();
      val _ = a_0ia ();
      val a =
        (if not xa andalso false
          then (fn f_ => fn () => f_ ((ht_new (E2_, E3_) (heap_list D_)) ()) ())
                 (fn x_b => (fn () => (true, x_b)))
          else (fn f_ => fn () => f_ (a_0ia ()) ())
                 (fn xb =>
                   (fn f_ => fn () => f_ ((emptyi xb) ()) ())
                     (fn x_a =>
                       (if x_a
                         then (fn f_ => fn () => f_
                                ((ht_new (E2_, E3_) (heap_list D_)) ()) ())
                                (fn x_c => (fn () => (false, x_c)))
                         else (fn f_ => fn () => f_ (a_0ia ()) ())
                                (fn xc =>
                                  (fn f_ => fn () => f_ ((keyia xc) ()) ())
                                    (fn xd =>
                                      (fn f_ => fn () => f_ (a_0ia ()) ())
(fn xaa =>
  (fn f_ => fn () => f_ ((ht_new (E2_, E3_) (heap_list D_)) ()) ())
    (fn xba =>
      (fn f_ => fn () => f_
        ((ht_update (E1_, E2_, E3_) (heap_list D_) xd [xaa] xba) ()) ())
        (fn xe =>
          (fn f_ => fn () => f_ (a_0ia ()) ())
            (fn xab =>
              (fn f_ => fn () => f_
                ((heap_WHILET
                   (fn (_, (a1b, a2b)) =>
                     (fn () => (not a2b andalso not (op_list_is_empty a1b))))
                   (fn (a1a, (a1b, a2b)) =>
                     let
                       val (a1c, a2c) =
                         (case a1b
                           of [] => cODE_ABORT (fn _ => (hd a1b, tl a1b))
                           | a :: b => (a, b));
                     in
                       (fn f_ => fn () => f_ ((emptyi a1c) ()) ())
                         (fn x_e =>
                           (if x_e then (fn () => (a1a, (a2c, a2b)))
                             else (fn f_ => fn () => f_ ((succs1i a1c) ()) ())
                                    (fn x_f =>
                                      imp_nfoldli x_f
(fn (_, (_, b)) => (fn () => (not b)))
(fn xj => fn (a1d, (a1e, _)) =>
  (fn f_ => fn () => f_ ((emptyi xj) ()) ())
    (fn x_i =>
      (if x_i then (fn () => (a1d, (a1e, false)))
        else (fn f_ => fn () => f_ ((keyia xj) ()) ())
               (fn x_k =>
                 (fn f_ => fn () => f_
                   ((hms_extract (ht_lookup (E1_, E2_, E3_) (heap_list D_))
                      (ht_delete (E1_, E2_, E3_) (heap_list D_)) x_k a1d)
                   ()) ())
                   (fn a =>
                     (case a
                       of (NONE, a2f) =>
                         (fn f_ => fn () => f_ ((copyia xj) ()) ())
                           (fn xf =>
                             (fn f_ => fn () => f_
                               ((ht_update (E1_, E2_, E3_) (heap_list D_) x_k
                                  [xf] a2f)
                               ()) ())
                               (fn x_m =>
                                 (fn () =>
                                   (x_m, (op_list_prepend xj a1e, false)))))
                       | (SOME x_m, a2f) =>
                         (fn f_ => fn () => f_ ((lso_bex_impl (leia xj) x_m) ())
                           ())
                           (fn x_n =>
                             (if x_n
                               then (fn f_ => fn () => f_
                                      ((ht_update (E1_, E2_, E3_) (heap_list D_)
 x_k x_m a2f)
                                      ()) ())
                                      (fn x_o => (fn () => (x_o, (a1e, false))))
                               else (fn f_ => fn () => f_ ((copyia xj) ()) ())
                                      (fn xf =>
(fn f_ => fn () => f_
  ((ht_update (E1_, E2_, E3_) (heap_list D_) x_k (xf :: x_m) a2f) ()) ())
  (fn x_o => (fn () => (x_o, (op_list_prepend xj a1e, false)))))))))))))
(a1a, (a2c, false)))))
                     end)
                   (xe, (op_list_prepend xab [], false)))
                ()) ())
                (fn (a1a, (_, a2b)) => (fn () => (a2b, a1a)))))))))))))
          ();
    in
      let
        val (_, a2) = a;
      in
        (fn f_ => fn () => f_
          ((ran_of_map_impl (E1_, E2_, E3_) (heap_list D_) a2) ()) ())
          (fn x_a =>
            (fn f_ => fn () => f_ ((ht_new (E2_, E3_) (heap_list D_)) ()) ())
              (fn xb =>
                (fn f_ => fn () => f_
                  ((imp_nfoldli x_a (fn (a1a, _) => (fn () => (not a1a)))
                     (fn xd => fn (_, a2a) =>
                       imp_nfoldli xd (fn (a1b, _) => (fn () => (not a1b)))
                         (fn xg => fn (_, a2b) =>
                           (fn f_ => fn () => f_ ((pi xg) ()) ())
                             (fn xc =>
                               (fn f_ => fn () => f_ ((qi xg) ()) ())
                                 (fn xaa =>
                                   (if xc andalso xaa
                                     then (fn f_ => fn () => f_
    ((ht_new (E2_, E3_) (heap_list D_)) ()) ())
    (fn xe =>
      (fn f_ => fn () => f_
        ((leadsto_impl_0 D_ (E1_, E2_, E3_) Type Type Type copyia succsia leia
           keyia (a2b, (xe, xg)))
        ()) ())
        (fn (a1, (_, a2aa)) => (fn () => (a2aa, a1))))
                                     else (fn () => (false, a2b))))))
                         (false, a2a))
                     (false, xb))
                  ()) ())
                  (fn (a1a, _) => (fn () => a1a))))
      end
        ()
    end);

fun bounded_int bounds s =
  equal_nata (size_list s) (size_list bounds) andalso
    all_interval_nat
      (fn i =>
        less_int (fst (nth bounds i)) (nth s i) andalso
          less_int (nth s i) (snd (nth bounds i)))
      zero_nata (size_list s);

fun as_length x = snd x;

fun last_seg_tr A_ s =
  let
    val (a, (aa, (_, _))) = s;
    val (_, bc) =
      whilea
        (fn (xe, _) =>
          less_nat xe
            (if equal_nata
                  (plus_nat (minus_nat (as_length aa) one_nata) one_nata)
                  (as_length aa)
              then as_length a
              else as_get aa
                     (plus_nat (minus_nat (as_length aa) one_nata) one_nata)))
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
        (if insert then plus_nat n one_nata else n))
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
  less_eq_nat (times_nat (array_length a) load_factora)
    (times_nat n (nat_of_integer (100 : IntInf.int)));

fun hm_grow (HashMap (a, n)) =
  plus_nat (times_nat (nat_of_integer (2 : IntInf.int)) (array_length a))
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
            (fn (xf, _) =>
              less_nat xf
                (if equal_nata (plus_nat x one_nata) (as_length aa)
                  then as_length a else as_get aa (plus_nat x one_nata)))
            (fn (ac, bc) =>
              (suc ac,
                ahm_update (eq A1_) (bounded_hashcode_nat A2_) (as_get a ac)
                  (uminus_inta (Int_of_integer (1 : IntInf.int))) bc))
            (as_get aa x, ab);
      in
        bc
      end;
    val xb = as_take (as_top aa) a;
    val xc = as_pop aa;
  in
    (xb, (xc, (xa, bb)))
  end;

fun glist_delete_aux eq x [] asa = asa
  | glist_delete_aux eq x (y :: ys) asa =
    (if eq x y then rev_append asa ys else glist_delete_aux eq x ys (y :: asa));

fun glist_delete eq x l = glist_delete_aux eq x l [];

fun is_Nil a = (case a of [] => true | _ :: _ => false);

fun find_max_nat n uu =
  (if equal_nata n zero_nata then zero_nata
    else (if uu (minus_nat n one_nata) then minus_nat n one_nata
           else find_max_nat (minus_nat n one_nata) uu));

fun amtx_copy A_ = array_copy A_;

fun amtx_dflt A_ n m v = make A_ (times_nat n m) (fn _ => v);

fun norm_lower A_ e t = (if dbm_lt A_ e (Lt t) then Lt t else e);

fun norm_upper A_ e t = (if dbm_lt A_ (Le t) e then INF else e);

fun gi_E (Gen_g_impl_ext (gi_V, gi_E, gi_V0, more)) = gi_E;

fun more (Gen_g_impl_ext (gi_V, gi_E, gi_V0, more)) = more;

fun as_is_empty s = equal_nata (snd s) zero_nata;

fun minus_set A_ a (Coset xs) = Set (filtera (fn x => member A_ x a) xs)
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
    val xa = as_take (plus_nat x one_nata) aa;
  in
    (a, (xa, (ab, bb)))
  end;

fun as_singleton B_ x = (FArray.IsabelleMapping.array_of_list [x], one B_);

fun new_hashmap_with size = HashMap (new_array [] size, zero_nata);

fun ahm_empty def_size = new_hashmap_with def_size;

fun push_code (A1_, A2_) g_impl =
  (fn x => fn (xa, (xb, (xc, xd))) =>
    let
      val _ = Gabow_Skeleton_Statistics.newnode ();
      val xf = as_length xa;
      val xg = as_push xa x;
      val xh = as_push xb xf;
      val xi =
        ahm_update (eq A1_) (bounded_hashcode_nat A2_) x (int_of_nat xf) xc;
      val xj =
        (if is_Nil (gi_E g_impl x) then xd else as_push xd (xf, gi_E g_impl x));
    in
      (xg, (xh, (xi, xj)))
    end);

fun compute_SCC_tr (A1_, A2_) g =
  let
    val _ = Gabow_Skeleton_Statistics.start ();
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
                       (fn (_, xh) =>
                         not (as_is_empty let
    val (xi, (_, (_, _))) = xh;
  in
    xi
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
                                 val (_, (_, (xn, _))) = bb;
                               in
                                 xn
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
            val (_, (_, (xn, _))) = bb;
          in
            xn
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
    val _ = Gabow_Skeleton_Statistics.stop ();
  in
    aa
  end;

fun constraint_clk (LTa (c, uu)) = c
  | constraint_clk (LEa (c, uv)) = c
  | constraint_clk (EQa (c, uw)) = c
  | constraint_clk (GE (c, ux)) = c
  | constraint_clk (GT (c, uy)) = c;

fun bounded A_ bounds s =
  equal_nata (size_list s) (size_list bounds) andalso
    all_interval_nat
      (fn i =>
        less A_ (fst (nth bounds i)) (nth s i) andalso
          less A_ (nth s i) (snd (nth bounds i)))
      zero_nata (size_list s);

fun stripfp p = map_option stripf o p;

fun constraint_pair (LTa (x, m)) = (x, m)
  | constraint_pair (LEa (x, m)) = (x, m)
  | constraint_pair (EQa (x, m)) = (x, m)
  | constraint_pair (GE (x, m)) = (x, m)
  | constraint_pair (GT (x, m)) = (x, m);

fun is_instr (INSTR uu) = true
  | is_instr (CEXP v) = false;

fun maxa A_ (Set (x :: xs)) =
  fold (max ((ord_preorder o preorder_order o order_linorder) A_)) xs x;

fun mina A_ (Set (x :: xs)) =
  fold (min ((ord_preorder o preorder_order o order_linorder) A_)) xs x;

fun check_conj_blocka A_ prog pc =
  (if less_eq_nat (size_list prog) pc then NONE
    else (if equal_optiona (equal_instrc A_) (nth prog pc) (SOME (INSTR HALT))
           then SOME pc
           else (if equal_optiona (equal_instrc A_) (nth prog pc)
                      (SOME (INSTR COPY)) andalso
                      ((case nth prog (plus_nat pc one_nata) of NONE => false
                         | SOME (INSTR _) => false
                         | SOME (CEXP _) => true) andalso
                        equal_optiona (equal_instrc A_)
                          (nth prog
                            (plus_nat pc (nat_of_integer (2 : IntInf.int))))
                          (SOME (INSTR AND)))
                  then check_conj_blocka A_ prog
                         (plus_nat pc (nat_of_integer (3 : IntInf.int)))
                  else (if equal_optiona (equal_instrc A_) (nth prog pc)
                             (SOME (INSTR COPY)) andalso
                             ((case nth prog
                                      (plus_nat pc
(nat_of_integer (2 : IntInf.int)))
                                of NONE => false | SOME (INSTR _) => false
                                | SOME (CEXP _) => true) andalso
                               (equal_optiona (equal_instrc A_)
                                  (nth prog
                                    (plus_nat pc
                                      (nat_of_integer (3 : IntInf.int))))
                                  (SOME (INSTR AND)) andalso
                                 (case nth prog (plus_nat pc one_nata)
                                   of NONE => false
                                   | SOME (INSTR (JMPZ _)) => true
                                   | SOME (INSTR ADD) => false
                                   | SOME (INSTR NOT) => false
                                   | SOME (INSTR AND) => false
                                   | SOME (INSTR LT) => false
                                   | SOME (INSTR LE) => false
                                   | SOME (INSTR EQ) => false
                                   | SOME (INSTR (PUSH _)) => false
                                   | SOME (INSTR POP) => false
                                   | SOME (INSTR (LID _)) => false
                                   | SOME (INSTR STORE) => false
                                   | SOME (INSTR (STOREI (_, _))) => false
                                   | SOME (INSTR COPY) => false
                                   | SOME (INSTR CALL) => false
                                   | SOME (INSTR RETURN) => false
                                   | SOME (INSTR HALT) => false
                                   | SOME (INSTR (STOREC (_, _))) => false
                                   | SOME (INSTR (SETF _)) => false
                                   | SOME (CEXP _) => false)))
                         then (case (nth prog (plus_nat pc one_nata),
                                      check_conj_blocka A_ prog
(plus_nat pc (nat_of_integer (4 : IntInf.int))))
                                of (NONE, _) => NONE
                                | (SOME (INSTR (JMPZ _)), NONE) => NONE
                                | (SOME (INSTR (JMPZ pcb)), SOME pca) =>
                                  (if equal_nata pcb pca then SOME pcb
                                    else NONE)
                                | (SOME (INSTR ADD), _) => NONE
                                | (SOME (INSTR NOT), _) => NONE
                                | (SOME (INSTR AND), _) => NONE
                                | (SOME (INSTR LT), _) => NONE
                                | (SOME (INSTR LE), _) => NONE
                                | (SOME (INSTR EQ), _) => NONE
                                | (SOME (INSTR (PUSH _)), _) => NONE
                                | (SOME (INSTR POP), _) => NONE
                                | (SOME (INSTR (LID _)), _) => NONE
                                | (SOME (INSTR STORE), _) => NONE
                                | (SOME (INSTR (STOREI (_, _))), _) => NONE
                                | (SOME (INSTR COPY), _) => NONE
                                | (SOME (INSTR CALL), _) => NONE
                                | (SOME (INSTR RETURN), _) => NONE
                                | (SOME (INSTR HALT), _) => NONE
                                | (SOME (INSTR (STOREC (_, _))), _) => NONE
                                | (SOME (INSTR (SETF _)), _) => NONE
                                | (SOME (CEXP _), _) => NONE)
                         else NONE))));

fun check_conj_block p pca pc =
  (case nth p pca of NONE => false | SOME (INSTR _) => false
    | SOME (CEXP _) => true) andalso
    equal_optiona equal_nat
      (check_conj_blocka equal_int p (plus_nat pca one_nata)) (SOME pc) orelse
    (case nth p pca of NONE => false | SOME (INSTR _) => false
      | SOME (CEXP _) => true) andalso
      (equal_optiona (equal_instrc equal_int) (nth p (plus_nat pca one_nata))
         (SOME (INSTR AND)) andalso
        equal_optiona equal_nat
          (check_conj_blocka equal_int p
            (plus_nat pca (nat_of_integer (2 : IntInf.int))))
          (SOME pc));

fun sup_seta A_ (Set xs) = fold (sup_set A_) xs bot_set;

fun steps_approx n prog pc =
  (if equal_nata n zero_nata
    then (if less_nat pc (size_list prog) then insert equal_nat pc bot_set
           else bot_set)
    else (if less_eq_nat (size_list prog) pc then bot_set
           else (case nth prog pc of NONE => insert equal_nat pc bot_set
                  | SOME cmd =>
                    let
                      val succs =
                        (case cmd
                          of INSTR (JMPZ pca) =>
                            insert equal_nat (plus_nat pc one_nata)
                              (insert equal_nat pca bot_set)
                          | INSTR ADD =>
                            insert equal_nat (plus_nat pc one_nata) bot_set
                          | INSTR NOT =>
                            insert equal_nat (plus_nat pc one_nata) bot_set
                          | INSTR AND =>
                            insert equal_nat (plus_nat pc one_nata) bot_set
                          | INSTR LT =>
                            insert equal_nat (plus_nat pc one_nata) bot_set
                          | INSTR LE =>
                            insert equal_nat (plus_nat pc one_nata) bot_set
                          | INSTR EQ =>
                            insert equal_nat (plus_nat pc one_nata) bot_set
                          | INSTR (PUSH _) =>
                            insert equal_nat (plus_nat pc one_nata) bot_set
                          | INSTR POP =>
                            insert equal_nat (plus_nat pc one_nata) bot_set
                          | INSTR (LID _) =>
                            insert equal_nat (plus_nat pc one_nata) bot_set
                          | INSTR STORE =>
                            insert equal_nat (plus_nat pc one_nata) bot_set
                          | INSTR (STOREI (_, _)) =>
                            insert equal_nat (plus_nat pc one_nata) bot_set
                          | INSTR COPY =>
                            insert equal_nat (plus_nat pc one_nata) bot_set
                          | INSTR CALL => Set (upt zero_nata (size_list prog))
                          | INSTR RETURN => Set (upt zero_nata (size_list prog))
                          | INSTR HALT => bot_set
                          | INSTR (STOREC (_, _)) =>
                            insert equal_nat (plus_nat pc one_nata) bot_set
                          | INSTR (SETF _) =>
                            insert equal_nat (plus_nat pc one_nata) bot_set
                          | CEXP _ =>
                            insert equal_nat (plus_nat pc one_nata) bot_set);
                    in
                      sup_set equal_nat (insert equal_nat pc bot_set)
                        (sup_seta equal_nat
                          (image (steps_approx (minus_nat n one_nata) prog)
                            succs))
                    end)));

fun conjunction_check p pc_s n =
  let
    val s = steps_approx n p pc_s;
    val sa =
      filter
        (fn pc =>
          (case nth p pc of NONE => false | SOME (INSTR _) => false
            | SOME (CEXP _) => true))
        s;
  in
    eq_set (card_UNIV_nat, equal_nat) sa bot_set orelse
      check_conj_block p (mina linorder_nat sa) (maxa linorder_nat s)
  end;

fun conjunction_check2 x =
  (fn trans => fn prog => fn max_steps =>
    list_all
      (list_all
        (list_all
          (fn (pc_g, (_, (_, _))) => conjunction_check prog pc_g max_steps)))
      trans)
    x;

fun time_indep_check prog pc n =
  ball (steps_approx n prog pc)
    (fn pca =>
      (if less_nat pca (size_list prog)
        then (case nth prog pca of NONE => true | SOME a => is_instr a)
        else true));

fun time_indep_check2 x =
  (fn trans => fn prog => fn max_steps =>
    list_all
      (list_all
        (list_all
          (fn (_, (_, (pc_u, _))) => time_indep_check prog pc_u max_steps)))
      trans)
    x;

fun time_indep_check1 x =
  (fn pred => fn prog => fn max_steps =>
    list_all (list_all (fn pc => time_indep_check prog pc max_steps)) pred)
    x;

fun init p = map (fn _ => zero_nata) (upt zero_nata p);

fun prog prog pc = (if less_nat pc (size_list prog) then nth prog pc else NONE);

fun init_pred_check x =
  (fn p => fn proga => fn max_steps => fn pred => fn s_0 =>
    all_interval_nat
      (fn q =>
        (case exec (stripfp (prog proga)) max_steps
                (nth (nth pred q) (nth (init p) q), ([], (s_0, (true, [])))) []
          of NONE => false | SOME ((_, (_, (_, (true, _)))), _) => true
          | SOME ((_, (_, (_, (false, _)))), _) => false))
      zero_nata p)
    x;

fun uPPAAL_Reachability_Problem_precompiled_start_state_axioms x =
  (fn p => fn max_steps => fn trans => fn prog => fn bounds => fn pred =>
    fn s_0 =>
    init_pred_check p prog max_steps pred s_0 andalso
      (bounded ord_int bounds s_0 andalso
        (time_indep_check1 pred prog max_steps andalso
          (time_indep_check2 trans prog max_steps andalso
            conjunction_check2 trans prog max_steps))))
    x;

fun collect_store prog =
  Set (map_filter
        (fn a =>
          (case a of NONE => NONE | SOME (INSTR (JMPZ _)) => NONE
            | SOME (INSTR ADD) => NONE | SOME (INSTR NOT) => NONE
            | SOME (INSTR AND) => NONE | SOME (INSTR LT) => NONE
            | SOME (INSTR LE) => NONE | SOME (INSTR EQ) => NONE
            | SOME (INSTR (PUSH _)) => NONE | SOME (INSTR POP) => NONE
            | SOME (INSTR (LID _)) => NONE | SOME (INSTR STORE) => NONE
            | SOME (INSTR (STOREI (_, _))) => NONE | SOME (INSTR COPY) => NONE
            | SOME (INSTR CALL) => NONE | SOME (INSTR RETURN) => NONE
            | SOME (INSTR HALT) => NONE
            | SOME (INSTR (STOREC (c, x))) => SOME (c, x)
            | SOME (INSTR (SETF _)) => NONE | SOME (CEXP _) => NONE))
        prog);

fun check_resets prog =
  ball (collect_store prog) (fn (_, x) => equal_inta x zero_inta);

fun collect_cexp prog =
  Set (map_filter
        (fn a =>
          (case a of NONE => NONE
            | SOME aa => (case aa of INSTR _ => NONE | CEXP ab => SOME ab)))
        prog);

fun collect_clock_pairs cc = image constraint_pair (Set cc);

fun clkp_set inv prog =
  sup_set (equal_prod equal_nat equal_int)
    (sup_seta (equal_prod equal_nat equal_int)
      (image collect_clock_pairs (Set (concat inv))))
    (image constraint_pair (collect_cexp prog));

fun clk_set inv prog =
  sup_set equal_nat (image fst (clkp_set inv prog))
    (image fst (collect_store prog));

fun check_pre p m inv pred trans prog =
  equal_nata (size_list inv) p andalso
    (equal_nata (size_list trans) p andalso
      (equal_nata (size_list pred) p andalso
        (all_interval_nat
           (fn i =>
             equal_nata (size_list (nth pred i))
               (size_list (nth trans i)) andalso
               equal_nata (size_list (nth inv i)) (size_list (nth trans i)))
           zero_nata p andalso
          (list_all
             (fn t =>
               list_all
                 (list_all (fn (_, (_, (_, l))) => less_nat l (size_list t))) t)
             trans andalso
            (less_nat zero_nata p andalso
              (less_nat zero_nata m andalso
                (all_interval_nat (fn i => not (null (nth trans i))) zero_nata
                   p andalso
                  (all_interval_nat
                     (fn q => not (null (nth (nth trans q) zero_nata)))
                     zero_nata p andalso
                    (ball (clkp_set inv prog)
                       (fn (_, a) => less_eq_int zero_inta a) andalso
                      (eq_set (card_UNIV_nat, equal_nat) (clk_set inv prog)
                         (Set (upt one_nata (suc m))) andalso
                        check_resets prog))))))))));

fun uPPAAL_Reachability_Problem_precompiled p m inv pred trans prog =
  check_pre p m inv pred trans prog;

fun uPPAAL_Reachability_Problem_precompiled_start_state p m max_steps inv trans
  prog bounds pred s_0 =
  uPPAAL_Reachability_Problem_precompiled p m inv pred trans prog andalso
    uPPAAL_Reachability_Problem_precompiled_start_state_axioms p max_steps trans
      prog bounds pred s_0;

fun sup_option A_ (SOME x) (SOME y) = SOME (sup A_ x y)
  | sup_option A_ x NONE = x
  | sup_option A_ NONE y = y;

fun find_resets_start prog pc =
  (if less_nat pc (size_list prog)
    then (case nth prog pc of NONE => NONE | SOME (INSTR (JMPZ _)) => NONE
           | SOME (INSTR ADD) => NONE | SOME (INSTR NOT) => NONE
           | SOME (INSTR AND) => NONE | SOME (INSTR LT) => NONE
           | SOME (INSTR LE) => NONE | SOME (INSTR EQ) => NONE
           | SOME (INSTR (PUSH _)) => NONE | SOME (INSTR POP) => NONE
           | SOME (INSTR (LID _)) => NONE | SOME (INSTR STORE) => NONE
           | SOME (INSTR (STOREI (_, _))) => NONE | SOME (INSTR COPY) => NONE
           | SOME (INSTR CALL) => NONE | SOME (INSTR RETURN) => NONE
           | SOME (INSTR HALT) => NONE
           | SOME (INSTR (STOREC (_, _))) =>
             sup_option sup_nat (SOME pc)
               (find_resets_start prog (plus_nat pc one_nata))
           | SOME (INSTR (SETF _)) => NONE | SOME (CEXP _) => NONE)
    else NONE);

fun collect_storea prog pc =
  (case find_resets_start prog pc of NONE => bot_set
    | SOME pca =>
      sup_seta (equal_prod equal_nat equal_int)
        (image
          (fn a =>
            (case a of NONE => bot_set | SOME (INSTR (JMPZ _)) => bot_set
              | SOME (INSTR ADD) => bot_set | SOME (INSTR NOT) => bot_set
              | SOME (INSTR AND) => bot_set | SOME (INSTR LT) => bot_set
              | SOME (INSTR LE) => bot_set | SOME (INSTR EQ) => bot_set
              | SOME (INSTR (PUSH _)) => bot_set | SOME (INSTR POP) => bot_set
              | SOME (INSTR (LID _)) => bot_set | SOME (INSTR STORE) => bot_set
              | SOME (INSTR (STOREI (_, _))) => bot_set
              | SOME (INSTR COPY) => bot_set | SOME (INSTR CALL) => bot_set
              | SOME (INSTR RETURN) => bot_set | SOME (INSTR HALT) => bot_set
              | SOME (INSTR (STOREC (c, x))) =>
                insert (equal_prod equal_nat equal_int) (c, x) bot_set
              | SOME (INSTR (SETF _)) => bot_set | SOME (CEXP _) => bot_set))
          (image (nth prog) (Set (upt pc (suc pca))))));

fun collect_cexpa max_steps prog pc =
  sup_seta (equal_acconstraint equal_nat equal_int)
    (image
      (fn a =>
        (case a of NONE => bot_set | SOME (INSTR _) => bot_set
          | SOME (CEXP ac) =>
            insert (equal_acconstraint equal_nat equal_int) ac bot_set))
      (image (nth prog) (steps_approx max_steps prog pc)));

fun clkp_seta max_steps inv trans prog i l =
  sup_set (equal_prod equal_nat equal_int)
    (collect_clock_pairs (nth (nth inv i) l))
    (sup_seta (equal_prod equal_nat equal_int)
      (image
        (fn (g, _) => image constraint_pair (collect_cexpa max_steps prog g))
        (Set (nth (nth trans i) l))));

fun find_next_halt prog pc =
  (if less_nat pc (size_list prog)
    then (case nth prog pc of NONE => find_next_halt prog (plus_nat pc one_nata)
           | SOME (INSTR (JMPZ _)) => find_next_halt prog (plus_nat pc one_nata)
           | SOME (INSTR ADD) => find_next_halt prog (plus_nat pc one_nata)
           | SOME (INSTR NOT) => find_next_halt prog (plus_nat pc one_nata)
           | SOME (INSTR AND) => find_next_halt prog (plus_nat pc one_nata)
           | SOME (INSTR LT) => find_next_halt prog (plus_nat pc one_nata)
           | SOME (INSTR LE) => find_next_halt prog (plus_nat pc one_nata)
           | SOME (INSTR EQ) => find_next_halt prog (plus_nat pc one_nata)
           | SOME (INSTR (PUSH _)) => find_next_halt prog (plus_nat pc one_nata)
           | SOME (INSTR POP) => find_next_halt prog (plus_nat pc one_nata)
           | SOME (INSTR (LID _)) => find_next_halt prog (plus_nat pc one_nata)
           | SOME (INSTR STORE) => find_next_halt prog (plus_nat pc one_nata)
           | SOME (INSTR (STOREI (_, _))) =>
             find_next_halt prog (plus_nat pc one_nata)
           | SOME (INSTR COPY) => find_next_halt prog (plus_nat pc one_nata)
           | SOME (INSTR CALL) => find_next_halt prog (plus_nat pc one_nata)
           | SOME (INSTR RETURN) => find_next_halt prog (plus_nat pc one_nata)
           | SOME (INSTR HALT) => SOME pc
           | SOME (INSTR (STOREC (_, _))) =>
             find_next_halt prog (plus_nat pc one_nata)
           | SOME (INSTR (SETF _)) => find_next_halt prog (plus_nat pc one_nata)
           | SOME (CEXP _) => find_next_halt prog (plus_nat pc one_nata))
    else NONE);

fun guaranteed_execution_cond A_ prog pc_s n =
  (case find_next_halt prog pc_s of NONE => false
    | SOME pc_t =>
      all_interval_nat
        (fn pc =>
          not (is_none (nth prog pc)) andalso
            (not (member (equal_option (equal_instrc A_)) (nth prog pc)
                   (image SOME
                     (image INSTR
                       (insert equal_instr STORE
                         (insert equal_instr HALT
                           (insert equal_instr POP
                             (insert equal_instr CALL
                               (insert equal_instr RETURN
                                 (insert equal_instr AND
                                   (insert equal_instr NOT
                                     (insert equal_instr ADD
                                       (insert equal_instr LT
 (insert equal_instr LE (insert equal_instr EQ bot_set)))))))))))))) andalso
              (case nth prog pc of NONE => true | SOME (INSTR (JMPZ _)) => true
                | SOME (INSTR ADD) => true | SOME (INSTR NOT) => true
                | SOME (INSTR AND) => true | SOME (INSTR LT) => true
                | SOME (INSTR LE) => true | SOME (INSTR EQ) => true
                | SOME (INSTR (PUSH _)) => true | SOME (INSTR POP) => true
                | SOME (INSTR (LID _)) => true | SOME (INSTR STORE) => true
                | SOME (INSTR (STOREI (_, _))) => true
                | SOME (INSTR COPY) => true | SOME (INSTR CALL) => true
                | SOME (INSTR RETURN) => true | SOME (INSTR HALT) => true
                | SOME (INSTR (STOREC (_, d))) => equal_inta d zero_inta
                | SOME (INSTR (SETF _)) => true | SOME (CEXP _) => true)))
        pc_s pc_t andalso
        (all_interval_nat
           (fn pc =>
             (case nth prog pc of NONE => true
               | SOME (INSTR (JMPZ pca)) =>
                 less_nat pc pca andalso less_eq_nat pca pc_t
               | SOME (INSTR ADD) => true | SOME (INSTR NOT) => true
               | SOME (INSTR AND) => true | SOME (INSTR LT) => true
               | SOME (INSTR LE) => true | SOME (INSTR EQ) => true
               | SOME (INSTR (PUSH _)) => true | SOME (INSTR POP) => true
               | SOME (INSTR (LID _)) => true | SOME (INSTR STORE) => true
               | SOME (INSTR (STOREI (_, _))) => true
               | SOME (INSTR COPY) => true | SOME (INSTR CALL) => true
               | SOME (INSTR RETURN) => true | SOME (INSTR HALT) => true
               | SOME (INSTR (STOREC (_, _))) => true
               | SOME (INSTR (SETF _)) => true | SOME (CEXP _) => true))
           pc_s pc_t andalso
          less_nat (minus_nat pc_t pc_s) n));

fun uPPAAL_Reachability_Problem_precompiled_ceiling_axioms p m max_steps inv
  trans prog k =
  all_interval_nat
    (fn i =>
      all_interval_nat
        (fn l =>
          ball (clkp_seta max_steps inv trans prog i l)
            (fn (x, ma) =>
              less_eq_int ma (int_of_nat (nth (nth (nth k i) l) x))))
        zero_nata (size_list (nth trans i)))
    zero_nata p andalso
    all_interval_nat
      (fn i =>
        all_interval_nat
          (fn l =>
            ball (collect_clock_pairs (nth (nth inv i) l))
              (fn (x, ma) =>
                less_eq_int ma (int_of_nat (nth (nth (nth k i) l) x))))
          zero_nata (size_list (nth trans i)))
      zero_nata p andalso
    (all_interval_nat
       (fn i =>
         all_interval_nat
           (fn l =>
             list_all
               (fn (_, (_, (r, la))) =>
                 ball (minus_set equal_nat
                        (Set (upt zero_nata (plus_nat m one_nata)))
                        (image fst (collect_storea prog r)))
                   (fn c =>
                     less_eq_nat (nth (nth (nth k i) la) c)
                       (nth (nth (nth k i) l) c)))
               (nth (nth trans i) l))
           zero_nata (size_list (nth trans i)))
       zero_nata p andalso
      equal_nata (size_list k) p) andalso
    (all_interval_nat
       (fn i => equal_nata (size_list (nth k i)) (size_list (nth trans i)))
       zero_nata p andalso
       list_all
         (list_all (fn xxs => equal_nata (size_list xxs) (plus_nat m one_nata)))
         k andalso
      (all_interval_nat
         (fn i =>
           all_interval_nat
             (fn l => equal_nata (nth (nth (nth k i) l) zero_nata) zero_nata)
             zero_nata (size_list (nth trans i)))
         zero_nata p andalso
        all_interval_nat
          (fn i =>
            all_interval_nat
              (fn l =>
                list_all
                  (fn (_, (_, (r, _))) =>
                    guaranteed_execution_cond equal_int prog r max_steps)
                  (nth (nth trans i) l))
              zero_nata (size_list (nth trans i)))
          zero_nata p));

fun check_ceiling p m max_steps inv trans prog k =
  uPPAAL_Reachability_Problem_precompiled_ceiling_axioms p m max_steps inv trans
    prog k;

fun uPPAAL_Reachability_Problem_precompiled_ceiling p m max_steps inv pred trans
  prog k =
  check_pre p m inv pred trans prog andalso
    check_ceiling p m max_steps inv trans prog k;

fun uPPAAL_Reachability_Problem_precompiled_axioms trans na =
  list_all
    (list_all
      (list_all
        (fn (_, a) => let
                        val (aa, _) = a;
                      in
                        pred_act equal_nat (fn ab => less_nat ab na) aa
                      end)))
    trans;

fun uPPAAL_Reachability_Problem_precompileda p m max_steps inv trans prog bounds
  pred s_0 na k =
  uPPAAL_Reachability_Problem_precompiled_start_state p m max_steps inv trans
    prog bounds pred s_0 andalso
    (uPPAAL_Reachability_Problem_precompiled_ceiling p m max_steps inv pred
       trans prog k andalso
      uPPAAL_Reachability_Problem_precompiled_axioms trans na);

fun actions_by_state i =
  fold (fn t => fn acc =>
         list_update acc (fst (snd t)) ((i, t) :: nth acc (fst (snd t))));

fun all_actions_by_state_impl upt_p empty_ran i l =
  fold (fn ia => actions_by_state ia (sub (sub i ia) (nth l ia))) upt_p
    empty_ran;

fun run_impl max_steps program pc s =
  exec program max_steps (pc, ([], (s, (true, [])))) [];

fun make_reset_impl max_steps program m1 s =
  (case run_impl max_steps program m1 s of NONE => []
    | SOME ((_, (_, (_, (_, r1)))), _) => r1);

fun check_pred_impl p max_steps pred program bnds l s =
  all_interval_nat
    (fn q =>
      (case run_impl max_steps program (nth (nth pred q) (nth l q)) s
        of NONE => false
        | SOME ((_, (_, (_, (f, _)))), _) =>
          f andalso
            all_interval_nat
              (fn i =>
                less_int (fst (sub bnds i)) (nth s i) andalso
                  less_int (nth s i) (snd (sub bnds i)))
              zero_nata (size_list s)))
    zero_nata p;

fun make_cconstr_impl program pcs =
  map_filter
    (fn pc =>
      (case program pc of NONE => NONE
        | SOME a => (case a of INSTR _ => NONE | CEXP aa => SOME aa)))
    pcs;

fun check_g_impl max_steps programf program pc s =
  (case run_impl max_steps programf pc s of NONE => NONE
    | SOME ((_, (_, (_, (true, _)))), pcs) =>
      SOME (make_cconstr_impl program pcs)
    | SOME ((_, (_, (_, (false, _)))), _) => NONE);

fun pairs_by_action_impl p max_steps pred pf pt porig bnds =
  (fn (l, s) => fn out =>
    concat o
      map (fn (i, (g1, (_, (m1, l1)))) =>
            map_filter
              (fn (j, a) =>
                let
                  val (g2, aa) = a;
                  val (ab, (m2, l2)) = aa;
                in
                  (if equal_nata i j then NONE
                    else (case (check_g_impl max_steps pt porig g1 s,
                                 check_g_impl max_steps pt porig g2 s)
                           of (NONE, _) => NONE | (SOME _, NONE) => NONE
                           | (SOME cc1, SOME cc2) =>
                             (case run_impl max_steps pf m2 s of NONE => NONE
                               | SOME ((_, (_, (s1, (_, r2)))), _) =>
                                 (case run_impl max_steps pf m1 s1
                                   of NONE => NONE
                                   | SOME ((_, (_, (sa, (_, _)))), _) =>
                                     (if check_pred_impl p max_steps pred pf
   bnds (list_update (list_update l i l1) j l2) sa
                                       then SOME
      (cc1 @ cc2,
        (ab, (make_reset_impl max_steps pf m1 s @ r2,
               (list_update (list_update l i l1) j l2, sa))))
                                       else NONE)))))
                end)
              out));

fun trans_i_from_impl p max_steps pred bounds programf programt program bnds
  trans_i_array =
  (fn (l, s) => fn i =>
    map_filter
      (fn (g, a) =>
        let
          val (aa, (m, la)) = a;
        in
          (case check_g_impl max_steps programt program g s of NONE => NONE
            | SOME cc =>
              (case run_impl max_steps programf m s of NONE => NONE
                | SOME ((_, (_, (sa, (_, r)))), _) =>
                  (if check_pred_impl p max_steps pred programf
                        (Vector.fromList bounds) (list_update l i la) sa
                    then SOME (cc, (aa, (r, (list_update l i la, sa))))
                    else NONE)))
        end)
      (sub (sub trans_i_array i) (nth l i)));

fun trans_out_map trans =
  map (map (map (fn (g, a) => let
                                val (aa, (m, l)) = a;
                                val Out ab = aa;
                              in
                                (g, (ab, (m, l)))
                              end) o
             filtera
               (fn a =>
                 (case a of (_, (In _, (_, _))) => false
                   | (_, (Out _, (_, _))) => true
                   | (_, (Sil _, (_, _))) => false))))
    trans;

fun trans_in_map trans =
  map (map (map (fn (g, a) => let
                                val (aa, (m, l)) = a;
                                val In ab = aa;
                              in
                                (g, (ab, (m, l)))
                              end) o
             filtera
               (fn a =>
                 (case a of (_, (In _, (_, _))) => true
                   | (_, (Out _, (_, _))) => false
                   | (_, (Sil _, (_, _))) => false))))
    trans;

fun trans_i_map trans =
  map (map (map_filter
             (fn (g, a) =>
               let
                 val (aa, (m, l)) = a;
               in
                 (case aa of In _ => NONE | Out _ => NONE
                   | Sil ab => SOME (g, (ab, (m, l))))
               end)))
    trans;

fun repair_pair_impl (A1_, A2_) n =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val x = fwi_impl (A1_, A2_) n ai bi ();
    in
      fwi_impl (A1_, A2_) n x bia ()
    end);

fun reset_canonical_upd_impl (A1_, A2_, A3_) n =
  (fn ai => fn bib => fn bia => fn bi => fn () =>
    let
      val x =
        mtx_set (heap_DBMEntry A3_) (suc n) ai (bia, zero_nata) (Le bi) ();
      val xa =
        mtx_set (heap_DBMEntry A3_) (suc n) x (zero_nata, bia)
          (Le (uminus A2_ bi)) ();
    in
      imp_fora one_nata (plus_nat bib one_nata)
        (fn xb => fn sigma =>
          (if equal_nata xb bia then (fn () => sigma)
            else (fn f_ => fn () => f_
                   ((mtx_get (heap_DBMEntry A3_) (suc n) sigma (zero_nata, xb))
                   ()) ())
                   (fn x_d =>
                     (fn f_ => fn () => f_
                       ((mtx_get (heap_DBMEntry A3_) (suc n) sigma
                          (xb, zero_nata))
                       ()) ())
                       (fn x_e =>
                         (fn f_ => fn () => f_
                           ((mtx_set (heap_DBMEntry A3_) (suc n) sigma (bia, xb)
                              (plus_DBMEntrya A1_ (Le bi) x_d))
                           ()) ())
                           (fn x_f =>
                             mtx_set (heap_DBMEntry A3_) (suc n) x_f (xb, bia)
                               (plus_DBMEntrya A1_ (Le (uminus A2_ bi))
                                 x_e))))))
        xa ()
    end);

fun up_canonical_upd_impl (A1_, A2_) n =
  (fn ai => fn bi =>
    imp_fora one_nata (plus_nat bi one_nata)
      (fn xa => fn sigma =>
        mtx_set (heap_DBMEntry A2_) (suc n) sigma (xa, zero_nata) INF)
      ai);

fun dbm_add_int INF uu = INF
  | dbm_add_int (Le v) INF = INF
  | dbm_add_int (Lt v) INF = INF
  | dbm_add_int (Le a) (Le b) = Le (plus_inta a b)
  | dbm_add_int (Le a) (Lt b) = Lt (plus_inta a b)
  | dbm_add_int (Lt a) (Le b) = Lt (plus_inta a b)
  | dbm_add_int (Lt a) (Lt b) = Lt (plus_inta a b);

fun fw_upd_impl_int n =
  (fn ai => fn bib => fn bia => fn bi => fn () =>
    let
      val x = mtx_get (heap_DBMEntry heap_int) (suc n) ai (bia, bi) ();
      val xa = mtx_get (heap_DBMEntry heap_int) (suc n) ai (bia, bib) ();
      val xb = mtx_get (heap_DBMEntry heap_int) (suc n) ai (bib, bi) ();
    in
      mtx_set (heap_DBMEntry heap_int) (suc n) ai (bia, bi)
        (min (ord_DBMEntry (equal_int, linorder_int)) x (dbm_add_int xa xb)) ()
    end);

fun fw_impl_int n =
  imp_fora zero_nata (plus_nat n one_nata)
    (fn xb =>
      imp_fora zero_nata (plus_nat n one_nata)
        (fn xd =>
          imp_fora zero_nata (plus_nat n one_nata)
            (fn xf => fn sigma => fw_upd_impl_int n sigma xb xd xf)));

fun dbm_subset_impl (A1_, A2_, A3_) n =
  (fn ai => fn bi =>
    imp_for zero_nata (suc n) (fn a => (fn () => a))
      (fn xb => fn _ =>
        imp_for zero_nata (suc n) (fn a => (fn () => a))
          (fn xe => fn _ => fn () =>
            let
              val x_f = mtx_get (heap_DBMEntry A3_) (suc n) ai (xb, xe) ();
              val x_g = mtx_get (heap_DBMEntry A3_) (suc n) bi (xb, xe) ();
            in
              less_eq_DBMEntry
                (A2_, (linorder_linordered_ab_semigroup_add o
                        linordered_ab_semigroup_add_linordered_ab_monoid_add o
                        linordered_ab_monoid_add_linordered_cancel_ab_monoid_add)
                        A1_)
                x_f x_g
            end)
          true)
      true);

fun check_diag_impla (A1_, A2_) n =
  (fn ai => fn bi =>
    imp_for zero_nata (suc ai) (fn sigma => (fn () => (not sigma)))
      (fn xb => fn sigma => fn () =>
        let
          val x = mtx_get (heap_DBMEntry A2_) (suc n) bi (xb, xb) ();
        in
          less_DBMEntry
            ((linorder_linordered_ab_semigroup_add o
               linordered_ab_semigroup_add_linordered_ab_monoid_add o
               linordered_ab_monoid_add_linordered_cancel_ab_monoid_add)
              A1_)
            x (Le (zero ((zero_monoid_add o monoid_add_comm_monoid_add o
                           comm_monoid_add_ordered_comm_monoid_add o
                           ordered_comm_monoid_add_linordered_ab_monoid_add o
                           linordered_ab_monoid_add_linordered_cancel_ab_monoid_add)
                          A1_))) orelse
            sigma
        end)
      false);

fun check_diag_impl (A1_, A2_) n =
  (fn xi =>
    imp_for zero_nata (suc n) (fn sigma => (fn () => (not sigma)))
      (fn xc => fn sigma => fn () =>
        let
          val x = mtx_get (heap_DBMEntry A2_) (suc n) xi (xc, xc) ();
        in
          less_DBMEntry
            ((linorder_linordered_ab_semigroup_add o
               linordered_ab_semigroup_add_linordered_ab_monoid_add o
               linordered_ab_monoid_add_linordered_cancel_ab_monoid_add)
              A1_)
            x (Le (zero ((zero_monoid_add o monoid_add_comm_monoid_add o
                           comm_monoid_add_ordered_comm_monoid_add o
                           ordered_comm_monoid_add_linordered_ab_monoid_add o
                           linordered_ab_monoid_add_linordered_cancel_ab_monoid_add)
                          A1_))) orelse
            sigma
        end)
      false);

fun abstra_upd_impl (A1_, A2_, A3_, A4_) n =
  (fn ai => fn bi =>
    (case ai
      of LTa (x41a, x42a) =>
        (fn () =>
          let
            val x = mtx_get (heap_DBMEntry A4_) (suc n) bi (x41a, zero_nata) ();
          in
            mtx_set (heap_DBMEntry A4_) (suc n) bi (x41a, zero_nata)
              (min (ord_DBMEntry
                     (A3_, (linorder_linordered_ab_semigroup_add o
                             linordered_ab_semigroup_add_linordered_ab_monoid_add o
                             linordered_ab_monoid_add_linordered_cancel_ab_monoid_add)
                             A1_))
                x (Lt x42a))
              ()
          end)
      | LEa (x41a, x42a) =>
        (fn () =>
          let
            val x = mtx_get (heap_DBMEntry A4_) (suc n) bi (x41a, zero_nata) ();
          in
            mtx_set (heap_DBMEntry A4_) (suc n) bi (x41a, zero_nata)
              (min (ord_DBMEntry
                     (A3_, (linorder_linordered_ab_semigroup_add o
                             linordered_ab_semigroup_add_linordered_ab_monoid_add o
                             linordered_ab_monoid_add_linordered_cancel_ab_monoid_add)
                             A1_))
                x (Le x42a))
              ()
          end)
      | EQa (x41a, x42a) =>
        (fn () =>
          let
            val x = mtx_get (heap_DBMEntry A4_) (suc n) bi (zero_nata, x41a) ();
            val x_a =
              mtx_get (heap_DBMEntry A4_) (suc n) bi (x41a, zero_nata) ();
            val x_b =
              mtx_set (heap_DBMEntry A4_) (suc n) bi (zero_nata, x41a)
                (min (ord_DBMEntry
                       (A3_, (linorder_linordered_ab_semigroup_add o
                               linordered_ab_semigroup_add_linordered_ab_monoid_add o
                               linordered_ab_monoid_add_linordered_cancel_ab_monoid_add)
                               A1_))
                  x (Le (uminus A2_ x42a)))
                ();
          in
            mtx_set (heap_DBMEntry A4_) (suc n) x_b (x41a, zero_nata)
              (min (ord_DBMEntry
                     (A3_, (linorder_linordered_ab_semigroup_add o
                             linordered_ab_semigroup_add_linordered_ab_monoid_add o
                             linordered_ab_monoid_add_linordered_cancel_ab_monoid_add)
                             A1_))
                x_a (Le x42a))
              ()
          end)
      | GT (x41a, x42a) =>
        (fn () =>
          let
            val x = mtx_get (heap_DBMEntry A4_) (suc n) bi (zero_nata, x41a) ();
          in
            mtx_set (heap_DBMEntry A4_) (suc n) bi (zero_nata, x41a)
              (min (ord_DBMEntry
                     (A3_, (linorder_linordered_ab_semigroup_add o
                             linordered_ab_semigroup_add_linordered_ab_monoid_add o
                             linordered_ab_monoid_add_linordered_cancel_ab_monoid_add)
                             A1_))
                x (Lt (uminus A2_ x42a)))
              ()
          end)
      | GE (x41a, x42a) =>
        (fn () =>
          let
            val x = mtx_get (heap_DBMEntry A4_) (suc n) bi (zero_nata, x41a) ();
          in
            mtx_set (heap_DBMEntry A4_) (suc n) bi (zero_nata, x41a)
              (min (ord_DBMEntry
                     (A3_, (linorder_linordered_ab_semigroup_add o
                             linordered_ab_semigroup_add_linordered_ab_monoid_add o
                             linordered_ab_monoid_add_linordered_cancel_ab_monoid_add)
                             A1_))
                x (Le (uminus A2_ x42a)))
              ()
          end)));

fun check_bexp (Not a) l s = not (check_bexp a l s)
  | check_bexp (And (a, b)) l s = check_bexp a l s andalso check_bexp b l s
  | check_bexp (Or (a, b)) l s = check_bexp a l s orelse check_bexp b l s
  | check_bexp (Imply (a, b)) l s =
    (if check_bexp a l s then check_bexp b l s else true)
  | check_bexp (Loc (p, la)) l uu = equal_nata (nth l p) la
  | check_bexp (Eq (i, x)) uv s = equal_inta (nth s i) x
  | check_bexp (Lea (i, x)) uw s = less_eq_int (nth s i) x
  | check_bexp (Lta (i, x)) ux s = less_int (nth s i) x
  | check_bexp (Ge (i, x)) uy s = less_eq_int x (nth s i)
  | check_bexp (Gt (i, x)) uz s = less_int x (nth s i);

fun hd_of_formula (EX phi) = check_bexp phi
  | hd_of_formula (EG phi) = check_bexp phi
  | hd_of_formula (AX phi) = (fn x => not o check_bexp phi x)
  | hd_of_formula (AG phi) = (fn x => not o check_bexp phi x)
  | hd_of_formula (Leadsto (phi, uu)) = check_bexp phi;

fun norm_upd_impl (A1_, A2_) n =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val x = mtx_get (heap_DBMEntry A2_) (suc n) ai (zero_nata, zero_nata) ();
      val xa =
        mtx_set (heap_DBMEntry A2_) (suc n) ai (zero_nata, zero_nata)
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
                    A1_)))
          ();
      val xb =
        imp_fora one_nata (suc bi)
          (fn xc => fn sigma =>
            (fn f_ => fn () => f_
              ((mtx_get (heap_DBMEntry A2_) (suc n) sigma (zero_nata, xc)) ())
              ())
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
                                  group_add_ab_group_add o
                                  ab_group_add_ordered_ab_group_add o
                                  ordered_ab_group_add_linordered_ab_group_add)
                                 A1_)))
                    (uminus
                      ((uminus_group_add o group_add_ab_group_add o
                         ab_group_add_ordered_ab_group_add o
                         ordered_ab_group_add_linordered_ab_group_add)
                        A1_)
                      (sub bia xc)))))
          xa ();
    in
      imp_fora one_nata (suc bi)
        (fn xba => fn sigma =>
          (fn f_ => fn () => f_
            ((mtx_get (heap_DBMEntry A2_) (suc n) sigma (xba, zero_nata)) ())
            ())
            (fn xc =>
              (fn f_ => fn () => f_
                ((mtx_set (heap_DBMEntry A2_) (suc n) sigma (xba, zero_nata)
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
                       xc (sub bia xba))
                     (zero ((zero_monoid_add o monoid_add_group_add o
                              group_add_ab_group_add o
                              ab_group_add_ordered_ab_group_add o
                              ordered_ab_group_add_linordered_ab_group_add)
                             A1_))))
                ()) ())
                (imp_fora one_nata (suc bi)
                  (fn xe => fn sigmaa =>
                    (fn f_ => fn () => f_
                      ((mtx_get (heap_DBMEntry A2_) (suc n) sigmaa (xba, xe))
                      ()) ())
                      (fn xd =>
                        mtx_set (heap_DBMEntry A2_) (suc n) sigmaa (xba, xe)
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
                              xd (sub bia xba))
                            (uminus
                              ((uminus_group_add o group_add_ab_group_add o
                                 ab_group_add_ordered_ab_group_add o
                                 ordered_ab_group_add_linordered_ab_group_add)
                                A1_)
                              (sub bia xe))))))))
        xb ()
    end);

fun reachability_checker p m max_steps inv trans prog bounds pred s_0 na k
  formula =
  let
    val i = upt zero_nata (plus_nat m one_nata);
    val ia = Set (upt zero_nata p);
    val ib = upt zero_nata na;
    val ic = upt zero_nata p;
    val id = Vector.fromList prog;
    val ie = Vector.fromList (map (map_option stript) prog);
    val ifa = Vector.fromList (map (map_option stripf) prog);
    val ig = size_list prog;
    val ida = (fn pc => (if less_nat pc ig then sub id pc else NONE));
    val iea = (fn pc => (if less_nat pc ig then sub ie pc else NONE));
    val ifb = (fn pc => (if less_nat pc ig then sub ifa pc else NONE));
    val iga = Vector.fromList bounds;
    val ih = Vector.fromList (map Vector.fromList (trans_i_map trans));
    val ii = Vector.fromList (map Vector.fromList (trans_in_map trans));
    val ij = Vector.fromList (map Vector.fromList (trans_out_map trans));
    val ik = Vector.fromList (map Vector.fromList inv);
    val iba =
      (fn l =>
        let
          val (la, s) = l;
          val ina = all_actions_by_state_impl ic (map (fn _ => []) ib) ii la;
          val out = all_actions_by_state_impl ic (map (fn _ => []) ib) ij la;
        in
          maps (fn a =>
                 pairs_by_action_impl p max_steps pred ifb iea ida iga (la, s)
                   (nth out a) (nth ina a))
            ib
        end @
          maps (trans_i_from_impl p max_steps pred bounds ifb iea ida iga ih l)
            ic);
    val idb =
      Vector.fromList
        (map (Vector.fromList o map (Vector.fromList o map int_of_nat)) k);
  in
    (fn () =>
      let
        val x =
          let
            val key = (fn a => (fn () => a)) o fst;
            val suba =
              (fn ai => fn bi =>
                let
                  val (a1, a2) = ai;
                  val (a1a, a2a) = bi;
                in
                  (if equal_proda (equal_list equal_nat) (equal_list equal_int)
                        a1 a1a
                    then dbm_subset_impl
                           (linordered_cancel_ab_monoid_add_int, equal_int,
                             heap_int)
                           m a2 a2a
                    else (fn () => false))
                end);
            val copy =
              (fn (a1, a2) =>
                (fn f_ => fn () => f_ ((amtx_copy (heap_DBMEntry heap_int) a2)
                  ()) ())
                  (fn x => (fn () => (a1, x))));
            val start =
              (fn f_ => fn () => f_
                ((amtx_dflt (heap_DBMEntry heap_int) (suc m) (suc m)
                   (Le zero_inta))
                ()) ())
                (fn x_a => (fn () => ((init p, s_0), x_a)));
            val final = (fn xi => (fn () => let
      val ((a, b), _) = xi;
    in
      hd_of_formula formula a b
    end));
            val succs =
              (fn (a1, a2) =>
                imp_nfoldli (iba a1) (fn _ => (fn () => true))
                  (fn xc => fn sigma =>
                    let
                      val (a1a, (_, (a1c, a2c))) = xc;
                    in
                      (fn f_ => fn () => f_
                        ((amtx_copy (heap_DBMEntry heap_int) a2) ()) ())
                        (fn x =>
                          (fn f_ => fn () => f_
                            (((fn f_ => fn () => f_
                                ((up_canonical_upd_impl
                                   (linordered_cancel_ab_monoid_add_int,
                                     heap_int)
                                   m x m)
                                ()) ())
                               (fn xa =>
                                 (fn f_ => fn () => f_
                                   ((imp_nfoldli
                                      let
val (l, _) = a1;
                                      in
maps (fn il => sub (sub ik il) (nth l il)) ic
                                      end
                                      (fn _ => (fn () => true))
                                      (fn ai => fn bi =>
(fn f_ => fn () => f_
  ((abstra_upd_impl
     (linordered_cancel_ab_monoid_add_int, uminus_int, equal_int, heap_int) m ai
     bi)
  ()) ())
  (fn xb =>
    repair_pair_impl
      (linordered_ab_monoid_add_DBMEntry
         (linordered_cancel_ab_monoid_add_int, equal_int),
        heap_DBMEntry heap_int)
      m xb zero_nata (constraint_clk ai)))
                                      xa)
                                   ()) ())
                                   (fn xb =>
                                     (fn f_ => fn () => f_
                                       ((check_diag_impla
  (linordered_cancel_ab_monoid_add_int, heap_int) m m xb)
                                       ()) ())
                                       (fn xaa =>
 (fn f_ => fn () => f_
   ((if xaa then (fn () => xb)
      else imp_nfoldli a1a (fn _ => (fn () => true))
             (fn ai => fn bi =>
               (fn f_ => fn () => f_
                 ((abstra_upd_impl
                    (linordered_cancel_ab_monoid_add_int, uminus_int, equal_int,
                      heap_int)
                    m ai bi)
                 ()) ())
                 (fn xd =>
                   repair_pair_impl
                     (linordered_ab_monoid_add_DBMEntry
                        (linordered_cancel_ab_monoid_add_int, equal_int),
                       heap_DBMEntry heap_int)
                     m xd zero_nata (constraint_clk ai)))
             xb)
   ()) ())
   (fn x_a =>
     (fn f_ => fn () => f_
       ((check_diag_impla (linordered_cancel_ab_monoid_add_int, heap_int) m m
          x_a)
       ()) ())
       (fn xd =>
         (fn f_ => fn () => f_
           ((if xd then (fn () => x_a)
              else (fn f_ => fn () => f_
                     ((imp_nfoldli a1c (fn _ => (fn () => true))
                        (fn xca => fn sigmaa =>
                          reset_canonical_upd_impl
                            (linordered_cancel_ab_monoid_add_int, uminus_int,
                              heap_int)
                            m sigmaa m xca zero_inta)
                        x_a)
                     ()) ())
                     (imp_nfoldli
                       let
                         val (l, _) = a2c;
                       in
                         maps (fn il => sub (sub ik il) (nth l il)) ic
                       end
                       (fn _ => (fn () => true))
                       (fn ai => fn bi =>
                         (fn f_ => fn () => f_
                           ((abstra_upd_impl
                              (linordered_cancel_ab_monoid_add_int, uminus_int,
                                equal_int, heap_int)
                              m ai bi)
                           ()) ())
                           (fn xe =>
                             repair_pair_impl
                               (linordered_ab_monoid_add_DBMEntry
                                  (linordered_cancel_ab_monoid_add_int,
                                    equal_int),
                                 heap_DBMEntry heap_int)
                               m xe zero_nata (constraint_clk ai)))))
           ()) ())
           (fn x_b =>
             (fn f_ => fn () => f_
               ((check_diag_impla
                  (linordered_cancel_ab_monoid_add_int, heap_int) m m x_b)
               ()) ())
               (fn x_c =>
                 (if x_c then (fn () => x_b)
                   else (fn f_ => fn () => f_
                          ((norm_upd_impl
                             (linordered_ab_group_add_int, heap_int) m x_b
                             let
                               val (l, _) = a2c;
                             in
                               Vector.fromList
                                 (map (fn c =>
maxa linorder_int (image (fn il => sub (sub (sub idb il) (nth l il)) c) ia))
                                   i)
                             end
                             m)
                          ()) ())
                          (fw_impl_int m))))))))))
                            ()) ())
                            (fn xa =>
                              (fn () => (op_list_prepend (a2c, xa) sigma))))
                    end)
                  []);
            val a =
              (fn (_, a) =>
                check_diag_impl (linordered_cancel_ab_monoid_add_int, heap_int)
                  m a);
          in
            pw_impl
              (heap_prod (heap_prod (heap_list heap_nat) (heap_list heap_int))
                (heap_array (typerep_DBMEntry typerep_int)))
              (equal_prod (equal_list equal_nat) (equal_list equal_int),
                hashable_prod (hashable_list hashable_nat)
                  (hashable_list hashable_int),
                heap_prod (heap_list heap_nat) (heap_list heap_int))
              key copy suba start final succs a
          end
            ();
        val _ = ();
      in
        x
      end)
  end;

fun leadsto_checker Type Type Type p m max_steps inv trans prog bounds pred s_0
  na k formula =
  let
    val i = upt zero_nata (plus_nat m one_nata);
    val ia = Set (upt zero_nata p);
    val ib = upt zero_nata na;
    val ic = upt zero_nata p;
    val id = Vector.fromList prog;
    val ie = Vector.fromList (map (map_option stript) prog);
    val ifa = Vector.fromList (map (map_option stripf) prog);
    val ig = size_list prog;
    val ida = (fn pc => (if less_nat pc ig then sub id pc else NONE));
    val iea = (fn pc => (if less_nat pc ig then sub ie pc else NONE));
    val ifb = (fn pc => (if less_nat pc ig then sub ifa pc else NONE));
    val iga = Vector.fromList bounds;
    val ih = Vector.fromList (map Vector.fromList (trans_i_map trans));
    val ii = Vector.fromList (map Vector.fromList (trans_in_map trans));
    val ij = Vector.fromList (map Vector.fromList (trans_out_map trans));
    val ik = Vector.fromList (map Vector.fromList inv);
    val iba =
      (fn l =>
        let
          val (la, s) = l;
          val ina = all_actions_by_state_impl ic (map (fn _ => []) ib) ii la;
          val out = all_actions_by_state_impl ic (map (fn _ => []) ib) ij la;
        in
          maps (fn a =>
                 pairs_by_action_impl p max_steps pred ifb iea ida iga (la, s)
                   (nth out a) (nth ina a))
            ib
        end @
          maps (trans_i_from_impl p max_steps pred bounds ifb iea ida iga ih l)
            ic);
    val idb =
      Vector.fromList
        (map (Vector.fromList o map (Vector.fromList o map int_of_nat)) k);
  in
    (fn psi => fn () =>
      let
        val r =
          let
            val key = (fn a => (fn () => a)) o fst;
            val suba =
              (fn ai => fn bi =>
                let
                  val (a1, a2) = ai;
                  val (a1a, a2a) = bi;
                in
                  (if equal_proda (equal_list equal_nat) (equal_list equal_int)
                        a1 a1a
                    then dbm_subset_impl
                           (linordered_cancel_ab_monoid_add_int, equal_int,
                             heap_int)
                           m a2 a2a
                    else (fn () => false))
                end);
            val copy =
              (fn (a1, a2) =>
                (fn f_ => fn () => f_ ((amtx_copy (heap_DBMEntry heap_int) a2)
                  ()) ())
                  (fn x => (fn () => (a1, x))));
            val start =
              (fn f_ => fn () => f_
                ((amtx_dflt (heap_DBMEntry heap_int) (suc m) (suc m)
                   (Le zero_inta))
                ()) ())
                (fn x_a => (fn () => ((init p, s_0), x_a)));
            val final = (fn xi => (fn () => let
      val ((a, b), _) = xi;
    in
      hd_of_formula formula a b
    end));
            val finala = (fn xi => (fn () => let
       val ((l, s), _) = xi;
     in
       not (check_bexp psi l s)
     end));
            val succs =
              (fn xi =>
                (fn f_ => fn () => f_
                  (let
                     val (a1, a2) = xi;
                   in
                     imp_nfoldli (iba a1) (fn _ => (fn () => true))
                       (fn xc => fn sigma =>
                         let
                           val (a1a, (_, (a1c, a2c))) = xc;
                         in
                           (if let
                                 val (l, s) = a2c;
                               in
                                 not (check_bexp psi l s)
                               end
                             then (fn f_ => fn () => f_
                                    ((amtx_copy (heap_DBMEntry heap_int) a2) ())
                                    ())
                                    (fn x =>
                                      (fn f_ => fn () => f_
(((fn f_ => fn () => f_
    ((up_canonical_upd_impl (linordered_cancel_ab_monoid_add_int, heap_int) m x
       m)
    ()) ())
   (fn xa =>
     (fn f_ => fn () => f_
       ((imp_nfoldli let
                       val (l, _) = a1;
                     in
                       maps (fn il => sub (sub ik il) (nth l il)) ic
                     end
          (fn _ => (fn () => true))
          (fn ai => fn bi =>
            (fn f_ => fn () => f_
              ((abstra_upd_impl
                 (linordered_cancel_ab_monoid_add_int, uminus_int, equal_int,
                   heap_int)
                 m ai bi)
              ()) ())
              (fn xb =>
                repair_pair_impl
                  (linordered_ab_monoid_add_DBMEntry
                     (linordered_cancel_ab_monoid_add_int, equal_int),
                    heap_DBMEntry heap_int)
                  m xb zero_nata (constraint_clk ai)))
          xa)
       ()) ())
       (fn xb =>
         (fn f_ => fn () => f_
           ((check_diag_impla (linordered_cancel_ab_monoid_add_int, heap_int) m
              m xb)
           ()) ())
           (fn xaa =>
             (fn f_ => fn () => f_
               ((if xaa then (fn () => xb)
                  else imp_nfoldli a1a (fn _ => (fn () => true))
                         (fn ai => fn bi =>
                           (fn f_ => fn () => f_
                             ((abstra_upd_impl
                                (linordered_cancel_ab_monoid_add_int,
                                  uminus_int, equal_int, heap_int)
                                m ai bi)
                             ()) ())
                             (fn xd =>
                               repair_pair_impl
                                 (linordered_ab_monoid_add_DBMEntry
                                    (linordered_cancel_ab_monoid_add_int,
                                      equal_int),
                                   heap_DBMEntry heap_int)
                                 m xd zero_nata (constraint_clk ai)))
                         xb)
               ()) ())
               (fn x_a =>
                 (fn f_ => fn () => f_
                   ((check_diag_impla
                      (linordered_cancel_ab_monoid_add_int, heap_int) m m x_a)
                   ()) ())
                   (fn xd =>
                     (fn f_ => fn () => f_
                       ((if xd then (fn () => x_a)
                          else (fn f_ => fn () => f_
                                 ((imp_nfoldli a1c (fn _ => (fn () => true))
                                    (fn xca => fn sigmaa =>
                                      reset_canonical_upd_impl
(linordered_cancel_ab_monoid_add_int, uminus_int, heap_int) m sigmaa m xca
zero_inta)
                                    x_a)
                                 ()) ())
                                 (imp_nfoldli
                                   let
                                     val (l, _) = a2c;
                                   in
                                     maps (fn il => sub (sub ik il) (nth l il))
                                       ic
                                   end
                                   (fn _ => (fn () => true))
                                   (fn ai => fn bi =>
                                     (fn f_ => fn () => f_
                                       ((abstra_upd_impl
  (linordered_cancel_ab_monoid_add_int, uminus_int, equal_int, heap_int) m ai
  bi)
                                       ()) ())
                                       (fn xe =>
 repair_pair_impl
   (linordered_ab_monoid_add_DBMEntry
      (linordered_cancel_ab_monoid_add_int, equal_int),
     heap_DBMEntry heap_int)
   m xe zero_nata (constraint_clk ai)))))
                       ()) ())
                       (fn x_b =>
                         (fn f_ => fn () => f_
                           ((check_diag_impla
                              (linordered_cancel_ab_monoid_add_int, heap_int) m
                              m x_b)
                           ()) ())
                           (fn x_c =>
                             (if x_c then (fn () => x_b)
                               else (fn f_ => fn () => f_
                                      ((norm_upd_impl
 (linordered_ab_group_add_int, heap_int) m x_b
 let
   val (l, _) = a2c;
 in
   Vector.fromList
     (map (fn c =>
            maxa linorder_int
              (image (fn il => sub (sub (sub idb il) (nth l il)) c) ia))
       i)
 end
 m)
                                      ()) ())
                                      (fw_impl_int m))))))))))
()) ())
(fn xa => (fn () => (op_list_prepend (a2c, xa) sigma))))
                             else (fn () => sigma))
                         end)
                       []
                   end
                  ()) ())
                  (fn x =>
                    (fn f_ => fn () => f_
                      ((imp_nfoldli x (fn _ => (fn () => true))
                         (fn xc => fn sigma =>
                           (fn f_ => fn () => f_
                             (let
                                val (_, a2) = xc;
                              in
                                (fn f_ => fn () => f_
                                  ((check_diag_impl
                                     (linordered_cancel_ab_monoid_add_int,
                                       heap_int)
                                     m a2)
                                  ()) ())
                                  (fn x_c => (fn () => (not x_c)))
                              end
                             ()) ())
                             (fn x_c =>
                               (fn () =>
                                 (if x_c then op_list_prepend xc sigma
                                   else sigma))))
                         [])
                      ()) ())
                      (fn xa => (fn () => (op_list_rev xa)))));
            val succsa =
              (fn xi =>
                (fn f_ => fn () => f_
                  (let
                     val (a1, a2) = xi;
                   in
                     imp_nfoldli (iba a1) (fn _ => (fn () => true))
                       (fn xc => fn sigma =>
                         let
                           val (a1a, (_, (a1c, a2c))) = xc;
                         in
                           (fn f_ => fn () => f_
                             ((amtx_copy (heap_DBMEntry heap_int) a2) ()) ())
                             (fn x =>
                               (fn f_ => fn () => f_
                                 (((fn f_ => fn () => f_
                                     ((up_canonical_upd_impl
(linordered_cancel_ab_monoid_add_int, heap_int) m x m)
                                     ()) ())
                                    (fn xa =>
                                      (fn f_ => fn () => f_
((imp_nfoldli let
                val (l, _) = a1;
              in
                maps (fn il => sub (sub ik il) (nth l il)) ic
              end
   (fn _ => (fn () => true))
   (fn ai => fn bi =>
     (fn f_ => fn () => f_
       ((abstra_upd_impl
          (linordered_cancel_ab_monoid_add_int, uminus_int, equal_int, heap_int)
          m ai bi)
       ()) ())
       (fn xb =>
         repair_pair_impl
           (linordered_ab_monoid_add_DBMEntry
              (linordered_cancel_ab_monoid_add_int, equal_int),
             heap_DBMEntry heap_int)
           m xb zero_nata (constraint_clk ai)))
   xa)
()) ())
(fn xb =>
  (fn f_ => fn () => f_
    ((check_diag_impla (linordered_cancel_ab_monoid_add_int, heap_int) m m xb)
    ()) ())
    (fn xaa =>
      (fn f_ => fn () => f_
        ((if xaa then (fn () => xb)
           else imp_nfoldli a1a (fn _ => (fn () => true))
                  (fn ai => fn bi =>
                    (fn f_ => fn () => f_
                      ((abstra_upd_impl
                         (linordered_cancel_ab_monoid_add_int, uminus_int,
                           equal_int, heap_int)
                         m ai bi)
                      ()) ())
                      (fn xd =>
                        repair_pair_impl
                          (linordered_ab_monoid_add_DBMEntry
                             (linordered_cancel_ab_monoid_add_int, equal_int),
                            heap_DBMEntry heap_int)
                          m xd zero_nata (constraint_clk ai)))
                  xb)
        ()) ())
        (fn x_a =>
          (fn f_ => fn () => f_
            ((check_diag_impla (linordered_cancel_ab_monoid_add_int, heap_int) m
               m x_a)
            ()) ())
            (fn xd =>
              (fn f_ => fn () => f_
                ((if xd then (fn () => x_a)
                   else (fn f_ => fn () => f_
                          ((imp_nfoldli a1c (fn _ => (fn () => true))
                             (fn xca => fn sigmaa =>
                               reset_canonical_upd_impl
                                 (linordered_cancel_ab_monoid_add_int,
                                   uminus_int, heap_int)
                                 m sigmaa m xca zero_inta)
                             x_a)
                          ()) ())
                          (imp_nfoldli
                            let
                              val (l, _) = a2c;
                            in
                              maps (fn il => sub (sub ik il) (nth l il)) ic
                            end
                            (fn _ => (fn () => true))
                            (fn ai => fn bi =>
                              (fn f_ => fn () => f_
                                ((abstra_upd_impl
                                   (linordered_cancel_ab_monoid_add_int,
                                     uminus_int, equal_int, heap_int)
                                   m ai bi)
                                ()) ())
                                (fn xe =>
                                  repair_pair_impl
                                    (linordered_ab_monoid_add_DBMEntry
                                       (linordered_cancel_ab_monoid_add_int,
 equal_int),
                                      heap_DBMEntry heap_int)
                                    m xe zero_nata (constraint_clk ai)))))
                ()) ())
                (fn x_b =>
                  (fn f_ => fn () => f_
                    ((check_diag_impla
                       (linordered_cancel_ab_monoid_add_int, heap_int) m m x_b)
                    ()) ())
                    (fn x_c =>
                      (if x_c then (fn () => x_b)
                        else (fn f_ => fn () => f_
                               ((norm_upd_impl
                                  (linordered_ab_group_add_int, heap_int) m x_b
                                  let
                                    val (l, _) = a2c;
                                  in
                                    Vector.fromList
                                      (map
(fn c =>
  maxa linorder_int (image (fn il => sub (sub (sub idb il) (nth l il)) c) ia))
i)
                                  end
                                  m)
                               ()) ())
                               (fw_impl_int m))))))))))
                                 ()) ())
                                 (fn xa =>
                                   (fn () =>
                                     (op_list_prepend (a2c, xa) sigma))))
                         end)
                       []
                   end
                  ()) ())
                  (fn x =>
                    (fn f_ => fn () => f_
                      ((imp_nfoldli x (fn _ => (fn () => true))
                         (fn xc => fn sigma =>
                           (fn f_ => fn () => f_
                             (let
                                val (_, a2) = xc;
                              in
                                (fn f_ => fn () => f_
                                  ((check_diag_impl
                                     (linordered_cancel_ab_monoid_add_int,
                                       heap_int)
                                     m a2)
                                  ()) ())
                                  (fn x_c => (fn () => (not x_c)))
                              end
                             ()) ())
                             (fn x_c =>
                               (fn () =>
                                 (if x_c then op_list_prepend xc sigma
                                   else sigma))))
                         [])
                      ()) ())
                      (fn xa => (fn () => (op_list_rev xa)))));
            val empty =
              (fn (_, a) =>
                check_diag_impl (linordered_cancel_ab_monoid_add_int, heap_int)
                  m a);
          in
            leadsto_impl
              (heap_prod (heap_prod (heap_list heap_nat) (heap_list heap_int))
                (heap_array (typerep_DBMEntry typerep_int)))
              (equal_prod (equal_list equal_nat) (equal_list equal_int),
                hashable_prod (hashable_list hashable_nat)
                  (hashable_list hashable_int),
                heap_prod (heap_list heap_nat) (heap_list heap_int))
              Type Type Type copy succs start suba key succsa empty final finala
          end
            ();
      in
        not r
      end)
  end;

fun dfs_map_impl_0 D_ (E1_, E2_, E3_) Type Type Type succsi lei keyi copyi x =
  let
    val (a1, (a1a, a2a)) = x;
  in
    (fn () =>
      let
        val xa = keyi a2a ();
        val xaa =
          hms_extract (ht_lookup (E1_, E2_, E3_) (heap_list D_))
            (ht_delete (E1_, E2_, E3_) (heap_list D_)) xa a1a ();
        val a =
          (case xaa of (NONE, a2b) => (fn () => (a2b, false))
            | (SOME x_c, a2b) =>
              (fn f_ => fn () => f_
                ((imp_nfoldli x_c (fn sigma => (fn () => (not sigma)))
                   (fn xf => fn sigma =>
                     (fn f_ => fn () => f_ ((lei xf a2a) ()) ())
                       (fn x_f => (fn () => (x_f orelse sigma))))
                   false)
                ()) ())
                (fn x_d =>
                  (fn f_ => fn () => f_
                    ((ht_update (E1_, E2_, E3_) (heap_list D_) xa x_c a2b) ())
                    ())
                    (fn x_e => (fn () => (x_e, x_d)))))
            ();
      in
        (case a of (a1b, true) => (fn () => (a1, (a1b, true)))
          | (a1b, false) =>
            (fn f_ => fn () => f_ ((keyi a2a) ()) ())
              (fn xb =>
                (fn f_ => fn () => f_
                  ((hms_extract (ht_lookup (E1_, E2_, E3_) (heap_list D_))
                     (ht_delete (E1_, E2_, E3_) (heap_list D_)) xb a1)
                  ()) ())
                  (fn xab =>
                    (fn f_ => fn () => f_
                      ((case xab of (NONE, a2c) => (fn () => (a2c, false))
                         | (SOME x_e, a2c) =>
                           (fn f_ => fn () => f_ ((lso_bex_impl (lei a2a) x_e)
                             ()) ())
                             (fn x_f =>
                               (fn f_ => fn () => f_
                                 ((ht_update (E1_, E2_, E3_) (heap_list D_) xb
                                    x_e a2c)
                                 ()) ())
                                 (fn x_g => (fn () => (x_g, x_f)))))
                      ()) ())
                      (fn aa =>
                        (case aa
                          of (a1c, true) => (fn () => (a1c, (a1b, false)))
                          | (a1c, false) =>
                            (fn f_ => fn () => f_ ((copyi a2a) ()) ())
                              (fn xc =>
                                (fn f_ => fn () => f_ ((keyi xc) ()) ())
                                  (fn xd =>
                                    (fn f_ => fn () => f_
                                      ((hms_extract
 (ht_lookup (E1_, E2_, E3_) (heap_list D_))
 (ht_delete (E1_, E2_, E3_) (heap_list D_)) xd a1b)
                                      ()) ())
                                      (fn xac =>
(fn f_ => fn () => f_
  ((case xac
     of (NONE, a2d) =>
       (fn f_ => fn () => f_ ((copyi a2a) ()) ())
         (fn xad =>
           (fn f_ => fn () => f_
             ((ht_update (E1_, E2_, E3_) (heap_list D_) xd
                (op_list_prepend xad []) a2d)
             ()) ())
             (fn x_h => (fn () => (NONE, x_h))))
     | (SOME x_g, a2d) =>
       (fn f_ => fn () => f_ ((copyi a2a) ()) ())
         (fn xad =>
           (fn f_ => fn () => f_
             ((ht_update (E1_, E2_, E3_) (heap_list D_) xd
                (op_list_prepend xad x_g) a2d)
             ()) ())
             (fn x_i => (fn () => (NONE, x_i)))))
  ()) ())
  (fn (_, a2d) =>
    (fn f_ => fn () => f_ ((succsi a2a) ()) ())
      (fn xe =>
        (fn f_ => fn () => f_
          ((imp_nfoldli xe (fn (_, (_, b)) => (fn () => (not b)))
             (fn xk => fn (a1e, (a1f, _)) =>
               dfs_map_impl_0 D_ (E1_, E2_, E3_) Type Type Type succsi lei keyi
                 copyi (a1e, (a1f, xk)))
             (a1c, (a2d, false)))
          ()) ())
          (fn (a1e, (a1f, a2f)) =>
            (fn f_ => fn () => f_ ((copyi a2a) ()) ())
              (fn xf =>
                (fn f_ => fn () => f_ ((keyi xf) ()) ())
                  (fn xg =>
                    (fn f_ => fn () => f_
                      ((hms_extract (ht_lookup (E1_, E2_, E3_) (heap_list D_))
                         (ht_delete (E1_, E2_, E3_) (heap_list D_)) xg a1f)
                      ()) ())
                      (fn xad =>
                        (fn f_ => fn () => f_
                          ((case xad
                             of (NONE, a2g) =>
                               (fn f_ => fn () => f_
                                 ((ht_update (E1_, E2_, E3_) (heap_list D_) xg
                                    [] a2g)
                                 ()) ())
                                 (fn x_k => (fn () => (NONE, x_k)))
                             | (SOME x_j, a2g) =>
                               (fn f_ => fn () => f_
                                 ((ht_update (E1_, E2_, E3_) (heap_list D_) xg
                                    (if op_list_is_empty x_j then []
                                      else op_list_tl x_j)
                                    a2g)
                                 ()) ())
                                 (fn x_l => (fn () => (NONE, x_l))))
                          ()) ())
                          (fn (_, a2g) =>
                            (fn f_ => fn () => f_ ((copyi a2a) ()) ())
                              (fn xh =>
                                (fn f_ => fn () => f_ ((keyi xh) ()) ())
                                  (fn xi =>
                                    (fn f_ => fn () => f_
                                      ((hms_extract
 (ht_lookup (E1_, E2_, E3_) (heap_list D_))
 (ht_delete (E1_, E2_, E3_) (heap_list D_)) xi a1e)
                                      ()) ())
                                      (fn xae =>
(fn f_ => fn () => f_
  ((case xae
     of (NONE, a2h) =>
       (fn f_ => fn () => f_ ((copyi a2a) ()) ())
         (fn xaf =>
           (fn f_ => fn () => f_
             ((ht_update (E1_, E2_, E3_) (heap_list D_) xi [xaf] a2h) ()) ())
             (fn x_m => (fn () => (NONE, x_m))))
     | (SOME x_l, a2h) =>
       (fn f_ => fn () => f_ ((copyi a2a) ()) ())
         (fn xaf =>
           (fn f_ => fn () => f_
             ((ht_update (E1_, E2_, E3_) (heap_list D_) xi (xaf :: x_l) a2h) ())
             ())
             (fn x_n => (fn () => (NONE, x_n)))))
  ()) ())
  (fn (_, a2h) => (fn () => (a2h, (a2g, a2f))))))))))))))))))))))
          ()
      end)
  end;

fun dfs_map_impl D_ (E1_, E2_, E3_) Type Type Type succsi a_0i lei keyi copyi =
  (fn () =>
    let
      val x = ht_new (E2_, E3_) (heap_list D_) ();
      val xa = ht_new (E2_, E3_) (heap_list D_) ();
      val xb = a_0i ();
      val xc =
        dfs_map_impl_0 D_ (E1_, E2_, E3_) Type Type Type succsi lei keyi copyi
          (x, (xa, xb)) ();
      val a = let
                val (a1, (_, a2a)) = xc;
              in
                (fn () => (a2a, a1))
              end
                ();
    in
      let
        val (a1, _) = a;
      in
        (fn () => a1)
      end
        ()
    end);

fun alw_ev_checker Type Type Type p m max_steps inv trans prog bounds pred s_0
  na k formula =
  let
    val i = upt zero_nata (plus_nat m one_nata);
    val ia = Set (upt zero_nata p);
    val ib = upt zero_nata na;
    val ic = upt zero_nata p;
    val id = Vector.fromList prog;
    val ie = Vector.fromList (map (map_option stript) prog);
    val ifa = Vector.fromList (map (map_option stripf) prog);
    val ig = size_list prog;
    val ida = (fn pc => (if less_nat pc ig then sub id pc else NONE));
    val iea = (fn pc => (if less_nat pc ig then sub ie pc else NONE));
    val ifb = (fn pc => (if less_nat pc ig then sub ifa pc else NONE));
    val iga = Vector.fromList bounds;
    val ih = Vector.fromList (map Vector.fromList (trans_i_map trans));
    val ii = Vector.fromList (map Vector.fromList (trans_in_map trans));
    val ij = Vector.fromList (map Vector.fromList (trans_out_map trans));
    val ik = Vector.fromList (map Vector.fromList inv);
    val iba =
      (fn l =>
        let
          val (la, s) = l;
          val ina = all_actions_by_state_impl ic (map (fn _ => []) ib) ii la;
          val out = all_actions_by_state_impl ic (map (fn _ => []) ib) ij la;
        in
          maps (fn a =>
                 pairs_by_action_impl p max_steps pred ifb iea ida iga (la, s)
                   (nth out a) (nth ina a))
            ib
        end @
          maps (trans_i_from_impl p max_steps pred bounds ifb iea ida iga ih l)
            ic);
    val idb =
      Vector.fromList
        (map (Vector.fromList o map (Vector.fromList o map int_of_nat)) k);
  in
    (fn () =>
      let
        val x =
          let
            val key = (fn a => (fn () => a)) o fst;
            val suba =
              (fn ai => fn bi =>
                let
                  val (a1, a2) = ai;
                  val (a1a, a2a) = bi;
                in
                  (if equal_proda (equal_list equal_nat) (equal_list equal_int)
                        a1 a1a
                    then dbm_subset_impl
                           (linordered_cancel_ab_monoid_add_int, equal_int,
                             heap_int)
                           m a2 a2a
                    else (fn () => false))
                end);
            val copy =
              (fn (a1, a2) =>
                (fn f_ => fn () => f_ ((amtx_copy (heap_DBMEntry heap_int) a2)
                  ()) ())
                  (fn x => (fn () => (a1, x))));
            val start =
              (fn f_ => fn () => f_
                ((amtx_dflt (heap_DBMEntry heap_int) (suc m) (suc m)
                   (Le zero_inta))
                ()) ())
                (fn x_a => (fn () => ((init p, s_0), x_a)));
            val succs =
              (fn xi =>
                (fn f_ => fn () => f_
                  (let
                     val (a1, a2) = xi;
                   in
                     imp_nfoldli (iba a1) (fn _ => (fn () => true))
                       (fn xc => fn sigma =>
                         let
                           val (a1a, (_, (a1c, a2c))) = xc;
                         in
                           (if let
                                 val (a, b) = a2c;
                               in
                                 hd_of_formula formula a b
                               end
                             then (fn f_ => fn () => f_
                                    ((amtx_copy (heap_DBMEntry heap_int) a2) ())
                                    ())
                                    (fn x =>
                                      (fn f_ => fn () => f_
(((fn f_ => fn () => f_
    ((up_canonical_upd_impl (linordered_cancel_ab_monoid_add_int, heap_int) m x
       m)
    ()) ())
   (fn xa =>
     (fn f_ => fn () => f_
       ((imp_nfoldli let
                       val (l, _) = a1;
                     in
                       maps (fn il => sub (sub ik il) (nth l il)) ic
                     end
          (fn _ => (fn () => true))
          (fn ai => fn bi =>
            (fn f_ => fn () => f_
              ((abstra_upd_impl
                 (linordered_cancel_ab_monoid_add_int, uminus_int, equal_int,
                   heap_int)
                 m ai bi)
              ()) ())
              (fn xb =>
                repair_pair_impl
                  (linordered_ab_monoid_add_DBMEntry
                     (linordered_cancel_ab_monoid_add_int, equal_int),
                    heap_DBMEntry heap_int)
                  m xb zero_nata (constraint_clk ai)))
          xa)
       ()) ())
       (fn xb =>
         (fn f_ => fn () => f_
           ((check_diag_impla (linordered_cancel_ab_monoid_add_int, heap_int) m
              m xb)
           ()) ())
           (fn xaa =>
             (fn f_ => fn () => f_
               ((if xaa then (fn () => xb)
                  else imp_nfoldli a1a (fn _ => (fn () => true))
                         (fn ai => fn bi =>
                           (fn f_ => fn () => f_
                             ((abstra_upd_impl
                                (linordered_cancel_ab_monoid_add_int,
                                  uminus_int, equal_int, heap_int)
                                m ai bi)
                             ()) ())
                             (fn xd =>
                               repair_pair_impl
                                 (linordered_ab_monoid_add_DBMEntry
                                    (linordered_cancel_ab_monoid_add_int,
                                      equal_int),
                                   heap_DBMEntry heap_int)
                                 m xd zero_nata (constraint_clk ai)))
                         xb)
               ()) ())
               (fn x_a =>
                 (fn f_ => fn () => f_
                   ((check_diag_impla
                      (linordered_cancel_ab_monoid_add_int, heap_int) m m x_a)
                   ()) ())
                   (fn xd =>
                     (fn f_ => fn () => f_
                       ((if xd then (fn () => x_a)
                          else (fn f_ => fn () => f_
                                 ((imp_nfoldli a1c (fn _ => (fn () => true))
                                    (fn xca => fn sigmaa =>
                                      reset_canonical_upd_impl
(linordered_cancel_ab_monoid_add_int, uminus_int, heap_int) m sigmaa m xca
zero_inta)
                                    x_a)
                                 ()) ())
                                 (imp_nfoldli
                                   let
                                     val (l, _) = a2c;
                                   in
                                     maps (fn il => sub (sub ik il) (nth l il))
                                       ic
                                   end
                                   (fn _ => (fn () => true))
                                   (fn ai => fn bi =>
                                     (fn f_ => fn () => f_
                                       ((abstra_upd_impl
  (linordered_cancel_ab_monoid_add_int, uminus_int, equal_int, heap_int) m ai
  bi)
                                       ()) ())
                                       (fn xe =>
 repair_pair_impl
   (linordered_ab_monoid_add_DBMEntry
      (linordered_cancel_ab_monoid_add_int, equal_int),
     heap_DBMEntry heap_int)
   m xe zero_nata (constraint_clk ai)))))
                       ()) ())
                       (fn x_b =>
                         (fn f_ => fn () => f_
                           ((check_diag_impla
                              (linordered_cancel_ab_monoid_add_int, heap_int) m
                              m x_b)
                           ()) ())
                           (fn x_c =>
                             (if x_c then (fn () => x_b)
                               else (fn f_ => fn () => f_
                                      ((norm_upd_impl
 (linordered_ab_group_add_int, heap_int) m x_b
 let
   val (l, _) = a2c;
 in
   Vector.fromList
     (map (fn c =>
            maxa linorder_int
              (image (fn il => sub (sub (sub idb il) (nth l il)) c) ia))
       i)
 end
 m)
                                      ()) ())
                                      (fw_impl_int m))))))))))
()) ())
(fn xa => (fn () => (op_list_prepend (a2c, xa) sigma))))
                             else (fn () => sigma))
                         end)
                       []
                   end
                  ()) ())
                  (fn x =>
                    (fn f_ => fn () => f_
                      ((imp_nfoldli x (fn _ => (fn () => true))
                         (fn xc => fn sigma =>
                           (fn f_ => fn () => f_
                             (let
                                val (_, a2) = xc;
                              in
                                (fn f_ => fn () => f_
                                  ((check_diag_impl
                                     (linordered_cancel_ab_monoid_add_int,
                                       heap_int)
                                     m a2)
                                  ()) ())
                                  (fn x_c => (fn () => (not x_c)))
                              end
                             ()) ())
                             (fn x_c =>
                               (fn () =>
                                 (if x_c then op_list_prepend xc sigma
                                   else sigma))))
                         [])
                      ()) ())
                      (fn xa => (fn () => (op_list_rev xa)))));
          in
            dfs_map_impl
              (heap_prod (heap_prod (heap_list heap_nat) (heap_list heap_int))
                (heap_array (typerep_DBMEntry typerep_int)))
              (equal_prod (equal_list equal_nat) (equal_list equal_int),
                hashable_prod (hashable_list hashable_nat)
                  (hashable_list hashable_int),
                heap_prod (heap_list heap_nat) (heap_list heap_int))
              Type Type Type succs start suba key copy
          end
            ();
        val _ = ();
      in
        x
      end)
  end;

fun model_checker Type Type Type p m max_steps inv trans prog bounds pred s_0 na
  k formula =
  (case formula
    of EX _ =>
      reachability_checker p m max_steps inv trans prog bounds pred s_0 na k
        formula
    | EG _ =>
      (if let
            val (a, b) = (init p, s_0);
          in
            hd_of_formula formula a b
          end
        then alw_ev_checker Type Type Type p m max_steps inv trans prog bounds
               pred s_0 na k formula
        else (fn () => false))
    | AX _ =>
      (fn () =>
        let
          val r =
            (if let
                  val (a, b) = (init p, s_0);
                in
                  hd_of_formula formula a b
                end
              then alw_ev_checker Type Type Type p m max_steps inv trans prog
                     bounds pred s_0 na k formula
              else (fn () => false))
              ();
        in
          not r
        end)
    | AG _ =>
      (fn () =>
        let
          val r =
            reachability_checker p m max_steps inv trans prog bounds pred s_0 na
              k formula ();
        in
          not r
        end)
    | Leadsto (_, a) =>
      leadsto_checker Type Type Type p m max_steps inv trans prog bounds pred
        s_0 na k formula a);

fun precond_mc Type Type Type pa m k max_steps i t prog final bounds p s_0 na =
  (if uPPAAL_Reachability_Problem_precompileda pa m max_steps i t prog bounds p
        s_0 na k
    then (fn () =>
           let
             val x =
               model_checker Type Type Type pa m max_steps i t prog bounds p s_0
                 na k final ();
           in
             SOME x
           end)
    else (fn () => NONE));

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

fun resets trans prog q c l =
  fold (fn (_, (_, (r, la))) => fn xs =>
         (if membera equal_nat xs la orelse
               member equal_nat c (image fst (collect_storea prog r))
           then xs else la :: xs))
    (nth (nth trans q) l) [];

fun ea trans prog q c l = resets trans prog q c l;

fun n trans q = size_list (nth trans q);

fun e trans prog q c l =
  (if equal_nata l (n trans q) then upt zero_nata (n trans q)
    else filtera (fn la => membera equal_nat (ea trans prog q c la) l)
           (upt zero_nata (n trans q)));

fun bound_inv inv q c l =
  maxa linorder_int
    (sup_set equal_int (insert equal_int zero_inta bot_set)
      (sup_seta equal_int
        (image
          (fn (x, d) =>
            (if equal_nata x c then insert equal_int d bot_set else bot_set))
          (collect_clock_pairs (nth (nth inv q) l)))));

fun bound_g max_steps inv trans prog q c l =
  maxa linorder_int
    (sup_set equal_int (insert equal_int zero_inta bot_set)
      (sup_seta equal_int
        (image
          (fn (x, d) =>
            (if equal_nata x c then insert equal_int d bot_set else bot_set))
          (clkp_seta max_steps inv trans prog q l))));

fun bound max_steps inv trans prog q c l =
  max ord_int (bound_g max_steps inv trans prog q c l) (bound_inv inv q c l);

fun w max_steps inv trans prog q c la l =
  (if equal_nata la (n trans q)
    then uminus_inta (bound max_steps inv trans prog q c l) else zero_inta);

fun v trans q = (fn v => less_eq_nat v (n trans q));

fun g max_steps inv trans prog q c =
  Gen_g_impl_ext
    (v trans q, e trans prog q c, [n trans q], w max_steps inv trans prog q c);

fun local_ceiling max_steps inv trans prog q c =
  let
    val a =
      calc_shortest_scc_paths (plus_int, zero_int, ord_int)
        (g max_steps inv trans prog q c) (n trans q);
  in
    map (fn aa => (case aa of NONE => zero_inta | SOME ab => uminus_inta ab)) a
  end;

fun k p m max_steps inv trans prog =
  app rev
    (fold (fn q => fn xs =>
            app (fn x => rev x :: xs)
              (fold (fn l => fn xsa =>
                      app (fn x => (zero_inta :: rev x) :: xsa)
                        (fold (fn c =>
                                (fn a =>
                                  nth (local_ceiling max_steps inv trans prog q
c)
                                    l ::
                                    a))
                          (upt one_nata (suc m)) []))
                (upt zero_nata (n trans q)) []))
      (upt zero_nata p) []);

end; (*struct Model_Checker*)

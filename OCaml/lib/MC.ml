open JANI_Model_Checker
open Ppx_yojson_conv_lib

(** Extend Z with support for `ppx_deriving` and `ppx_show`. *)
module Z = struct
  include Z

  let t_of_yojson = function
  | `Int i -> Z.of_int i
  | `Intlit s -> Z.of_string s
  | s -> raise (Yojson_conv.of_yojson_error "Z.t_of_yojson: invalid argument" s)

  let yojson_of_t x: Yojson.Safe.t = `Int (Z.to_int x)

  let show = Z.to_string

  let pp ppf i = Format.pp_print_string ppf (show i)

end

(** Extend the exported Munta code with some utilities. *)

include Model_Checker

let of_int i = Int_of_integer (Z.of_int i)

let to_int i = Z.to_int (integer_of_int i)

let nat_of_int i = nat_of_integer (Z.of_int i)

let int_of_nat i = Z.to_int (integer_of_nat i)

let nat_of_yojson x = nat_of_int (int_of_yojson x)
let yojson_of_nat x = yojson_of_int (int_of_nat x)


(** Copy the JANI "record" definitions to derive utility functions.
    Unforunately, I didn't get `ppx_import` to work to reduce the boilerplate.
*)

type int = Model_Checker.int = Int_of_integer of Z.t
[@@deriving yojson]

type 'a bounded_type_ext = 'a Model_Checker.bounded_type_ext
  = Bounded_type_ext of int * int * 'a
  [@@deriving yojson]

type typea = Model_Checker.typea = TBounded of unit bounded_type_ext | TClock
  [@@deriving yojson]
type ('a, 'b) bexp = ('a, 'b)  Model_Checker.bexp =
  True | Not of ('a, 'b) bexp |
  And of ('a, 'b) bexp * ('a, 'b) bexp | Or of ('a, 'b) bexp * ('a, 'b) bexp |
  Imply of ('a, 'b) bexp * ('a, 'b) bexp | Eq of ('a, 'b) exp * ('a, 'b) exp |
  Lea of ('a, 'b) exp * ('a, 'b) exp | Lta of ('a, 'b) exp * ('a, 'b) exp |
  Ge of ('a, 'b) exp * ('a, 'b) exp | Gt of ('a, 'b) exp * ('a, 'b) exp
and ('a, 'b) exp = ('a, 'b)  Model_Checker.exp = Const of 'b | Var of 'a |
  If_then_else of ('a, 'b) bexp * ('a, 'b) exp * ('a, 'b) exp |
  Binop of ('b -> 'b -> 'b) * ('a, 'b) exp * ('a, 'b) exp |
  Unop of ('b -> 'b) * ('a, 'b) exp
  [@@deriving yojson]
type 'a assignment_ext = 'a Model_Checker.assignment_ext =
  Assignment_ext of string * (string, int) exp * nat * string option * 'a
  [@@deriving yojson]
type 'a destination_ext = 'a Model_Checker.destination_ext =
  Destination_ext of
    string * unit option * unit assignment_ext list * string option * 'a
  [@@deriving yojson]
type 'a edge_ext = 'a Model_Checker.edge_ext =
  Edge_ext of
    string * string option * unit option * (string, int) bexp *
      unit destination_ext list * string option * 'a
  [@@deriving yojson]
type 'a sync_ext = 'a Model_Checker.sync_ext =
  Sync_ext of (string option) list * string option * string option * 'a
  [@@deriving yojson]
type 'a variable_declaration_ext = 'a Model_Checker.variable_declaration_ext =
  Variable_declaration_ext of
    string * typea * bool * (string, int) exp option * 'a
  [@@deriving yojson]
type 'a element_ext = 'a Model_Checker.element_ext =
  Element_ext of string * string list * string option * 'a
  [@@deriving yojson]
type 'a composition_ext = 'a Model_Checker.composition_ext =
  Composition_ext of
    unit element_ext list * unit sync_ext list * string option * 'a
  [@@deriving yojson]
type 'a transient_value_ext = 'a Model_Checker.transient_value_ext =
  Transient_value_ext of string * (string, int) exp * string option * 'a
  [@@deriving yojson]
type 'a location_ext = 'a Model_Checker.location_ext =
  Location_ext of
    string * (string, int) bexp option * unit transient_value_ext list * 'a
  [@@deriving yojson]
type 'a automaton_ext = 'a Model_Checker.automaton_ext =
  Automaton_ext of
    string * unit variable_declaration_ext list * unit option *
      unit location_ext list * string list * unit edge_ext list *
      string option * 'a
  [@@deriving yojson]
type 'a action_ext = 'a Model_Checker.action_ext =
  Action_ext of string * string option * 'a
  [@@deriving yojson]
type 'a model_ext = 'a Model_Checker.model_ext =
  Model_ext of
    int * string * unit * unit * unit option * unit action_ext list *
      unit list * unit variable_declaration_ext list * unit option * unit *
      unit automaton_ext list * unit composition_ext * 'a
  [@@deriving yojson]
type 'a result = 'a Model_Checker.result =
  Result of 'a | Error of string list
  [@@deriving yojson]
type ('a, 'b, 'c, 'd) sexp = ('a, 'b, 'c, 'd) Model_Checker.sexp =
  Truea | Nota of ('a, 'b, 'c, 'd) sexp |
  Anda of ('a, 'b, 'c, 'd) sexp * ('a, 'b, 'c, 'd) sexp |
  Ora of ('a, 'b, 'c, 'd) sexp * ('a, 'b, 'c, 'd) sexp |
  Implya of ('a, 'b, 'c, 'd) sexp * ('a, 'b, 'c, 'd) sexp | Eqa of 'c * 'd |
  Leb of 'c * 'd | Ltb of 'c * 'd | Gea of 'c * 'd | Gta of 'c * 'd |
  Loc of 'a * 'b
  [@@deriving yojson]
type ('a, 'b, 'c, 'd) formula = ('a, 'b, 'c, 'd) Model_Checker.formula =
  EX of ('a, 'b, 'c, 'd) sexp |
  EG of ('a, 'b, 'c, 'd) sexp | AX of ('a, 'b, 'c, 'd) sexp |
  AG of ('a, 'b, 'c, 'd) sexp |
  Leadsto of ('a, 'b, 'c, 'd) sexp * ('a, 'b, 'c, 'd) sexp
  [@@deriving yojson]

let yojson_of_unit (): Yojson.Safe.t = `Tuple []

let show_model model =
  yojson_of_model_ext yojson_of_unit model
  |> Yojson.Safe.pretty_to_string

let yojson_of_formula' =
  yojson_of_formula
    yojson_of_nat yojson_of_string yojson_of_string yojson_of_int

let show_formula formula =
  yojson_of_formula' formula |> Yojson.Safe.pretty_to_string
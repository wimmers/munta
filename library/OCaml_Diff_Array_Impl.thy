theory OCaml_Diff_Array_Impl
  imports Collections.Diff_Array
begin

code_printing code_module "STArray" \<rightharpoonup>
  (OCaml)
\<open>
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

let new_array (a:'a) (n:Z.t) = array (Z.to_int n, a);;

let array_length (a:'a array_type) = Z.of_int (length a);;

let array_get (a:'a array_type) (i:Z.t) = sub (a, Z.to_int i);;

let array_set (a:'a array_type) (i:Z.t) (e:'a) = update (a, Z.to_int i, e);;

let array_of_list (xs:'a list) = fromList xs;;

let array_grow (a:'a array_type) (i:Z.t) (x:'a) = grow (a, Z.to_int i, x);;

let array_shrink (a:'a array_type) (sz:Z.t) = shrink (a,Z.to_int sz);;

let array_get_oo (d:'a) (a:'a array_type) (i:Z.t) =
  try sub (a,Z.to_int i) with Invalid_argument _ -> d

let array_set_oo (d:(unit->'a array_type)) (a:'a array_type) (i:Z.t) (e:'a) =
  try update (a, Z.to_int i, e) with Invalid_argument _ -> d ()

end;;

end;;
\<close>

code_printing
  type_constructor array \<rightharpoonup> (OCaml) "_/ FArray.IsabelleMapping.array'_type"
| constant Array \<rightharpoonup> (OCaml) "FArray.IsabelleMapping.array'_of'_list"
| constant new_array' \<rightharpoonup> (OCaml) "FArray.IsabelleMapping.new'_array"
| constant array_length' \<rightharpoonup> (OCaml) "FArray.IsabelleMapping.array'_length"
| constant array_get' \<rightharpoonup> (OCaml) "FArray.IsabelleMapping.array'_get"
| constant array_set' \<rightharpoonup> (OCaml) "FArray.IsabelleMapping.array'_set"
| constant array_grow' \<rightharpoonup> (OCaml) "FArray.IsabelleMapping.array'_grow"
| constant array_shrink' \<rightharpoonup> (OCaml) "FArray.IsabelleMapping.array'_shrink"
| constant array_of_list \<rightharpoonup> (OCaml) "FArray.IsabelleMapping.array'_of'_list"
| constant array_get_oo' \<rightharpoonup> (OCaml) "FArray.IsabelleMapping.array'_get'_oo"
| constant array_set_oo' \<rightharpoonup> (OCaml) "FArray.IsabelleMapping.array'_set'_oo"

end

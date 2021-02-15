(* Basic operators for Tuples in mini-cic *)

open Constr
open MiniCic.CoreType

exception OutOfTupleBoundary

let is_const_fst c = Constr.compare c fst_const = 0

let is_const_snd c = Constr.compare c snd_const = 0

let mk_prod_type types =
  List.fold_right
    (fun c acc -> mkApp (prod_type, [|c; acc|]))
    (List.tl types) (List.hd types)

let mk_pair eles =
  List.fold_right
    (fun (c, t) (c', t') ->
      ( mkApp (CoreType.pair, [|t; t'; c; c'|])
      , mkApp (CoreType.prod_type, [|t; t'|]) ) )
    (List.tl eles) (List.hd eles)

(* Select the kth elements of e (t_1 * t2 * t3 * tk ....) *)
let rec mk_select eles k e : Constr.t =
  Js.log (Printf.sprintf "k is %d" k) ;
  match eles with
  | [] -> assert false
  | [_] when k == 0 -> e
  | (_, hd) :: tl when k == 0 ->
      let types = List.map (fun c -> snd c) tl in
      mkApp (CoreType.fst_const, [|hd; mk_prod_type types; e|])
  | [(_, hd); (_, tl)] when k == 1 -> mkApp (CoreType.snd_const, [|hd; tl; e|])
  | (_, hd) :: tl when k < List.length eles ->
      let e = mk_select tl (k - 1) e in
      let types = List.map (fun c -> snd c) tl in
      mkApp (CoreType.snd_const, [|hd; mk_prod_type types; e|])
  | _ -> assert false

let is_select c =
  match c with
  | App (op, [|_; _; _|]) when is_const_snd op || is_const_snd op -> true
  | _ -> false

(* Parse the select of a tuple, return idx, type, and tuple constr *)
let parse_select c =
  let rec aux c idx =
    match c with
    | App (op, [|t; _; inner|]) when is_const_fst op -> (idx, t, inner)
    | App (op, [|_; t; inner|]) when is_const_snd op ->
        if is_select c then aux inner (idx + 1) else (idx + 1, t, inner)
    | _ -> assert false
  in
  aux c 0

let type_list_of_tuple_type c =
  let rec aux c =
    match c with
    | App (op, [|t; tl|]) when Constr.compare op prod_type = 0 -> t :: aux tl
    | _ -> [c]
  in
  aux c

let type_list_of_tuple_body env c =
  let t = Retype.type_of env c in
  type_list_of_tuple_type t

(* Basic operators for Tuples in mini-cic *)

exception OutOfTupleBoundary

let mk_prod_type types =
  List.fold_right (fun c acc -> Constr.mkApp (CoreType.prod_type, [|c; acc|]))
    (List.tl types) (List.hd types)

let mk_pair eles =
  List.fold_right (fun (c,t) (c', t') ->
    Constr.mkApp (CoreType.pair, [|t; t'; c; c'|])
    , Constr.mkApp (CoreType.prod_type, [|t; t'|])
  ) (List.tl eles) (List.hd eles)

(* Select the kth elements of e (t_1 * t2 * t3 * tk ....) *)
let rec mk_select eles k e : Constr.t =
  Js.log (Printf.sprintf "k is %d" k);
  match eles with
  | [] -> assert false
  | [e, _] when k == 0 -> e
  | (_, hd) :: tl when k == 0 ->
    let types = List.map (fun c -> snd c) tl in
    Constr.mkApp (CoreType.fst_const, [|hd;mk_prod_type types;e|])
  | [(_, hd); (_, tl)] when k == 1 ->
    Constr.mkApp (CoreType.snd_const, [|hd;tl;e|])
  | (_, hd) :: tl when k < List.length eles ->
      let e = mk_select tl (k-1) e in
      let types = List.map (fun c -> snd c) tl in
      Constr.mkApp (CoreType.snd_const, [|hd;mk_prod_type types;e|])
  | _ -> assert false

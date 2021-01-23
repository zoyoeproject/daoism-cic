open Constr

let ind_to_string ind =
  match ind with
  | (mutind, i) ->
    "(" ^ Names.MutInd.to_string mutind ^ ", " ^ string_of_int i ^ ")"

let rec to_string c =
  match c with
  | Rel i -> "Rel " ^ string_of_int i
  | Var n -> "Var " ^ Names.Id.to_string n
  | Prod (name, typ, body) ->
    "Prod(" ^ Names.Name.to_string name ^ ", "
    ^ to_string typ ^ ", " ^ to_string body ^ ")"
  | Lambda(name, typ, body) ->
    "Lambda (" ^ Names.Name.to_string name ^ ", "
    ^ to_string typ ^ ", " ^ to_string body ^ ")"
  | LetIn(name, typ, argbody, body) ->
    "Let " ^ Names.Name.to_string name ^ ": "
    ^ to_string typ ^ " = " ^ to_string argbody
    ^ " in " ^ to_string body
  | App(func, args) ->
    "App(" ^ to_string func ^ ", [|"
    ^ Array.fold_left(fun s t -> s ^ to_string t ^ "; ") "" args
    ^ "|]"
  | Const(con, i) ->
    "Const(" ^ Names.Constant.to_string con ^ ", " ^ string_of_int i ^ ")"
  | Ind(ind, i') ->
    "Ind(" ^ ind_to_string ind
    ^ ", " ^ string_of_int i' ^ ")"
  | Construct((ind, i), i') ->
    "Construct(" ^ "(" ^ ind_to_string ind ^ ", " ^ string_of_int i ^ ")"
    ^ ", " ^ string_of_int i' ^ ")"
  | Case(_, typ, cond, args) ->
    (* TODO! add the printer of ci_info *)
    "Case(" ^"ci_info" ^ ", " ^ to_string typ ^ ", "
    ^ to_string cond ^ ", [|" ^
    Array.fold_left (fun s t -> s ^ to_string t ^ "; ") "" args
    ^ "|])"
  | Int i -> "Int " ^ string_of_int i
  | Float f -> "Float " ^ Js.Float.toString f
  | Fix _ | Evar _ -> assert false




open Names

module ConstantMap =  Map.Make(Constant)

type global_entry = {
  entry_body: Constr.t option;
  entry_type: Constr.t;
}

let mk_entry a b = {entry_body=a; entry_type=b}

type env = {
  env_globals : global_entry ConstantMap.t;
  env_named_context : Constr.named_declaration Id.Map.t;
  env_rel_context   : Constr.rel_context;
  env_nb_rel: int;
}

let lookup_constant env c = ConstantMap.find c env.env_globals

let add_constant c body t env = {
    env with env_globals = ConstantMap.add c (mk_entry body t) env.env_globals
  }

let empty_env = {
  env_globals = ConstantMap.empty;
  env_named_context = Id.Map.empty;
  env_rel_context = [];
  env_nb_rel = 0;
}

let push_rel d env =
    { env with
      env_rel_context = Context.Rel.add d env.env_rel_context;
      env_nb_rel = env.env_nb_rel + 1 }

let lookup_rel n env =
  try
    List.nth env.env_rel_context (n - 1)
  with Invalid_argument _ ->
    raise Not_found

(* Named context *)
let push_named d env = {
  env with env_named_context =
    Id.Map.add (Context.Named.Declaration.get_id d) d env.env_named_context
  }

let lookup_named id env =
  (Id.Map.find id env.env_named_context)

(*

let lookup_named_ctxt id ctxt =
  fst (Id.Map.find id ctxt.env_named_map)

let fold_constants f env acc =
  Cmap_env.fold (fun c (body,_) acc -> f c body acc) env.env_globals.Globals.constants acc

let fold_inductives f env acc =
  Mindmap_env.fold (fun c (body,_) acc -> f c body acc) env.env_globals.Globals.inductives acc

(* Global constants *)

let lookup_constant_key kn env =
  Cmap_env.get kn env.env_globals.Globals.constants

let lookup_constant kn env =
  fst (lookup_constant_key kn env)

let mem_constant kn env = Cmap_env.mem kn env.env_globals.Globals.constants

let named_context env = env.env_named_context.env_named_ctx
let named_context_val env = env.env_named_context
let rel_context env = env.env_rel_context.env_rel_ctx
let opaque_tables env = env.indirect_pterms
let set_opaque_tables env indirect_pterms = { env with indirect_pterms }

let empty_context env =
  match env.env_rel_context.env_rel_ctx, env.env_named_context.env_named_ctx with
  | [], [] -> true
  | _ -> false

(* Rel context *)
let evaluable_rel n env =
  is_local_def (lookup_rel n env)

let nb_rel env = env.env_nb_rel

let push_rel_context ctxt x = Context.Rel.fold_outside push_rel ctxt ~init:x

let push_rec_types (lna,typarray,_) env =
  let ctxt = Array.map2_i (fun i na t -> LocalAssum (na, lift i t)) lna typarray in
  Array.fold_left (fun e assum -> push_rel assum e) env ctxt

let fold_rel_context f env ~init =
  let rec fold_right env =
    match match_rel_context_val env.env_rel_context with
    | None -> init
    | Some (rd, _, rc) ->
        let env =
          { env with
            env_rel_context = rc;
            env_nb_rel = env.env_nb_rel - 1 } in
        f env rd (fold_right env)
  in fold_right env

(* Named context *)

let named_context_of_val c = c.env_named_ctx

let ids_of_named_context_val c = Id.Map.domain c.env_named_map

let empty_named_context = Context.Named.empty

let push_named_context = List.fold_right push_named

let val_of_named_context ctxt =
  List.fold_right push_named_context_val ctxt empty_named_context_val


let eq_named_context_val c1 c2 =
   c1 == c2 || Context.Named.equal Constr.equal (named_context_of_val c1) (named_context_of_val c2)

(* A local const is evaluable if it is defined  *)

let named_type id env =
  let open Context.Named.Declaration in
  get_type (lookup_named id env)

let named_body id env =
  let open Context.Named.Declaration in
  get_value (lookup_named id env)

let evaluable_named id env =
  match named_body id env with
  | Some _      -> true
  | _          -> false

let reset_with_named_context ctxt env =
  { env with
    env_named_context = ctxt;
    env_rel_context = empty_rel_context_val;
    env_nb_rel = 0 }

let reset_context = reset_with_named_context empty_named_context_val

let pop_rel_context n env =
  let rec skip n ctx =
    if Int.equal n 0 then ctx
    else match match_rel_context_val ctx with
    | None -> invalid_arg "List.skipn"
    | Some (_, _, ctx) -> skip (pred n) ctx
  in
  let ctxt = env.env_rel_context in
  { env with
    env_rel_context = skip n ctxt;
    env_nb_rel = env.env_nb_rel - n }

let fold_named_context f env ~init =
  let rec fold_right env =
    match match_named_context_val env.env_named_context with
    | None -> init
    | Some (d, _v, rem) ->
        let env =
          reset_with_named_context rem env in
        f env d (fold_right env)
  in fold_right env

let fold_named_context_reverse f ~init env =
  Context.Named.fold_inside f ~init:init (named_context env)

*)

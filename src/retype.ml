module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

open Names
open Constr

type retype_error =
  | NotASort
  | NotAType
  | BadVariable of Id.t
  | NonFunctionalConstruction

let retype_error_to_string = function
  | NotASort -> "Not a sort"
  | NotAType -> "Not a type"
  | BadVariable id -> "Bad variable " ^ (Id.to_string id)
  | NonFunctionalConstruction -> "NonFunctionConstruction"

exception RetypeError of retype_error

let retype_error re = raise (RetypeError re)

let () =
  Printexc.register_printer
    (function
      | RetypeError err -> Some (retype_error_to_string err)
      | _ -> None (* for other exceptions *)
    )

let type_of_var env id =
  try NamedDecl.get_type (Env.lookup_named id env)
  with Not_found -> retype_error (BadVariable id)

let type_of_constant env c =
  let cpair = Env.lookup_constant env c in
  cpair.entry_type

let rec subst_type env typ = function
  | [] -> typ
  | h::rest ->
      match typ with (* whd_all env sigma typ *)
        | Prod (_,_,c2) -> subst_type env (Vars.subst1 h c2) rest
        | _ -> retype_error NonFunctionalConstruction

let rec type_of env cstr =
  match cstr with
  | Rel n ->
      let ty = RelDecl.get_type (Env.lookup_rel n env) in
      lift n ty
  | Var id -> type_of_var env id
  | Const (cst, _) -> type_of_constant env cst
  | Ind _ (*ind, u*) -> assert false
  | Construct _ (*cstr, u*) -> assert false
  | Case (_, p, _, _) -> (* Not implemented due to recursive type *)
    p (* Should be mkApp p XXX *)
  | Lambda (name,c1,c2) ->
        mkProd (name, c1, type_of (Env.push_rel (LocalAssum (name,c1)) env) c2)
  | LetIn (name,b,c1,c2) ->
       Vars.subst1 b (type_of (Env.push_rel (LocalDef (name,b,c1)) env) c2)
  | App(f,args) -> subst_type env (type_of env f) (Array.to_list args)
  | Prod _ -> assert false
  | Int _ ->  CoreType.int_type
  | Float _ -> CoreType.float_type
  | _ -> assert false

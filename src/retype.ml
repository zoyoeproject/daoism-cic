module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

open Names

type retype_error =
  | NotASort
  | NotAType
  | BadVariable of Id.t

exception RetypeError of retype_error

let retype_error re = raise (RetypeError re)

let type_of_var env id =
  try NamedDecl.get_type (Env.lookup_named id env)
  with Not_found -> retype_error (BadVariable id)

let type_of_constant env c =
  let cpair = Env.lookup_constant env c in
  cpair.entry_type

(*
let type_of env =
  let rec type_of env cstr =
    match EConstr.kind sigma cstr with
    | Rel n ->
        let ty = RelDecl.get_type (lookup_rel n env) in
        lift n ty
    | Var id -> type_of_var env id
    | Const (cst, u) -> EConstr.of_constr (rename_type_of_constant env (cst, EInstance.kind sigma u))
    | Evar ev -> existential_type sigma ev
    | Ind (ind, u) -> EConstr.of_constr (rename_type_of_inductive env (ind, EInstance.kind sigma u))
    | Construct (cstr, u) -> EConstr.of_constr (rename_type_of_constructor env (cstr, EInstance.kind sigma u))
    | Case (_,p,c,lf) -> assert false (* Not implemented due to recursive type *)
    | Lambda (name,c1,c2) ->
          mkProd (name, c1, type_of (push_rel (LocalAssum (name,c1)) env) c2)
    | LetIn (name,b,c1,c2) ->
         subst1 b (type_of (push_rel (LocalDef (name,b,c1)) env) c2)
    | Fix ((_,i),(_,tys,_)) -> tys.(i)
    | App(f,args) when Termops.is_template_polymorphic_ind env sigma f ->
        let t = type_of_global_reference_knowing_parameters env f args in
        strip_outer_cast sigma (subst_type env sigma t (Array.to_list args))
    | App(f,args) ->
        strip_outer_cast sigma
          (subst_type env sigma (type_of env f) (Array.to_list args))
    | Prod _ -> mkSort (sort_of env cstr)
    | Int _ -> Typeops.type_of_int env
    | Float _ -> Typeops.type_of_float env

*)

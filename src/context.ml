(* This file defines types and combinators regarding indexes-based and
   names-based contexts *)

(** The modules defined below represent a {e local context}
    as defined by Chapter 4 in the Reference Manual:

    A {e local context} is an ordered list of of {e local declarations}
    of names that we call {e variables}.

    A {e local declaration} of some variable can be either:
    - a {e local assumption}, or
    - a {e local definition}.
*)

open Names

(** Representation of contexts that can capture anonymous as well as non-anonymous variables.
    Individual declarations are then designated by de Bruijn indexes. *)
module Rel =
struct
  (** Representation of {e local declarations}. *)
  module Declaration =
  struct
    (* local declaration *)
    type ('constr, 'types) pt =
      | LocalAssum of Name.t * 'types            (** name, type *)
      | LocalDef of Name.t * 'constr * 'types   (** name, value, type *)

    let get_name = function
      | LocalAssum (na,_) | LocalDef (na,_,_) -> na

    (** Return [Some value] for local-declarations and [None] for local-assumptions. *)
    let get_value = function
      | LocalAssum _ -> None
      | LocalDef (_,v,_) -> Some v

    (** Return the type of the name bound by a given declaration. *)
    let get_type = function
      | LocalAssum (_,ty)
      | LocalDef (_,_,ty) -> ty

    (** Set the name that is bound by a given declaration. *)
    let set_name na = function
      | LocalAssum (_,ty) -> LocalAssum (na, ty)
      | LocalDef (_,v,ty) -> LocalDef (na, v, ty)

    (** Set the type of the bound variable in a given declaration. *)
    let set_type ty = function
      | LocalAssum (na,_) -> LocalAssum (na, ty)
      | LocalDef (na,v,_) -> LocalDef (na, v, ty)

    (** Return [true] iff a given declaration is a local assumption. *)
    let is_local_assum = function
      | LocalAssum _ -> true
      | LocalDef _ -> false

    (** Return [true] iff a given declaration is a local definition. *)
    let is_local_def = function
      | LocalAssum _ -> false
      | LocalDef _ -> true

    (** Check whether any term in a given declaration satisfies a given predicate. *)
    let exists f = function
      | LocalAssum (_, ty) -> f ty
      | LocalDef (_, v, ty) -> f v || f ty

      (** Check whether all terms in a given declaration satisfy a given predicate. *)
    let for_all f = function
      | LocalAssum (_, ty) -> f ty
      | LocalDef (_, v, ty) -> f v && f ty

    (** Check whether the two given declarations are equal. *)
    let equal eq decl1 decl2 =
      match decl1, decl2 with
      | LocalAssum (n1,ty1), LocalAssum (n2, ty2) ->
          Name.equal n1 n2 && eq ty1 ty2
      | LocalDef (n1,v1,ty1), LocalDef (n2,v2,ty2) ->
          Name.equal n1 n2 && eq v1 v2 && eq ty1 ty2
      | _ ->
          false

    (** For local assumptions, this function returns the original local assumptions.
        For local definitions, this function maps the value in the local definition. *)
    let map_value f = function
      | LocalAssum _ as decl -> decl
      | LocalDef (na, v, t) as decl ->
          let v' = f v in
          if v == v' then decl else LocalDef (na, v', t)

    (** Map the type of the name bound by a given declaration. *)
    let map_type f = function
      | LocalAssum (na, ty) as decl ->
          let ty' = f ty in
          if ty == ty' then decl else LocalAssum (na, ty')
      | LocalDef (na, v, ty) as decl ->
          let ty' = f ty in
          if ty == ty' then decl else LocalDef (na, v, ty')

    (** Map all terms in a given declaration. *)
    let map_constr f = function
      | LocalAssum (na, ty) as decl ->
          let ty' = f ty in
          if ty == ty' then decl else LocalAssum (na, ty')
      | LocalDef (na, v, ty) as decl ->
          let v' = f v in
          let ty' = f ty in
          if v == v' && ty == ty' then decl else LocalDef (na, v', ty')

    let map_constr_het f = function
      | LocalAssum (na, ty) ->
          let ty' = f ty in
          LocalAssum (na, ty')
      | LocalDef (na, v, ty) ->
          let v' = f v in
          let ty' = f ty in
          LocalDef (na, v', ty')

    (** Perform a given action on all terms in a given declaration. *)
    let iter_constr f = function
      | LocalAssum (_,ty) -> f ty
      | LocalDef (_,v,ty) -> f v; f ty

    (** Reduce all terms in a given declaration to a single value. *)
    let fold_constr f decl acc =
      match decl with
      | LocalAssum (_n,ty) -> f ty acc
      | LocalDef (_n,v,ty) -> f ty (f v acc)

    let to_tuple = function
      | LocalAssum (na, ty) -> na, None, ty
      | LocalDef (na, v, ty) -> na, Some v, ty

    let drop_body = function
      | LocalAssum _ as d -> d
      | LocalDef (na, _v, ty) -> LocalAssum (na, ty)

  end

  (** Rel-context is represented as a list of declarations.
      Inner-most declarations are at the beginning of the list.
      Outer-most declarations are at the end of the list. *)
  type ('constr, 'types) pt = ('constr, 'types) Declaration.pt list

  (** empty rel-context *)
  let empty = []

  (** Return a new rel-context enriched by with a given inner-most declaration. *)
  let add d ctx = d :: ctx

  (** Return the number of {e local declarations} in a given context. *)
  let length = List.length

  (** [extended_rel_list n Γ] builds an instance [args] such that [Γ,Δ ⊢ args:Γ]
      with n = |Δ| and with the local definitions of [Γ] skipped in
      [args]. Example: for [x:T,y:=c,z:U] and [n]=2, it gives [Rel 5, Rel 3]. *)
  let nhyps ctx =
    let open Declaration in
    let rec nhyps acc = function
      | [] -> acc
      | LocalAssum _ :: hyps -> nhyps (succ acc) hyps
      | LocalDef _ :: hyps -> nhyps acc hyps
    in
    nhyps 0 ctx

  (** Return a declaration designated by a given de Bruijn index.
      @raise Not_found if the designated de Bruijn index is not present in the designated rel-context. *)
  let rec lookup n ctx =
    match n, ctx with
    | 1, decl :: _ -> decl
    | n, _ :: sign -> lookup (n-1) sign
    | _, []        -> raise Not_found

  (** Map all terms in a given rel-context. *)
  let map f = List.map (Declaration.map_constr f)

  (** Perform a given action on every declaration in a given rel-context. *)
  let iter f = List.iter (Declaration.iter_constr f)

  (** Reduce all terms in a given rel-context to a single value.
      Innermost declarations are processed first. *)
  let fold_inside f ~init = List.fold_left f init

  (** Reduce all terms in a given rel-context to a single value.
      Outermost declarations are processed first. *)
  let fold_outside f l ~init = List.fold_right f l init

  (** Map a given rel-context to a list where each {e local assumption} is mapped to [true]
      and each {e local definition} is mapped to [false]. *)
  let to_tags l =
    let rec aux l = function
      | [] -> l
      | Declaration.LocalDef _ :: ctx -> aux (true::l) ctx
      | Declaration.LocalAssum _ :: ctx -> aux (false::l) ctx
    in aux [] l

  let drop_bodies l = List.map Declaration.drop_body l

  (** [extended_list n Γ] builds an instance [args] such that [Γ,Δ ⊢ args:Γ]
      with n = |Δ| and with the {e local definitions} of [Γ] skipped in
      [args]. Example: for [x:T, y:=c, z:U] and [n]=2, it gives [Rel 5, Rel 3]. *)
  let to_extended_list mk n l =
    let rec reln l p = function
      | Declaration.LocalAssum _ :: hyps -> reln (mk (n+p) :: l) (p+1) hyps
      | Declaration.LocalDef _ :: hyps -> reln l (p+1) hyps
      | [] -> l
    in
    reln [] 1 l

  (** [extended_vect n Γ] does the same, returning instead an array. *)
  let to_extended_vect mk n hyps = Array.of_list (to_extended_list mk n hyps)
end

(** This module represents contexts that can capture non-anonymous variables.
    Individual declarations are then designated by the identifiers they bind. *)
module Named =
struct
  (** Representation of {e local declarations}. *)
  module Declaration =
  struct
    (** local declaration *)
    type ('constr, 'types) pt =
      | LocalAssum of Id.t * 'types             (** identifier, type *)
      | LocalDef of Id.t * 'constr * 'types    (** identifier, value, type *)

    let get_id = function
      | LocalAssum (id,_) | LocalDef (id,_,_) -> id

    (** Return [Some value] for local-declarations and [None] for local-assumptions. *)
    let get_value = function
      | LocalAssum _ -> None
      | LocalDef (_,v,_) -> Some v

    (** Return the type of the name bound by a given declaration. *)
    let get_type = function
      | LocalAssum (_,ty)
      | LocalDef (_,_,ty) -> ty

    (** Set the identifier that is bound by a given declaration. *)
    let set_name na =
      function
      | LocalAssum (_,ty) -> LocalAssum (na, ty)
      | LocalDef (_, v, ty) -> LocalDef (na, v, ty)

    (** Set the type of the bound variable in a given declaration. *)
    let set_type ty = function
      | LocalAssum (id,_) -> LocalAssum (id, ty)
      | LocalDef (id,v,_) -> LocalDef (id, v, ty)

    (** Return [true] iff a given declaration is a local assumption. *)
    let is_local_assum = function
      | LocalAssum _ -> true
      | LocalDef _ -> false

    (** Return [true] iff a given declaration is a local definition. *)
    let is_local_def = function
      | LocalDef _ -> true
      | LocalAssum _ -> false

    (** Check whether any term in a given declaration satisfies a given predicate. *)
    let exists f = function
      | LocalAssum (_, ty) -> f ty
      | LocalDef (_, v, ty) -> f v || f ty

    (** Check whether all terms in a given declaration satisfy a given predicate. *)
    let for_all f = function
      | LocalAssum (_, ty) -> f ty
      | LocalDef (_, v, ty) -> f v && f ty

    (** Check whether the two given declarations are equal. *)
    let equal eq decl1 decl2 =
      match decl1, decl2 with
      | LocalAssum (id1, ty1), LocalAssum (id2, ty2) ->
          Id.equal id1 id2 && eq ty1 ty2
      | LocalDef (id1, v1, ty1), LocalDef (id2, v2, ty2) ->
          Id.equal id1 id2 && eq v1 v2 && eq ty1 ty2
      | _ ->
          false

    (** For local assumptions, this function returns the original local assumptions.
        For local definitions, this function maps the value in the local definition. *)
    let map_value f = function
      | LocalAssum _ as decl -> decl
      | LocalDef (na, v, t) as decl ->
          let v' = f v in
          if v == v' then decl else LocalDef (na, v', t)

    (** Map the type of the name bound by a given declaration. *)
    let map_type f = function
      | LocalAssum (id, ty) as decl ->
          let ty' = f ty in
          if ty == ty' then decl else LocalAssum (id, ty')
      | LocalDef (id, v, ty) as decl ->
          let ty' = f ty in
          if ty == ty' then decl else LocalDef (id, v, ty')

    (** Map all terms in a given declaration. *)
    let map_constr f = function
      | LocalAssum (id, ty) as decl ->
          let ty' = f ty in
          if ty == ty' then decl else LocalAssum (id, ty')
      | LocalDef (id, v, ty) as decl ->
          let v' = f v in
          let ty' = f ty in
          if v == v' && ty == ty' then decl else LocalDef (id, v', ty')

    (** Perform a given action on all terms in a given declaration. *)
    let iter_constr f = function
      | LocalAssum (_, ty) -> f ty
      | LocalDef (_, v, ty) -> f v; f ty

    (** Reduce all terms in a given declaration to a single value. *)
    let fold_constr f decl a =
      match decl with
      | LocalAssum (_, ty) -> f ty a
      | LocalDef (_, v, ty) -> a |> f v |> f ty

    let to_tuple = function
      | LocalAssum (id, ty) -> id, None, ty
      | LocalDef (id, v, ty) -> id, Some v, ty

    let of_tuple = function
      | id, None, ty -> LocalAssum (id, ty)
      | id, Some v, ty -> LocalDef (id, v, ty)

    let drop_body = function
      | LocalAssum _ as d -> d
      | LocalDef (id, _v, ty) -> LocalAssum (id, ty)

    let of_rel_decl f = function
      | Rel.Declaration.LocalAssum (na,t) ->
          LocalAssum (f na, t)
      | Rel.Declaration.LocalDef (na,v,t) ->
          LocalDef (f na, v, t)

    let to_rel_decl =
      function
      | LocalAssum (id,t) ->
          Rel.Declaration.LocalAssum (Names.Name.mk_name id, t)
      | LocalDef (id,v,t) ->
          Rel.Declaration.LocalDef (Names.Name.mk_name id,v,t)
  end

  (** Named-context is represented as a list of declarations.
      Inner-most declarations are at the beginning of the list.
      Outer-most declarations are at the end of the list. *)
  type ('constr, 'types) pt = ('constr, 'types) Declaration.pt list

  (** empty named-context *)
  let empty = []

  (** empty named-context *)
  let add d ctx = d :: ctx

  (** Return the number of {e local declarations} in a given named-context. *)
  let length = List.length

(** Return a declaration designated by a given identifier
    @raise Not_found if the designated identifier is not present in the designated named-context. *)
  let rec lookup id = function
    | decl :: _ when Id.equal id (Declaration.get_id decl) -> decl
    | _ :: sign -> lookup id sign
    | [] -> raise Not_found

  (** Map all terms in a given named-context. *)
  let map f = List.map (Declaration.map_constr f)

  (** Perform a given action on every declaration in a given named-context. *)
  let iter f = List.iter (Declaration.iter_constr f)

  (** Reduce all terms in a given named-context to a single value.
      Innermost declarations are processed first. *)
  let fold_inside f ~init = List.fold_left f init

  (** Reduce all terms in a given named-context to a single value.
      Outermost declarations are processed first. *)
  let fold_outside f l ~init = List.fold_right f l init

  (** Return the set of all identifiers bound in a given named-context. *)
  let to_vars l =
    List.fold_left (fun accu decl -> Id.Set.add (Declaration.get_id decl) accu) Id.Set.empty l

  let drop_bodies l = List.map Declaration.drop_body l

end

module Id =
struct
  type t = string

  let equal = String.equal

  let compare = String.compare

  let of_string s = s

  let to_string id = id

  module Set = Set.Make (String)
  module Map = Map.Make (String)

end

module Name =
struct
  exception GetIdOfAnonymous
  type t = Anonymous     (** anonymous identifier *)
         | Name of Id.t  (** non-anonymous identifier *)

  let mk_name id =
    Name id

  let get_id = function
    | Anonymous -> raise GetIdOfAnonymous
    | Name id -> id

  let is_anonymous = function
    | Anonymous -> true
    | Name _ -> false

  let is_name x = not (is_anonymous x)

  let compare n1 n2 = match n1, n2 with
    | Anonymous, Anonymous -> 0
    | Name id1, Name id2 -> Id.compare id1 id2
    | Anonymous, Name _ -> -1
    | Name _, Anonymous -> 1

  let equal n1 n2 = match n1, n2 with
    | Anonymous, Anonymous -> true
    | Name id1, Name id2 -> String.equal id1 id2
    | _ -> false

  let to_string = function
    | Anonymous -> "_"
    | Name id -> Id.to_string id

end

type variable = Id.t

type module_ident = Id.t

let default_module_name = "LOCAL"

let list_compare compare t1 t2 =
  let rec rec_compare t1 t2 = match t1, t2 with
  | [], [] -> 0
  | _, [] -> 1
  | [], _ -> -1
  | t::tl, t'::tl' ->
    let c = compare t t' in
    if compare t t' = 0 then
      rec_compare tl tl'
    else c
  in rec_compare t1 t2



module DirPath =
struct
  type t = module_ident list

  let compare = list_compare Id.compare
  let equal a b = (compare a b = 0)

  let make x = x
  let repr x = x

  let empty = []

  let is_empty x = match x with
    | [] -> true
    | _ -> false

  let to_string = function
    | [] -> "<>"
    | sl -> String.concat "." (List.rev_map Id.to_string sl)

  let initial = [default_module_name]

end

module Label =
struct
  include Id
  let make = Id.of_string
  let of_id id = id
  let to_id id = id
end

(** {6 The module part of the kernel name } *)

module ModPath = struct

  type t =
    | MPfile of DirPath.t
    | MPdot of t * Label.t

  type module_path = t

  let rec to_string = function
    | MPfile sl -> DirPath.to_string sl
    | MPdot (mp,l) -> to_string mp ^ "." ^ Label.to_string l

  (** we compare labels first if both are MPdots *)
  let rec compare mp1 mp2 =
    if mp1 == mp2 then 0
    else match mp1, mp2 with
      | MPfile p1, MPfile p2 -> DirPath.compare p1 p2
      | MPdot (mp1, l1), MPdot (mp2, l2) ->
        let c = String.compare l1 l2 in
        if not (c == 0) then c
        else compare mp1 mp2
      | MPfile _, _ -> -1
      | MPdot _, _ -> 1

  let initial = MPfile DirPath.initial

  let rec dp = function
  | MPfile sl -> sl
  | MPdot (mp,_l) -> dp mp

end

module KerName = struct

  type t = {
    modpath : ModPath.t;
    knlabel : Label.t;
  }

  type kernel_name = t

  let make modpath knlabel = {modpath; knlabel;}
  let repr kn = (kn.modpath, kn.knlabel)

  let modpath kn = kn.modpath
  let label kn = kn.knlabel

  let to_string_gen mp_to_string kn =
    mp_to_string kn.modpath ^ "." ^ Label.to_string kn.knlabel

  let to_string kn = to_string_gen ModPath.to_string kn

  let compare (kn1 : kernel_name) (kn2 : kernel_name) =
    if kn1 == kn2 then 0
    else
      let c = String.compare kn1.knlabel kn2.knlabel in
      if not (c = 0) then c
      else
        ModPath.compare kn1.modpath kn2.modpath

end

module Constant = KerName
module MutInd = KerName

(** Designation of a (particular) inductive type. *)
type inductive = MutInd.t      (* the name of the inductive type *)
               * int           (* the position of this inductive type
                                  within the block of mutually-recursive inductive types.
                                  BEWARE: indexing starts from 0. *)
(** Designation of a (particular) constructor of a (particular) inductive type. *)
type constructor = inductive   (* designates the inductive type *)
                 * int         (* the index of the constructor
                                  BEWARE: indexing starts from 1. *)

let compare_inductive ind1 ind2 =
  let (mut1, i1) = ind1 in
  let (mut2, i2) = ind2 in
  let c = MutInd.compare mut1 mut2 in
  if c = 0 then Int.compare i1 i2 else c

let compare_constructor c1 c2 =
  let (ind1, i1) = c1 in
  let (ind2, i2) = c2 in
  let c = compare_inductive ind1 ind2 in
  if c = 0 then Int.compare i1 i2 else c
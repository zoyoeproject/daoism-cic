module RelDecl = Context.Rel.Declaration

(*********************)
(*     Occurring     *)
(*********************)

exception LocalOccur

(* (closedn n M) raises FreeVar if a variable of height greater than n
   occurs in M, returns () otherwise *)

let closedn n c =
  let rec closed_rec n c = match c with
    | Constr.Rel m -> if m>n then raise LocalOccur
    | _ -> Constr.iter_with_binders succ closed_rec n c
  in
  try closed_rec n c; true with LocalOccur -> false

(* [closed0 M] is true iff [M] is a (de Bruijn) closed term *)

let closed0 c = closedn 0 c

(* (noccurn n M) returns true iff (Rel n) does NOT occur in term M  *)

let noccurn n term =
  let rec occur_rec n c = match c with
    | Constr.Rel m -> if m = n then raise LocalOccur
    | _ -> Constr.iter_with_binders succ occur_rec n c
  in
  try occur_rec n term; true with LocalOccur -> false

(* (noccur_between n m M) returns true iff (Rel p) does NOT occur in term M
  for n <= p < n+m *)

let noccur_between n m term =
  let rec occur_rec n c = match c with
    | Constr.Rel p -> if n<=p && p<n+m then raise LocalOccur
    | _        -> Constr.iter_with_binders succ occur_rec n c
  in
  try occur_rec n term; true with LocalOccur -> false

(*********************)
(*      Lifting      *)
(*********************)

let exliftn = Constr.exliftn
let liftn = Constr.liftn
let lift = Constr.lift

(*********************)
(*   Substituting    *)
(*********************)

(* (subst1 M c) substitutes M for Rel(1) in c
   we generalise it to (substl [M1,...,Mn] c) which substitutes in parallel
   M1,...,Mn for respectively Rel(1),...,Rel(n) in c *)

(* 1st : general case *)

type info = Closed | Open | Unknown
type 'a substituend = { mutable sinfo: info; sit: 'a }

let lift_substituend depth s =
  match s.sinfo with
    | Closed -> s.sit
    | Open -> lift depth s.sit
    | Unknown ->
      let sit = s.sit in
      if closed0 sit then
        let () = s.sinfo <- Closed in
        sit
      else
        let () = s.sinfo <- Open in
        lift depth sit

let make_substituend c = { sinfo=Unknown; sit=c }

let substn_many lamv n c =
  let lv = Array.length lamv in
  if lv = 0 then c
  else
    let rec substrec depth c = match c with
      | Constr.Rel k     ->
          if k<=depth then c
          else if k-depth <= lv then lift_substituend depth (Array.unsafe_get lamv (k-depth-1))
          else Constr.mkRel (k-lv)
      | _ -> Constr.map_with_binders succ substrec depth c in
    substrec n c

(*
let substkey = CProfile.declare_profile "substn_many";;
let substn_many lamv n c = CProfile.profile3 substkey substn_many lamv n c;;
*)

let make_subst = function
| [] -> [||]
| hd :: tl ->
  let len = List.length tl in
  let subst = Array.make (1 + len) (make_substituend hd) in
  let s = ref tl in
  for i = 1 to len do
    match !s with
    | [] -> assert false
    | x :: tl ->
      Array.unsafe_set subst i (make_substituend x);
      s := tl
  done;
  subst

(* The type of substitutions, with term substituting most recent
    binder at the head *)

type substl = Constr.t list

let substnl laml n c = substn_many (make_subst laml) n c
let substl laml c = substn_many (make_subst laml) 0 c
let subst1 lam c = substn_many [|make_substituend lam|] 0 c



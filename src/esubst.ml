(*********************)
(*      Lifting      *)
(*********************)

(* Explicit lifts and basic operations *)
(* Invariant to preserve in this module: no lift contains two consecutive
    [ELSHFT] nor two consecutive [ELLFT]. *)
type lift =
  | ELID
  | ELSHFT of lift * int (* ELSHFT(l,n) == lift of n, then apply lift l *)
  | ELLFT of int * lift  (* ELLFT(n,l)  == apply l to de Bruijn > n *)
                         (*                 i.e under n binders *)

let el_id = ELID

(* compose a relocation of magnitude n *)
let el_shft_rec n = function
  | ELSHFT(el,k) -> ELSHFT(el,k+n)
  | el           -> ELSHFT(el,n)
let el_shft n el = if n = 0 then el else el_shft_rec n el

(* cross n binders *)
let el_liftn_rec n = function
  | ELID        -> ELID
  | ELLFT(k,el) -> ELLFT(n+k, el)
  | el          -> ELLFT(n, el)
let el_liftn n el = if n = 0 then el else el_liftn_rec n el

let el_lift el = el_liftn_rec 1 el

(* relocation of de Bruijn n in an explicit lift *)
let rec reloc_rel n = function
  | ELID -> n
  | ELLFT(k,el) ->
      if n <= k then n else (reloc_rel (n-k) el) + k
  | ELSHFT(el,k) -> (reloc_rel (n+k) el)

let rec is_lift_id = function
  | ELID -> true
  | ELSHFT(e,n) -> n = 0 && is_lift_id e
  | ELLFT (_,e) -> is_lift_id e



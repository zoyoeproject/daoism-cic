open Names

let iterate =
  let rec iterate_f f n x =
    if n <= 0 then x else iterate_f f (pred n) (f x)
  in
  iterate_f

let repeat n f x =
  let rec loop i = if i <> 0 then (f x; loop (i - 1)) in loop n

type case_info =
  { ci_ind        : inductive;      (* inductive type to which belongs the value that is being matched *)
    ci_npar       : int;            (* number of parameters of the above inductive type *)
    ci_cstrs      : (int * int) array; (* fst > snd *)
  }

let compare_array f a1 a2 =
  let rec aux i size =
    if i = size
    then 0
    else
      let c = f a1.(i) a2.(i) in
      if c = 0
      then aux (i + 1) size
      else c
  in
  let s1 = Array.length a1 in
  let s2 = Array.length a2 in
  let c1 = Int.compare s1 s2 in
  if c1 = 0
  then aux 0 s1
  else c1

let compare_case_info ci1 ci2 =
  let aux (i11, i12) (i21, i22) =
    let c = Int.compare i11 i21 in
    if c = 0 then Int.compare i12 i22 else c
  in
  let c = Names.compare_inductive ci1.ci_ind ci2.ci_ind in
  let c = if c = 0 then Int.compare ci1.ci_npar ci2.ci_npar else c in
  let c = if c = 0 then compare_array aux ci1.ci_cstrs ci2.ci_cstrs else c in
  c

(* [constr array] is an instance matching definitional [named_context] in
   the same order (i.e. last argument first) *)
type 'constr pexistential = Evar.t * 'constr array

type ('constr, 'types) prec_declaration =
    Name.t array * 'types array * 'constr array

type ('constr, 'types) pfixpoint =
    (int array * int) * ('constr, 'types) prec_declaration

(* [Var] is used for named variables and [Rel] for variables as
   de Bruijn indices. *)
type t =
  | Rel       of int
  | Var       of Id.t
  | Evar      of t pexistential
  | Prod      of Name.t * t * t
  | Lambda    of Name.t * t * t
  | LetIn     of Name.t * t * t * t
  | App       of t * t array
  | Const     of (Constant.t * int)
  | Ind       of (inductive * int)
  | Construct of (constructor * int)
  | Case      of case_info * t * t * t array
  | Fix       of (t, t) pfixpoint
  | Int       of int
  | Float     of float

let to_compare_index t =
  match t with
  | Rel _ -> 0
  | Var _ -> 1
  | Evar _ -> 2
  | Prod _ -> 3
  | Lambda _ -> 4
  | LetIn _ -> 5
  | App _ -> 6
  | Const _ -> 7
  | Ind _ -> 8
  | Construct _ -> 9
  | Case _ -> 10
  | Fix _ -> 11
  | Int _ -> 12
  | Float _ -> 13

let rec compare t1 t2 =
  let compare_pexistential p1 p2 =
    let (e1, arr1) = p1 in
    let (e2, arr2) = p2 in
    let c = Evar.compare e1 e2 in
    if c = 0 then compare_array compare arr1 arr2 else c
  in
  let compare_prec_declaration p1 p2 =
    let (arr11, arr12, arr13) = p1 in
    let (arr21, arr22, arr23) = p2 in
    let c = compare_array Name.compare arr11 arr21 in
    let c = if c = 0 then compare_array compare arr12 arr22 else c in
    let c = if c = 0 then compare_array compare arr13 arr23 else c in
    c
  in
  let compare_pfixpoint p1 p2 =
    let ((arr1, i1), p1) = p1 in
    let ((arr2, i2), p2) = p2 in
    let c = compare_array Int.compare arr1 arr2 in
    let c = if c = 0 then Int.compare i1 i2 else c in
    let c = if c = 0 then compare_prec_declaration p1 p2 else c in
    c
  in
  match t1, t2 with
  | Rel i1, Rel i2 -> Int.compare i1 i2
  | Var id1, Var id2 -> Id.compare id1 id2
  | Evar e1, Evar e2 -> compare_pexistential e1 e2
  | Prod (_, t1, b1), Prod (_, t2, b2) -> compare_array compare [| t1; b1 |] [| t2; b2 |]
  | Lambda (_, t1, b1), Lambda (_, t2, b2) -> compare_array compare [| t1; b1 |] [| t2; b2 |]
  | LetIn (_, a1, t1, b1), LetIn (_, a2, t2, b2) -> compare_array compare [| a1; t1; b1 |] [| a2; t2; b2 |]
  | App (t1, arr1), App (t2, arr2) ->
    let c = compare t1 t2 in
    if c = 0 then compare_array compare arr1 arr2 else c
  | Const (con1, i1), Const (con2, i2) ->
    let c = Constant.compare con1 con2 in
    if c = 0 then Int.compare i1 i2 else c
  | Ind (ind1, i1), Ind (ind2, i2) ->
    let c = Names.compare_inductive ind1 ind2 in
    if c = 0 then Int.compare i1 i2 else c
  | Construct (c1, i1), Construct (c2, i2) ->
    let c = Names.compare_constructor c1 c2 in
    if c = 0 then Int.compare i1 i2 else c
  | Case (ci1, t1, c1, arr1), Case (ci2, t2, c2, arr2) ->
    let c = compare_case_info ci1 ci2 in
    let c = if c = 0 then compare_array compare [| t1; c1 |] [| t2; c2 |] else c in
    let c = if c = 0 then compare_array compare arr1 arr2 else c in
    c
  | Fix f1, Fix f2 -> compare_pfixpoint f1 f2
  | Int i1, Int i2 -> Int.compare i1 i2
  | Float f1, Float f2 -> Float.compare f1 f2
  | _, _ -> Int.compare (to_compare_index t1) (to_compare_index t2)

let mkRel n = Rel n

(* Constructs the product (x:t1)t2 *)
let mkProd (x,t1,t2) = Prod (x,t1,t2)

(* Constructs the abstraction [x:t1]t2 *)
let mkLambda (x,t1,t2) = Lambda (x,t1,t2)

(* Constructs [x=c_1:t]c_2 *)
let mkLetIn (x,c1,t,c2) = LetIn (x,c1,t,c2)

(* If lt = [t1; ...; tn], constructs the application (t1 ... tn) *)
(* We ensure applicative terms have at least one argument and the
   function is not itself an applicative term *)
let mkApp (f, a) =
  if Array.length a = 0 then f else
    match f with
      | App (g, cl) -> App (g, Array.append cl a)
      | _ -> App (f, a)

let map_puniverses f (x,u) = (f x, u)
let in_punivs a = (a, 0)

(* Constructs a constant *)
let mkConst c = Const (in_punivs c)
let mkConstU c = Const c

(* Constructs an existential variable *)
let mkEvar e = Evar e

(* Constructs the ith (co)inductive type of the block named kn *)
let mkInd m = Ind (in_punivs m)
let mkIndU m = Ind m

(* Constructs the jth constructor of the ith (co)inductive type of the
   block named kn. *)
let mkConstruct c = Construct (in_punivs c)
let mkConstructU c = Construct c
let mkConstructUi ((ind,u),i) = Construct ((ind,i),u)

(* Constructs the term <p>Case c of c1 | c2 .. | cn end *)
let mkCase (ci, p, c, ac) = Case (ci, p, c, ac)

(* If recindxs = [|i1,...in|]
      funnames = [|f1,...fn|]
      typarray = [|t1,...tn|]
      bodies   = [|b1,...bn|]
   then

      mkFix ((recindxs,i),(funnames,typarray,bodies))

   constructs the ith function of the block

    Fixpoint f1 [ctx1] : t1 := b1
    with     f2 [ctx2] : t2 := b2
    ...
    with     fn [ctxn] : tn := bn.

   where the length of the jth context is ij.
*)

let mkFix fix = Fix fix

(* Constructs a Variable named id *)
let mkVar id = Var id

(* Constructs a primitive integer *)
let mkInt i = Int i

(************************************************************************)
(*    kind_of_term = constructions as seen by the user                 *)
(************************************************************************)

(* User view of [constr]. For [App], it is ensured there is at
   least one argument and the function is not itself an applicative
   term *)

(**********************************************************************)
(*          Non primitive term destructors                            *)
(**********************************************************************)

(* Destructor operations : partial functions
   Raise [DestKO] if the const has not the expected form *)

exception DestKO

(* Tests if an evar *)
let isEvar c = match c with Evar _ -> true | _ -> false
(* Tests if a de Bruijn index *)
let isRel c = match c with Rel _ -> true | _ -> false
let isRelN n c = match c with Rel n' -> n = n' | _ -> false
(* Tests if a variable *)
let isVar c = match c with Var _ -> true | _ -> false
let isVarId id c = match c with Var id' -> Id.equal id id' | _ -> false
(* Tests if an inductive *)
let isInd c = match c with Ind _ -> true | _ -> false
let isProd c = match c with | Prod _ -> true | _ -> false
let isLambda c = match c with | Lambda _ -> true | _ -> false
let isLetIn c =  match c with LetIn _ -> true | _ -> false
let isApp c = match c with App _ -> true | _ -> false
let isConst c = match c with Const _ -> true | _ -> false
let isConstruct c = match c with Construct _ -> true | _ -> false
let isCase c =  match c with Case _ -> true | _ -> false
let isFix c =  match c with Fix _ -> true | _ -> false

(* Destructs a de Bruijn index *)
let destRel c = match c with
  | Rel n -> n
  | _ -> raise DestKO

(* Destructs a variable *)
let destVar c = match c with
  | Var id -> id
  | _ -> raise DestKO

(* Destructs the product (x:t1)t2 *)
let destProd c = match c with
  | Prod (x,t1,t2) -> (x,t1,t2)
  | _ -> raise DestKO

(* Destructs the abstraction [x:t1]t2 *)
let destLambda c = match c with
  | Lambda (x,t1,t2) -> (x,t1,t2)
  | _ -> raise DestKO

(* Destructs the let [x:=b:t1]t2 *)
let destLetIn c = match c with
  | LetIn (x,b,t1,t2) -> (x,b,t1,t2)
  | _ -> raise DestKO

(* Destructs an application *)
let destApp c = match c with
  | App (f,a) -> (f, a)
  | _ -> raise DestKO

(* Destructs a constant *)
let destConst c = match c with
  | Const kn -> kn
  | _ -> raise DestKO

(* Destructs an existential variable *)
let destEvar c = match c with
  | Evar (_kn, _a as r) -> r
  | _ -> raise DestKO

(* Destructs a (co)inductive type named kn *)
let destInd c = match c with
  | Ind (_kn, _a as r) -> r
  | _ -> raise DestKO

(* Destructs a constructor *)
let destConstruct c = match c with
  | Construct (_kn, _a as r) -> r
  | _ -> raise DestKO

(* Destructs a term <p>Case c of lc1 | lc2 .. | lcn end *)
let destCase c = match c with
  | Case (ci,p,c,v) -> (ci,p,c,v)
  | _ -> raise DestKO

let destFix c = match c with
  | Fix fix -> fix
  | _ -> raise DestKO

(******************************************************************)
(* Flattening and unflattening of embedded applications and casts *)
(******************************************************************)

let decompose_app c =
  match c with
    | App (f,cl) -> (f, Array.to_list cl)
    | _ -> (c,[])

let decompose_appvect c =
  match c with
    | App (f,cl) -> (f, cl)
    | _ -> (c,[||])

(****************************************************************************)
(*              Functions to recur through subterms                         *)
(****************************************************************************)

(* [fold f acc c] folds [f] on the immediate subterms of [c]
   starting from [acc] and proceeding from left to right according to
   the usual representation of the constructions; it is not recursive *)

let array_fold_left2 f init lsx lsy =
  let (acc, _) = Array.fold_left (fun (acc,i) c -> (f acc c lsy.(i), i+1)) (init, 0) lsx in
  acc

let array_fold_left2_i f init lsx lsy =
  let (acc, _) = Array.fold_left (fun (acc,i) c -> (f i acc c lsy.(i), i+1)) (init, 0) lsx in
  acc

let array_map2 f lsx lsy =
  Array.mapi (fun i c -> (f c lsy.(i))) lsx

let fold f acc c = match c with
  | (Rel _ | Var _  | Const _ | Ind _ | Construct _ | Int _ | Float _) -> acc
  | Prod (_,t,c) -> f (f acc t) c
  | Lambda (_,t,c) -> f (f acc t) c
  | LetIn (_,b,t,c) -> f (f (f acc b) t) c
  | App (c,l) -> Array.fold_left f (f acc c) l
  | Evar (_,l) -> Array.fold_left f acc l
  | Case (_,p,c,bl) -> Array.fold_left f (f (f acc p) c) bl
  | Fix (_,(_lna,tl,bl)) ->
    array_fold_left2 (fun acc t b -> f (f acc t) b) acc tl bl

(* [iter f c] iters [f] on the immediate subterms of [c]; it is
   not recursive and the order with which subterms are processed is
   not specified *)

let iter f c = match c with
  | (Rel _ | Var _   | Const _ | Ind _
    | Construct _ | Int _ | Float _) -> ()
  | Prod (_,t,c) -> f t; f c
  | Lambda (_,t,c) -> f t; f c
  | LetIn (_,b,t,c) -> f b; f t; f c
  | App (c,l) -> f c; Array.iter f l
  | Evar (_,l) -> Array.iter f l
  | Case (_,p,c,bl) -> f p; f c; Array.iter f bl
  | Fix (_,(_,tl,bl)) -> Array.iter f tl; Array.iter f bl

(* [iter_with_binders g f n c] iters [f n] on the immediate
   subterms of [c]; it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)

let iter_with_binders g f n c = match c with
  | (Rel _ | Var _   | Const _ | Ind _ | Construct _ | Int _ | Float _) -> ()
  | Prod (_,t,c) -> f n t; f (g n) c
  | Lambda (_,t,c) -> f n t; f (g n) c
  | LetIn (_,b,t,c) -> f n b; f n t; f (g n) c
  | App (c,l) -> f n c; Array.iter (fun x-> f n x) l
  | Evar (_,l) -> Array.iter (fun x-> f n x) l
  | Case (_,p,c,bl) -> f n p; f n c; Array.iter (fun x -> f n x) bl
  | Fix (_,(_,tl,bl)) ->
      Array.iter (fun x -> f n x) tl;
      Array.iter (fun x -> f (iterate g (Array.length tl) n) x) bl

(* [fold_constr_with_binders g f n acc c] folds [f n] on the immediate
   subterms of [c] starting from [acc] and proceeding from left to
   right according to the usual representation of the constructions as
   [fold_constr] but it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive *)

let fold_constr_with_binders g f n acc c =
  match c with
  | (Rel _ | Var _  | Const _ | Ind _ | Construct _ | Int _ | Float _) -> acc
  | Prod (_na,t,c) -> f (g  n) (f n acc t) c
  | Lambda (_na,t,c) -> f (g  n) (f n acc t) c
  | LetIn (_na,b,t,c) -> f (g  n) (f n (f n acc b) t) c
  | App (c,l) -> Array.fold_left (f n) (f n acc c) l
  | Evar (_,l) -> Array.fold_left (f n) acc l
  | Case (_,p,c,bl) -> Array.fold_left (f n) (f n (f n acc p) c) bl
  | Fix (_,(_,tl,bl)) ->
      let n' = iterate g (Array.length tl) n in
      let fd = Array.map2 (fun t b -> (t,b)) tl bl in
      Array.fold_left (fun acc (t,b) -> f n' (f n acc t) b) acc fd

(* [map f c] maps [f] on the immediate subterms of [c]; it is
   not recursive and the order with which subterms are processed is
   not specified *)

let map f c = match c with
  | (Rel _ | Var _ | Const _ | Ind _ | Construct _ | Int _ | Float _) -> c
  | Prod (na,t,b) ->
      let b' = f b in
      let t' = f t in
      if b'==b && t' == t then c
      else mkProd (na, t', b')
  | Lambda (na,t,b) ->
      let b' = f b in
      let t' = f t in
      if b'==b && t' == t then c
      else mkLambda (na, t', b')
  | LetIn (na,b,t,k) ->
      let b' = f b in
      let t' = f t in
      let k' = f k in
      if b'==b && t' == t && k'==k then c
      else mkLetIn (na, b', t', k')
  | App (b,l) ->
      let b' = f b in
      let l' = Array.map f l in
      if b'==b && l'==l then c
      else mkApp (b', l')
  | Evar (e,l) ->
      let l' = Array.map f l in
      if l'==l then c
      else mkEvar (e, l')
  | Case (ci,p,b,bl) ->
      let b' = f b in
      let p' = f p in
      let bl' = Array.map f bl in
      if b'==b && p'==p && bl'==bl then c
      else mkCase (ci, p', b', bl')
  | Fix (ln,(lna,tl,bl)) ->
      let tl' = Array.map f tl in
      let bl' = Array.map f bl in
      if tl'==tl && bl'==bl then c
      else mkFix (ln,(lna,tl',bl'))

(* Like {!map} but with an accumulator. *)

(*
let fold_map f accu c = match c with
  | (Rel _ | Var _  | Const _ | Ind _ | Construct _ | Int _ | Float _) -> accu, c
  | Prod (na,t,b) ->
      let accu, b' = f accu b in
      let accu, t' = f accu t in
      if b'==b && t' == t then accu, c
      else accu, mkProd (na, t', b')
  | Lambda (na,t,b) ->
      let accu, b' = f accu b in
      let accu, t' = f accu t in
      if b'==b && t' == t then accu, c
      else accu, mkLambda (na, t', b')
  | LetIn (na,b,t,k) ->
      let accu, b' = f accu b in
      let accu, t' = f accu t in
      let accu, k' = f accu k in
      if b'==b && t' == t && k'==k then accu, c
      else accu, mkLetIn (na, b', t', k')
  | App (b,l) ->
      let accu, b' = f accu b in
      let accu, l' = Array.Smart.fold_left_map f accu l in
      if b'==b && l'==l then accu, c
      else accu, mkApp (b', l')
*)

(* [map_with_binders g f n c] maps [f n] on the immediate
   subterms of [c]; it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)

let map_with_binders g f l c0 = match c0 with
  | (Rel _ | Var _ | Const _ | Ind _ | Construct _ | Int _ | Float _) -> c0
  | Prod (na, t, c) ->
    let t' = f l t in
    let c' = f (g l) c in
    if t' == t && c' == c then c0
    else mkProd (na, t', c')
  | Lambda (na, t, c) ->
    let t' = f l t in
    let c' = f (g l) c in
    if t' == t && c' == c then c0
    else mkLambda (na, t', c')
  | LetIn (na, b, t, c) ->
    let b' = f l b in
    let t' = f l t in
    let c' = f (g l) c in
    if b' == b && t' == t && c' == c then c0
    else mkLetIn (na, b', t', c')
  | App (c, al) ->
    let c' = f l c in
    let al' = Array.map (fun x -> f l x) al in
    if c' == c && al' == al then c0
    else mkApp (c', al')
  | Evar (e, al) ->
    let al' = Array.map (fun x -> f l x) al in
    if al' == al then c0
    else mkEvar (e, al')
  | Case (ci, p, c, bl) ->
    let p' = f l p in
    let c' = f l c in
    let bl' = Array.map (fun x -> f l x) bl in
    if p' == p && c' == c && bl' == bl then c0
    else mkCase (ci, p', c', bl')
  | Fix (ln, (lna, tl, bl)) ->
    let tl' = Array.map (fun x -> f l x) tl in
    let l' = iterate g (Array.length tl) l in
    let bl' = Array.map (fun x -> f l' x) bl in
    if tl' == tl && bl' == bl then c0
    else mkFix (ln,(lna,tl',bl'))

(*********************)
(*      Lifting      *)
(*********************)

(* The generic lifting function *)
let rec exliftn el c =
  let open Esubst in
  match c with
  | Rel i -> mkRel(reloc_rel i el)
  | _ -> map_with_binders el_lift exliftn el c

(* Lifting the binding depth across k bindings *)

let liftn n k c =
  let open Esubst in
  match el_liftn (pred k) (el_shft n el_id) with
    | ELID -> c
    | el -> exliftn el c

let lift n = liftn n 1

let fold_with_full_binders g f n acc c =
  let open Context.Rel.Declaration in
  match c with
  | Rel _ | Var _  | Const _ | Ind _ | Construct _  | Int _ | Float _ -> acc
  | Prod (na,t,c) -> f (g (LocalAssum (na,t)) n) (f n acc t) c
  | Lambda (na,t,c) -> f (g (LocalAssum (na,t)) n) (f n acc t) c
  | LetIn (na,b,t,c) -> f (g (LocalDef (na,b,t)) n) (f n (f n acc b) t) c
  | App (c,l) -> Array.fold_left (f n) (f n acc c) l
  | Evar (_,l) -> Array.fold_left (f n) acc l
  | Case (_,p,c,bl) -> Array.fold_left (f n) (f n (f n acc p) c) bl
  | Fix (_,(lna,tl,bl)) ->
      let n' = array_fold_left2_i (fun i c n t -> g (LocalAssum (n,lift i t)) c) n lna tl in
      let fd = array_map2 (fun t b -> (t,b)) tl bl in
      Array.fold_left (fun acc (t,b) -> f n' (f n acc t) b) acc fd

(* declaration for env *)
type rel_declaration = (t, t) Context.Rel.Declaration.pt
type named_declaration = (t, t) Context.Named.Declaration.pt

type rel_context = rel_declaration list
type named_context = named_declaration list
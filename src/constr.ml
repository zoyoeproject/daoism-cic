open Names
open Context

type case_info =
  { ci_ind        : inductive;      (* inductive type to which belongs the value that is being matched *)
    ci_npar       : int;            (* number of parameters of the above inductive type *)
    ci_cstrs      : (int * int) array; (* fst > snd *)
  }

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
  | Const     of (Constant.t * int )
  | Ind       of (inductive * int)
  | Construct of (constructor * int)
  | Case      of case_info * t * t * t array
  | Fix       of (t, t) pfixpoint
  | Int       of int

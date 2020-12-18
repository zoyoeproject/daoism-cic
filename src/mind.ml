open Names
type inductive_cell = {
    cell_typename : Id.t; (** Name of the type: [Ii] *)
    cell_ctxt : Constr.rel_context; (** Arity context of [Ii] with parameters: [forall params, Ui] *)
    cell_cons: (Name.t * Constr.t) array; (** Names of the constructors: [cij] *)
}

type inductive_block = {
    cells : inductive_cell array;  (** The component of the mutual inductive block *)
    block_hyps : Constr.named_context;  (** Section hypotheses on which the block depends *)
    block_ctxt : Constr.rel_context;  (** The context of parameters (includes let-in declaration) *)
}

let mk_inductive_body cells hyps ctxt = { cells = cells; block_hyps = hyps; block_ctxt = ctxt }

let mk_inductive_cell name ctxt cons =  { cell_typename = name; cell_ctxt = ctxt; cell_cons = cons }

(* For the convinent of creating enum and record *)

let mk_enum_cell name enums mind =
  let cons = Array.map (fun x ->
    (Name.Name x, mind)
  ) enums in
  mk_inductive_cell name [] cons

let mk_record_cell name fields mind =
  let typ = Array.fold_left (fun acc (id,typ) ->
     Constr.mkLambda (Name.Name id, typ, acc)
  ) mind fields in
  let cons = [|Name.Anonymous, typ|] in
  mk_inductive_cell name [] cons

let mk_enum_body name enums mind =
  mk_inductive_body [|mk_enum_cell name enums mind|] [] []

let mk_record_body name fields mind =
  mk_inductive_body [|mk_record_cell name fields mind|] [] []


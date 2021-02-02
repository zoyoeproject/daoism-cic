open Names
let core_dir = ModPath.MPfile (DirPath.make [Id.of_string "core"])
let c_type = Constant.make core_dir (Label.of_string "Type")
let c_int_type = Constant.make core_dir (Label.of_string "int")
let c_float_type = Constant.make core_dir (Label.of_string "float")
let c_fst = Constant.make core_dir (Label.of_string "fst")
let c_snd = Constant.make core_dir (Label.of_string "snd")

let i_bool = KerName.make core_dir (Label.of_string "bool")
let i_prod = KerName.make core_dir (Label.of_string "prod")

let base_type = Constr.Const (c_type, 0)
let int_type = Constr.Const (c_int_type, 0)
let float_type = Constr.Const (c_float_type, 0)
let bool_type = Constr.mkInd (i_bool, 0)
let prod_type = Constr.mkInd (i_prod, 0)
let fst_const = Constr.Const (c_fst, 0)
let snd_const = Constr.Const (c_snd, 0)

let pair = Constr.mkConstruct ((i_prod, 0), 0)

let bool_ind = MiniCic.Mind.mk_enum_body (Id.of_string "bool")
  [|(Id.of_string "true"); (Id.of_string "fase")|]

let prod_ind =
  let open Constr in
  let open Mind in
  let mk_name str = Name.mk_name (Id.of_string str) in
  let cell = mk_record_cell (Id.of_string "prod")
    [|"pair", (
      mkProd (mk_name "T1", base_type,
        (mkProd (mk_name "T2", base_type,
          (mkProd (mk_name "x", mkRel 2,
            (mkProd (mk_name "y", mkRel 2,
              (mkApp (prod_type, [|mkRel 4; mkRel 3|]))
            ))
          ))
        ))
      ))
   |]
  in mk_inductive_body [|cell|] [] []

let bootstrap_env =
  let env = Env.empty_env in
  env
  |> Env.add_constant c_int_type None base_type [||] [||]
  |> Env.add_constant c_float_type None base_type [||] [||]
  |> Env.add_mutind i_bool bool_ind
  |> Env.add_mutind i_prod prod_ind

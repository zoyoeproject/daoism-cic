open Names
let core_dir = ModPath.MPfile (DirPath.make [Id.of_string "core"])
let c_int_type = Constant.make core_dir (Label.of_string "int")
let c_float_type = Constant.make core_dir (Label.of_string "float")
let i_bool = KerName.make core_dir (Label.of_string "bool")

let int_type = Constr.Const (c_int_type, 0)
let float_type = Constr.Const (c_float_type, 0)
let bool_type = Constr.mkInd (i_bool, 0)

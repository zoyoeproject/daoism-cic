open Names
exception Found of (constructor * int)
exception UnknownField
let iterp_project ident env =
   let open Mind in
   try
     ignore @@ Env.fold_minds (fun c ibody _ ->
       let s = Array.fold_left (fun (k, _) cell -> (* iterate cells *)
         let s = Array.fold_left (fun (i, _) cons -> (* iterate cons *)
           let s = Array.fold_left (
             fun (idx, n) (name,t) -> (* iterate field *)
             if name = Name.Name ident then
               raise (Found (((c, k), i), idx))
             else (idx + 1, n)
           ) (0, None) (snd cons) in
           (i + 1, snd s)
         ) (0, None) cell.cell_cons in
         (k + 1, snd s)
       ) (0, None) ibody.cells in
       snd s
     ) None env;
     raise UnknownField
   with
     Found (c, n) -> (c, n)

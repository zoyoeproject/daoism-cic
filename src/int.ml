type t = int

let compare i1 i2 =
  if i1 < i2
  then -1
  else
    if i1 = i2 then 0
    else 1

let eq i1 i2 =
  i1 = i2

let hash i = i
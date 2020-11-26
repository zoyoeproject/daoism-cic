let compare f1 f2 =
  if f1 < f2
  then -1
  else
    if f1 = f2 then 0
    else 1
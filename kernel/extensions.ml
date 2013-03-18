type ('a,'b) chk =
| WellTyped of 'b
| TypeError
| MoreChk of ('a -> 'b -> ('a, 'b) chk)

type t = string

let irr = "Irr"
let iprf = "iPrf"
let ijmeq = "iJMeq"
let isubst = "isubst"

let to_string x = x

let equal a b = a == b
let compare a b = Pervasives.compare a b
let hash a = Hashtbl.hash a

type t

val irr : t
val iprf : t
val ijmeq : t
val isubst : t

val to_string : t -> string
val equal : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int

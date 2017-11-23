type t

val make : int array -> t
val make_self_init : unit -> t

val bits : t -> int * t
val int : int -> t -> int * t
val bool : t -> bool * t

val split : t -> t * t

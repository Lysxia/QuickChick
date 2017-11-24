module RS = Random.State

type t = RS.t

let make = RS.make
let make_self_init = RS.make_self_init

let bits g = (RS.bits g, g)
let int n g = (RS.int g n, g)
let bool g = (RS.bool g, g)

let split g = (g, g)

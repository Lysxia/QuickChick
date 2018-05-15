module PRNG : sig
  include module type of PureSplitMix
  val random_int : int * int -> t -> int
end

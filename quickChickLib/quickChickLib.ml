module PRNG = struct
  include PureSplitMix

  let random_int (x, y) r =
    if x > y then
      failwith
        (Printf.sprintf "random_int: unordered arguments (%d, %d)" x y)
    else
      x + PureSplitMix.int r (y - x + 1)
end

/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace Inkproof.Export

/-- `q` rounded to three decimal places, without trailing zeros. Covered by rounding tests; a theorem relating the string to the
rounded value did not close in the time-box, as the digit handling goes through `toString` on `Nat`. -/
def decimal (q : Rat) : String :=
  let n : Int := (q * 1000 + 1 / 2).floor
  let frac := toString (n.natAbs % 1000)
  let digits := (List.replicate (3 - frac.length) '0' ++ frac.toList).reverse.dropWhile (· == '0')
  let sign := if n < 0 then "-" else ""
  let whole := sign ++ toString (n.natAbs / 1000)
  if digits.isEmpty then whole else whole ++ "." ++ String.ofList digits.reverse

end Inkproof.Export

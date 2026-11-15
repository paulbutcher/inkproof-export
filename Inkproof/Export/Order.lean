/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Export.Lower

namespace Inkproof.Export

open Inkproof.Scene

/-- The primitives that draw a display list, in painting order. -/
def lowerAll (dl : DisplayList) : List Prim :=
  dl.paintOrder.flatMap fun c => lowerShape c.color c.shape

theorem lowerAll_eq (dl : DisplayList) :
    lowerAll dl = dl.paintOrder.flatMap fun c => lowerShape c.color c.shape := rfl

end Inkproof.Export
